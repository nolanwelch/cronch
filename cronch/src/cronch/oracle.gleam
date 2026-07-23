/// Hole-filling protocol and oracle driver.
///
/// A term may contain Hole(id, goal_type) nodes representing open proof
/// obligations. The oracle proposes candidate terms for each hole; the kernel
/// re-checks every proposal before the hole closes. Soundness comes entirely
/// from that kernel re-check -- the oracle is fully untrusted.
///
/// This is the seam where an external reasoner (automated or interactive)
/// plugs in. A wrong proposal is silently rejected and the hole stays open;
/// a bad oracle can never close a hole unsoundly.
///
/// The solve driver always wraps the store in verifying_store, so a store that
/// mislabels a content address can only cause holes to stay stuck, never
/// produce an incorrect proof.

import cronch/digest.{type Digest}
import cronch/hash
import cronch/kernel
import cronch/term.{type Term}
import gleam/list
import gleam/option.{type Option, None, Some}

/// The store type: a pure map from content address to term.
pub type Store =
  fn(Digest) -> Option(Term)

/// An open obligation in situ: its hole id, the typing context at the hole,
/// and the type to inhabit.
pub type Goal {
  Goal(id: Int, cx: kernel.Context, target: Term)
}

/// A candidate inhabitant for a hole. The term may itself contain holes.
pub type Proposal {
  Proposal(hole: Int, term: Term)
}

/// Anything that proposes candidates. A function suffices -- no typeclass needed.
/// Proposals are never trusted: the kernel re-checks every one.
pub type Oracle =
  fn(Goal) -> Option(Proposal)

/// The result of driving a problem to (partial) completion.
pub type Outcome {
  Outcome(artifact: Term, stuck: List(#(Int, Term)))
}

/// Whether the artifact contains no remaining holes.
pub fn is_closed(o: Outcome) -> Bool {
  !has_holes(o.artifact)
}

// ── Built-in oracles ──────────────────────────────────────────────────────────

/// The bootstrap oracle: closes Eq A a a with Refl A a, gives up otherwise.
/// Structural lhs == rhs is the fast path; the kernel re-check handles
/// definitional equality (a structurally distinct but beta-equal pair).
pub fn refl_oracle() -> Oracle {
  fn(g: Goal) -> Option(Proposal) {
    case g.target {
      term.Eq(ty, lhs, rhs) if lhs == rhs ->
        Some(Proposal(hole: g.id, term: term.Refl(ty, lhs)))
      _ -> None
    }
  }
}

/// An oracle backed by a fixed list of (goal_type, candidate_term) pairs.
/// Proposes the first candidate whose paired type equals the goal's target
/// (de Bruijn structural equality is alpha-equivalence, so == suffices).
///
/// Replace the list lookup with a call that generates a candidate and you have
/// a full oracle seam -- an LLM, SMT solver, or interactive prover fits here.
pub fn library_oracle(candidates: List(#(Term, Term))) -> Oracle {
  fn(g: Goal) -> Option(Proposal) {
    case list.find(candidates, fn(pair) { pair.0 == g.target }) {
      Error(_) -> None
      Ok(#(_, candidate)) -> Some(Proposal(hole: g.id, term: candidate))
    }
  }
}

// ── Verifying store ───────────────────────────────────────────────────────────

/// Wrap a store to enforce content-address faithfulness on every resolve.
/// Any object whose hash does not match the requested address is silently
/// dropped (fail closed -- the hole stays stuck rather than closing on a lie).
/// The hash algorithm is taken from the requested Digest, so this is agile.
pub fn verifying_store(inner: Store) -> Store {
  fn(d: Digest) -> Option(Term) {
    case inner(d) {
      None -> None
      Some(t) -> {
        let digest.Digest(algo, _) = d
        case hash.hash(algo, t) == d {
          True -> Some(t)
          False -> None
        }
      }
    }
  }
}

// ── Solve ─────────────────────────────────────────────────────────────────────

/// Drive a problem (a goal type) to completion: start from a single open hole
/// at the problem type and fill until no progress.
pub fn solve(store: Store, oracle: Oracle, problem: Term) -> Outcome {
  solve_state(store, oracle, term.Hole(0, problem))
}

/// Drive an arbitrary starting term (which may already have binders and holes).
/// The store is always wrapped with verifying_store before the kernel sees it.
pub fn solve_state(store: Store, oracle: Oracle, start: Term) -> Outcome {
  let store = verifying_store(store)
  loop(store, oracle, start, [])
}

fn loop(
  store: Store,
  oracle: Oracle,
  state: Term,
  stuck: List(Int),
) -> Outcome {
  case next_goal(state, stuck) {
    None -> Outcome(artifact: state, stuck: collect_stuck(state, stuck))
    Some(goal) ->
      case oracle(goal) {
        None -> loop(store, oracle, state, [goal.id, ..stuck])
        Some(p) ->
          case kernel.check(store, goal.cx, p.term, goal.target) {
            Ok(_) -> loop(store, oracle, fill(state, goal.id, p.term), stuck)
            Error(_) -> loop(store, oracle, state, [goal.id, ..stuck])
          }
      }
  }
}

// ── Private helpers ───────────────────────────────────────────────────────────

fn next_goal(t: Term, skip: List(Int)) -> Option(Goal) {
  go(t, kernel.empty(), skip)
}

fn go(t: Term, cx: kernel.Context, skip: List(Int)) -> Option(Goal) {
  case t {
    term.Hole(id, target) ->
      case list.contains(skip, id) {
        False -> Some(Goal(id: id, cx: cx, target: target))
        True -> go(target, cx, skip)
      }
    term.Var(_) | term.Sort(_) | term.Const(_) -> None
    term.Pi(a, b) ->
      case go(a, cx, skip) {
        Some(_) as g -> g
        None -> go(b, kernel.push(cx, a), skip)
      }
    term.Lam(a, b) ->
      case go(a, cx, skip) {
        Some(_) as g -> g
        None -> go(b, kernel.push(cx, a), skip)
      }
    term.App(f, a) ->
      case go(f, cx, skip) {
        Some(_) as g -> g
        None -> go(a, cx, skip)
      }
    term.Eq(ty, a, b) ->
      case go(ty, cx, skip) {
        Some(_) as g -> g
        None ->
          case go(a, cx, skip) {
            Some(_) as g -> g
            None -> go(b, cx, skip)
          }
      }
    term.Refl(ty, a) ->
      case go(ty, cx, skip) {
        Some(_) as g -> g
        None -> go(a, cx, skip)
      }
    term.Trusted(_, _, args, rty) ->
      case go(args, cx, skip) {
        Some(_) as g -> g
        None -> go(rty, cx, skip)
      }
  }
}

fn fill(t: Term, id: Int, replacement: Term) -> Term {
  case t {
    term.Hole(hid, _) if hid == id -> replacement
    term.Hole(hid, goal) -> term.Hole(hid, fill(goal, id, replacement))
    term.Var(_) | term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(fill(a, id, replacement), fill(b, id, replacement))
    term.Lam(a, b) -> term.Lam(fill(a, id, replacement), fill(b, id, replacement))
    term.App(f, a) -> term.App(fill(f, id, replacement), fill(a, id, replacement))
    term.Eq(ty, a, b) ->
      term.Eq(
        fill(ty, id, replacement),
        fill(a, id, replacement),
        fill(b, id, replacement),
      )
    term.Refl(ty, a) ->
      term.Refl(fill(ty, id, replacement), fill(a, id, replacement))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(
        host,
        proc,
        fill(args, id, replacement),
        fill(rty, id, replacement),
      )
  }
}

fn has_holes(t: Term) -> Bool {
  case t {
    term.Hole(_, _) -> True
    term.Var(_) | term.Sort(_) | term.Const(_) -> False
    term.Pi(a, b) | term.Lam(a, b) -> has_holes(a) || has_holes(b)
    term.App(f, a) -> has_holes(f) || has_holes(a)
    term.Eq(ty, a, b) -> has_holes(ty) || has_holes(a) || has_holes(b)
    term.Refl(ty, a) -> has_holes(ty) || has_holes(a)
    term.Trusted(_, _, args, rty) -> has_holes(args) || has_holes(rty)
  }
}

fn collect_stuck(t: Term, stuck_ids: List(Int)) -> List(#(Int, Term)) {
  collect_holes(t)
  |> list.filter(fn(pair) { list.contains(stuck_ids, pair.0) })
}

fn collect_holes(t: Term) -> List(#(Int, Term)) {
  case t {
    term.Hole(id, goal) -> [#(id, goal), ..collect_holes(goal)]
    term.Var(_) | term.Sort(_) | term.Const(_) -> []
    term.Pi(a, b) | term.Lam(a, b) ->
      list.append(collect_holes(a), collect_holes(b))
    term.App(f, a) -> list.append(collect_holes(f), collect_holes(a))
    term.Eq(ty, a, b) ->
      list.append(collect_holes(ty), list.append(collect_holes(a), collect_holes(b)))
    term.Refl(ty, a) -> list.append(collect_holes(ty), collect_holes(a))
    term.Trusted(_, _, args, rty) ->
      list.append(collect_holes(args), collect_holes(rty))
  }
}
