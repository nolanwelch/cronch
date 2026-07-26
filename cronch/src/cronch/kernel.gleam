/// The type-checking kernel.
///
/// This is the entire trusted surface of the system. Every function here is
/// pure: ill-typed terms, unresolvable references, universe overflow, and
/// a fuel-exhausted reduction are reported as TypeError, never a panic.
/// That liveness guarantee holds under `Limited(n)` Fuel by construction.
/// Under `Unlimited` Fuel it does not: a non-terminating rule
/// set can make whnf/normalize/def_eq/infer/check hang, exactly the way an
/// infinite loop in any other pure function would. That is a caller's
/// explicit, visible choice (see the Fuel doc comment below), never a
/// hidden kernel default.
///
/// shift/subst are the highest-risk code in the whole project. Most soundness
/// bugs live there. The implementations below are the deliberately obvious
/// ones. Do not optimize them.
///
/// Trusted surface (public functions called from outside the kernel):
///   whnf, normalize, def_eq, infer, check --
///   whnf_with_uses, normalize_with_uses (called only by trust.gleam, to
///   recompute which rule sets a reduction actually invoked; see RuleUse).
///
/// shift, subst, beta are also public because they are useful to callers
/// (e.g. elaboration, pretty-printing) and are pure/total regardless of Fuel.
import cronch/digest.{type Digest}
import cronch/pubkey.{type PublicKey}
import cronch/rewrite.{type Rule}
import cronch/term.{type Term}
import gleam/dict
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

/// Maximum allowed universe level (u32::MAX). Sort(max_universe) has no
/// successor: attempting to infer its type is UniverseOverflow.
const max_universe: Int = 4_294_967_295

// ── Store, SignatureStore, Env, and Context ────────────────────────────────────

/// A pure read-only map from content address to term.
/// The only thing the kernel reads beyond its direct arguments.
pub type Store =
  fn(Digest) -> Option(Term)

/// A store that resolves nothing. Use for closed terms with no Const nodes.
pub fn no_store() -> Store {
  fn(_) { None }
}

/// The type of an axiomatic constant: a symbol with a declared type and no
/// body. Consulted before `defs` by both `whnf` and `infer` -- an axiomatic
/// constant never delta-unfolds. It reduces, if at all, only through rules
/// in `RuleStore` (see rewrite.gleam). This is how new type formers (Sigma,
/// an equality eliminator, ...) get added without growing `Term` itself.
pub type SignatureStore =
  fn(Digest) -> Option(Term)

/// A signature store that resolves nothing.
pub fn empty_sigs() -> SignatureStore {
  fn(_) { None }
}

/// Re-exported so call sites that only need the RuleStore type or "no
/// rules" don't need a direct import of cronch/rewrite.
pub type RuleStore =
  rewrite.RuleStore

pub fn empty_rules() -> RuleStore {
  rewrite.empty_rules()
}

/// Everything the kernel reads beyond its direct term/context arguments,
/// bundled so it threads as one value through whnf/normalize/def_eq/infer/
/// check instead of three.
///
/// Precondition, not checked at runtime: `defs` and `sigs` must be disjoint
/// -- no Digest may be a key in both. A digest is supposed to denote exactly
/// one thing (a definition with a body, or an axiom with none), never both.
/// Both `whnf` and `infer` consult `sigs` first, so if this precondition is
/// violated, `sigs` silently wins for that digest and `defs`'s entry is
/// never seen. This is consistent with how a `Store` has always been "a
/// pure function the caller is responsible for constructing correctly" --
/// checking it here would add a lookup-time cost to every single Const
/// resolution to guard against a builder bug that content-addressing
/// already makes unlikely (an honest builder never assigns one digest two
/// different meanings).
pub type Env {
  Env(defs: Store, sigs: SignatureStore, rules: RuleStore)
}

/// Wrap a bare definitional store as an Env with no axiomatic constants and
/// no rewrite rules -- the mechanical adaptation for every call site that
/// only ever needed a Store before Env existed.
pub fn env_from_store(defs: Store) -> Env {
  Env(defs: defs, sigs: empty_sigs(), rules: empty_rules())
}

/// A typing context: a stack of variable types, Var(0)'s type at the head.
pub opaque type Context {
  Context(types: List(Term))
}

/// The empty context.
pub fn empty() -> Context {
  Context([])
}

/// Extend the context: the new term becomes the type of Var(0).
pub fn push(cx: Context, ty: Term) -> Context {
  Context([ty, ..cx.types])
}

/// The type of Var(n) in cx, shifted into the current context.
///
/// The stored type was recorded n+1 binders ago, so its free variables must
/// be shifted up by n+1. Getting this wrong is the classic soundness bug.
fn type_of_var(cx: Context, n: Int) -> Option(Term) {
  lookup(cx.types, n, 0)
}

fn lookup(types: List(Term), n: Int, depth: Int) -> Option(Term) {
  case types {
    [] -> None
    [ty, ..] if n == 0 -> Some(shift(depth + 1, 0, ty))
    [_, ..rest] -> lookup(rest, n - 1, depth + 1)
  }
}

// ── Fuel ──────────────────────────────────────────────────────────────────────

/// A reduction budget. `Limited(n)` guarantees whnf/normalize/def_eq/infer/
/// check terminate -- reporting `FuelExhausted` rather than hanging -- even
/// against a rule set that turns out to be non-terminating in practice.
/// Confluence and termination of a rule set are never checked anywhere in
/// this codebase (see rewrite.gleam's Rule doc comment); Limited fuel is the
/// kernel's only defense against that. `Unlimited` turns the defense off: a
/// non-terminating rule set then hangs the caller's process, exactly like an
/// infinite loop in any other pure function would. That is a legitimate,
/// explicit choice ("I have already convinced myself this rule set
/// terminates, and I don't want an artificial ceiling on legitimate deep
/// reductions"), never a hidden default -- there is no bare-Int overload and
/// no default parameter; every entry point below takes a Fuel value.
pub type Fuel {
  Limited(Int)
  Unlimited
}

/// A generous, fixed budget for the test suite and any other call site that
/// is not specifically exercising fuel exhaustion. Large enough that no
/// legitimate reduction in this codebase's tests comes close (the deepest
/// reduction chains here are a few dozen steps); small enough that a
/// non-terminating rule set still fails in well under a second on the BEAM.
pub const test_fuel: Fuel = Limited(100_000)

// Consume one unit of fuel. Unlimited is never decremented and never runs
// out; Limited(0) is exhausted.
fn consume(fuel: Fuel) -> Result(Fuel, TypeError) {
  case fuel {
    Unlimited -> Ok(Unlimited)
    Limited(0) -> Error(FuelExhausted)
    Limited(n) -> Ok(Limited(n - 1))
  }
}

// ── RuleUse ───────────────────────────────────────────────────────────────────

/// One rule set invoked while reducing a term, identified by its signer and
/// content hash. Returned by whnf_with_uses/normalize_with_uses so
/// trust.gleam can recompute an artifact's rule-set trust dependencies by
/// re-running the exact reduction the kernel performs, rather than
/// statically guessing which rules a term *could* invoke (undecidable in
/// general, and would over- or under-report). See trust.gleam for how this
/// feeds into trust sets.
pub type RuleUse {
  RuleUse(author: PublicKey, rule_set: Digest)
}

// ── TypeError ─────────────────────────────────────────────────────────────────

/// Why a term failed to type-check. Never a panic.
pub type TypeError {
  UnboundVar(Int)
  ExpectedSort(Term)
  NotAFunction(Term)
  Mismatch(expected: Term, actual: Term)
  Unresolved(Digest)
  UniverseOverflow
  TrustedProcNotAType(Term)
  TrustedProcNotPi(Term)
  TrustedCodomainMismatch(expected: Term, actual: Term)
  /// A rewrite-rule application ran out of Limited fuel. Never produced
  /// under Unlimited fuel -- see the Fuel doc comment.
  FuelExhausted
}

// ── Shift and substitution ────────────────────────────────────────────────────

/// shift(d, cutoff, t): add d to every free variable Var(k) with k >= cutoff.
/// The cutoff rises by one under each binder. d may be negative (used in beta).
pub fn shift(d: Int, cutoff: Int, t: Term) -> Term {
  case t {
    term.Var(k) ->
      case k >= cutoff {
        True -> term.Var(k + d)
        False -> term.Var(k)
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(shift(d, cutoff, a), shift(d, cutoff + 1, b))
    term.Lam(a, b) -> term.Lam(shift(d, cutoff, a), shift(d, cutoff + 1, b))
    term.App(f, a) -> term.App(shift(d, cutoff, f), shift(d, cutoff, a))
    term.Eq(ty, a, b) ->
      term.Eq(shift(d, cutoff, ty), shift(d, cutoff, a), shift(d, cutoff, b))
    term.Refl(ty, a) -> term.Refl(shift(d, cutoff, ty), shift(d, cutoff, a))
    term.Hole(id, ty) -> term.Hole(id, shift(d, cutoff, ty))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(host, proc, shift(d, cutoff, args), shift(d, cutoff, rty))
  }
}

/// subst(j, s, t): substitute s for Var(j) in t.
/// Under each binder, j becomes j+1 and s is shifted up by one.
pub fn subst(j: Int, s: Term, t: Term) -> Term {
  case t {
    term.Var(k) ->
      case k == j {
        True -> s
        False -> t
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(subst(j, s, a), subst(j + 1, shift(1, 0, s), b))
    term.Lam(a, b) -> term.Lam(subst(j, s, a), subst(j + 1, shift(1, 0, s), b))
    term.App(f, a) -> term.App(subst(j, s, f), subst(j, s, a))
    term.Eq(ty, a, b) ->
      term.Eq(subst(j, s, ty), subst(j, s, a), subst(j, s, b))
    term.Refl(ty, a) -> term.Refl(subst(j, s, ty), subst(j, s, a))
    term.Hole(id, ty) -> term.Hole(id, subst(j, s, ty))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(host, proc, subst(j, s, args), subst(j, s, rty))
  }
}

/// Beta-reduce App(Lam(_, body), arg).
/// beta(arg, body) = shift(-1, 0, subst(0, shift(1, 0, arg), body))
pub fn beta(arg: Term, body: Term) -> Term {
  let arg_up = shift(1, 0, arg)
  let substituted = subst(0, arg_up, body)
  shift(-1, 0, substituted)
}

// ── Reduction ─────────────────────────────────────────────────────────────────
//
// whnf is implemented as whnf_go, generic over the "tag" carried alongside
// each rule (type parameter `u` below). The untracked, public `whnf` tags
// every rule with Nil and throws the tags away; `whnf_with_uses` tags every
// rule with its owning rule set's RuleUse and returns the tags that actually
// fired. There is exactly one reduction algorithm either way -- the public
// `whnf` is not a separate, simpler implementation that could drift from
// the one trust.gleam depends on for soundness-relevant accounting.
//
// Design note on Fuel and nesting: whnf_go does NOT thread an updated Fuel
// value back out of nested calls (e.g. reducing the function position of an
// App before trying rules on the resulting spine reuses the same Fuel value
// the caller passed in, rather than an amount reduced by whatever the
// nested call consumed). This is deliberately simpler than a single global
// counter threaded through the whole call. It is still safe: any single
// reduction chain that alternates forever between "reduce the head" and
// "try a rule on the result" is bounded by (structural depth of the
// original term) x (fuel), which is finite for a finite input term, so
// whnf_go still always terminates or reports FuelExhausted -- it just is
// not a perfectly tight bound on total work. Fuel exhaustion is a
// termination guard, not a precise cost accounting mechanism (see the Fuel
// doc comment); this trade favors simplicity.

/// Weak head normal form: beta/delta/rule-reduce the head until it is stuck.
/// Never reduces under binders or inside arguments.
/// An unresolvable Const is left in place (it is a type error in infer, not here).
pub fn whnf(env: Env, fuel: Fuel, t: Term) -> Result(Term, TypeError) {
  let prov = fn(d) { list.map(env.rules(d), fn(r) { #(Nil, r) }) }
  use #(term, _uses) <- result.try(whnf_go(env, prov, fuel, t))
  Ok(term)
}

/// Like whnf, but also returns every RuleUse that fired while reducing t.
/// Used only by trust.gleam to recompute rule-set trust dependencies.
pub fn whnf_with_uses(
  env: Env,
  prov: fn(Digest) -> List(#(RuleUse, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(RuleUse)), TypeError) {
  whnf_go(env, prov, fuel, t)
}

fn whnf_go(
  env: Env,
  prov: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(u)), TypeError) {
  case t {
    term.App(f, a) -> {
      use #(fh, uses1) <- result.try(whnf_go(env, prov, fuel, f))
      case fh {
        term.Lam(_, body) -> whnf_go(env, prov, fuel, beta(a, body))
        stuck -> {
          use #(final, uses2) <- result.try(try_rewrite(
            env,
            prov,
            fuel,
            term.App(stuck, a),
          ))
          Ok(#(final, list.append(uses1, uses2)))
        }
      }
    }
    // sigs is consulted first, same precondition as infer's Const case
    // (see Env's doc comment): an axiomatic constant never delta-unfolds,
    // it only ever reduces through rules.
    term.Const(d) ->
      case env.sigs(d) {
        Some(_) -> try_rewrite(env, prov, fuel, t)
        None ->
          case env.defs(d) {
            None -> try_rewrite(env, prov, fuel, t)
            Some(def) -> whnf_go(env, prov, fuel, def)
          }
      }
    other -> Ok(#(other, []))
  }
}

// Try every rule keyed to t's head Const (if it has one) against t itself.
// On the first match, consume one unit of fuel and keep reducing the
// result. On no match, t is genuinely stuck -- returned unchanged, same as
// a plain unresolvable Const was before rules existed.
fn try_rewrite(
  env: Env,
  prov: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(u)), TypeError) {
  case head_const(t) {
    None -> Ok(#(t, []))
    Some(d) ->
      case find_match(prov(d), t) {
        None -> Ok(#(t, []))
        Some(#(tag, rewritten)) -> {
          use fuel2 <- result.try(consume(fuel))
          use #(final, more) <- result.try(whnf_go(env, prov, fuel2, rewritten))
          Ok(#(final, [tag, ..more]))
        }
      }
  }
}

// The Const at the head of an application spine, e.g. head_const(f a b) =
// head_const(f). None for anything not headed by a Const (Lam, Sort, ...).
fn head_const(t: Term) -> Option(Digest) {
  case t {
    term.Const(d) -> Some(d)
    term.App(f, _) -> head_const(f)
    _ -> None
  }
}

fn find_match(tagged: List(#(u, Rule)), t: Term) -> Option(#(u, Term)) {
  case tagged {
    [] -> None
    [#(tag, rule), ..rest] ->
      case rewrite.match_pattern(rule.lhs, t, dict.new()) {
        Some(slots) -> Some(#(tag, rewrite.instantiate(rule.rhs, slots)))
        None -> find_match(rest, t)
      }
  }
}

/// Full normal form: whnf, then recurse into every subterm.
/// Trusted is inert: its fields are normalized but the node never reduces.
pub fn normalize(env: Env, fuel: Fuel, t: Term) -> Result(Term, TypeError) {
  let prov = fn(d) { list.map(env.rules(d), fn(r) { #(Nil, r) }) }
  use #(term, _uses) <- result.try(normalize_go(env, prov, fuel, t))
  Ok(term)
}

/// Like normalize, but also returns every RuleUse that fired anywhere in
/// the term. Used only by trust.gleam.
pub fn normalize_with_uses(
  env: Env,
  prov: fn(Digest) -> List(#(RuleUse, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(RuleUse)), TypeError) {
  normalize_go(env, prov, fuel, t)
}

fn normalize_go(
  env: Env,
  prov: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(u)), TypeError) {
  use #(h, uses1) <- result.try(whnf_go(env, prov, fuel, t))
  case h {
    term.Var(_) | term.Sort(_) | term.Const(_) -> Ok(#(h, uses1))
    term.Pi(a, b) -> {
      use #(na, uses2) <- result.try(normalize_go(env, prov, fuel, a))
      use #(nb, uses3) <- result.try(normalize_go(env, prov, fuel, b))
      Ok(#(term.Pi(na, nb), list.append(uses1, list.append(uses2, uses3))))
    }
    term.Lam(a, b) -> {
      use #(na, uses2) <- result.try(normalize_go(env, prov, fuel, a))
      use #(nb, uses3) <- result.try(normalize_go(env, prov, fuel, b))
      Ok(#(term.Lam(na, nb), list.append(uses1, list.append(uses2, uses3))))
    }
    term.App(f, a) -> {
      use #(nf, uses2) <- result.try(normalize_go(env, prov, fuel, f))
      use #(na, uses3) <- result.try(normalize_go(env, prov, fuel, a))
      Ok(#(term.App(nf, na), list.append(uses1, list.append(uses2, uses3))))
    }
    term.Eq(ty, a, b) -> {
      use #(nty, uses2) <- result.try(normalize_go(env, prov, fuel, ty))
      use #(na, uses3) <- result.try(normalize_go(env, prov, fuel, a))
      use #(nb, uses4) <- result.try(normalize_go(env, prov, fuel, b))
      Ok(#(
        term.Eq(nty, na, nb),
        list.append(uses1, list.append(uses2, list.append(uses3, uses4))),
      ))
    }
    term.Refl(ty, a) -> {
      use #(nty, uses2) <- result.try(normalize_go(env, prov, fuel, ty))
      use #(na, uses3) <- result.try(normalize_go(env, prov, fuel, a))
      Ok(#(term.Refl(nty, na), list.append(uses1, list.append(uses2, uses3))))
    }
    term.Hole(id, ty) -> {
      use #(nty, uses2) <- result.try(normalize_go(env, prov, fuel, ty))
      Ok(#(term.Hole(id, nty), list.append(uses1, uses2)))
    }
    term.Trusted(host, proc, args, rty) -> {
      use #(nargs, uses2) <- result.try(normalize_go(env, prov, fuel, args))
      use #(nrty, uses3) <- result.try(normalize_go(env, prov, fuel, rty))
      Ok(#(
        term.Trusted(host, proc, nargs, nrty),
        list.append(uses1, list.append(uses2, uses3)),
      ))
    }
  }
}

/// Definitional equality: whnf both sides, then compare heads structurally.
/// Up to beta, delta, and rewrite rules. No eta in v0.
/// Trusted nodes compare structurally: equal host/proc and def_eq args/result_ty.
pub fn def_eq(
  env: Env,
  fuel: Fuel,
  a: Term,
  b: Term,
) -> Result(Bool, TypeError) {
  use wa <- result.try(whnf(env, fuel, a))
  use wb <- result.try(whnf(env, fuel, b))
  case wa, wb {
    term.Var(i), term.Var(j) -> Ok(i == j)
    term.Sort(i), term.Sort(j) -> Ok(i == j)
    term.Const(d1), term.Const(d2) -> Ok(d1 == d2)
    term.Pi(a1, b1), term.Pi(a2, b2) -> and_eq(env, fuel, a1, a2, b1, b2)
    term.Lam(a1, b1), term.Lam(a2, b2) -> and_eq(env, fuel, a1, a2, b1, b2)
    term.App(f1, x1), term.App(f2, x2) -> and_eq(env, fuel, f1, f2, x1, x2)
    term.Eq(t1, a1, b1), term.Eq(t2, a2, b2) ->
      and3_eq(env, fuel, t1, t2, a1, a2, b1, b2)
    term.Refl(t1, a1), term.Refl(t2, a2) -> and_eq(env, fuel, t1, t2, a1, a2)
    term.Hole(i, t1), term.Hole(j, t2) ->
      case i == j {
        False -> Ok(False)
        True -> def_eq(env, fuel, t1, t2)
      }
    term.Trusted(h1, p1, a1, r1), term.Trusted(h2, p2, a2, r2) ->
      case h1 == h2 && p1 == p2 {
        False -> Ok(False)
        True -> and_eq(env, fuel, a1, a2, r1, r2)
      }
    _, _ -> Ok(False)
  }
}

fn and_eq(
  env: Env,
  fuel: Fuel,
  x1: Term,
  x2: Term,
  y1: Term,
  y2: Term,
) -> Result(Bool, TypeError) {
  use e1 <- result.try(def_eq(env, fuel, x1, x2))
  case e1 {
    True -> def_eq(env, fuel, y1, y2)
    False -> Ok(False)
  }
}

fn and3_eq(
  env: Env,
  fuel: Fuel,
  x1: Term,
  x2: Term,
  y1: Term,
  y2: Term,
  z1: Term,
  z2: Term,
) -> Result(Bool, TypeError) {
  use e1 <- result.try(def_eq(env, fuel, x1, x2))
  case e1 {
    False -> Ok(False)
    True -> and_eq(env, fuel, y1, y2, z1, z2)
  }
}

// ── Type checking ─────────────────────────────────────────────────────────────

/// Infer the type of t in context cx. Returns a well-formed type or an error.
/// The returned type is always valid; check relies on this invariant.
pub fn infer(
  env: Env,
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(Term, TypeError) {
  case t {
    term.Var(n) ->
      case type_of_var(cx, n) {
        None -> Error(UnboundVar(n))
        Some(ty) -> Ok(ty)
      }

    term.Sort(u) ->
      case u >= max_universe {
        True -> Error(UniverseOverflow)
        False -> Ok(term.Sort(u + 1))
      }

    term.Pi(a, b) -> {
      use i <- result.try(infer_sort(env, fuel, cx, a))
      let cx2 = push(cx, a)
      use j <- result.try(infer_sort(env, fuel, cx2, b))
      Ok(term.Sort(int.max(i, j)))
    }

    term.Lam(a, b) -> {
      use _ <- result.try(infer_sort(env, fuel, cx, a))
      let cx2 = push(cx, a)
      use body_ty <- result.try(infer(env, fuel, cx2, b))
      Ok(term.Pi(a, body_ty))
    }

    term.App(f, x) -> {
      use f_ty <- result.try(infer(env, fuel, cx, f))
      use w <- result.try(whnf(env, fuel, f_ty))
      case w {
        term.Pi(dom, cod) -> {
          use _ <- result.try(check(env, fuel, cx, x, dom))
          Ok(beta(x, cod))
        }
        other -> Error(NotAFunction(other))
      }
    }

    term.Eq(ty, a, b) -> {
      use i <- result.try(infer_sort(env, fuel, cx, ty))
      use _ <- result.try(check(env, fuel, cx, a, ty))
      use _ <- result.try(check(env, fuel, cx, b, ty))
      Ok(term.Sort(i))
    }

    term.Refl(ty, a) -> {
      use _ <- result.try(infer_sort(env, fuel, cx, ty))
      use _ <- result.try(check(env, fuel, cx, a, ty))
      Ok(term.Eq(ty, a, a))
    }

    // sigs is consulted first: an axiomatic constant's declared type is
    // returned directly, and it is never unfolded via defs. See Env's doc
    // comment for the precondition this relies on (defs/sigs disjoint).
    term.Const(d) ->
      case env.sigs(d) {
        Some(ty) -> Ok(ty)
        None ->
          case env.defs(d) {
            None -> Error(Unresolved(d))
            Some(def) -> infer(env, fuel, empty(), def)
          }
      }

    term.Hole(_, goal) -> {
      use _ <- result.try(infer_sort(env, fuel, cx, goal))
      Ok(goal)
    }

    term.Trusted(_, proc, args, result_ty) ->
      infer_trusted(env, fuel, cx, proc, args, result_ty)
  }
}

/// Check that t has type expected in context cx.
/// Sound because infer returns only well-formed types: success means expected
/// is def_eq to a genuine inferred type.
pub fn check(
  env: Env,
  fuel: Fuel,
  cx: Context,
  t: Term,
  expected: Term,
) -> Result(Nil, TypeError) {
  use actual <- result.try(infer(env, fuel, cx, t))
  use eq <- result.try(def_eq(env, fuel, actual, expected))
  case eq {
    True -> Ok(Nil)
    False -> Error(Mismatch(expected: expected, actual: actual))
  }
}

// ── Private helpers ───────────────────────────────────────────────────────────

fn infer_sort(
  env: Env,
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(Int, TypeError) {
  use ty <- result.try(infer(env, fuel, cx, t))
  use w <- result.try(whnf(env, fuel, ty))
  case w {
    term.Sort(u) -> Ok(u)
    found -> Error(ExpectedSort(found))
  }
}

fn infer_trusted(
  env: Env,
  fuel: Fuel,
  cx: Context,
  proc: Digest,
  args: Term,
  result_ty: Term,
) -> Result(Term, TypeError) {
  case env.defs(proc) {
    None -> Error(Unresolved(proc))
    Some(sig) ->
      case infer(env, fuel, empty(), sig) {
        Error(_) -> Error(TrustedProcNotAType(sig))
        Ok(_) -> {
          use w <- result.try(whnf(env, fuel, sig))
          case w {
            term.Pi(dom, cod) -> {
              use _ <- result.try(check(env, fuel, cx, args, dom))
              let expected = beta(args, cod)
              use _ <- result.try(infer_sort(env, fuel, cx, result_ty))
              use eq <- result.try(def_eq(env, fuel, result_ty, expected))
              case eq {
                True -> Ok(result_ty)
                False ->
                  Error(TrustedCodomainMismatch(
                    expected: expected,
                    actual: result_ty,
                  ))
              }
            }
            other -> Error(TrustedProcNotPi(other))
          }
        }
      }
  }
}
