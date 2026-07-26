/// User-declared rewrite rules: the data-driven extension point for
/// definitional equality.
///
/// New type formers (Sigma, an equality eliminator, eventually inductive
/// recursors) are declared as ordinary axiomatic constants (kernel.gleam's
/// SignatureStore) plus `Rule`s here -- never as new `Term` variants. A rule
/// set is content-addressed and signed like anything else in this repo; the
/// trust layer (trust.gleam) decides whether a client's policy accepts it.
/// This module only defines the data shape and pure matching/instantiation;
/// wiring rules into reduction happens in kernel.gleam's `whnf`.
///
/// Hard constraint, load-bearing, do not relax: `Pattern` has no case for
/// `Hole` or `Trusted`, and never will. Two invariants elsewhere in the
/// codebase depend on this:
///
///   - oracle.gleam's `has_holes` reasons that "a term with no Hole nodes is
///     closed." A rule that could manufacture a fresh Hole out of nothing
///     would let a rule set silently reopen a closed proof.
///   - trust.gleam's trust sets reason that every Trusted node in a term is
///     visible by walking its structure. A rule that could manufacture a
///     fresh Trusted node would let a rule set hide a trust dependency
///     behind what looks like ordinary computation.
///
/// `PVar(k)` is the only escape hatch, and it is safe: it always matches
/// whatever subterm is there, Hole/Trusted included, and carries it forward
/// *opaquely* -- the matched subterm reappears verbatim (via `instantiate`)
/// wherever `Var(k)` occurs in the rule's rhs, but the rule can never inspect
/// its shape, and the rhs can never introduce a Hole/Trusted that was not
/// already present, unexpanded, in the term being reduced.
///
/// Deviation from the literal "Var, Sort, Const, App only" pattern grammar:
/// see `PRefl` below. It is added solely so the reference J-eliminator rule
/// (test/support/reference_rules.gleam) can match on `Refl`, and it does not
/// weaken the hard constraint above -- `Eq`/`Refl` are ordinary primitive
/// term formers with no closedness or trust invariant riding on them the way
/// Hole/Trusted have.
import cronch/digest.{type Digest}
import cronch/term.{type Term}
import gleam/dict.{type Dict}
import gleam/option.{type Option, None, Some}

// ── Patterns and rules ───────────────────────────────────────────────────────

/// A pattern a rule's left-hand side is built from. Deliberately a small
/// subset of `Term`: only the shapes needed to recognize "some axiomatic
/// constant applied to some arguments," plus `PRefl` (see module comment).
pub type Pattern {
  /// Binds the matched subterm under slot `Int`. Always matches; see the
  /// module comment for why that is safe.
  PVar(Int)
  PSort(Int)
  PConst(Digest)
  PApp(Pattern, Pattern)
  /// Matches `Refl(ty, val)`. Not part of the original Var/Sort/Const/App
  /// grammar -- see the module-level deviation note.
  PRefl(ty: Pattern, val: Pattern)
}

/// A rewrite rule: `lhs` matches a term, `rhs` (with `Var(k)` for `k <
/// nvars` standing for "whatever PVar(k) matched") replaces it.
///
/// Confluence and termination of a rule set are not checked here, or
/// anywhere in this codebase -- that is out of scope by design (see the
/// task description this module was built for). A rule set's soundness is
/// established out-of-band by whoever signs it; the kernel's only
/// obligation is to fail closed (via fuel) if it turns out not to
/// terminate, never to silently loop.
pub type Rule {
  Rule(lhs: Pattern, rhs: Term, nvars: Int)
}

/// A pure lookup from a head Const digest to the rules whose lhs ultimately
/// applies to that constant. Keying by head digest means whnf only ever
/// looks at rules relevant to the term it is reducing, not the whole set.
pub type RuleStore =
  fn(Digest) -> List(Rule)

/// A rule store with no rules. The rewrite mechanism is fully inert until a
/// caller supplies something else.
pub fn empty_rules() -> RuleStore {
  fn(_) { [] }
}

// ── Matching ──────────────────────────────────────────────────────────────────

/// Try to match `pat` against `t`, extending `slots` with any newly-bound
/// pattern variables. A repeated `PVar(k)` must match a subterm structurally
/// equal (`==`, i.e. alpha-equivalent de Bruijn terms) to whatever `k` is
/// already bound to -- not merely `def_eq`. Structural equality is the
/// simpler choice and is sufficient for every rule this codebase declares
/// (fst/snd/pair, J): the terms a repeated pattern variable is expected to
/// unify are always literally the same subterm reappearing in the matched
/// term (e.g. the two `a`s in `J(C, c, a, a, Refl(A, a))`), never merely
/// definitionally-equal-but-distinct terms. Using `def_eq` here would also
/// require threading an Env and Fuel through matching, which this module
/// deliberately has no dependency on (see the circular-import note below).
pub fn match_pattern(
  pat: Pattern,
  t: Term,
  slots: Dict(Int, Term),
) -> Option(Dict(Int, Term)) {
  case pat, t {
    PVar(k), _ ->
      case dict.get(slots, k) {
        Ok(bound) ->
          case bound == t {
            True -> Some(slots)
            False -> None
          }
        Error(_) -> Some(dict.insert(slots, k, t))
      }
    PSort(u), term.Sort(v) ->
      case u == v {
        True -> Some(slots)
        False -> None
      }
    PConst(d1), term.Const(d2) ->
      case d1 == d2 {
        True -> Some(slots)
        False -> None
      }
    PApp(pf, pa), term.App(f, a) -> {
      use slots2 <- option.then(match_pattern(pf, f, slots))
      match_pattern(pa, a, slots2)
    }
    PRefl(pty, pval), term.Refl(ty, val) -> {
      use slots2 <- option.then(match_pattern(pty, ty, slots))
      match_pattern(pval, val, slots2)
    }
    _, _ -> None
  }
}

// ── Instantiation ─────────────────────────────────────────────────────────────

/// Replace `Var(k)` for `k < nvars` in `rhs` with the term bound to slot `k`
/// in `slots`, shifting each substituted term by the binder depth it is
/// inserted under -- the same discipline `kernel.subst` uses for a single
/// variable, generalized to simultaneously substituting many.
///
/// `shift_up` below duplicates `kernel.shift`'s algorithm rather than
/// calling it. This is a deliberate, narrow deviation: kernel.gleam must
/// import this module to wire rules into `whnf` (task requirement), so this
/// module cannot import kernel.gleam back without a cycle. The duplicated
/// code is small, private, and pinned down by the differential test in
/// rewrite_test.gleam that checks it against the same case kernel_test.gleam
/// uses to pin down `subst`/`beta`. If kernel.shift's algorithm ever
/// changes, this must change with it.
pub fn instantiate(rhs: Term, slots: Dict(Int, Term)) -> Term {
  instantiate_at(rhs, 0, slots)
}

fn instantiate_at(t: Term, depth: Int, slots: Dict(Int, Term)) -> Term {
  case t {
    term.Var(k) ->
      case k < depth {
        True -> t
        False ->
          case dict.get(slots, k - depth) {
            Ok(s) -> shift_up(depth, s)
            // A rule referencing a slot outside 0..nvars is malformed; rule
            // well-formedness is not validated here (out of scope -- see
            // the Rule doc comment), so this leaves the index untouched
            // rather than panicking.
            Error(_) -> t
          }
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) ->
      term.Pi(instantiate_at(a, depth, slots), instantiate_at(b, depth + 1, slots))
    term.Lam(a, b) ->
      term.Lam(instantiate_at(a, depth, slots), instantiate_at(b, depth + 1, slots))
    term.App(f, a) ->
      term.App(instantiate_at(f, depth, slots), instantiate_at(a, depth, slots))
    term.Eq(ty, a, b) ->
      term.Eq(
        instantiate_at(ty, depth, slots),
        instantiate_at(a, depth, slots),
        instantiate_at(b, depth, slots),
      )
    term.Refl(ty, a) ->
      term.Refl(instantiate_at(ty, depth, slots), instantiate_at(a, depth, slots))
    term.Hole(id, goal) -> term.Hole(id, instantiate_at(goal, depth, slots))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(
        host,
        proc,
        instantiate_at(args, depth, slots),
        instantiate_at(rty, depth, slots),
      )
  }
}

// shift_up(d, t): add d (d >= 0 always, since it is only ever a binder
// depth) to every free variable in t. See the instantiate doc comment for
// why this duplicates kernel.shift instead of calling it.
fn shift_up(d: Int, t: Term) -> Term {
  case d {
    0 -> t
    _ -> shift_from(d, 0, t)
  }
}

fn shift_from(d: Int, cutoff: Int, t: Term) -> Term {
  case t {
    term.Var(k) ->
      case k >= cutoff {
        True -> term.Var(k + d)
        False -> term.Var(k)
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(shift_from(d, cutoff, a), shift_from(d, cutoff + 1, b))
    term.Lam(a, b) -> term.Lam(shift_from(d, cutoff, a), shift_from(d, cutoff + 1, b))
    term.App(f, a) -> term.App(shift_from(d, cutoff, f), shift_from(d, cutoff, a))
    term.Eq(ty, a, b) ->
      term.Eq(shift_from(d, cutoff, ty), shift_from(d, cutoff, a), shift_from(d, cutoff, b))
    term.Refl(ty, a) -> term.Refl(shift_from(d, cutoff, ty), shift_from(d, cutoff, a))
    term.Hole(id, goal) -> term.Hole(id, shift_from(d, cutoff, goal))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(
        host,
        proc,
        shift_from(d, cutoff, args),
        shift_from(d, cutoff, rty),
      )
  }
}
