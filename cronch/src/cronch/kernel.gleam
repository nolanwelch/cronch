/// The type-checking kernel.
///
/// This is the entire trusted surface of the system. Every function here is
/// pure and total: ill-typed terms, unresolvable references, and universe
/// overflow are reported as TypeError, never panics.
///
/// shift/subst are the highest-risk code in the whole project. Most soundness
/// bugs live there. The implementations below are the deliberately obvious
/// ones. Do not optimize them.
///
/// Trusted surface (public functions called from outside the kernel):
///   whnf, normalize, def_eq, infer, check
///
/// shift, subst, beta are also public because they are useful to callers
/// (e.g. elaboration, pretty-printing) and are pure/total.
import cronch/digest.{type Digest}
import cronch/term.{type Term}
import gleam/int
import gleam/option.{type Option, None, Some}
import gleam/result

/// Maximum allowed universe level (u32::MAX). Sort(max_universe) has no
/// successor: attempting to infer its type is UniverseOverflow.
const max_universe: Int = 4_294_967_295

// ── Store and Context ─────────────────────────────────────────────────────────

/// A pure read-only map from content address to term.
/// The only thing the kernel reads beyond its direct arguments.
pub type Store =
  fn(Digest) -> Option(Term)

/// A store that resolves nothing. Use for closed terms with no Const nodes.
pub fn no_store() -> Store {
  fn(_) { None }
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

/// Weak head normal form: beta/delta-reduce the head until it is stuck.
/// Never reduces under binders or inside arguments.
/// An unresolvable Const is left in place (it is a type error in infer, not here).
pub fn whnf(store: Store, t: Term) -> Term {
  case t {
    term.App(f, a) ->
      case whnf(store, f) {
        term.Lam(_, body) -> whnf(store, beta(a, body))
        stuck -> term.App(stuck, a)
      }
    term.Const(d) ->
      case store(d) {
        None -> t
        Some(def) -> whnf(store, def)
      }
    other -> other
  }
}

/// Full normal form: whnf, then recurse into every subterm.
/// Trusted is inert: its fields are normalized but the node never reduces.
pub fn normalize(store: Store, t: Term) -> Term {
  let h = whnf(store, t)
  case h {
    term.Var(_) | term.Sort(_) | term.Const(_) -> h
    term.Pi(a, b) -> term.Pi(normalize(store, a), normalize(store, b))
    term.Lam(a, b) -> term.Lam(normalize(store, a), normalize(store, b))
    term.App(f, a) -> term.App(normalize(store, f), normalize(store, a))
    term.Eq(ty, a, b) ->
      term.Eq(normalize(store, ty), normalize(store, a), normalize(store, b))
    term.Refl(ty, a) -> term.Refl(normalize(store, ty), normalize(store, a))
    term.Hole(id, ty) -> term.Hole(id, normalize(store, ty))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(host, proc, normalize(store, args), normalize(store, rty))
  }
}

/// Definitional equality: whnf both sides, then compare heads structurally.
/// Up to beta and delta. No eta in v0.
/// Trusted nodes compare structurally: equal host/proc and def_eq args/result_ty.
pub fn def_eq(store: Store, a: Term, b: Term) -> Bool {
  let a = whnf(store, a)
  let b = whnf(store, b)
  case a, b {
    term.Var(i), term.Var(j) -> i == j
    term.Sort(i), term.Sort(j) -> i == j
    term.Const(d1), term.Const(d2) -> d1 == d2
    term.Pi(a1, b1), term.Pi(a2, b2) ->
      def_eq(store, a1, a2) && def_eq(store, b1, b2)
    term.Lam(a1, b1), term.Lam(a2, b2) ->
      def_eq(store, a1, a2) && def_eq(store, b1, b2)
    term.App(f1, x1), term.App(f2, x2) ->
      def_eq(store, f1, f2) && def_eq(store, x1, x2)
    term.Eq(t1, a1, b1), term.Eq(t2, a2, b2) ->
      def_eq(store, t1, t2) && def_eq(store, a1, a2) && def_eq(store, b1, b2)
    term.Refl(t1, a1), term.Refl(t2, a2) ->
      def_eq(store, t1, t2) && def_eq(store, a1, a2)
    term.Hole(i, t1), term.Hole(j, t2) -> i == j && def_eq(store, t1, t2)
    term.Trusted(h1, p1, a1, r1), term.Trusted(h2, p2, a2, r2) ->
      h1 == h2 && p1 == p2 && def_eq(store, a1, a2) && def_eq(store, r1, r2)
    _, _ -> False
  }
}

// ── Type checking ─────────────────────────────────────────────────────────────

/// Infer the type of t in context cx. Returns a well-formed type or an error.
/// The returned type is always valid; check relies on this invariant.
pub fn infer(store: Store, cx: Context, t: Term) -> Result(Term, TypeError) {
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
      use i <- result.try(infer_sort(store, cx, a))
      let cx2 = push(cx, a)
      use j <- result.try(infer_sort(store, cx2, b))
      Ok(term.Sort(int.max(i, j)))
    }

    term.Lam(a, b) -> {
      use _ <- result.try(infer_sort(store, cx, a))
      let cx2 = push(cx, a)
      use body_ty <- result.try(infer(store, cx2, b))
      Ok(term.Pi(a, body_ty))
    }

    term.App(f, x) -> {
      use f_ty <- result.try(infer(store, cx, f))
      case whnf(store, f_ty) {
        term.Pi(dom, cod) -> {
          use _ <- result.try(check(store, cx, x, dom))
          Ok(beta(x, cod))
        }
        other -> Error(NotAFunction(other))
      }
    }

    term.Eq(ty, a, b) -> {
      use i <- result.try(infer_sort(store, cx, ty))
      use _ <- result.try(check(store, cx, a, ty))
      use _ <- result.try(check(store, cx, b, ty))
      Ok(term.Sort(i))
    }

    term.Refl(ty, a) -> {
      use _ <- result.try(infer_sort(store, cx, ty))
      use _ <- result.try(check(store, cx, a, ty))
      Ok(term.Eq(ty, a, a))
    }

    term.Const(d) ->
      case store(d) {
        None -> Error(Unresolved(d))
        Some(def) -> infer(store, empty(), def)
      }

    term.Hole(_, goal) -> {
      use _ <- result.try(infer_sort(store, cx, goal))
      Ok(goal)
    }

    term.Trusted(_, proc, args, result_ty) ->
      infer_trusted(store, cx, proc, args, result_ty)
  }
}

/// Check that t has type expected in context cx.
/// Sound because infer returns only well-formed types: success means expected
/// is def_eq to a genuine inferred type.
pub fn check(
  store: Store,
  cx: Context,
  t: Term,
  expected: Term,
) -> Result(Nil, TypeError) {
  use actual <- result.try(infer(store, cx, t))
  case def_eq(store, actual, expected) {
    True -> Ok(Nil)
    False -> Error(Mismatch(expected: expected, actual: actual))
  }
}

// ── Private helpers ───────────────────────────────────────────────────────────

fn infer_sort(store: Store, cx: Context, t: Term) -> Result(Int, TypeError) {
  use ty <- result.try(infer(store, cx, t))
  case whnf(store, ty) {
    term.Sort(u) -> Ok(u)
    found -> Error(ExpectedSort(found))
  }
}

fn infer_trusted(
  store: Store,
  cx: Context,
  proc: Digest,
  args: Term,
  result_ty: Term,
) -> Result(Term, TypeError) {
  case store(proc) {
    None -> Error(Unresolved(proc))
    Some(sig) ->
      case infer(store, empty(), sig) {
        Error(_) -> Error(TrustedProcNotAType(sig))
        Ok(_) ->
          case whnf(store, sig) {
            term.Pi(dom, cod) -> {
              use _ <- result.try(check(store, cx, args, dom))
              let expected = beta(args, cod)
              use _ <- result.try(infer_sort(store, cx, result_ty))
              case def_eq(store, result_ty, expected) {
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
