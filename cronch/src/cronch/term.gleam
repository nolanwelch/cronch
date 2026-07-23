import cronch/digest.{type Digest}
import cronch/pubkey.{type PublicKey}

/// The term language for the type-checking kernel.
///
/// De Bruijn indices throughout -- no bound-variable names.
/// Structural equality is alpha-equivalence for free.
pub type Term {
  /// de Bruijn index. `Var(0)` is the nearest enclosing binder.
  Var(n: Int)
  /// Universe / sort. `Sort(0)` is `Type 0`. `Sort(u) : Sort(u + 1)`.
  Sort(u: Int)
  /// Dependent function type `(x : A) -> B`. `codomain` is under one binder.
  Pi(domain: Term, codomain: Term)
  /// Lambda `lam (x : A) => b`. `body` is under one binder.
  Lam(domain: Term, body: Term)
  /// Application `f a`.
  App(func: Term, arg: Term)
  /// Propositional equality `Eq A a b`. The one built-in proposition.
  Eq(ty: Term, lhs: Term, rhs: Term)
  /// Reflexivity `refl A a : Eq A a a`.
  Refl(ty: Term, val: Term)
  /// Reference to another term by its content address.
  Const(hash: Digest)
  /// An open obligation. A term containing any Hole is not a closed proof.
  Hole(id: Int, goal: Term)
  /// A result held on a host's authority. Never reduces in the kernel.
  /// The kernel only checks that `args` and `result_ty` match the
  /// procedure's declared signature.
  Trusted(host: PublicKey, proc: Digest, args: Term, result_ty: Term)
}
