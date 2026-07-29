/// Reference rule set: dependent pairs (Sigma) and an equality eliminator
/// (J), declared entirely as axiomatic constants (kernel.gleam's
/// SignatureStore) plus rewrite rules (rewrite.gleam) -- no new `Term`
/// variant, per the explicit non-goal in this task. This is a worked
/// example proving the axiomatic-constant-plus-rule mechanism from
/// kernel.gleam/rewrite.gleam is sufficient to add real type formers
/// without touching the trusted core, and it is the fixture for the
/// trust-gating validation test in reference_rules_test.gleam.
///
/// It lives under test/support, not src/, because that is exactly what it
/// is: a worked example and test fixture, not part of the kernel itself.
///
/// All five constants are content-addressed by hashing their declared type
/// with hash.hash -- the same content-addressing scheme used everywhere
/// else in this codebase (definitions in syntax/elab.gleam are addressed
/// the same way).
///
/// J is declared using the *existing* Eq/Refl Term constructors -- it does
/// not add a new primitive for equality, only an axiom and a rule that
/// pattern-matches on Refl (see rewrite.gleam's PRefl deviation note for
/// why that one extra pattern form exists).
import cronch/digest.{type Digest}
import cronch/hash
import cronch/kernel
import cronch/rewrite.{type Rule}
import cronch/term.{type Term}
import gleam/list
import gleam/option.{type Option, None, Some}

// ── Term-building helpers ─────────────────────────────────────────────────────

fn app2(f: Term, a: Term, b: Term) -> Term {
  term.App(term.App(f, a), b)
}

fn app3(f: Term, a: Term, b: Term, c: Term) -> Term {
  term.App(app2(f, a, b), c)
}

fn app4(f: Term, a: Term, b: Term, c: Term, d: Term) -> Term {
  term.App(app3(f, a, b, c), d)
}

fn app6(f: Term, a: Term, b: Term, c: Term, d: Term, e: Term, g: Term) -> Term {
  term.App(term.App(app4(f, a, b, c, d), e), g)
}

// ── Sigma : (A : Type0) -> (A -> Type0) -> Type0 ───────────────────────────────

/// `Sigma : (A : Type0) -> (A -> Type0) -> Type0`.
pub fn sigma_typ() -> Term {
  term.Pi(
    term.Sort(0),
    term.Pi(term.Pi(term.Var(0), term.Sort(0)), term.Sort(0)),
  )
}

pub fn sigma_digest() -> Digest {
  hash.hash(digest.Blake3, sigma_typ())
}

/// `pair : (A : Type0) -> (B : A -> Type0) -> (a : A) -> B a -> Sigma A B`.
pub fn pair_typ() -> Term {
  term.Pi(
    term.Sort(0),
    term.Pi(
      term.Pi(term.Var(0), term.Sort(0)),
      term.Pi(
        term.Var(1),
        term.Pi(
          term.App(term.Var(1), term.Var(0)),
          app2(term.Const(sigma_digest()), term.Var(3), term.Var(2)),
        ),
      ),
    ),
  )
}

pub fn pair_digest() -> Digest {
  hash.hash(digest.Blake3, pair_typ())
}

/// `fst : (A : Type0) -> (B : A -> Type0) -> Sigma A B -> A`.
pub fn fst_typ() -> Term {
  term.Pi(
    term.Sort(0),
    term.Pi(
      term.Pi(term.Var(0), term.Sort(0)),
      term.Pi(
        app2(term.Const(sigma_digest()), term.Var(1), term.Var(0)),
        term.Var(2),
      ),
    ),
  )
}

pub fn fst_digest() -> Digest {
  hash.hash(digest.Blake3, fst_typ())
}

/// `snd : (A : Type0) -> (B : A -> Type0) -> (p : Sigma A B) -> B (fst A B p)`.
pub fn snd_typ() -> Term {
  term.Pi(
    term.Sort(0),
    term.Pi(
      term.Pi(term.Var(0), term.Sort(0)),
      term.Pi(
        app2(term.Const(sigma_digest()), term.Var(1), term.Var(0)),
        term.App(
          term.Var(1),
          app3(term.Const(fst_digest()), term.Var(2), term.Var(1), term.Var(0)),
        ),
      ),
    ),
  )
}

pub fn snd_digest() -> Digest {
  hash.hash(digest.Blake3, snd_typ())
}

// `fst A B (pair A B a b) --> a`. Slots: 0=A, 1=B, 2=a, 3=b.
pub fn fst_rule() -> Rule {
  let lhs =
    rewrite.PApp(
      rewrite.PApp(
        rewrite.PApp(rewrite.PConst(fst_digest()), rewrite.PVar(0)),
        rewrite.PVar(1),
      ),
      rewrite.PApp(
        rewrite.PApp(
          rewrite.PApp(
            rewrite.PApp(rewrite.PConst(pair_digest()), rewrite.PVar(0)),
            rewrite.PVar(1),
          ),
          rewrite.PVar(2),
        ),
        rewrite.PVar(3),
      ),
    )
  rewrite.Rule(lhs: lhs, rhs: term.Var(2), var_count: 4)
}

// `snd A B (pair A B a b) --> b`. Same shape as fst_rule, slots: 0=A, 1=B,
// 2=a, 3=b.
pub fn snd_rule() -> Rule {
  let lhs =
    rewrite.PApp(
      rewrite.PApp(
        rewrite.PApp(rewrite.PConst(snd_digest()), rewrite.PVar(0)),
        rewrite.PVar(1),
      ),
      rewrite.PApp(
        rewrite.PApp(
          rewrite.PApp(
            rewrite.PApp(rewrite.PConst(pair_digest()), rewrite.PVar(0)),
            rewrite.PVar(1),
          ),
          rewrite.PVar(2),
        ),
        rewrite.PVar(3),
      ),
    )
  rewrite.Rule(lhs: lhs, rhs: term.Var(3), var_count: 4)
}

// ── J : equality elimination, using the existing Eq/Refl primitives ───────────

/// `J : (A : Type0) ->`
/// `    (C : (x : A) -> (y : A) -> Eq A x y -> Type0) ->`
/// `    (c : (x : A) -> C x x (Refl A x)) ->`
/// `    (a : A) -> (b : A) -> (p : Eq A a b) -> C a b p`.
pub fn j_typ() -> Term {
  let motive_typ =
    term.Pi(
      term.Var(0),
      term.Pi(
        term.Var(1),
        term.Pi(term.Eq(term.Var(2), term.Var(1), term.Var(0)), term.Sort(0)),
      ),
    )
  let case_refl_typ =
    term.Pi(
      term.Var(1),
      app3(
        term.Var(1),
        term.Var(0),
        term.Var(0),
        term.Refl(term.Var(2), term.Var(0)),
      ),
    )
  term.Pi(
    term.Sort(0),
    term.Pi(
      motive_typ,
      term.Pi(
        case_refl_typ,
        term.Pi(
          term.Var(2),
          term.Pi(
            term.Var(3),
            term.Pi(
              term.Eq(term.Var(4), term.Var(1), term.Var(0)),
              app3(term.Var(4), term.Var(2), term.Var(1), term.Var(0)),
            ),
          ),
        ),
      ),
    ),
  )
}

pub fn j_digest() -> Digest {
  hash.hash(digest.Blake3, j_typ())
}

// `J A C c a a (Refl A a) --> c a`. Slots: 0=A, 1=C, 2=c, 3=a (used for both
// occurrences of "a" and inside the Refl -- a repeated pattern variable, so
// this only fires when they are literally the same term).
pub fn j_rule() -> Rule {
  let lhs =
    rewrite.PApp(
      rewrite.PApp(
        rewrite.PApp(
          rewrite.PApp(
            rewrite.PApp(
              rewrite.PApp(rewrite.PConst(j_digest()), rewrite.PVar(0)),
              rewrite.PVar(1),
            ),
            rewrite.PVar(2),
          ),
          rewrite.PVar(3),
        ),
        rewrite.PVar(3),
      ),
      rewrite.PRefl(rewrite.PVar(0), rewrite.PVar(3)),
    )
  rewrite.Rule(lhs: lhs, rhs: term.App(term.Var(2), term.Var(3)), var_count: 4)
}

// ── The rule set, and an Environment carrying it ───────────────────────────────────────

/// The whole reference rule set, in a fixed order (order is part of its
/// content address -- see serialize.encode_rule_set).
pub fn rule_set() -> List(Rule) {
  [fst_rule(), snd_rule(), j_rule()]
}

/// This rule set's content hash -- what a rule-set author signs, and what a
/// policy authorizes (see trust.gleam's RuleSetTrust/RuleSetSignature).
pub fn rule_set_hash() -> Digest {
  hash.hash_rule_set(digest.Blake3, rule_set())
}

fn signatures_table() -> List(#(Digest, Term)) {
  [
    #(sigma_digest(), sigma_typ()),
    #(pair_digest(), pair_typ()),
    #(fst_digest(), fst_typ()),
    #(snd_digest(), snd_typ()),
    #(j_digest(), j_typ()),
  ]
}

/// The SignatureStore for all five axiomatic constants declared here.
pub fn signatures() -> kernel.SignatureStore {
  fn(d: Digest) -> Option(Term) {
    case list.find(signatures_table(), fn(e) { e.0 == d }) {
      Ok(#(_, typ)) -> Some(typ)
      Error(_) -> None
    }
  }
}

/// The RuleStore for the reference rule set, keyed by head Const digest.
pub fn rules() -> kernel.RuleStore {
  let table = [
    #(fst_digest(), [fst_rule()]),
    #(snd_digest(), [snd_rule()]),
    #(j_digest(), [j_rule()]),
  ]
  fn(d: Digest) {
    case list.find(table, fn(e) { e.0 == d }) {
      Ok(#(_, rs)) -> rs
      Error(_) -> []
    }
  }
}

/// An Environment with no other definitions, just this reference rule set's
/// axiomatic constants and rules.
pub fn environment() -> kernel.Environment {
  kernel.Environment(
    definitions: kernel.no_store(),
    signatures: signatures(),
    rules: rules(),
  )
}

// ── Example reductions (untyped -- these exercise whnf/normalize directly,
// not kernel.check; see reference_rules_test.gleam for why that is enough
// to validate trust-gating) ────────────────────────────────────────────────

/// `fst A B (pair A B a b)` for arbitrary placeholder A/B/a/b, reducing to
/// `a`. Returns `#(artifact, expected)`.
pub fn fst_pair_example() -> #(Term, Term) {
  let a_val = term.Sort(0)
  let b_fam = term.Lam(term.Sort(0), term.Sort(1))
  let a_elem = term.Sort(7)
  let b_elem = term.Sort(8)
  let sigma_val = app4(term.Const(pair_digest()), a_val, b_fam, a_elem, b_elem)
  let artifact = app3(term.Const(fst_digest()), a_val, b_fam, sigma_val)
  #(artifact, a_elem)
}

/// `snd A B (pair A B a b)`, reducing to `b`.
pub fn snd_pair_example() -> #(Term, Term) {
  let a_val = term.Sort(0)
  let b_fam = term.Lam(term.Sort(0), term.Sort(1))
  let a_elem = term.Sort(7)
  let b_elem = term.Sort(8)
  let sigma_val = app4(term.Const(pair_digest()), a_val, b_fam, a_elem, b_elem)
  let artifact = app3(term.Const(snd_digest()), a_val, b_fam, sigma_val)
  #(artifact, b_elem)
}

/// `J A C c a a (Refl A a)`, reducing to `c a` and then on to whatever that
/// beta-reduces to.
pub fn j_example() -> #(Term, Term) {
  let a_typ = term.Sort(0)
  let motive =
    term.Lam(
      term.Sort(0),
      term.Lam(
        term.Sort(0),
        term.Lam(term.Eq(term.Sort(0), term.Var(1), term.Var(0)), term.Var(0)),
      ),
    )
  let case_refl = term.Lam(term.Sort(0), term.Var(0))
  let elem = term.Sort(9)
  let refl_proof = term.Refl(a_typ, elem)
  let artifact =
    app6(
      term.Const(j_digest()),
      a_typ,
      motive,
      case_refl,
      elem,
      elem,
      refl_proof,
    )
  #(artifact, elem)
}
