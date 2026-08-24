/// The shared checking corpus.
///
/// One environment, one rule set, and a list of named checking problems that
/// every part of this PR is measured against: Part C's non-regression and
/// monotonicity tests, Part D's fuel determinism, Part F's replay, Part J's
/// "recording is not deciding". Keeping them in one place means those tests
/// agree on what "the corpus" is instead of each inventing its own.
///
/// The environment extends test/support/reference_rules.gleam rather than
/// replacing it: the Sigma/J axioms and rules are exactly the ones already
/// there, plus four extra axioms and one extra rule that this PR needs. The
/// reference rule set's own content hash is untouched, so the existing tests
/// that pin it keep passing.
///
/// Constants are content-addressed by hashing their declared type, matching
/// reference_rules.gleam's convention. Every declared type here is distinct,
/// so no two constants collide.
import cronch/digest.{type Digest}
import cronch/hash
import cronch/kernel
import cronch/pubkey.{type PublicKey}
import cronch/rewrite.{type Rule}
import cronch/term.{type Term}
import gleam/list
import gleam/option.{type Option, None, Some}
import support/reference_rules

// ── Identities ────────────────────────────────────────────────────────────────

/// The rule-set author whose signature a policy would pin.
pub fn author() -> PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<0xA1:size(256)>>)
}

/// A Trusted-node host.
pub fn host() -> PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<0xB2:size(256)>>)
}

/// A second host, never used by any corpus artifact. Revoking it must change
/// nothing -- the negative control for Part G.
pub fn other_host() -> PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<0xB3:size(256)>>)
}

// ── Extra axioms ──────────────────────────────────────────────────────────────

/// `A : Type 0`. An ordinary opaque type.
pub fn atom_typ() -> Term {
  term.Sort(0)
}

pub fn atom() -> Digest {
  hash.hash(digest.Blake3, atom_typ())
}

/// `a : A`. An inhabitant of it.
pub fn elem_typ() -> Term {
  term.Const(atom())
}

pub fn elem() -> Digest {
  hash.hash(digest.Blake3, elem_typ())
}

/// `W : Type 1`. Declared one universe up, and rewritten to `Type 0` by the
/// rule below. The rewrite is type-preserving (`Type 0 : Type 1`), so this is
/// a legitimate rule, not a rigged one.
pub fn w_typ() -> Term {
  term.Sort(1)
}

pub fn w() -> Digest {
  hash.hash(digest.Blake3, w_typ())
}

/// `S : W`. The constant whose sort can only be established by rewriting `W`.
/// This is the whole point of the Part C regression fixture: `S` is usable as
/// a type ONLY because `W` reduces to `Type 0`, and that reduction happens
/// while checking a binder's domain annotation -- nowhere in the artifact's
/// own normal form.
pub fn s_typ() -> Term {
  term.Const(w())
}

pub fn s() -> Digest {
  hash.hash(digest.Blake3, s_typ())
}

/// `L : Type 2`, rewritten to itself. Used to build a term whose check cannot
/// terminate under any finite budget, for the Exhausted cases. Declared at
/// level 2 only so its type differs from every other axiom's and it gets its
/// own content address.
pub fn loop_typ() -> Term {
  term.Sort(2)
}

pub fn loop_const() -> Digest {
  hash.hash(digest.Blake3, loop_typ())
}

// ── Extra rules ───────────────────────────────────────────────────────────────

/// `W --> Type 0`. Fires only while establishing that `S` denotes a type.
pub fn w_rule() -> Rule {
  rewrite.Rule(lhs: rewrite.PConst(w()), rhs: term.Sort(0), var_count: 0)
}

/// `L --> L`. Never terminates. Declared, like every other rule here, with no
/// termination check anywhere -- which is exactly why fuel exists.
pub fn loop_rule() -> Rule {
  rewrite.Rule(
    lhs: rewrite.PConst(loop_const()),
    rhs: term.Const(loop_const()),
    var_count: 0,
  )
}

/// The corpus rule set: the reference rules plus this module's two, in a fixed
/// order. Order is part of the content address.
pub fn rule_set() -> List(Rule) {
  list.append(reference_rules.rule_set(), [w_rule(), loop_rule()])
}

/// The corpus rule set's content hash -- what an author signs and a policy
/// authorizes.
pub fn rule_set_hash() -> Digest {
  hash.hash_rule_set(digest.Blake3, rule_set())
}

// ── Definitions ───────────────────────────────────────────────────────────────

/// `id_A = lam (x : A) => x`, a constant with a body. Addressed by hashing the
/// body, matching syntax/elab.gleam's convention for definitions.
pub fn id_body() -> Term {
  term.Lam(term.Const(atom()), term.Var(0))
}

pub fn id_def() -> Digest {
  hash.hash(digest.Blake3, id_body())
}

/// The declared signature of the host procedure a Trusted node names:
/// `A -> A`. Addressed by hashing it, and resolved out of `definitions`
/// because that is where `infer_trusted` looks for a procedure signature.
pub fn proc_sig() -> Term {
  term.Pi(term.Const(atom()), term.Const(atom()))
}

pub fn proc() -> Digest {
  hash.hash(digest.Blake3, proc_sig())
}

// ── The environment ───────────────────────────────────────────────────────────

fn signature_table() -> List(#(Digest, Term)) {
  [
    #(atom(), atom_typ()),
    #(elem(), elem_typ()),
    #(w(), w_typ()),
    #(s(), s_typ()),
    #(loop_const(), loop_typ()),
  ]
}

fn definition_table() -> List(#(Digest, Term)) {
  [#(id_def(), id_body()), #(proc(), proc_sig())]
}

fn rule_table() -> List(#(Digest, List(Rule))) {
  [
    #(reference_rules.fst_digest(), [reference_rules.fst_rule()]),
    #(reference_rules.snd_digest(), [reference_rules.snd_rule()]),
    #(reference_rules.j_digest(), [reference_rules.j_rule()]),
    #(w(), [w_rule()]),
    #(loop_const(), [loop_rule()]),
  ]
}

fn lookup(table: List(#(Digest, a)), d: Digest) -> Option(a) {
  case list.find(table, fn(e) { e.0 == d }) {
    Ok(#(_, v)) -> Some(v)
    Error(_) -> None
  }
}

// Each of these builds its table ONCE and captures it in the returned
// closure. Building it inside the closure instead would re-hash every
// constant on every single store lookup -- the digests here are content
// addresses, so each one is a Blake3 of a serialized term.

pub fn definitions() -> kernel.Store {
  let table = definition_table()
  fn(d) { lookup(table, d) }
}

pub fn signatures() -> kernel.SignatureStore {
  let table = signature_table()
  let reference = reference_rules.signatures()
  fn(d) {
    case lookup(table, d) {
      Some(t) -> Some(t)
      None -> reference(d)
    }
  }
}

pub fn rules() -> kernel.RuleStore {
  let table = rule_table()
  fn(d) {
    case lookup(table, d) {
      Some(rs) -> rs
      None -> []
    }
  }
}

pub fn environment() -> kernel.Environment {
  kernel.Environment(
    definitions: definitions(),
    signatures: signatures(),
    rules: rules(),
  )
}

/// An environment with the same axioms but NO rules. Checking an artifact
/// against this is how a test demonstrates that a rule set is a genuine
/// dependency rather than a decoration.
pub fn environment_without_rules() -> kernel.Environment {
  kernel.Environment(
    definitions: definitions(),
    signatures: signatures(),
    rules: kernel.empty_rules(),
  )
}

/// Every rule in the corpus rule set, tagged with that set's (author, hash).
pub fn provenance() -> kernel.Provenance {
  let tag = kernel.RuleUse(author: author(), rule_set: rule_set_hash())
  let rules = rules()
  fn(d) { list.map(rules(d), fn(r) { #(tag, r) }) }
}

/// A provenance that attributes nothing, for the no-rules environment.
pub fn empty_provenance() -> kernel.Provenance {
  fn(_) { [] }
}

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

/// `B = lam (_ : A) => A`, the constant type family over `A`.
pub fn family() -> Term {
  term.Lam(term.Const(atom()), term.Const(atom()))
}

/// `pair A B a a : Sigma A B`.
pub fn a_pair() -> Term {
  app4(
    term.Const(reference_rules.pair_digest()),
    term.Const(atom()),
    family(),
    term.Const(elem()),
    term.Const(elem()),
  )
}

// ── The corpus ────────────────────────────────────────────────────────────────

/// What a case is expected to do, recorded so a reader can see the intent
/// without running it. Tests still compute the verdict rather than trusting
/// this field.
pub type Expectation {
  ExpectAccept
  ExpectReject
  ExpectExhaust
}

/// One named checking problem: check `term` against `typ` in the empty
/// context, under `environment`/`provenance`.
pub type Case {
  Case(
    name: String,
    environment: kernel.Environment,
    provenance: kernel.Provenance,
    term: Term,
    typ: Term,
    expectation: Expectation,
    note: String,
  )
}

fn case_in(
  name: String,
  t: Term,
  typ: Term,
  expectation: Expectation,
  note: String,
) -> Case {
  Case(
    name: name,
    environment: environment(),
    provenance: provenance(),
    term: t,
    typ: typ,
    expectation: expectation,
    note: note,
  )
}

/// THE Part C regression artifact.
///
/// `lam (x : S) => x`, checked against `S -> S`. It typechecks, and it
/// typechecks ONLY because the rule `W --> Type 0` fires: `S`'s declared type
/// is `W`, and establishing that a binder's domain annotation denotes a type
/// means reducing `W` to a sort. Nothing in the artifact's normal form
/// mentions `W`, so a trust set reconstructed by normalizing the artifact sees
/// no rule use at all and reports the empty set -- and the purist policy then
/// says "authorized" for an artifact whose acceptance depended on an
/// unauthorized rule set.
pub fn annotation_only_artifact() -> Term {
  term.Lam(term.Const(s()), term.Var(0))
}

pub fn annotation_only_typ() -> Term {
  term.Pi(term.Const(s()), term.Const(s()))
}

/// A term whose check cannot terminate: the conversion check reduces `L`,
/// which rewrites to itself forever.
pub fn looping_artifact() -> Term {
  term.Lam(term.Const(loop_const()), term.Var(0))
}

pub fn looping_typ() -> Term {
  term.Pi(term.Const(loop_const()), term.Const(loop_const()))
}

/// Every case, in a fixed order. Nothing here iterates a map or a store, so
/// this list is identical across runs, processes and targets.
pub fn cases() -> List(Case) {
  [
    case_in(
      "purist/identity",
      term.Lam(term.Sort(0), term.Var(0)),
      term.Pi(term.Sort(0), term.Sort(0)),
      ExpectAccept,
      "no Const, no Trusted, no rule can fire",
    ),
    case_in(
      "purist/sort",
      term.Sort(0),
      term.Sort(1),
      ExpectAccept,
      "the smallest possible derivation",
    ),
    case_in(
      "purist/nested-lambda",
      term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0))),
      term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1))),
      ExpectAccept,
      "binders under binders, still purist",
    ),
    case_in(
      "purist/refl",
      term.Refl(term.Sort(1), term.Sort(0)),
      term.Eq(term.Sort(1), term.Sort(0), term.Sort(0)),
      ExpectAccept,
      "the built-in equality, at a sort",
    ),
    case_in(
      "const/axiom",
      term.Const(elem()),
      term.Const(atom()),
      ExpectAccept,
      "an axiomatic constant at its declared type",
    ),
    case_in(
      "const/definition",
      term.Const(id_def()),
      term.Pi(term.Const(atom()), term.Const(atom())),
      ExpectAccept,
      "a defined constant, resolved through the store",
    ),
    case_in(
      "host/trusted-node",
      term.Trusted(host(), proc(), term.Const(elem()), term.Const(atom())),
      term.Const(atom()),
      ExpectAccept,
      "carries a HostTrust dependency and no rule-set dependency",
    ),
    case_in(
      "rules/fst-in-conversion",
      term.Refl(
        term.Const(atom()),
        app3(
          term.Const(reference_rules.fst_digest()),
          term.Const(atom()),
          family(),
          a_pair(),
        ),
      ),
      term.Eq(term.Const(atom()), term.Const(elem()), term.Const(elem())),
      ExpectAccept,
      "the fst rule fires inside the conversion check",
    ),
    case_in(
      "rules/annotation-only",
      annotation_only_artifact(),
      annotation_only_typ(),
      ExpectAccept,
      "Part C regression: rule set used ONLY in a binder's type annotation",
    ),
    case_in(
      "reject/mismatch",
      term.Lam(term.Sort(0), term.Var(0)),
      term.Pi(term.Sort(0), term.Sort(1)),
      ExpectReject,
      "well-formed term, wrong declared type",
    ),
    case_in(
      "reject/unbound",
      term.Var(3),
      term.Sort(0),
      ExpectReject,
      "no such variable in the empty context",
    ),
    case_in(
      "reject/not-a-function",
      term.App(term.Sort(0), term.Sort(0)),
      term.Sort(0),
      ExpectReject,
      "applying something whose type is not a Pi",
    ),
    case_in(
      "reject/unresolved-const",
      term.Const(digest.Digest(digest.Blake3, <<0xEE:size(256)>>)),
      term.Sort(0),
      ExpectReject,
      "a Const in neither store -- fails closed",
    ),
    case_in(
      "exhaust/self-rewriting-const",
      looping_artifact(),
      looping_typ(),
      ExpectExhaust,
      "the conversion check reduces L, which rewrites to itself forever",
    ),
  ]
}

/// The cases expected to typecheck. Several parts only care about these.
pub fn accepting_cases() -> List(Case) {
  list.filter(cases(), fn(c) { c.expectation == ExpectAccept })
}
