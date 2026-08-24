/// Part H: declared effect set, enforced.
import cronch/capability
import cronch/digest
import cronch/hash
import cronch/kernel
import cronch/pubkey
import cronch/receipt
import cronch/term
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should
import support/corpus

fn key(b: Int) -> pubkey.PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<b:size(256)>>)
}

fn dig(b: Int) -> digest.Digest {
  digest.Digest(digest.Blake3, <<b:size(256)>>)
}

fn cap(host: pubkey.PublicKey, n: Int) -> capability.Capability {
  capability.Capability(host: host, proc: capability.proc_name(proc_digest(n)))
}

/// A distinct host-procedure signature per `n`, content-addressed the way
/// everything else is. Procedure objects have to actually resolve: an
/// unresolvable one makes the reachable set Unknown, which is the whole point
/// of the fail-closed tests further down, and would drown out everything else
/// up here.
fn proc_body(n: Int) -> term.Term {
  term.Pi(term.Sort(n), term.Sort(n))
}

fn proc_digest(n: Int) -> digest.Digest {
  hash.hash(digest.Blake3, proc_body(n))
}

/// A term with a `Trusted` node naming `host` and procedure `n`.
fn effectful(host: pubkey.PublicKey, n: Int) -> term.Term {
  term.Trusted(host, proc_digest(n), term.Sort(0), term.Sort(0))
}

/// An environment resolving `entries` plus every procedure object these tests
/// use.
fn env_with(entries: List(#(digest.Digest, term.Term))) -> kernel.Environment {
  let procs =
    list.map([1, 2, 3, 5, 8, 9], fn(n) { #(proc_digest(n), proc_body(n)) })
  let table = list.append(entries, procs)
  kernel.Environment(
    definitions: fn(d) {
      case list.find(table, fn(e) { e.0 == d }) {
        Ok(#(_, t)) -> Some(t)
        Error(_) -> None
      }
    },
    signatures: kernel.empty_signatures(),
    rules: kernel.empty_rules(),
  )
}

fn pure_env() -> kernel.Environment {
  env_with([])
}

// ── a pure term reaches nothing ───────────────────────────────────────────────

pub fn a_pure_term_yields_the_empty_set_test() {
  let t = term.Lam(term.Sort(0), term.Var(0))
  capability.of_term(t, pure_env()) |> should.equal(capability.empty())
  capability.to_list(capability.of_term(t, pure_env()))
  |> should.equal(Ok([]))
}

pub fn a_pure_term_admits_against_an_empty_declaration_test() {
  let t = term.Lam(term.Sort(0), term.Var(0))
  capability.admit(t, pure_env(), capability.empty())
  |> should.equal(capability.Admitted)
  capability.is_admitted(capability.admit(t, pure_env(), capability.empty()))
  |> should.be_true
}

pub fn every_purist_corpus_artifact_reaches_nothing_test() {
  corpus.cases()
  |> list.filter(fn(c) { is_purist(c.name) })
  |> list.each(fn(c) {
    capability.of_term(c.term, c.environment)
    |> should.equal(capability.empty())
  })
}

fn is_purist(name: String) -> Bool {
  case name {
    "purist/" <> _ -> True
    _ -> False
  }
}

// ── direct and transitive reach ───────────────────────────────────────────────

pub fn a_direct_trusted_node_is_detected_test() {
  let t = effectful(key(1), 2)
  capability.of_term(t, pure_env())
  |> should.equal(capability.from_list([cap(key(1), 2)]))
}

pub fn a_capability_three_const_hops_away_is_detected_test() {
  // The artifact names none of these. It reaches the Trusted node through
  // three definitions, and has the capability all the same -- otherwise
  // declaring only what you mention would be defeated by moving the node into
  // a definition.
  let leaf = effectful(key(1), 2)
  let leaf_d = hash.hash(digest.Blake3, leaf)
  let mid = term.Lam(term.Sort(0), term.Const(leaf_d))
  let mid_d = hash.hash(digest.Blake3, mid)
  let top = term.App(term.Const(mid_d), term.Sort(0))
  let top_d = hash.hash(digest.Blake3, top)
  let artifact = term.Lam(term.Sort(0), term.Const(top_d))

  let environment = env_with([#(leaf_d, leaf), #(mid_d, mid), #(top_d, top)])

  capability.of_term(artifact, environment)
  |> should.equal(capability.from_list([cap(key(1), 2)]))

  // And at each shorter distance too.
  capability.of_term(top, environment)
  |> should.equal(capability.from_list([cap(key(1), 2)]))
  capability.of_term(leaf, environment)
  |> should.equal(capability.from_list([cap(key(1), 2)]))
}

pub fn a_capability_reached_through_an_axioms_declared_type_is_detected_test() {
  // An axiom has no body, but its declared TYPE can still mention a Trusted
  // node, and that is reachable.
  let typ = effectful(key(1), 2)
  let axiom = dig(0x77)
  let environment =
    kernel.Environment(..pure_env(), signatures: fn(d) {
      case d == axiom {
        True -> Some(typ)
        False -> None
      }
    })
  capability.of_term(term.Const(axiom), environment)
  |> should.equal(capability.from_list([cap(key(1), 2)]))
}

pub fn several_distinct_capabilities_are_all_collected_test() {
  let t = term.App(effectful(key(1), 1), effectful(key(2), 2))
  capability.of_term(t, pure_env())
  |> should.equal(capability.from_list([cap(key(1), 1), cap(key(2), 2)]))
}

pub fn the_same_capability_twice_is_one_capability_test() {
  let t = term.App(effectful(key(1), 1), effectful(key(1), 1))
  let assert Ok(caps) = capability.to_list(capability.of_term(t, pure_env()))
  list.length(caps) |> should.equal(1)
}

pub fn collection_terminates_on_a_cyclic_store_test() {
  let a = dig(1)
  let b = dig(2)
  let environment = env_with([#(a, term.Const(b)), #(b, term.Const(a))])
  capability.of_term(term.Const(a), environment)
  |> should.equal(capability.empty())
}

// ── excess ────────────────────────────────────────────────────────────────────

pub fn one_undeclared_capability_yields_excess_naming_exactly_that_one_test() {
  let t = term.App(effectful(key(1), 1), effectful(key(2), 2))
  let declared = capability.from_list([cap(key(1), 1)])
  capability.admit(t, pure_env(), declared)
  |> should.equal(capability.Excess([cap(key(2), 2)]))
}

pub fn declaring_everything_admits_test() {
  let t = term.App(effectful(key(1), 1), effectful(key(2), 2))
  let declared = capability.from_list([cap(key(1), 1), cap(key(2), 2)])
  capability.admit(t, pure_env(), declared) |> should.equal(capability.Admitted)
}

pub fn over_declaring_admits_test() {
  // The property is "no more than declared", so declaring extra is allowed --
  // and is exactly why the property is only as informative as the declaration
  // is narrow.
  let t = effectful(key(1), 1)
  let declared =
    capability.from_list([
      cap(key(1), 1),
      cap(key(9), 9),
      cap(key(8), 8),
    ])
  capability.admit(t, pure_env(), declared) |> should.equal(capability.Admitted)
}

pub fn excess_is_sorted_test() {
  let t =
    term.App(
      term.App(effectful(key(9), 9), effectful(key(1), 1)),
      effectful(key(5), 5),
    )
  let assert capability.Excess(excess) =
    capability.admit(t, pure_env(), capability.empty())
  excess
  |> should.equal([cap(key(1), 1), cap(key(5), 5), cap(key(9), 9)])
}

pub fn the_declared_host_matters_not_just_the_procedure_test() {
  // Two hosts running the same procedure are two capabilities. Authorizing one
  // does not authorize the other.
  let t = effectful(key(2), 1)
  let declared = capability.from_list([cap(key(1), 1)])
  capability.admit(t, pure_env(), declared)
  |> should.equal(capability.Excess([cap(key(2), 1)]))
}

// ── unresolvable is refused, never treated as empty ───────────────────────────

pub fn an_unresolvable_reference_yields_unknown_test() {
  let t = term.Const(dig(0xEE))
  capability.of_term(t, pure_env()) |> capability.is_unknown |> should.be_true
  capability.to_list(capability.of_term(t, pure_env())) |> should.be_error
}

pub fn an_unresolvable_reference_is_refused_rather_than_admitted_test() {
  // The attack: point at a name the verifier cannot fetch, and a naive
  // implementation reports an empty reachable set and a clean declaration.
  let t = term.Const(dig(0xEE))
  capability.admit(t, pure_env(), capability.empty())
  |> should.equal(capability.Unresolvable)
  capability.is_admitted(capability.admit(t, pure_env(), capability.empty()))
  |> should.be_false
}

pub fn unresolvable_is_not_excess_of_nothing_test() {
  // `Excess([])` would read as "nothing undeclared", which is the opposite of
  // what an unresolvable reference means. They are separate variants.
  let t = term.Const(dig(0xEE))
  let a = capability.admit(t, pure_env(), capability.empty())
  { a == capability.Excess([]) } |> should.be_false
  a |> should.equal(capability.Unresolvable)
}

pub fn an_unresolvable_reference_anywhere_poisons_the_whole_set_test() {
  // Even alongside a perfectly resolvable, perfectly declared capability.
  let t = term.App(effectful(key(1), 1), term.Const(dig(0xEE)))
  let declared = capability.from_list([cap(key(1), 1)])
  capability.admit(t, pure_env(), declared)
  |> should.equal(capability.Unresolvable)
}

pub fn unknown_is_not_a_subset_of_anything_test() {
  let everything = capability.from_list([cap(key(1), 1)])
  capability.subset(capability.unknown(), everything) |> should.be_false
  capability.subset(capability.unknown(), capability.empty()) |> should.be_false
  capability.subset(capability.unknown(), capability.unknown())
  |> should.be_false
  capability.subset(capability.empty(), capability.unknown()) |> should.be_false
}

pub fn joining_with_unknown_is_unknown_test() {
  let known = capability.from_list([cap(key(1), 1)])
  capability.join([known, capability.unknown()])
  |> capability.is_unknown
  |> should.be_true
  capability.join([capability.unknown(), known])
  |> capability.is_unknown
  |> should.be_true
}

// ── subset and join ───────────────────────────────────────────────────────────

pub fn subset_is_reflexive_and_ordered_test() {
  let small = capability.from_list([cap(key(1), 1)])
  let big = capability.from_list([cap(key(1), 1), cap(key(2), 2)])
  capability.subset(small, small) |> should.be_true
  capability.subset(capability.empty(), small) |> should.be_true
  capability.subset(small, big) |> should.be_true
  capability.subset(big, small) |> should.be_false
}

fn sets() -> List(capability.CapabilitySet) {
  [
    capability.empty(),
    capability.from_list([cap(key(1), 1)]),
    capability.from_list([cap(key(2), 2)]),
    capability.from_list([cap(key(1), 1), cap(key(3), 3)]),
  ]
}

pub fn join_is_commutative_test() {
  list.each(sets(), fn(a) {
    list.each(sets(), fn(b) {
      capability.join([a, b]) |> should.equal(capability.join([b, a]))
    })
  })
}

pub fn join_is_associative_test() {
  list.each(sets(), fn(a) {
    list.each(sets(), fn(b) {
      list.each(sets(), fn(c) {
        capability.join([capability.join([a, b]), c])
        |> should.equal(capability.join([a, capability.join([b, c])]))
      })
    })
  })
}

pub fn join_is_idempotent_test() {
  list.each(sets(), fn(a) {
    capability.join([a, a]) |> should.equal(a)
    capability.join([a]) |> should.equal(a)
  })
}

pub fn join_of_nothing_is_the_empty_set_test() {
  capability.join([]) |> should.equal(capability.empty())
}

pub fn join_contains_both_operands_test() {
  list.each(sets(), fn(a) {
    list.each(sets(), fn(b) {
      let j = capability.join([a, b])
      capability.subset(a, j) |> should.be_true
      capability.subset(b, j) |> should.be_true
    })
  })
}

// ── digest ────────────────────────────────────────────────────────────────────

pub fn the_digest_is_invariant_under_input_order_test() {
  let a = capability.from_list([cap(key(1), 1), cap(key(2), 2)])
  let b = capability.from_list([cap(key(2), 2), cap(key(1), 1)])
  capability.digest(digest.Blake3, a)
  |> should.equal(capability.digest(digest.Blake3, b))
}

pub fn the_digest_is_invariant_under_duplication_test() {
  let a = capability.from_list([cap(key(1), 1)])
  let b = capability.from_list([cap(key(1), 1), cap(key(1), 1)])
  capability.digest(digest.Blake3, a)
  |> should.equal(capability.digest(digest.Blake3, b))
}

pub fn distinct_sets_have_distinct_digests_test() {
  let candidates = [capability.unknown(), ..sets()]
  let digests =
    list.map(candidates, fn(s) { capability.digest(digest.Blake3, s) })
  list.length(list.unique(digests)) |> should.equal(list.length(candidates))
}

pub fn the_unknown_set_does_not_look_like_the_empty_set_test() {
  // A receipt recording an unknown set must not be mistaken for one recording
  // a pure artifact.
  {
    capability.digest(digest.Blake3, capability.unknown())
    == capability.digest(digest.Blake3, capability.empty())
  }
  |> should.be_false
}

pub fn the_encoding_carries_the_capability_set_kind_tag_test() {
  let assert <<tag, _:bits>> = capability.encode(capability.empty())
  tag |> should.equal(0x04)
}

// ── receipts carry the capability digest ──────────────────────────────────────

pub fn a_receipt_records_the_capability_set_digest_test() {
  list.each(corpus.cases(), fn(c) {
    let r =
      receipt.issue(
        "cronch-kernel/0.1.0",
        c.environment,
        c.provenance,
        100_000,
        c.term,
        c.typ,
      )
    r.capabilities
    |> should.equal([
      capability.digest(
        digest.Blake3,
        capability.of_term(c.term, c.environment),
      ),
    ])
  })
}

pub fn the_trusted_node_corpus_case_records_its_host_procedure_test() {
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "host/trusted-node" })
  capability.of_term(c.term, c.environment)
  |> should.equal(
    capability.from_list([
      capability.Capability(
        host: corpus.host(),
        proc: capability.proc_name(corpus.proc()),
      ),
    ]),
  )
}

pub fn an_artifact_reaching_an_unresolvable_const_records_the_unknown_digest_test() {
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "reject/unresolved-const" })
  capability.of_term(c.term, c.environment)
  |> capability.is_unknown
  |> should.be_true
  let r =
    receipt.issue(
      "cronch-kernel/0.1.0",
      c.environment,
      c.provenance,
      100_000,
      c.term,
      c.typ,
    )
  r.capabilities
  |> should.equal([capability.digest(digest.Blake3, capability.unknown())])
}
