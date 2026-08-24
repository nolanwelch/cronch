/// Part G: the ledger, and the exactly-computable blast radius of a
/// revocation.
///
/// The receipts here are built by hand rather than issued from real checks.
/// That is deliberate: the ledger's job is to reason about receipts as data,
/// including receipts an adversary made up, and hand-built ones let these
/// tests construct dependency shapes (a depth-5 chain, a diamond, a cycle)
/// that no honest store would produce.
import cronch/basis
import cronch/canonical
import cronch/digest
import cronch/ledger
import cronch/pubkey
import cronch/receipt
import cronch/trust
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

const kernel_id = "cronch-kernel/0.1.0"

fn key(b: Int) -> pubkey.PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<b:size(256)>>)
}

fn dig(b: Int) -> digest.Digest {
  digest.Digest(digest.Blake3, <<b:size(256)>>)
}

fn author() -> pubkey.PublicKey {
  key(0xA1)
}

fn rule_set() -> digest.Digest {
  dig(0x5E)
}

fn host() -> pubkey.PublicKey {
  key(0xB2)
}

fn a_basis() -> basis.Basis {
  basis.Basis(kernel_id: kernel_id, axioms: [], rule_sets: [], hosts: [])
}

fn basis_digest() -> digest.Digest {
  basis.digest(receipt.default_algorithm, a_basis())
}

/// A receipt for `artifact`, depending on `deps`, carrying `trust_set` and
/// `axioms`, with the given verdict.
fn rcpt(
  artifact: digest.Digest,
  deps: List(digest.Digest),
  trust_set: List(trust.TrustPair),
  axioms: List(digest.Digest),
  verdict: receipt.Verdict,
) -> receipt.Receipt {
  receipt.canonicalize(receipt.Receipt(
    version: 1,
    basis: basis_digest(),
    artifact: artifact,
    spec: dig(0xFF),
    deps: deps,
    axioms: axioms,
    trust_set: trust_set,
    capabilities: [],
    fuel_declared: 1000,
    fuel_used: 1,
    verdict: verdict,
  ))
}

fn accepted(
  artifact: digest.Digest,
  deps: List(digest.Digest),
  trust_set: List(trust.TrustPair),
) -> receipt.Receipt {
  rcpt(artifact, deps, trust_set, [], receipt.Accepted)
}

/// Revoking the fixture rule set -- the revocation most of these tests use.
fn revoke_fixture() -> ledger.Revocation {
  ledger.RevokeRuleSet(author(), rule_set())
}

/// 1..n, hand-rolled: gleam_stdlib 1.0.3 has no list.range.
fn upto(n: Int) -> List(Int) {
  case n <= 0 {
    True -> []
    False -> list.append(upto(n - 1), [n])
  }
}

fn of(receipts: List(receipt.Receipt)) -> ledger.Ledger {
  receipts
  |> list.fold(ledger.new(), ledger.add)
  |> ledger.add_basis(a_basis())
}

// ── G1: the shape the whole design is for ─────────────────────────────────────

/// A uses a fixture rule set. B depends on A through a Const. C is purist:
/// empty trust set, no deps, no axioms.
fn g1() -> #(ledger.Ledger, digest.Digest, digest.Digest, digest.Digest) {
  let a = dig(0x0A)
  let b = dig(0x0B)
  let c = dig(0x0C)
  let l =
    of([
      accepted(a, [], [trust.RuleSetTrust(author(), rule_set())]),
      accepted(b, [a], []),
      accepted(c, [], []),
    ])
  #(l, a, b, c)
}

pub fn g1_revoking_a_rule_set_kills_exactly_its_dependents_test() {
  let #(l, a, b, c) = g1()
  let radius = ledger.blast_radius(l, [revoke_fixture()])
  radius |> should.equal(canonical.sort_digests([a, b]))
  list.contains(radius, c) |> should.be_false
}

pub fn g1_survivors_is_exactly_the_complement_test() {
  let #(l, _, _, c) = g1()
  ledger.survivors(l, [revoke_fixture()]) |> should.equal([c])
}

pub fn g1_with_no_revocations_everything_accepted_survives_test() {
  let #(l, a, b, c) = g1()
  ledger.blast_radius(l, []) |> should.equal([])
  ledger.survivors(l, []) |> should.equal(canonical.sort_digests([a, b, c]))
}

pub fn g1_revoking_an_unrelated_rule_set_kills_nothing_test() {
  let #(l, _, _, _) = g1()
  ledger.blast_radius(l, [ledger.RevokeRuleSet(author(), dig(0x99))])
  |> should.equal([])
}

pub fn g1_revoking_the_right_hash_by_the_wrong_author_kills_nothing_test() {
  // Authorization and revocation are both pinned to (author, exact hash), not
  // to an author alone.
  let #(l, _, _, _) = g1()
  ledger.blast_radius(l, [ledger.RevokeRuleSet(key(0xEE), rule_set())])
  |> should.equal([])
}

// ── G2: a depth-5 chain ───────────────────────────────────────────────────────

pub fn g2_revoking_the_root_of_a_depth_five_chain_kills_all_five_test() {
  let d1 = dig(1)
  let d2 = dig(2)
  let d3 = dig(3)
  let d4 = dig(4)
  let d5 = dig(5)
  let l =
    of([
      accepted(d1, [], [trust.RuleSetTrust(author(), rule_set())]),
      accepted(d2, [d1], []),
      accepted(d3, [d2], []),
      accepted(d4, [d3], []),
      accepted(d5, [d4], []),
    ])
  ledger.blast_radius(l, [revoke_fixture()])
  |> should.equal(canonical.sort_digests([d1, d2, d3, d4, d5]))
  ledger.survivors(l, [revoke_fixture()]) |> should.equal([])
}

pub fn g2_revoking_the_middle_kills_only_downstream_test() {
  // The chain's earlier links are untouched: revocation propagates from a
  // dependency to its dependents, never backwards.
  let d1 = dig(1)
  let d2 = dig(2)
  let d3 = dig(3)
  let d4 = dig(4)
  let d5 = dig(5)
  let l =
    of([
      accepted(d1, [], []),
      accepted(d2, [d1], []),
      accepted(d3, [d2], [trust.RuleSetTrust(author(), rule_set())]),
      accepted(d4, [d3], []),
      accepted(d5, [d4], []),
    ])
  ledger.blast_radius(l, [revoke_fixture()])
  |> should.equal(canonical.sort_digests([d3, d4, d5]))
  ledger.survivors(l, [revoke_fixture()])
  |> should.equal(canonical.sort_digests([d1, d2]))
}

// ── G3: a diamond ─────────────────────────────────────────────────────────────

pub fn g3_a_diamonds_shared_ancestor_kills_both_branches_and_the_join_test() {
  //       root
  //       /  \
  //   left    right
  //       \  /
  //       join
  let root = dig(0x10)
  let left = dig(0x11)
  let right = dig(0x12)
  let join = dig(0x13)
  let l =
    of([
      accepted(root, [], [trust.RuleSetTrust(author(), rule_set())]),
      accepted(left, [root], []),
      accepted(right, [root], []),
      accepted(join, [left, right], []),
    ])
  let radius = ledger.blast_radius(l, [revoke_fixture()])

  // Each listed exactly once, despite the join being reachable by two paths.
  radius |> should.equal(canonical.sort_digests([root, left, right, join]))
  list.length(radius) |> should.equal(4)
  list.length(list.unique(radius)) |> should.equal(4)
  ledger.survivors(l, [revoke_fixture()]) |> should.equal([])
}

// ── G4: purist survival ───────────────────────────────────────────────────────

pub fn g4_a_purist_artifact_survives_every_rule_set_and_host_revocation_test() {
  // Empty trust set, no axioms, no capabilities. There is nothing to revoke
  // that could reach it -- which is the point of purist artifacts.
  let purist = dig(0xC0)
  let l = of([accepted(purist, [], [])])
  let revocations = [
    ledger.RevokeRuleSet(author(), rule_set()),
    ledger.RevokeRuleSet(key(1), dig(1)),
    ledger.RevokeRuleSet(key(2), dig(2)),
    ledger.RevokeHost(host()),
    ledger.RevokeHost(key(3)),
    ledger.RevokeAxiom(dig(4)),
  ]
  list.each(revocations, fn(r) {
    ledger.blast_radius(l, [r]) |> should.equal([])
    ledger.survivors(l, [r]) |> should.equal([purist])
  })
  // And all of them at once.
  ledger.survivors(l, revocations) |> should.equal([purist])
}

pub fn g4_a_purist_artifact_does_not_survive_revocation_of_its_own_basis_test() {
  // The one thing that does reach it. A basis revocation is a statement about
  // the kernel and context, which every artifact depends on by construction.
  let purist = dig(0xC0)
  let l = of([accepted(purist, [], [])])
  ledger.survivors(l, [ledger.RevokeBasis(basis_digest())]) |> should.equal([])
}

// ── G5: cycles ────────────────────────────────────────────────────────────────

pub fn g5_a_cyclic_dependency_graph_terminates_test() {
  // Adversaries supply receipts. Nothing here may rest on the graph being a
  // DAG.
  let x = dig(0x21)
  let y = dig(0x22)
  let z = dig(0x23)
  let l =
    of([
      accepted(x, [y], []),
      accepted(y, [z], []),
      accepted(z, [x], [trust.RuleSetTrust(author(), rule_set())]),
    ])
  ledger.blast_radius(l, [revoke_fixture()])
  |> should.equal(canonical.sort_digests([x, y, z]))
  ledger.survivors(l, [revoke_fixture()]) |> should.equal([])
}

pub fn g5_a_cycle_with_nothing_revoked_kills_nothing_test() {
  let x = dig(0x21)
  let y = dig(0x22)
  let l = of([accepted(x, [y], []), accepted(y, [x], [])])
  ledger.blast_radius(l, []) |> should.equal([])
  ledger.survivors(l, []) |> should.equal(canonical.sort_digests([x, y]))
}

pub fn g5_a_self_referential_receipt_terminates_test() {
  let x = dig(0x30)
  let l = of([accepted(x, [x], [trust.RuleSetTrust(author(), rule_set())])])
  ledger.blast_radius(l, [revoke_fixture()]) |> should.equal([x])
}

pub fn g5_a_long_cycle_does_not_overflow_the_stack_test() {
  // Two hundred links, each depending on the next, the last back to the first.
  let ids = list.map(upto(200), dig)
  let assert [first, ..] = ids
  let receipts =
    list.index_map(ids, fn(id, i) {
      let next = case list.drop(ids, i + 1) {
        [n, ..] -> n
        [] -> first
      }
      accepted(id, [next], [])
    })
  let l = of(receipts)
  ledger.blast_radius(l, []) |> should.equal([])
  list.length(ledger.survivors(l, [])) |> should.equal(200)
  // And with one link revoked, the whole cycle goes.
  let poisoned =
    of([
      accepted(first, [dig(2)], [trust.RuleSetTrust(author(), rule_set())]),
      ..list.drop(receipts, 1)
    ])
  list.length(ledger.blast_radius(poisoned, [revoke_fixture()]))
  |> should.equal(200)
}

// ── G6: idempotence ───────────────────────────────────────────────────────────

pub fn g6_add_is_idempotent_test() {
  let r = accepted(dig(1), [], [])
  let once = ledger.add(ledger.new(), r)
  let hundred =
    list.fold(list.repeat(r, 100), ledger.new(), fn(l, x) { ledger.add(l, x) })
  ledger.all_receipts(once) |> should.equal(ledger.all_receipts(hundred))
  list.length(ledger.all_receipts(hundred)) |> should.equal(1)
  ledger.artifacts(hundred) |> should.equal([dig(1)])
}

pub fn g6_add_basis_is_idempotent_test() {
  let l = list.fold(list.repeat(a_basis(), 50), ledger.new(), ledger.add_basis)
  ledger.survivors(ledger.add(l, accepted(dig(1), [], [])), [])
  |> should.equal([dig(1)])
}

pub fn g6_two_distinct_receipts_for_one_artifact_are_both_kept_test() {
  // Idempotence is by receipt digest, not by artifact: an artifact can hold
  // several genuinely different receipts, and the conflicts query depends on
  // that.
  let a = dig(1)
  let l =
    of([
      accepted(a, [], []),
      rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
    ])
  list.length(ledger.receipts_for(l, a)) |> should.equal(2)
}

pub fn g6_insertion_order_does_not_affect_any_answer_test() {
  let a = accepted(dig(1), [], [trust.RuleSetTrust(author(), rule_set())])
  let b = accepted(dig(2), [dig(1)], [])
  let c = accepted(dig(3), [], [])
  let forward = of([a, b, c])
  let backward = of([c, b, a])
  ledger.all_receipts(forward) |> should.equal(ledger.all_receipts(backward))
  ledger.blast_radius(forward, [revoke_fixture()])
  |> should.equal(ledger.blast_radius(backward, [revoke_fixture()]))
  ledger.survivors(forward, []) |> should.equal(ledger.survivors(backward, []))
}

// ── G7: conflicts ─────────────────────────────────────────────────────────────

pub fn g7_conflicts_detects_a_planted_contradictory_pair_test() {
  // Same artifact, same basis, opposite verdicts. Either the kernel is
  // nondeterministic or somebody is equivocating; both need to be loud.
  let a = dig(1)
  let l =
    of([
      accepted(a, [], []),
      rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
    ])
  let found = ledger.conflicts(l)
  list.length(found) |> should.equal(1)
  let assert [#(artifact, receipts)] = found
  artifact |> should.equal(a)
  list.length(receipts) |> should.equal(2)
}

pub fn g7_conflicts_is_empty_on_a_clean_ledger_test() {
  let #(l, _, _, _) = g1()
  ledger.conflicts(l) |> should.equal([])
  ledger.conflicts(ledger.new()) |> should.equal([])
}

pub fn g7_accepted_versus_exhausted_under_one_basis_is_a_conflict_test() {
  let a = dig(1)
  let l = of([accepted(a, [], []), rcpt(a, [], [], [], receipt.Exhausted)])
  list.length(ledger.conflicts(l)) |> should.equal(1)
}

pub fn g7_different_bases_disagreeing_is_not_a_conflict_test() {
  // This is the system working. Two contexts can legitimately reach different
  // answers -- that is what a basis is for.
  let a = dig(1)
  let other =
    receipt.Receipt(
      ..rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
      basis: dig(0xEE),
    )
  let l = of([accepted(a, [], []), other])
  ledger.conflicts(l) |> should.equal([])
}

pub fn g7_identical_receipts_are_never_a_conflict_test() {
  let a = dig(1)
  let l = of([accepted(a, [], []), accepted(a, [], [])])
  ledger.conflicts(l) |> should.equal([])
}

// ── G8: only Accepted receipts confer warrant ─────────────────────────────────

pub fn g8_exhausted_receipts_never_appear_in_survivors_test() {
  // Under zero revocations, so the only reason to be absent is the verdict.
  let a = dig(1)
  let l = of([rcpt(a, [], [], [], receipt.Exhausted)])
  ledger.survivors(l, []) |> should.equal([])
  ledger.blast_radius(l, []) |> should.equal([])
}

pub fn g8_rejected_receipts_never_appear_in_survivors_test() {
  let a = dig(1)
  let l = of([rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch))])
  ledger.survivors(l, []) |> should.equal([])
}

pub fn g8_an_artifact_the_ledger_never_heard_of_is_not_a_survivor_test() {
  // Unknown is not safe. Silence is not a pass.
  let #(l, _, _, _) = g1()
  list.contains(ledger.survivors(l, []), dig(0xDEAD)) |> should.be_false
  ledger.get(l, dig(0xDEAD)) |> should.equal(None)
}

pub fn g8_without_accepted_verdict_lists_exactly_those_artifacts_test() {
  let good = dig(1)
  let bad = dig(2)
  let unfinished = dig(3)
  let l =
    of([
      accepted(good, [], []),
      rcpt(bad, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
      rcpt(unfinished, [], [], [], receipt.Exhausted),
    ])
  ledger.without_accepted_verdict(l)
  |> should.equal(canonical.sort_digests([bad, unfinished]))
}

pub fn g8_a_dependent_of_a_non_survivor_is_still_reported_honestly_test() {
  // B depends on A, and A only ever failed to check. B is not killed by a
  // revocation -- nothing was revoked -- but A is not a survivor, so a
  // consumer reading `survivors` sees B without A and can draw its own
  // conclusion. The ledger does not silently promote A.
  let a = dig(1)
  let b = dig(2)
  let l =
    of([
      rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
      accepted(b, [a], []),
    ])
  ledger.survivors(l, []) |> should.equal([b])
  ledger.without_accepted_verdict(l) |> should.equal([a])
}

// ── get ───────────────────────────────────────────────────────────────────────

pub fn get_prefers_an_accepted_receipt_test() {
  let a = dig(1)
  let l =
    of([
      rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch)),
      accepted(a, [], []),
    ])
  case ledger.get(l, a) {
    Some(r) -> r.verdict |> should.equal(receipt.Accepted)
    None -> should.fail()
  }
}

pub fn get_is_deterministic_regardless_of_insertion_order_test() {
  let a = dig(1)
  let x = rcpt(a, [], [], [], receipt.Rejected(receipt.TypeMismatch))
  let y = rcpt(a, [], [], [], receipt.Exhausted)
  ledger.get(of([x, y]), a) |> should.equal(ledger.get(of([y, x]), a))
}

pub fn get_returns_none_for_an_empty_ledger_test() {
  ledger.get(ledger.new(), dig(1)) |> should.equal(None)
}

// ── the other revocation kinds ────────────────────────────────────────────────

pub fn revoking_a_host_kills_artifacts_that_trust_it_test() {
  let a = dig(1)
  let b = dig(2)
  let l =
    of([
      accepted(a, [], [trust.HostTrust(host(), dig(0x77))]),
      accepted(b, [], [trust.HostTrust(key(0xEE), dig(0x77))]),
    ])
  ledger.blast_radius(l, [ledger.RevokeHost(host())]) |> should.equal([a])
  ledger.survivors(l, [ledger.RevokeHost(host())]) |> should.equal([b])
}

pub fn revoking_a_host_ignores_which_procedure_it_ran_test() {
  // A compromised host is compromised for every procedure it ever ran.
  let a = dig(1)
  let l =
    of([
      accepted(a, [], [
        trust.HostTrust(host(), dig(1)),
        trust.HostTrust(host(), dig(2)),
      ]),
    ])
  ledger.blast_radius(l, [ledger.RevokeHost(host())]) |> should.equal([a])
}

pub fn revoking_an_axiom_kills_artifacts_that_assume_it_test() {
  let a = dig(1)
  let b = dig(2)
  let l =
    of([
      rcpt(a, [], [], [dig(0x88)], receipt.Accepted),
      rcpt(b, [], [], [dig(0x99)], receipt.Accepted),
    ])
  ledger.blast_radius(l, [ledger.RevokeAxiom(dig(0x88))]) |> should.equal([a])
  ledger.survivors(l, [ledger.RevokeAxiom(dig(0x88))]) |> should.equal([b])
}

pub fn revoking_an_axiom_kills_anything_depending_on_it_directly_test() {
  // Even if the dependent's own axiom list somehow omits it: a revoked object
  // is dead, and depending on a dead object is fatal.
  let a = dig(1)
  let l = of([accepted(a, [dig(0x88)], [])])
  ledger.blast_radius(l, [ledger.RevokeAxiom(dig(0x88))]) |> should.equal([a])
}

pub fn revoking_a_kernel_kills_receipts_issued_under_it_test() {
  let a = dig(1)
  let l = of([accepted(a, [], [])])
  ledger.blast_radius(l, [ledger.RevokeKernel(kernel_id)]) |> should.equal([a])
  ledger.blast_radius(l, [ledger.RevokeKernel("some-other-kernel/9.9")])
  |> should.equal([])
}

pub fn revoking_a_kernel_fails_closed_on_an_unregistered_basis_test() {
  // The ledger cannot show this receipt was NOT issued under the revoked
  // kernel, so it must not claim it survived. Harsh, and the right direction:
  // the alternative is an artifact outliving a kernel revocation because
  // nobody wrote down which kernel checked it.
  let a = dig(1)
  let unregistered = list.fold([accepted(a, [], [])], ledger.new(), ledger.add)
  ledger.blast_radius(unregistered, [ledger.RevokeKernel("anything")])
  |> should.equal([a])
  ledger.survivors(unregistered, [ledger.RevokeKernel("anything")])
  |> should.equal([])
}

pub fn multiple_revocations_are_the_union_test() {
  let #(l, a, b, c) = g1()
  ledger.blast_radius(l, [
    revoke_fixture(),
    ledger.RevokeBasis(dig(0xEE)),
  ])
  |> should.equal(canonical.sort_digests([a, b]))

  ledger.blast_radius(l, [
    revoke_fixture(),
    ledger.RevokeBasis(basis_digest()),
  ])
  |> should.equal(canonical.sort_digests([a, b, c]))
}

pub fn results_are_sorted_and_deduped_test() {
  let #(l, _, _, _) = g1()
  let radius = ledger.blast_radius(l, [revoke_fixture()])
  radius |> should.equal(canonical.sort_digests(radius))
  list.length(radius) |> should.equal(list.length(list.unique(radius)))
  let s = ledger.survivors(l, [])
  s |> should.equal(canonical.sort_digests(s))
}

pub fn blast_radius_and_survivors_are_disjoint_test() {
  let #(l, _, _, _) = g1()
  let revocations = [revoke_fixture()]
  let radius = ledger.blast_radius(l, revocations)
  list.each(ledger.survivors(l, revocations), fn(s) {
    list.contains(radius, s) |> should.be_false
  })
}
