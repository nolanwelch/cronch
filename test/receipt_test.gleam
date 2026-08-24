/// Part F: receipts.
import cronch/canonical
import cronch/capability
import cronch/digest
import cronch/kernel
import cronch/pubkey
import cronch/receipt
import cronch/serialize
import cronch/term
import cronch/trust
import gleam/bit_array
import gleam/int
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should
import support/corpus

const kernel_id = "cronch-kernel/0.1.0"

const budget = 100_000

fn key(b: Int) -> pubkey.PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<b:size(256)>>)
}

fn dig(b: Int) -> digest.Digest {
  digest.Digest(digest.Blake3, <<b:size(256)>>)
}

fn issue(c: corpus.Case) -> receipt.Receipt {
  receipt.issue(kernel_id, c.environment, c.provenance, budget, c.term, c.typ)
}

fn named(name: String) -> corpus.Case {
  let assert [c] = list.filter(corpus.cases(), fn(c) { c.name == name })
  c
}

/// A synthetic receipt, so the tamper tests can reach fields that no corpus
/// case happens to populate.
fn sample() -> receipt.Receipt {
  receipt.canonicalize(receipt.Receipt(
    version: 1,
    basis: dig(1),
    artifact: dig(2),
    spec: dig(3),
    deps: [dig(5), dig(4)],
    axioms: [dig(6)],
    trust_set: [
      trust.RuleSetTrust(key(2), dig(8)),
      trust.HostTrust(key(1), dig(7)),
    ],
    capabilities: [dig(9)],
    fuel_declared: 1000,
    fuel_used: 42,
    verdict: receipt.Accepted,
  ))
}

// ── F1: round trip ────────────────────────────────────────────────────────────

pub fn f1_round_trip_accepted_test() {
  let r = sample()
  receipt.decode(receipt.encode(r)) |> should.equal(Ok(r))
}

pub fn f1_round_trip_every_reject_reason_test() {
  // All ten, individually. A reason that does not survive the wire is a reason
  // replay would spuriously fail on.
  list.each(receipt.all_reject_reasons(), fn(reason) {
    let r = receipt.Receipt(..sample(), verdict: receipt.Rejected(reason))
    receipt.decode(receipt.encode(r)) |> should.equal(Ok(r))
  })
}

pub fn f1_round_trip_exhausted_test() {
  let r = receipt.Receipt(..sample(), verdict: receipt.Exhausted)
  receipt.decode(receipt.encode(r)) |> should.equal(Ok(r))
}

pub fn f1_reason_tags_are_pairwise_distinct_test() {
  let tags = list.map(receipt.all_reject_reasons(), receipt.reason_tag)
  list.length(list.unique(tags)) |> should.equal(10)
}

pub fn f1_round_trip_with_empty_lists_test() {
  let r =
    receipt.canonicalize(
      receipt.Receipt(
        ..sample(),
        deps: [],
        axioms: [],
        trust_set: [],
        capabilities: [],
        fuel_declared: 0,
        fuel_used: 0,
      ),
    )
  receipt.decode(receipt.encode(r)) |> should.equal(Ok(r))
}

pub fn f1_round_trip_every_corpus_receipt_test() {
  list.each(corpus.cases(), fn(c) {
    let r = issue(c)
    receipt.decode(receipt.encode(r)) |> should.equal(Ok(r))
  })
}

// ── issue never fails, and negative results are first-class ───────────────────

pub fn issue_produces_a_receipt_for_every_corpus_case_test() {
  // Including the ones that do not typecheck and the one that cannot finish.
  list.each(corpus.cases(), fn(c) {
    let r = issue(c)
    r.version |> should.equal(1)
    let expected = case c.expectation {
      corpus.ExpectAccept -> receipt.Accepted
      corpus.ExpectReject -> r.verdict
      corpus.ExpectExhaust -> receipt.Exhausted
    }
    case c.expectation {
      corpus.ExpectAccept -> r.verdict |> should.equal(expected)
      corpus.ExpectExhaust -> r.verdict |> should.equal(receipt.Exhausted)
      corpus.ExpectReject ->
        case r.verdict {
          receipt.Rejected(_) -> Nil
          _ -> should.fail()
        }
    }
  })
}

pub fn a_rejection_carries_the_right_closed_reason_test() {
  issue(named("reject/unbound")).verdict
  |> should.equal(receipt.Rejected(receipt.UnboundVariable))
  issue(named("reject/mismatch")).verdict
  |> should.equal(receipt.Rejected(receipt.TypeMismatch))
  issue(named("reject/not-a-function")).verdict
  |> should.equal(receipt.Rejected(receipt.NotAFunction))
  issue(named("reject/unresolved-const")).verdict
  |> should.equal(receipt.Rejected(receipt.UnknownConstant))
}

pub fn an_exhausted_receipt_is_not_a_rejection_test() {
  let r = issue(named("exhaust/self-rewriting-const"))
  r.verdict |> should.equal(receipt.Exhausted)
  case r.verdict {
    receipt.Rejected(_) -> should.fail()
    receipt.Accepted -> should.fail()
    receipt.Exhausted -> Nil
  }
}

pub fn a_policy_refusal_is_recorded_as_a_rejection_test() {
  // The artifact typechecks. Under the purist policy it is refused anyway,
  // and the refusal is recorded rather than turning into a silent acceptance.
  let c = named("rules/annotation-only")
  let r =
    receipt.issue_under_policy(
      kernel_id,
      c.environment,
      c.provenance,
      trust.empty_policy(),
      budget,
      c.term,
      c.typ,
    )
  r.verdict |> should.equal(receipt.Rejected(receipt.UnauthorizedRuleSet))

  // Authorizing that exact rule set flips it.
  let permitted =
    receipt.issue_under_policy(
      kernel_id,
      c.environment,
      c.provenance,
      trust.policy_with_rule_sets([#(corpus.author(), corpus.rule_set_hash())]),
      budget,
      c.term,
      c.typ,
    )
  permitted.verdict |> should.equal(receipt.Accepted)
}

pub fn an_unauthorized_host_is_recorded_as_such_test() {
  let c = named("host/trusted-node")
  let r =
    receipt.issue_under_policy(
      kernel_id,
      c.environment,
      c.provenance,
      trust.empty_policy(),
      budget,
      c.term,
      c.typ,
    )
  r.verdict |> should.equal(receipt.Rejected(receipt.UnauthorizedHost))
}

// ── receipt contents ──────────────────────────────────────────────────────────

pub fn deps_are_direct_references_only_test() {
  // `lam (x : S) => x` mentions S directly. W is reachable only through S's
  // declared type, so it is an axiom but NOT a dep -- deps stay O(the term).
  let r = issue(named("rules/annotation-only"))
  r.deps |> should.equal([corpus.s()])
  list.contains(r.axioms, corpus.w()) |> should.be_true
  list.contains(r.deps, corpus.w()) |> should.be_false
}

pub fn a_trusted_procedure_is_a_dep_test() {
  // Revoking the object a Trusted node names must be able to reach this
  // artifact, so the procedure counts as a direct reference.
  let r = issue(named("host/trusted-node"))
  list.contains(r.deps, corpus.proc()) |> should.be_true
}

pub fn the_trust_set_comes_from_the_derivation_test() {
  // The Part C fix, visible in the receipt: the annotation-only artifact's
  // receipt names the rule set its acceptance rested on.
  issue(named("rules/annotation-only")).trust_set
  |> should.equal([
    trust.RuleSetTrust(corpus.author(), corpus.rule_set_hash()),
  ])
}

pub fn a_purist_receipt_has_empty_sets_test() {
  let r = issue(named("purist/identity"))
  r.trust_set |> should.equal([])
  r.axioms |> should.equal([])
  r.deps |> should.equal([])
  // `capabilities` names the digest of the EMPTY capability set, not an empty
  // list: "reaches nothing" is a computed fact with an identity, and must not
  // look the same as "nobody computed it".
  r.capabilities
  |> should.equal([
    capability.digest(digest.Blake3, capability.empty()),
  ])
}

pub fn every_set_field_is_sorted_and_deduped_test() {
  list.each(corpus.cases(), fn(c) {
    let r = issue(c)
    r.deps |> should.equal(canonical.sort_digests(r.deps))
    r.axioms |> should.equal(canonical.sort_digests(r.axioms))
    receipt.canonicalize(r) |> should.equal(r)
  })
}

pub fn fuel_declared_is_the_budget_and_fuel_used_the_cost_test() {
  let r = issue(named("rules/fst-in-conversion"))
  r.fuel_declared |> should.equal(budget)
  { r.fuel_used > 0 } |> should.be_true
  { r.fuel_used <= r.fuel_declared } |> should.be_true
}

pub fn a_cost_overrun_yields_exhausted_not_accepted_test() {
  // The mathematics works out. The claim about cost does not, so there is no
  // verdict -- and specifically not an acceptance.
  let c = named("rules/fst-in-conversion")
  let honest = issue(c)
  let understated =
    receipt.issue(
      kernel_id,
      c.environment,
      c.provenance,
      honest.fuel_used - 1,
      c.term,
      c.typ,
    )
  understated.verdict |> should.equal(receipt.Exhausted)
}

// ── F4: stability ─────────────────────────────────────────────────────────────

pub fn f4_issuing_twice_yields_identical_bytes_test() {
  // For all three verdict kinds, from freshly built environments each time.
  list.each(corpus.cases(), fn(c) {
    let a =
      receipt.issue(
        kernel_id,
        corpus.environment(),
        corpus.provenance(),
        budget,
        c.term,
        c.typ,
      )
    let b =
      receipt.issue(
        kernel_id,
        corpus.environment(),
        corpus.provenance(),
        budget,
        c.term,
        c.typ,
      )
    receipt.encode(a) |> should.equal(receipt.encode(b))
    receipt.digest(digest.Blake3, a)
    |> should.equal(receipt.digest(digest.Blake3, b))
  })
}

pub fn f4_all_three_verdict_kinds_are_covered_by_the_corpus_test() {
  // Guards the test above against quietly covering only one verdict kind.
  let verdicts = list.map(corpus.cases(), fn(c) { issue(c).verdict })
  list.contains(verdicts, receipt.Accepted) |> should.be_true
  list.contains(verdicts, receipt.Exhausted) |> should.be_true
  list.any(verdicts, fn(v) {
    case v {
      receipt.Rejected(_) -> True
      _ -> False
    }
  })
  |> should.be_true
}

pub fn f4_field_order_is_fixed_test() {
  // Two receipts differing in one field must differ in bytes -- otherwise a
  // field is not actually being encoded.
  let base = sample()
  let variants = [
    receipt.Receipt(..base, basis: dig(99)),
    receipt.Receipt(..base, artifact: dig(99)),
    receipt.Receipt(..base, spec: dig(99)),
    receipt.Receipt(..base, deps: [dig(99)]),
    receipt.Receipt(..base, axioms: [dig(99)]),
    receipt.Receipt(..base, trust_set: []),
    receipt.Receipt(..base, capabilities: []),
    receipt.Receipt(..base, fuel_declared: 999),
    receipt.Receipt(..base, fuel_used: 999),
    receipt.Receipt(..base, verdict: receipt.Exhausted),
  ]
  let encodings = list.map([base, ..variants], receipt.encode)
  list.length(list.unique(encodings)) |> should.equal(11)
}

// ── F2: replay succeeds on honest receipts ────────────────────────────────────

/// An environment whose store also resolves every corpus artifact and spec by
/// content address, so `replay` can fetch what a receipt names.
fn replay_environment() -> kernel.Environment {
  let base = corpus.environment()
  let extra =
    list.flat_map(corpus.cases(), fn(c) {
      [
        #(receipt.term_address(c.term), c.term),
        #(receipt.term_address(c.typ), c.typ),
      ]
    })
  kernel.Environment(..base, definitions: fn(d) {
    case list.find(extra, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> base.definitions(d)
    }
  })
}

pub fn f2_replay_succeeds_on_every_honest_receipt_test() {
  list.each(corpus.cases(), fn(c) {
    let r = issue(c)
    receipt.replay_terms(
      r,
      kernel_id,
      c.environment,
      c.provenance,
      c.term,
      c.typ,
    )
    |> should.be_true
  })
}

pub fn f2_replay_resolves_the_artifact_from_the_store_test() {
  let c = named("purist/identity")
  let environment = replay_environment()
  let r =
    receipt.issue(kernel_id, environment, c.provenance, budget, c.term, c.typ)
  receipt.replay(r, kernel_id, environment, c.provenance) |> should.be_true
}

pub fn f2_replay_fails_when_the_artifact_is_not_in_the_store_test() {
  // Absence of the thing being attested is not evidence for the attestation.
  let c = named("purist/identity")
  let r = issue(c)
  receipt.replay(r, kernel_id, c.environment, c.provenance) |> should.be_false
}

pub fn f2_replay_fails_under_a_different_kernel_id_test() {
  // The verifier's own kernel identity, never the receipt's claim about
  // itself. A different kernel cannot vouch for a check it did not perform.
  let c = named("purist/identity")
  let r = issue(c)
  receipt.replay_terms(
    r,
    "some-other-kernel/9.9",
    c.environment,
    c.provenance,
    c.term,
    c.typ,
  )
  |> should.be_false
}

pub fn f2_replay_fails_on_the_wrong_terms_test() {
  // Handing replay a different artifact must not make a receipt verify.
  let r = issue(named("purist/identity"))
  let other = named("purist/sort")
  receipt.replay_terms(
    r,
    kernel_id,
    other.environment,
    other.provenance,
    other.term,
    other.typ,
  )
  |> should.be_false
}

// ── F3: replay fails on each tamper, as separate named tests ──────────────────

fn honest() -> #(corpus.Case, receipt.Receipt) {
  let c = named("rules/fst-in-conversion")
  #(c, issue(c))
}

fn replays(c: corpus.Case, r: receipt.Receipt) -> Bool {
  receipt.replay_terms(r, kernel_id, c.environment, c.provenance, c.term, c.typ)
}

pub fn f3_tamper_fuel_used_incremented_test() {
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, fuel_used: r.fuel_used + 1))
  |> should.be_false
}

pub fn f3_tamper_fuel_used_decremented_test() {
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, fuel_used: r.fuel_used - 1))
  |> should.be_false
}

pub fn f3_tamper_trust_pair_removed_test() {
  let #(c, r) = honest()
  { r.trust_set != [] } |> should.be_true
  replays(c, receipt.Receipt(..r, trust_set: [])) |> should.be_false
}

pub fn f3_tamper_trust_pair_added_test() {
  let #(c, r) = honest()
  replays(
    c,
    receipt.Receipt(..r, trust_set: [
      trust.HostTrust(key(0xCC), dig(0xCC)),
      ..r.trust_set
    ]),
  )
  |> should.be_false
}

pub fn f3_tamper_dep_added_test() {
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, deps: [dig(0xDD), ..r.deps]))
  |> should.be_false
}

pub fn f3_tamper_dep_removed_test() {
  let #(c, r) = honest()
  { r.deps != [] } |> should.be_true
  let assert [_, ..rest] = r.deps
  replays(c, receipt.Receipt(..r, deps: rest)) |> should.be_false
}

pub fn f3_tamper_axiom_removed_test() {
  let #(c, r) = honest()
  { r.axioms != [] } |> should.be_true
  let assert [_, ..rest] = r.axioms
  replays(c, receipt.Receipt(..r, axioms: rest)) |> should.be_false
}

pub fn f3_tamper_verdict_flipped_rejected_to_accepted_test() {
  // The attack this whole object exists to stop.
  let c = named("reject/mismatch")
  let r = issue(c)
  case r.verdict {
    receipt.Rejected(_) -> Nil
    _ -> should.fail()
  }
  replays(c, receipt.Receipt(..r, verdict: receipt.Accepted))
  |> should.be_false
}

pub fn f3_tamper_verdict_flipped_exhausted_to_accepted_test() {
  let c = named("exhaust/self-rewriting-const")
  let r = issue(c)
  r.verdict |> should.equal(receipt.Exhausted)
  replays(c, receipt.Receipt(..r, verdict: receipt.Accepted))
  |> should.be_false
}

pub fn f3_tamper_spec_replaced_with_a_weaker_type_test() {
  // Claiming a proof of something easier than what was actually checked.
  let #(c, r) = honest()
  let weaker = term.Sort(0)
  replays(c, receipt.Receipt(..r, spec: receipt.term_address(weaker)))
  |> should.be_false
}

pub fn f3_tamper_basis_digest_replaced_test() {
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, basis: dig(0xBB))) |> should.be_false
}

pub fn f3_tamper_fuel_declared_lowered_below_the_true_cost_test() {
  // fuel_declared is part of the QUESTION, not the answer: it is the budget
  // the check was run under. Raising it describes a different, weaker check,
  // and replay -- which re-runs under whatever budget the receipt states --
  // faithfully confirms that different check. That is correct behaviour, and
  // it is safe, because a larger budget cannot manufacture a verdict.
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, fuel_declared: r.fuel_declared + 1))
  |> should.be_true

  // Lowering it below the cost actually incurred is a different matter: the
  // check no longer completes within the stated budget, so re-running yields
  // Exhausted while the receipt claims Accepted.
  let understated = receipt.Receipt(..r, fuel_declared: r.fuel_used - 1)
  replays(c, understated) |> should.be_false
}

pub fn f3_tamper_capability_added_test() {
  let #(c, r) = honest()
  replays(c, receipt.Receipt(..r, capabilities: [dig(0xAA)]))
  |> should.be_false
}

// ── F6: version ───────────────────────────────────────────────────────────────

pub fn f6_a_receipt_declaring_a_version_other_than_one_is_refused_test() {
  list.each([0, 2, 3, 99, 4_294_967_295], fn(v) {
    let bytes = receipt.encode(receipt.Receipt(..sample(), version: v))
    case v == 1 {
      True -> {
        receipt.decode(bytes) |> should.be_ok
        Nil
      }
      False ->
        receipt.decode(bytes)
        |> should.equal(Error(receipt.UnsupportedVersion(v)))
    }
  })
}

pub fn f6_version_is_checked_before_any_other_field_is_interpreted_test() {
  // A future version's fields could mean anything, so reading them under this
  // version's layout would be guessing. Truncated-after-version bytes must
  // report the version problem, not a field problem.
  let bytes = <<0x02, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x07>>
  receipt.decode(bytes) |> should.equal(Error(receipt.UnsupportedVersion(7)))
}

// ── F5: hostile decode ────────────────────────────────────────────────────────

/// A deterministic linear congruential generator. Hand-rolled: no new
/// dependencies, and a fixed seed means this test is the same test on every
/// run, machine and target. A fuzzer whose corpus changes between runs is a
/// flaky test, not a stronger one.
fn lcg(state: Int) -> Int {
  int.bitwise_and(state * 1_103_515_245 + 12_345, 0x7FFFFFFF)
}

fn random_bytes(state: Int, len: Int, acc: BitArray) -> #(BitArray, Int) {
  case len <= 0 {
    True -> #(acc, state)
    False -> {
      let next = lcg(state)
      let byte = int.bitwise_and(int.bitwise_shift_right(next, 8), 0xFF)
      random_bytes(next, len - 1, bit_array.concat([acc, <<byte>>]))
    }
  }
}

/// Every prefix of `b`, longest first.
fn truncations(b: BitArray, n: Int) -> List(BitArray) {
  case n < 0 {
    True -> []
    False -> [take(b, n), ..truncations(b, n - 1)]
  }
}

fn take(b: BitArray, n: Int) -> BitArray {
  let bits = n * 8
  case b {
    <<head:bits-size(bits), _:bits>> -> head
    _ -> b
  }
}

/// Flip one byte of `b` at `index` to `value`.
fn mutate(b: BitArray, index: Int, value: Int) -> BitArray {
  let head_bits = index * 8
  case b {
    <<head:bits-size(head_bits), _, tail:bits>> ->
      bit_array.concat([head, <<value>>, tail])
    _ -> b
  }
}

pub fn f5_decode_never_accepts_a_truncated_receipt_test() {
  // Every length from empty to one byte short, exhaustively.
  let bytes = receipt.encode(sample())
  let size = bit_array.byte_size(bytes)
  truncations(bytes, size - 1)
  |> list.each(fn(prefix) { receipt.decode(prefix) |> should.be_error })
  // And the untruncated one still decodes, so the test is not vacuous.
  receipt.decode(bytes) |> should.be_ok
}

pub fn f5_decode_survives_single_byte_mutations_test() {
  // Every byte position, several values each. A mutation may legitimately
  // still decode (a different but well-formed receipt); what must never
  // happen is a crash, a hang, or an unbounded allocation.
  let bytes = receipt.encode(sample())
  let size = bit_array.byte_size(bytes)
  list.each(positions(size - 1), fn(i) {
    list.each([0x00, 0x01, 0x7F, 0x80, 0xFE, 0xFF], fn(v) {
      let mutated = mutate(bytes, i, v)
      case receipt.decode(mutated) {
        // Whatever comes back must re-encode to the exact bytes it came from.
        // Anything weaker would mean one receipt has two byte
        // representations, and `replay` compares bytes.
        Ok(r) -> receipt.encode(r) |> should.equal(mutated)
        Error(_) -> Nil
      }
    })
  })
}

pub fn f5_decode_rejects_thousands_of_random_byte_strings_test() {
  // Fixed seed, so this is a deterministic test rather than a lottery.
  fuzz_random(20_260_824, 3000)
}

fn fuzz_random(state: Int, remaining: Int) -> Nil {
  case remaining <= 0 {
    True -> Nil
    False -> {
      let next = lcg(state)
      let len = int.bitwise_and(next, 0x3F)
      let #(bytes, after) = random_bytes(next, len, <<>>)
      case receipt.decode(bytes) {
        Ok(r) -> receipt.encode(r) |> should.equal(bytes)
        Error(_) -> Nil
      }
      fuzz_random(after, remaining - 1)
    }
  }
}

pub fn f5_decode_rejects_receipts_declaring_absurd_list_lengths_test() {
  // A well-formed header followed by a four-billion-element list declaration.
  // Must fail on the first element it cannot read, not reserve for it.
  let header = <<
    0x02, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x01, 0x00, 1:size(256), 0x00,
    2:size(256), 0x00, 3:size(256),
  >>
  let absurd_counts = [
    <<0xFF, 0xFF, 0xFF, 0xFF, 0x0F>>,
    <<0xFF, 0xFF, 0xFF, 0x7F>>,
    <<0x80, 0x80, 0x80, 0x01>>,
  ]
  list.each(absurd_counts, fn(count) {
    receipt.decode(bit_array.concat([header, count])) |> should.be_error
  })
}

pub fn f5_decode_rejects_every_foreign_kind_tag_test() {
  let assert <<_, rest:bits>> = receipt.encode(sample())
  list.each([0x00, 0x01, 0x03, 0x04, 0x05, 0xFF], fn(tag) {
    receipt.decode(<<tag, rest:bits>>) |> should.be_error
  })
}

pub fn f5_decode_rejects_unknown_verdict_and_reason_tags_test() {
  let prefix = drop_last(receipt.encode(sample()), 1)
  list.each([0x03, 0x04, 0x7F, 0xFF], fn(tag) {
    receipt.decode(bit_array.concat([prefix, <<tag>>]))
    |> should.equal(Error(receipt.UnknownVerdictTag(tag)))
  })
  list.each([0x0A, 0x0B, 0xFF], fn(tag) {
    receipt.decode(bit_array.concat([prefix, <<0x01, tag>>]))
    |> should.equal(Error(receipt.UnknownReasonTag(tag)))
  })
}

pub fn encode_never_emits_a_non_canonical_ordering_test() {
  // The producer side of the one-byte-string-per-receipt rule: however a
  // caller happens to order a list, the bytes are the same. The consumer side
  // -- refusing bytes that arrive out of order -- is the two tests below,
  // which have to build their input by hand precisely because this module
  // will not emit one.
  let r = sample()
  let unsorted = receipt.Receipt(..r, deps: list.reverse(r.deps))
  { r.deps != list.reverse(r.deps) } |> should.be_true
  receipt.encode(unsorted) |> should.equal(receipt.encode(r))
}

pub fn f5_decode_rejects_a_duplicated_list_entry_test() {
  // Hand-built bytes with the same digest listed twice in `deps`.
  let doubled =
    build_receipt_bytes(
      canonical.digest_list([dig(4), dig(4)]),
      canonical.digest_list([]),
    )
  receipt.decode(doubled) |> should.equal(Error(receipt.NonCanonical))
}

pub fn f5_decode_rejects_a_descending_list_test() {
  let descending =
    build_receipt_bytes(
      canonical.digest_list([dig(9), dig(1)]),
      canonical.digest_list([]),
    )
  receipt.decode(descending) |> should.equal(Error(receipt.NonCanonical))
}

/// A receipt's bytes assembled field by field, so a test can put something in
/// that `encode` would never produce.
fn build_receipt_bytes(deps: BitArray, axioms: BitArray) -> BitArray {
  bit_array.concat([
    <<0x02, 0xFF, 0xFF, 0xFF, 0xFF>>,
    serialize.varint(canonical.format_version),
    serialize.varint(1),
    serialize.digest_field(dig(1)),
    serialize.digest_field(dig(2)),
    serialize.digest_field(dig(3)),
    deps,
    axioms,
    serialize.varint(0),
    canonical.digest_list([]),
    serialize.varint(0),
    serialize.varint(0),
    <<0x00>>,
  ])
}

pub fn f5_decode_rejects_trailing_bytes_test() {
  let bytes = receipt.encode(sample())
  receipt.decode(bit_array.concat([bytes, <<0x00>>]))
  |> should.equal(Error(receipt.Trailing))
}

pub fn f5_decode_of_the_empty_string_is_an_error_test() {
  receipt.decode(<<>>) |> should.be_error
}

fn positions(n: Int) -> List(Int) {
  case n < 0 {
    True -> []
    False -> [n, ..positions(n - 1)]
  }
}

fn drop_last(b: BitArray, n: Int) -> BitArray {
  take(b, bit_array.byte_size(b) - n)
}

// ── nothing here is signed ────────────────────────────────────────────────────

pub fn a_receipt_carries_no_issuer_and_no_signature_test() {
  // Encoded twice by two "different parties" -- same bytes, because there is
  // nothing in a receipt that identifies who made it. If a signature or an
  // issuer field ever appears, this test is where it shows up.
  let c = named("purist/identity")
  let a =
    receipt.issue(kernel_id, c.environment, c.provenance, budget, c.term, c.typ)
  let b =
    receipt.issue(kernel_id, c.environment, c.provenance, budget, c.term, c.typ)
  receipt.encode(a) |> should.equal(receipt.encode(b))
  receipt.digest(digest.Blake3, a)
  |> should.equal(receipt.digest(digest.Blake3, b))
}

pub fn receipt_digests_are_domain_separated_from_terms_test() {
  // A receipt's identity cannot collide with a term's: different kind tags.
  let r = sample()
  let as_term = receipt.term_address(term.Sort(0))
  { receipt.digest(digest.Blake3, r) == as_term } |> should.be_false
}

pub fn issue_with_none_policy_matches_plain_issue_test() {
  let c = named("rules/annotation-only")
  let a = issue(c)
  let b =
    receipt.issue_with(
      digest.Blake3,
      kernel_id,
      c.environment,
      c.provenance,
      None,
      budget,
      c.term,
      c.typ,
    )
  receipt.encode(a) |> should.equal(receipt.encode(b))
}
