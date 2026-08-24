import cronch/canonical
import cronch/digest
import cronch/hash
import cronch/pubkey
import cronch/rewrite
import cronch/serialize
import cronch/term
import gleam/bit_array
import gleam/int
import gleam/list
import gleam/order
import gleeunit/should
import support/reference_rules

// ── fixtures ──────────────────────────────────────────────────────────────────

fn key(b: Int) -> pubkey.PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<b:size(256)>>)
}

fn dig(b: Int) -> digest.Digest {
  digest.Digest(digest.Blake3, <<b:size(256)>>)
}

/// A spread of terms wide enough that every term tag appears, including the
/// short ones (`Var`, `Sort`) that the length half of the disjointness
/// argument is about.
fn term_fixtures() -> List(term.Term) {
  let #(fst, _) = reference_rules.fst_pair_example()
  let #(snd, _) = reference_rules.snd_pair_example()
  let #(j, _) = reference_rules.j_example()
  [
    term.Var(0),
    term.Var(1),
    term.Var(4_294_967_295),
    term.Sort(0),
    term.Sort(1),
    term.Sort(4_294_967_295),
    term.Pi(term.Sort(0), term.Var(0)),
    term.Lam(term.Sort(0), term.Var(0)),
    term.App(term.Var(0), term.Var(1)),
    term.Eq(term.Sort(0), term.Var(0), term.Var(0)),
    term.Refl(term.Sort(0), term.Var(0)),
    term.Const(dig(7)),
    term.Hole(0, term.Sort(0)),
    term.Hole(3, term.Pi(term.Sort(0), term.Sort(0))),
    term.Trusted(key(2), dig(3), term.Sort(0), term.Sort(1)),
    reference_rules.sigma_typ(),
    reference_rules.pair_typ(),
    reference_rules.fst_typ(),
    reference_rules.snd_typ(),
    reference_rules.j_typ(),
    fst,
    snd,
    j,
  ]
}

/// A payload per class, built the way the class itself builds one. The Basis,
/// Receipt and CapabilitySet payload shapes land in later parts; here they
/// stand for "some payload of that class", which is all the disjointness
/// argument needs.
fn payload_fixtures() -> List(#(canonical.Kind, BitArray)) {
  let smallest_basis =
    bit_array.concat([
      canonical.string_field(""),
      canonical.digest_list([]),
      canonical.key_digest_list([]),
      canonical.pubkey_list([]),
    ])
  let populated_basis =
    bit_array.concat([
      canonical.string_field("cronch-kernel/0.1.0"),
      canonical.digest_list(canonical.sort_digests([dig(1), dig(2)])),
      canonical.key_digest_list([#(key(1), dig(3))]),
      canonical.pubkey_list([key(9)]),
    ])
  [
    #(canonical.KindTerm, serialize.encode(term.Var(0))),
    #(canonical.KindTerm, serialize.encode(reference_rules.j_typ())),
    #(canonical.KindBasis, smallest_basis),
    #(canonical.KindBasis, populated_basis),
    #(
      canonical.KindReceipt,
      bit_array.concat([serialize.varint(1), dig(4).bytes]),
    ),
    #(canonical.KindRuleSet, serialize.encode_rule_set([])),
    #(
      canonical.KindRuleSet,
      serialize.encode_rule_set(reference_rules.rule_set()),
    ),
    #(canonical.KindCapabilitySet, canonical.pubkey_list([])),
    #(canonical.KindCapabilitySet, canonical.pubkey_list([key(1), key(2)])),
  ]
}

fn envelope_fixtures() -> List(#(canonical.Kind, BitArray)) {
  list.map(payload_fixtures(), fn(p) { #(p.0, canonical.envelope(p.0, p.1)) })
}

fn first_byte(b: BitArray) -> Int {
  let assert <<x, _:bits>> = b
  x
}

// ── kind tags ─────────────────────────────────────────────────────────────────

pub fn kind_tags_are_the_declared_bytes_test() {
  canonical.kind_tag(canonical.KindTerm) |> should.equal(0x00)
  canonical.kind_tag(canonical.KindBasis) |> should.equal(0x01)
  canonical.kind_tag(canonical.KindReceipt) |> should.equal(0x02)
  canonical.kind_tag(canonical.KindRuleSet) |> should.equal(0x03)
  canonical.kind_tag(canonical.KindCapabilitySet) |> should.equal(0x04)
}

pub fn kind_tags_are_pairwise_distinct_test() {
  let tags = list.map(canonical.all_kinds(), canonical.kind_tag)
  list.length(list.unique(tags))
  |> should.equal(list.length(canonical.all_kinds()))
}

pub fn envelope_starts_with_its_kind_tag_test() {
  // The first half of the by-construction argument: byte 0 of an envelope is
  // exactly the kind tag, whatever the payload is.
  list.each(envelope_fixtures(), fn(e) {
    first_byte(e.1) |> should.equal(canonical.kind_tag(e.0))
  })
}

// ── cross-class disjointness, by construction ─────────────────────────────────

pub fn no_two_classes_can_produce_equal_encodings_test() {
  // Exhaustive over kind pairs, not over payloads: for any two DISTINCT kinds
  // the first bytes differ, so no payload whatsoever can make the encodings
  // equal. This is the whole construction argument, stated as a test.
  list.each(canonical.all_kinds(), fn(a) {
    list.each(canonical.all_kinds(), fn(b) {
      case a == b {
        True -> Nil
        False -> {
          { canonical.kind_tag(a) == canonical.kind_tag(b) }
          |> should.be_false
        }
      }
    })
  })
}

pub fn sampled_cross_class_encodings_are_all_distinct_test() {
  // The sampled half: every fixture envelope against every other, across all
  // five classes. Distinct bytes, and therefore distinct digests.
  let envelopes = envelope_fixtures()
  list.each(envelopes, fn(x) {
    list.each(envelopes, fn(y) {
      case x.0 == y.0 && x.1 == y.1 {
        True -> Nil
        False -> { x.1 == y.1 } |> should.be_false
      }
    })
  })
}

pub fn sampled_cross_class_digests_are_all_distinct_test() {
  let digests =
    list.map(payload_fixtures(), fn(p) {
      canonical.digest_of(digest.Blake3, p.0, p.1)
    })
  list.length(list.unique(digests)) |> should.equal(list.length(digests))
}

pub fn same_payload_under_different_kinds_digests_differently_test() {
  // The attack the kind tag exists to stop: identical payload bytes reused
  // across classes must not yield a shared identity.
  let payload = serialize.encode(term.Sort(0))
  let digests =
    list.map(canonical.all_kinds(), fn(k) {
      canonical.digest_of(digest.Blake3, k, payload)
    })
  list.length(list.unique(digests)) |> should.equal(5)
}

// ── disjointness from the legacy untagged Term encoding ───────────────────────

pub fn legacy_var_and_sort_encodings_fit_in_six_bytes_test() {
  // One side of the length argument. u32::MAX is the largest value either
  // field can hold (serialize rejects anything above it), so this is the
  // worst case, not a sample.
  bit_array.byte_size(serialize.encode(term.Var(4_294_967_295)))
  |> should.equal(6)
  bit_array.byte_size(serialize.encode(term.Sort(4_294_967_295)))
  |> should.equal(6)
  list.each(term_fixtures(), fn(t) {
    case t {
      term.Var(_) | term.Sort(_) ->
        { bit_array.byte_size(serialize.encode(t)) <= 6 } |> should.be_true
      _ -> Nil
    }
  })
}

pub fn every_envelope_is_at_least_seven_bytes_test() {
  // The other side of the length argument: no envelope is short enough to be
  // a Var or Sort encoding, whatever it carries.
  canonical.envelope_min_size |> should.equal(7)
  list.each(envelope_fixtures(), fn(e) {
    { bit_array.byte_size(e.1) >= canonical.envelope_min_size }
    |> should.be_true
  })
}

pub fn envelope_byte_one_is_never_a_legacy_tag_test() {
  // The structural argument for every legacy encoding that is not Var/Sort:
  // byte 1 there is a term tag (0x00..0x09), a digest algorithm tag or a key
  // scheme tag, all of which are small. An envelope carries 0xFF.
  list.each(envelope_fixtures(), fn(e) {
    let assert <<_, b1, _:bits>> = e.1
    b1 |> should.equal(0xFF)
    { b1 <= 0x09 } |> should.be_false
  })
  list.each(digest.all_algorithms(), fn(a) {
    { digest.algorithm_tag(a) == 0xFF } |> should.be_false
  })
  list.each(pubkey.all_schemes(), fn(s) {
    { pubkey.scheme_tag(s) == 0xFF } |> should.be_false
  })
}

pub fn no_envelope_equals_any_legacy_term_encoding_test() {
  // The sampled check backing the argument above.
  let legacy = list.map(term_fixtures(), serialize.encode)
  list.each(envelope_fixtures(), fn(e) {
    list.each(legacy, fn(l) { { e.1 == l } |> should.be_false })
  })
}

pub fn no_envelope_decodes_as_a_term_test() {
  // Stronger than byte inequality against a fixture list: an envelope is not
  // a valid term encoding at all, so it cannot equal ANY term's encoding.
  list.each(envelope_fixtures(), fn(e) {
    serialize.decode(e.1) |> should.be_error
  })
}

// ── legacy digests are unchanged ──────────────────────────────────────────────

pub fn legacy_term_hash_is_untouched_test() {
  // hash.hash still hashes the bare term encoding, with no kind tag. If this
  // ever fails, every stored Const address in every store has moved.
  list.each(term_fixtures(), fn(t) {
    hash.hash(digest.Blake3, t)
    |> should.equal(digest.hash_bytes(digest.Blake3, serialize.encode(t)))
  })
}

pub fn legacy_rule_set_hash_is_untouched_test() {
  hash.hash_rule_set(digest.Blake3, reference_rules.rule_set())
  |> should.equal(digest.hash_bytes(
    digest.Blake3,
    serialize.encode_rule_set(reference_rules.rule_set()),
  ))
}

pub fn tagged_and_legacy_digests_differ_test() {
  // The split is real, not cosmetic: the two functions genuinely disagree, so
  // a caller cannot use one where the other is expected and get away with it.
  list.each(term_fixtures(), fn(t) {
    { canonical.term_digest(digest.Blake3, t) == hash.hash(digest.Blake3, t) }
    |> should.be_false
  })
  {
    canonical.rule_set_digest(digest.Blake3, reference_rules.rule_set())
    == hash.hash_rule_set(digest.Blake3, reference_rules.rule_set())
  }
  |> should.be_false
}

// ── field encodings ───────────────────────────────────────────────────────────

pub fn string_field_round_trips_test() {
  list.each(["", "cronch-kernel/0.1.0", "unicode: λΠ ✓", "a"], fn(s) {
    canonical.take_string(canonical.string_field(s))
    |> should.equal(Ok(#(s, <<>>)))
  })
}

pub fn string_field_is_length_prefixed_not_terminated_test() {
  // A string containing what would be a terminator or a field boundary is
  // still read back whole.
  let s = "a\u{0000}b"
  canonical.take_string(canonical.string_field(s))
  |> should.equal(Ok(#(s, <<>>)))
}

pub fn take_string_rejects_a_declared_length_past_the_end_test() {
  canonical.take_string(<<200, 0x61>>) |> should.be_error
}

pub fn take_string_rejects_invalid_utf8_test() {
  canonical.take_string(<<2, 0xFF, 0xFE>>) |> should.be_error
}

pub fn digest_list_round_trips_test() {
  let ds = canonical.sort_digests([dig(3), dig(1), dig(2)])
  canonical.take_digest_list(canonical.digest_list(ds))
  |> should.equal(Ok(#(ds, <<>>)))
  canonical.take_digest_list(canonical.digest_list([]))
  |> should.equal(Ok(#([], <<>>)))
}

pub fn pubkey_list_round_trips_test() {
  let ks = canonical.sort_pubkeys([key(3), key(1)])
  canonical.take_pubkey_list(canonical.pubkey_list(ks))
  |> should.equal(Ok(#(ks, <<>>)))
}

pub fn key_digest_list_round_trips_test() {
  let ps = canonical.sort_key_digests([#(key(2), dig(9)), #(key(1), dig(1))])
  canonical.take_key_digest_list(canonical.key_digest_list(ps))
  |> should.equal(Ok(#(ps, <<>>)))
}

pub fn absurd_declared_list_length_fails_rather_than_allocating_test() {
  // varint 0xFFFFFFFF followed by nothing. Must fail on the first element it
  // cannot read, not reserve four billion slots.
  let absurd = bit_array.concat([serialize.varint(4_294_967_295), <<>>])
  canonical.take_digest_list(absurd) |> should.be_error
  canonical.take_pubkey_list(absurd) |> should.be_error
  canonical.take_key_digest_list(absurd) |> should.be_error
}

pub fn field_encodings_reuse_the_serializer_primitives_test() {
  // Constraint 5: no parallel encoding conventions. These must be the exact
  // bytes serialize itself writes for the same values.
  serialize.digest_field(dig(5))
  |> should.equal(bit_array.concat([<<0x00>>, <<5:size(256)>>]))
  serialize.pubkey_field(key(5))
  |> should.equal(bit_array.concat([<<0x00>>, <<5:size(256)>>]))
  serialize.varint(300) |> should.equal(<<0xAC, 0x02>>)
  serialize.take_varint(<<0xAC, 0x02>>) |> should.equal(Ok(#(300, <<>>)))
}

// ── raw-byte ordering ─────────────────────────────────────────────────────────

pub fn compare_bytes_is_raw_not_rendered_test() {
  canonical.compare_bytes(<<0x0A>>, <<0x09>>) |> should.equal(order.Gt)
  canonical.compare_bytes(<<0x09>>, <<0x0A>>) |> should.equal(order.Lt)
  canonical.compare_bytes(<<1, 2>>, <<1, 2>>) |> should.equal(order.Eq)
  // A shorter array is a prefix and sorts first.
  canonical.compare_bytes(<<1>>, <<1, 0>>) |> should.equal(order.Lt)
  canonical.compare_bytes(<<>>, <<0>>) |> should.equal(order.Lt)
}

pub fn sort_digests_is_by_raw_bytes_and_idempotent_test() {
  let unsorted = [dig(200), dig(3), dig(255), dig(0), dig(3)]
  let sorted = canonical.sort_digests(unsorted)
  sorted |> should.equal([dig(0), dig(3), dig(200), dig(255)])
  canonical.sort_digests(sorted) |> should.equal(sorted)
}

pub fn sort_is_permutation_invariant_test() {
  let a = canonical.sort_digests([dig(1), dig(2), dig(3)])
  let b = canonical.sort_digests([dig(3), dig(1), dig(2)])
  let c = canonical.sort_digests([dig(2), dig(3), dig(1), dig(1)])
  a |> should.equal(b)
  b |> should.equal(c)
}

pub fn digest_ordering_accounts_for_the_algorithm_tag_test() {
  // Ordering runs over the canonical field bytes, tag included, so it stays
  // total if a second algorithm is ever registered.
  list.each(digest.all_algorithms(), fn(a) {
    let d = digest.Digest(a, <<1:size(256)>>)
    canonical.compare_digests(d, d) |> should.equal(order.Eq)
  })
}

pub fn envelope_is_deterministic_across_repeated_calls_test() {
  // Constraint 7: nothing entering a hash may vary between runs.
  list.each(payload_fixtures(), fn(p) {
    let once = canonical.digest_of(digest.Blake3, p.0, p.1)
    list.each(list.repeat(Nil, 20), fn(_) {
      canonical.digest_of(digest.Blake3, p.0, p.1) |> should.equal(once)
    })
  })
}

pub fn rule_set_envelope_covers_rule_order_test() {
  // Rule order is observable behaviour (whnf tries rules in order), so it is
  // part of the content address here exactly as it is in the legacy hash.
  let forward = reference_rules.rule_set()
  let assert [a, b, c] = forward
  let reversed: List(rewrite.Rule) = [c, b, a]
  {
    canonical.rule_set_digest(digest.Blake3, forward)
    == canonical.rule_set_digest(digest.Blake3, reversed)
  }
  |> should.be_false
}

pub fn envelope_min_size_matches_the_smallest_real_payload_test() {
  // Guards against the constant drifting away from what `envelope` produces:
  // header plus a one-byte payload is exactly envelope_min_size.
  bit_array.byte_size(canonical.envelope(canonical.KindRuleSet, <<0>>))
  |> should.equal(canonical.envelope_min_size)
  int.compare(canonical.envelope_min_size, 6) |> should.equal(order.Gt)
}
