/// Content addressing tests.
///
/// Address vectors for terms that contain no Const or Trusted nodes are stable
/// across the wire-format changes for hash agility (their encoding is
/// unchanged). Vectors for Const/Trusted would change if those terms are
/// re-encoded, so we only test round-trip properties there.
import cronch/digest
import cronch/hash
import cronch/term
import gleam/string
import gleeunit/should

// ── Address vectors (stable: no Const or Trusted) ────────────────────────────
// These come from conformance/vectors/serialization.json in the reference
// implementation. Encoding of these terms is byte-identical so the hashes
// should match.

pub fn var_0_address_test() {
  hash.address(digest.Blake3, term.Var(0))
  |> should.equal(
    "blake3:1ad48f49627079d806b802c74f40c39d55fe1d78b3faf0f8017aec62cec42122",
  )
}

pub fn var_127_address_test() {
  hash.address(digest.Blake3, term.Var(127))
  |> should.equal(
    "blake3:9c4af9461a9002f15f59b41368f45bff543cf64ac22f3e0c595635c6b9e2ea5d",
  )
}

pub fn sort_0_address_test() {
  hash.address(digest.Blake3, term.Sort(0))
  |> should.equal(
    "blake3:687376c930d7020a32f04c396fc2e5eab49cd09a738fa03d573033416a6a47ce",
  )
}

pub fn sort_1_address_test() {
  hash.address(digest.Blake3, term.Sort(1))
  |> should.equal(
    "blake3:2022ec9d571ba774cf9e83d0194962f5d1e3aa1a48d486a67e2762a6c7959015",
  )
}

pub fn pi_poly_id_type_address_test() {
  let t = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  hash.address(digest.Blake3, t)
  |> should.equal(
    "blake3:38ba1c85fb33cf17dac512ce5f5d9dc921b0ad9480fba1cdc9097f166fb2d44d",
  )
}

pub fn hole_0_type0_address_test() {
  hash.address(digest.Blake3, term.Hole(0, term.Sort(0)))
  |> should.equal(
    "blake3:85e010eef753fb59f0caaee3237267886bf6079d6c0bf6301ea503a081a68a36",
  )
}

// ── Address format ────────────────────────────────────────────────────────────

pub fn address_has_algorithm_prefix_test() {
  hash.address(digest.Blake3, term.Sort(0))
  |> string.starts_with("blake3:")
  |> should.be_true
}

pub fn address_is_correct_length_test() {
  // "blake3:" (7) + 64 hex chars = 71
  hash.address(digest.Blake3, term.Sort(0))
  |> string.length
  |> should.equal(71)
}

pub fn distinct_terms_have_distinct_addresses_test() {
  should.not_equal(
    hash.address(digest.Blake3, term.Sort(0)),
    hash.address(digest.Blake3, term.Sort(1)),
  )
}

pub fn address_is_deterministic_test() {
  let t = term.Pi(term.Sort(0), term.Var(0))
  should.equal(hash.address(digest.Blake3, t), hash.address(digest.Blake3, t))
}

// ── parse_address ─────────────────────────────────────────────────────────────

pub fn parse_roundtrip_test() {
  let t = term.Sort(0)
  let expected_digest = hash.hash(digest.Blake3, t)
  hash.parse_address(hash.address(digest.Blake3, t))
  |> should.be_ok
  |> should.equal(expected_digest)
}

pub fn parse_rejects_wrong_algorithm_test() {
  hash.parse_address(
    "sha256:687376c930d7020a32f04c396fc2e5eab49cd09a738fa03d573033416a6a47ce",
  )
  |> should.be_error
}

pub fn parse_rejects_short_digest_test() {
  hash.parse_address("blake3:abc") |> should.be_error
}

pub fn parse_rejects_missing_colon_test() {
  hash.parse_address(
    "blake3687376c930d7020a32f04c396fc2e5eab49cd09a738fa03d573033416a6a47ce",
  )
  |> should.be_error
}

pub fn parse_rejects_invalid_hex_test() {
  // Valid length but contains 'zz' which isn't hex
  hash.parse_address(
    "blake3:zz4af9461a9002f15f59b41368f45bff543cf64ac22f3e0c595635c6b9e2ea5d",
  )
  |> should.be_error
}
