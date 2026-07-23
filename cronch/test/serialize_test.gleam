import cronch/digest
import cronch/pubkey
import cronch/serialize.{
  NonCanonicalVarint, Truncated, UnknownHashAlgorithm, UnknownKeyScheme,
  UnknownTag, VarintOverflow, TrailingBytes,
}
import cronch/term
import gleam/bit_array
import gleeunit/should

// ── Encoding: terms with no Const or Trusted ─────────────────────────────────
// These encodings are byte-for-byte:
//   tag byte | fields...
// varints are canonical little-endian base-128.

pub fn var_0_test() {
  serialize.encode(term.Var(0))
  |> should.equal(<<0x00, 0x00>>)
}

pub fn var_127_test() {
  serialize.encode(term.Var(127))
  |> should.equal(<<0x00, 0x7f>>)
}

pub fn var_128_test() {
  // 128 in LEB128: continuation byte 0x80, value byte 0x01
  serialize.encode(term.Var(128))
  |> should.equal(<<0x00, 0x80, 0x01>>)
}

pub fn var_16384_test() {
  // 16384 = 0x4000, three LEB128 bytes: 0x80 0x80 0x01
  serialize.encode(term.Var(16384))
  |> should.equal(<<0x00, 0x80, 0x80, 0x01>>)
}

pub fn sort_0_test() {
  serialize.encode(term.Sort(0))
  |> should.equal(<<0x01, 0x00>>)
}

pub fn sort_1_test() {
  serialize.encode(term.Sort(1))
  |> should.equal(<<0x01, 0x01>>)
}

// Pi(Sort(0), Pi(Var(0), Var(1)))
pub fn pi_poly_id_type_test() {
  let t = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  serialize.encode(t)
  |> should.equal(<<0x02, 0x01, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01>>)
}

// Lam(Sort(0), Lam(Var(0), Var(0)))
pub fn lam_poly_id_test() {
  let t = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  serialize.encode(t)
  |> should.equal(<<0x03, 0x01, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00>>)
}

// App(lam_poly_id, Sort(3))
pub fn app_id_at_type3_test() {
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  serialize.encode(term.App(id, term.Sort(3)))
  |> should.equal(<<0x04, 0x03, 0x01, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x01, 0x03>>)
}

// Eq(Var(1), Var(0), Var(0))
pub fn eq_refl_shape_test() {
  serialize.encode(term.Eq(term.Var(1), term.Var(0), term.Var(0)))
  |> should.equal(<<0x05, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00>>)
}

// Refl(Var(1), Var(0))
pub fn refl_test() {
  serialize.encode(term.Refl(term.Var(1), term.Var(0)))
  |> should.equal(<<0x06, 0x00, 0x01, 0x00, 0x00>>)
}

// Hole(0, Sort(0))
pub fn hole_0_type0_test() {
  serialize.encode(term.Hole(0, term.Sort(0)))
  |> should.equal(<<0x08, 0x00, 0x01, 0x00>>)
}

// Hole(99, Pi(Sort(0), Sort(0)))
pub fn hole_99_pi_test() {
  serialize.encode(term.Hole(99, term.Pi(term.Sort(0), term.Sort(0))))
  |> should.equal(<<0x08, 0x63, 0x02, 0x01, 0x00, 0x01, 0x00>>)
}

// ── Encoding: Const ───────────────────────────────────────────────────────────
// Const wire layout: tag 0x07 | algo_tag(1 byte) | digest_bytes
// Blake3 algo tag = 0x00, digest = 32 bytes.

pub fn const_zero_blake3_test() {
  let zero32 = <<
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  >>
  let t = term.Const(digest.Digest(digest.Blake3, zero32))
  // 0x07 tag, then 0x00 Blake3 algo tag, then 32 zero bytes
  let expected = <<
    0x07, 0x00,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  >>
  serialize.encode(t) |> should.equal(expected)
}

// ── Encoding: Trusted ─────────────────────────────────────────────────────────
// Trusted wire layout:
//   tag 0x09 | scheme_tag(1) | key_bytes | algo_tag(1) | digest_bytes | args | result_ty
// Ed25519 scheme tag = 0x00, key = 32 bytes. Blake3 algo tag = 0x00, digest = 32 bytes.

pub fn trusted_encodes_test() {
  let host_bytes = <<
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  >>
  let proc_bytes = <<
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  >>
  let host = pubkey.PublicKey(pubkey.Ed25519, host_bytes)
  let proc = digest.Digest(digest.Blake3, proc_bytes)
  let t = term.Trusted(host, proc, term.Var(0), term.Var(0))

  // 0x09 | 0x00 (Ed25519) | host_bytes | 0x00 (Blake3) | proc_bytes | Var(0) | Var(0)
  let expected = <<
    0x09, 0x00,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    0x00,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    0x00, 0x00,
    0x00, 0x00,
  >>
  serialize.encode(t) |> should.equal(expected)
}

// ── Round-trip tests ──────────────────────────────────────────────────────────

pub fn round_trip_var_test() {
  let t = term.Var(42)
  serialize.decode(serialize.encode(t)) |> should.equal(Ok(t))
}

pub fn round_trip_sort_test() {
  serialize.decode(serialize.encode(term.Sort(7)))
  |> should.equal(Ok(term.Sort(7)))
}

pub fn round_trip_pi_test() {
  let t = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  serialize.decode(serialize.encode(t)) |> should.equal(Ok(t))
}

pub fn round_trip_const_test() {
  let h = digest.Digest(digest.Blake3, <<
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
  >>)
  let t = term.Const(h)
  serialize.decode(serialize.encode(t)) |> should.equal(Ok(t))
}

pub fn round_trip_trusted_test() {
  let host = pubkey.PublicKey(pubkey.Ed25519, <<
    0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe,
    0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe,
    0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe,
    0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe,
  >>)
  let proc = digest.Digest(digest.Blake3, <<
    0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef,
    0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef,
    0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef,
    0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef, 0xef,
  >>)
  let t =
    term.Trusted(host, proc, term.App(term.Var(0), term.Sort(0)), term.Sort(0))
  serialize.decode(serialize.encode(t)) |> should.equal(Ok(t))
}

pub fn round_trip_leibniz_test() {
  // Pi(Pi(Var(2), Sort(0)), Pi(App(Var(0), Var(2)), App(Var(1), Var(2))))
  let t =
    term.Pi(
      term.Pi(term.Var(2), term.Sort(0)),
      term.Pi(
        term.App(term.Var(0), term.Var(2)),
        term.App(term.Var(1), term.Var(2)),
      ),
    )
  serialize.decode(serialize.encode(t)) |> should.equal(Ok(t))
}

// ── Rejection tests ───────────────────────────────────────────────────────────

pub fn rejects_empty_test() {
  serialize.decode(<<>>) |> should.equal(Error(Truncated))
}

pub fn rejects_unknown_tag_test() {
  serialize.decode(<<0xff>>) |> should.equal(Error(UnknownTag(0xff)))
}

pub fn rejects_trailing_bytes_test() {
  let bytes = bit_array.append(serialize.encode(term.Sort(0)), <<0x00>>)
  serialize.decode(bytes) |> should.equal(Error(TrailingBytes))
}

pub fn rejects_truncated_pi_test() {
  // Pi tag with only one of its two subterms
  serialize.decode(bit_array.append(<<0x02>>, serialize.encode(term.Sort(0))))
  |> should.equal(Error(Truncated))
}

pub fn rejects_truncated_const_test() {
  // Const tag + Blake3 algo tag + only 2 bytes instead of 32
  serialize.decode(<<0x07, 0x00, 0x00, 0x01>>)
  |> should.equal(Error(Truncated))
}

pub fn rejects_unknown_hash_algorithm_test() {
  // Const tag + unknown algo byte 0xff
  serialize.decode(<<0x07, 0xff>>)
  |> should.equal(Error(UnknownHashAlgorithm(0xff)))
}

pub fn rejects_unknown_key_scheme_test() {
  // Trusted tag + unknown scheme byte 0xff
  serialize.decode(<<0x09, 0xff>>)
  |> should.equal(Error(UnknownKeyScheme(0xff)))
}

pub fn rejects_overlong_varint_zero_test() {
  // Var with overlong zero varint: final byte is 0x00 after a continuation
  serialize.decode(<<0x00, 0x80, 0x00>>)
  |> should.equal(Error(NonCanonicalVarint))
}

pub fn rejects_overlong_varint_one_test() {
  serialize.decode(<<0x00, 0x81, 0x00>>)
  |> should.equal(Error(NonCanonicalVarint))
}

pub fn rejects_varint_overflow_test() {
  // Six continuation bytes -- overflows u32
  serialize.decode(<<0x01, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01>>)
  |> should.equal(Error(VarintOverflow))
}
