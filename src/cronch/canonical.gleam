/// Domain-separated canonical encoding for the hashable artifact classes.
///
/// Outside the TCB. Nothing here decides anything; it only turns values into
/// bytes so they can be hashed, and back.
///
/// Why a kind tag
/// --------------
/// This PR introduces several new hashable classes. If a Basis, a Receipt and
/// a Term could ever produce equal digests, that is a cross-class collision
/// channel: whoever controls the class with the weakest structural constraints
/// gets to forge identity in the others. So every encoding in this family
/// begins with a one-byte kind tag:
///
///   0x00 Term   0x01 Basis   0x02 Receipt   0x03 RuleSet   0x04 CapabilitySet
///
/// Two encodings of different classes therefore differ in their first byte,
/// and so are unequal, by construction. No hash function is consulted for that
/// argument -- it holds at the byte level.
///
/// Why the guard bytes and the format version
/// ------------------------------------------
/// The "tag byte differs" argument closes only if *every* hashable class is
/// tagged. One is not: `hash.hash` predates this PR, feeds `serialize.encode`
/// straight into the hash, and its output addresses every `Const` in every
/// store that already exists. Prefixing it with 0x00 would change all of them,
/// so per the brief it stays byte-identical and the tagged term encoding
/// (`term_envelope` below) is a separate function.
///
/// That leaves legacy Term encodings sharing leading bytes with the new
/// classes: a `Pi` encoding starts 0x02, the same first byte as a Receipt. So
/// the envelope header is
///
///   kind tag (1) | 0xFF 0xFF 0xFF 0xFF (4) | varint format_version (1+)
///
/// and the argument that no envelope is ever equal to a legacy Term encoding
/// needs no case analysis at all:
///
///   - A legacy `Var`/`Sort`/`Hole` encoding is a tag byte followed by a
///     canonical varint, which is at most five bytes -- so at most six bytes
///     in total for `Var`/`Sort`, and for `Hole` byte 1 must begin a varint
///     that is followed by a term.
///   - Every other legacy encoding carries a sub-term tag, a digest algorithm
///     tag, or a key scheme tag at byte 1. All of those are small: 0x00..0x09
///     for a term tag, 0x00 for the registered algorithm and scheme. None is
///     0xFF.
///   - Every envelope is at least `envelope_min_size` (7) bytes: six of
///     header plus a payload that is never empty.
///
/// So an envelope is too long to be a `Var`/`Sort` encoding and carries a byte
/// at position 1 that no other legacy encoding can carry. Both halves are
/// checked in canonical_test.gleam rather than left as prose.
///
/// The format version is part of the hashed bytes on purpose: if this envelope
/// layout ever changes, digests under the new layout must not collide with
/// digests under the old one either.
///
/// Everything hashed here follows the existing serializer's conventions --
/// fixed field order, length-prefixed variable-length fields, sets sorted by
/// raw digest bytes, no floats, no iteration over anything unordered. The
/// varint, digest and pubkey primitives are `serialize`'s own, re-exported
/// rather than reimplemented.
import cronch/digest.{type Digest, type HashAlgorithm}
import cronch/pubkey.{type PublicKey}
import cronch/rewrite.{type Rule}
import cronch/serialize.{type DecodeError}
import cronch/term.{type Term}
import gleam/bit_array
import gleam/int
import gleam/list
import gleam/order.{type Order}
import gleam/result

/// The hashable artifact classes. Adding one means adding a variant here and
/// a tag byte in `kind_tag` that no existing variant uses.
pub type Kind {
  KindTerm
  KindBasis
  KindReceipt
  KindRuleSet
  KindCapabilitySet
}

/// The one-byte kind tag. Never changes for an existing variant: it is the
/// first byte of a hashed encoding, so changing one rewrites every digest of
/// that class.
pub fn kind_tag(kind: Kind) -> Int {
  case kind {
    KindTerm -> 0x00
    KindBasis -> 0x01
    KindReceipt -> 0x02
    KindRuleSet -> 0x03
    KindCapabilitySet -> 0x04
  }
}

/// Every kind, for the exhaustive disjointness test.
pub fn all_kinds() -> List(Kind) {
  [KindTerm, KindBasis, KindReceipt, KindRuleSet, KindCapabilitySet]
}

/// The guard bytes following the kind tag. 0xFF is not a term tag, not a
/// digest algorithm tag and not a key scheme tag, so no legacy Term encoding
/// can carry one at byte 1. See the module comment.
pub const guard: BitArray = <<0xFF, 0xFF, 0xFF, 0xFF>>

/// Version of the envelope layout itself -- distinct from, and independent
/// of, any version an individual artifact class carries in its payload
/// (`Receipt.version`, for one).
pub const format_version: Int = 1

/// Smallest envelope this module can produce: six header bytes plus a payload
/// of at least one byte. Load-bearing for the disjointness argument above,
/// because the longest legacy `Var`/`Sort` encoding is six bytes. Pinned from
/// both sides by tests.
pub const envelope_min_size: Int = 7

/// Wrap a class payload: kind tag, guard bytes, then the payload verbatim.
pub fn envelope(kind: Kind, payload: BitArray) -> BitArray {
  bit_array.concat([
    <<{ kind_tag(kind) }>>,
    guard,
    serialize.varint(format_version),
    payload,
  ])
}

/// Hash a class payload under its kind. The only way anything in this PR
/// produces a digest of a new artifact class.
pub fn digest_of(
  algorithm: HashAlgorithm,
  kind: Kind,
  payload: BitArray,
) -> Digest {
  digest.hash_bytes(algorithm, envelope(kind, payload))
}

/// The tagged encoding of a term.
///
/// NOT what `hash.hash` produces, and deliberately so: `hash.hash` is the
/// pre-existing content address of every `Const` in every store, and it stays
/// byte-identical. This exists so `Term` participates in the same
/// domain-separated family as the new classes when a caller wants a digest
/// that is provably not a Basis or a Receipt. Nothing in this PR replaces a
/// legacy term address with it.
pub fn term_envelope(t: Term) -> BitArray {
  envelope(KindTerm, serialize.encode(t))
}

/// Tagged digest of a term. See `term_envelope` for why this is not
/// `hash.hash`.
pub fn term_digest(algorithm: HashAlgorithm, t: Term) -> Digest {
  digest.hash_bytes(algorithm, term_envelope(t))
}

/// The tagged encoding of a rule set.
///
/// NOT what `hash.hash_rule_set` produces. Rule-set content hashes are what a
/// rule-set author signs and what a `trust.Policy` authorizes, so those
/// addresses are already in circulation and stay byte-identical for exactly
/// the same reason term addresses do.
pub fn rule_set_envelope(rules: List(Rule)) -> BitArray {
  envelope(KindRuleSet, serialize.encode_rule_set(rules))
}

/// Tagged digest of a rule set. See `rule_set_envelope`.
pub fn rule_set_digest(algorithm: HashAlgorithm, rules: List(Rule)) -> Digest {
  digest.hash_bytes(algorithm, rule_set_envelope(rules))
}

// ── Field encodings ───────────────────────────────────────────────────────────

/// A length-prefixed UTF-8 string: varint byte-length, then the bytes.
/// Length-prefixed rather than terminated so no string content can be
/// mistaken for a field boundary.
pub fn string_field(s: String) -> BitArray {
  let bytes = bit_array.from_string(s)
  bit_array.concat([serialize.varint(bit_array.byte_size(bytes)), bytes])
}

/// Read a length-prefixed UTF-8 string. Fails closed on a truncated body or
/// on bytes that are not valid UTF-8 -- an unrepresentable string is never
/// silently replaced with a lossy one.
pub fn take_string(data: BitArray) -> Result(#(String, BitArray), DecodeError) {
  use #(size, rest) <- result.try(serialize.take_varint(data))
  let bits = size * 8
  case rest {
    <<body:bits-size(bits), tail:bits>> ->
      case bit_array.to_string(body) {
        Ok(s) -> Ok(#(s, tail))
        Error(Nil) -> Error(serialize.Truncated)
      }
    _ -> Error(serialize.Truncated)
  }
}

/// A counted list of digests: varint count, then each digest field in the
/// order given. Callers that need set semantics must `sort_digests` first --
/// this function encodes what it is handed and does not reorder, so that a
/// list whose order is meaningful stays encodable.
pub fn digest_list(ds: List(Digest)) -> BitArray {
  bit_array.concat([
    serialize.varint(list.length(ds)),
    ..list.map(ds, serialize.digest_field)
  ])
}

/// Read a counted list of digests. The count is read first and consumed one
/// element at a time against the remaining bytes, so a declared length larger
/// than the body runs out and fails rather than allocating for it.
pub fn take_digest_list(
  data: BitArray,
) -> Result(#(List(Digest), BitArray), DecodeError) {
  use #(count, rest) <- result.try(serialize.take_varint(data))
  take_n(rest, count, [], serialize.take_digest)
}

/// A counted list of public keys: varint count, then each pubkey field.
pub fn pubkey_list(ks: List(PublicKey)) -> BitArray {
  bit_array.concat([
    serialize.varint(list.length(ks)),
    ..list.map(ks, serialize.pubkey_field)
  ])
}

/// Read a counted list of public keys.
pub fn take_pubkey_list(
  data: BitArray,
) -> Result(#(List(PublicKey), BitArray), DecodeError) {
  use #(count, rest) <- result.try(serialize.take_varint(data))
  take_n(rest, count, [], serialize.take_pubkey)
}

/// A counted list of (public key, digest) pairs, each encoded key-then-digest.
pub fn key_digest_list(ps: List(#(PublicKey, Digest))) -> BitArray {
  bit_array.concat([
    serialize.varint(list.length(ps)),
    ..list.map(ps, fn(p) {
      bit_array.concat([
        serialize.pubkey_field(p.0),
        serialize.digest_field(p.1),
      ])
    })
  ])
}

/// Read a counted list of (public key, digest) pairs.
pub fn take_key_digest_list(
  data: BitArray,
) -> Result(#(List(#(PublicKey, Digest)), BitArray), DecodeError) {
  use #(count, rest) <- result.try(serialize.take_varint(data))
  take_n(rest, count, [], fn(d) {
    use #(k, r1) <- result.try(serialize.take_pubkey(d))
    use #(h, r2) <- result.try(serialize.take_digest(r1))
    Ok(#(#(k, h), r2))
  })
}

// Read exactly `remaining` elements with `one`. Each element must come out of
// the bytes actually present, so an absurd declared count fails on the first
// element it cannot read rather than reserving anything for it.
fn take_n(
  data: BitArray,
  remaining: Int,
  acc: List(a),
  one: fn(BitArray) -> Result(#(a, BitArray), DecodeError),
) -> Result(#(List(a), BitArray), DecodeError) {
  case remaining <= 0 {
    True -> Ok(#(list.reverse(acc), data))
    False -> {
      use #(x, rest) <- result.try(one(data))
      take_n(rest, remaining - 1, [x, ..acc], one)
    }
  }
}

// ── Raw-byte ordering ─────────────────────────────────────────────────────────

/// Lexicographic comparison of raw bytes, shortest-prefix-first.
///
/// Raw bytes, never a string rendering: a hex or base64 rendering happens to
/// agree with byte order for equal-length inputs, but that is a coincidence of
/// those alphabets rather than a property anything should depend on, and it
/// stops being true the moment lengths differ.
pub fn compare_bytes(a: BitArray, b: BitArray) -> Order {
  case a, b {
    <<x, ra:bits>>, <<y, rb:bits>> ->
      case int.compare(x, y) {
        order.Eq -> compare_bytes(ra, rb)
        other -> other
      }
    <<>>, <<>> -> order.Eq
    <<>>, _ -> order.Lt
    _, _ -> order.Gt
  }
}

/// Order two digests by their canonical field bytes -- algorithm tag first,
/// then raw digest bytes. Including the tag keeps the order total across
/// algorithms rather than only within one.
pub fn compare_digests(a: Digest, b: Digest) -> Order {
  compare_bytes(serialize.digest_field(a), serialize.digest_field(b))
}

/// Order two public keys by their canonical field bytes.
pub fn compare_pubkeys(a: PublicKey, b: PublicKey) -> Order {
  compare_bytes(serialize.pubkey_field(a), serialize.pubkey_field(b))
}

/// Order two (key, digest) pairs by key bytes, then digest bytes.
pub fn compare_key_digest(
  a: #(PublicKey, Digest),
  b: #(PublicKey, Digest),
) -> Order {
  case compare_pubkeys(a.0, b.0) {
    order.Eq -> compare_digests(a.1, b.1)
    other -> other
  }
}

/// Sort digests by raw bytes and drop duplicates. Idempotent.
pub fn sort_digests(ds: List(Digest)) -> List(Digest) {
  ds |> list.unique |> list.sort(compare_digests)
}

/// Sort public keys by raw bytes and drop duplicates. Idempotent.
pub fn sort_pubkeys(ks: List(PublicKey)) -> List(PublicKey) {
  ks |> list.unique |> list.sort(compare_pubkeys)
}

/// Sort (key, digest) pairs by raw bytes and drop duplicates. Idempotent.
pub fn sort_key_digests(
  ps: List(#(PublicKey, Digest)),
) -> List(#(PublicKey, Digest)) {
  ps |> list.unique |> list.sort(compare_key_digest)
}
