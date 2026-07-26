/// Canonical serialization and deserialization of terms.
///
/// There is exactly one encoding per term. Decoding rejects every non-canonical
/// byte string: `decode(encode(t)) == Ok(t)` for all `t`, and any `bytes` that
/// decodes at all satisfies `encode(decode(bytes)) == bytes`.
///
/// Wire layout
/// -----------
/// Each term begins with a 1-byte tag (0x00–0x09) followed by fixed fields:
///
///   Var(n)            tag 0x00 | varint n
///   Sort(u)           tag 0x01 | varint u
///   Pi(A, B)          tag 0x02 | term A | term B
///   Lam(A, b)         tag 0x03 | term A | term b
///   App(f, a)         tag 0x04 | term f | term a
///   Eq(A, a, b)       tag 0x05 | term A | term a | term b
///   Refl(A, a)        tag 0x06 | term A | term a
///   Const(d)          tag 0x07 | digest d
///   Hole(id, A)       tag 0x08 | varint id | term A
///   Trusted(…)        tag 0x09 | pubkey host | digest proc | term args | term result_ty
///
/// digest  = algo_tag(1) | bytes(digest_size(algo))
/// pubkey  = scheme_tag(1) | bytes(key_size(scheme))
/// varint  = canonical little-endian base-128, u32 range
///
/// Any other leading byte is a decode error. Trailing bytes after one complete
/// term are a decode error.

import cronch/digest.{type Digest}
import cronch/pubkey.{type PublicKey}
import cronch/rewrite.{type Pattern, type Rule}
import cronch/term.{type Term}
import gleam/bytes_tree.{type BytesTree}
import gleam/int
import gleam/list
import gleam/result

/// Reasons a byte string can fail to decode. Non-canonical input is always
/// rejected, never silently accepted.
pub type DecodeError {
  /// Input ended in the middle of a field.
  Truncated
  /// Leading tag byte is not in 0x00–0x09.
  UnknownTag(Int)
  /// Algorithm byte in a digest field is not recognised.
  UnknownHashAlgorithm(Int)
  /// Scheme byte in a pubkey field is not recognised.
  UnknownKeyScheme(Int)
  /// Varint has a redundant high-zero group (overlong encoding).
  NonCanonicalVarint
  /// Varint encodes a value greater than u32::MAX.
  VarintOverflow
  /// A complete term decoded but bytes remained after it.
  TrailingBytes
  /// Leading tag byte of a Pattern is not in 0x00–0x04.
  UnknownPatternTag(Int)
}

// ── Encoding ──────────────────────────────────────────────────────────────────

/// Canonical serialization of a term. Total and deterministic.
pub fn encode(t: Term) -> BitArray {
  bytes_tree.to_bit_array(encode_tree(t))
}

fn encode_tree(t: Term) -> BytesTree {
  case t {
    term.Var(n) ->
      bytes_tree.from_bit_array(<<0x00>>)
      |> bytes_tree.append_tree(encode_varint(n))

    term.Sort(u) ->
      bytes_tree.from_bit_array(<<0x01>>)
      |> bytes_tree.append_tree(encode_varint(u))

    term.Pi(a, b) ->
      bytes_tree.from_bit_array(<<0x02>>)
      |> bytes_tree.append_tree(encode_tree(a))
      |> bytes_tree.append_tree(encode_tree(b))

    term.Lam(a, b) ->
      bytes_tree.from_bit_array(<<0x03>>)
      |> bytes_tree.append_tree(encode_tree(a))
      |> bytes_tree.append_tree(encode_tree(b))

    term.App(f, a) ->
      bytes_tree.from_bit_array(<<0x04>>)
      |> bytes_tree.append_tree(encode_tree(f))
      |> bytes_tree.append_tree(encode_tree(a))

    term.Eq(ty, a, b) ->
      bytes_tree.from_bit_array(<<0x05>>)
      |> bytes_tree.append_tree(encode_tree(ty))
      |> bytes_tree.append_tree(encode_tree(a))
      |> bytes_tree.append_tree(encode_tree(b))

    term.Refl(ty, a) ->
      bytes_tree.from_bit_array(<<0x06>>)
      |> bytes_tree.append_tree(encode_tree(ty))
      |> bytes_tree.append_tree(encode_tree(a))

    term.Const(hash_val) ->
      bytes_tree.from_bit_array(<<0x07>>)
      |> bytes_tree.append_tree(encode_digest(hash_val))

    term.Hole(id, ty) ->
      bytes_tree.from_bit_array(<<0x08>>)
      |> bytes_tree.append_tree(encode_varint(id))
      |> bytes_tree.append_tree(encode_tree(ty))

    term.Trusted(host, proc, args, result_ty) ->
      bytes_tree.from_bit_array(<<0x09>>)
      |> bytes_tree.append_tree(encode_pubkey(host))
      |> bytes_tree.append_tree(encode_digest(proc))
      |> bytes_tree.append_tree(encode_tree(args))
      |> bytes_tree.append_tree(encode_tree(result_ty))
  }
}

fn encode_digest(d: Digest) -> BytesTree {
  case d {
    digest.Digest(algo, bytes) -> {
      let tag = digest.algorithm_tag(algo)
      bytes_tree.from_bit_array(<<tag>>)
      |> bytes_tree.append(bytes)
    }
  }
}

fn encode_pubkey(k: PublicKey) -> BytesTree {
  case k {
    pubkey.PublicKey(scheme, bytes) -> {
      let tag = pubkey.scheme_tag(scheme)
      bytes_tree.from_bit_array(<<tag>>)
      |> bytes_tree.append(bytes)
    }
  }
}

// Canonical LEB128 varint encoder. u32 range, little-endian base-128.
fn encode_varint(n: Int) -> BytesTree {
  let b = int.bitwise_and(n, 0x7f)
  let rest = int.bitwise_shift_right(n, 7)
  case rest {
    0 -> bytes_tree.from_bit_array(<<b>>)
    _ -> {
      let b_cont = int.bitwise_or(b, 0x80)
      bytes_tree.from_bit_array(<<b_cont>>)
      |> bytes_tree.append_tree(encode_varint(rest))
    }
  }
}

// ── Encoding: Pattern, Rule, rule sets ─────────────────────────────────────────
//
// Additive only: this does not touch the Term/Digest/HostResult wire format
// above. A rule set (List(Rule)) is content-addressed the same way every
// other object in this codebase is -- hash.gleam's hash_rule_set feeds this
// encoding through digest.hash_bytes, exactly as hash.hash does for Term.

fn encode_pattern_tree(p: Pattern) -> BytesTree {
  case p {
    rewrite.PVar(k) ->
      bytes_tree.from_bit_array(<<0x00>>)
      |> bytes_tree.append_tree(encode_varint(k))

    rewrite.PSort(u) ->
      bytes_tree.from_bit_array(<<0x01>>)
      |> bytes_tree.append_tree(encode_varint(u))

    rewrite.PConst(d) ->
      bytes_tree.from_bit_array(<<0x02>>)
      |> bytes_tree.append_tree(encode_digest(d))

    rewrite.PApp(f, a) ->
      bytes_tree.from_bit_array(<<0x03>>)
      |> bytes_tree.append_tree(encode_pattern_tree(f))
      |> bytes_tree.append_tree(encode_pattern_tree(a))

    rewrite.PRefl(ty, val) ->
      bytes_tree.from_bit_array(<<0x04>>)
      |> bytes_tree.append_tree(encode_pattern_tree(ty))
      |> bytes_tree.append_tree(encode_pattern_tree(val))
  }
}

/// Canonical serialization of a Pattern. Total and deterministic, same
/// tag-then-fields discipline as `encode`.
pub fn encode_pattern(p: Pattern) -> BitArray {
  bytes_tree.to_bit_array(encode_pattern_tree(p))
}

/// Canonical serialization of a Rule: lhs pattern | rhs term | varint nvars.
pub fn encode_rule(r: Rule) -> BitArray {
  bytes_tree.to_bit_array(encode_rule_tree(r))
}

fn encode_rule_tree(r: Rule) -> BytesTree {
  encode_pattern_tree(r.lhs)
  |> bytes_tree.append_tree(encode_tree(r.rhs))
  |> bytes_tree.append_tree(encode_varint(r.nvars))
}

/// Canonical serialization of a rule set: varint count | rule*count, in
/// list order. Order is part of the content address -- two rule sets with
/// the same rules in a different order are, deliberately, different objects
/// (whnf tries rules in order, so order is observable behavior).
pub fn encode_rule_set(rules: List(Rule)) -> BitArray {
  let tree =
    bytes_tree.from_bit_array(<<>>)
    |> bytes_tree.append_tree(encode_varint(list.length(rules)))
  list.fold(rules, tree, fn(acc, r) {
    bytes_tree.append_tree(acc, encode_rule_tree(r))
  })
  |> bytes_tree.to_bit_array
}

// ── Decoding ──────────────────────────────────────────────────────────────────

/// Decode canonical bytes into a term. Rejects non-canonical encodings
/// and trailing bytes.
pub fn decode(bytes: BitArray) -> Result(Term, DecodeError) {
  case decode_term(bytes) {
    Ok(#(t, <<>>)) -> Ok(t)
    Ok(#(_, _)) -> Error(TrailingBytes)
    Error(e) -> Error(e)
  }
}

fn decode_term(data: BitArray) -> Result(#(Term, BitArray), DecodeError) {
  case data {
    <<>> -> Error(Truncated)
    <<tag, rest:bits>> -> decode_by_tag(tag, rest)
    _ -> Error(Truncated)
  }
}

fn decode_by_tag(
  tag: Int,
  rest: BitArray,
) -> Result(#(Term, BitArray), DecodeError) {
  case tag {
    0x00 -> {
      use #(n, r) <- result.try(decode_varint(rest))
      Ok(#(term.Var(n), r))
    }
    0x01 -> {
      use #(u, r) <- result.try(decode_varint(rest))
      Ok(#(term.Sort(u), r))
    }
    0x02 -> {
      use #(a, r2) <- result.try(decode_term(rest))
      use #(b, r3) <- result.try(decode_term(r2))
      Ok(#(term.Pi(a, b), r3))
    }
    0x03 -> {
      use #(a, r2) <- result.try(decode_term(rest))
      use #(b, r3) <- result.try(decode_term(r2))
      Ok(#(term.Lam(a, b), r3))
    }
    0x04 -> {
      use #(f, r2) <- result.try(decode_term(rest))
      use #(a, r3) <- result.try(decode_term(r2))
      Ok(#(term.App(f, a), r3))
    }
    0x05 -> {
      use #(ty, r2) <- result.try(decode_term(rest))
      use #(a, r3) <- result.try(decode_term(r2))
      use #(b, r4) <- result.try(decode_term(r3))
      Ok(#(term.Eq(ty, a, b), r4))
    }
    0x06 -> {
      use #(ty, r2) <- result.try(decode_term(rest))
      use #(a, r3) <- result.try(decode_term(r2))
      Ok(#(term.Refl(ty, a), r3))
    }
    0x07 -> {
      use #(hash_val, r) <- result.try(decode_digest(rest))
      Ok(#(term.Const(hash_val), r))
    }
    0x08 -> {
      use #(id, r2) <- result.try(decode_varint(rest))
      use #(ty, r3) <- result.try(decode_term(r2))
      Ok(#(term.Hole(id, ty), r3))
    }
    0x09 -> {
      use #(host, r2) <- result.try(decode_pubkey(rest))
      use #(proc, r3) <- result.try(decode_digest(r2))
      use #(args, r4) <- result.try(decode_term(r3))
      use #(result_ty, r5) <- result.try(decode_term(r4))
      Ok(#(term.Trusted(host, proc, args, result_ty), r5))
    }
    other -> Error(UnknownTag(other))
  }
}

fn decode_digest(data: BitArray) -> Result(#(Digest, BitArray), DecodeError) {
  case data {
    <<algo_tag, rest:bits>> ->
      case digest.decode_algorithm_tag(algo_tag) {
        Error(Nil) -> Error(UnknownHashAlgorithm(algo_tag))
        Ok(algo) -> {
          let n = digest.digest_size(algo) * 8
          case rest {
            <<bytes:bits-size(n), r:bits>> ->
              Ok(#(digest.Digest(algo, bytes), r))
            _ -> Error(Truncated)
          }
        }
      }
    _ -> Error(Truncated)
  }
}

fn decode_pubkey(data: BitArray) -> Result(#(PublicKey, BitArray), DecodeError) {
  case data {
    <<scheme_tag, rest:bits>> ->
      case pubkey.decode_scheme_tag(scheme_tag) {
        Error(Nil) -> Error(UnknownKeyScheme(scheme_tag))
        Ok(scheme) -> {
          let n = pubkey.key_size(scheme) * 8
          case rest {
            <<bytes:bits-size(n), r:bits>> ->
              Ok(#(pubkey.PublicKey(scheme, bytes), r))
            _ -> Error(Truncated)
          }
        }
      }
    _ -> Error(Truncated)
  }
}

// Strict canonical LEB128 varint decoder.
// Rejects overlong encodings and values exceeding u32::MAX.
fn decode_varint(data: BitArray) -> Result(#(Int, BitArray), DecodeError) {
  decode_varint_loop(data, 0, 0)
}

fn decode_varint_loop(
  data: BitArray,
  acc: Int,
  count: Int,
) -> Result(#(Int, BitArray), DecodeError) {
  case data {
    <<byte, rest:bits>> -> {
      let value = int.bitwise_and(byte, 0x7f)
      let next_acc =
        int.bitwise_or(acc, int.bitwise_shift_left(value, count * 7))
      case next_acc > 4_294_967_295 {
        True -> Error(VarintOverflow)
        False ->
          case int.bitwise_and(byte, 0x80) {
            // Final byte -- reject overlong: multi-byte varint ending in 0x00.
            0 ->
              case count > 0 && byte == 0 {
                True -> Error(NonCanonicalVarint)
                False -> Ok(#(next_acc, rest))
              }
            // Continuation bit -- a u32 needs at most 5 bytes.
            _ ->
              case count >= 4 {
                True -> Error(VarintOverflow)
                False -> decode_varint_loop(rest, next_acc, count + 1)
              }
          }
      }
    }
    _ -> Error(Truncated)
  }
}

// ── Decoding: Pattern, Rule, rule sets ─────────────────────────────────────────

/// Decode canonical bytes into a Pattern. Rejects non-canonical encodings
/// and trailing bytes, same discipline as `decode`.
pub fn decode_pattern(bytes: BitArray) -> Result(Pattern, DecodeError) {
  case decode_pattern_term(bytes) {
    Ok(#(p, <<>>)) -> Ok(p)
    Ok(#(_, _)) -> Error(TrailingBytes)
    Error(e) -> Error(e)
  }
}

fn decode_pattern_term(
  data: BitArray,
) -> Result(#(Pattern, BitArray), DecodeError) {
  case data {
    <<>> -> Error(Truncated)
    <<tag, rest:bits>> -> decode_pattern_by_tag(tag, rest)
    _ -> Error(Truncated)
  }
}

fn decode_pattern_by_tag(
  tag: Int,
  rest: BitArray,
) -> Result(#(Pattern, BitArray), DecodeError) {
  case tag {
    0x00 -> {
      use #(k, r) <- result.try(decode_varint(rest))
      Ok(#(rewrite.PVar(k), r))
    }
    0x01 -> {
      use #(u, r) <- result.try(decode_varint(rest))
      Ok(#(rewrite.PSort(u), r))
    }
    0x02 -> {
      use #(d, r) <- result.try(decode_digest(rest))
      Ok(#(rewrite.PConst(d), r))
    }
    0x03 -> {
      use #(f, r2) <- result.try(decode_pattern_term(rest))
      use #(a, r3) <- result.try(decode_pattern_term(r2))
      Ok(#(rewrite.PApp(f, a), r3))
    }
    0x04 -> {
      use #(ty, r2) <- result.try(decode_pattern_term(rest))
      use #(val, r3) <- result.try(decode_pattern_term(r2))
      Ok(#(rewrite.PRefl(ty, val), r3))
    }
    other -> Error(UnknownPatternTag(other))
  }
}

/// Decode canonical bytes into a Rule.
pub fn decode_rule(bytes: BitArray) -> Result(Rule, DecodeError) {
  case decode_rule_term(bytes) {
    Ok(#(r, <<>>)) -> Ok(r)
    Ok(#(_, _)) -> Error(TrailingBytes)
    Error(e) -> Error(e)
  }
}

fn decode_rule_term(data: BitArray) -> Result(#(Rule, BitArray), DecodeError) {
  use #(lhs, r1) <- result.try(decode_pattern_term(data))
  use #(rhs, r2) <- result.try(decode_term(r1))
  use #(nvars, r3) <- result.try(decode_varint(r2))
  Ok(#(rewrite.Rule(lhs: lhs, rhs: rhs, nvars: nvars), r3))
}

/// Decode canonical bytes into a rule set (a list of Rules, in order).
pub fn decode_rule_set(bytes: BitArray) -> Result(List(Rule), DecodeError) {
  use #(count, r1) <- result.try(decode_varint(bytes))
  use #(rules, r2) <- result.try(decode_rule_list(r1, count, []))
  case r2 {
    <<>> -> Ok(rules)
    _ -> Error(TrailingBytes)
  }
}

fn decode_rule_list(
  data: BitArray,
  remaining: Int,
  acc: List(Rule),
) -> Result(#(List(Rule), BitArray), DecodeError) {
  case remaining <= 0 {
    True -> Ok(#(list.reverse(acc), data))
    False -> {
      use #(r, rest) <- result.try(decode_rule_term(data))
      decode_rule_list(rest, remaining - 1, [r, ..acc])
    }
  }
}
