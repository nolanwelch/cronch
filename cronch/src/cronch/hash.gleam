/// Content addressing of terms.
///
/// An address is a self-describing string:
///
///   address = algorithm_name ":" lowerhex(digest_bytes)
///
/// The algorithm name is inside the string so it is unambiguous which hash
/// function produced a given address. A consumer must check the prefix before
/// interpreting the bytes.
import cronch/digest.{type Digest, type HashAlgorithm, Digest}
import cronch/rewrite.{type Rule}
import cronch/serialize
import cronch/term.{type Term}
import gleam/bit_array
import gleam/string

/// Hash a term's canonical bytes with the given algorithm.
pub fn hash(algorithm: HashAlgorithm, t: Term) -> Digest {
  digest.hash_bytes(algorithm, serialize.encode(t))
}

/// Hash a rule set's canonical bytes with the given algorithm. A rule set
/// is content-addressed the same way a term is -- see
/// serialize.encode_rule_set for the wire format.
pub fn hash_rule_set(algorithm: HashAlgorithm, rules: List(Rule)) -> Digest {
  digest.hash_bytes(algorithm, serialize.encode_rule_set(rules))
}

/// Self-describing string address for an already-computed digest.
pub fn address_of(d: Digest) -> String {
  let Digest(algorithm, bytes) = d

  digest.algorithm_name(algorithm)
  <> ":"
  <> { bytes |> bit_array.base16_encode |> string.lowercase }
}

/// Compute and format the address of a term.
pub fn address(algorithm: HashAlgorithm, t: Term) -> String {
  address_of(hash(algorithm, t))
}

/// Parse an `"<algorithm>:<lowerhex-digest>"` address string into a Digest.
/// Returns `Error(Nil)` for any malformed input (wrong prefix, bad length,
/// invalid hex, unknown algorithm).
pub fn parse_address(s: String) -> Result(Digest, Nil) {
  try_algorithms(s, digest.all_algorithms())
}

fn try_algorithms(
  s: String,
  algorithms: List(HashAlgorithm),
) -> Result(Digest, Nil) {
  // Split once on ":" to separate the algorithm name from the hex digest.
  // A valid address has exactly one colon, so any other split result is rejected.
  case string.split(s, on: ":") {
    [name, hex] -> match_algorithm(name, hex, algorithms)
    _ -> Error(Nil)
  }
}

fn match_algorithm(
  name: String,
  hex: String,
  algorithms: List(HashAlgorithm),
) -> Result(Digest, Nil) {
  case algorithms {
    [] -> Error(Nil)
    [algorithm, ..rest] ->
      case
        digest.algorithm_name(algorithm) == name
        && string.length(hex) == digest.digest_size(algorithm) * 2
      {
        False -> match_algorithm(name, hex, rest)
        True ->
          case hex |> string.uppercase |> bit_array.base16_decode {
            Ok(bytes) -> Ok(Digest(algorithm, bytes))
            Error(_) -> Error(Nil)
          }
      }
  }
}
