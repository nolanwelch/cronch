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
import cronch/serialize
import cronch/term.{type Term}
import gleam/bit_array
import gleam/string

/// Hash a term's canonical bytes with the given algorithm.
pub fn hash(algo: HashAlgorithm, t: Term) -> Digest {
  digest.hash_bytes(algo, serialize.encode(t))
}

/// Self-describing string address for an already-computed digest.
pub fn address_of(d: Digest) -> String {
  case d {
    Digest(algo, bytes) ->
      digest.algorithm_name(algo)
      <> ":"
      <> { bytes |> bit_array.base16_encode |> string.lowercase }
  }
}

/// Compute and format the address of a term.
pub fn address(algo: HashAlgorithm, t: Term) -> String {
  address_of(hash(algo, t))
}

/// Parse an `"<algorithm>:<lowerhex-digest>"` address string into a Digest.
/// Returns `Error(Nil)` for any malformed input (wrong prefix, bad length,
/// invalid hex, unknown algorithm).
pub fn parse_address(s: String) -> Result(Digest, Nil) {
  try_algorithms(s, digest.all_algorithms())
}

fn try_algorithms(
  s: String,
  algos: List(HashAlgorithm),
) -> Result(Digest, Nil) {
  // Split once on ":" to separate the algorithm name from the hex digest.
  // A valid address has exactly one colon, so any other split result is rejected.
  case string.split(s, on: ":") {
    [name, hex] -> match_algorithm(name, hex, algos)
    _ -> Error(Nil)
  }
}

fn match_algorithm(
  name: String,
  hex: String,
  algos: List(HashAlgorithm),
) -> Result(Digest, Nil) {
  case algos {
    [] -> Error(Nil)
    [algo, ..rest] ->
      case
        digest.algorithm_name(algo) == name
        && string.length(hex) == digest.digest_size(algo) * 2
      {
        False -> match_algorithm(name, hex, rest)
        True ->
          case hex |> string.uppercase |> bit_array.base16_decode {
            Ok(bytes) -> Ok(Digest(algo, bytes))
            Error(_) -> Error(Nil)
          }
      }
  }
}
