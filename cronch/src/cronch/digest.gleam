/// A content digest: a hash algorithm plus its raw output bytes.
///
/// Every algorithm has a fixed-size output and a 1-byte wire tag. Adding a
/// new algorithm is: add a variant here, handle it in the five functions below,
/// and add it to `all_algorithms`.

import gblake3

pub type HashAlgorithm {
  Blake3
}

pub type Digest {
  Digest(algorithm: HashAlgorithm, bytes: BitArray)
}

/// Hash `data` with the given algorithm.
pub fn hash_bytes(algo: HashAlgorithm, data: BitArray) -> Digest {
  let bytes = case algo {
    Blake3 -> gblake3.hash(data)
  }
  Digest(algo, bytes)
}

/// The 1-byte wire tag for an algorithm. Never changes for an existing variant.
pub fn algorithm_tag(algo: HashAlgorithm) -> Int {
  case algo {
    Blake3 -> 0x00
  }
}

/// Reverse of `algorithm_tag`. Returns `Error(Nil)` for unknown tags.
pub fn decode_algorithm_tag(tag: Int) -> Result(HashAlgorithm, Nil) {
  case tag {
    0x00 -> Ok(Blake3)
    _ -> Error(Nil)
  }
}

/// The lowercase prefix used in address strings, e.g. `"blake3"`.
pub fn algorithm_name(algo: HashAlgorithm) -> String {
  case algo {
    Blake3 -> "blake3"
  }
}

/// Digest output size in bytes for the given algorithm.
pub fn digest_size(algo: HashAlgorithm) -> Int {
  case algo {
    Blake3 -> 32
  }
}

/// All currently registered algorithms. Used for address parsing so new
/// algorithms are automatically tried once added here.
pub fn all_algorithms() -> List(HashAlgorithm) {
  [Blake3]
}
