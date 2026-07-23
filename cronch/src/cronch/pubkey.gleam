/// An asymmetric public key: the scheme used and the raw key bytes.
///
/// Every scheme has a fixed key size and a 1-byte wire tag. Adding a new
/// scheme is: add a variant here and handle it in the three functions below.

pub type KeyScheme {
  Ed25519
}

pub type PublicKey {
  PublicKey(scheme: KeyScheme, bytes: BitArray)
}

/// The 1-byte wire tag for a key scheme. Never changes for an existing variant.
pub fn scheme_tag(scheme: KeyScheme) -> Int {
  case scheme {
    Ed25519 -> 0x00
  }
}

/// Reverse of `scheme_tag`. Returns `Error(Nil)` for unknown tags.
pub fn decode_scheme_tag(tag: Int) -> Result(KeyScheme, Nil) {
  case tag {
    0x00 -> Ok(Ed25519)
    _ -> Error(Nil)
  }
}

/// Key size in bytes for the given scheme.
pub fn key_size(scheme: KeyScheme) -> Int {
  case scheme {
    Ed25519 -> 32
  }
}

/// The lowercase prefix used in address strings, e.g. `"ed25519"`.
pub fn scheme_name(scheme: KeyScheme) -> String {
  case scheme {
    Ed25519 -> "ed25519"
  }
}

/// All currently registered key schemes. Used for address parsing so new
/// schemes are automatically tried once added here.
pub fn all_schemes() -> List(KeyScheme) {
  [Ed25519]
}
