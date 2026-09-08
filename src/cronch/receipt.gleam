/// A Receipt: a recomputable audit record of one check.
///
/// Outside the kernel and outside the TCB.
///
/// NOT SIGNED. NOT TRUSTED. NOT A CACHE.
/// -------------------------------------
/// Accepting a receipt requires trusting nobody, because verifying one is just
/// recomputing it. `replay` re-runs the check from scratch and returns True
/// only if the receipt it freshly issues is BYTE-IDENTICAL to the one it was
/// handed. Not equivalent -- the same bytes.
///
/// That property is the entire value of this object, and it is fragile in one
/// specific direction: anything that makes a receipt cheaper to accept than to
/// recompute destroys it. So there is no signing here, no authority, no
/// issuer identity, no trusted cache, and no "we already checked this one"
/// short circuit. A receipt from a stranger and a receipt you issued yourself
/// are worth exactly the same, which is to say: worth recomputing.
///
/// Why RejectReason is a closed variant type and never a String
/// -----------------------------------------------------------
/// A receipt's bytes must be reproducible by an independent implementation
/// years from now. Prose messages get reworded by every refactor -- a
/// clarified error message, a renamed variable interpolated into it, a
/// translated string -- and each rewording changes the bytes, so `replay`
/// would start failing on receipts that are perfectly honest. Users who see
/// replay failures that do not mean anything learn to ignore replay failures,
/// and then the one that does mean something goes unnoticed. A closed variant
/// type has no such drift: adding a reason is a deliberate, visible wire
/// change.
///
/// Negative results are first-class
/// --------------------------------
/// `issue` NEVER fails. A rejection or an exhaustion produces a Receipt
/// bearing that verdict. A checkable record that something does NOT typecheck
/// under a stated basis is a real artifact -- it is what lets a consumer
/// distinguish "refuted" from "nobody looked" -- and it costs one variant.
import cronch/basis
import cronch/canonical
import cronch/capability
import cronch/digest.{type Digest, type HashAlgorithm}
import cronch/hash
import cronch/kernel.{type Environment, type Provenance}
import cronch/pubkey.{type PublicKey}
import cronch/serialize
import cronch/term.{type Term}
import cronch/trust.{type Policy, type TrustPair}
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleam/result

/// The only receipt version this implementation issues or accepts.
pub const version: Int = 1

/// The hash algorithm receipts are built with. Fixed rather than a parameter
/// on `issue` so that two verifiers cannot produce differently-hashed receipts
/// for the same check and both be right; `issue_with` takes it explicitly for
/// callers doing algorithm migration.
pub const default_algorithm: HashAlgorithm = digest.Blake3

// ── Verdict ───────────────────────────────────────────────────────────────────

/// Why a check said no. A CLOSED variant type -- never a String. See the
/// module comment for why that is a security property and not a style choice.
pub type RejectReason {
  /// A term's inferred type was not definitionally equal to the expected one.
  TypeMismatch
  /// A de Bruijn index with no binder.
  UnboundVariable
  /// Something in function position whose type is not a Pi.
  NotAFunction
  /// A term used as a type does not denote a sort, or a universe overflowed.
  SortError
  /// A Trusted node whose procedure signature is not a well-formed type, or
  /// is not a function type.
  IllFormedTerm
  /// A Const that resolves in neither the definitions nor the signatures.
  UnknownConstant
  /// A rule set the derivation used that the policy does not authorize.
  UnauthorizedRuleSet
  /// A Trusted-node host the policy does not authorize.
  UnauthorizedHost
  /// The artifact reaches host procedures beyond the capabilities it declared.
  CapabilityExceeded
  /// A rewrite rule that is not well-formed.
  MalformedRule
}

/// Every reason, in wire-tag order. Used by the round-trip tests, and the
/// place to add a variant if one is ever needed.
pub fn all_reject_reasons() -> List(RejectReason) {
  [
    TypeMismatch,
    UnboundVariable,
    NotAFunction,
    SortError,
    IllFormedTerm,
    UnknownConstant,
    UnauthorizedRuleSet,
    UnauthorizedHost,
    CapabilityExceeded,
    MalformedRule,
  ]
}

/// What a check concluded. Three outcomes, never two: `Exhausted` is not a
/// rejection and must never be read as one.
pub type Verdict {
  Accepted
  Rejected(RejectReason)
  Exhausted
}

/// Map a kernel error onto the closed reason set.
///
/// `FuelExhausted` is deliberately absent: it is not a rejection, and the
/// caller must have handled it as `Exhausted` before reaching here. It maps to
/// `SortError` only because this function is total; no path in this module
/// reaches that case, and the `Exhausted` verdict is produced first.
pub fn reason_of(error: kernel.TypeError) -> RejectReason {
  case error {
    kernel.Mismatch(_, _) -> TypeMismatch
    kernel.TrustedCodomainMismatch(_, _) -> TypeMismatch
    kernel.UnboundVar(_) -> UnboundVariable
    kernel.NotAFunction(_) -> NotAFunction
    kernel.ExpectedSort(_) -> SortError
    kernel.UniverseOverflow -> SortError
    kernel.TrustedProcNotAType(_) -> IllFormedTerm
    kernel.TrustedProcNotPi(_) -> IllFormedTerm
    kernel.Unresolved(_) -> UnknownConstant
    kernel.FuelExhausted -> SortError
  }
}

// ── Receipt ───────────────────────────────────────────────────────────────────

/// One check, recorded.
pub type Receipt {
  Receipt(
    /// Wire version. Only `1` is issued or accepted.
    version: Int,
    /// The context the check ran against.
    basis: Digest,
    /// Content address of the term that was checked.
    artifact: Digest,
    /// Content address of the declared type -- the contract.
    spec: Digest,
    /// DIRECT Const references in the artifact, sorted. Not transitive: this
    /// keeps each receipt O(its own term). Transitivity is the ledger's job.
    deps: List(Digest),
    /// References with no definition, sorted. The same set the named basis
    /// commits to, so a receipt and its basis cannot disagree about what was
    /// assumed.
    axioms: List(Digest),
    /// Trust dependencies the acceptance rested on, from the derivation.
    trust_set: List(TrustPair),
    /// The digest of the artifact's capability set: which host procedures it
    /// can reach, transitively. A single-element list rather than a bare
    /// Digest so that a future receipt can name several capability views
    /// without a wire break; empty only for a set that could not be computed
    /// at all, which never happens here because an unresolvable reference has
    /// its own digest (see capability.gleam).
    capabilities: List(Digest),
    /// The budget the check was given.
    fuel_declared: Int,
    /// The reduction steps the derivation actually performed.
    fuel_used: Int,
    verdict: Verdict,
  )
}

/// Sort and dedupe every set-valued field. Applied by `issue` and before every
/// encoding, so two receipts describing the same check are the same bytes.
pub fn canonicalize(r: Receipt) -> Receipt {
  Receipt(
    ..r,
    deps: canonical.sort_digests(r.deps),
    axioms: canonical.sort_digests(r.axioms),
    trust_set: sort_trust(r.trust_set),
    capabilities: canonical.sort_digests(r.capabilities),
  )
}

fn sort_trust(pairs: List(TrustPair)) -> List(TrustPair) {
  pairs
  |> list.unique
  |> list.sort(fn(a, b) {
    canonical.compare_bytes(trust_bytes(a), trust_bytes(b))
  })
}

fn trust_bytes(p: TrustPair) -> BitArray {
  case p {
    trust.HostTrust(host, proc) ->
      bit_array.concat([
        <<0x00>>,
        serialize.pubkey_field(host),
        serialize.digest_field(proc),
      ])
    trust.RuleSetTrust(author, hash_val) ->
      bit_array.concat([
        <<0x01>>,
        serialize.pubkey_field(author),
        serialize.digest_field(hash_val),
      ])
  }
}

// ── Issuing ───────────────────────────────────────────────────────────────────

/// Issue a receipt for one check. NEVER fails.
///
/// `kernel_id` is supplied by whoever is doing the checking, and is never read
/// out of anything being checked. That is what makes `replay` a real test: a
/// verifier replays with ITS OWN kernel identity, so a receipt issued by a
/// different kernel produces a different basis digest and fails to replay,
/// rather than being accepted on the strength of a claim it carries about
/// itself.
///
/// The basis names the context as EXERCISED -- its rule sets and hosts are the
/// ones the derivation actually depended on -- because a `kernel.Environment`
/// is a set of pure functions with no key listing and cannot be enumerated.
pub fn issue(
  kernel_id: String,
  environment: Environment,
  provenance: Provenance,
  fuel_declared: Int,
  t: Term,
  typ: Term,
) -> Receipt {
  issue_with(
    default_algorithm,
    kernel_id,
    environment,
    provenance,
    None,
    fuel_declared,
    t,
    typ,
  )
}

/// Issue a receipt and additionally gate the result on a trust policy.
///
/// A check that succeeds mathematically but uses a rule set or host the policy
/// does not authorize is `Rejected(UnauthorizedRuleSet)` or
/// `Rejected(UnauthorizedHost)` -- a refusal, recorded, rather than an
/// acceptance with a caveat.
pub fn issue_under_policy(
  kernel_id: String,
  environment: Environment,
  provenance: Provenance,
  policy: Policy,
  fuel_declared: Int,
  t: Term,
  typ: Term,
) -> Receipt {
  issue_with(
    default_algorithm,
    kernel_id,
    environment,
    provenance,
    Some(policy),
    fuel_declared,
    t,
    typ,
  )
}

/// The one issuing implementation. `policy` of `None` means "do not gate";
/// every other caller above funnels through here so there is a single place
/// where a verdict is decided.
pub fn issue_with(
  algorithm: HashAlgorithm,
  kernel_id: String,
  environment: Environment,
  provenance: Provenance,
  policy: option.Option(Policy),
  fuel_declared: Int,
  t: Term,
  typ: Term,
) -> Receipt {
  let checked =
    kernel.check_reporting(
      environment,
      provenance,
      kernel.Limited(fuel_declared),
      kernel.empty(),
      t,
      typ,
    )

  // The static walk is available whatever happened, so a receipt always
  // records the host dependencies visible in the term itself -- even one that
  // never finished checking.
  let static_pairs = trust.trust_set(environment, t)

  let #(verdict, pairs, fuel_used) = case checked {
    // Reduction hit the guard. No derivation, so the trust set is necessarily
    // incomplete -- which is sound because an Exhausted receipt confers no
    // warrant anywhere (see ledger.gleam).
    Error(kernel.FuelExhausted) -> #(Exhausted, static_pairs, fuel_declared)

    Error(e) -> #(Rejected(reason_of(e)), static_pairs, 0)

    Ok(report) -> {
      let pairs = trust.merge_pairs(environment, t, report)
      case report.fuel_used > fuel_declared {
        // Completed, but cost more than declared. A declared cost that a
        // check exceeds is a hard failure of the artifact's claim,
        // independent of whether the mathematics worked out -- so no verdict,
        // not an acceptance.
        True -> #(Exhausted, pairs, report.fuel_used)
        False -> #(gate(pairs, policy), pairs, report.fuel_used)
      }
    }
  }

  let b =
    basis.from_environment(
      kernel_id,
      environment,
      rule_sets_of(pairs),
      hosts_of(pairs),
      t,
    )

  canonicalize(Receipt(
    version: version,
    basis: basis.digest(algorithm, b),
    artifact: hash.hash(algorithm, t),
    spec: hash.hash(algorithm, typ),
    deps: direct_deps(t),
    axioms: b.axioms,
    trust_set: pairs,
    capabilities: [
      capability.digest(algorithm, capability.of_term(t, environment)),
    ],
    fuel_declared: fuel_declared,
    fuel_used: fuel_used,
    verdict: verdict,
  ))
}

// Apply the policy, if there is one. A trust set entry the policy does not
// cover turns an otherwise-successful check into a recorded refusal.
fn gate(pairs: List(TrustPair), policy: option.Option(Policy)) -> Verdict {
  case policy {
    None -> Accepted
    Some(p) ->
      case trust.unauthorized(pairs, p) {
        [] -> Accepted
        // Host first: a host dependency is authority over a *result*, which
        // is strictly the more serious of the two, so it is the reason
        // reported when both are present.
        unauthorized ->
          case list.any(unauthorized, is_host) {
            True -> Rejected(UnauthorizedHost)
            False -> Rejected(UnauthorizedRuleSet)
          }
      }
  }
}

fn is_host(p: TrustPair) -> Bool {
  case p {
    trust.HostTrust(_, _) -> True
    trust.RuleSetTrust(_, _) -> False
  }
}

fn rule_sets_of(pairs: List(TrustPair)) -> List(#(PublicKey, Digest)) {
  list.filter_map(pairs, fn(p) {
    case p {
      trust.RuleSetTrust(author, h) -> Ok(#(author, h))
      trust.HostTrust(_, _) -> Error(Nil)
    }
  })
}

fn hosts_of(pairs: List(TrustPair)) -> List(PublicKey) {
  list.filter_map(pairs, fn(p) {
    case p {
      trust.HostTrust(host, _) -> Ok(host)
      trust.RuleSetTrust(_, _) -> Error(Nil)
    }
  })
}

/// Direct `Const` references in a term. Its own structure only -- nothing is
/// followed into the store, so this is O(the term).
pub fn direct_deps(t: Term) -> List(Digest) {
  canonical.sort_digests(collect_consts(t, []))
}

fn collect_consts(t: Term, acc: List(Digest)) -> List(Digest) {
  case t {
    term.Var(_) | term.Sort(_) -> acc
    term.Const(d) -> [d, ..acc]
    term.Pi(a, b) | term.Lam(a, b) -> collect_consts(b, collect_consts(a, acc))
    term.App(f, a) -> collect_consts(a, collect_consts(f, acc))
    term.Eq(typ, a, b) ->
      collect_consts(b, collect_consts(a, collect_consts(typ, acc)))
    term.Refl(typ, a) -> collect_consts(a, collect_consts(typ, acc))
    term.Hole(_, goal) -> collect_consts(goal, acc)
    // A Trusted node's procedure is a store reference like any other, so it
    // is a dependency: revoking the object it names must reach this artifact.
    term.Trusted(_, proc, args, rty) ->
      collect_consts(rty, collect_consts(args, [proc, ..acc]))
  }
}

/// The content address of a term, under the algorithm receipts use.
///
/// This is `hash.hash`, the pre-existing address every `Const` in every store
/// already carries -- NOT the tagged `canonical.term_digest`. A receipt's
/// `artifact` and `spec` have to be the addresses the store answers to, or
/// `replay` could not fetch what a receipt names.
pub fn term_address(t: Term) -> Digest {
  hash.hash(default_algorithm, t)
}

// ── Digest and encoding ───────────────────────────────────────────────────────

/// A receipt's own content address, under kind tag 0x02.
pub fn digest(algorithm: HashAlgorithm, r: Receipt) -> Digest {
  canonical.digest_of(algorithm, canonical.KindReceipt, payload(r))
}

/// Canonical bytes of a receipt. Fixed field order, counted lists, sets
/// sorted by raw bytes, no floats, nothing whose order is unspecified.
pub fn encode(r: Receipt) -> BitArray {
  canonical.envelope(canonical.KindReceipt, payload(r))
}

fn payload(r0: Receipt) -> BitArray {
  let r = canonicalize(r0)
  bit_array.concat([
    serialize.varint(r.version),
    serialize.digest_field(r.basis),
    serialize.digest_field(r.artifact),
    serialize.digest_field(r.spec),
    canonical.digest_list(r.deps),
    canonical.digest_list(r.axioms),
    trust_list(r.trust_set),
    canonical.digest_list(r.capabilities),
    serialize.varint(r.fuel_declared),
    serialize.varint(r.fuel_used),
    verdict_bytes(r.verdict),
  ])
}

fn trust_list(pairs: List(TrustPair)) -> BitArray {
  bit_array.concat([
    serialize.varint(list.length(pairs)),
    ..list.map(pairs, trust_bytes)
  ])
}

fn verdict_bytes(v: Verdict) -> BitArray {
  case v {
    Accepted -> <<0x00>>
    Rejected(reason) -> <<0x01, { reason_tag(reason) }>>
    Exhausted -> <<0x02>>
  }
}

/// The wire tag of a reject reason. Never changes for an existing variant.
pub fn reason_tag(reason: RejectReason) -> Int {
  case reason {
    TypeMismatch -> 0x00
    UnboundVariable -> 0x01
    NotAFunction -> 0x02
    SortError -> 0x03
    IllFormedTerm -> 0x04
    UnknownConstant -> 0x05
    UnauthorizedRuleSet -> 0x06
    UnauthorizedHost -> 0x07
    CapabilityExceeded -> 0x08
    MalformedRule -> 0x09
  }
}

fn reason_of_tag(tag: Int) -> Result(RejectReason, DecodeError) {
  case tag {
    0x00 -> Ok(TypeMismatch)
    0x01 -> Ok(UnboundVariable)
    0x02 -> Ok(NotAFunction)
    0x03 -> Ok(SortError)
    0x04 -> Ok(IllFormedTerm)
    0x05 -> Ok(UnknownConstant)
    0x06 -> Ok(UnauthorizedRuleSet)
    0x07 -> Ok(UnauthorizedHost)
    0x08 -> Ok(CapabilityExceeded)
    0x09 -> Ok(MalformedRule)
    other -> Error(UnknownReasonTag(other))
  }
}

// ── Decoding ──────────────────────────────────────────────────────────────────

/// Why a byte string is not a receipt. Every one of these is a refusal; there
/// is no lenient path and no partial decode.
pub type DecodeError {
  /// A field failed the shared canonical decoder.
  Field(serialize.DecodeError)
  /// The leading kind tag is not a Receipt's.
  NotAReceipt(Int)
  /// The envelope format version is not this implementation's.
  UnknownEnvelopeVersion(Int)
  /// The receipt's declared version is not 1.
  UnsupportedVersion(Int)
  /// The verdict tag is not 0x00, 0x01 or 0x02.
  UnknownVerdictTag(Int)
  /// The reject reason tag is not one of the ten declared reasons.
  UnknownReasonTag(Int)
  /// A trust-pair kind byte is neither host (0x00) nor rule set (0x01).
  UnknownTrustTag(Int)
  /// The bytes decoded, but their set-valued fields were not sorted and
  /// deduplicated -- so re-encoding would not reproduce them. Canonical
  /// encoding means exactly one byte string per receipt; accepting a second
  /// one would give the same receipt two identities and break replay.
  NonCanonical
  /// A complete receipt decoded but bytes remained after it.
  Trailing
  /// Input ended in the middle of a field.
  Incomplete
}

fn field(r: Result(a, serialize.DecodeError)) -> Result(a, DecodeError) {
  result.map_error(r, Field)
}

/// Read a receipt back from canonical bytes.
///
/// Total: every malformed, truncated, over-long, non-canonical or
/// unrecognized input yields an error. It never panics, never loops, and never
/// allocates for a declared length it has not actually read.
///
/// Round-trip contract, the same one `serialize` holds for terms:
/// `decode(encode(r)) == Ok(canonicalize(r))`, and any `bytes` that decodes at
/// all satisfies `encode(decode(bytes)) == bytes`.
pub fn decode(bytes: BitArray) -> Result(Receipt, DecodeError) {
  use rest <- result.try(strip_envelope(bytes))
  use #(v, r1) <- result.try(field(serialize.take_varint(rest)))
  // Version is checked BEFORE anything else is interpreted. A future version's
  // fields could mean anything, so reading them under this version's layout
  // would be guessing.
  use _ <- result.try(case v == version {
    True -> Ok(Nil)
    False -> Error(UnsupportedVersion(v))
  })
  use #(basis_digest, r2) <- result.try(field(serialize.take_digest(r1)))
  use #(artifact, r3) <- result.try(field(serialize.take_digest(r2)))
  use #(spec, r4) <- result.try(field(serialize.take_digest(r3)))
  use #(deps, r5) <- result.try(field(canonical.take_digest_list(r4)))
  use #(axioms, r6) <- result.try(field(canonical.take_digest_list(r5)))
  use #(trust_set, r7) <- result.try(take_trust_list(r6))
  use #(capabilities, r8) <- result.try(field(canonical.take_digest_list(r7)))
  use #(fuel_declared, r9) <- result.try(field(serialize.take_varint(r8)))
  use #(fuel_used, r10) <- result.try(field(serialize.take_varint(r9)))
  use #(verdict, r11) <- result.try(take_verdict(r10))
  use _ <- result.try(case r11 {
    <<>> -> Ok(Nil)
    _ -> Error(Trailing)
  })
  let decoded =
    Receipt(
      version: v,
      basis: basis_digest,
      artifact: artifact,
      spec: spec,
      deps: deps,
      axioms: axioms,
      trust_set: trust_set,
      capabilities: capabilities,
      fuel_declared: fuel_declared,
      fuel_used: fuel_used,
      verdict: verdict,
    )
  // Exactly one byte string per receipt, in both directions. A list that
  // arrived out of order or with a repeat would re-encode to different bytes,
  // which would give one receipt two identities -- and `replay`, which
  // compares bytes, would then be comparing the wrong thing.
  case canonicalize(decoded) == decoded {
    True -> Ok(decoded)
    False -> Error(NonCanonical)
  }
}

fn strip_envelope(bytes: BitArray) -> Result(BitArray, DecodeError) {
  let expected = canonical.kind_tag(canonical.KindReceipt)
  case bytes {
    <<tag, 0xFF, 0xFF, 0xFF, 0xFF, rest:bits>> if tag == expected -> {
      use #(v, r) <- result.try(field(serialize.take_varint(rest)))
      case v == canonical.format_version {
        True -> Ok(r)
        False -> Error(UnknownEnvelopeVersion(v))
      }
    }
    <<tag, _:bits>> -> Error(NotAReceipt(tag))
    _ -> Error(Incomplete)
  }
}

fn take_trust_list(
  data: BitArray,
) -> Result(#(List(TrustPair), BitArray), DecodeError) {
  use #(count, rest) <- result.try(field(serialize.take_varint(data)))
  take_trust_n(rest, count, [])
}

// One element at a time out of the bytes actually present, so a declared
// count of four billion fails on the first element it cannot read.
fn take_trust_n(
  data: BitArray,
  remaining: Int,
  acc: List(TrustPair),
) -> Result(#(List(TrustPair), BitArray), DecodeError) {
  case remaining <= 0 {
    True -> Ok(#(list.reverse(acc), data))
    False ->
      case data {
        <<kind, rest:bits>> -> {
          use #(key, r1) <- result.try(field(serialize.take_pubkey(rest)))
          use #(d, r2) <- result.try(field(serialize.take_digest(r1)))
          use pair <- result.try(case kind {
            0x00 -> Ok(trust.HostTrust(key, d))
            0x01 -> Ok(trust.RuleSetTrust(key, d))
            other -> Error(UnknownTrustTag(other))
          })
          take_trust_n(r2, remaining - 1, [pair, ..acc])
        }
        _ -> Error(Incomplete)
      }
  }
}

fn take_verdict(data: BitArray) -> Result(#(Verdict, BitArray), DecodeError) {
  case data {
    <<0x00, rest:bits>> -> Ok(#(Accepted, rest))
    <<0x01, tag, rest:bits>> -> {
      use reason <- result.try(reason_of_tag(tag))
      Ok(#(Rejected(reason), rest))
    }
    <<0x01>> -> Error(Incomplete)
    <<0x02, rest:bits>> -> Ok(#(Exhausted, rest))
    <<other, _:bits>> -> Error(UnknownVerdictTag(other))
    _ -> Error(Incomplete)
  }
}

// ── Replay ────────────────────────────────────────────────────────────────────

/// Re-run the check from scratch and report whether the freshly issued receipt
/// is BYTE-IDENTICAL to the supplied one.
///
/// Not "equivalent". Not "compatible". The same bytes. Equivalence would need
/// a notion of which differences are acceptable, and every such notion is a
/// place for an attacker to live.
///
/// `kernel_id` is the VERIFIER's own kernel identity, never read out of the
/// receipt. A receipt issued under a different kernel produces a different
/// basis digest and fails here -- which is the correct answer, because this
/// verifier cannot vouch for a check it did not perform.
///
/// The artifact and its spec are resolved out of `environment.definitions` by
/// the content addresses the receipt carries. If either does not resolve, the
/// answer is False: absence of the thing being attested is not evidence for
/// the attestation.
pub fn replay(
  r: Receipt,
  kernel_id: String,
  environment: Environment,
  provenance: Provenance,
) -> Bool {
  case environment.definitions(r.artifact), environment.definitions(r.spec) {
    Some(t), Some(typ) ->
      replay_terms(r, kernel_id, environment, provenance, t, typ)
    _, _ -> False
  }
}

/// `replay` for a caller that already holds the artifact and its spec.
///
/// The terms are re-hashed and checked against the receipt's own addresses
/// first, so handing this the wrong pair cannot make a receipt replay.
pub fn replay_terms(
  r: Receipt,
  kernel_id: String,
  environment: Environment,
  provenance: Provenance,
  t: Term,
  typ: Term,
) -> Bool {
  case
    hash.hash(default_algorithm, t) == r.artifact
    && hash.hash(default_algorithm, typ) == r.spec
  {
    False -> False
    True -> {
      let fresh =
        issue(kernel_id, environment, provenance, r.fuel_declared, t, typ)
      encode(fresh) == encode(r)
    }
  }
}
