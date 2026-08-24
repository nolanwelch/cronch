/// A Basis: the complete checking context, named by a single hash.
///
/// Outside the kernel and outside the TCB. A Basis decides nothing; it records
/// what a check was run *against*, so that "this artifact typechecks" is a
/// claim with a subject rather than a floating assertion.
///
/// THE FLOOR IS CHOSEN LOCALLY. NEVER NEGOTIATED.
/// ---------------------------------------------
/// `BasisFloor` is what a verifier is willing to accept. There is deliberately
/// no function in this module -- or anywhere in this codebase -- that derives,
/// relaxes, intersects, merges, or negotiates a floor from external input, and
/// none should ever be added. A floor that can be influenced by the party
/// whose artifact is being judged is not a floor.
///
/// If a handshake protocol is ever built on top of this, the only thing it may
/// do with a peer's stated basis is compare it against a floor held locally and
/// abort on failure. It may not adopt the peer's floor, meet it halfway, or
/// compute a common denominator. `satisfies/2` takes the floor second and
/// returns a Bool for exactly this reason: there is no combining operation to
/// reach for.
///
/// No wire protocol, socket or peer negotiation is implemented here, and none
/// is stubbed.
///
/// Why axioms are a field
/// ----------------------
/// `axioms` are the artifact's unproven postulates: constants it refers to
/// that the store can type but cannot define. They are load-bearing and must
/// be visible, because an inconsistent axiom set makes every certificate under
/// it typecheck perfectly while proving nothing. A basis that hides its axioms
/// is worse than no basis, since it manufactures confidence.
import cronch/canonical
import cronch/digest.{type Digest, type HashAlgorithm}
import cronch/kernel.{type Environment}
import cronch/pubkey.{type PublicKey}
import cronch/serialize.{type DecodeError}
import cronch/term.{type Term}
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleam/result

/// Everything a check was run against.
///
/// `kernel_id` names the checker itself: a different kernel is a different
/// basis even over identical axioms, because soundness is a property of the
/// kernel and not of the inputs.
pub type Basis {
  Basis(
    kernel_id: String,
    /// Declared constants with NO definition -- the artifact's postulates.
    axioms: List(Digest),
    /// The signed rule sets admissible here, as (author, rule-set hash).
    rule_sets: List(#(PublicKey, Digest)),
    /// Trusted-node hosts admissible here.
    hosts: List(PublicKey),
  )
}

/// Sort every field by raw digest/key bytes and drop duplicates.
///
/// Idempotent, and a fixed point of itself: `canonicalize(canonicalize(b)) ==
/// canonicalize(b)`. Two bases that differ only in the order somebody happened
/// to list their axioms are the same basis and must hash the same, so this
/// runs before every digest.
pub fn canonicalize(b: Basis) -> Basis {
  Basis(
    kernel_id: b.kernel_id,
    axioms: canonical.sort_digests(b.axioms),
    rule_sets: canonical.sort_key_digests(b.rule_sets),
    hosts: canonical.sort_pubkeys(b.hosts),
  )
}

/// The canonical bytes of a basis, under kind tag 0x01.
///
/// Fixed field order, length-prefixed strings, counted lists, sets sorted by
/// raw bytes. Canonicalized first, so the encoding is a function of the basis
/// as a value and not of how it was written down.
pub fn encode(b: Basis) -> BitArray {
  canonical.envelope(canonical.KindBasis, payload(b))
}

fn payload(b: Basis) -> BitArray {
  let c = canonicalize(b)
  bit_array.concat([
    canonical.string_field(c.kernel_id),
    canonical.digest_list(c.axioms),
    canonical.key_digest_list(c.rule_sets),
    canonical.pubkey_list(c.hosts),
  ])
}

/// A basis's content address.
pub fn digest(algorithm: HashAlgorithm, b: Basis) -> Digest {
  canonical.digest_of(algorithm, canonical.KindBasis, payload(b))
}

/// Read a basis back. Fails closed on anything malformed, truncated or
/// trailing.
pub fn decode(bytes: BitArray) -> Result(Basis, DecodeError) {
  use rest <- result.try(strip_envelope(bytes))
  use #(kernel_id, r1) <- result.try(canonical.take_string(rest))
  use #(axioms, r2) <- result.try(canonical.take_digest_list(r1))
  use #(rule_sets, r3) <- result.try(canonical.take_key_digest_list(r2))
  use #(hosts, r4) <- result.try(canonical.take_pubkey_list(r3))
  use _ <- result.try(case r4 {
    <<>> -> Ok(Nil)
    _ -> Error(serialize.TrailingBytes)
  })
  let decoded =
    Basis(
      kernel_id: kernel_id,
      axioms: axioms,
      rule_sets: rule_sets,
      hosts: hosts,
    )
  // Canonical means canonical in both directions: a basis whose fields arrived
  // out of order or with repeats would re-encode to different bytes, giving
  // one basis two digests.
  case canonicalize(decoded) == decoded {
    True -> Ok(decoded)
    False -> Error(serialize.TrailingBytes)
  }
}

// Check and remove the kind tag, guard bytes and format version. Any deviation
// is a decode error, including a kind tag belonging to a different artifact
// class -- that is the whole point of the tag.
fn strip_envelope(bytes: BitArray) -> Result(BitArray, DecodeError) {
  let expected = canonical.kind_tag(canonical.KindBasis)
  case bytes {
    <<tag, 0xFF, 0xFF, 0xFF, 0xFF, rest:bits>> if tag == expected -> {
      use #(version, r) <- result.try(serialize.take_varint(rest))
      case version == canonical.format_version {
        True -> Ok(r)
        False -> Error(serialize.UnknownTag(version))
      }
    }
    <<tag, _:bits>> -> Error(serialize.UnknownTag(tag))
    _ -> Error(serialize.Truncated)
  }
}

// ── Building a basis from an environment ──────────────────────────────────────

/// Derive the basis an artifact is checked under.
///
/// `axioms` is computed from the artifact's own reachable constants, not by
/// enumerating a store: a `kernel.Store` is a pure function with no key
/// listing, so there is nothing to enumerate. A reachable `Const` counts as an
/// axiom when the environment gives it a signature but no definition -- a
/// declared type and no body is exactly what an axiom is.
///
/// A `Const` that resolves in NEITHER store is unresolvable. It is recorded as
/// an axiom too, and deliberately so: the check that follows will fail on it
/// with `Unresolved`, and until then it is an assumption the artifact is
/// making about a name nobody can supply. Silently dropping it would let an
/// artifact shrink its declared assumption set by referring to things that do
/// not exist.
///
/// `rule_sets` and `hosts` come from `provenance` and from the caller
/// respectively, because neither is derivable from an `Environment`: the rule
/// store hands back bare rules with no author, and nothing enumerates hosts.
pub fn from_environment(
  kernel_id: String,
  environment: Environment,
  rule_sets: List(#(PublicKey, Digest)),
  hosts: List(PublicKey),
  t: Term,
) -> Basis {
  canonicalize(Basis(
    kernel_id: kernel_id,
    axioms: axioms_of(environment, t),
    rule_sets: rule_sets,
    hosts: hosts,
  ))
}

/// Every constant an artifact reaches, transitively through definitions, that
/// has no definition of its own. Sorted and deduplicated.
///
/// The visited set is not an optimization: a store is supplied by whoever is
/// being checked, and nothing stops it returning terms that refer back to each
/// other. Termination must not depend on the graph being acyclic.
pub fn axioms_of(environment: Environment, t: Term) -> List(Digest) {
  let #(found, _) = walk(environment, t, [], [])
  canonical.sort_digests(found)
}

fn walk(
  environment: Environment,
  t: Term,
  found: List(Digest),
  visited: List(Digest),
) -> #(List(Digest), List(Digest)) {
  case t {
    term.Var(_) | term.Sort(_) -> #(found, visited)
    term.Const(d) -> follow(environment, d, found, visited)
    term.Pi(a, b) | term.Lam(a, b) -> {
      let #(found, visited) = walk(environment, a, found, visited)
      walk(environment, b, found, visited)
    }
    term.App(f, a) -> {
      let #(found, visited) = walk(environment, f, found, visited)
      walk(environment, a, found, visited)
    }
    term.Eq(typ, a, b) -> {
      let #(found, visited) = walk(environment, typ, found, visited)
      let #(found, visited) = walk(environment, a, found, visited)
      walk(environment, b, found, visited)
    }
    term.Refl(typ, a) -> {
      let #(found, visited) = walk(environment, typ, found, visited)
      walk(environment, a, found, visited)
    }
    term.Hole(_, goal) -> walk(environment, goal, found, visited)
    term.Trusted(_, proc, args, rty) -> {
      let #(found, visited) = follow(environment, proc, found, visited)
      let #(found, visited) = walk(environment, args, found, visited)
      walk(environment, rty, found, visited)
    }
  }
}

fn follow(
  environment: Environment,
  d: Digest,
  found: List(Digest),
  visited: List(Digest),
) -> #(List(Digest), List(Digest)) {
  case list.contains(visited, d) {
    True -> #(found, visited)
    False -> {
      let visited = [d, ..visited]
      case environment.definitions(d) {
        // Has a body: not an axiom. Keep walking into it, because its own
        // references are the artifact's assumptions too.
        Some(body) -> walk(environment, body, found, visited)
        None ->
          case environment.signatures(d) {
            // Declared type, no body. An axiom. Its declared type may itself
            // refer to further axioms, so walk that as well.
            Some(typ) -> walk(environment, typ, [d, ..found], visited)
            // Neither. Unresolvable, and still an assumption -- see the
            // `from_environment` doc comment.
            None -> #([d, ..found], visited)
          }
      }
    }
  }
}

// ── The floor ─────────────────────────────────────────────────────────────────

/// What a verifier is willing to accept, chosen locally. See the module
/// comment: nothing derives one of these from anything a peer says.
pub type BasisFloor {
  BasisFloor(
    required_kernel: String,
    max_axioms: Int,
    forbidden_axioms: List(Digest),
    forbidden_hosts: List(PublicKey),
  )
}

/// The strictest floor: this exact kernel, no axioms at all, and so nothing
/// to forbid. A basis passing this has assumed nothing.
pub fn purist_floor(kernel_id: String) -> BasisFloor {
  BasisFloor(
    required_kernel: kernel_id,
    max_axioms: 0,
    forbidden_axioms: [],
    forbidden_hosts: [],
  )
}

/// Whether a basis clears a floor.
///
/// Every clause is a refusal: the kernel must match exactly, the axiom count
/// must not exceed the cap, and no forbidden axiom or host may appear. There
/// is no clause that can make an otherwise-failing basis pass, so adding a
/// field to `Basis` can never loosen an existing floor.
pub fn satisfies(b: Basis, floor: BasisFloor) -> Bool {
  let c = canonicalize(b)
  c.kernel_id == floor.required_kernel
  && list.length(c.axioms) <= floor.max_axioms
  && !list.any(c.axioms, fn(a) { list.contains(floor.forbidden_axioms, a) })
  && !list.any(c.hosts, fn(h) { list.contains(floor.forbidden_hosts, h) })
}

/// Why a basis failed a floor. For diagnostics only -- `satisfies` is the
/// decision, and this must never be consulted to soften it.
pub type FloorFailure {
  WrongKernel(required: String, found: String)
  TooManyAxioms(limit: Int, found: Int)
  ForbiddenAxiom(Digest)
  ForbiddenHost(PublicKey)
}

/// Every reason a basis fails a floor, in a fixed order. Empty exactly when
/// `satisfies` is True.
pub fn failures(b: Basis, floor: BasisFloor) -> List(FloorFailure) {
  let c = canonicalize(b)
  let kernel_failure = case c.kernel_id == floor.required_kernel {
    True -> []
    False -> [
      WrongKernel(required: floor.required_kernel, found: c.kernel_id),
    ]
  }
  let count = list.length(c.axioms)
  let count_failure = case count <= floor.max_axioms {
    True -> []
    False -> [TooManyAxioms(limit: floor.max_axioms, found: count)]
  }
  let axiom_failures =
    c.axioms
    |> list.filter(fn(a) { list.contains(floor.forbidden_axioms, a) })
    |> list.map(ForbiddenAxiom)
  let host_failures =
    c.hosts
    |> list.filter(fn(h) { list.contains(floor.forbidden_hosts, h) })
    |> list.map(ForbiddenHost)
  list.flatten([kernel_failure, count_failure, axiom_failures, host_failures])
}
