/// Declared effect set, enforced.
///
/// Outside the kernel and outside the TCB.
///
/// WHAT THIS PROVES
/// ----------------
/// That an artifact cannot reach any host procedure it did not declare. A
/// `Trusted(host, proc, ...)` node names a host and a procedure, which makes it
/// a capability marker in all but name; `of_term` collects them, transitively
/// through `Const` references, and `admit` refuses anything the declaration
/// does not cover.
///
/// WHAT THIS DOES NOT PROVE
/// ------------------------
/// Be plain about this, because the property is shallow on purpose and its
/// value comes from being cheap and universal rather than deep:
///
///   - It bounds WHICH host procedures are reachable. It says nothing about
///     what the artifact computes, whether it calls them, how often, in what
///     order, or with what arguments. It is a reachability bound, not a
///     specification, and no correctness claim follows from it.
///   - It is only as strong as the runtime's guarantee that `Trusted` is the
///     sole effect channel. If effects can enter by any other route, this
///     bounds nothing at all. THAT GUARANTEE IS NOT CURRENTLY ENFORCED
///     ANYWHERE IN THIS REPOSITORY -- there is no plugin runtime, no host
///     execution, and nothing that checks a running artifact against its
///     declaration. Today this is a static property of terms. See the open
///     risks in docs/PR-NOTES.md.
///   - A declaration that covers everything proves nothing. The property is
///     "no more than declared", so it is exactly as informative as the
///     declaration is narrow.
///
/// UNRESOLVABLE IS NOT EMPTY
/// -------------------------
/// If a `Const` cannot be resolved, the capability set is UNKNOWN, and unknown
/// is refused. Treating an unresolvable reference as contributing nothing
/// would make hiding a capability trivial: point at a name the verifier
/// cannot fetch and the declaration comes out clean.
import cronch/canonical
import cronch/digest.{type Digest, type HashAlgorithm}
import cronch/kernel.{type Environment}
import cronch/pubkey.{type PublicKey}
import cronch/serialize
import cronch/term.{type Term}
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleam/order.{type Order}

/// One host procedure an artifact can reach.
///
/// `proc` is a `String` here rather than the `Digest` a `Trusted` node
/// carries, because a capability is something a person declares on a command
/// line and reads in a report. The rendering is the content address (see
/// `of_digest`), so nothing is lost: the identity is still the hash.
pub type Capability {
  Capability(host: PublicKey, proc: String)
}

/// A sorted, deduplicated set of capabilities -- or UNKNOWN.
///
/// Opaque so that the sorted-and-deduplicated invariant holds by construction,
/// and so that `Unknown` cannot be pattern-matched away into an empty set by a
/// caller in a hurry.
pub opaque type CapabilitySet {
  Known(List(Capability))
  /// At least one reference could not be resolved, so the true set is not
  /// merely unmeasured -- it is unbounded from here. Never empty, never a
  /// subset of anything, never admitted.
  Unknown
}

/// The empty capability set. A pure artifact's.
pub fn empty() -> CapabilitySet {
  Known([])
}

/// Build a set from a list. Sorted and deduplicated.
pub fn from_list(caps: List(Capability)) -> CapabilitySet {
  Known(
    caps
    |> list.unique
    |> list.sort(compare_capability),
  )
}

/// The unknown set. Nothing admits against it and it admits nothing.
pub fn unknown() -> CapabilitySet {
  Unknown
}

/// Whether a set is unknown. The only way to observe the distinction, and
/// deliberately not a way to get at a list of capabilities from one.
pub fn is_unknown(s: CapabilitySet) -> Bool {
  case s {
    Unknown -> True
    Known(_) -> False
  }
}

/// The capabilities in a set, or `Error(Nil)` if it is unknown. There is no
/// default and no empty fallback: an unknown set has no member list, and
/// inventing one is exactly the mistake this type exists to prevent.
pub fn to_list(s: CapabilitySet) -> Result(List(Capability), Nil) {
  case s {
    Known(caps) -> Ok(caps)
    Unknown -> Error(Nil)
  }
}

fn compare_capability(a: Capability, b: Capability) -> Order {
  case canonical.compare_pubkeys(a.host, b.host) {
    order.Eq ->
      canonical.compare_bytes(
        bit_array.from_string(a.proc),
        bit_array.from_string(b.proc),
      )
    other -> other
  }
}

/// Render a procedure digest as the string a `Capability` carries: the
/// self-describing content address, e.g. `"blake3:1f2e..."`.
pub fn proc_name(d: Digest) -> String {
  hash_address(d)
}

// The address rendering, kept local rather than importing hash.gleam, which
// would pull the whole content-addressing module in for one formatting call.
fn hash_address(d: Digest) -> String {
  let digest.Digest(algorithm, bytes) = d
  digest.algorithm_name(algorithm) <> ":" <> lower_hex(bytes)
}

fn lower_hex(b: BitArray) -> String {
  do_lower_hex(b, "")
}

fn do_lower_hex(b: BitArray, acc: String) -> String {
  case b {
    <<byte, rest:bits>> ->
      do_lower_hex(rest, acc <> nibble(byte / 16) <> nibble(byte % 16))
    _ -> acc
  }
}

fn nibble(n: Int) -> String {
  case n {
    0 -> "0"
    1 -> "1"
    2 -> "2"
    3 -> "3"
    4 -> "4"
    5 -> "5"
    6 -> "6"
    7 -> "7"
    8 -> "8"
    9 -> "9"
    10 -> "a"
    11 -> "b"
    12 -> "c"
    13 -> "d"
    14 -> "e"
    _ -> "f"
  }
}

// ── Collecting ────────────────────────────────────────────────────────────────

/// Every host procedure a term can reach, transitively through `Const`.
///
/// Transitive on purpose: a term that reaches a host procedure three `Const`
/// hops away has that capability whether or not it names it directly.
/// Declaring only what you mention would be trivially defeated by moving the
/// `Trusted` node into a definition.
///
/// Returns `Unknown` if any reachable `Const` resolves in neither store. See
/// the module comment.
///
/// Termination rests on a visited set, not on the store being acyclic.
pub fn of_term(t: Term, environment: Environment) -> CapabilitySet {
  let #(caps, resolved, _) = walk(environment, t, [], True, [])
  case resolved {
    False -> Unknown
    True -> from_list(caps)
  }
}

fn walk(
  environment: Environment,
  t: Term,
  caps: List(Capability),
  resolved: Bool,
  visited: List(Digest),
) -> #(List(Capability), Bool, List(Digest)) {
  case t {
    term.Var(_) | term.Sort(_) -> #(caps, resolved, visited)
    term.Const(d) -> follow(environment, d, caps, resolved, visited)
    term.Pi(a, b) | term.Lam(a, b) -> {
      let #(caps, resolved, visited) =
        walk(environment, a, caps, resolved, visited)
      walk(environment, b, caps, resolved, visited)
    }
    term.App(f, a) -> {
      let #(caps, resolved, visited) =
        walk(environment, f, caps, resolved, visited)
      walk(environment, a, caps, resolved, visited)
    }
    term.Eq(typ, a, b) -> {
      let #(caps, resolved, visited) =
        walk(environment, typ, caps, resolved, visited)
      let #(caps, resolved, visited) =
        walk(environment, a, caps, resolved, visited)
      walk(environment, b, caps, resolved, visited)
    }
    term.Refl(typ, a) -> {
      let #(caps, resolved, visited) =
        walk(environment, typ, caps, resolved, visited)
      walk(environment, a, caps, resolved, visited)
    }
    term.Hole(_, goal) -> walk(environment, goal, caps, resolved, visited)
    term.Trusted(host, proc, args, rty) -> {
      let caps = [Capability(host: host, proc: proc_name(proc)), ..caps]
      // The procedure object itself is followed: a host hidden inside it is
      // still reachable, and must surface.
      let #(caps, resolved, visited) =
        follow(environment, proc, caps, resolved, visited)
      let #(caps, resolved, visited) =
        walk(environment, args, caps, resolved, visited)
      walk(environment, rty, caps, resolved, visited)
    }
  }
}

fn follow(
  environment: Environment,
  d: Digest,
  caps: List(Capability),
  resolved: Bool,
  visited: List(Digest),
) -> #(List(Capability), Bool, List(Digest)) {
  case list.contains(visited, d) {
    True -> #(caps, resolved, visited)
    False -> {
      let visited = [d, ..visited]
      case environment.definitions(d) {
        Some(body) -> walk(environment, body, caps, resolved, visited)
        None ->
          case environment.signatures(d) {
            // An axiom has a declared type and no body. Its type can still
            // mention a Trusted node, so it is walked.
            Some(typ) -> walk(environment, typ, caps, resolved, visited)
            // Resolves nowhere. The reachable set is unbounded from here.
            None -> #(caps, False, visited)
          }
      }
    }
  }
}

// ── Set operations ────────────────────────────────────────────────────────────

/// Whether every capability in `a` is also in `b`.
///
/// `Unknown` on either side is False. An unknown set is not a subset of
/// anything -- it is unbounded -- and nothing is a subset of it, because it
/// makes no claim about what it contains.
pub fn subset(a: CapabilitySet, b: CapabilitySet) -> Bool {
  case a, b {
    Known(xs), Known(ys) -> list.all(xs, fn(x) { list.contains(ys, x) })
    _, _ -> False
  }
}

/// Union. Associative, commutative and idempotent.
///
/// Absorbing in `Unknown`: joining an unknown set with anything is unknown,
/// because the unknown part is still unbounded.
pub fn join(sets: List(CapabilitySet)) -> CapabilitySet {
  list.fold(sets, empty(), fn(acc, s) {
    case acc, s {
      Known(xs), Known(ys) -> from_list(list.append(xs, ys))
      _, _ -> Unknown
    }
  })
}

/// The capabilities in `a` that are not in `b`. `Error(Nil)` if either is
/// unknown -- there is no meaningful excess against an unbounded set.
pub fn difference(
  a: CapabilitySet,
  b: CapabilitySet,
) -> Result(List(Capability), Nil) {
  case a, b {
    Known(xs), Known(ys) -> Ok(list.filter(xs, fn(x) { !list.contains(ys, x) }))
    _, _ -> Error(Nil)
  }
}

// ── Digest ────────────────────────────────────────────────────────────────────

/// A capability set's content address, under kind tag 0x04.
///
/// `Unknown` has a digest distinct from every known set's, including the empty
/// one, so a receipt recording an unknown set cannot be mistaken for one
/// recording a pure artifact.
pub fn digest(algorithm: HashAlgorithm, s: CapabilitySet) -> Digest {
  canonical.digest_of(algorithm, canonical.KindCapabilitySet, payload(s))
}

/// Canonical bytes of a capability set: a presence byte, then a counted list
/// of (pubkey, length-prefixed procedure name) pairs in sorted order.
pub fn encode(s: CapabilitySet) -> BitArray {
  canonical.envelope(canonical.KindCapabilitySet, payload(s))
}

fn payload(s: CapabilitySet) -> BitArray {
  case s {
    // 0x00 marks unknown, and carries no list -- there is no list to carry.
    Unknown -> <<0x00>>
    Known(caps) ->
      bit_array.concat([
        <<0x01>>,
        serialize.varint(list.length(caps)),
        ..list.map(caps, fn(c) {
          bit_array.concat([
            serialize.pubkey_field(c.host),
            canonical.string_field(c.proc),
          ])
        })
      ])
  }
}

// ── Admission ─────────────────────────────────────────────────────────────────

/// The outcome of checking an artifact against its declared effect set.
pub type Admission {
  /// The artifact reaches nothing beyond what it declared.
  Admitted
  /// It reaches these, and did not declare them. Sorted; never empty.
  Excess(List(Capability))
  /// A reference could not be resolved, so what it reaches is unbounded.
  /// Refused, and NOT a synonym for `Excess([])`.
  Unresolvable
}

/// Check an artifact against a declared effect set.
///
/// Three outcomes, and `Unresolvable` is genuinely separate: `Excess([])`
/// would read as "nothing undeclared", which is the opposite of what an
/// unresolvable reference means.
pub fn admit(
  t: Term,
  environment: Environment,
  declared: CapabilitySet,
) -> Admission {
  let actual = of_term(t, environment)
  case difference(actual, declared) {
    Error(Nil) -> Unresolvable
    Ok([]) -> Admitted
    Ok(excess) -> Excess(list.sort(excess, compare_capability))
  }
}

/// Whether an admission permits the artifact. The only predicate over
/// `Admission`, and it is False for both refusal kinds.
pub fn is_admitted(a: Admission) -> Bool {
  case a {
    Admitted -> True
    Excess(_) | Unresolvable -> False
  }
}
