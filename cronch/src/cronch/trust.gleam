/// Trust sets, policy gating, and host-signature verification.
///
/// Three responsibilities, all kept outside the kernel:
///
///   1. Trust sets -- walk the term graph to collect every (host, proc) pair
///      an artifact depends on, directly or transitively through Const.
///      Pure function of the graph; a verifier recomputes it, so a registry
///      cannot lie about it.
///
///   2. Policy -- a set of accepted host public keys. An artifact is authorized
///      under a policy when every (host, proc) pair in its trust set is covered
///      by the policy. The empty (purist) policy only accepts host-free artifacts.
///
///   3. Host signature verification -- asymmetric signature over
///      proc_bytes || hash(canonical(args)) || hash(canonical(result)).
///      The kernel never sees a signature; all signature logic lives here.
///
/// Policy MUST be checked before the kernel runs. An artifact may be well-typed
/// yet still denied by policy; `unauthorized` must return empty before calling
/// `infer` or `check`.

import cronch/digest.{type Digest}
import cronch/hash
import cronch/pubkey.{type PublicKey}
import cronch/term.{type Term}
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleam/order
import gleam/string

/// A trust dependency: one (host authority, pinned procedure hash) pair.
pub type TrustPair =
  #(PublicKey, Digest)

/// The store type: a pure map from content address to term.
pub type Store =
  fn(Digest) -> option.Option(Term)

// ── Trust sets ────────────────────────────────────────────────────────────────

/// Recompute the trust set of a term: every (host, proc) in its own Trusted
/// nodes, unioned with the trust set of every object reachable through Const.
/// The result is sorted and deduplicated. Terminates because the object graph
/// is a DAG; the visited set is a belt-and-suspenders guard.
pub fn trust_set(store: Store, t: Term) -> List(TrustPair) {
  let #(pairs, _) = walk(store, t, [], [])
  pairs
  |> list.unique
  |> list.sort(compare_pair)
}

fn walk(
  store: Store,
  t: Term,
  pairs: List(TrustPair),
  visited: List(Digest),
) -> #(List(TrustPair), List(Digest)) {
  case t {
    term.Trusted(host, proc, args, result_ty) -> {
      let pairs = [#(host, proc), ..pairs]
      // Follow proc transitively: a host hidden inside the procedure object
      // must surface in the trust set (no under-reporting).
      let #(pairs, visited) = follow(store, proc, pairs, visited)
      let #(pairs, visited) = walk(store, args, pairs, visited)
      walk(store, result_ty, pairs, visited)
    }
    term.Const(d) -> follow(store, d, pairs, visited)
    term.Var(_) | term.Sort(_) -> #(pairs, visited)
    term.Pi(a, b) | term.Lam(a, b) -> {
      let #(pairs, visited) = walk(store, a, pairs, visited)
      walk(store, b, pairs, visited)
    }
    term.App(f, a) -> {
      let #(pairs, visited) = walk(store, f, pairs, visited)
      walk(store, a, pairs, visited)
    }
    term.Eq(ty, a, b) -> {
      let #(pairs, visited) = walk(store, ty, pairs, visited)
      let #(pairs, visited) = walk(store, a, pairs, visited)
      walk(store, b, pairs, visited)
    }
    term.Refl(ty, a) -> {
      let #(pairs, visited) = walk(store, ty, pairs, visited)
      walk(store, a, pairs, visited)
    }
    term.Hole(_, goal) -> walk(store, goal, pairs, visited)
  }
}

fn follow(
  store: Store,
  d: Digest,
  pairs: List(TrustPair),
  visited: List(Digest),
) -> #(List(TrustPair), List(Digest)) {
  case list.contains(visited, d) {
    True -> #(pairs, visited)
    False ->
      case store(d) {
        None -> #(pairs, [d, ..visited])
        Some(def) -> walk(store, def, pairs, [d, ..visited])
      }
  }
}

// Lexicographic comparison of two TrustPairs, by host bytes then proc bytes.
// All public keys and digests are fixed-size, so hex-encoding gives a correct
// and stable lexicographic order.
fn compare_pair(a: TrustPair, b: TrustPair) -> order.Order {
  let #(pubkey.PublicKey(_, ah), digest.Digest(_, ap)) = a
  let #(pubkey.PublicKey(_, bh), digest.Digest(_, bp)) = b
  case string.compare(bit_array.base16_encode(ah), bit_array.base16_encode(bh)) {
    order.Eq ->
      string.compare(bit_array.base16_encode(ap), bit_array.base16_encode(bp))
    other -> other
  }
}

// ── Policy ────────────────────────────────────────────────────────────────────

/// A client trust policy: the set of accepted host public keys.
/// The empty policy is purist mode -- only host-free artifacts pass.
pub opaque type Policy {
  Policy(hosts: List(PublicKey))
}

/// The empty (purist) policy. Only artifacts with an empty trust set pass.
pub fn empty_policy() -> Policy {
  Policy([])
}

/// A policy that accepts the given host keys.
pub fn policy_with_hosts(hosts: List(PublicKey)) -> Policy {
  Policy(hosts)
}

/// The (host, proc) pairs in the trust set NOT covered by the policy.
/// An empty result means the artifact is authorized under the policy.
pub fn unauthorized(set: List(TrustPair), policy: Policy) -> List(TrustPair) {
  list.filter(set, fn(pair) { !list.contains(policy.hosts, pair.0) })
}

/// Whether the trust set is fully authorized under the policy.
pub fn is_authorized(set: List(TrustPair), policy: Policy) -> Bool {
  list.is_empty(unauthorized(set, policy))
}

// ── Host signature verification ───────────────────────────────────────────────

/// A host-signed result traveling on the wire.
pub type HostResult {
  HostResult(
    host: PublicKey,
    proc: Digest,
    args: Term,
    result: Term,
    signature: BitArray,
  )
}

/// The message a host signs:
///   raw_proc_bytes || hash(canonical(args)) || hash(canonical(result))
///
/// Binding all three ties the signature to a specific pinned procedure on
/// specific inputs producing a specific output. The hash algorithm is the
/// same one carried in the proc Digest.
pub fn host_message(proc: Digest, args: Term, result: Term) -> BitArray {
  let digest.Digest(algo, proc_bytes) = proc
  let digest.Digest(_, args_hash) = hash.hash(algo, args)
  let digest.Digest(_, result_hash) = hash.hash(algo, result)
  bit_array.concat([proc_bytes, args_hash, result_hash])
}

/// Verify a host result's signature. Fails closed: a malformed key,
/// malformed signature, or any verification failure returns False.
/// The kernel never calls this; it does not know what a signature is.
pub fn verify_host_result(r: HostResult) -> Bool {
  let pubkey.PublicKey(scheme, key_bytes) = r.host
  let msg = host_message(r.proc, r.args, r.result)
  case scheme {
    pubkey.Ed25519 -> ffi_verify_ed25519(msg, r.signature, key_bytes)
  }
}

@external(erlang, "cronch_crypto", "verify_ed25519")
fn ffi_verify_ed25519(msg: BitArray, sig: BitArray, pubkey: BitArray) -> Bool
