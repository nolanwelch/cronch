/// Trust sets, policy gating, and signature verification.
///
/// Four responsibilities, all kept outside the kernel:
///
///   1. Trust sets -- collect every trust dependency an artifact carries: a
///      (host, proc) pair from a Trusted node, found by walking the term
///      graph directly and transitively through Const, plus a (rule-set
///      author, rule-set hash) pair for every rewrite rule the kernel
///      actually invoked. Pure and reproducible; a verifier recomputes it, so
///      a registry cannot lie about it.
///
///      Rule uses come from the typing derivation itself
///      (`trust_set_of_check` / `trust_set_of_infer`), not from a separate
///      reconstruction. The older reduction-scoped `trust_set_with_rules`
///      under-reports and is kept only for callers that want the uses of a
///      reduction rather than of a check.
///
///   2. Policy -- a set of accepted host public keys and a set of accepted
///      (rule-set author, rule-set hash) pairs. An artifact is authorized
///      under a policy when every entry in its trust set is covered by the
///      policy. The empty (purist) policy accepts only artifacts with zero
///      trust dependencies of any kind -- oracle or rule-set alike. There is
///      no "default trusted" rule set: even the reference rule set in
///      test/support/reference_rules.gleam must be explicitly listed in a
///      policy like anything else.
///
///   3. Host signature verification -- asymmetric signature over
///      proc_bytes || hash(canonical(args)) || hash(canonical(result)).
///
///   4. Rule-set signature verification -- asymmetric signature over a rule
///      set's own content hash, using the same crypto FFI as (3).
///
///   The kernel never sees a signature; all signature logic lives here.
///
/// Policy MUST be checked before the kernel runs. An artifact may be well-typed
/// yet still denied by policy; `unauthorized` must return empty before calling
/// `infer` or `check`.
import cronch/digest.{type Digest}
import cronch/hash
import cronch/kernel
import cronch/pubkey.{type PublicKey}
import cronch/rewrite
import cronch/term.{type Term}
import gleam/bit_array
import gleam/int
import gleam/list
import gleam/option.{None, Some}
import gleam/order
import gleam/result
import gleam/string

/// A trust dependency an artifact carries: authority over a host
/// procedure's result, or authority to run a signed rule set during
/// reduction. Both are "a (public key, content digest) pair this artifact's
/// correctness rests on that the kernel itself cannot verify" --
/// unauthorized/is_authorized treat the two uniformly so no call site needs
/// to special-case which kind of trust dependency it is looking at.
pub type TrustPair {
  HostTrust(host: PublicKey, proc: Digest)
  RuleSetTrust(author: PublicKey, hash: Digest)
}

/// The store type: a pure map from content address to term.
pub type Store =
  fn(Digest) -> option.Option(Term)

// ── Trust sets ────────────────────────────────────────────────────────────────

/// Recompute the trust set of a term: every (host, proc) in its own Trusted
/// nodes, unioned with the trust set of every object reachable through Const.
/// The result is sorted and deduplicated. Terminates because the object graph
/// is a DAG; the visited set is a belt-and-suspenders guard.
///
/// This does not account for rule-set trust dependencies -- see
/// `trust_set_with_rules` below for why that needs the kernel's own
/// reduction rather than a static walk, and for the design decision behind
/// splitting it into a second function instead of changing this one's
/// signature (every existing caller of `trust_set` keeps working unchanged).
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
    term.Trusted(host, proc, args, result_typ) -> {
      let pairs = [HostTrust(host, proc), ..pairs]
      // Follow proc transitively: a host hidden inside the procedure object
      // must surface in the trust set (no under-reporting).
      let #(pairs, visited) = follow(store, proc, pairs, visited)
      let #(pairs, visited) = walk(store, args, pairs, visited)
      walk(store, result_typ, pairs, visited)
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
    term.Eq(typ, a, b) -> {
      let #(pairs, visited) = walk(store, typ, pairs, visited)
      let #(pairs, visited) = walk(store, a, pairs, visited)
      walk(store, b, pairs, visited)
    }
    term.Refl(typ, a) -> {
      let #(pairs, visited) = walk(store, typ, pairs, visited)
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

// Lexicographic comparison of two TrustPairs: HostTrust before RuleSetTrust,
// then by first-key bytes, then by second-key bytes. All public keys and
// digests are fixed-size, so hex-encoding gives a correct and stable
// lexicographic order.
fn compare_pair(a: TrustPair, b: TrustPair) -> order.Order {
  let #(ta, ah, ap) = pair_key(a)
  let #(tb, bh, bp) = pair_key(b)
  case int.compare(ta, tb) {
    order.Eq ->
      case
        string.compare(bit_array.base16_encode(ah), bit_array.base16_encode(bh))
      {
        order.Eq ->
          string.compare(
            bit_array.base16_encode(ap),
            bit_array.base16_encode(bp),
          )
        other -> other
      }
    other -> other
  }
}

fn pair_key(p: TrustPair) -> #(Int, BitArray, BitArray) {
  case p {
    HostTrust(pubkey.PublicKey(_, h), digest.Digest(_, pr)) -> #(0, h, pr)
    RuleSetTrust(pubkey.PublicKey(_, h), digest.Digest(_, rs)) -> #(1, h, rs)
  }
}

// ── Rule-set trust ────────────────────────────────────────────────────────────
//
// Design decision (flagged as needing one when this module was extended for
// rewrite-rule support): which rules a term *could* eventually invoke is not
// a well-defined static question -- whether some lhs pattern could ever
// match some reduct of a subterm is exactly as hard as reduction itself.
// Guessing conservatively would either under-report (unsound: a rule set
// genuinely exercised escapes the trust set and slips past policy) or
// wildly over-report (every rule set ever declared, whether or not this
// particular term goes near it).
//
// So trust_set_with_rules does not walk statically at all. It re-runs the
// kernel's own reduction -- kernel.normalize_with_uses -- and reads off
// exactly which RuleUses fired. This is guaranteed to match what a real
// check/infer against this Environment would exercise, because it IS that same
// reduction: kernel.gleam's tracked and untracked entry points share one
// implementation (whnf_go/normalize_go), so there is no second, simpler
// path that could silently drift from what the kernel actually does. A
// verifier can always recompute this independently, exactly like the
// existing `trust_set` walk.
//
// Scope limitation, and why it is not enough. This accounts only for rule
// sets exercised while NORMALIZING the artifact term (and transitively
// through Const, matching `follow`'s reach). Rewriting also happens while
// checking TYPE annotations -- in `infer_sort` on every binder domain, in the
// whnf of a function's type in the App case, and in every def_eq conversion
// check. A rule set exercised only there never reaches this set, so
// `is_authorized` can return True for an artifact whose acceptance genuinely
// depended on an unauthorized rule set. That is a policy bypass, and
// `trust_set_of_check` / `trust_set_of_infer` below are the fix.
//
// The fix is NOT a second normalization pass over the type annotations. That
// would be the same reconstruction with a wider net: it would still miss
// conversions performed at points nobody anticipated, and it would duplicate
// the reduction path. Instead the kernel reports rule uses as a byproduct of
// the derivation itself, at the point each reduction happens, and the
// functions below just read that off.

/// The trust set of a REDUCTION: the ordinary Trusted/Const walk, plus every
/// rule set invoked while normalizing `t`.
///
/// Retained for callers that genuinely want "what did reducing this term
/// use" -- and for terms that are not well-typed at all, which the derivation
/// functions below cannot report on because there is no derivation.
///
/// NOT the right input to an authorization decision. It under-reports: see the
/// scope note above. Use `trust_set_of_check` or `trust_set_of_infer`.
pub fn trust_set_with_rules(
  environment: kernel.Environment,
  fuel: kernel.Fuel,
  provenance: fn(Digest) -> List(#(kernel.RuleUse, rewrite.Rule)),
  t: Term,
) -> Result(List(TrustPair), kernel.TypeError) {
  let host_pairs = trust_set(environment.definitions, t)
  use #(_, uses) <- result.try(kernel.normalize_with_uses(
    environment,
    provenance,
    fuel,
    t,
  ))
  let rule_pairs = list.map(uses, fn(u) { RuleSetTrust(u.author, u.rule_set) })
  Ok(
    list.append(host_pairs, rule_pairs)
    |> list.unique
    |> list.sort(compare_pair),
  )
}

// ── Derivation-integral trust sets ────────────────────────────────────────────
//
// These are what an authorization decision consults. Each runs the kernel's
// own typing derivation with reporting turned on and reads the rule uses off
// the Report. Nothing is reconstructed, nothing is re-normalized, and there is
// no second reduction path: kernel.infer/check are wrappers over the very
// functions these call, with the Report discarded.
//
// A term that does not typecheck has no derivation and therefore no
// derivation trust set -- the TypeError propagates. Fail closed: there is no
// path here where a failed check yields an empty (and so trivially
// authorized) set.

/// Every trust dependency an artifact's ACCEPTANCE rests on, when checked
/// against a declared type: the Trusted/Const walk, plus every rule set the
/// typing derivation invoked anywhere -- including while checking type
/// annotations, where the reduction-scoped set above is blind.
pub fn trust_set_of_check(
  environment: kernel.Environment,
  provenance: kernel.Provenance,
  fuel: kernel.Fuel,
  cx: kernel.Context,
  t: Term,
  typ: Term,
) -> Result(List(TrustPair), kernel.TypeError) {
  use report <- result.try(kernel.check_reporting(
    environment,
    provenance,
    fuel,
    cx,
    t,
    typ,
  ))
  Ok(merge_pairs(environment, t, report))
}

/// As `trust_set_of_check`, for a derivation that infers the type rather than
/// checking against a declared one.
pub fn trust_set_of_infer(
  environment: kernel.Environment,
  provenance: kernel.Provenance,
  fuel: kernel.Fuel,
  cx: kernel.Context,
  t: Term,
) -> Result(#(Term, List(TrustPair)), kernel.TypeError) {
  use #(typ, report) <- result.try(kernel.infer_reporting(
    environment,
    provenance,
    fuel,
    cx,
    t,
  ))
  Ok(#(typ, merge_pairs(environment, t, report)))
}

/// The trust pairs a Report contributes, on their own. Exposed so a caller
/// that already holds a Report (receipt.gleam does) does not have to re-run
/// the derivation to get them.
pub fn pairs_of_report(report: kernel.Report) -> List(TrustPair) {
  list.map(report.rule_uses, fn(u) { RuleSetTrust(u.author, u.rule_set) })
}

/// Combine the static Trusted/Const walk with a Report's rule uses, sorted and
/// deduplicated. The walk is still needed: a Trusted node is a trust
/// dependency whether or not any reduction touches it.
pub fn merge_pairs(
  environment: kernel.Environment,
  t: Term,
  report: kernel.Report,
) -> List(TrustPair) {
  list.append(trust_set(environment.definitions, t), pairs_of_report(report))
  |> list.unique
  |> list.sort(compare_pair)
}

// ── Policy ────────────────────────────────────────────────────────────────────

/// A client trust policy: the set of accepted host public keys, and the set
/// of accepted (rule-set author, rule-set hash) pairs. The empty policy is
/// purist mode -- only artifacts with an empty trust set of either kind pass.
pub opaque type Policy {
  Policy(hosts: List(PublicKey), rule_sets: List(#(PublicKey, Digest)))
}

/// The empty (purist) policy. Only artifacts with an empty trust set pass.
pub fn empty_policy() -> Policy {
  Policy([], [])
}

/// A policy that accepts the given host keys (any rule-set dependency is
/// still denied).
pub fn policy_with_hosts(hosts: List(PublicKey)) -> Policy {
  Policy(hosts, [])
}

/// A policy that accepts the given (rule-set author, rule-set hash) pairs
/// (any host dependency is still denied). Each entry authorizes exactly one
/// signed rule set, not "anything from this author" -- mirroring how a host
/// policy pins a specific host key rather than a name.
pub fn policy_with_rule_sets(rule_sets: List(#(PublicKey, Digest))) -> Policy {
  Policy([], rule_sets)
}

/// A policy that accepts both a set of host keys and a set of specific
/// signed rule sets.
pub fn policy_with(
  hosts: List(PublicKey),
  rule_sets: List(#(PublicKey, Digest)),
) -> Policy {
  Policy(hosts, rule_sets)
}

/// The trust-set entries NOT covered by the policy, regardless of kind.
/// An empty result means the artifact is authorized under the policy.
pub fn unauthorized(set: List(TrustPair), policy: Policy) -> List(TrustPair) {
  list.filter(set, fn(pair) {
    case pair {
      HostTrust(host, _) -> !list.contains(policy.hosts, host)
      RuleSetTrust(author, hash) ->
        !list.contains(policy.rule_sets, #(author, hash))
    }
  })
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
  let digest.Digest(algorithm, proc_bytes) = proc
  let digest.Digest(_, args_hash) = hash.hash(algorithm, args)
  let digest.Digest(_, result_hash) = hash.hash(algorithm, result)
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

// ── Rule-set signature verification ───────────────────────────────────────────

/// A rule-set author's signature over a specific rule set's content hash --
/// the rule-set analogue of HostResult's signature over a computed result.
pub type RuleSetSignature {
  RuleSetSignature(author: PublicKey, hash: Digest, signature: BitArray)
}

/// The message a rule-set author signs: the raw digest bytes of the rule
/// set's own content address. Binding the signature to the content hash
/// (not a mutable name) means accepting "rule set X by author A" pins the
/// exact rules in X, the same way host_message pins a result to a specific
/// procedure/args/result rather than a name.
pub fn rule_set_message(hash: Digest) -> BitArray {
  let digest.Digest(_, bytes) = hash
  bytes
}

/// Verify a rule-set author's signature. Fails closed, same as
/// verify_host_result, and reuses the same crypto FFI.
pub fn verify_rule_set_signature(s: RuleSetSignature) -> Bool {
  let pubkey.PublicKey(scheme, key_bytes) = s.author
  let msg = rule_set_message(s.hash)
  case scheme {
    pubkey.Ed25519 -> ffi_verify_ed25519(msg, s.signature, key_bytes)
  }
}

@external(erlang, "cronch_crypto", "verify_ed25519")
fn ffi_verify_ed25519(msg: BitArray, sig: BitArray, pubkey: BitArray) -> Bool
