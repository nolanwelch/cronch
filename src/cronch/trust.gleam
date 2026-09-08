/// Trust sets, policy gating, and signature verification.
///
/// Four responsibilities, all kept outside the kernel:
///
///   1. Trust sets -- collect every trust dependency an artifact carries: a
///      (host, proc) pair from a Trusted node, found by walking the term
///      graph directly and transitively through Const -- through a constant's
///      definition where it has one and through its declared type where it
///      does not, so an axiom cannot hide a Trusted node -- plus a (rule-set
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
///   3. Host result verification -- an asymmetric signature over
///      proc_bytes || hash(canonical(args)) || hash(canonical(result)), AND a
///      check that the result inhabits the type the pinned procedure promises
///      for those arguments. A signature says who computed a result, not that
///      the result is the kind of thing that was asked for; accepting on the
///      signature alone lets a faithful host inject an ill-typed term.
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

// ── Trust sets ────────────────────────────────────────────────────────────────

/// Recompute the trust set of a term: every (host, proc) in its own Trusted
/// nodes, unioned with the trust set of every object reachable through Const --
/// through a constant's DEFINITION when it has one, and through its DECLARED
/// TYPE when it does not. The result is sorted and deduplicated.
///
/// The declared-type case is why this takes an `Environment` and not a bare
/// definitional store. An axiomatic constant lives in `environment.signatures`
/// with no body; a store-only walk resolved it to `None`, stopped, and
/// reported nothing -- so a `Trusted` node hiding inside an axiom's declared
/// type escaped the trust set entirely and the purist policy authorized a
/// host-dependent artifact. An axiom's declared type is load-bearing (it is
/// the only thing the kernel knows about that constant), so every trust
/// dependency in it is one the artifact rests on.
///
/// The reach is deliberately the same as `basis.axioms_of`'s: a constant's
/// body if it has one, its declared type if it does not, nothing when it
/// resolves in neither store. Two walks over the same graph disagreeing about
/// what is reachable would be a bug in one of them. See `follow` for the one
/// deliberate difference, which only arises on an environment that violates
/// `kernel.Environment`'s disjointness precondition.
///
/// Terminates on any graph, cyclic or not: a store is supplied by whoever is
/// being checked, so the visited set is load-bearing rather than a
/// belt-and-suspenders guard.
///
/// This does not account for rule-set trust dependencies -- see
/// `trust_set_with_rules` below for why that needs the kernel's own
/// reduction rather than a static walk.
pub fn trust_set(environment: kernel.Environment, t: Term) -> List(TrustPair) {
  let #(pairs, _) = walk(environment, t, [], [])
  pairs
  |> list.unique
  |> list.sort(compare_pair)
}

fn walk(
  environment: kernel.Environment,
  t: Term,
  pairs: List(TrustPair),
  visited: List(Digest),
) -> #(List(TrustPair), List(Digest)) {
  case t {
    term.Trusted(host, proc, args, result_typ) -> {
      let pairs = [HostTrust(host, proc), ..pairs]
      // Follow proc transitively: a host hidden inside the procedure object
      // must surface in the trust set (no under-reporting).
      let #(pairs, visited) = follow(environment, proc, pairs, visited)
      let #(pairs, visited) = walk(environment, args, pairs, visited)
      walk(environment, result_typ, pairs, visited)
    }
    term.Const(d) -> follow(environment, d, pairs, visited)
    term.Var(_) | term.Sort(_) -> #(pairs, visited)
    term.Pi(a, b) | term.Lam(a, b) -> {
      let #(pairs, visited) = walk(environment, a, pairs, visited)
      walk(environment, b, pairs, visited)
    }
    term.App(f, a) -> {
      let #(pairs, visited) = walk(environment, f, pairs, visited)
      walk(environment, a, pairs, visited)
    }
    term.Eq(typ, a, b) -> {
      let #(pairs, visited) = walk(environment, typ, pairs, visited)
      let #(pairs, visited) = walk(environment, a, pairs, visited)
      walk(environment, b, pairs, visited)
    }
    term.Refl(typ, a) -> {
      let #(pairs, visited) = walk(environment, typ, pairs, visited)
      walk(environment, a, pairs, visited)
    }
    term.Hole(_, goal) -> walk(environment, goal, pairs, visited)
  }
}

// Resolve a content address and keep walking. Same reach as basis.gleam's
// `follow`, minus the axiom bookkeeping: a definition is walked as a body, an
// axiom is walked through its declared type, and an address that resolves in
// neither store contributes nothing (a check against such an environment
// fails with `Unresolved` before any authorization decision matters).
//
// The one case where the two stores can both answer is a violation of
// `kernel.Environment`'s documented disjointness precondition, which nothing
// checks and which the party being checked supplies. There, both are walked.
// The kernel resolves `signatures` first (kernel.gleam's Const cases in
// `infer_go` and `whnf_go`) while basis.gleam resolves `definitions` first, so
// picking either order alone would leave a digest whose other meaning is
// load-bearing somewhere and reported nowhere -- the same under-reporting this
// function exists to close. Walking both can only over-report, and only on an
// environment that is already malformed.
fn follow(
  environment: kernel.Environment,
  d: Digest,
  pairs: List(TrustPair),
  visited: List(Digest),
) -> #(List(TrustPair), List(Digest)) {
  case list.contains(visited, d) {
    True -> #(pairs, visited)
    False -> {
      let visited = [d, ..visited]
      case environment.signatures(d), environment.definitions(d) {
        // An axiom: a declared type and no body. That type is the only thing
        // the kernel knows about the constant, so every trust dependency in
        // it is one the artifact's acceptance rests on.
        Some(typ), None -> walk(environment, typ, pairs, visited)
        // A definition: its own references are the artifact's dependencies too.
        None, Some(def) -> walk(environment, def, pairs, visited)
        Some(typ), Some(def) -> {
          let #(pairs, visited) = walk(environment, typ, pairs, visited)
          walk(environment, def, pairs, visited)
        }
        None, None -> #(pairs, visited)
      }
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
  let host_pairs = trust_set(environment, t)
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
  list.append(trust_set(environment, t), pairs_of_report(report))
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

// ── Host result verification ──────────────────────────────────────────────────
//
// A host result has to clear two independent bars, and the older
// `verify_host_result` only ever checked the first:
//
//   1. AUTHENTICITY. The signature is by the host key named, over exactly this
//      (proc, args, result). Says who computed it. Says nothing about what
//      they computed.
//
//   2. WELL-TYPEDNESS. The result inhabits the type the pinned procedure
//      promises for these arguments. A host that signs `Sort(0)` where the
//      procedure's codomain says `Nat` is authentically wrong, and a check
//      that stops after (1) accepts it.
//
// Nothing here is in the kernel and nothing here teaches the kernel about
// signatures: `verify_host_result` calls the kernel's ordinary public `check`,
// exactly as any other client of it would.
//
// The declared type is DERIVED FROM THE PINNED PROCEDURE, not read off the
// wire. `HostResult` carries no `result_typ` field, and adding one would be a
// wire-format change AND would let the signer nominate the standard it is
// judged against -- it could ship a result with a type it happens to inhabit.
// Instead the expected type is computed the same way kernel.gleam's
// `infer_trusted` computes it: whnf the procedure's signature object to a
// `Pi(domain, codomain)`, require `args : domain`, and take
// `beta(args, codomain)`. So this agrees with the Trusted typing rule by
// construction, and a `Trusted` node's own `result_typ` is def_eq to what is
// computed here whenever that node type-checks at all.

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

/// Verify a host result's SIGNATURE ONLY. Fails closed: a malformed key,
/// malformed signature, or any verification failure returns False.
/// The kernel never calls this; it does not know what a signature is.
///
/// Authenticity is not acceptability -- a host can faithfully sign a result of
/// the wrong type. Call `verify_host_result` to decide whether to believe a
/// result; this is exposed for callers that need the two bars separately
/// (diagnostics that distinguish "not from this host" from "not of this
/// type").
pub fn verify_host_signature(r: HostResult) -> Bool {
  let pubkey.PublicKey(scheme, key_bytes) = r.host
  let msg = host_message(r.proc, r.args, r.result)
  case scheme {
    pubkey.Ed25519 -> ffi_verify_ed25519(msg, r.signature, key_bytes)
  }
}

/// The type a host result is REQUIRED to inhabit, derived from the pinned
/// procedure and the arguments rather than from anything the host asserts.
///
/// Mirrors kernel.gleam's `infer_trusted`: the procedure object must be a
/// type, must whnf to a `Pi`, the arguments must check against its domain,
/// and the answer is its codomain instantiated at those arguments. Every
/// failure is a `TypeError`, never a default type -- there is no path here
/// that returns a type the host was not held to.
pub fn host_result_type(
  environment: kernel.Environment,
  fuel: kernel.Fuel,
  proc: Digest,
  args: Term,
) -> Result(Term, kernel.TypeError) {
  case environment.definitions(proc) {
    // The procedure the signature pins is not in the environment, so there is
    // no promise to hold the result to. Fail closed rather than wave it
    // through: this is the same `Unresolved` the kernel raises for a Trusted
    // node on an unknown proc.
    None -> Error(kernel.Unresolved(proc))
    Some(sig) -> {
      use _ <- result.try(
        kernel.infer(environment, fuel, kernel.empty(), sig)
        |> result.replace_error(kernel.TrustedProcNotAType(sig)),
      )
      use head <- result.try(kernel.whnf(environment, fuel, sig))
      case head {
        term.Pi(domain, codomain) -> {
          use _ <- result.try(kernel.check(
            environment,
            fuel,
            kernel.empty(),
            args,
            domain,
          ))
          Ok(kernel.beta(args, codomain))
        }
        other -> Error(kernel.TrustedProcNotPi(other))
      }
    }
  }
}

/// Verify a host result: authentic AND well-typed. Fails closed on both bars
/// -- a bad signature, an unresolvable or non-functional procedure, arguments
/// outside the procedure's domain, a fuel exhaustion during the check, or a
/// result that does not inhabit the procedure's codomain all return False.
///
/// `fuel` is explicit because the type check is real reduction, with the same
/// termination guard as any other kernel call, and a budget for it must be
/// visible at the call site rather than hidden behind a default.
///
/// Signature verification still happens entirely here, outside the kernel;
/// the type check is an ordinary call to the kernel's public `check`.
pub fn verify_host_result(
  environment: kernel.Environment,
  fuel: kernel.Fuel,
  r: HostResult,
) -> Bool {
  verify_host_signature(r) && result_has_declared_type(environment, fuel, r)
}

fn result_has_declared_type(
  environment: kernel.Environment,
  fuel: kernel.Fuel,
  r: HostResult,
) -> Bool {
  case host_result_type(environment, fuel, r.proc, r.args) {
    Error(_) -> False
    Ok(typ) ->
      kernel.check(environment, fuel, kernel.empty(), r.result, typ)
      |> result.is_ok
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
