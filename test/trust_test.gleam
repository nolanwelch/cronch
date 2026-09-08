import cronch/digest
import cronch/hash
import cronch/kernel
import cronch/pubkey
import cronch/rewrite
import cronch/term
import cronch/trust
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

// ── helpers ───────────────────────────────────────────────────────────────────

fn make_store(entries: List(#(digest.Digest, term.Term))) -> kernel.Store {
  fn(d: digest.Digest) {
    case list.find(entries, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> None
    }
  }
}

/// An environment with nothing in it: no definitions, no signatures, no rules.
fn empty_env() -> kernel.Environment {
  kernel.environment_from_store(kernel.no_store())
}

/// An environment whose definitional store is `store` and which declares no
/// axioms.
fn defs_env(store: kernel.Store) -> kernel.Environment {
  kernel.environment_from_store(store)
}

/// An environment with no definitions at all, in which every entry of
/// `entries` is an axiom: a constant with a declared type and no body.
fn axioms_env(
  entries: List(#(digest.Digest, term.Term)),
) -> kernel.Environment {
  kernel.Environment(
    definitions: kernel.no_store(),
    signatures: make_store(entries),
    rules: kernel.empty_rules(),
  )
}

fn fake_host(b: Int) -> pubkey.PublicKey {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>
  pubkey.PublicKey(pubkey.Ed25519, bytes)
}

fn fake_proc(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

// ── trust_set: pure terms ─────────────────────────────────────────────────────

pub fn pure_term_empty_trust_set_test() {
  let t = term.Lam(term.Sort(0), term.Var(0))
  trust.trust_set(empty_env(), t)
  |> should.equal([])
}

pub fn sort_empty_trust_set_test() {
  trust.trust_set(empty_env(), term.Sort(0))
  |> should.equal([])
}

// ── trust_set: own Trusted nodes ──────────────────────────────────────────────

pub fn own_trusted_node_test() {
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let t = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  trust.trust_set(empty_env(), t)
  |> should.equal([trust.HostTrust(host, proc)])
}

pub fn two_distinct_hosts_test() {
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h2 = fake_host(0x03)
  let p2 = fake_proc(0x04)
  let t =
    term.App(
      term.Trusted(h1, p1, term.Sort(0), term.Sort(0)),
      term.Trusted(h2, p2, term.Sort(0), term.Sort(0)),
    )
  let set = trust.trust_set(empty_env(), t)
  set |> list.length |> should.equal(2)
  set |> list.contains(trust.HostTrust(h1, p1)) |> should.be_true
  set |> list.contains(trust.HostTrust(h2, p2)) |> should.be_true
}

pub fn duplicate_trusted_nodes_deduplicated_test() {
  // Same (host, proc) appearing twice -> trust set has exactly one entry.
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let node = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let t = term.App(node, node)
  trust.trust_set(empty_env(), t)
  |> should.equal([trust.HostTrust(host, proc)])
}

// ── trust_set: transitive through Const ──────────────────────────────────────

pub fn transitive_through_const_test() {
  // Object Y has a Trusted node. X references Y via Const.
  // X's trust set must include Y's (host, proc).
  let host = fake_host(0x09)
  let proc = fake_proc(0x08)
  let y = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let y_addr = hash.hash(digest.Blake3, y)
  let store = make_store([#(y_addr, y)])
  // X = Lam(Sort(0), Const(y_addr))
  let x = term.Lam(term.Sort(0), term.Const(y_addr))
  trust.trust_set(defs_env(store), x)
  |> should.equal([trust.HostTrust(host, proc)])
}

pub fn const_not_in_store_adds_nothing_test() {
  let d = fake_proc(0xff)
  let t = term.Const(d)
  trust.trust_set(empty_env(), t)
  |> should.equal([])
}

// ── trust_set: proc reference transitivity ────────────────────────────────────

pub fn proc_reference_followed_test() {
  // The proc-signature object itself contains a Trusted node.
  // A root Trusted node whose proc is that object must surface BOTH hosts.
  let inner_host = fake_host(0x0b)
  let inner_proc = fake_proc(0x0c)
  let inner = term.Trusted(inner_host, inner_proc, term.Sort(0), term.Sort(0))
  let inner_addr = hash.hash(digest.Blake3, inner)

  // proc_obj references inner by Const -- Pi(Sort(0), Const(inner_addr))
  let proc_obj = term.Pi(term.Sort(0), term.Const(inner_addr))
  let proc_addr = hash.hash(digest.Blake3, proc_obj)

  let store = make_store([#(inner_addr, inner), #(proc_addr, proc_obj)])

  let outer_host = fake_host(0x0a)
  let root = term.Trusted(outer_host, proc_addr, term.Sort(0), term.Sort(0))
  let set = trust.trust_set(defs_env(store), root)

  set |> list.length |> should.equal(2)
  set |> list.contains(trust.HostTrust(outer_host, proc_addr)) |> should.be_true
  set
  |> list.contains(trust.HostTrust(inner_host, inner_proc))
  |> should.be_true
}

pub fn cycle_guard_no_infinite_loop_test() {
  // Two objects that reference each other would cause infinite recursion without
  // the visited guard. We can't actually build a real cycle in a DAG, but we
  // can verify the visited set prevents re-visiting an already-seen address.
  // Here: store has one entry, the root references it twice (via two Const nodes).
  let host = fake_host(0x05)
  let proc = fake_proc(0x06)
  let y = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let y_addr = hash.hash(digest.Blake3, y)
  let store = make_store([#(y_addr, y)])
  // App(Const(y_addr), Const(y_addr)) -- visits y twice but adds pair once
  let t = term.App(term.Const(y_addr), term.Const(y_addr))
  trust.trust_set(defs_env(store), t)
  |> should.equal([trust.HostTrust(host, proc)])
}

// ── trust_set: sorted order ───────────────────────────────────────────────────

pub fn trust_set_is_sorted_test() {
  // Build two pairs with deterministic ordering.
  // fake_host/proc(0x01) < fake_host/proc(0x03) by hex lexicographic order.
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h3 = fake_host(0x03)
  let p4 = fake_proc(0x04)
  // Insert in reverse order to confirm sort happens.
  let t =
    term.App(
      term.Trusted(h3, p4, term.Sort(0), term.Sort(0)),
      term.Trusted(h1, p1, term.Sort(0), term.Sort(0)),
    )
  let set = trust.trust_set(empty_env(), t)
  set |> should.equal([trust.HostTrust(h1, p1), trust.HostTrust(h3, p4)])
}

// ── policy ────────────────────────────────────────────────────────────────────

pub fn empty_policy_denies_host_test() {
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let set = [trust.HostTrust(host, proc)]
  trust.is_authorized(set, trust.empty_policy())
  |> should.be_false
}

pub fn empty_policy_admits_empty_trust_set_test() {
  trust.is_authorized([], trust.empty_policy())
  |> should.be_true
}

pub fn policy_with_host_admits_it_test() {
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let set = [trust.HostTrust(host, proc)]
  let policy = trust.policy_with_hosts([host])
  trust.is_authorized(set, policy)
  |> should.be_true
}

pub fn policy_missing_one_host_denies_test() {
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h2 = fake_host(0x03)
  let p2 = fake_proc(0x04)
  let set = [trust.HostTrust(h1, p1), trust.HostTrust(h2, p2)]
  // Policy only admits h1; h2 is not covered.
  let policy = trust.policy_with_hosts([h1])
  trust.is_authorized(set, policy)
  |> should.be_false
  trust.unauthorized(set, policy)
  |> should.equal([trust.HostTrust(h2, p2)])
}

pub fn policy_covering_all_hosts_authorizes_test() {
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h2 = fake_host(0x03)
  let p2 = fake_proc(0x04)
  let set = [trust.HostTrust(h1, p1), trust.HostTrust(h2, p2)]
  let policy = trust.policy_with_hosts([h1, h2])
  trust.is_authorized(set, policy)
  |> should.be_true
  trust.unauthorized(set, policy)
  |> should.equal([])
}

// ── policy: purist denies well-typed host (conformance) ───────────────────────

pub fn purist_denies_welltyped_host_test() {
  // An artifact with a Trusted node is well-typed but still denied by the
  // purist policy. Policy verdict precedes the kernel verdict.
  let proc_sig = term.Pi(term.Sort(1), term.Sort(5))
  let proc = hash.hash(digest.Blake3, proc_sig)
  let store = make_store([#(proc, proc_sig)])
  let host = fake_host(0x01)
  let root = term.Trusted(host, proc, term.Sort(0), term.Sort(5))
  let set = trust.trust_set(defs_env(store), root)
  // Trust set has one entry.
  set |> list.length |> should.equal(1)
  // Purist policy denies it.
  trust.is_authorized(set, trust.empty_policy())
  |> should.be_false
}

pub fn policy_admits_listed_host_test() {
  let proc_sig = term.Pi(term.Sort(1), term.Sort(5))
  let proc = hash.hash(digest.Blake3, proc_sig)
  let host = fake_host(0x01)
  let set = [trust.HostTrust(host, proc)]
  let policy = trust.policy_with_hosts([host])
  trust.is_authorized(set, policy)
  |> should.be_true
}

// ── host_message ──────────────────────────────────────────────────────────────

pub fn host_message_length_test() {
  // Message is exactly 96 bytes: 32 (proc) + 32 (hash(args)) + 32 (hash(result))
  let proc = fake_proc(0x03)
  let msg = trust.host_message(proc, term.Sort(0), term.Sort(5))
  bit_array.byte_size(msg) |> should.equal(96)
}

pub fn host_message_changes_with_result_test() {
  let proc = fake_proc(0x03)
  let msg1 = trust.host_message(proc, term.Sort(0), term.Sort(0))
  let msg2 = trust.host_message(proc, term.Sort(0), term.Sort(1))
  { msg1 == msg2 } |> should.be_false
}

pub fn host_message_changes_with_args_test() {
  let proc = fake_proc(0x03)
  let msg1 = trust.host_message(proc, term.Sort(0), term.Sort(0))
  let msg2 = trust.host_message(proc, term.Sort(1), term.Sort(0))
  { msg1 == msg2 } |> should.be_false
}

pub fn host_message_changes_with_proc_test() {
  let p1 = fake_proc(0x03)
  let p2 = fake_proc(0x04)
  let msg1 = trust.host_message(p1, term.Sort(0), term.Sort(0))
  let msg2 = trust.host_message(p2, term.Sort(0), term.Sort(0))
  { msg1 == msg2 } |> should.be_false
}

// ── verify_host_signature: authenticity alone ─────────────────────────────────
//
// These four tests were written against `verify_host_result` when that
// function checked nothing but the signature. What they actually assert is a
// property of SIGNATURES -- valid verifies, tampered/wrong-key/garbage do not
// -- and that property is still a requirement, so they now name the function
// that owns it. `verify_host_result` is a strictly stronger predicate and gets
// its own tests below; asserting authenticity through it would have meant
// dragging an environment into a test about crypto.

pub fn verify_host_signature_valid_test() {
  // Generate a key, sign, verify round-trip.
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let host = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  let msg = trust.host_message(proc, args, result)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  let r =
    trust.HostResult(
      host: host,
      proc: proc,
      args: args,
      result: result,
      signature: sig,
    )
  trust.verify_host_signature(r) |> should.be_true
}

pub fn verify_host_signature_tampered_result_test() {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let host = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  let msg = trust.host_message(proc, args, result)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  // Tamper: change result
  let r =
    trust.HostResult(
      host: host,
      proc: proc,
      args: args,
      result: term.Sort(6),
      signature: sig,
    )
  trust.verify_host_signature(r) |> should.be_false
}

pub fn verify_host_signature_wrong_key_test() {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let #(wrong_pub, _) = ffi_generate_ed25519()
  let _ = pub_bytes
  let host = pubkey.PublicKey(pubkey.Ed25519, wrong_pub)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  let msg = trust.host_message(proc, args, result)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  let r =
    trust.HostResult(
      host: host,
      proc: proc,
      args: args,
      result: result,
      signature: sig,
    )
  trust.verify_host_signature(r) |> should.be_false
}

pub fn verify_host_signature_bad_signature_test() {
  let #(pub_bytes, _) = ffi_generate_ed25519()
  let host = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  // All-zero signature -- invalid
  let bad_sig = <<
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  >>
  let r =
    trust.HostResult(
      host: host,
      proc: proc,
      args: args,
      result: result,
      signature: bad_sig,
    )
  trust.verify_host_signature(r) |> should.be_false
}

// ── verify_host_result: authenticity AND well-typedness ───────────────────────
//
// A signature says who computed a result. It says nothing about WHAT they
// computed, so a host that faithfully signs a result of the wrong type used to
// pass verification. `verify_host_result` now also holds the result to the
// type the pinned procedure promises for the given arguments, derived from the
// procedure itself rather than read off the wire.

/// An environment in which `proc` is the procedure object `Pi (Sort 1) . Sort 5`:
/// given a type in Sort(1), it promises something in Sort(5). Sort(0) : Sort(1)
/// is an acceptable argument and Sort(4) : Sort(5) an acceptable result.
fn host_env() -> #(kernel.Environment, digest.Digest) {
  let proc_sig = term.Pi(term.Sort(1), term.Sort(5))
  let proc = hash.hash(digest.Blake3, proc_sig)
  #(defs_env(make_store([#(proc, proc_sig)])), proc)
}

fn signed(
  proc: digest.Digest,
  args: term.Term,
  result: term.Term,
) -> trust.HostResult {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let sig = ffi_sign_ed25519(trust.host_message(proc, args, result), priv_bytes)
  trust.HostResult(
    host: pubkey.PublicKey(pubkey.Ed25519, pub_bytes),
    proc: proc,
    args: args,
    result: result,
    signature: sig,
  )
}

pub fn verify_host_result_accepts_signed_welltyped_result_test() {
  let #(environment, proc) = host_env()
  let r = signed(proc, term.Sort(0), term.Sort(4))
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_true
}

pub fn verify_host_result_rejects_signed_illtyped_result_test() {
  // THE REGRESSION. Sort(9) : Sort(10), not Sort(5). The host signed it
  // faithfully -- verify_host_signature says so -- and the old
  // signature-only verify_host_result accepted it.
  let #(environment, proc) = host_env()
  let r = signed(proc, term.Sort(0), term.Sort(9))
  trust.verify_host_signature(r) |> should.be_true
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_false
}

pub fn verify_host_result_rejects_args_outside_the_domain_test() {
  // Sort(7) : Sort(8), so it is not in the procedure's domain Sort(1). The
  // promise the procedure makes is only about arguments it accepts, so there
  // is no type to hold the result to and nothing to believe.
  let #(environment, proc) = host_env()
  let r = signed(proc, term.Sort(7), term.Sort(4))
  trust.verify_host_signature(r) |> should.be_true
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_false
}

pub fn verify_host_result_rejects_unresolvable_proc_test() {
  // Fail closed: no procedure object in the environment means no promise to
  // check the result against, not "nothing to object to".
  let #(environment, _proc) = host_env()
  let r = signed(fake_proc(0x40), term.Sort(0), term.Sort(4))
  trust.verify_host_signature(r) |> should.be_true
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_false
}

pub fn verify_host_result_rejects_non_pi_proc_test() {
  // A procedure object that is not a function type promises nothing about a
  // result at all.
  let proc_sig = term.Sort(3)
  let proc = hash.hash(digest.Blake3, proc_sig)
  let environment = defs_env(make_store([#(proc, proc_sig)]))
  let r = signed(proc, term.Sort(0), term.Sort(4))
  trust.verify_host_signature(r) |> should.be_true
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_false
}

pub fn verify_host_result_still_fails_closed_on_a_bad_signature_test() {
  // Well-typed is not enough either: the two bars are independent, and the
  // type check must not paper over a signature that does not verify.
  let #(environment, proc) = host_env()
  let r = signed(proc, term.Sort(0), term.Sort(4))
  let forged = trust.HostResult(..r, signature: <<0:size(512)>>)
  trust.verify_host_signature(forged) |> should.be_false
  trust.verify_host_result(environment, kernel.test_fuel, forged)
  |> should.be_false
}

pub fn verify_host_result_denies_when_fuel_runs_out_test() {
  // The type check is real reduction under the kernel's ordinary termination
  // guard, so the fuel argument has to reach it. Here the procedure object
  // only becomes a Pi after a rewrite rule fires: with fuel it verifies, and
  // with a budget that cannot finish the reduction the answer is a denial,
  // not an acceptance.
  let g = fake_proc(0x45)
  let proc_sig = term.App(term.Const(g), term.Sort(0))
  let proc = hash.hash(digest.Blake3, proc_sig)
  let rule =
    rewrite.Rule(
      lhs: rewrite.PApp(rewrite.PConst(g), rewrite.PVar(0)),
      rhs: term.Pi(term.Sort(1), term.Sort(5)),
      var_count: 1,
    )
  let environment =
    kernel.Environment(
      definitions: make_store([#(proc, proc_sig)]),
      signatures: make_store([#(g, term.Pi(term.Sort(1), term.Sort(6)))]),
      rules: fn(d) {
        case d == g {
          True -> [rule]
          False -> []
        }
      },
    )
  let r = signed(proc, term.Sort(0), term.Sort(4))
  trust.verify_host_result(environment, kernel.test_fuel, r) |> should.be_true
  trust.verify_host_result(environment, kernel.Limited(0), r)
  |> should.be_false
}

pub fn host_result_type_is_the_codomain_at_the_arguments_test() {
  let #(environment, proc) = host_env()
  trust.host_result_type(environment, kernel.test_fuel, proc, term.Sort(0))
  |> should.equal(Ok(term.Sort(5)))

  // Arguments outside the domain, and an unknown procedure, are errors rather
  // than a fallback type.
  trust.host_result_type(environment, kernel.test_fuel, proc, term.Sort(7))
  |> should.be_error
  let missing = fake_proc(0x41)
  trust.host_result_type(environment, kernel.test_fuel, missing, term.Sort(0))
  |> should.equal(Error(kernel.Unresolved(missing)))
}

pub fn verify_host_result_expected_type_depends_on_the_arguments_test() {
  // A dependent procedure: `Pi (A : Sort 0) . A`. The type the result must
  // inhabit is not fixed by the procedure alone -- it is the codomain
  // instantiated at the arguments the signature covers, so a result that
  // would be fine for one argument is rejected for another.
  let proc_sig = term.Pi(term.Sort(0), term.Var(0))
  let proc = hash.hash(digest.Blake3, proc_sig)
  let nat = fake_proc(0x42)
  let bool_ = fake_proc(0x43)
  let zero = fake_proc(0x44)
  let environment =
    kernel.Environment(
      definitions: make_store([#(proc, proc_sig)]),
      signatures: make_store([
        #(nat, term.Sort(0)),
        #(bool_, term.Sort(0)),
        // zero : nat
        #(zero, term.Const(nat)),
      ]),
      rules: kernel.empty_rules(),
    )

  trust.host_result_type(environment, kernel.test_fuel, proc, term.Const(nat))
  |> should.equal(Ok(term.Const(nat)))

  // zero : nat, asked for a nat -- accepted.
  trust.verify_host_result(
    environment,
    kernel.test_fuel,
    signed(proc, term.Const(nat), term.Const(zero)),
  )
  |> should.be_true

  // The same signed result offered as a bool -- rejected.
  trust.verify_host_result(
    environment,
    kernel.test_fuel,
    signed(proc, term.Const(bool_), term.Const(zero)),
  )
  |> should.be_false
}

// ── policy: mixed host and rule-set trust dependencies ─────────────────────────

pub fn policy_treats_host_and_rule_set_dependencies_independently_test() {
  // A trust set with one HostTrust and one RuleSetTrust entry: a policy
  // authorizing only the host still denies the rule set, and vice versa --
  // unauthorized/is_authorized must not special-case which kind of
  // dependency is missing.
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let author = fake_host(0x03)
  let rule_hash = fake_proc(0x04)
  let set = [trust.HostTrust(host, proc), trust.RuleSetTrust(author, rule_hash)]

  trust.is_authorized(set, trust.policy_with_hosts([host])) |> should.be_false
  trust.unauthorized(set, trust.policy_with_hosts([host]))
  |> should.equal([trust.RuleSetTrust(author, rule_hash)])

  trust.is_authorized(set, trust.policy_with_rule_sets([#(author, rule_hash)]))
  |> should.be_false
  trust.unauthorized(set, trust.policy_with_rule_sets([#(author, rule_hash)]))
  |> should.equal([trust.HostTrust(host, proc)])

  trust.is_authorized(set, trust.policy_with([host], [#(author, rule_hash)]))
  |> should.be_true
}

pub fn policy_rule_set_authorization_is_pinned_to_exact_hash_test() {
  // Authorizing (author, hash1) does not authorize (author, hash2) -- an
  // author is not a blanket grant over every rule set they might sign.
  let author = fake_host(0x05)
  let hash1 = fake_proc(0x06)
  let hash2 = fake_proc(0x07)
  let set = [trust.RuleSetTrust(author, hash1)]
  trust.is_authorized(set, trust.policy_with_rule_sets([#(author, hash2)]))
  |> should.be_false
  trust.is_authorized(set, trust.policy_with_rule_sets([#(author, hash1)]))
  |> should.be_true
}

// ── trust_set_with_rules ────────────────────────────────────────────────────────

// A minimal environment: one axiomatic constant `f` with a single rewrite rule
// `f x --> x`, so `f (Sort 0)` normalizes to `Sort 0` only by invoking the
// rule set.
fn strip_env() -> #(kernel.Environment, digest.Digest) {
  let f_digest = fake_proc(0x10)
  let signatures = fn(d: digest.Digest) {
    case d == f_digest {
      True -> Some(term.Pi(term.Sort(0), term.Sort(0)))
      False -> None
    }
  }
  let rule =
    rewrite.Rule(
      lhs: rewrite.PApp(rewrite.PConst(f_digest), rewrite.PVar(0)),
      rhs: term.Var(0),
      var_count: 1,
    )
  let rules = fn(d: digest.Digest) {
    case d == f_digest {
      True -> [rule]
      False -> []
    }
  }
  #(
    kernel.Environment(
      definitions: kernel.no_store(),
      signatures: signatures,
      rules: rules,
    ),
    f_digest,
  )
}

pub fn trust_set_with_rules_reports_the_rule_set_used_test() {
  let #(environment, f_digest) = strip_env()
  let author = fake_host(0x11)
  let rule_set_hash = fake_proc(0x12)
  let tag = kernel.RuleUse(author: author, rule_set: rule_set_hash)
  let provenance = fn(d: digest.Digest) {
    case d == f_digest {
      True -> [
        #(
          tag,
          rewrite.Rule(
            lhs: rewrite.PApp(rewrite.PConst(f_digest), rewrite.PVar(0)),
            rhs: term.Var(0),
            var_count: 1,
          ),
        ),
      ]
      False -> []
    }
  }
  let artifact = term.App(term.Const(f_digest), term.Sort(0))

  let assert Ok(set) =
    trust.trust_set_with_rules(
      environment,
      kernel.test_fuel,
      provenance,
      artifact,
    )
  set |> should.equal([trust.RuleSetTrust(author, rule_set_hash)])

  trust.is_authorized(set, trust.empty_policy()) |> should.be_false
  trust.is_authorized(
    set,
    trust.policy_with_rule_sets([#(author, rule_set_hash)]),
  )
  |> should.be_true
}

pub fn trust_set_with_rules_is_empty_when_no_rule_fires_test() {
  // A term that never invokes the axiomatic constant at all has no
  // rule-set trust dependency, even though the Environment carries rules.
  let #(environment, _f_digest) = strip_env()
  let provenance = fn(_: digest.Digest) { [] }
  let artifact = term.Sort(0)
  trust.trust_set_with_rules(
    environment,
    kernel.test_fuel,
    provenance,
    artifact,
  )
  |> should.equal(Ok([]))
}

pub fn trust_set_with_rules_includes_host_dependencies_too_test() {
  // trust_set_with_rules must not drop the ordinary Trusted/Const walk --
  // it is additive on top of it.
  let #(environment, _f_digest) = strip_env()
  let host = fake_host(0x13)
  let proc = fake_proc(0x14)
  let provenance = fn(_: digest.Digest) { [] }
  let artifact = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  trust.trust_set_with_rules(
    environment,
    kernel.test_fuel,
    provenance,
    artifact,
  )
  |> should.equal(Ok([trust.HostTrust(host, proc)]))
}

// ── rule-set signature verification ───────────────────────────────────────────

pub fn verify_rule_set_signature_valid_test() {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let author = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let rule_set_hash = fake_proc(0x20)
  let msg = trust.rule_set_message(rule_set_hash)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  trust.verify_rule_set_signature(trust.RuleSetSignature(
    author: author,
    hash: rule_set_hash,
    signature: sig,
  ))
  |> should.be_true
}

pub fn verify_rule_set_signature_tampered_hash_test() {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let author = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let rule_set_hash = fake_proc(0x21)
  let msg = trust.rule_set_message(rule_set_hash)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  // Tamper: claim the signature covers a different rule set's hash.
  let other_hash = fake_proc(0x22)
  trust.verify_rule_set_signature(trust.RuleSetSignature(
    author: author,
    hash: other_hash,
    signature: sig,
  ))
  |> should.be_false
}

pub fn verify_rule_set_signature_wrong_key_test() {
  let #(_pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let #(wrong_pub, _) = ffi_generate_ed25519()
  let wrong_author = pubkey.PublicKey(pubkey.Ed25519, wrong_pub)
  let rule_set_hash = fake_proc(0x23)
  let msg = trust.rule_set_message(rule_set_hash)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  trust.verify_rule_set_signature(trust.RuleSetSignature(
    author: wrong_author,
    hash: rule_set_hash,
    signature: sig,
  ))
  |> should.be_false
}

// ── trust_set: transitive through an axiom's DECLARED TYPE ────────────────────
//
// An axiomatic constant has no definition, so it lives in
// `environment.signatures`. A walk that consulted only `environment.definitions`
// resolved it to None and stopped, and a Trusted node reachable only through
// the axiom's declared type contributed nothing to the trust set -- so the
// purist policy authorized a host-dependent artifact. These tests pin the
// declared type as in-reach.

pub fn axiom_declared_type_surfaces_host_trust_test() {
  let host = fake_host(0x31)
  let proc = fake_proc(0x32)
  // `axiom : Pi (Sort 0) . <Trusted node>` -- declared type only, no body.
  let declared =
    term.Pi(term.Sort(0), term.Trusted(host, proc, term.Sort(0), term.Sort(0)))
  let axiom = hash.hash(digest.Blake3, declared)
  let environment = axioms_env([#(axiom, declared)])
  let artifact = term.Const(axiom)

  // The dependency is not visible in the artifact term at all: it is reachable
  // only by resolving the axiom and walking what the store says its type is.
  trust.trust_set(defs_env(kernel.no_store()), artifact) |> should.equal([])

  let set = trust.trust_set(environment, artifact)
  set |> should.equal([trust.HostTrust(host, proc)])

  // The point of the fix: the purist policy now DENIES this artifact. Before,
  // the trust set was empty and `is_authorized` returned True.
  trust.is_authorized(set, trust.empty_policy()) |> should.be_false
  trust.unauthorized(set, trust.empty_policy())
  |> should.equal([trust.HostTrust(host, proc)])
  trust.is_authorized(set, trust.policy_with_hosts([host])) |> should.be_true
}

pub fn axiom_declared_type_is_followed_transitively_test() {
  // outer's declared type mentions inner, whose declared type hides the
  // Trusted node: two axiom hops, no definitions anywhere.
  let host = fake_host(0x33)
  let proc = fake_proc(0x34)
  let inner_typ = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let inner = hash.hash(digest.Blake3, inner_typ)
  let outer_typ = term.Pi(term.Sort(0), term.Const(inner))
  let outer = hash.hash(digest.Blake3, outer_typ)
  let environment = axioms_env([#(inner, inner_typ), #(outer, outer_typ)])

  trust.trust_set(environment, term.Const(outer))
  |> should.equal([trust.HostTrust(host, proc)])
}

pub fn axiom_proc_signature_surfaces_inner_host_test() {
  // The existing `proc_reference_followed_test` covers a proc object that has
  // a definition. A pinned procedure is far more likely to be declared than
  // defined: its type is known, its implementation is the host's business.
  // So the inner host must surface through a proc that is an AXIOM too.
  let inner_host = fake_host(0x35)
  let inner_proc = fake_proc(0x36)
  let inner = term.Trusted(inner_host, inner_proc, term.Sort(0), term.Sort(0))
  let inner_addr = hash.hash(digest.Blake3, inner)
  let proc_typ = term.Pi(term.Sort(0), term.Const(inner_addr))
  let proc_addr = hash.hash(digest.Blake3, proc_typ)
  let environment = axioms_env([#(inner_addr, inner), #(proc_addr, proc_typ)])

  let outer_host = fake_host(0x37)
  let root = term.Trusted(outer_host, proc_addr, term.Sort(0), term.Sort(0))
  let set = trust.trust_set(environment, root)

  set |> list.length |> should.equal(2)
  set |> list.contains(trust.HostTrust(outer_host, proc_addr)) |> should.be_true
  set
  |> list.contains(trust.HostTrust(inner_host, inner_proc))
  |> should.be_true
}

pub fn axiom_walk_terminates_on_a_cyclic_signature_store_test() {
  // The signature store is supplied by the party being checked, so nothing
  // stops two declared types referring to each other. Termination must not
  // depend on the graph being acyclic.
  let host = fake_host(0x38)
  let proc = fake_proc(0x39)
  let a = fake_proc(0x3a)
  let b = fake_proc(0x3b)
  let environment =
    axioms_env([
      #(
        a,
        term.Pi(
          term.Const(b),
          term.Trusted(host, proc, term.Sort(0), term.Sort(0)),
        ),
      ),
      #(b, term.Const(a)),
    ])

  trust.trust_set(environment, term.Const(a))
  |> should.equal([trust.HostTrust(host, proc)])
}

pub fn unresolvable_const_still_adds_nothing_test() {
  // A Const in neither store carries no trust dependency of its own. It is a
  // hard type error (`Unresolved`) at check time, which is where it is
  // reported -- the trust set does not need to invent an entry for it.
  trust.trust_set(axioms_env([]), term.Const(fake_proc(0x3c)))
  |> should.equal([])
}

// ── FFI: Ed25519 sign/keygen (via cronch_crypto) ──────────────────────────────

@external(erlang, "cronch_crypto", "generate_keypair")
fn ffi_generate_ed25519() -> #(BitArray, BitArray)

@external(erlang, "cronch_crypto", "sign_ed25519")
fn ffi_sign_ed25519(msg: BitArray, priv_key: BitArray) -> BitArray
