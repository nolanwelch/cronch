import cronch/digest
import cronch/hash
import cronch/pubkey
import cronch/term
import cronch/trust
import gleam/bit_array
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

// ── helpers ───────────────────────────────────────────────────────────────────

fn no_store() -> trust.Store {
  fn(_) { None }
}

fn make_store(entries: List(#(digest.Digest, term.Term))) -> trust.Store {
  fn(d: digest.Digest) {
    case list.find(entries, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> None
    }
  }
}

fn fake_host(b: Int) -> pubkey.PublicKey {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
  >>
  pubkey.PublicKey(pubkey.Ed25519, bytes)
}

fn fake_proc(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

// ── trust_set: pure terms ─────────────────────────────────────────────────────

pub fn pure_term_empty_trust_set_test() {
  let t = term.Lam(term.Sort(0), term.Var(0))
  trust.trust_set(no_store(), t)
  |> should.equal([])
}

pub fn sort_empty_trust_set_test() {
  trust.trust_set(no_store(), term.Sort(0))
  |> should.equal([])
}

// ── trust_set: own Trusted nodes ──────────────────────────────────────────────

pub fn own_trusted_node_test() {
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let t = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  trust.trust_set(no_store(), t)
  |> should.equal([#(host, proc)])
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
  let set = trust.trust_set(no_store(), t)
  set |> list.length |> should.equal(2)
  set |> list.contains(#(h1, p1)) |> should.be_true
  set |> list.contains(#(h2, p2)) |> should.be_true
}

pub fn duplicate_trusted_nodes_deduplicated_test() {
  // Same (host, proc) appearing twice -> trust set has exactly one entry.
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let node = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let t = term.App(node, node)
  trust.trust_set(no_store(), t)
  |> should.equal([#(host, proc)])
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
  trust.trust_set(store, x)
  |> should.equal([#(host, proc)])
}

pub fn const_not_in_store_adds_nothing_test() {
  let d = fake_proc(0xff)
  let t = term.Const(d)
  trust.trust_set(no_store(), t)
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

  let store =
    make_store([#(inner_addr, inner), #(proc_addr, proc_obj)])

  let outer_host = fake_host(0x0a)
  let root = term.Trusted(outer_host, proc_addr, term.Sort(0), term.Sort(0))
  let set = trust.trust_set(store, root)

  set |> list.length |> should.equal(2)
  set |> list.contains(#(outer_host, proc_addr)) |> should.be_true
  set |> list.contains(#(inner_host, inner_proc)) |> should.be_true
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
  trust.trust_set(store, t)
  |> should.equal([#(host, proc)])
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
  let set = trust.trust_set(no_store(), t)
  set |> should.equal([#(h1, p1), #(h3, p4)])
}

// ── policy ────────────────────────────────────────────────────────────────────

pub fn empty_policy_denies_host_test() {
  let host = fake_host(0x01)
  let proc = fake_proc(0x02)
  let set = [#(host, proc)]
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
  let set = [#(host, proc)]
  let policy = trust.policy_with_hosts([host])
  trust.is_authorized(set, policy)
  |> should.be_true
}

pub fn policy_missing_one_host_denies_test() {
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h2 = fake_host(0x03)
  let p2 = fake_proc(0x04)
  let set = [#(h1, p1), #(h2, p2)]
  // Policy only admits h1; h2 is not covered.
  let policy = trust.policy_with_hosts([h1])
  trust.is_authorized(set, policy)
  |> should.be_false
  trust.unauthorized(set, policy)
  |> should.equal([#(h2, p2)])
}

pub fn policy_covering_all_hosts_authorizes_test() {
  let h1 = fake_host(0x01)
  let p1 = fake_proc(0x02)
  let h2 = fake_host(0x03)
  let p2 = fake_proc(0x04)
  let set = [#(h1, p1), #(h2, p2)]
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
  let root =
    term.Trusted(host, proc, term.Sort(0), term.Sort(5))
  let set = trust.trust_set(store, root)
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
  let set = [#(host, proc)]
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

// ── verify_host_result ────────────────────────────────────────────────────────

pub fn verify_host_result_valid_test() {
  // Generate a key, sign, verify round-trip.
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let host = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  let msg = trust.host_message(proc, args, result)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  let r = trust.HostResult(host: host, proc: proc, args: args, result: result, signature: sig)
  trust.verify_host_result(r) |> should.be_true
}

pub fn verify_host_result_tampered_result_test() {
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
      host: host, proc: proc, args: args,
      result: term.Sort(6), signature: sig,
    )
  trust.verify_host_result(r) |> should.be_false
}

pub fn verify_host_result_wrong_key_test() {
  let #(pub_bytes, priv_bytes) = ffi_generate_ed25519()
  let #(wrong_pub, _) = ffi_generate_ed25519()
  let _ = pub_bytes
  let host = pubkey.PublicKey(pubkey.Ed25519, wrong_pub)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  let msg = trust.host_message(proc, args, result)
  let sig = ffi_sign_ed25519(msg, priv_bytes)
  let r = trust.HostResult(host: host, proc: proc, args: args, result: result, signature: sig)
  trust.verify_host_result(r) |> should.be_false
}

pub fn verify_host_result_bad_signature_test() {
  let #(pub_bytes, _) = ffi_generate_ed25519()
  let host = pubkey.PublicKey(pubkey.Ed25519, pub_bytes)
  let proc = fake_proc(0x03)
  let args = term.Sort(0)
  let result = term.Sort(5)
  // All-zero signature -- invalid
  let bad_sig = <<
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  >>
  let r =
    trust.HostResult(
      host: host, proc: proc, args: args, result: result, signature: bad_sig,
    )
  trust.verify_host_result(r) |> should.be_false
}

// ── FFI: Ed25519 sign/keygen (via cronch_crypto) ──────────────────────────────

@external(erlang, "cronch_crypto", "generate_keypair")
fn ffi_generate_ed25519() -> #(BitArray, BitArray)

@external(erlang, "cronch_crypto", "sign_ed25519")
fn ffi_sign_ed25519(msg: BitArray, priv_key: BitArray) -> BitArray
