import cronch/digest
import cronch/kernel
import cronch/pubkey
import cronch/rewrite
import cronch/trust
import gleam/list
import gleeunit/should
import support/reference_rules

// ── helpers ───────────────────────────────────────────────────────────────────

fn fake_author() -> pubkey.PublicKey {
  let bytes = <<
    9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
  >>
  pubkey.PublicKey(pubkey.Ed25519, bytes)
}

fn provenance(
  author: pubkey.PublicKey,
  hash: digest.Digest,
) -> fn(digest.Digest) -> List(#(kernel.RuleUse, rewrite.Rule)) {
  let tag = kernel.RuleUse(author: author, rule_set: hash)
  fn(d) {
    reference_rules.rules()(d)
    |> list.map(fn(r) { #(tag, r) })
  }
}

// ── axiom types are well-formed ────────────────────────────────────────────────

pub fn axiom_types_are_well_formed_test() {
  // Every declared signature must itself type-check as a valid type -- a
  // sanity check on the hand-written de Bruijn indices above as much as on
  // the mechanism.
  let environment = reference_rules.environment()
  kernel.infer(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    reference_rules.sigma_typ(),
  )
  |> should.be_ok
  kernel.infer(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    reference_rules.pair_typ(),
  )
  |> should.be_ok
  kernel.infer(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    reference_rules.fst_typ(),
  )
  |> should.be_ok
  kernel.infer(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    reference_rules.snd_typ(),
  )
  |> should.be_ok
  kernel.infer(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    reference_rules.j_typ(),
  )
  |> should.be_ok
}

// ── the rules require the rule set -- an axiom alone is inert ─────────────────

pub fn fst_stays_stuck_without_the_rule_set_test() {
  // Same signatures, but no rules: fst/pair are genuine, permanently-stuck
  // axiomatic constants. Nothing reduces -- proving the reduction in the
  // tests below comes from the rule set, not from the axioms alone.
  let env_no_rules =
    kernel.Environment(
      definitions: kernel.no_store(),
      signatures: reference_rules.signatures(),
      rules: kernel.empty_rules(),
    )
  let #(artifact, _expected) = reference_rules.fst_pair_example()
  kernel.normalize(env_no_rules, kernel.test_fuel, artifact)
  |> should.equal(Ok(artifact))
}

// ── Sigma projections and J actually compute ───────────────────────────────────

pub fn sigma_fst_reduces_test() {
  let environment = reference_rules.environment()
  let #(artifact, expected) = reference_rules.fst_pair_example()
  kernel.normalize(environment, kernel.test_fuel, artifact)
  |> should.equal(Ok(expected))
}

pub fn sigma_snd_reduces_test() {
  let environment = reference_rules.environment()
  let #(artifact, expected) = reference_rules.snd_pair_example()
  kernel.normalize(environment, kernel.test_fuel, artifact)
  |> should.equal(Ok(expected))
}

pub fn j_refl_reduces_test() {
  let environment = reference_rules.environment()
  let #(artifact, expected) = reference_rules.j_example()
  kernel.normalize(environment, kernel.test_fuel, artifact)
  |> should.equal(Ok(expected))
}

// ── the trust-gating validation test ───────────────────────────────────────────
//
// This is the test that proves the trust-gating mechanism from trust.gleam
// actually works for a rule set, not merely that the rewriting works (that
// much is already covered above): (a) the reference rule set is a real
// trust dependency that the purist policy refuses, and (b) explicitly
// authorizing this exact (author, rule-set hash) pair -- and nothing more
// -- is what flips that verdict.

pub fn sigma_projection_requires_an_authorized_rule_set_test() {
  let environment = reference_rules.environment()
  let author = fake_author()
  let rule_set_hash = reference_rules.rule_set_hash()
  let provenance = provenance(author, rule_set_hash)
  let #(artifact, expected) = reference_rules.fst_pair_example()

  let assert Ok(set) =
    trust.trust_set_with_rules(
      environment,
      kernel.test_fuel,
      provenance,
      artifact,
    )

  // The reference rule set shows up as a genuine trust dependency.
  set |> should.equal([trust.RuleSetTrust(author, rule_set_hash)])

  // (a) fails under the empty (purist) policy: zero trust dependencies of
  // any kind, oracle or rule-set, are accepted -- exactly as before this
  // task, per trust.gleam's module doc comment.
  trust.is_authorized(set, trust.empty_policy()) |> should.be_false

  // (b) succeeds once this exact (author, hash) pair is authorized.
  let policy = trust.policy_with_rule_sets([#(author, rule_set_hash)])
  trust.is_authorized(set, policy) |> should.be_true

  // A policy that authorizes a different rule-set hash (e.g. a stale or
  // tampered version) still refuses it -- authorization is pinned to the
  // exact content address, not the author alone.
  let other_hash =
    digest.Digest(digest.Blake3, <<
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1,
    >>)
  let stale_policy = trust.policy_with_rule_sets([#(author, other_hash)])
  trust.is_authorized(set, stale_policy) |> should.be_false

  // The rewriting itself does not depend on policy at all -- the kernel
  // computes regardless; policy is what a caller consults *before* trusting
  // that computation (see trust.gleam's module doc comment: "Policy MUST be
  // checked before the kernel runs").
  kernel.normalize(environment, kernel.test_fuel, artifact)
  |> should.equal(Ok(expected))
}
