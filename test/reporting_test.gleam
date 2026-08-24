/// Part C: rule-use reporting is a byproduct of the typing derivation.
///
/// C1 is the regression test for the policy bypass. C2/C3/C4 are the
/// guardrails that say the fix observed more without deciding differently.
import cronch/kernel
import cronch/trust
import gleam/list
import gleeunit/should
import support/corpus

// ── helpers ───────────────────────────────────────────────────────────────────

/// The verdict a plain (non-reporting) check reaches. Three outcomes, never
/// two: a budget exhaustion is not a rejection.
type Verdict {
  Accepted
  Rejected
  Exhausted
}

fn verdict_of(r: Result(a, kernel.TypeError)) -> Verdict {
  case r {
    Ok(_) -> Accepted
    Error(kernel.FuelExhausted) -> Exhausted
    Error(_) -> Rejected
  }
}

fn plain_verdict(c: corpus.Case) -> Verdict {
  verdict_of(kernel.check(
    c.environment,
    kernel.test_fuel,
    kernel.empty(),
    c.term,
    c.typ,
  ))
}

fn reported_verdict(c: corpus.Case) -> Verdict {
  verdict_of(kernel.check_reporting(
    c.environment,
    c.provenance,
    kernel.test_fuel,
    kernel.empty(),
    c.term,
    c.typ,
  ))
}

/// The trust set as it was computed BEFORE this part: the Trusted/Const walk
/// plus whatever normalizing the artifact happens to invoke. Kept here rather
/// than deleted, because "the new set is a superset of the old one" is only a
/// meaningful claim if the old one is still computable.
fn old_trust_set(
  c: corpus.Case,
) -> Result(List(trust.TrustPair), kernel.TypeError) {
  trust.trust_set_with_rules(
    c.environment,
    kernel.test_fuel,
    c.provenance,
    c.term,
  )
}

fn new_trust_set(
  c: corpus.Case,
) -> Result(List(trust.TrustPair), kernel.TypeError) {
  trust.trust_set_of_check(
    c.environment,
    c.provenance,
    kernel.test_fuel,
    kernel.empty(),
    c.term,
    c.typ,
  )
}

fn corpus_rule_set() -> trust.TrustPair {
  trust.RuleSetTrust(corpus.author(), corpus.rule_set_hash())
}

// ── C1: the regression ────────────────────────────────────────────────────────

pub fn c1_annotation_only_rule_use_is_a_policy_bypass_test() {
  // The artifact: `lam (x : S) => x` checked against `S -> S`.
  //
  // `S`'s declared type is the axiom `W`, and `W` is only a *sort* because
  // the rule `W --> Type 0` says so. Establishing that a binder's domain
  // annotation denotes a type therefore fires that rule -- inside the
  // derivation, in `infer_sort`, where nothing in the artifact's normal form
  // ever goes.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "rules/annotation-only" })

  // It typechecks.
  kernel.check(c.environment, kernel.test_fuel, kernel.empty(), c.term, c.typ)
  |> should.be_ok

  // And it typechecks ONLY because of that rule set: with the same axioms and
  // no rules, `W` never becomes a sort and the check fails. So the dependency
  // is genuine, not decorative.
  kernel.check(
    corpus.environment_without_rules(),
    kernel.test_fuel,
    kernel.empty(),
    c.term,
    c.typ,
  )
  |> should.be_error

  // THE BUG. The reduction-scoped trust set sees nothing at all...
  old_trust_set(c) |> should.equal(Ok([]))

  // ...and so the purist policy -- which is supposed to accept only artifacts
  // with zero trust dependencies of any kind -- reports this one authorized.
  let assert Ok(old) = old_trust_set(c)
  trust.is_authorized(old, trust.empty_policy()) |> should.be_true

  // THE FIX. The derivation-integral set names the rule set the acceptance
  // actually rested on.
  new_trust_set(c) |> should.equal(Ok([corpus_rule_set()]))

  // And the purist policy now REFUSES it.
  let assert Ok(new) = new_trust_set(c)
  trust.is_authorized(new, trust.empty_policy()) |> should.be_false
  trust.unauthorized(new, trust.empty_policy())
  |> should.equal([corpus_rule_set()])

  // Authorizing that exact (author, rule-set hash) pair, and nothing else, is
  // what flips the verdict back.
  trust.is_authorized(
    new,
    trust.policy_with_rule_sets([#(corpus.author(), corpus.rule_set_hash())]),
  )
  |> should.be_true
}

pub fn c1_the_report_names_the_rule_set_directly_test() {
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "rules/annotation-only" })
  let assert Ok(report) =
    kernel.check_reporting(
      c.environment,
      c.provenance,
      kernel.test_fuel,
      kernel.empty(),
      c.term,
      c.typ,
    )
  // Reported at the point the reduction happened, so the use is present even
  // though the artifact's normal form never mentions W.
  list.contains(
    report.rule_uses,
    kernel.RuleUse(author: corpus.author(), rule_set: corpus.rule_set_hash()),
  )
  |> should.be_true
}

// ── C2: non-regression ────────────────────────────────────────────────────────

pub fn c2_verdicts_are_unchanged_for_every_corpus_term_test() {
  // Recording is not deciding: turning reporting on must not move a single
  // accept/reject/exhaust outcome.
  list.each(corpus.cases(), fn(c) {
    reported_verdict(c)
    |> should.equal(plain_verdict(c))
  })
}

pub fn c2_verdicts_match_the_declared_expectation_test() {
  // The corpus's own note about each case, checked rather than trusted -- so
  // "unchanged" is anchored to something, not merely self-consistent.
  list.each(corpus.cases(), fn(c) {
    let expected = case c.expectation {
      corpus.ExpectAccept -> Accepted
      corpus.ExpectReject -> Rejected
      corpus.ExpectExhaust -> Exhausted
    }
    plain_verdict(c) |> should.equal(expected)
  })
}

pub fn c2_the_c1_artifact_still_typechecks_test() {
  // Only its reported dependency changed. It is not newly rejected, and it is
  // not newly accepted either.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "rules/annotation-only" })
  plain_verdict(c) |> should.equal(Accepted)
  reported_verdict(c) |> should.equal(Accepted)
}

pub fn c2_inferred_types_are_unchanged_test() {
  // The reporting path returns the same type, not merely the same verdict.
  list.each(corpus.cases(), fn(c) {
    let plain =
      kernel.infer(c.environment, kernel.test_fuel, kernel.empty(), c.term)
    let reported =
      kernel.infer_reporting(
        c.environment,
        c.provenance,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
      )
    case plain, reported {
      Ok(a), Ok(#(b, _)) -> a |> should.equal(b)
      Error(a), Error(b) -> a |> should.equal(b)
      _, _ -> should.fail()
    }
  })
}

// ── C3: monotonicity ──────────────────────────────────────────────────────────

pub fn c3_new_trust_set_is_a_superset_of_the_old_one_test() {
  // For every corpus term that typechecks, everything the old set reported is
  // still reported. The fix only ever adds.
  list.each(corpus.accepting_cases(), fn(c) {
    let assert Ok(old) = old_trust_set(c)
    let assert Ok(new) = new_trust_set(c)
    list.each(old, fn(pair) { list.contains(new, pair) |> should.be_true })
  })
}

pub fn c3_terms_whose_trust_set_grew_are_exactly_the_expected_ones_test() {
  // Every term here was previously misreported. Pinning the list means a
  // future change that silently widens or narrows the fix fails this test
  // rather than passing quietly.
  let grew =
    corpus.accepting_cases()
    |> list.filter(fn(c) {
      let assert Ok(old) = old_trust_set(c)
      let assert Ok(new) = new_trust_set(c)
      list.length(new) > list.length(old)
    })
    |> list.map(fn(c) { c.name })

  grew |> should.equal(["rules/annotation-only"])
}

pub fn c3_growth_is_only_ever_rule_set_trust_test() {
  // The static Trusted/Const walk is unchanged, so nothing new appears as a
  // HostTrust -- a host dependency was never the thing being under-reported.
  list.each(corpus.accepting_cases(), fn(c) {
    let assert Ok(old) = old_trust_set(c)
    let assert Ok(new) = new_trust_set(c)
    list.each(new, fn(pair) {
      case list.contains(old, pair) {
        True -> Nil
        False ->
          case pair {
            trust.RuleSetTrust(_, _) -> Nil
            trust.HostTrust(_, _) -> should.fail()
          }
      }
    })
  })
}

// ── C4: purist artifacts stay purist ──────────────────────────────────────────

pub fn c4_purist_artifacts_have_an_empty_trust_set_test() {
  // Widening the net must not sweep up artifacts that depend on nothing. If
  // this fails, the fix over-reports and the purist policy becomes useless.
  corpus.accepting_cases()
  |> list.filter(fn(c) { starts_with_purist(c.name) })
  |> list.each(fn(c) {
    new_trust_set(c) |> should.equal(Ok([]))
    let assert Ok(set) = new_trust_set(c)
    trust.is_authorized(set, trust.empty_policy()) |> should.be_true
  })
}

pub fn c4_purist_artifacts_report_no_rule_uses_test() {
  corpus.accepting_cases()
  |> list.filter(fn(c) { starts_with_purist(c.name) })
  |> list.each(fn(c) {
    let assert Ok(report) =
      kernel.check_reporting(
        c.environment,
        c.provenance,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    report.rule_uses |> should.equal([])
  })
}

fn starts_with_purist(name: String) -> Bool {
  case name {
    "purist/" <> _ -> True
    _ -> False
  }
}

// ── fail-closed ───────────────────────────────────────────────────────────────

pub fn a_failed_check_yields_no_trust_set_at_all_test() {
  // Absence of evidence never yields acceptance: a term that does not
  // typecheck has no derivation, so there is no derivation trust set to
  // mistake for an empty (and therefore authorized) one.
  corpus.cases()
  |> list.filter(fn(c) { c.expectation != corpus.ExpectAccept })
  |> list.each(fn(c) { new_trust_set(c) |> should.be_error })
}

pub fn an_exhausted_check_yields_no_trust_set_test() {
  let assert [c] =
    list.filter(corpus.cases(), fn(c) {
      c.name == "exhaust/self-rewriting-const"
    })
  new_trust_set(c) |> should.equal(Error(kernel.FuelExhausted))
}

// ── the reporting entry points are the same derivation ────────────────────────

pub fn reporting_and_plain_agree_on_errors_test() {
  list.each(corpus.cases(), fn(c) {
    let plain =
      kernel.check(
        c.environment,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    let reported =
      kernel.check_reporting(
        c.environment,
        c.provenance,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    case plain, reported {
      Ok(_), Ok(_) -> Nil
      Error(a), Error(b) -> a |> should.equal(b)
      _, _ -> should.fail()
    }
  })
}

pub fn rule_uses_are_reported_in_firing_order_with_repeats_test() {
  // Not a set: a Report says what happened, and callers that want a set
  // deduplicate. Keeping repeats is what makes fuel_used and rule_uses agree
  // about how much rewriting actually took place.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "rules/fst-in-conversion" })
  let assert Ok(report) =
    kernel.check_reporting(
      c.environment,
      c.provenance,
      kernel.test_fuel,
      kernel.empty(),
      c.term,
      c.typ,
    )
  { report.rule_uses != [] } |> should.be_true
  list.each(report.rule_uses, fn(u) {
    u |> should.equal(kernel.RuleUse(corpus.author(), corpus.rule_set_hash()))
  })
}
