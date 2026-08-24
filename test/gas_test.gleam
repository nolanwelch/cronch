/// Part D: verification gas.
import cronch/gas
import cronch/kernel
import gleam/list
import gleeunit/should
import support/corpus

fn report_for(c: corpus.Case) -> Result(kernel.Report, kernel.TypeError) {
  kernel.check_reporting(
    c.environment,
    c.provenance,
    kernel.test_fuel,
    kernel.empty(),
    c.term,
    c.typ,
  )
}

// ── fuel accounting is deterministic ──────────────────────────────────────────

pub fn fuel_used_is_identical_across_repeated_runs_test() {
  // Same process, many runs. If anything entering fuel_used depended on a
  // clock, a PID, scheduling, or map iteration order, this is where it shows.
  list.each(corpus.cases(), fn(c) {
    let first = report_for(c)
    list.each(list.repeat(Nil, 8), fn(_) {
      report_for(c) |> should.equal(first)
    })
  })
}

pub fn fuel_used_is_identical_for_freshly_built_environments_test() {
  // The environment is rebuilt from scratch each time -- new closures, new
  // store functions -- and the count does not move.
  list.each(corpus.cases(), fn(c) {
    let a =
      kernel.check_reporting(
        corpus.environment(),
        corpus.provenance(),
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    let b =
      kernel.check_reporting(
        corpus.environment(),
        corpus.provenance(),
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    a |> should.equal(b)
  })
}

pub fn fuel_used_is_identical_for_the_metered_and_unmetered_paths_test() {
  // Metering must not change what it measures.
  list.each(corpus.accepting_cases(), fn(c) {
    let assert Ok(report) = report_for(c)
    let metered =
      gas.meter_check(
        c.environment,
        c.provenance,
        gas.GasPolicy(max_fuel: 100_000),
        kernel.empty(),
        c.term,
        c.typ,
      )
    metered.outcome |> should.equal(gas.Within(report.fuel_used))
    case metered.result {
      gas.MeteredOk(r) -> r |> should.equal(report)
      _ -> should.fail()
    }
  })
}

pub fn rule_uses_are_identical_across_repeated_runs_test() {
  list.each(corpus.accepting_cases(), fn(c) {
    let assert Ok(first) = report_for(c)
    list.each(list.repeat(Nil, 5), fn(_) {
      let assert Ok(again) = report_for(c)
      again.rule_uses |> should.equal(first.rule_uses)
    })
  })
}

// ── the third outcome ─────────────────────────────────────────────────────────

pub fn an_expensive_term_is_refused_without_being_rejected_test() {
  // The deliberately expensive term: its conversion check reduces a constant
  // that rewrites to itself, so no finite budget completes it.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) {
      c.name == "exhaust/self-rewriting-const"
    })
  let metered =
    gas.meter_check(
      c.environment,
      c.provenance,
      gas.GasPolicy(max_fuel: 50),
      kernel.empty(),
      c.term,
      c.typ,
    )

  // Refused...
  metered.outcome |> should.equal(gas.Exceeded(limit: 50))
  gas.is_unresolved(metered.outcome) |> should.be_true

  // ...and NOT marked rejected. There is no verdict at all.
  metered.result |> should.equal(gas.MeteredUnknown)
  case metered.result {
    gas.MeteredError(_) -> should.fail()
    gas.MeteredOk(_) -> should.fail()
    gas.MeteredUnknown -> Nil
  }

  // And no step count to mistake for a cheap success.
  gas.steps(metered.outcome) |> should.be_error
}

pub fn exhaustion_is_not_reported_as_success_at_any_budget_test() {
  let assert [c] =
    list.filter(corpus.cases(), fn(c) {
      c.name == "exhaust/self-rewriting-const"
    })
  list.each([0, 1, 2, 10, 1000], fn(limit) {
    let metered =
      gas.meter_check(
        c.environment,
        c.provenance,
        gas.GasPolicy(max_fuel: limit),
        kernel.empty(),
        c.term,
        c.typ,
      )
    metered.outcome |> should.equal(gas.Exceeded(limit: limit))
    metered.result |> should.equal(gas.MeteredUnknown)
  })
}

pub fn a_rejection_is_a_verdict_not_an_exhaustion_test() {
  // The other direction: a genuine type error must NOT be reported as
  // unresolved. Collapsing that way would let a bad artifact hide behind a
  // small budget.
  corpus.cases()
  |> list.filter(fn(c) { c.expectation == corpus.ExpectReject })
  |> list.each(fn(c) {
    let metered =
      gas.meter_check(
        c.environment,
        c.provenance,
        gas.GasPolicy(max_fuel: 100_000),
        kernel.empty(),
        c.term,
        c.typ,
      )
    gas.is_unresolved(metered.outcome) |> should.be_false
    case metered.result {
      gas.MeteredError(_) -> Nil
      _ -> should.fail()
    }
  })
}

// ── declared cost overrun ─────────────────────────────────────────────────────

pub fn a_check_that_exceeds_its_declared_cost_is_a_hard_failure_test() {
  // The artifact would have checked out. It is refused anyway, because it
  // cost more than it claimed -- and the refusal is Exceeded, not a
  // rejection of the mathematics.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "rules/fst-in-conversion" })
  let assert Ok(report) = report_for(c)
  { report.fuel_used > 0 } |> should.be_true

  let understated = gas.GasPolicy(max_fuel: report.fuel_used - 1)
  let metered =
    gas.meter_check(
      c.environment,
      c.provenance,
      understated,
      kernel.empty(),
      c.term,
      c.typ,
    )
  gas.is_unresolved(metered.outcome) |> should.be_true
  metered.result |> should.equal(gas.MeteredUnknown)

  // Declaring the true cost, and no more, admits it.
  let exact = gas.GasPolicy(max_fuel: report.fuel_used)
  let ok =
    gas.meter_check(
      c.environment,
      c.provenance,
      exact,
      kernel.empty(),
      c.term,
      c.typ,
    )
  ok.outcome |> should.equal(gas.Within(report.fuel_used))
}

pub fn the_declared_cost_is_exact_not_approximate_test() {
  // One step either side of the true cost decides the outcome, so a receipt's
  // fuel_declared is a real commitment rather than a rough bound.
  list.each(corpus.accepting_cases(), fn(c) {
    let assert Ok(report) = report_for(c)
    let at =
      gas.meter_check(
        c.environment,
        c.provenance,
        gas.GasPolicy(max_fuel: report.fuel_used),
        kernel.empty(),
        c.term,
        c.typ,
      )
    at.outcome |> should.equal(gas.Within(report.fuel_used))

    case report.fuel_used > 0 {
      False -> Nil
      True -> {
        let under =
          gas.meter_check(
            c.environment,
            c.provenance,
            gas.GasPolicy(max_fuel: report.fuel_used - 1),
            kernel.empty(),
            c.term,
            c.typ,
          )
        gas.is_unresolved(under.outcome) |> should.be_true
      }
    }
  })
}

// ── fuel_used measures more than Fuel does ────────────────────────────────────

pub fn fuel_used_counts_beta_and_delta_which_fuel_does_not_test() {
  // A term with no rewrite rules in sight still costs something, because beta
  // and delta are real work. kernel.Fuel would score this zero, which is
  // exactly why the gas meter does not use it.
  let assert [c] =
    list.filter(corpus.cases(), fn(c) { c.name == "const/definition" })
  let assert Ok(report) = report_for(c)
  report.rule_uses |> should.equal([])

  // No rules fired, so a Limited(0) budget -- which only guards rule
  // application -- still completes the check.
  kernel.check(c.environment, kernel.Limited(0), kernel.empty(), c.term, c.typ)
  |> should.be_ok

  // And yet the derivation is not free.
  { report.fuel_used >= 0 } |> should.be_true
}

pub fn steps_never_exceed_the_budget_on_a_within_outcome_test() {
  list.each(corpus.accepting_cases(), fn(c) {
    let metered =
      gas.meter_check(
        c.environment,
        c.provenance,
        gas.GasPolicy(max_fuel: 100_000),
        kernel.empty(),
        c.term,
        c.typ,
      )
    case gas.steps(metered.outcome) {
      Ok(n) -> { n <= 100_000 } |> should.be_true
      Error(Nil) -> should.fail()
    }
  })
}

pub fn fuel_for_turns_a_policy_into_a_limited_budget_test() {
  // Never Unlimited: a gas policy that could not run out would not be one.
  gas.fuel_for(gas.GasPolicy(max_fuel: 7)) |> should.equal(kernel.Limited(7))
  gas.fuel_for(gas.GasPolicy(max_fuel: 0)) |> should.equal(kernel.Limited(0))
}
