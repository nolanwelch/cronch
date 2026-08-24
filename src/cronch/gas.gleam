/// Verification gas: a declared cost for checking an artifact, and the
/// outcome of metering a check against it.
///
/// Outside the kernel, and outside the TCB. Nothing here can make a check
/// succeed that would otherwise fail; it can only refuse to call a check
/// successful.
///
/// Three outcomes, never two
/// -------------------------
/// A check that exhausts its budget is NEITHER accepted NOR rejected. "This
/// artifact does not typecheck" and "I could not afford to find out" are
/// different claims about the world, and collapsing them in either direction
/// is a bug:
///
///   - folded into rejection, a budget too small to verify an honest artifact
///     silently defames it;
///   - folded into acceptance, an adversary gets a proof of anything by making
///     verification expensive enough.
///
/// So `GasOutcome` has no Boolean reading, `Exceeded` is not an error variant
/// of `Within`, and no function in this module returns a Bool.
///
/// Two ways to run out
/// -------------------
/// They are genuinely different and both land in `Exceeded`:
///
///   - The kernel reports `FuelExhausted`. Reduction hit the `Fuel` guard and
///     stopped; the derivation is incomplete and no verdict exists.
///   - The derivation completed, but performed more steps than the artifact
///     declared it would. The verdict exists, and is discarded: a declared
///     cost that a check exceeds is a hard failure of the artifact's claim,
///     independent of whether the check would eventually have succeeded.
///
/// The second is the reason `fuel_used` is a step counter rather than `Fuel`
/// arithmetic. `Fuel` is consumed only by rewrite-rule application, so a term
/// can be arbitrarily expensive in beta and delta steps while consuming almost
/// no fuel. Metering the declared cost against the step count catches that;
/// metering it against `Fuel` would not.
import cronch/kernel.{type Environment, type Provenance, type TypeError}
import cronch/term.{type Term}

/// A locally chosen ceiling on how much work verifying an artifact may take,
/// measured in the reduction steps `kernel.Report.fuel_used` counts.
pub type GasPolicy {
  GasPolicy(max_fuel: Int)
}

/// The result of metering a check. Not a Result, not a Bool: `Exceeded` is a
/// third outcome that must survive every pattern match on its own.
pub type GasOutcome {
  /// The derivation completed within budget, having performed this many steps.
  Within(Int)
  /// The budget was reached. The check is neither accepted nor rejected.
  Exceeded(limit: Int)
}

/// What a metered check produced. `outcome` is separate from `result` on
/// purpose: a caller must look at both, and cannot get an accept/reject
/// verdict out of an `Exceeded` run at all, because there is none to give.
pub type Metered {
  Metered(outcome: GasOutcome, result: MeteredResult)
}

/// The verdict a metered check reached, when it reached one.
pub type MeteredResult {
  /// The derivation completed and the type checked out, within budget.
  MeteredOk(report: kernel.Report)
  /// The derivation completed and the type did not check out, within budget.
  MeteredError(error: TypeError)
  /// No verdict: the budget ran out first, or the completed derivation cost
  /// more than was declared. Never a synonym for either of the above.
  MeteredUnknown
}

/// Turn a gas policy into the reduction budget the kernel enforces.
///
/// `max_fuel` bounds rewrite-rule applications specifically -- that is what
/// `kernel.Fuel` counts -- while the same number is used below as the ceiling
/// on total steps. Since every rule application is also a step, a derivation
/// that stays within the step budget necessarily stayed within the fuel
/// budget, so the two never disagree about which direction to fail in.
pub fn fuel_for(policy: GasPolicy) -> kernel.Fuel {
  kernel.Limited(policy.max_fuel)
}

/// Meter a check against a declared cost.
///
/// Never returns a Bool and never collapses the three outcomes. The order of
/// the cases below is the whole content of this function: exhaustion is tested
/// before success, and overrun is tested before success, so there is no path
/// on which running out of budget is reported as a passing check.
pub fn meter_check(
  environment: Environment,
  provenance: Provenance,
  policy: GasPolicy,
  cx: kernel.Context,
  t: Term,
  typ: Term,
) -> Metered {
  case
    kernel.check_reporting(
      environment,
      provenance,
      fuel_for(policy),
      cx,
      t,
      typ,
    )
  {
    // Reduction hit the guard. No derivation, no verdict.
    Error(kernel.FuelExhausted) ->
      Metered(Exceeded(limit: policy.max_fuel), MeteredUnknown)

    // A real type error, reached within budget. This IS a verdict.
    Error(e) -> Metered(within_or_exceeded(0, policy), MeteredError(e))

    Ok(report) ->
      case report.fuel_used > policy.max_fuel {
        // The derivation completed, and cost more than was declared. The
        // artifact's claim about its own cost is false, so the run yields no
        // verdict even though one was computed.
        True -> Metered(Exceeded(limit: policy.max_fuel), MeteredUnknown)
        False -> Metered(Within(report.fuel_used), MeteredOk(report))
      }
  }
}

/// Meter an inference the same way.
pub fn meter_infer(
  environment: Environment,
  provenance: Provenance,
  policy: GasPolicy,
  cx: kernel.Context,
  t: Term,
) -> #(Metered, Result(Term, Nil)) {
  case
    kernel.infer_reporting(environment, provenance, fuel_for(policy), cx, t)
  {
    Error(kernel.FuelExhausted) -> #(
      Metered(Exceeded(limit: policy.max_fuel), MeteredUnknown),
      Error(Nil),
    )
    Error(e) -> #(
      Metered(within_or_exceeded(0, policy), MeteredError(e)),
      Error(Nil),
    )
    Ok(#(typ, report)) ->
      case report.fuel_used > policy.max_fuel {
        True -> #(
          Metered(Exceeded(limit: policy.max_fuel), MeteredUnknown),
          Error(Nil),
        )
        False -> #(
          Metered(Within(report.fuel_used), MeteredOk(report)),
          Ok(typ),
        )
      }
  }
}

// A type error carries no Report, so there is no step count to compare. It
// completed within the fuel guard by definition (FuelExhausted is handled
// separately above), so it is Within -- with a cost this module cannot
// observe, recorded as 0 rather than guessed at.
fn within_or_exceeded(used: Int, policy: GasPolicy) -> GasOutcome {
  case used > policy.max_fuel {
    True -> Exceeded(limit: policy.max_fuel)
    False -> Within(used)
  }
}

/// Whether an outcome left the check unresolved. Deliberately NOT
/// `is_accepted` or `is_rejected`: this is the only predicate over
/// `GasOutcome`, and it separates "we know something" from "we do not",
/// rather than offering a Boolean the caller could read as a verdict.
pub fn is_unresolved(outcome: GasOutcome) -> Bool {
  case outcome {
    Exceeded(_) -> True
    Within(_) -> False
  }
}

/// The steps a completed run performed, or `Error(Nil)` if it did not
/// complete. There is no default and no zero: an `Exceeded` run does not have
/// a step count, and pretending it has one is how an overrun gets recorded as
/// a cheap success.
pub fn steps(outcome: GasOutcome) -> Result(Int, Nil) {
  case outcome {
    Within(n) -> Ok(n)
    Exceeded(_) -> Error(Nil)
  }
}
