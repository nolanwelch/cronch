/// The reporting path takes its rules from the Environment, never the caller.
///
/// `try_rewrite` matches against whatever rule list it is handed, so whichever
/// function supplies that list IS the rule source. Before this, the reporting
/// entry points handed it the caller's `Provenance` directly: a caller could
/// have the verdict computed under rules of its own choosing while the
/// receipt's Basis recorded the Environment's. These tests pin the fix, and
/// pin that the rules involved really are verdict-changing so the tests
/// cannot pass vacuously.
import cronch/digest
import cronch/kernel
import cronch/pubkey
import cronch/rewrite
import cronch/term
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

fn fake_digest(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

fn author() -> pubkey.PublicKey {
  let b = 0x7A
  pubkey.PublicKey(pubkey.Ed25519, <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>)
}

fn w() -> digest.Digest {
  fake_digest(0x77)
}

fn s() -> digest.Digest {
  fake_digest(0x55)
}

fn tag() -> kernel.RuleUse {
  kernel.RuleUse(author: author(), rule_set: fake_digest(0x99))
}

// `W --> Type 0`. Nothing in the artifact's normal form mentions `W`: the
// rule fires only while establishing that a binder's domain annotation
// denotes a type, which is the interesting case for reporting.
fn w_rule() -> rewrite.Rule {
  rewrite.Rule(lhs: rewrite.PConst(w()), rhs: term.Sort(0), var_count: 0)
}

// `S : W` and `W : Type 1`, both axioms. `W` is a sort ONLY if the rule
// fires, so `lam (x : S) => x` typechecks against `S -> S` exactly when the
// rule is in play and not otherwise.
fn env(with_rule: Bool) -> kernel.Environment {
  kernel.Environment(
    definitions: kernel.no_store(),
    signatures: fn(d) {
      case d == s(), d == w() {
        True, _ -> Some(term.Const(w()))
        _, True -> Some(term.Sort(1))
        _, _ -> None
      }
    },
    rules: fn(d) {
      case with_rule && d == w() {
        True -> [w_rule()]
        False -> []
      }
    },
  )
}

fn artifact() -> term.Term {
  term.Lam(term.Const(s()), term.Var(0))
}

fn declared() -> term.Term {
  term.Pi(term.Const(s()), term.Const(s()))
}

// Attributes every rule the environment actually holds -- what an honest
// caller passes.
fn honest_provenance(environment: kernel.Environment) -> kernel.Provenance {
  fn(d) { list.map(environment.rules(d), fn(r) { #(tag(), r) }) }
}

// Offers `W --> Type 0` whether or not the environment has it.
fn injecting_provenance() -> kernel.Provenance {
  fn(d) {
    case d == w() {
      True -> [#(tag(), w_rule())]
      False -> []
    }
  }
}

pub fn the_rule_in_question_really_does_decide_the_verdict_test() {
  // Without this, every test below could pass for the boring reason that the
  // rule never mattered.
  kernel.check(
    env(True),
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.be_ok

  kernel.check(
    env(False),
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.equal(Error(kernel.ExpectedSort(term.Const(w()))))
}

pub fn a_caller_supplied_rule_cannot_change_a_verdict_test() {
  // THE FIX. The environment holds no rules; the caller offers the one rule
  // that would make the check succeed. The reporting path used to reduce
  // under it and return Ok -- an acceptance available only to whoever was
  // holding the reporting entry point. Now the reporting verdict is the plain
  // verdict.
  let environment = env(False)
  let reported =
    kernel.check_reporting(
      environment,
      injecting_provenance(),
      kernel.test_fuel,
      kernel.empty(),
      artifact(),
      declared(),
    )
  reported |> should.equal(Error(kernel.ExpectedSort(term.Const(w()))))

  // Stated as the general property rather than as one error value: the
  // reporting verdict IS the plain verdict, whatever the caller passes.
  let plain =
    kernel.check(
      environment,
      kernel.test_fuel,
      kernel.empty(),
      artifact(),
      declared(),
    )
  case reported, plain {
    Error(a), Error(b) -> a |> should.equal(b)
    _, _ -> panic as "a caller's rules moved the reporting verdict"
  }
}

pub fn infer_reporting_takes_its_rules_from_the_environment_too_test() {
  kernel.infer_reporting(
    env(False),
    injecting_provenance(),
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
  )
  |> should.equal(Error(kernel.ExpectedSort(term.Const(w()))))

  // And with the rule genuinely installed, the same call succeeds and names
  // the rule set: the fix removed a caller's rules, not the reporting.
  let environment = env(True)
  kernel.infer_reporting(
    environment,
    honest_provenance(environment),
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
  )
  |> should.equal(
    Ok(#(declared(), kernel.Report(rule_uses: [tag()], fuel_used: 1))),
  )
}

pub fn an_environment_rule_still_gets_attributed_test() {
  // The honest path is unchanged: rules come from the Environment, the tag
  // comes from the Provenance, and the Report names the rule set the
  // acceptance rested on.
  let environment = env(True)
  kernel.check_reporting(
    environment,
    honest_provenance(environment),
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.equal(Ok(kernel.Report(rule_uses: [tag()], fuel_used: 1)))
}

pub fn a_rule_the_caller_declines_to_attribute_fails_closed_test() {
  // The other direction of the same hole: the caller cannot shrink the
  // reported trust set either. The environment's rule fires (the verdict does
  // not depend on who is listening), but a Report that omitted it would be a
  // policy bypass -- an artifact whose acceptance rested on a rule set,
  // recorded as resting on none. So there is no Report at all.
  let environment = env(True)

  // Plain `check` accepts...
  kernel.check(
    environment,
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.be_ok

  // ...and asking for a report while attributing nothing is an error, not an
  // acceptance with an empty rule_uses list.
  kernel.check_reporting(
    environment,
    fn(_) { [] },
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.equal(Error(kernel.Unresolved(w())))

  // Same for a Provenance that attributes some other rule for that digest:
  // agreement is by rule, not by digest.
  let other_rule =
    rewrite.Rule(lhs: rewrite.PConst(w()), rhs: term.Sort(1), var_count: 0)
  kernel.check_reporting(
    environment,
    fn(d) {
      case d == w() {
        True -> [#(tag(), other_rule)]
        False -> []
      }
    },
    kernel.test_fuel,
    kernel.empty(),
    artifact(),
    declared(),
  )
  |> should.equal(Error(kernel.Unresolved(w())))
}
