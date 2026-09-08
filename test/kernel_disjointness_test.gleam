/// definitions and rules must be disjoint.
///
/// `kernel.Environment` documents the precondition and declines to check it
/// on the resolution path; this is the regression test that says why it
/// matters, plus coverage of `kernel.definition_rule_conflicts`, the check a
/// builder is supposed to run instead.
import cronch/digest
import cronch/kernel
import cronch/rewrite
import cronch/term
import gleam/option.{None, Some}
import gleeunit/should

fn fake_digest(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

// A digest that is BOTH a definition and a rule head -- a violation of the
// Environment precondition, and the whole point of this module.
//
//   A : an ordinary axiom, `A : Type 0`
//   W : the rule `W --> Type 0`, and (when present) the definition
//       `W := Type 1`
//
// `check A W` asks whether `A`'s type is convertible with `W`. `A`'s type is
// `Type 0`, so the answer is entirely determined by what `W` reduces to --
// the definition if there is one, the rule if there is not. `W` is never
// inferred, only reduced, so withholding its body does not make anything
// unresolvable: the conversion check simply routes to the rule instead.
fn conflicting_env(
  with_definition: Bool,
) -> #(kernel.Environment, List(digest.Digest)) {
  let a = fake_digest(0xA0)
  let w = fake_digest(0x11)
  let rule =
    rewrite.Rule(lhs: rewrite.PConst(w), rhs: term.Sort(0), var_count: 0)
  #(
    kernel.Environment(
      definitions: fn(d) {
        case with_definition && d == w {
          True -> Some(term.Sort(1))
          False -> None
        }
      },
      signatures: fn(d) {
        case d == a {
          True -> Some(term.Sort(0))
          False -> None
        }
      },
      rules: fn(d) {
        case d == w {
          True -> [rule]
          False -> []
        }
      },
    ),
    [a, w],
  )
}

pub fn withholding_a_conflicting_definition_flips_reject_to_accept_test() {
  let #(with_def, keys) = conflicting_env(True)
  let #(without_def, _) = conflicting_env(False)
  let assert [a, w] = keys
  let artifact = term.Const(a)
  let declared = term.Const(w)

  // With the definition present, `W` delta-unfolds to `Type 1` and the rule
  // keyed to `W` never gets a chance to fire: REJECTED.
  kernel.check(with_def, kernel.test_fuel, kernel.empty(), artifact, declared)
  |> should.equal(
    Error(kernel.Mismatch(expected: declared, actual: term.Sort(0))),
  )

  // Withhold exactly that definition and nothing else. Now `W` resolves
  // through the rule to `Type 0`: ACCEPTED. Same artifact, same declared
  // type, same rules -- and the verdict is a function of whether one
  // redundant description of what `W` means happened to be installed.
  kernel.check(
    without_def,
    kernel.test_fuel,
    kernel.empty(),
    artifact,
    declared,
  )
  |> should.equal(Ok(Nil))
}

pub fn the_flip_is_the_delta_step_not_the_missing_body_test() {
  // Why the flip happens, pinned one level down so a future reader does not
  // have to reconstruct it: whnf of `W` under the conflicting environment
  // unfolds the body and stops, never trying the rule.
  let #(with_def, keys) = conflicting_env(True)
  let #(without_def, _) = conflicting_env(False)
  let assert [_, w] = keys

  kernel.whnf(with_def, kernel.test_fuel, term.Const(w))
  |> should.equal(Ok(term.Sort(1)))

  kernel.whnf(without_def, kernel.test_fuel, term.Const(w))
  |> should.equal(Ok(term.Sort(0)))
}

pub fn the_conflict_is_exactly_what_the_checker_reports_test() {
  let #(with_def, keys) = conflicting_env(True)
  let #(without_def, _) = conflicting_env(False)
  let assert [_, w] = keys

  // The environment that flips the verdict is the one that violates the
  // precondition, and `definition_rule_conflicts` names the digest.
  kernel.definition_rule_conflicts(with_def, keys) |> should.equal([w])

  // The honest environment has nothing to report.
  kernel.definition_rule_conflicts(without_def, keys) |> should.equal([])
}

pub fn definition_rule_conflicts_ignores_the_innocent_test() {
  // A digest with only rules, or only a body, is no conflict. And a
  // candidate list that omits the offending digest reports nothing: this is
  // a builder's check over keys it knows it installed, not a discovery
  // mechanism, because an Environment cannot be enumerated.
  let #(with_def, keys) = conflicting_env(True)
  let assert [a, _] = keys
  kernel.definition_rule_conflicts(with_def, [a]) |> should.equal([])
  kernel.definition_rule_conflicts(with_def, []) |> should.equal([])

  let only_a_body =
    kernel.environment_from_store(fn(d) {
      case d == fake_digest(0x01) {
        True -> Some(term.Sort(0))
        False -> None
      }
    })
  kernel.definition_rule_conflicts(only_a_body, [fake_digest(0x01)])
  |> should.equal([])
}
