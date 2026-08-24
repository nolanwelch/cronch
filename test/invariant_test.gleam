/// Part J: the invariants that guard the thesis.
///
/// These are not tests of a function. They are tests of the claims the whole
/// design rests on -- that the audit surface stays small, that it stays
/// isolated, that recording never decides, and that a receipt is the same
/// bytes wherever it is computed. Each of those is a habit unless something
/// fails when it lapses.
import cronch/kernel
import cronch/receipt
import cronch/trust
import gleam/int
import gleam/list
import gleam/string
import gleeunit/should
import support/corpus
import support/determinism

// ── J1: the TCB budget ────────────────────────────────────────────────────────

/// The maximum number of lines cronch/kernel.gleam may contain.
///
/// Measured after this PR (1092) plus ten percent. The kernel is the audit
/// surface: it has to stay readable in one sitting, and "small enough to
/// audit" is a property somebody has to be able to check rather than a habit
/// somebody has to remember.
///
/// RAISING THIS CONSTANT REQUIRES JUSTIFICATION IN THE PULL REQUEST
/// DESCRIPTION. Not a note in the commit message, not a comment here: the
/// description, where a reviewer will see it. Every line added to the kernel
/// is a line somebody has to read before trusting anything this system says,
/// and the budget exists so that adding them is a decision rather than a
/// drift.
const kernel_line_budget: Int = 1201

const kernel_path: String = "src/cronch/kernel.gleam"

fn kernel_source() -> String {
  case read_source(kernel_path) {
    Ok(text) -> text
    // A test that cannot find the kernel must fail, never quietly measure
    // nothing and pass.
    Error(Nil) -> panic as "cannot read src/cronch/kernel.gleam"
  }
}

fn line_count(text: String) -> Int {
  list.length(string.split(text, on: "\n")) - 1
}

pub fn j1_the_kernel_stays_within_its_line_budget_test() {
  let lines = line_count(kernel_source())
  case lines <= kernel_line_budget {
    True -> Nil
    False ->
      panic as {
        "kernel.gleam is "
        <> int.to_string(lines)
        <> " lines, over the budget of "
        <> int.to_string(kernel_line_budget)
        <> " -- raising the budget requires justification in the PR description"
      }
  }
}

pub fn j1_the_budget_is_not_absurdly_slack_test() {
  // A budget nothing could ever exceed is not a budget. If the kernel shrinks
  // a lot, the constant should come down with it rather than sitting there as
  // decoration.
  let lines = line_count(kernel_source())
  { kernel_line_budget < lines * 2 } |> should.be_true
}

// ── J2: no TCB imports ────────────────────────────────────────────────────────

/// Modules the kernel must never import. Every one is bookkeeping,
/// serialization of a new artifact kind, policy, ledger logic, or CLI -- and
/// none of those belongs in the audit surface. An import here would drag the
/// imported module into the TCB whether or not anybody meant it to.
const forbidden_imports: List(String) = [
  "cronch/basis", "cronch/receipt", "cronch/ledger", "cronch/capability",
  "cronch/cli", "cronch/gas", "cronch/trust", "cronch/oracle",
  "cronch/serialize", "cronch/hash", "cronch/canonical",
]

pub fn j2_the_kernel_imports_none_of_the_new_modules_test() {
  let source = kernel_source()
  list.each(forbidden_imports, fn(module) {
    case string.contains(source, "import " <> module) {
      False -> Nil
      True -> panic as { "kernel.gleam imports " <> module }
    }
  })
}

pub fn j2_the_kernel_imports_only_what_it_has_always_imported_test() {
  // The complement of the test above, stated positively: an import that is
  // neither on this list nor caught above still fails, so a new dependency
  // cannot slip in under a name nobody thought to forbid.
  let allowed = [
    "cronch/digest", "cronch/pubkey", "cronch/rewrite", "cronch/term",
    "gleam/dict", "gleam/int", "gleam/list", "gleam/option", "gleam/result",
  ]
  kernel_source()
  |> string.split(on: "\n")
  |> list.filter(fn(line) { string.starts_with(line, "import ") })
  |> list.each(fn(line) {
    let module =
      line
      |> string.drop_start(7)
      |> string.split(on: ".")
      |> list.first
      |> fn(r) {
        case r {
          Ok(m) -> string.trim(m)
          Error(Nil) -> ""
        }
      }
    case list.contains(allowed, module) {
      True -> Nil
      False ->
        panic as {
          "kernel.gleam has a new import: "
          <> module
          <> " -- adding one grows the trusted computing base"
        }
    }
  })
}

// ── J3: recording is not deciding ─────────────────────────────────────────────

pub fn j3_the_plain_checker_and_the_receipt_agree_for_every_corpus_term_test() {
  // The plain checker knows nothing about receipts, bases, trust sets or gas.
  // If issuing a receipt ever moved a verdict, everything else in this PR
  // would be worthless -- an audit record that changes what it audits is not a
  // record.
  list.each(corpus.cases(), fn(c) {
    let plain =
      kernel.check(
        c.environment,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    let recorded =
      receipt.issue(
        determinism.kernel_id,
        c.environment,
        c.provenance,
        determinism.budget,
        c.term,
        c.typ,
      )
    case plain, recorded.verdict {
      Ok(_), receipt.Accepted -> Nil
      Error(kernel.FuelExhausted), receipt.Exhausted -> Nil
      Error(e), receipt.Rejected(reason) ->
        reason |> should.equal(receipt.reason_of(e))
      _, _ ->
        panic as {
          "verdict disagreement on "
          <> c.name
          <> ": recording changed a decision"
        }
    }
  })
}

pub fn j3_a_policy_gated_receipt_never_accepts_what_the_checker_rejects_test() {
  // A policy can only ever turn an acceptance into a refusal. There is no
  // policy anywhere that turns a rejection into an acceptance, and this is
  // where that would show.
  list.each(corpus.cases(), fn(c) {
    let plain =
      kernel.check(
        c.environment,
        kernel.test_fuel,
        kernel.empty(),
        c.term,
        c.typ,
      )
    let gated =
      receipt.issue_under_policy(
        determinism.kernel_id,
        c.environment,
        c.provenance,
        trust.empty_policy(),
        determinism.budget,
        c.term,
        c.typ,
      )
    case plain, gated.verdict {
      Error(_), receipt.Accepted ->
        panic as { "policy gating accepted a rejected term: " <> c.name }
      _, _ -> Nil
    }
  })
}

pub fn j3_the_trust_set_never_changes_a_verdict_test() {
  // Computing the trust set is observation. Running the check with reporting
  // on and reporting off must reach the same place.
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
      _, _ -> panic as { "reporting changed a decision on " <> c.name }
    }
  })
}

// ── J4: cross-process determinism ─────────────────────────────────────────────

pub fn j4_receipts_are_byte_identical_in_a_fresh_os_process_test() {
  // A second BEAM: its own scheduler, its own heap, its own module table, its
  // own process identifiers, its own hash seeds. Anything that leaked a
  // timestamp, a PID, a counter or a map iteration order into a receipt
  // produces different bytes there, and this is where it surfaces.
  let here = determinism.receipts_hex()
  { string.length(here) > 0 } |> should.be_true

  let there =
    os_run(
      "erl -pa build/dev/erlang/*/ebin -noshell"
      <> " -eval 'io:format(\"~s\",[support@determinism:receipts_hex()]), halt().'",
    )
    |> string.trim

  // A missing or broken second BEAM must fail the test, not pass it by
  // comparing two empty strings.
  { string.length(there) > 0 } |> should.be_true
  there |> should.equal(here)
}

pub fn j4_receipts_are_byte_identical_across_repeated_runs_here_test() {
  // The same-process half, so a failure above can be attributed to the
  // process boundary rather than to plain nondeterminism.
  let first = determinism.receipts_hex()
  list.each(list.repeat(Nil, 5), fn(_) {
    determinism.receipts_hex() |> should.equal(first)
  })
}

pub fn j4_two_fresh_os_processes_agree_with_each_other_test() {
  let run = fn() {
    os_run(
      "erl -pa build/dev/erlang/*/ebin -noshell"
      <> " -eval 'io:format(\"~s\",[support@determinism:receipts_hex()]), halt().'",
    )
    |> string.trim
  }
  let a = run()
  let b = run()
  { string.length(a) > 0 } |> should.be_true
  a |> should.equal(b)
}

// ── FFI ───────────────────────────────────────────────────────────────────────

@external(erlang, "cronch_inspect_ffi", "read_source")
fn read_source(path: String) -> Result(String, Nil)

@external(erlang, "cronch_inspect_ffi", "os_run")
fn os_run(command: String) -> String
