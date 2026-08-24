/// Part I: the CLI, exercised through `run/1` rather than a subprocess.
///
/// `run` returns the exit code instead of halting, which is what makes these
/// tests possible at all -- the halting happens in `main`, one line away.
/// These cover argument handling and exit codes; the end-to-end behaviour over
/// a real directory is demo/revocation.sh and demo/admission.sh.
import cronch/cli
import gleeunit/should

// ── usage errors are exit code 2 ──────────────────────────────────────────────

pub fn no_arguments_is_a_usage_error_test() {
  cli.run([]) |> should.equal(2)
}

pub fn help_is_a_usage_error_test() {
  // Deliberately not 0: `--help` with no command did not do the thing the
  // caller wanted, and a script that runs `cronch` with a typo'd command must
  // not see success.
  cli.run(["--help"]) |> should.equal(2)
  cli.run(["-h"]) |> should.equal(2)
  cli.run(["help"]) |> should.equal(2)
}

pub fn an_unknown_command_is_a_usage_error_test() {
  cli.run(["frobnicate"]) |> should.equal(2)
  cli.run(["Check", "x"]) |> should.equal(2)
}

pub fn check_without_emit_receipts_is_a_usage_error_test() {
  cli.run(["check", "nonexistent.cronch"]) |> should.equal(2)
}

pub fn check_with_a_non_numeric_max_fuel_is_a_usage_error_test() {
  // Caught before the file is read, so a bad flag is reported as a bad flag
  // rather than as a missing file.
  cli.run([
    "check", "nonexistent.cronch", "--emit-receipts", "/tmp", "--max-fuel",
    "lots",
  ])
  |> should.equal(2)
}

pub fn check_with_a_negative_max_fuel_is_a_usage_error_test() {
  cli.run([
    "check", "nonexistent.cronch", "--emit-receipts", "/tmp", "--max-fuel", "-1",
  ])
  |> should.equal(2)
}

pub fn a_malformed_rule_set_flag_is_a_usage_error_test() {
  cli.run([
    "check", "nonexistent.cronch", "--emit-receipts", "/tmp", "--rule-set",
    "not-a-spec",
  ])
  |> should.equal(2)
}

pub fn admit_without_declare_is_a_usage_error_test() {
  cli.run(["admit", "nonexistent.cronch"]) |> should.equal(2)
}

pub fn admit_with_a_malformed_declaration_is_a_usage_error_test() {
  cli.run(["admit", "nonexistent.cronch", "--declare", "nonsense"])
  |> should.equal(2)
  cli.run(["admit", "nonexistent.cronch", "--declare", "zz:zz"])
  |> should.equal(2)
}

pub fn revoke_without_a_ledger_is_a_usage_error_test() {
  cli.run(["revoke", "--host", "ed25519:00"]) |> should.equal(2)
}

pub fn revoke_with_no_revocations_is_a_usage_error_test() {
  // Revoking nothing is not the same as revoking everything, and it is not a
  // no-op success either: it is a caller who forgot an argument.
  cli.run(["revoke", "--ledger", "/tmp"]) |> should.equal(2)
}

pub fn revoke_with_a_malformed_key_is_a_usage_error_test() {
  cli.run(["revoke", "--ledger", "/tmp", "--host", "not-hex"])
  |> should.equal(2)
}

pub fn revoke_with_a_malformed_rule_set_is_a_usage_error_test() {
  cli.run(["revoke", "--ledger", "/tmp", "--rule-set", "missing-hash"])
  |> should.equal(2)
}

pub fn audit_without_a_ledger_is_a_usage_error_test() {
  cli.run(["audit"]) |> should.equal(2)
}

// ── missing input is an internal error, not a usage error ─────────────────────

pub fn checking_a_file_that_does_not_exist_is_exit_three_test() {
  // The arguments were well-formed; the environment was not. Distinguishing
  // these is the whole reason there are two codes.
  cli.run([
    "check", "/nonexistent/definitely/not/here.cronch", "--emit-receipts",
    "/tmp/cronch-cli-test-missing",
  ])
  |> should.equal(3)
}

pub fn replaying_a_directory_that_does_not_exist_is_exit_three_test() {
  cli.run(["replay", "/nonexistent/definitely/not/here"]) |> should.equal(3)
}

pub fn auditing_a_directory_that_does_not_exist_is_exit_three_test() {
  cli.run(["audit", "--ledger", "/nonexistent/definitely/not/here"])
  |> should.equal(3)
}

pub fn revoking_against_a_directory_that_does_not_exist_is_exit_three_test() {
  cli.run([
    "revoke", "--ledger", "/nonexistent/definitely/not/here", "--kernel", "x",
  ])
  |> should.equal(3)
}

// ── the kernel identity is local ──────────────────────────────────────────────

pub fn the_cli_declares_its_own_kernel_identity_test() {
  // Never read out of anything being checked: a receipt issued under another
  // kernel produces a different basis digest and fails to replay here, which
  // is the correct answer rather than a bug.
  cli.kernel_id |> should.equal("cronch-kernel/0.1.0")
}
