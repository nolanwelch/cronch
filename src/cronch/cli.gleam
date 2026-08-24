/// The command line. A thin slice: check, replay, admit, revoke, audit.
///
/// Outside the kernel and outside the TCB. Every decision it reports is made
/// by receipt.gleam, ledger.gleam or capability.gleam; this module parses
/// arguments, reads and writes files, and prints.
///
/// Conventions
/// -----------
///   - Machine-readable on stdout, diagnostic on stderr. Every stdout line is
///     `KEYWORD field field ...`, space-separated, no colours, no spinners, no
///     tables. Anything a person needs but a script does not goes to stderr.
///   - Exit codes: 0 success, 1 negative result (a FAIL, an excess, a
///     rejection), 2 usage error, 3 internal error.
///   - No argument-parsing library, no config file, no interactive mode, no
///     environment-variable fallbacks. Flags are read positionally off a list.
///
/// Store layout
/// ------------
/// A receipt directory is also a ledger directory. Three file kinds, each
/// named by the content address of what it holds:
///
///   <algorithm>-<hex>.receipt   an encoded Receipt
///   <algorithm>-<hex>.term      an encoded Term (artifacts and specs)
///   <algorithm>-<hex>.basis     an encoded Basis
///
/// Terms are written alongside receipts because `replay` recomputes from
/// scratch, and recomputing needs the artifact and its spec, not just their
/// addresses. Bases are written so `revoke --kernel` can see which kernel a
/// receipt was issued under.
import cronch/basis
import cronch/capability
import cronch/digest.{type Digest}
import cronch/hash
import cronch/kernel
import cronch/ledger
import cronch/pubkey.{type PublicKey}
import cronch/receipt.{type Receipt}
import cronch/rewrite.{type Rule}
import cronch/serialize
import cronch/syntax/elab
import cronch/syntax/parse
import cronch/term.{type Term}
import cronch/trust
import gleam/bit_array
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string

/// This kernel's identity, as it appears in every Basis this CLI computes.
/// Local, and never read out of anything being checked.
pub const kernel_id: String = "cronch-kernel/0.1.0"

const default_max_fuel: Int = 1_000_000

// ── Entry point ───────────────────────────────────────────────────────────────

pub fn main() -> Nil {
  case run(argv()) {
    0 -> Nil
    code -> exit_with(code)
  }
}

/// Dispatch. Returns the exit code rather than halting, so it is testable.
pub fn run(args: List(String)) -> Int {
  case args {
    ["check", file, ..rest] -> cmd_check(file, rest)
    ["replay", dir] -> cmd_replay(dir)
    ["admit", file, ..rest] -> cmd_admit(file, rest)
    ["revoke", ..rest] -> cmd_revoke(rest)
    ["audit", ..rest] -> cmd_audit(rest)
    ["--help"] | ["-h"] | ["help"] | [] -> {
      usage()
      2
    }
    [other, ..] -> {
      warn("unknown command: " <> other)
      usage()
      2
    }
  }
}

fn usage() -> Nil {
  warn(
    "usage:
  cronch check <file> --emit-receipts <dir> [--max-fuel N] [--purist]
                      [--rule-set <author-hex>:<file>]...
  cronch replay <dir>
  cronch admit <file> --declare <host-hex>:<proc-hex>,...
  cronch revoke --ledger <dir> (--rule-set <author-hex>:<hash-hex>
                               | --host <key-hex> | --axiom <digest-hex>
                               | --kernel <id>)...
  cronch audit --ledger <dir>

exit codes: 0 success, 1 negative result, 2 usage error, 3 internal error",
  )
}

// ── check ─────────────────────────────────────────────────────────────────────

fn cmd_check(file: String, flags: List(String)) -> Int {
  case flag_value(flags, "--emit-receipts") {
    None -> {
      warn("check: --emit-receipts <dir> is required")
      2
    }
    Some(dir) ->
      case parse_int_flag(flags, "--max-fuel", default_max_fuel) {
        Error(bad) -> {
          warn("check: --max-fuel expects an integer, got " <> bad)
          2
        }
        Ok(max_fuel) ->
          case load_rule_sets(flag_values(flags, "--rule-set")) {
            Error(msg) -> {
              warn("check: " <> msg)
              2
            }
            Ok(rule_sets) ->
              check_module(
                file,
                dir,
                max_fuel,
                rule_sets,
                has(flags, "--purist"),
              )
          }
      }
  }
}

fn check_module(
  file: String,
  dir: String,
  max_fuel: Int,
  rule_sets: List(#(PublicKey, List(Rule))),
  purist: Bool,
) -> Int {
  case load_module(file) {
    Error(code) -> code
    Ok(m) -> {
      let environment = environment_of(m, rule_sets)
      let provenance = provenance_of(rule_sets)
      // The purist policy authorizes nothing. Without --purist no policy is
      // applied at all, and the receipt records the trust set for whoever
      // does apply one -- the CLI does not invent a policy for the user.
      let policy = case purist {
        True -> Some(trust.empty_policy())
        False -> None
      }
      case ensure_dir(dir) {
        Error(Nil) -> {
          warn("check: cannot create directory " <> dir)
          3
        }
        Ok(Nil) -> {
          let checkable =
            list.filter(m.entries, fn(e) { e.kind != elab.HoleKind })
          let results =
            list.map(checkable, fn(entry) {
              let r =
                receipt.issue_with(
                  receipt.default_algorithm,
                  kernel_id,
                  environment,
                  provenance,
                  policy,
                  max_fuel,
                  entry.term,
                  entry.declared_typ,
                )
              #(entry, r)
            })
          case write_results(dir, environment, results) {
            Error(msg) -> {
              warn("check: " <> msg)
              3
            }
            Ok(Nil) -> {
              list.each(results, fn(pair) {
                let #(entry, r) = pair
                io.println(
                  "CHECK "
                  <> entry.name
                  <> " "
                  <> verdict_word(r.verdict)
                  <> " artifact="
                  <> address(r.artifact)
                  <> " receipt="
                  <> address(receipt.digest(receipt.default_algorithm, r))
                  <> " fuel="
                  <> int.to_string(r.fuel_used)
                  <> "/"
                  <> int.to_string(r.fuel_declared),
                )
              })
              let skipped = list.length(m.entries) - list.length(checkable)
              case skipped > 0 {
                True ->
                  warn(
                    int.to_string(skipped)
                    <> " open hole(s) skipped: a hole is not a claim to check",
                  )
                False -> Nil
              }
              // A rejection or an exhaustion is a real receipt and was written
              // out. It is still a negative result, so the exit code says so.
              case
                list.all(results, fn(p) { { p.1 }.verdict == receipt.Accepted })
              {
                True -> 0
                False -> 1
              }
            }
          }
        }
      }
    }
  }
}

fn write_results(
  dir: String,
  environment: kernel.Environment,
  results: List(#(elab.ElabEntry, Receipt)),
) -> Result(Nil, String) {
  list.try_fold(results, Nil, fn(_, pair) {
    let #(entry, r) = pair
    let b =
      basis.from_environment(
        kernel_id,
        environment,
        rule_sets_of(r),
        hosts_of(r),
        entry.term,
      )
    use _ <- result.try(put(
      dir,
      receipt.digest(receipt.default_algorithm, r),
      "receipt",
      receipt.encode(r),
    ))
    use _ <- result.try(put(
      dir,
      r.artifact,
      "term",
      serialize.encode(entry.term),
    ))
    use _ <- result.try(put(
      dir,
      r.spec,
      "term",
      serialize.encode(entry.declared_typ),
    ))
    put(dir, r.basis, "basis", basis.encode(b))
  })
  |> result.replace(Nil)
  |> result.map_error(fn(_) { "cannot write to " <> dir })
}

fn rule_sets_of(r: Receipt) -> List(#(PublicKey, Digest)) {
  list.filter_map(r.trust_set, fn(p) {
    case p {
      trust.RuleSetTrust(a, h) -> Ok(#(a, h))
      trust.HostTrust(_, _) -> Error(Nil)
    }
  })
}

fn hosts_of(r: Receipt) -> List(PublicKey) {
  list.filter_map(r.trust_set, fn(p) {
    case p {
      trust.HostTrust(h, _) -> Ok(h)
      trust.RuleSetTrust(_, _) -> Error(Nil)
    }
  })
}

// ── replay ────────────────────────────────────────────────────────────────────

fn cmd_replay(dir: String) -> Int {
  case load_directory(dir) {
    Error(msg) -> {
      warn("replay: " <> msg)
      3
    }
    Ok(#(receipts, terms, _bases)) ->
      case receipts {
        [] -> {
          warn("replay: no receipts in " <> dir)
          1
        }
        _ -> {
          // The environment is the directory itself: every term it holds,
          // resolved by content address. Nothing else is trusted, and nothing
          // is fetched from anywhere.
          let environment =
            kernel.Environment(
              definitions: store_of(terms),
              signatures: kernel.empty_signatures(),
              rules: kernel.empty_rules(),
            )
          let provenance = fn(_) { [] }
          let outcomes =
            list.map(receipts, fn(r) {
              #(r, receipt.replay(r, kernel_id, environment, provenance))
            })
          list.each(outcomes, fn(o) {
            let #(r, ok) = o
            io.println(
              case ok {
                True -> "PASS "
                False -> "FAIL "
              }
              <> address(receipt.digest(receipt.default_algorithm, r))
              <> " artifact="
              <> address(r.artifact)
              <> " "
              <> verdict_word(r.verdict),
            )
          })
          case list.all(outcomes, fn(o) { o.1 }) {
            True -> 0
            False -> 1
          }
        }
      }
  }
}

// ── admit ─────────────────────────────────────────────────────────────────────

fn cmd_admit(file: String, flags: List(String)) -> Int {
  case flag_value(flags, "--declare") {
    None -> {
      warn("admit: --declare <host-hex>:<proc-hex>,... is required")
      2
    }
    Some(spec) ->
      case parse_declaration(spec) {
        Error(msg) -> {
          warn("admit: " <> msg)
          2
        }
        Ok(declared) ->
          case load_module(file) {
            Error(code) -> code
            Ok(m) -> {
              let environment = environment_of(m, [])
              let outcomes =
                list.map(m.entries, fn(entry) {
                  #(entry, capability.admit(entry.term, environment, declared))
                })
              list.each(outcomes, fn(o) {
                let #(entry, a) = o
                case a {
                  capability.Admitted -> io.println("ADMITTED " <> entry.name)
                  capability.Unresolvable ->
                    io.println(
                      "UNRESOLVABLE "
                      <> entry.name
                      <> " a reference could not be resolved,"
                      <> " so what it reaches is unbounded",
                    )
                  capability.Excess(caps) ->
                    list.each(caps, fn(c) {
                      io.println(
                        "EXCESS "
                        <> entry.name
                        <> " "
                        <> key_address(c.host)
                        <> " "
                        <> c.proc,
                      )
                    })
                }
              })
              case list.all(outcomes, fn(o) { capability.is_admitted(o.1) }) {
                True -> 0
                False -> 1
              }
            }
          }
      }
  }
}

fn parse_declaration(spec: String) -> Result(capability.CapabilitySet, String) {
  // An empty declaration is written as the empty string, and means "this
  // artifact reaches nothing". That is a real, and the strongest, claim.
  case spec {
    "" -> Ok(capability.empty())
    _ ->
      spec
      |> string.split(on: ",")
      |> list.try_map(parse_one_capability)
      |> result.map(capability.from_list)
  }
}

fn parse_one_capability(
  entry: String,
) -> Result(capability.Capability, String) {
  case string.split(entry, on: ":") {
    [host_hex, proc_hex] -> {
      use host <- result.try(
        parse_key(host_hex)
        |> result.replace_error("not a public key: " <> host_hex),
      )
      use proc <- result.try(
        parse_digest(proc_hex)
        |> result.replace_error("not a digest: " <> proc_hex),
      )
      Ok(capability.Capability(host: host, proc: capability.proc_name(proc)))
    }
    _ -> Error("expected <host-hex>:<proc-hex>, got " <> entry)
  }
}

// ── revoke ────────────────────────────────────────────────────────────────────

fn cmd_revoke(flags: List(String)) -> Int {
  case flag_value(flags, "--ledger") {
    None -> {
      warn("revoke: --ledger <dir> is required")
      2
    }
    Some(dir) ->
      case parse_revocations(flags) {
        Error(msg) -> {
          warn("revoke: " <> msg)
          2
        }
        Ok([]) -> {
          warn("revoke: at least one revocation is required")
          2
        }
        Ok(revocations) ->
          case load_ledger(dir) {
            Error(msg) -> {
              warn("revoke: " <> msg)
              3
            }
            Ok(l) -> {
              let radius = ledger.blast_radius(l, revocations)
              let surviving = ledger.survivors(l, revocations)
              let before = ledger.survivors(l, [])
              list.each(radius, fn(d) { io.println("KILLED " <> address(d)) })
              list.each(surviving, fn(d) {
                io.println("SURVIVES " <> address(d))
              })
              let lost = list.length(before) - list.length(surviving)
              io.println(
                int.to_string(lost)
                <> " of "
                <> int.to_string(list.length(before))
                <> " artifacts lose warrant.",
              )
              case lost > 0 {
                True -> 1
                False -> 0
              }
            }
          }
      }
  }
}

fn parse_revocations(
  flags: List(String),
) -> Result(List(ledger.Revocation), String) {
  let rule_sets =
    flag_values(flags, "--rule-set")
    |> list.try_map(fn(v) {
      case string.split(v, on: ":") {
        [author_hex, hash_hex] -> {
          use author <- result.try(
            parse_key(author_hex)
            |> result.replace_error("not a public key: " <> author_hex),
          )
          use h <- result.try(
            parse_digest(hash_hex)
            |> result.replace_error("not a digest: " <> hash_hex),
          )
          Ok(ledger.RevokeRuleSet(author, h))
        }
        _ -> Error("expected <author-hex>:<hash-hex>, got " <> v)
      }
    })
  use rule_sets <- result.try(rule_sets)
  use hosts <- result.try(
    flag_values(flags, "--host")
    |> list.try_map(fn(v) {
      parse_key(v)
      |> result.map(ledger.RevokeHost)
      |> result.replace_error("not a public key: " <> v)
    }),
  )
  use axioms <- result.try(
    flag_values(flags, "--axiom")
    |> list.try_map(fn(v) {
      parse_digest(v)
      |> result.map(ledger.RevokeAxiom)
      |> result.replace_error("not a digest: " <> v)
    }),
  )
  let kernels = list.map(flag_values(flags, "--kernel"), ledger.RevokeKernel)
  Ok(list.flatten([rule_sets, hosts, axioms, kernels]))
}

// ── audit ─────────────────────────────────────────────────────────────────────

fn cmd_audit(flags: List(String)) -> Int {
  case flag_value(flags, "--ledger") {
    None -> {
      warn("audit: --ledger <dir> is required")
      2
    }
    Some(dir) ->
      case load_ledger(dir) {
        Error(msg) -> {
          warn("audit: " <> msg)
          3
        }
        Ok(l) -> {
          let conflicting = ledger.conflicts(l)
          list.each(conflicting, fn(c) {
            let #(artifact, receipts) = c
            io.println(
              "CONFLICT "
              <> address(artifact)
              <> " "
              <> string.join(
                list.map(receipts, fn(r) { verdict_word(r.verdict) }),
                ",",
              )
              <> " under one basis",
            )
          })
          let unwarranted = ledger.without_accepted_verdict(l)
          list.each(unwarranted, fn(d) {
            io.println("NO-ACCEPTED-VERDICT " <> address(d))
          })
          io.println(
            int.to_string(list.length(ledger.artifacts(l)))
            <> " artifacts, "
            <> int.to_string(list.length(ledger.survivors(l, [])))
            <> " with warrant, "
            <> int.to_string(list.length(conflicting))
            <> " conflicts.",
          )
          case conflicting == [] && unwarranted == [] {
            True -> 0
            False -> 1
          }
        }
      }
  }
}

// ── Loading ───────────────────────────────────────────────────────────────────

fn load_module(file: String) -> Result(elab.ElabModule, Int) {
  case read_file(file) {
    Error(Nil) -> {
      warn("cannot read " <> file)
      Error(3)
    }
    Ok(bytes) ->
      case bit_array.to_string(bytes) {
        Error(Nil) -> {
          warn(file <> " is not valid UTF-8")
          Error(2)
        }
        Ok(src) ->
          case parse.parse_module(src) {
            Error(parse.ParseError(msg)) -> {
              warn("parse error in " <> file <> ": " <> msg)
              Error(2)
            }
            Ok(items) ->
              case elab.elaborate_module(items) {
                Error(e) -> {
                  warn("elaboration error in " <> file <> ": " <> elab_error(e))
                  Error(2)
                }
                Ok(m) -> Ok(m)
              }
          }
      }
  }
}

fn elab_error(e: elab.ElabError) -> String {
  case e {
    elab.UnboundName(n) -> "unbound name `" <> n <> "`"
    elab.TrustedInProofPosition -> "trusted in proof position"
    elab.UnboundProc(n) -> "unbound proc `" <> n <> "`"
    elab.DuplicateName(n) -> "duplicate name `" <> n <> "`"
  }
}

fn environment_of(
  m: elab.ElabModule,
  rule_sets: List(#(PublicKey, List(Rule))),
) -> kernel.Environment {
  kernel.Environment(
    definitions: m.store,
    signatures: kernel.empty_signatures(),
    rules: rule_store(list.flat_map(rule_sets, fn(rs) { rs.1 })),
  )
}

fn provenance_of(
  rule_sets: List(#(PublicKey, List(Rule))),
) -> kernel.Provenance {
  let tagged =
    list.flat_map(rule_sets, fn(rs) {
      let #(author, rules) = rs
      let h = hash.hash_rule_set(receipt.default_algorithm, rules)
      let tag = kernel.RuleUse(author: author, rule_set: h)
      list.filter_map(rules, fn(r) {
        case head_digest(r.lhs) {
          Some(d) -> Ok(#(d, #(tag, r)))
          None -> Error(Nil)
        }
      })
    })
  fn(d) {
    tagged
    |> list.filter(fn(e) { e.0 == d })
    |> list.map(fn(e) { e.1 })
  }
}

fn rule_store(rules: List(Rule)) -> kernel.RuleStore {
  let keyed =
    list.filter_map(rules, fn(r) {
      case head_digest(r.lhs) {
        Some(d) -> Ok(#(d, r))
        None -> Error(Nil)
      }
    })
  fn(d) {
    keyed
    |> list.filter(fn(e) { e.0 == d })
    |> list.map(fn(e) { e.1 })
  }
}

// The Const at the head of a pattern's application spine. A rule whose lhs is
// not headed by a Const can never fire (whnf keys rules by head Const), so it
// is dropped rather than silently keyed to something arbitrary.
fn head_digest(p: rewrite.Pattern) -> Option(Digest) {
  case p {
    rewrite.PConst(d) -> Some(d)
    rewrite.PApp(f, _) -> head_digest(f)
    _ -> None
  }
}

fn load_rule_sets(
  specs: List(String),
) -> Result(List(#(PublicKey, List(Rule))), String) {
  list.try_map(specs, fn(spec) {
    case string.split(spec, on: ":") {
      [author_hex, path] -> {
        use author <- result.try(
          parse_key(author_hex)
          |> result.replace_error("not a public key: " <> author_hex),
        )
        use bytes <- result.try(
          read_file(path) |> result.replace_error("cannot read " <> path),
        )
        use rules <- result.try(
          serialize.decode_rule_set(bytes)
          |> result.replace_error("not a canonical rule set: " <> path),
        )
        Ok(#(author, rules))
      }
      _ -> Error("expected <author-hex>:<file>, got " <> spec)
    }
  })
}

/// Read every receipt, term and basis in a directory.
///
/// A file that does not decode is a hard failure, not a skip: a directory
/// half of which is unreadable is not a ledger, and quietly ignoring the
/// unreadable half is how "no conflicts found" comes to mean nothing.
fn load_directory(
  dir: String,
) -> Result(#(List(Receipt), List(#(Digest, Term)), List(basis.Basis)), String) {
  use names <- result.try(
    list_dir(dir) |> result.replace_error("cannot list " <> dir),
  )
  use receipts <- result.try(
    names
    |> list.filter(fn(n) { string.ends_with(n, ".receipt") })
    |> list.try_map(fn(n) {
      use bytes <- result.try(
        read_file(dir <> "/" <> n)
        |> result.replace_error("cannot read " <> n),
      )
      receipt.decode(bytes)
      |> result.replace_error("not a canonical receipt: " <> n)
    }),
  )
  use terms <- result.try(
    names
    |> list.filter(fn(n) { string.ends_with(n, ".term") })
    |> list.try_map(fn(n) {
      use bytes <- result.try(
        read_file(dir <> "/" <> n)
        |> result.replace_error("cannot read " <> n),
      )
      use t <- result.try(
        serialize.decode(bytes)
        |> result.replace_error("not a canonical term: " <> n),
      )
      // The address is recomputed from the bytes rather than taken from the
      // filename. A file named after one thing and containing another must
      // not resolve as either.
      Ok(#(hash.hash(receipt.default_algorithm, t), t))
    }),
  )
  use bases <- result.try(
    names
    |> list.filter(fn(n) { string.ends_with(n, ".basis") })
    |> list.try_map(fn(n) {
      use bytes <- result.try(
        read_file(dir <> "/" <> n)
        |> result.replace_error("cannot read " <> n),
      )
      basis.decode(bytes)
      |> result.replace_error("not a canonical basis: " <> n)
    }),
  )
  Ok(#(receipts, terms, bases))
}

fn load_ledger(dir: String) -> Result(ledger.Ledger, String) {
  use #(receipts, _terms, bases) <- result.try(load_directory(dir))
  let l = list.fold(receipts, ledger.new(), ledger.add)
  Ok(list.fold(bases, l, ledger.add_basis))
}

fn store_of(terms: List(#(Digest, Term))) -> kernel.Store {
  fn(d) {
    case list.find(terms, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> None
    }
  }
}

fn put(
  dir: String,
  d: Digest,
  extension: String,
  bytes: BitArray,
) -> Result(Nil, String) {
  write_file(dir <> "/" <> filename(d) <> "." <> extension, bytes)
  |> result.replace_error("cannot write " <> filename(d))
}

// ── Formatting and parsing ────────────────────────────────────────────────────

/// The self-describing address, as `hash.address_of` renders it.
fn address(d: Digest) -> String {
  hash.address_of(d)
}

fn key_address(k: PublicKey) -> String {
  let pubkey.PublicKey(scheme, bytes) = k
  pubkey.scheme_name(scheme) <> ":" <> lower_hex(bytes)
}

// A filename form of an address: the same content, with the colon replaced so
// the name is uncontroversial on every filesystem.
fn filename(d: Digest) -> String {
  string.replace(address(d), each: ":", with: "-")
}

fn lower_hex(b: BitArray) -> String {
  b |> bit_array.base16_encode |> string.lowercase
}

fn parse_digest(hex: String) -> Result(Digest, Nil) {
  // Accept both the bare hex and the full self-describing address, so output
  // from one command can be pasted straight into another.
  case string.contains(hex, ":") {
    True -> hash.parse_address(hex)
    False -> hash.parse_address("blake3:" <> hex)
  }
}

fn parse_key(hex: String) -> Result(PublicKey, Nil) {
  let #(scheme_name, body) = case string.split_once(hex, on: ":") {
    Ok(#(s, b)) -> #(s, b)
    Error(Nil) -> #("ed25519", hex)
  }
  use scheme <- result.try(
    list.find(pubkey.all_schemes(), fn(s) {
      pubkey.scheme_name(s) == scheme_name
    })
    |> result.replace_error(Nil),
  )
  use bytes <- result.try(body |> string.uppercase |> bit_array.base16_decode)
  case bit_array.byte_size(bytes) == pubkey.key_size(scheme) {
    True -> Ok(pubkey.PublicKey(scheme, bytes))
    False -> Error(Nil)
  }
}

fn verdict_word(v: receipt.Verdict) -> String {
  case v {
    receipt.Accepted -> "ACCEPTED"
    receipt.Exhausted -> "EXHAUSTED"
    receipt.Rejected(reason) -> "REJECTED(" <> reason_word(reason) <> ")"
  }
}

fn reason_word(r: receipt.RejectReason) -> String {
  case r {
    receipt.TypeMismatch -> "TypeMismatch"
    receipt.UnboundVariable -> "UnboundVariable"
    receipt.NotAFunction -> "NotAFunction"
    receipt.SortError -> "SortError"
    receipt.IllFormedTerm -> "IllFormedTerm"
    receipt.UnknownConstant -> "UnknownConstant"
    receipt.UnauthorizedRuleSet -> "UnauthorizedRuleSet"
    receipt.UnauthorizedHost -> "UnauthorizedHost"
    receipt.CapabilityExceeded -> "CapabilityExceeded"
    receipt.MalformedRule -> "MalformedRule"
  }
}

// ── Flags ─────────────────────────────────────────────────────────────────────
//
// Positional, hand-rolled, and about twenty lines. A flag is a token starting
// with `--`; its value is the token after it. Repeated flags accumulate.

fn has(flags: List(String), name: String) -> Bool {
  list.contains(flags, name)
}

fn flag_value(flags: List(String), name: String) -> Option(String) {
  case flag_values(flags, name) {
    [v, ..] -> Some(v)
    [] -> None
  }
}

fn flag_values(flags: List(String), name: String) -> List(String) {
  case flags {
    [f, v, ..rest] if f == name -> [v, ..flag_values(rest, name)]
    [_, ..rest] -> flag_values(rest, name)
    [] -> []
  }
}

fn parse_int_flag(
  flags: List(String),
  name: String,
  fallback: Int,
) -> Result(Int, String) {
  case flag_value(flags, name) {
    None -> Ok(fallback)
    Some(v) ->
      case int.parse(v) {
        Ok(n) if n >= 0 -> Ok(n)
        _ -> Error(v)
      }
  }
}

// ── FFI ───────────────────────────────────────────────────────────────────────

@external(erlang, "cronch_cli_ffi", "argv")
fn argv() -> List(String)

@external(erlang, "cronch_cli_ffi", "read_file")
fn read_file(path: String) -> Result(BitArray, Nil)

@external(erlang, "cronch_cli_ffi", "write_file")
fn write_file(path: String, bytes: BitArray) -> Result(Nil, Nil)

@external(erlang, "cronch_cli_ffi", "list_dir")
fn list_dir(path: String) -> Result(List(String), Nil)

@external(erlang, "cronch_cli_ffi", "ensure_dir")
fn ensure_dir(path: String) -> Result(Nil, Nil)

@external(erlang, "cronch_cli_ffi", "print_error")
fn warn(text: String) -> Nil

@external(erlang, "cronch_cli_ffi", "exit_with")
fn exit_with(code: Int) -> Nil
