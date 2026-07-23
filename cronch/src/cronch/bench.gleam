/// Dev-only micro-benchmark runner.
///
/// Run with gleam run -m cronch/bench
///
/// Uses Erlang's `timer:tc/1` (microsecond precision) with a warm-up pass so
/// the BEAM JIT has compiled the hot paths before timing begins.
/// No external dependencies required.
import cronch/digest
import cronch/hash
import cronch/kernel
import cronch/oracle
import cronch/serialize
import cronch/syntax/elab
import cronch/syntax/lex
import cronch/syntax/parse
import cronch/syntax/print
import cronch/term
import gleam/io
import gleam/list
import gleam/option
import gleam/string

// ── FFI timer ─────────────────────────────────────────────────────────────────

/// Erlang timer:tc/1 — runs f(), returns {Microseconds, Result}.
@external(erlang, "timer", "tc")
fn timer_tc(f: fn() -> a) -> #(Int, a)

// ── Harness ───────────────────────────────────────────────────────────────────

fn bench(name: String, n: Int, f: fn() -> a) -> Nil {
  // Warm-up: 10 % of iterations (min 1) so the JIT is hot before timing.
  let warmup = n / 10 + 1
  repeat(warmup, f)
  // Timed run.
  let #(us, _) = timer_tc(fn() { repeat(n, f) })
  let ns_per = us * 1000 / n
  io.println(
    left_pad(name, 44)
    <> "  "
    <> left_pad(int_str(ns_per), 8)
    <> " ns/iter  (n="
    <> int_str(n)
    <> ")",
  )
}

fn section(title: String) -> Nil {
  io.println("")
  io.println(
    "── " <> title <> " " <> string.repeat("─", 54 - string.length(title)),
  )
}

fn repeat(n: Int, f: fn() -> a) -> Nil {
  case n <= 0 {
    True -> Nil
    False -> {
      let _ = f()
      repeat(n - 1, f)
    }
  }
}

// ── Fixtures ──────────────────────────────────────────────────────────────────

fn no_store() -> kernel.Store {
  fn(_) { option.None }
}

fn deep_pi(depth: Int) -> term.Term {
  case depth <= 0 {
    True -> term.Var(0)
    False -> term.Pi(term.Sort(0), deep_pi(depth - 1))
  }
}

const fol_src = "
define id_proof : fun (P : Type 0) -> P -> P :=
  lam (P : Type 0) => lam (p : P) => p
define mp : fun (P : Type 0) -> fun (Q : Type 0) -> (P -> Q) -> P -> Q :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (f : P -> Q) => lam (x : P) => f x
define hs : fun (P : Type 0) -> fun (Q : Type 0) -> fun (R : Type 0) ->
              (P -> Q) -> (Q -> R) -> P -> R :=
  lam (P : Type 0) => lam (Q : Type 0) => lam (R : Type 0) =>
    lam (pq : P -> Q) => lam (qr : Q -> R) => lam (p : P) =>
      qr (pq p)
define weakening : fun (P : Type 0) -> fun (Q : Type 0) -> P -> Q -> P :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (p : P) => lam (q : Q) => p
define perm : fun (P : Type 0) -> fun (Q : Type 0) -> fun (R : Type 0) ->
                (P -> Q -> R) -> Q -> P -> R :=
  lam (P : Type 0) => lam (Q : Type 0) => lam (R : Type 0) =>
    lam (f : P -> Q -> R) => lam (q : Q) => lam (p : P) =>
      f p q
define contraction : fun (P : Type 0) -> fun (Q : Type 0) ->
                       (P -> P -> Q) -> P -> Q :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (f : P -> P -> Q) => lam (p : P) =>
      f p p
define eq_refl : fun (A : Type 0) -> fun (a : A) -> Eq A a a :=
  lam (A : Type 0) => lam (a : A) => refl A a
"

// ── Main ──────────────────────────────────────────────────────────────────────

pub fn main() -> Nil {
  io.println("cronch benchmark suite")
  io.println(string.repeat("═", 62))

  // ── Shared fixtures ────────────────────────────────────────────────────────
  let var0 = term.Var(0)
  let sort0 = term.Sort(0)
  let id_lam = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  let id_type = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  let deep20 = deep_pi(20)
  let beta_redex = term.App(term.Lam(term.Sort(0), term.Var(0)), term.Sort(1))
  let eq_goal = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))

  let enc_var0 = serialize.encode(var0)
  let enc_id_lam = serialize.encode(id_lam)
  let enc_deep20 = serialize.encode(deep20)

  let fol_items = case parse.parse_module(fol_src) {
    Ok(items) -> items
    Error(_) -> {
      io.println("ERROR: failed to parse FOL source")
      []
    }
  }
  let fol_elab_m = case elab.elaborate_module(fol_items) {
    Ok(m) -> m
    Error(_) -> {
      io.println("ERROR: failed to elaborate FOL source")
      elab.ElabModule(
        store: fn(_) { option.None },
        env: gleam_dict_new(),
        entries: [],
      )
    }
  }
  let fol_first_term = case fol_elab_m.entries {
    [e, ..] -> e.term
    [] -> sort0
  }

  // ── 1. Hash ────────────────────────────────────────────────────────────────
  section("hash")
  bench("hash/var0", 500_000, fn() { hash.hash(digest.Blake3, var0) })
  bench("hash/sort0", 500_000, fn() { hash.hash(digest.Blake3, sort0) })
  bench("hash/id_lam", 200_000, fn() { hash.hash(digest.Blake3, id_lam) })
  bench("hash/deep_pi_20", 100_000, fn() { hash.hash(digest.Blake3, deep20) })

  // ── 2. Serialize encode ────────────────────────────────────────────────────
  section("serialize encode")
  bench("encode/var0", 500_000, fn() { serialize.encode(var0) })
  bench("encode/id_lam", 200_000, fn() { serialize.encode(id_lam) })
  bench("encode/deep_pi_20", 100_000, fn() { serialize.encode(deep20) })

  // ── 3. Serialize decode ────────────────────────────────────────────────────
  section("serialize decode")
  bench("decode/var0", 500_000, fn() { serialize.decode(enc_var0) })
  bench("decode/id_lam", 200_000, fn() { serialize.decode(enc_id_lam) })
  bench("decode/deep_pi_20", 100_000, fn() { serialize.decode(enc_deep20) })

  // ── 4. Kernel ──────────────────────────────────────────────────────────────
  let store = no_store()
  let cx = kernel.empty()

  section("kernel")
  bench("kernel.whnf/beta_redex", 200_000, fn() {
    kernel.whnf(store, beta_redex)
  })
  bench("kernel.whnf/id_lam", 200_000, fn() { kernel.whnf(store, id_lam) })
  bench("kernel.def_eq/id_lam=id_lam", 200_000, fn() {
    kernel.def_eq(store, id_lam, id_lam)
  })
  bench("kernel.infer/sort0", 200_000, fn() { kernel.infer(store, cx, sort0) })
  bench("kernel.infer/id_lam", 100_000, fn() { kernel.infer(store, cx, id_lam) })
  bench("kernel.check/id_lam:id_type", 100_000, fn() {
    kernel.check(store, cx, id_lam, id_type)
  })

  // ── 5. Syntax ──────────────────────────────────────────────────────────────
  section("syntax")
  bench("lex/fol_src", 50_000, fn() { lex.lex(fol_src) })
  bench("parse/fol_src", 20_000, fn() { parse.parse_module(fol_src) })
  bench("elab/fol_items", 10_000, fn() { elab.elaborate_module(fol_items) })
  bench("print/id_lam", 200_000, fn() { print.print_term(id_lam) })
  bench("print/fol_first_term", 100_000, fn() {
    print.print_term(fol_first_term)
  })
  bench("round_trip/fol_src", 5000, fn() {
    case parse.parse_module(fol_src) {
      Error(_) -> []
      Ok(items) ->
        case elab.elaborate_module(items) {
          Error(_) -> []
          Ok(m) -> list.map(m.entries, fn(e) { print.print_term(e.term) })
        }
    }
  })

  // ── 6. Oracle ──────────────────────────────────────────────────────────────
  section("oracle")
  bench("oracle.solve/refl_eq", 100_000, fn() {
    oracle.solve(store, oracle.refl_oracle(), eq_goal)
  })
  bench("oracle.solve/stuck_sort0", 100_000, fn() {
    oracle.solve(store, oracle.refl_oracle(), sort0)
  })

  io.println("")
  io.println(string.repeat("═", 62))
  io.println("done")
}

// ── String helpers ────────────────────────────────────────────────────────────

fn left_pad(s: String, width: Int) -> String {
  let pad = width - string.length(s)
  case pad > 0 {
    True -> string.repeat(" ", pad) <> s
    False -> s
  }
}

fn int_str(n: Int) -> String {
  case n < 0 {
    True -> "-" <> int_str(-n)
    False ->
      case n {
        0 -> "0"
        _ -> do_int_str(n, "")
      }
  }
}

fn do_int_str(n: Int, acc: String) -> String {
  case n {
    0 -> acc
    _ -> do_int_str(n / 10, digit_char(n % 10) <> acc)
  }
}

fn digit_char(d: Int) -> String {
  case d {
    0 -> "0"
    1 -> "1"
    2 -> "2"
    3 -> "3"
    4 -> "4"
    5 -> "5"
    6 -> "6"
    7 -> "7"
    8 -> "8"
    _ -> "9"
  }
}

@external(erlang, "maps", "new")
fn gleam_dict_new() -> elab.Env
