import cronch/digest
import cronch/pubkey
import cronch/syntax/elab
import cronch/syntax/lex
import cronch/syntax/parse
import cronch/syntax/print
import cronch/term
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

// ── Helpers ───────────────────────────────────────────────────────────────────

fn zero_bytes32() -> BitArray {
  <<
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  >>
}

fn ab_bytes32() -> BitArray {
  <<
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
    0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab, 0xab,
  >>
}

fn b1_bytes32() -> BitArray {
  <<
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  >>
}

fn b2_bytes32() -> BitArray {
  <<
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  >>
}

fn zero_digest() -> digest.Digest {
  digest.Digest(digest.Blake3, zero_bytes32())
}

fn ab_digest() -> digest.Digest {
  digest.Digest(digest.Blake3, ab_bytes32())
}

// ── Lexer tests ───────────────────────────────────────────────────────────────

pub fn lex_punctuation_and_words_test() {
  let toks =
    lex.lex("fun (x : A) -> B := lam y => z -- comment\n")
    |> should.be_ok
  toks
  |> should.equal([
    lex.Word("fun"),
    lex.LParen,
    lex.Word("x"),
    lex.Colon,
    lex.Word("A"),
    lex.RParen,
    lex.Arrow,
    lex.Word("B"),
    lex.ColonEq,
    lex.Word("lam"),
    lex.Word("y"),
    lex.FatArrow,
    lex.Word("z"),
  ])
}

pub fn lex_colon_eq_beats_colon_test() {
  lex.lex(":=") |> should.be_ok |> should.equal([lex.ColonEq])
  lex.lex(":") |> should.be_ok |> should.equal([lex.Colon])
}

pub fn lex_rejects_illegal_char_test() {
  lex.lex("a & b") |> should.be_error
}

pub fn lex_comment_skipped_test() {
  lex.lex("a -- ignored\nb")
  |> should.be_ok
  |> should.equal([lex.Word("a"), lex.Word("b")])
}

pub fn lex_is_hex32_test() {
  lex.is_hex32("ab" |> string_repeat(32)) |> should.be_true
  lex.is_hex32("ab" |> string_repeat(31)) |> should.be_false
  lex.is_hex32("gg" |> string_repeat(32)) |> should.be_false
  lex.is_hex32("0123456789abcdef" |> string_repeat(4)) |> should.be_true
}

fn string_repeat(s: String, n: Int) -> String {
  case n <= 0 {
    True -> ""
    False -> s <> string_repeat(s, n - 1)
  }
}

// ── Parser tests ──────────────────────────────────────────────────────────────

pub fn parse_pi_and_lam_test() {
  let e = parse.parse_expr("fun (x : Type 0) -> x") |> should.be_ok
  e |> should.equal(parse.EPi("x", parse.ESort(0), parse.EName("x")))
}

pub fn parse_lam_test() {
  let e = parse.parse_expr("lam (x : Type 0) => x") |> should.be_ok
  e |> should.equal(parse.ELam("x", parse.ESort(0), parse.EName("x")))
}

pub fn parse_app_left_assoc_test() {
  let e = parse.parse_expr("f x y") |> should.be_ok
  let expected =
    parse.EApp(
      parse.EApp(parse.EName("f"), parse.EName("x")),
      parse.EName("y"),
    )
  e |> should.equal(expected)
}

pub fn parse_arrow_right_assoc_test() {
  let e = parse.parse_expr("A -> B -> C") |> should.be_ok
  let expected =
    parse.EArrow(
      parse.EName("A"),
      parse.EArrow(parse.EName("B"), parse.EName("C")),
    )
  e |> should.equal(expected)
}

pub fn parse_eq_refl_test() {
  parse.parse_expr("Eq A a b")
  |> should.be_ok
  |> should.equal(
    parse.EEq(parse.EName("A"), parse.EName("a"), parse.EName("b")),
  )
  parse.parse_expr("refl A a")
  |> should.be_ok
  |> should.equal(parse.ERefl(parse.EName("A"), parse.EName("a")))
}

pub fn parse_var_ix_test() {
  parse.parse_expr("var 5") |> should.be_ok |> should.equal(parse.EVarIx(5))
}

pub fn parse_hole_expr_test() {
  parse.parse_expr("hole 0 : Type 1")
  |> should.be_ok
  |> should.equal(parse.EHole(parse.HoleNum(0), parse.ESort(1)))
}

pub fn parse_hole_named_test() {
  parse.parse_expr("hole myhole : Type 0")
  |> should.be_ok
  |> should.equal(parse.EHole(parse.HoleName("myhole"), parse.ESort(0)))
}

pub fn parse_const_ref_test() {
  let hex = string_repeat("ab", 32)
  let src = "ref blake3_" <> hex
  parse.parse_expr(src)
  |> should.be_ok
  |> should.equal(parse.EConst(ab_digest()))
}

pub fn parse_module_items_test() {
  let src =
    "define id : fun (A : Type 0) -> A -> A := lam (A : Type 0) => lam (a : A) => a\nhole goal : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  items |> list.length |> should.equal(2)
  case items {
    [parse.Define(name: "id", ..), parse.HoleItem(name: "goal", ..)] ->
      should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn parse_runtime_item_test() {
  let host_hex = string_repeat("01", 32)
  let proc_hex = string_repeat("02", 32)
  let src =
    "runtime r : Type 0 := trusted ed25519_"
    <> host_hex
    <> " blake3_"
    <> proc_hex
    <> " (Type 0) : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  items |> list.length |> should.equal(1)
  case items {
    [parse.Runtime(name: "r", ..)] -> should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn parse_keyword_rejected_as_name_test() {
  parse.parse_expr("fun (fun : Type 0) -> fun")
  |> should.be_error
}

pub fn parse_trailing_token_error_test() {
  // A colon cannot start an atom, so it becomes a trailing-token error.
  parse.parse_expr("Type 0 :") |> should.be_error
}

// ── Printer tests ─────────────────────────────────────────────────────────────

pub fn print_sort_test() {
  print.print_term(term.Sort(0)) |> should.equal("Type 0")
  print.print_term(term.Sort(3)) |> should.equal("Type 3")
}

pub fn print_var_bound_test() {
  // At depth 2, Var(0) = x1, Var(1) = x0
  // We test by printing a Lam where the body is Var(0)
  let t = term.Lam(term.Sort(0), term.Var(0))
  print.print_term(t) |> should.equal("lam (x0 : Type 0) => x0")
}

pub fn print_var_free_test() {
  // Var(7) at depth 0 = free = "var 7"
  print.print_term(term.Var(7)) |> should.equal("var 7")
}

pub fn print_const_test() {
  let hex = string_repeat("00", 32)
  let expected = "ref blake3_" <> hex
  print.print_term(term.Const(zero_digest())) |> should.equal(expected)
}

pub fn print_pi_always_dependent_test() {
  // Pi(Sort(0), Pi(Var(0), Var(1))) = id type
  let t = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  let printed = print.print_term(t)
  printed
  |> should.equal(
    "fun (x0 : Type 0) -> fun (x1 : x0) -> x0",
  )
}

pub fn print_hole_test() {
  print.print_term(term.Hole(42, term.Sort(0)))
  |> should.equal("hole 42 : Type 0")
}

// ── Round-trip tests ──────────────────────────────────────────────────────────

fn parse_term(src: String) -> Result(term.Term, String) {
  case parse.parse_expr(src) {
    Error(parse.ParseError(msg)) -> Error("parse: " <> msg)
    Ok(e) ->
      case elab.elaborate_closed(e, elab.Runtime) {
        Error(_) -> Error("elab failed")
        Ok(t) -> Ok(t)
      }
  }
}

fn round_trip(t: term.Term) -> Nil {
  let printed = print.print_term(t)
  let back =
    parse_term(printed)
    |> should.be_ok
  back |> should.equal(t)
}

pub fn round_trip_var_test() {
  round_trip(term.Var(0))
  round_trip(term.Var(7))
}

pub fn round_trip_sort_test() {
  round_trip(term.Sort(0))
  round_trip(term.Sort(3))
}

pub fn round_trip_pi_id_type_test() {
  // fun (A : Type 0) -> (A -> A)
  round_trip(term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1))))
}

pub fn round_trip_lam_id_test() {
  let id =
    term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  round_trip(id)
}

pub fn round_trip_app_test() {
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  round_trip(term.App(id, term.Sort(3)))
  // nested App
  round_trip(
    term.App(term.App(term.Var(0), term.Var(1)), term.Var(2)),
  )
}

pub fn round_trip_eq_refl_test() {
  round_trip(term.Eq(term.Var(1), term.Var(0), term.Var(0)))
  round_trip(term.Refl(term.Var(1), term.Var(0)))
}

pub fn round_trip_const_test() {
  round_trip(term.Const(zero_digest()))
  round_trip(term.Const(ab_digest()))
}

pub fn round_trip_hole_test() {
  round_trip(term.Hole(0, term.Sort(0)))
  round_trip(term.Hole(42, term.Pi(term.Sort(0), term.Sort(0))))
}

pub fn round_trip_pi_free_var_test() {
  // Pi whose body references a free variable beyond the binder
  round_trip(term.Pi(term.Sort(0), term.Var(5)))
}

pub fn round_trip_lam_free_var_test() {
  round_trip(term.Lam(term.Sort(0), term.App(term.Var(0), term.Var(9))))
}

pub fn round_trip_trusted_test() {
  let host = pubkey.PublicKey(pubkey.Ed25519, b1_bytes32())
  let proc = digest.Digest(digest.Blake3, b2_bytes32())
  round_trip(term.Trusted(host, proc, term.Var(0), term.Var(0)))
}

pub fn round_trip_eq_with_compound_children_test() {
  // Eq ty (App ...) rhs -- arguments need parentheses in atom position
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  round_trip(
    term.Eq(term.Sort(0), term.App(id, term.Sort(0)), term.Sort(0)),
  )
}

// ── Elaborator tests ──────────────────────────────────────────────────────────

pub fn elab_name_to_var_test() {
  // lam (x : Type 0) => x  should elaborate to Lam(Sort(0), Var(0))
  let e = parse.ELam("x", parse.ESort(0), parse.EName("x"))
  elab.elaborate_closed(e, elab.Proof)
  |> should.be_ok
  |> should.equal(term.Lam(term.Sort(0), term.Var(0)))
}

pub fn elab_arrow_sugar_test() {
  // A -> B sugar: fun (_ : A) -> B
  let src = "fun (A : Type 0) -> A -> A"
  let e = parse.parse_expr(src) |> should.be_ok
  elab.elaborate_closed(e, elab.Proof)
  |> should.be_ok
  |> should.equal(
    term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1))),
  )
}

pub fn elab_unbound_name_error_test() {
  let e = parse.EName("missing")
  elab.elaborate_closed(e, elab.Proof)
  |> should.be_error
  |> should.equal(elab.UnboundName("missing"))
}

pub fn elab_trusted_in_proof_position_error_test() {
  let host = pubkey.PublicKey(pubkey.Ed25519, b1_bytes32())
  let proc = digest.Digest(digest.Blake3, b2_bytes32())
  let e =
    parse.ETrusted(
      host: host,
      proc: parse.ProcDigest(proc),
      args: parse.ESort(0),
      result_ty: parse.ESort(0),
    )
  elab.elaborate_closed(e, elab.Proof)
  |> should.be_error
  |> should.equal(elab.TrustedInProofPosition)
}

pub fn elab_trusted_in_runtime_position_ok_test() {
  let host = pubkey.PublicKey(pubkey.Ed25519, b1_bytes32())
  let proc = digest.Digest(digest.Blake3, b2_bytes32())
  let e =
    parse.ETrusted(
      host: host,
      proc: parse.ProcDigest(proc),
      args: parse.ESort(0),
      result_ty: parse.ESort(0),
    )
  elab.elaborate_closed(e, elab.Runtime)
  |> should.be_ok
  |> should.equal(term.Trusted(host, proc, term.Sort(0), term.Sort(0)))
}

pub fn elab_module_basic_test() {
  let src = "define id : fun (A : Type 0) -> A -> A := lam (A : Type 0) => lam (a : A) => a"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  m.entries |> list.length |> should.equal(1)
  let entry = case m.entries {
    [e] -> e
    _ -> panic as "expected exactly one entry"
  }
  entry.name |> should.equal("id")
  entry.kind |> should.equal(elab.DefineKind)
  // The elaborated term should be the polymorphic identity function
  entry.term
  |> should.equal(
    term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0))),
  )
}

pub fn elab_module_name_resolution_test() {
  // Second item refers to the first by name (becomes Const)
  let src =
    "define base : Type 1 := fun (x : Type 0) -> Type 0\ndefine use_base : Type 2 := base"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  m.entries |> list.length |> should.equal(2)
  let use_entry = case m.entries {
    [_, e] -> e
    _ -> panic as "expected two entries"
  }
  // use_base's body should be Const(addr of base)
  case use_entry.term {
    term.Const(_) -> should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn elab_module_duplicate_name_error_test() {
  let src = "define x : Type 0 := Type 0\ndefine x : Type 0 := Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  elab.elaborate_module(items)
  |> should.be_error
  |> should.equal(elab.DuplicateName("x"))
}

pub fn elab_module_hole_item_test() {
  let src = "hole mygoal : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  m.entries |> list.length |> should.equal(1)
  let entry = case m.entries {
    [e] -> e
    _ -> panic as "expected one entry"
  }
  entry.kind |> should.equal(elab.HoleKind)
  case entry.term {
    term.Hole(_, _) -> should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn elab_module_trusted_in_runtime_test() {
  // A runtime item using a trusted node with proc name resolved from env.
  let host_hex = string_repeat("01", 32)
  let proc_hex = string_repeat("02", 32)
  let src =
    "runtime r : Type 0 := trusted ed25519_"
    <> host_hex
    <> " blake3_"
    <> proc_hex
    <> " (Type 0) : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  m.entries |> list.length |> should.equal(1)
  let entry = case m.entries {
    [e] -> e
    _ -> panic as "expected one entry"
  }
  entry.kind |> should.equal(elab.RuntimeKind)
  case entry.term {
    term.Trusted(_, _, _, _) -> should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn elab_module_trusted_in_define_blocked_test() {
  let host_hex = string_repeat("01", 32)
  let proc_hex = string_repeat("02", 32)
  let src =
    "define bad : Type 0 := trusted ed25519_"
    <> host_hex
    <> " blake3_"
    <> proc_hex
    <> " (Type 0) : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  elab.elaborate_module(items)
  |> should.be_error
  |> should.equal(elab.TrustedInProofPosition)
}

pub fn elab_module_trusted_proc_by_name_test() {
  // Define a proc object, then use it by name in a runtime definition.
  let host_hex = string_repeat("fe", 32)
  let src =
    "define myproc : Type 1 := fun (x : Type 0) -> Type 0\nruntime r : Type 0 := trusted ed25519_"
    <> host_hex
    <> " myproc (Type 0) : Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  m.entries |> list.length |> should.equal(2)
  let r_entry = case m.entries {
    [_, e] -> e
    _ -> panic as "expected two entries"
  }
  r_entry.name |> should.equal("r")
  case r_entry.term {
    term.Trusted(_, _, _, _) -> should.be_true(True)
    _ -> should.be_true(False)
  }
}

pub fn elab_module_store_resolves_terms_test() {
  let src = "define t : Type 1 := Type 0"
  let items = parse.parse_module(src) |> should.be_ok
  let m = elab.elaborate_module(items) |> should.be_ok
  let entry = case m.entries {
    [e] -> e
    _ -> panic as "expected one entry"
  }
  // The store should resolve the address back to the term.
  m.store(entry.address) |> should.equal(Some(entry.term))
  // An unknown address returns None.
  m.store(zero_digest()) |> should.equal(None)
}
