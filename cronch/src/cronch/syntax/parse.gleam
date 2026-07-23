/// Surface AST and recursive-descent parser.
///
/// The surface AST keeps human names; elaboration converts to de Bruijn `Term`s.
/// Addresses are written as `algo_name_64hex` (a single word token); this keeps
/// the colon token unambiguous for type annotations.

import cronch/digest
import cronch/pubkey
import cronch/syntax/lex.{type Tok}
import gleam/bit_array
import gleam/list
import gleam/string

// ── Surface AST ───────────────────────────────────────────────────────────────

/// How a hole's id was written: an explicit number or a name (fresh id allocated
/// during elaboration).
pub type HoleSpec {
  HoleNum(Int)
  HoleName(String)
}

/// A procedure reference in a `trusted` form: either a literal address or a name
/// to be resolved against the module environment.
pub type ProcRef {
  ProcDigest(digest.Digest)
  ProcName(String)
}

/// Surface expression.
pub type Expr {
  /// An identifier: bound variable name or top-level name.
  EName(String)
  /// Explicit de Bruijn index `var n` (round-trip only).
  EVarIx(Int)
  /// Universe `Type n`.
  ESort(Int)
  /// Content reference `algo_name_64hex`.
  EConst(digest.Digest)
  /// Non-dependent function type `A -> B` (sugar: elaborates to Pi with `_`).
  EArrow(Expr, Expr)
  /// Dependent function type `fun (x : A) -> B`.
  EPi(String, Expr, Expr)
  /// Lambda `lam (x : A) => b`.
  ELam(String, Expr, Expr)
  /// Application `f a`.
  EApp(Expr, Expr)
  /// Propositional equality `Eq ty a b`.
  EEq(Expr, Expr, Expr)
  /// Reflexivity `refl ty a`.
  ERefl(Expr, Expr)
  /// Open obligation `hole spec : goal`.
  EHole(HoleSpec, Expr)
  /// Host-authority result `trusted host proc args : result_ty`.
  ETrusted(host: pubkey.PublicKey, proc: ProcRef, args: Expr, result_ty: Expr)
}

/// Top-level item.
pub type Item {
  /// `define name : T := e`  (proof position; `trusted` not allowed in body).
  Define(name: String, ty: Expr, body: Expr)
  /// `runtime name : T := e`  (runtime position; `trusted` allowed in body).
  Runtime(name: String, ty: Expr, body: Expr)
  /// `hole name : T`  (a standalone open obligation).
  HoleItem(name: String, ty: Expr)
}

pub type ParseError {
  ParseError(msg: String)
}

// ── Parser result type ────────────────────────────────────────────────────────

/// A parser result: either `(value, remaining_tokens)` or an error.
type PR(a) =
  Result(#(a, List(Tok)), ParseError)

// ── Token helpers ─────────────────────────────────────────────────────────────

fn expect(toks: List(Tok), want: Tok) -> Result(List(Tok), ParseError) {
  case toks {
    [t, ..rest] if t == want -> Ok(rest)
    other ->
      Error(ParseError(
        "expected " <> tok_to_string(want) <> ", found " <> first_tok_string(other),
      ))
  }
}

fn expect_word(toks: List(Tok)) -> Result(#(String, List(Tok)), ParseError) {
  case toks {
    [lex.Word(w), ..rest] -> Ok(#(w, rest))
    other -> Error(ParseError("expected a word, found " <> first_tok_string(other)))
  }
}

fn expect_name(toks: List(Tok)) -> Result(#(String, List(Tok)), ParseError) {
  case expect_word(toks) {
    Error(e) -> Error(e)
    Ok(#(w, rest)) ->
      case is_keyword(w) {
        True ->
          Error(ParseError("expected a name, found keyword `" <> w <> "`"))
        False -> Ok(#(w, rest))
      }
  }
}

// ── Keywords ──────────────────────────────────────────────────────────────────

fn is_keyword(w: String) -> Bool {
  list.contains(
    [
      "fun", "lam", "trusted", "hole", "Eq", "refl", "Type", "var", "ref",
      "define", "runtime",
    ],
    w,
  )
}

// ── Address word helpers ──────────────────────────────────────────────────────

fn parse_digest_word(w: String) -> Result(digest.Digest, ParseError) {
  case string.split(w, "_") {
    [algo_name, hex] ->
      case
        list.find(digest.all_algorithms(), fn(a) {
          digest.algorithm_name(a) == algo_name
        })
      {
        Error(_) ->
          Error(ParseError("unknown hash algorithm: " <> algo_name))
        Ok(algo) ->
          case bit_array.base16_decode(string.uppercase(hex)) {
            Ok(bytes) -> Ok(digest.Digest(algo, bytes))
            Error(_) -> Error(ParseError("invalid hex in address: " <> hex))
          }
      }
    _ ->
      Error(ParseError(
        "expected algo_hex address word (e.g. blake3_000...0), got: " <> w,
      ))
  }
}

fn parse_pubkey_word(w: String) -> Result(pubkey.PublicKey, ParseError) {
  case string.split(w, "_") {
    [scheme_name, hex] ->
      case
        list.find(pubkey.all_schemes(), fn(s) {
          pubkey.scheme_name(s) == scheme_name
        })
      {
        Error(_) ->
          Error(ParseError("unknown key scheme: " <> scheme_name))
        Ok(scheme) ->
          case bit_array.base16_decode(string.uppercase(hex)) {
            Ok(bytes) -> Ok(pubkey.PublicKey(scheme, bytes))
            Error(_) -> Error(ParseError("invalid hex in public key: " <> hex))
          }
      }
    _ ->
      Error(ParseError(
        "expected scheme_hex pubkey word (e.g. ed25519_000...0), got: " <> w,
      ))
  }
}

fn is_digest_word(w: String) -> Bool {
  case string.split(w, "_") {
    [_, suffix] -> lex.is_hex32(suffix)
    _ -> False
  }
}

// ── Sub-parsers ───────────────────────────────────────────────────────────────

fn parse_num(toks: List(Tok)) -> Result(#(Int, List(Tok)), ParseError) {
  case expect_word(toks) {
    Error(e) -> Error(e)
    Ok(#(w, rest)) ->
      case int_of_string(w) {
        Ok(n) -> Ok(#(n, rest))
        Error(_) -> Error(ParseError("expected a number, got: " <> w))
      }
  }
}

fn parse_binder_group(
  toks: List(Tok),
) -> Result(#(#(String, Expr), List(Tok)), ParseError) {
  use toks <- chain(expect(toks, lex.LParen))
  use #(name, toks) <- chain(expect_name(toks))
  use toks <- chain(expect(toks, lex.Colon))
  use #(ty, toks) <- chain(parse_term(toks))
  use toks <- chain(expect(toks, lex.RParen))
  Ok(#(#(name, ty), toks))
}

fn parse_hole_spec(
  toks: List(Tok),
) -> Result(#(HoleSpec, List(Tok)), ParseError) {
  case expect_word(toks) {
    Error(e) -> Error(e)
    Ok(#(w, rest)) ->
      case int_of_string(w) {
        Ok(n) -> Ok(#(HoleNum(n), rest))
        Error(_) ->
          case is_keyword(w) {
            True ->
              Error(ParseError(
                "expected hole id or name, found keyword: " <> w,
              ))
            False -> Ok(#(HoleName(w), rest))
          }
      }
  }
}

fn parse_proc_ref(
  toks: List(Tok),
) -> Result(#(ProcRef, List(Tok)), ParseError) {
  case toks {
    [lex.Word(w), ..rest] ->
      case is_digest_word(w) {
        True ->
          case parse_digest_word(w) {
            Ok(d) -> Ok(#(ProcDigest(d), rest))
            Error(e) -> Error(e)
          }
        False ->
          case is_keyword(w) {
            True ->
              Error(ParseError(
                "expected proc reference, found keyword: " <> w,
              ))
            False -> Ok(#(ProcName(w), rest))
          }
      }
    other ->
      Error(ParseError(
        "expected proc reference, found: " <> first_tok_string(other),
      ))
  }
}

// ── Grammar ───────────────────────────────────────────────────────────────────

// term := "fun" binder | "lam" binder | "trusted" ... | "hole" ... | arrow
fn parse_term(toks: List(Tok)) -> PR(Expr) {
  case toks {
    [lex.Word("fun"), ..rest] -> {
      use #(#(name, dom), toks) <- chain(parse_binder_group(rest))
      use toks <- chain(expect(toks, lex.Arrow))
      use #(body, toks) <- chain(parse_term(toks))
      Ok(#(EPi(name, dom, body), toks))
    }
    [lex.Word("lam"), ..rest] -> {
      use #(#(name, dom), toks) <- chain(parse_binder_group(rest))
      use toks <- chain(expect(toks, lex.FatArrow))
      use #(body, toks) <- chain(parse_term(toks))
      Ok(#(ELam(name, dom, body), toks))
    }
    [lex.Word("trusted"), ..rest] -> {
      use #(host_word, toks) <- chain(expect_word(rest))
      use host <- chain(parse_pubkey_word(host_word))
      use #(proc, toks) <- chain(parse_proc_ref(toks))
      use #(args, toks) <- chain(parse_atom(toks))
      use toks <- chain(expect(toks, lex.Colon))
      use #(result_ty, toks) <- chain(parse_term(toks))
      Ok(#(
        ETrusted(host: host, proc: proc, args: args, result_ty: result_ty),
        toks,
      ))
    }
    [lex.Word("hole"), ..rest] -> {
      use #(spec, toks) <- chain(parse_hole_spec(rest))
      use toks <- chain(expect(toks, lex.Colon))
      use #(goal, toks) <- chain(parse_term(toks))
      Ok(#(EHole(spec, goal), toks))
    }
    _ -> parse_arrow(toks)
  }
}

// arrow := eqapp ("->" term)?
fn parse_arrow(toks: List(Tok)) -> PR(Expr) {
  use #(lhs, toks) <- chain(parse_eqapp(toks))
  case toks {
    [lex.Arrow, ..rest] -> {
      use #(rhs, toks) <- chain(parse_term(rest))
      Ok(#(EArrow(lhs, rhs), toks))
    }
    _ -> Ok(#(lhs, toks))
  }
}

// eqapp := "Eq" atom atom atom | "refl" atom atom | app
fn parse_eqapp(toks: List(Tok)) -> PR(Expr) {
  case toks {
    [lex.Word("Eq"), ..rest] -> {
      use #(ty, toks) <- chain(parse_atom(rest))
      use #(a, toks) <- chain(parse_atom(toks))
      use #(b, toks) <- chain(parse_atom(toks))
      Ok(#(EEq(ty, a, b), toks))
    }
    [lex.Word("refl"), ..rest] -> {
      use #(ty, toks) <- chain(parse_atom(rest))
      use #(a, toks) <- chain(parse_atom(toks))
      Ok(#(ERefl(ty, a), toks))
    }
    _ -> parse_app(toks)
  }
}

// app := atom atom*
fn parse_app(toks: List(Tok)) -> PR(Expr) {
  use #(head, toks) <- chain(parse_atom(toks))
  parse_app_loop(head, toks)
}

fn parse_app_loop(f: Expr, toks: List(Tok)) -> PR(Expr) {
  case starts_atom(toks) {
    False -> Ok(#(f, toks))
    True -> {
      use #(arg, toks) <- chain(parse_atom(toks))
      parse_app_loop(EApp(f, arg), toks)
    }
  }
}

fn starts_atom(toks: List(Tok)) -> Bool {
  case toks {
    [lex.LParen, ..] -> True
    [lex.Word("Type"), ..] -> True
    [lex.Word("var"), ..] -> True
    [lex.Word("ref"), ..] -> True
    [lex.Word(w), ..] ->
      case is_keyword(w) {
        True -> False
        False -> True
      }
    _ -> False
  }
}

// atom := "(" term ")" | "Type" num | "var" num | "ref" addr | name
fn parse_atom(toks: List(Tok)) -> PR(Expr) {
  case toks {
    [lex.LParen, ..rest] -> {
      use #(e, toks) <- chain(parse_term(rest))
      use toks <- chain(expect(toks, lex.RParen))
      Ok(#(e, toks))
    }
    [lex.Word("Type"), ..rest] -> {
      use #(n, toks) <- chain(parse_num(rest))
      Ok(#(ESort(n), toks))
    }
    [lex.Word("var"), ..rest] -> {
      use #(n, toks) <- chain(parse_num(rest))
      Ok(#(EVarIx(n), toks))
    }
    [lex.Word("ref"), ..rest] -> {
      use #(w, toks) <- chain(expect_word(rest))
      use d <- chain(parse_digest_word(w))
      Ok(#(EConst(d), toks))
    }
    [lex.Word(w), ..rest] ->
      case is_keyword(w) {
        True ->
          Error(ParseError(
            "unexpected keyword `" <> w <> "` in atom position",
          ))
        False -> Ok(#(EName(w), rest))
      }
    other ->
      Error(ParseError("expected an atom, found: " <> first_tok_string(other)))
  }
}

fn parse_item(toks: List(Tok)) -> PR(Item) {
  case toks {
    [lex.Word("define"), ..rest] -> {
      use #(name, toks) <- chain(expect_name(rest))
      use toks <- chain(expect(toks, lex.Colon))
      use #(ty, toks) <- chain(parse_term(toks))
      use toks <- chain(expect(toks, lex.ColonEq))
      use #(body, toks) <- chain(parse_term(toks))
      Ok(#(Define(name, ty, body), toks))
    }
    [lex.Word("runtime"), ..rest] -> {
      use #(name, toks) <- chain(expect_name(rest))
      use toks <- chain(expect(toks, lex.Colon))
      use #(ty, toks) <- chain(parse_term(toks))
      use toks <- chain(expect(toks, lex.ColonEq))
      use #(body, toks) <- chain(parse_term(toks))
      Ok(#(Runtime(name, ty, body), toks))
    }
    [lex.Word("hole"), ..rest] -> {
      use #(name, toks) <- chain(expect_name(rest))
      use toks <- chain(expect(toks, lex.Colon))
      use #(ty, toks) <- chain(parse_term(toks))
      Ok(#(HoleItem(name, ty), toks))
    }
    other ->
      Error(ParseError(
        "expected `define`, `runtime`, or `hole` at top level, found: "
        <> first_tok_string(other),
      ))
  }
}

fn parse_module_loop(
  toks: List(Tok),
  acc: List(Item),
) -> Result(List(Item), ParseError) {
  case toks {
    [] -> Ok(list.reverse(acc))
    _ -> {
      use #(item, toks) <- chain(parse_item(toks))
      parse_module_loop(toks, [item, ..acc])
    }
  }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Parse a single expression.
pub fn parse_expr(src: String) -> Result(Expr, ParseError) {
  case lex.lex(src) {
    Error(e) ->
      Error(ParseError(
        "lex error at " <> int_to_string(e.pos) <> ": " <> e.msg,
      ))
    Ok(toks) ->
      case parse_term(toks) {
        Error(e) -> Error(e)
        Ok(#(e, [])) -> Ok(e)
        Ok(#(_, rest)) ->
          Error(ParseError(
            "trailing tokens after expression: " <> toks_to_string(rest),
          ))
      }
  }
}

/// Parse a whole module (a sequence of top-level items).
pub fn parse_module(src: String) -> Result(List(Item), ParseError) {
  case lex.lex(src) {
    Error(e) ->
      Error(ParseError(
        "lex error at " <> int_to_string(e.pos) <> ": " <> e.msg,
      ))
    Ok(toks) -> parse_module_loop(toks, [])
  }
}

// ── Utilities ─────────────────────────────────────────────────────────────────

fn tok_to_string(tok: Tok) -> String {
  case tok {
    lex.LParen -> "("
    lex.RParen -> ")"
    lex.Arrow -> "->"
    lex.FatArrow -> "=>"
    lex.ColonEq -> ":="
    lex.Colon -> ":"
    lex.Word(w) -> w
  }
}

fn first_tok_string(toks: List(Tok)) -> String {
  case toks {
    [] -> "end-of-input"
    [t, ..] -> tok_to_string(t)
  }
}

fn toks_to_string(toks: List(Tok)) -> String {
  toks |> list.map(tok_to_string) |> string.join(" ")
}

fn int_to_string(n: Int) -> String {
  case n {
    0 -> "0"
    _ -> do_int_to_string(n, "")
  }
}

fn do_int_to_string(n: Int, acc: String) -> String {
  case n {
    0 -> acc
    _ -> do_int_to_string(n / 10, int_digit(n % 10) <> acc)
  }
}

fn int_digit(d: Int) -> String {
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

fn int_of_string(s: String) -> Result(Int, Nil) {
  do_int_of_string(string.to_graphemes(s), 0, False)
}

fn do_int_of_string(
  chars: List(String),
  acc: Int,
  seen: Bool,
) -> Result(Int, Nil) {
  case chars {
    [] ->
      case seen {
        True -> Ok(acc)
        False -> Error(Nil)
      }
    [c, ..rest] ->
      case digit_val(c) {
        Error(_) -> Error(Nil)
        Ok(d) -> do_int_of_string(rest, acc * 10 + d, True)
      }
  }
}

fn digit_val(c: String) -> Result(Int, Nil) {
  case c {
    "0" -> Ok(0)
    "1" -> Ok(1)
    "2" -> Ok(2)
    "3" -> Ok(3)
    "4" -> Ok(4)
    "5" -> Ok(5)
    "6" -> Ok(6)
    "7" -> Ok(7)
    "8" -> Ok(8)
    "9" -> Ok(9)
    _ -> Error(Nil)
  }
}

/// Monadic bind for parser results. Enables `use` syntax.
fn chain(
  r: Result(a, ParseError),
  f: fn(a) -> Result(b, ParseError),
) -> Result(b, ParseError) {
  case r {
    Error(e) -> Error(e)
    Ok(a) -> f(a)
  }
}
