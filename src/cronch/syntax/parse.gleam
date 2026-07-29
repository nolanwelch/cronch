/// Surface AST and recursive-descent parser.
///
/// The surface AST keeps human names; elaboration converts to de Bruijn `Term`s.
/// Addresses are written as `algo_name_64hex` (a single word token); this keeps
/// the colon token unambiguous for type annotations.
import cronch/digest
import cronch/pubkey
import cronch/syntax/lex.{type Token}
import gleam/bit_array
import gleam/list
import gleam/string

// ── Surface AST ───────────────────────────────────────────────────────────────

/// How a hole's id was written: an explicit number or a name (fresh id allocated
/// during elaboration).
pub type HoleSpec {
  HoleNumber(Int)
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
  /// Propositional equality `Eq typ a b`.
  EEq(Expr, Expr, Expr)
  /// Reflexivity `refl typ a`.
  ERefl(Expr, Expr)
  /// Open obligation `hole spec : goal`.
  EHole(HoleSpec, Expr)
  /// Host-authority result `trusted host proc args : result_typ`.
  ETrusted(host: pubkey.PublicKey, proc: ProcRef, args: Expr, result_typ: Expr)
}

/// Top-level item.
pub type Item {
  /// `define name : T := e`  (proof position; `trusted` not allowed in body).
  Define(name: String, typ: Expr, body: Expr)
  /// `runtime name : T := e`  (runtime position; `trusted` allowed in body).
  Runtime(name: String, typ: Expr, body: Expr)
  /// `hole name : T`  (a standalone open obligation).
  HoleItem(name: String, typ: Expr)
}

pub type ParseError {
  ParseError(msg: String)
}

// ── Parser result type ────────────────────────────────────────────────────────

/// A parser result: either `(value, remaining_tokens)` or an error.
type PR(a) =
  Result(#(a, List(Token)), ParseError)

// ── Token helpers ─────────────────────────────────────────────────────────────

fn expect(tokens: List(Token), want: Token) -> Result(List(Token), ParseError) {
  case tokens {
    [t, ..rest] if t == want -> Ok(rest)
    other ->
      Error(ParseError(
        "expected "
        <> tok_to_string(want)
        <> ", found "
        <> first_tok_string(other),
      ))
  }
}

fn expect_word(
  tokens: List(Token),
) -> Result(#(String, List(Token)), ParseError) {
  case tokens {
    [lex.Word(w), ..rest] -> Ok(#(w, rest))
    other ->
      Error(ParseError("expected a word, found " <> first_tok_string(other)))
  }
}

fn expect_name(
  tokens: List(Token),
) -> Result(#(String, List(Token)), ParseError) {
  case expect_word(tokens) {
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
        Error(_) -> Error(ParseError("unknown hash algorithm: " <> algo_name))
        Ok(algorithm) ->
          case bit_array.base16_decode(string.uppercase(hex)) {
            Ok(bytes) -> Ok(digest.Digest(algorithm, bytes))
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
        Error(_) -> Error(ParseError("unknown key scheme: " <> scheme_name))
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

fn parse_number(
  tokens: List(Token),
) -> Result(#(Int, List(Token)), ParseError) {
  case expect_word(tokens) {
    Error(e) -> Error(e)
    Ok(#(w, rest)) ->
      case int_of_string(w) {
        Ok(n) -> Ok(#(n, rest))
        Error(_) -> Error(ParseError("expected a number, got: " <> w))
      }
  }
}

fn parse_binder_group(
  tokens: List(Token),
) -> Result(#(#(String, Expr), List(Token)), ParseError) {
  use tokens <- chain(expect(tokens, lex.LParen))
  use #(name, tokens) <- chain(expect_name(tokens))
  use tokens <- chain(expect(tokens, lex.Colon))
  use #(typ, tokens) <- chain(parse_term(tokens))
  use tokens <- chain(expect(tokens, lex.RParen))
  Ok(#(#(name, typ), tokens))
}

fn parse_hole_spec(
  tokens: List(Token),
) -> Result(#(HoleSpec, List(Token)), ParseError) {
  case expect_word(tokens) {
    Error(e) -> Error(e)
    Ok(#(w, rest)) ->
      case int_of_string(w) {
        Ok(n) -> Ok(#(HoleNumber(n), rest))
        Error(_) ->
          case is_keyword(w) {
            True ->
              Error(ParseError("expected hole id or name, found keyword: " <> w))
            False -> Ok(#(HoleName(w), rest))
          }
      }
  }
}

fn parse_proc_ref(
  tokens: List(Token),
) -> Result(#(ProcRef, List(Token)), ParseError) {
  case tokens {
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
              Error(ParseError("expected proc reference, found keyword: " <> w))
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
fn parse_term(tokens: List(Token)) -> PR(Expr) {
  case tokens {
    [lex.Word("fun"), ..rest] -> {
      use #(#(name, domain), tokens) <- chain(parse_binder_group(rest))
      use tokens <- chain(expect(tokens, lex.Arrow))
      use #(body, tokens) <- chain(parse_term(tokens))
      Ok(#(EPi(name, domain, body), tokens))
    }
    [lex.Word("lam"), ..rest] -> {
      use #(#(name, domain), tokens) <- chain(parse_binder_group(rest))
      use tokens <- chain(expect(tokens, lex.FatArrow))
      use #(body, tokens) <- chain(parse_term(tokens))
      Ok(#(ELam(name, domain, body), tokens))
    }
    [lex.Word("trusted"), ..rest] -> {
      use #(host_word, tokens) <- chain(expect_word(rest))
      use host <- chain(parse_pubkey_word(host_word))
      use #(proc, tokens) <- chain(parse_proc_ref(tokens))
      use #(args, tokens) <- chain(parse_atom(tokens))
      use tokens <- chain(expect(tokens, lex.Colon))
      use #(result_typ, tokens) <- chain(parse_term(tokens))
      Ok(#(
        ETrusted(host: host, proc: proc, args: args, result_typ: result_typ),
        tokens,
      ))
    }
    [lex.Word("hole"), ..rest] -> {
      use #(spec, tokens) <- chain(parse_hole_spec(rest))
      use tokens <- chain(expect(tokens, lex.Colon))
      use #(goal, tokens) <- chain(parse_term(tokens))
      Ok(#(EHole(spec, goal), tokens))
    }
    _ -> parse_arrow(tokens)
  }
}

// arrow := eqapp ("->" term)?
fn parse_arrow(tokens: List(Token)) -> PR(Expr) {
  use #(lhs, tokens) <- chain(parse_eqapp(tokens))
  case tokens {
    [lex.Arrow, ..rest] -> {
      use #(rhs, tokens) <- chain(parse_term(rest))
      Ok(#(EArrow(lhs, rhs), tokens))
    }
    _ -> Ok(#(lhs, tokens))
  }
}

// eqapp := "Eq" atom atom atom | "refl" atom atom | app
fn parse_eqapp(tokens: List(Token)) -> PR(Expr) {
  case tokens {
    [lex.Word("Eq"), ..rest] -> {
      use #(typ, tokens) <- chain(parse_atom(rest))
      use #(a, tokens) <- chain(parse_atom(tokens))
      use #(b, tokens) <- chain(parse_atom(tokens))
      Ok(#(EEq(typ, a, b), tokens))
    }
    [lex.Word("refl"), ..rest] -> {
      use #(typ, tokens) <- chain(parse_atom(rest))
      use #(a, tokens) <- chain(parse_atom(tokens))
      Ok(#(ERefl(typ, a), tokens))
    }
    _ -> parse_app(tokens)
  }
}

// app := atom atom*
fn parse_app(tokens: List(Token)) -> PR(Expr) {
  use #(head, tokens) <- chain(parse_atom(tokens))
  parse_app_loop(head, tokens)
}

fn parse_app_loop(f: Expr, tokens: List(Token)) -> PR(Expr) {
  case starts_atom(tokens) {
    False -> Ok(#(f, tokens))
    True -> {
      use #(arg, tokens) <- chain(parse_atom(tokens))
      parse_app_loop(EApp(f, arg), tokens)
    }
  }
}

fn starts_atom(tokens: List(Token)) -> Bool {
  case tokens {
    [lex.LParen, ..]
    | [lex.Word("Type"), ..]
    | [lex.Word("var"), ..]
    | [lex.Word("ref"), ..] -> True
    [lex.Word(w), ..] -> !is_keyword(w)
    _ -> False
  }
}

// atom := "(" term ")" | "Type" number | "var" number | "ref" address | name
fn parse_atom(tokens: List(Token)) -> PR(Expr) {
  case tokens {
    [lex.LParen, ..rest] -> {
      use #(e, tokens) <- chain(parse_term(rest))
      use tokens <- chain(expect(tokens, lex.RParen))
      Ok(#(e, tokens))
    }
    [lex.Word("Type"), ..rest] -> {
      use #(n, tokens) <- chain(parse_number(rest))
      Ok(#(ESort(n), tokens))
    }
    [lex.Word("var"), ..rest] -> {
      use #(n, tokens) <- chain(parse_number(rest))
      Ok(#(EVarIx(n), tokens))
    }
    [lex.Word("ref"), ..rest] -> {
      use #(w, tokens) <- chain(expect_word(rest))
      use d <- chain(parse_digest_word(w))
      Ok(#(EConst(d), tokens))
    }
    [lex.Word(w), ..rest] ->
      case is_keyword(w) {
        True ->
          Error(ParseError("unexpected keyword `" <> w <> "` in atom position"))
        False -> Ok(#(EName(w), rest))
      }
    other ->
      Error(ParseError("expected an atom, found: " <> first_tok_string(other)))
  }
}

fn parse_item(tokens: List(Token)) -> PR(Item) {
  case tokens {
    [lex.Word("define"), ..rest] -> {
      use #(name, tokens) <- chain(expect_name(rest))
      use tokens <- chain(expect(tokens, lex.Colon))
      use #(typ, tokens) <- chain(parse_term(tokens))
      use tokens <- chain(expect(tokens, lex.ColonEq))
      use #(body, tokens) <- chain(parse_term(tokens))
      Ok(#(Define(name, typ, body), tokens))
    }
    [lex.Word("runtime"), ..rest] -> {
      use #(name, tokens) <- chain(expect_name(rest))
      use tokens <- chain(expect(tokens, lex.Colon))
      use #(typ, tokens) <- chain(parse_term(tokens))
      use tokens <- chain(expect(tokens, lex.ColonEq))
      use #(body, tokens) <- chain(parse_term(tokens))
      Ok(#(Runtime(name, typ, body), tokens))
    }
    [lex.Word("hole"), ..rest] -> {
      use #(name, tokens) <- chain(expect_name(rest))
      use tokens <- chain(expect(tokens, lex.Colon))
      use #(typ, tokens) <- chain(parse_term(tokens))
      Ok(#(HoleItem(name, typ), tokens))
    }
    other ->
      Error(ParseError(
        "expected `define`, `runtime`, or `hole` at top level, found: "
        <> first_tok_string(other),
      ))
  }
}

fn parse_module_loop(
  tokens: List(Token),
  acc: List(Item),
) -> Result(List(Item), ParseError) {
  case tokens {
    [] -> Ok(list.reverse(acc))
    _ -> {
      use #(item, tokens) <- chain(parse_item(tokens))
      parse_module_loop(tokens, [item, ..acc])
    }
  }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Parse a single expression.
pub fn parse_expr(src: String) -> Result(Expr, ParseError) {
  case lex.lex(src) {
    Error(e) ->
      Error(ParseError(
        "lex error at " <> int_to_string(e.position) <> ": " <> e.msg,
      ))
    Ok(tokens) ->
      case parse_term(tokens) {
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
        "lex error at " <> int_to_string(e.position) <> ": " <> e.msg,
      ))
    Ok(tokens) -> parse_module_loop(tokens, [])
  }
}

// ── Utilities ─────────────────────────────────────────────────────────────────

fn tok_to_string(tok: Token) -> String {
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

fn first_tok_string(tokens: List(Token)) -> String {
  case tokens {
    [] -> "end-of-input"
    [t, ..] -> tok_to_string(t)
  }
}

fn toks_to_string(tokens: List(Token)) -> String {
  tokens |> list.map(tok_to_string) |> string.join(" ")
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
