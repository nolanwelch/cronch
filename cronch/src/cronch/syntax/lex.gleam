/// Tokenizer for the ASCII surface syntax.
///
/// Punctuation budget: `(` `)` `->` `=>` `:=` `:`, plus `--` line comments.
/// Everything else is a Word: a maximal run of [A-Za-z0-9_].
/// No other characters are legal.

import gleam/bit_array
import gleam/list
import gleam/result
import gleam/string

pub type Tok {
  LParen
  RParen
  Arrow
  FatArrow
  ColonEq
  Colon
  Word(String)
}

pub type LexError {
  LexError(pos: Int, msg: String)
}

pub fn lex(src: String) -> Result(List(Tok), LexError) {
  do_lex(string.to_graphemes(src), 0, [])
  |> result.map(list.reverse)
}

fn do_lex(
  chars: List(String),
  pos: Int,
  acc: List(Tok),
) -> Result(List(Tok), LexError) {
  case chars {
    [] -> Ok(acc)
    [" ", ..rest] | ["\t", ..rest] | ["\r", ..rest] | ["\n", ..rest] ->
      do_lex(rest, pos + 1, acc)
    ["(", ..rest] -> do_lex(rest, pos + 1, [LParen, ..acc])
    [")", ..rest] -> do_lex(rest, pos + 1, [RParen, ..acc])
    ["-", "-", ..rest] -> skip_comment(rest, pos + 2, acc)
    ["-", ">", ..rest] -> do_lex(rest, pos + 2, [Arrow, ..acc])
    ["=", ">", ..rest] -> do_lex(rest, pos + 2, [FatArrow, ..acc])
    [":", "=", ..rest] -> do_lex(rest, pos + 2, [ColonEq, ..acc])
    [":", ..rest] -> do_lex(rest, pos + 1, [Colon, ..acc])
    [c, ..] ->
      case is_word_char(c) {
        True -> lex_word(chars, pos, acc)
        False -> Error(LexError(pos: pos, msg: "unexpected character: " <> c))
      }
  }
}

fn skip_comment(
  chars: List(String),
  pos: Int,
  acc: List(Tok),
) -> Result(List(Tok), LexError) {
  case chars {
    [] -> Ok(acc)
    ["\n", ..rest] -> do_lex(rest, pos + 1, acc)
    [_, ..rest] -> skip_comment(rest, pos + 1, acc)
  }
}

fn lex_word(
  chars: List(String),
  pos: Int,
  acc: List(Tok),
) -> Result(List(Tok), LexError) {
  let #(word_chars, rest) = list.split_while(chars, is_word_char)
  let word = string.concat(word_chars)
  do_lex(rest, pos + string.length(word), [Word(word), ..acc])
}

fn is_word_char(c: String) -> Bool {
  case bit_array.from_string(c) {
    <<b>> ->
      { b >= 0x41 && b <= 0x5a }
      || { b >= 0x61 && b <= 0x7a }
      || { b >= 0x30 && b <= 0x39 }
      || b == 0x5f
    _ -> False
  }
}

/// True when `w` is a 64-character lowercase-hex string (32 raw bytes).
pub fn is_hex32(w: String) -> Bool {
  string.length(w) == 64
  && list.all(string.to_graphemes(w), is_lower_hex_char)
}

fn is_lower_hex_char(c: String) -> Bool {
  case bit_array.from_string(c) {
    <<b>> ->
      { b >= 0x30 && b <= 0x39 } || { b >= 0x61 && b <= 0x66 }
    _ -> False
  }
}
