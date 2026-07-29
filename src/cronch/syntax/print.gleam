/// Printer: core `Term` -> surface text.
///
/// The one hard guarantee is round-trip: `parse_expr(print_term(t)) == t`
/// for every core term, which the test suite checks on a corpus.
///
/// Bound variables are printed with systematic binder-level names (`x{level}`).
/// Variables free at the print point are printed as `var {index}`.
/// Pi is always printed in the dependent `fun (x : A) -> B` form.
/// Content addresses are printed as `algo_name_64hex`.
import cronch/digest
import cronch/pubkey
import cronch/term
import gleam/bit_array
import gleam/string

// Precedence levels, low to high.
const term_prec = 0

// fun / lam / hole / trusted
const eqapp_prec = 1

// Eq / refl
const app_prec = 2

// application
const atom_prec = 3

// var / Type / ref / name / parenthesized

/// Print a core term as round-trippable surface syntax.
pub fn print_term(t: term.Term) -> String {
  let #(s, _) = print_at(t, 0)
  s
}

/// Print `t` at binder `depth`, parenthesizing if its precedence is below `min`.
fn at_least(t: term.Term, depth: Int, min: Int) -> String {
  let #(s, p) = print_at(t, depth)
  case p < min {
    True -> "(" <> s <> ")"
    False -> s
  }
}

fn print_at(t: term.Term, depth: Int) -> #(String, Int) {
  case t {
    term.Var(k) ->
      case k < depth {
        True -> #("x" <> int_to_string(depth - 1 - k), atom_prec)
        False -> #("var " <> int_to_string(k), atom_prec)
      }

    term.Sort(u) -> #("Type " <> int_to_string(u), atom_prec)

    term.Const(d) -> #("ref " <> digest_str(d), atom_prec)

    term.Pi(a, b) -> {
      let name = "x" <> int_to_string(depth)
      let domain = at_least(a, depth, term_prec)
      let body = at_least(b, depth + 1, term_prec)
      #("fun (" <> name <> " : " <> domain <> ") -> " <> body, term_prec)
    }

    term.Lam(a, b) -> {
      let name = "x" <> int_to_string(depth)
      let domain = at_least(a, depth, term_prec)
      let body = at_least(b, depth + 1, term_prec)
      #("lam (" <> name <> " : " <> domain <> ") => " <> body, term_prec)
    }

    term.App(f, a) -> {
      let func = at_least(f, depth, app_prec)
      let arg = at_least(a, depth, atom_prec)
      #(func <> " " <> arg, app_prec)
    }

    term.Eq(typ, a, b) -> {
      let typ_s = at_least(typ, depth, atom_prec)
      let a_s = at_least(a, depth, atom_prec)
      let b_s = at_least(b, depth, atom_prec)
      #("Eq " <> typ_s <> " " <> a_s <> " " <> b_s, eqapp_prec)
    }

    term.Refl(typ, a) -> {
      let typ_s = at_least(typ, depth, atom_prec)
      let a_s = at_least(a, depth, atom_prec)
      #("refl " <> typ_s <> " " <> a_s, eqapp_prec)
    }

    term.Hole(id, goal) -> {
      let goal_s = at_least(goal, depth, term_prec)
      #("hole " <> int_to_string(id) <> " : " <> goal_s, term_prec)
    }

    term.Trusted(host, proc, args, rty) -> {
      let host_s = pubkey_str(host)
      let proc_s = digest_str(proc)
      let args_s = at_least(args, depth, atom_prec)
      let rty_s = at_least(rty, depth, term_prec)
      #(
        "trusted " <> host_s <> " " <> proc_s <> " " <> args_s <> " : " <> rty_s,
        term_prec,
      )
    }
  }
}

fn digest_str(d: digest.Digest) -> String {
  let digest.Digest(algorithm, bytes) = d
  digest.algorithm_name(algorithm)
  <> "_"
  <> { bytes |> bit_array.base16_encode |> string.lowercase }
}

fn pubkey_str(public_key: pubkey.PublicKey) -> String {
  let pubkey.PublicKey(scheme, bytes) = public_key
  pubkey.scheme_name(scheme)
  <> "_"
  <> { bytes |> bit_array.base16_encode |> string.lowercase }
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
