/// End-to-end demo: FOL-flavored proofs via Curry-Howard.
///
/// Propositions are types in Type 0.  A proof of proposition P is a term of
/// type P.  Implication is the function type (->).  Universal quantification
/// is Pi.  Equality is the built-in Eq.
///
/// Pipeline: source text -> parse -> elaborate -> kernel check.

import cronch/kernel
import cronch/syntax/elab
import cronch/syntax/parse
import gleam/io
import gleam/list
import gleam/string

// ── FOL source ────────────────────────────────────────────────────────────────

const src = "
-- Propositions as types, proofs as terms (Curry-Howard correspondence)
--
-- P : Type 0   means  P is a proposition
-- t : P        means  t is a proof of P
-- P -> Q       means  P implies Q       (non-dependent function type)
-- Eq A a b     means  a equals b in A

-- Tautology: P implies P
define id_proof : fun (P : Type 0) -> P -> P :=
  lam (P : Type 0) => lam (p : P) => p

-- Modus ponens: (P -> Q) and P gives Q
define mp : fun (P : Type 0) -> fun (Q : Type 0) -> (P -> Q) -> P -> Q :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (f : P -> Q) => lam (x : P) => f x

-- Hypothetical syllogism: chain implications
define hs : fun (P : Type 0) -> fun (Q : Type 0) -> fun (R : Type 0) ->
              (P -> Q) -> (Q -> R) -> P -> R :=
  lam (P : Type 0) => lam (Q : Type 0) => lam (R : Type 0) =>
    lam (pq : P -> Q) => lam (qr : Q -> R) => lam (p : P) =>
      qr (pq p)

-- Weakening: a proof of P still holds under an extra assumption Q
define weakening : fun (P : Type 0) -> fun (Q : Type 0) -> P -> Q -> P :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (p : P) => lam (q : Q) => p

-- Permutation: swap two premises
define perm : fun (P : Type 0) -> fun (Q : Type 0) -> fun (R : Type 0) ->
                (P -> Q -> R) -> Q -> P -> R :=
  lam (P : Type 0) => lam (Q : Type 0) => lam (R : Type 0) =>
    lam (f : P -> Q -> R) => lam (q : Q) => lam (p : P) =>
      f p q

-- Contraction: two copies of the same premise can be merged
define contraction : fun (P : Type 0) -> fun (Q : Type 0) ->
                       (P -> P -> Q) -> P -> Q :=
  lam (P : Type 0) => lam (Q : Type 0) =>
    lam (f : P -> P -> Q) => lam (p : P) =>
      f p p

-- Reflexivity of equality: every term equals itself
define eq_refl : fun (A : Type 0) -> fun (a : A) -> Eq A a a :=
  lam (A : Type 0) => lam (a : A) => refl A a

-- Leibniz substitution at Type 0 (instantiated to the identity predicate):
-- if a = b then any proof about a is a proof about b... via the identity predicate
-- this version: if Eq Type0 P Q and we have a proof of P, we have Q (via refl + coercion)
-- skipped: requires J-elimination which is not built-in; left as an open hole
hole subst_j : fun (P : Type 0) -> fun (Q : Type 0) -> Eq (Type 0) P Q -> P -> Q
"

// ── Main ──────────────────────────────────────────────────────────────────────

pub fn main() -> Nil {
  io.println("cronch FOL demo -- Curry-Howard proof checker")
  io.println(string.repeat("-", 50))

  case parse.parse_module(src) {
    Error(parse.ParseError(msg)) -> io.println("parse error: " <> msg)
    Ok(items) ->
      case elab.elaborate_module(items) {
        Error(err) -> io.println("elab error: " <> describe_elab_error(err))
        Ok(m) -> run_checks(m)
      }
  }
}

fn run_checks(m: elab.ElabModule) -> Nil {
  let results =
    list.map(m.entries, fn(entry) {
      case entry.kind {
        elab.HoleKind ->
          #(entry.name, Skipped)
        _ ->
          case kernel.check(m.store, kernel.empty(), entry.term, entry.declared_ty) {
            Ok(_) -> #(entry.name, Proved)
            Error(_) -> #(entry.name, Failed)
          }
      }
    })

  list.each(results, fn(r) {
    let #(name, verdict) = r
    io.println("[" <> verdict_label(verdict) <> "] " <> name)
  })

  let proved = list.count(results, fn(r) { r.1 == Proved })
  let holes = list.count(results, fn(r) { r.1 == Skipped })
  let total = list.length(results)
  io.println(string.repeat("-", 50))
  io.println(
    int_str(proved)
    <> "/"
    <> int_str(total - holes)
    <> " proofs verified"
    <> case holes > 0 {
      True -> ", " <> int_str(holes) <> " open hole(s)"
      False -> ""
    },
  )
}

type Verdict {
  Proved
  Failed
  Skipped
}

fn verdict_label(v: Verdict) -> String {
  case v {
    Proved -> " OK  "
    Failed -> "FAIL "
    Skipped -> "HOLE "
  }
}

fn describe_elab_error(e: elab.ElabError) -> String {
  case e {
    elab.UnboundName(n) -> "unbound name `" <> n <> "`"
    elab.TrustedInProofPosition -> "trusted in proof position"
    elab.UnboundProc(n) -> "unbound proc `" <> n <> "`"
    elab.DuplicateName(n) -> "duplicate name `" <> n <> "`"
  }
}

fn int_str(n: Int) -> String {
  case n {
    0 -> "0"
    _ -> do_int_str(n, "")
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

