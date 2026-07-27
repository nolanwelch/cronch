import cronch/digest
import cronch/rewrite
import cronch/term
import gleam/dict
import gleam/option.{None, Some}
import gleeunit/should

// ── helpers ───────────────────────────────────────────────────────────────────

fn fake_digest(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

// ── match_pattern: base cases ─────────────────────────────────────────────────

pub fn match_var_always_binds_test() {
  rewrite.match_pattern(rewrite.PVar(0), term.Sort(5), dict.new())
  |> should.equal(Some(dict.from_list([#(0, term.Sort(5))])))
}

pub fn match_sort_exact_test() {
  rewrite.match_pattern(rewrite.PSort(3), term.Sort(3), dict.new())
  |> should.equal(Some(dict.new()))
}

pub fn match_sort_mismatch_test() {
  rewrite.match_pattern(rewrite.PSort(3), term.Sort(4), dict.new())
  |> should.equal(None)
}

pub fn match_const_exact_test() {
  let d = fake_digest(1)
  rewrite.match_pattern(rewrite.PConst(d), term.Const(d), dict.new())
  |> should.equal(Some(dict.new()))
}

pub fn match_const_mismatch_test() {
  let d1 = fake_digest(1)
  let d2 = fake_digest(2)
  rewrite.match_pattern(rewrite.PConst(d1), term.Const(d2), dict.new())
  |> should.equal(None)
}

pub fn match_app_binds_argument_test() {
  let d = fake_digest(1)
  let pattern = rewrite.PApp(rewrite.PConst(d), rewrite.PVar(0))
  let t = term.App(term.Const(d), term.Sort(2))
  rewrite.match_pattern(pattern, t, dict.new())
  |> should.equal(Some(dict.from_list([#(0, term.Sort(2))])))
}

pub fn match_refl_binds_both_fields_test() {
  let pattern = rewrite.PRefl(rewrite.PVar(0), rewrite.PVar(1))
  let t = term.Refl(term.Sort(0), term.Sort(1))
  rewrite.match_pattern(pattern, t, dict.new())
  |> should.equal(
    Some(dict.from_list([#(0, term.Sort(0)), #(1, term.Sort(1))])),
  )
}

// ── a matching rule fires; a non-matching rule doesn't ────────────────────────

pub fn rule_fires_end_to_end_test() {
  // fst (pair a b) --> a, applied to fst (pair Sort(3) Sort(4))
  let pair_d = fake_digest(10)
  let fst_d = fake_digest(11)
  let lhs =
    rewrite.PApp(
      rewrite.PConst(fst_d),
      rewrite.PApp(
        rewrite.PApp(rewrite.PConst(pair_d), rewrite.PVar(0)),
        rewrite.PVar(1),
      ),
    )
  let rhs = term.Var(0)
  let t =
    term.App(
      term.Const(fst_d),
      term.App(term.App(term.Const(pair_d), term.Sort(3)), term.Sort(4)),
    )
  let assert Some(slots) = rewrite.match_pattern(lhs, t, dict.new())
  rewrite.instantiate(rhs, slots)
  |> should.equal(term.Sort(3))
}

pub fn rule_does_not_fire_on_wrong_head_test() {
  // The same fst-pattern does not match a term headed by some other Const.
  let fst_d = fake_digest(11)
  let other_d = fake_digest(12)
  let lhs = rewrite.PApp(rewrite.PConst(fst_d), rewrite.PVar(0))
  let t = term.App(term.Const(other_d), term.Sort(0))
  rewrite.match_pattern(lhs, t, dict.new())
  |> should.equal(None)
}

pub fn rule_does_not_fire_on_wrong_shape_test() {
  // A pattern requiring an application does not match a bare Const, even
  // the right one -- shape matters, not just the head.
  let fst_d = fake_digest(11)
  let lhs = rewrite.PApp(rewrite.PConst(fst_d), rewrite.PVar(0))
  rewrite.match_pattern(lhs, term.Const(fst_d), dict.new())
  |> should.equal(None)
}

// ── repeated pattern variables must match equal subterms ──────────────────────

pub fn repeated_pattern_var_matches_equal_subterms_test() {
  let lhs = rewrite.PApp(rewrite.PVar(0), rewrite.PVar(0))
  rewrite.match_pattern(lhs, term.App(term.Sort(1), term.Sort(1)), dict.new())
  |> should.equal(Some(dict.from_list([#(0, term.Sort(1))])))
}

pub fn repeated_pattern_var_rejects_unequal_subterms_test() {
  let lhs = rewrite.PApp(rewrite.PVar(0), rewrite.PVar(0))
  rewrite.match_pattern(lhs, term.App(term.Sort(1), term.Sort(2)), dict.new())
  |> should.equal(None)
}

pub fn repeated_pattern_var_is_structural_not_def_eq_test() {
  // Sort(0) and App(Lam(Sort(0), Var(0)), Sort(0)) are def_eq (both reduce
  // to Sort(0)) but not structurally equal. A repeated pattern variable
  // requires structural equality (see rewrite.gleam's match_pattern doc
  // comment for why), so this must fail to match even though a def_eq-based
  // matcher would accept it.
  let id_applied_to_sort0 =
    term.App(term.Lam(term.Sort(0), term.Var(0)), term.Sort(0))
  let lhs = rewrite.PApp(rewrite.PVar(0), rewrite.PVar(0))
  rewrite.match_pattern(
    lhs,
    term.App(term.Sort(0), id_applied_to_sort0),
    dict.new(),
  )
  |> should.equal(None)
}

// ── instantiate: shift discipline ──────────────────────────────────────────────

pub fn instantiate_no_binders_is_plain_substitution_test() {
  let slots = dict.from_list([#(0, term.Sort(7))])
  rewrite.instantiate(term.App(term.Var(0), term.Var(0)), slots)
  |> should.equal(term.App(term.Sort(7), term.Sort(7)))
}

pub fn instantiate_shifts_across_one_binder_test() {
  // rhs = Lam(Sort(0), Var(1)): the body references pattern slot 0 from one
  // binder deep, so Var(1) (not Var(0)) is how the rule's rhs must spell
  // "whatever slot 0 is" once under a binder -- exactly mirroring how
  // kernel.beta's arg gets shift(1, 0, arg) before substitution. Slot 0 is
  // bound to Var(0) (a variable free relative to the rule's own top level);
  // once placed one binder deeper it must become Var(1) or it would
  // silently refer to the wrong (newly introduced) binder instead of the
  // outer context.
  let slots = dict.from_list([#(0, term.Var(0))])
  rewrite.instantiate(term.Lam(term.Sort(0), term.Var(1)), slots)
  |> should.equal(term.Lam(term.Sort(0), term.Var(1)))
}

pub fn instantiate_shifts_by_full_depth_under_nested_binders_test() {
  // Two binders deep: a slot value that is itself Var(2) (free relative to
  // the rule's top level) must shift by the full nesting depth (2), landing
  // on Var(4), not just +1.
  let slots = dict.from_list([#(0, term.Var(2))])
  let rhs = term.Pi(term.Sort(0), term.Lam(term.Sort(0), term.Var(2)))
  rewrite.instantiate(rhs, slots)
  |> should.equal(term.Pi(term.Sort(0), term.Lam(term.Sort(0), term.Var(4))))
}

pub fn instantiate_does_not_touch_genuinely_bound_variables_test() {
  // rhs = Lam(Sort(0), Var(0)): Var(0) here is bound BY this Lam (k < depth),
  // not a reference to any pattern slot, so it must pass through untouched
  // regardless of what slot 0 holds.
  let slots = dict.from_list([#(0, term.Sort(99))])
  rewrite.instantiate(term.Lam(term.Sort(0), term.Var(0)), slots)
  |> should.equal(term.Lam(term.Sort(0), term.Var(0)))
}

// ── hard constraint: Hole/Trusted are never structurally matched ──────────────

pub fn pvar_opaquely_carries_a_hole_test() {
  // PVar matches a Hole (it matches anything) but only opaquely: the Hole
  // reappears verbatim through instantiate, never inspected or rebuilt.
  let h = term.Hole(3, term.Sort(0))
  rewrite.match_pattern(rewrite.PVar(0), h, dict.new())
  |> should.equal(Some(dict.from_list([#(0, h)])))
}

pub fn non_var_patterns_never_match_hole_test() {
  let h = term.Hole(3, term.Sort(0))
  rewrite.match_pattern(rewrite.PSort(0), h, dict.new()) |> should.equal(None)
  rewrite.match_pattern(rewrite.PConst(fake_digest(1)), h, dict.new())
  |> should.equal(None)
  rewrite.match_pattern(
    rewrite.PApp(rewrite.PVar(0), rewrite.PVar(1)),
    h,
    dict.new(),
  )
  |> should.equal(None)
}
