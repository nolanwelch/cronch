import cronch/digest
import cronch/kernel
import cronch/pubkey
import cronch/term
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

// ── helpers ───────────────────────────────────────────────────────────────────

fn no_store() {
  kernel.no_store()
}

fn make_store(entries: List(#(digest.Digest, term.Term))) {
  fn(d: digest.Digest) {
    case list.find(entries, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> None
    }
  }
}

fn fake_digest(b: Int) -> digest.Digest {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
  >>
  digest.Digest(digest.Blake3, bytes)
}

fn fake_pubkey(b: Int) -> pubkey.PublicKey {
  let bytes = <<
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
    b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
  >>
  pubkey.PublicKey(pubkey.Ed25519, bytes)
}

fn empty() {
  kernel.empty()
}

fn push(cx, ty) {
  kernel.push(cx, ty)
}

// ── shift ─────────────────────────────────────────────────────────────────────

pub fn shift_var_above_cutoff_test() {
  kernel.shift(1, 0, term.Var(0))
  |> should.equal(term.Var(1))
}

pub fn shift_var_at_cutoff_test() {
  // Var(1) with cutoff=1: 1 >= 1, so shifts to Var(2)
  kernel.shift(1, 1, term.Var(1))
  |> should.equal(term.Var(2))
}

pub fn shift_var_below_cutoff_test() {
  // Var(0) with cutoff=1: 0 < 1, no change
  kernel.shift(1, 1, term.Var(0))
  |> should.equal(term.Var(0))
}

pub fn shift_negative_test() {
  kernel.shift(-1, 0, term.Var(1))
  |> should.equal(term.Var(0))
}

pub fn shift_sort_unchanged_test() {
  kernel.shift(5, 0, term.Sort(3))
  |> should.equal(term.Sort(3))
}

pub fn shift_under_pi_bound_var_test() {
  // Pi(Sort(0), Var(0)): Var(0) in codomain is bound (cutoff becomes 1 under binder)
  kernel.shift(1, 0, term.Pi(term.Sort(0), term.Var(0)))
  |> should.equal(term.Pi(term.Sort(0), term.Var(0)))
}

pub fn shift_under_pi_free_var_test() {
  // Pi(Sort(0), Var(1)): Var(1) under one binder is free (refers outside)
  // shift(1,0,...): under binder cutoff=1, Var(1) >= 1, becomes Var(2)
  kernel.shift(1, 0, term.Pi(term.Sort(0), term.Var(1)))
  |> should.equal(term.Pi(term.Sort(0), term.Var(2)))
}

// ── subst ─────────────────────────────────────────────────────────────────────

pub fn subst_hits_test() {
  kernel.subst(0, term.Sort(0), term.Var(0))
  |> should.equal(term.Sort(0))
}

pub fn subst_misses_test() {
  kernel.subst(0, term.Sort(0), term.Var(1))
  |> should.equal(term.Var(1))
}

pub fn subst_bound_var_in_body_unchanged_test() {
  // subst(0, Sort(0), Lam(Sort(0), Var(0)))
  // Under the binder j becomes 1; Var(0) != 1, unchanged.
  kernel.subst(0, term.Sort(0), term.Lam(term.Sort(0), term.Var(0)))
  |> should.equal(term.Lam(term.Sort(0), term.Var(0)))
}

pub fn subst_free_var_in_body_test() {
  // subst(0, Sort(0), Lam(Sort(0), Var(1)))
  // Under the binder j=1; Var(1) matches; substitute shift(1,0,Sort(0)) = Sort(0).
  kernel.subst(0, term.Sort(0), term.Lam(term.Sort(0), term.Var(1)))
  |> should.equal(term.Lam(term.Sort(0), term.Sort(0)))
}

pub fn subst_does_not_capture_test() {
  // subst(0, Var(0), Lam(Sort(0), Var(1)))
  // s = Var(0); in body, s is shifted to Var(1), then replaces Var(1).
  // Result: Lam(Sort(0), Var(1)) -- substituting Var(0) for the outer Var(0)
  // which appears as Var(1) inside the binder.
  kernel.subst(0, term.Var(0), term.Lam(term.Sort(0), term.Var(1)))
  |> should.equal(term.Lam(term.Sort(0), term.Var(1)))
}

// ── beta ──────────────────────────────────────────────────────────────────────

pub fn beta_identity_test() {
  // beta(Sort(3), Var(0)): body is the bound variable, substitutes to Sort(3)
  kernel.beta(term.Sort(3), term.Var(0))
  |> should.equal(term.Sort(3))
}

pub fn beta_constant_body_test() {
  // beta(Sort(3), Sort(0)): body ignores the argument
  kernel.beta(term.Sort(3), term.Sort(0))
  |> should.equal(term.Sort(0))
}

pub fn beta_outer_var_shifts_down_test() {
  // beta(Sort(0), Var(1)): Var(1) refers to the variable just outside the lambda.
  // After beta, that outer variable is now Var(0).
  kernel.beta(term.Sort(0), term.Var(1))
  |> should.equal(term.Var(0))
}

pub fn beta_no_capture_test() {
  // beta(Var(0), Lam(Sort(0), Var(1))): arg is Var(0).
  // body = Lam(Sort(0), Var(1)).  Var(1) under one binder refers to the thing
  // being substituted.  shift(1,0,Var(0)) = Var(1); subst(0, Var(1), body):
  //   under the inner binder j=1, Var(1) matches, replaced by shift(1,0,Var(1))=Var(2).
  // Then shift(-1,0,Lam(Sort(0),Var(2))) = Lam(Sort(0),Var(1)).
  // (The outer variable Var(0) propagated inward without capture.)
  kernel.beta(term.Var(0), term.Lam(term.Sort(0), term.Var(1)))
  |> should.equal(term.Lam(term.Sort(0), term.Var(1)))
}

// ── whnf ──────────────────────────────────────────────────────────────────────

pub fn whnf_sort_is_stuck_test() {
  kernel.whnf(no_store(), term.Sort(0))
  |> should.equal(term.Sort(0))
}

pub fn whnf_beta_reduces_test() {
  // App(Lam(Sort(0), Var(0)), Sort(3)) --> Sort(3)
  let id = term.Lam(term.Sort(0), term.Var(0))
  kernel.whnf(no_store(), term.App(id, term.Sort(3)))
  |> should.equal(term.Sort(3))
}

pub fn whnf_nested_beta_test() {
  // K := Lam(Sort(0), Lam(Sort(0), Var(1)))  -- const combinator
  // App(App(K, Sort(1)), Sort(2)) --> Sort(1)
  let k = term.Lam(term.Sort(0), term.Lam(term.Sort(0), term.Var(1)))
  let t = term.App(term.App(k, term.Sort(1)), term.Sort(2))
  kernel.whnf(no_store(), t)
  |> should.equal(term.Sort(1))
}

pub fn whnf_resolves_const_test() {
  let d = fake_digest(10)
  let store = make_store([#(d, term.Sort(0))])
  kernel.whnf(store, term.Const(d))
  |> should.equal(term.Sort(0))
}

pub fn whnf_unresolvable_const_is_stuck_test() {
  let d = fake_digest(11)
  kernel.whnf(no_store(), term.Const(d))
  |> should.equal(term.Const(d))
}

pub fn whnf_does_not_reduce_under_binder_test() {
  // Lam body is a redex but whnf does not go under binders
  let id = term.Lam(term.Sort(0), term.Var(0))
  let t = term.Lam(term.Sort(0), term.App(id, term.Var(0)))
  kernel.whnf(no_store(), t)
  |> should.equal(t)
}

// ── normalize ─────────────────────────────────────────────────────────────────

pub fn normalize_sort_test() {
  kernel.normalize(no_store(), term.Sort(0))
  |> should.equal(term.Sort(0))
}

pub fn normalize_reduces_inside_lam_test() {
  let id = term.Lam(term.Sort(0), term.Var(0))
  // Lam(Sort(0), App(id, Var(0))) -- body reduces to Var(0)
  let t = term.Lam(term.Sort(0), term.App(id, term.Var(0)))
  kernel.normalize(no_store(), t)
  |> should.equal(term.Lam(term.Sort(0), term.Var(0)))
}

pub fn normalize_reduces_inside_eq_test() {
  let id = term.Lam(term.Sort(0), term.Var(0))
  let t = term.Eq(term.Sort(0), term.App(id, term.Sort(0)), term.Sort(0))
  kernel.normalize(no_store(), t)
  |> should.equal(term.Eq(term.Sort(0), term.Sort(0), term.Sort(0)))
}

pub fn normalize_trusted_is_inert_test() {
  let host = fake_pubkey(1)
  let proc = fake_digest(2)
  let id = term.Lam(term.Sort(0), term.Var(0))
  // Trusted arg has a redex; normalize reduces it but the Trusted node stays
  let node = term.Trusted(host, proc, term.App(id, term.Sort(0)), term.Sort(0))
  kernel.normalize(no_store(), node)
  |> should.equal(term.Trusted(host, proc, term.Sort(0), term.Sort(0)))
}

// ── def_eq ────────────────────────────────────────────────────────────────────

pub fn def_eq_reflexive_sort_test() {
  kernel.def_eq(no_store(), term.Sort(0), term.Sort(0))
  |> should.be_true
}

pub fn def_eq_different_sorts_test() {
  kernel.def_eq(no_store(), term.Sort(0), term.Sort(1))
  |> should.be_false
}

pub fn def_eq_beta_test() {
  let id = term.Lam(term.Sort(0), term.Var(0))
  let redex = term.App(id, term.Sort(3))
  kernel.def_eq(no_store(), redex, term.Sort(3))
  |> should.be_true
}

pub fn def_eq_delta_test() {
  let d = fake_digest(20)
  let store = make_store([#(d, term.Pi(term.Sort(0), term.Sort(0)))])
  kernel.def_eq(store, term.Const(d), term.Pi(term.Sort(0), term.Sort(0)))
  |> should.be_true
}

pub fn def_eq_trusted_structural_test() {
  let host = fake_pubkey(1)
  let proc = fake_digest(2)
  let n1 = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let n2 = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  kernel.def_eq(no_store(), n1, n2)
  |> should.be_true
}

pub fn def_eq_trusted_different_args_test() {
  let host = fake_pubkey(1)
  let proc = fake_digest(2)
  let n1 = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  let n2 = term.Trusted(host, proc, term.Sort(1), term.Sort(0))
  kernel.def_eq(no_store(), n1, n2)
  |> should.be_false
}

// ── infer: conformance vectors ────────────────────────────────────────────────

pub fn infer_poly_id_test() {
  // Lam(Sort(0), Lam(Var(0), Var(0))) : Pi(Sort(0), Pi(Var(0), Var(1)))
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  let expected = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  kernel.infer(no_store(), empty(), id)
  |> should.equal(Ok(expected))
}

pub fn infer_poly_id_pi_type_test() {
  // Pi(Sort(0), Pi(Var(0), Var(1))) : Sort(1)
  let t = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  kernel.infer(no_store(), empty(), t)
  |> should.equal(Ok(term.Sort(1)))
}

pub fn infer_sort_succ_test() {
  kernel.infer(no_store(), empty(), term.Sort(7))
  |> should.equal(Ok(term.Sort(8)))
}

pub fn infer_type_in_type_rejected_test() {
  // Sort(0) is not a Pi, so applying it to anything is NotAFunction
  let bad = term.App(term.Sort(0), term.Sort(0))
  kernel.infer(no_store(), empty(), bad)
  |> should.equal(Error(kernel.NotAFunction(term.Sort(1))))
}

pub fn infer_unbound_var_rejected_test() {
  kernel.infer(no_store(), empty(), term.Var(0))
  |> should.equal(Error(kernel.UnboundVar(0)))
}

pub fn infer_eq_refl_shape_test() {
  // Refl(Sort(1), Sort(0)) : Eq(Sort(1), Sort(0), Sort(0))
  let t = term.Refl(term.Sort(1), term.Sort(0))
  let expected = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))
  kernel.infer(no_store(), empty(), t)
  |> should.equal(Ok(expected))
}

// ── infer: additional tests ───────────────────────────────────────────────────

pub fn infer_sort_max_universe_overflow_test() {
  // Sort(max_universe) has no successor
  kernel.infer(no_store(), empty(), term.Sort(4_294_967_295))
  |> should.equal(Error(kernel.UniverseOverflow))
}

pub fn infer_lam_wrong_arg_type_test() {
  // App(Lam(Sort(0), Var(0)), Sort(5)): Sort(5) has type Sort(6), domain is Sort(0)
  let f = term.Lam(term.Sort(0), term.Var(0))
  let bad = term.App(f, term.Sort(5))
  kernel.infer(no_store(), empty(), bad)
  |> should.be_error
}

pub fn infer_var_in_context_test() {
  // Context [Sort(0)]: Var(0) has type Sort(0)
  let cx = push(empty(), term.Sort(0))
  kernel.infer(no_store(), cx, term.Var(0))
  |> should.equal(Ok(term.Sort(0)))
}

pub fn infer_var_type_shifted_in_context_test() {
  // Context [A : Sort(0), a : A]: that is, push Sort(0) then push Var(0).
  // Var(1) = A, type = Sort(0).
  // Var(0) = a, type = shift(1, 0, Var(0)) = Var(1) = A.
  let cx = push(push(empty(), term.Sort(0)), term.Var(0))
  kernel.infer(no_store(), cx, term.Var(0))
  |> should.equal(Ok(term.Var(1)))
}

pub fn infer_refl_in_context_test() {
  // Context [A : Sort(0), a : A]: refl A a : Eq A a a
  let cx = push(push(empty(), term.Sort(0)), term.Var(0))
  let refl = term.Refl(term.Var(1), term.Var(0))
  let expected = term.Eq(term.Var(1), term.Var(0), term.Var(0))
  kernel.infer(no_store(), cx, refl)
  |> should.equal(Ok(expected))
}

pub fn infer_const_resolves_test() {
  let d = fake_digest(42)
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  let store = make_store([#(d, id)])
  kernel.infer(store, empty(), term.Const(d))
  |> should.equal(Ok(term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))))
}

pub fn infer_const_unresolved_test() {
  let d = fake_digest(9)
  kernel.infer(no_store(), empty(), term.Const(d))
  |> should.equal(Error(kernel.Unresolved(d)))
}

pub fn infer_hole_well_formed_test() {
  // A hole whose goal type is well-formed infers to that goal type
  let goal = term.Pi(term.Sort(0), term.Sort(0))
  let h = term.Hole(7, goal)
  kernel.infer(no_store(), empty(), h)
  |> should.equal(Ok(goal))
}

pub fn infer_hole_ill_formed_goal_rejected_test() {
  // A hole whose goal type is itself ill-typed is rejected
  let bad_goal = term.App(term.Sort(0), term.Sort(0))
  let h = term.Hole(0, bad_goal)
  kernel.infer(no_store(), empty(), h)
  |> should.be_error
}

// ── check ─────────────────────────────────────────────────────────────────────

pub fn check_id_at_pi_type_test() {
  let id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  let id_ty = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  kernel.check(no_store(), empty(), id, id_ty)
  |> should.equal(Ok(Nil))
}

pub fn check_type_in_type_rejected_test() {
  // Sort(0) : Sort(1), not Sort(0)
  kernel.check(no_store(), empty(), term.Sort(0), term.Sort(0))
  |> should.be_error
}

pub fn check_mismatch_reports_types_test() {
  // infer Sort(0) = Sort(1); checking against Sort(99) should fail with Mismatch
  kernel.check(no_store(), empty(), term.Sort(0), term.Sort(99))
  |> should.equal(
    Error(kernel.Mismatch(expected: term.Sort(99), actual: term.Sort(1))),
  )
}

pub fn check_up_to_beta_test() {
  // id : Pi(Sort(0), Sort(0))
  // Check against Pi(App(K, Sort(1)), Sort(0)) where K = lam _ -> Sort(0).
  // The domain is a beta-redex that reduces to Sort(0), so the types are
  // definitionally equal even though they differ syntactically.
  let k = term.Lam(term.Sort(1), term.Sort(0))
  let redex_dom = term.App(k, term.Sort(1))
  let goal = term.Pi(redex_dom, term.Sort(0))
  let id = term.Lam(term.Sort(0), term.Var(0))
  kernel.check(no_store(), empty(), id, goal)
  |> should.equal(Ok(Nil))
}

// ── Trusted ───────────────────────────────────────────────────────────────────

pub fn trusted_checks_weakly_test() {
  // proc signature: Pi(Sort(0), Var(0))  -- (T : Type0) -> T
  // In context [X : Sort(0)]: Trusted(host, proc, Var(0), Var(0)) : Var(0)
  let proc = fake_digest(200)
  let proc_sig = term.Pi(term.Sort(0), term.Var(0))
  let store = make_store([#(proc, proc_sig)])
  let host = fake_pubkey(1)
  let cx = push(empty(), term.Sort(0))
  let node = term.Trusted(host, proc, term.Var(0), term.Var(0))
  kernel.infer(store, cx, node)
  |> should.equal(Ok(term.Var(0)))
}

pub fn trusted_rejects_wrong_result_type_test() {
  // proc: (T:Type0) -> Type0; claim result_ty = Sort(5), but codomain[args] = Sort(0)
  let proc = fake_digest(201)
  let proc_sig = term.Pi(term.Sort(0), term.Sort(0))
  let store = make_store([#(proc, proc_sig)])
  let host = fake_pubkey(1)
  let cx = push(empty(), term.Sort(0))
  let node = term.Trusted(host, proc, term.Var(0), term.Sort(5))
  kernel.infer(store, cx, node)
  |> should.be_error
}

pub fn trusted_rejects_wrong_argument_type_test() {
  // proc: (T:Type0) -> Type0; args = Sort(5) has type Sort(6), not Sort(0)
  let proc = fake_digest(202)
  let proc_sig = term.Pi(term.Sort(0), term.Sort(0))
  let store = make_store([#(proc, proc_sig)])
  let host = fake_pubkey(1)
  let node = term.Trusted(host, proc, term.Sort(5), term.Sort(0))
  kernel.infer(store, empty(), node)
  |> should.be_error
}

pub fn trusted_rejects_unresolvable_proc_test() {
  let proc = fake_digest(203)
  let host = fake_pubkey(1)
  let node = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  kernel.infer(no_store(), empty(), node)
  |> should.equal(Error(kernel.Unresolved(proc)))
}

pub fn trusted_normalize_inert_test() {
  let host = fake_pubkey(1)
  let proc = fake_digest(2)
  let node = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  kernel.normalize(no_store(), node)
  |> should.equal(node)
}

pub fn trusted_def_eq_structural_test() {
  let host = fake_pubkey(1)
  let proc = fake_digest(2)
  let node = term.Trusted(host, proc, term.Sort(0), term.Sort(0))
  kernel.def_eq(no_store(), node, node)
  |> should.be_true
}

// ── differential: def_eq agrees with normalize-then-compare ───────────────────

fn corpus() -> List(term.Term) {
  let id = term.Lam(term.Sort(0), term.Var(0))
  [
    term.Sort(0),
    term.Sort(1),
    term.Var(0),
    term.Pi(term.Sort(0), term.Sort(0)),
    term.App(id, term.Sort(3)),
    term.Sort(3),
    term.App(id, term.App(id, term.Sort(2))),
    term.Sort(2),
    term.Lam(term.Sort(0), term.App(term.Lam(term.Var(0), term.Var(0)), term.Var(0))),
    term.Lam(term.Sort(0), term.Var(0)),
    term.Eq(term.Sort(0), term.App(id, term.Sort(0)), term.Sort(0)),
    term.Eq(term.Sort(0), term.Sort(0), term.Sort(0)),
  ]
}

pub fn def_eq_agrees_with_normalize_test() {
  let s = no_store()
  let c = corpus()
  list.each(c, fn(a) {
    list.each(c, fn(b) {
      let via_defeq = kernel.def_eq(s, a, b)
      let via_norm =
        kernel.normalize(s, a) == kernel.normalize(s, b)
      via_defeq |> should.equal(via_norm)
    })
  })
}

pub fn def_eq_delta_agrees_with_normalize_test() {
  let d = fake_digest(77)
  let store = make_store([#(d, term.Pi(term.Sort(0), term.Sort(0)))])
  let a = term.Const(d)
  let b = term.Pi(term.Sort(0), term.Sort(0))
  kernel.def_eq(store, a, b)
  |> should.be_true
  kernel.normalize(store, a)
  |> should.equal(kernel.normalize(store, b))
}
