import cronch/digest
import cronch/hash
import cronch/kernel
import cronch/oracle
import cronch/term
import gleam/list
import gleam/option.{None, Some}
import gleeunit/should

// ── helpers ───────────────────────────────────────────────────────────────────

fn no_store() -> oracle.Store {
  fn(_) { None }
}

fn make_store(entries: List(#(digest.Digest, term.Term))) -> oracle.Store {
  fn(d: digest.Digest) {
    case list.find(entries, fn(e) { e.0 == d }) {
      Ok(#(_, t)) -> Some(t)
      Error(_) -> None
    }
  }
}

// ── refl oracle ───────────────────────────────────────────────────────────────

pub fn refl_oracle_closes_closed_eq_goal_test() {
  // Eq(Sort(1), Sort(0), Sort(0)) is closed by Refl(Sort(1), Sort(0))
  let problem = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))
  let out = oracle.solve(no_store(), oracle.refl_oracle(), problem)
  oracle.is_closed(out) |> should.be_true
  out.artifact |> should.equal(term.Refl(term.Sort(1), term.Sort(0)))
  out.stuck |> should.equal([])
}

pub fn refl_oracle_closes_eq_under_binders_test() {
  // Lam(Sort(0), Lam(Var(0), Hole(0, Eq(Var(1), Var(0), Var(0)))))
  // The hole is in context [A : Sort(0), a : A]; it should fill with Refl(Var(1), Var(0))
  let start =
    term.Lam(
      term.Sort(0),
      term.Lam(term.Var(0), term.Hole(0, term.Eq(term.Var(1), term.Var(0), term.Var(0)))),
    )
  let out = oracle.solve_state(no_store(), oracle.refl_oracle(), start)
  oracle.is_closed(out) |> should.be_true
  let expected =
    term.Lam(
      term.Sort(0),
      term.Lam(term.Var(0), term.Refl(term.Var(1), term.Var(0))),
    )
  out.artifact |> should.equal(expected)
}

pub fn refl_oracle_gives_up_on_non_eq_goal_test() {
  // Sort(0) is not an Eq -- the oracle proposes nothing, hole stays stuck.
  let g = oracle.Goal(id: 0, cx: kernel.empty(), target: term.Sort(0))
  oracle.refl_oracle()(g)
  |> should.equal(None)
}

pub fn refl_oracle_gives_up_on_heterogeneous_eq_test() {
  // Eq A a b where a != b structurally -- oracle gives up (kernel would also reject).
  let g =
    oracle.Goal(
      id: 0,
      cx: kernel.empty(),
      target: term.Eq(term.Sort(0), term.Sort(0), term.Sort(1)),
    )
  oracle.refl_oracle()(g)
  |> should.equal(None)
}

// ── library oracle ────────────────────────────────────────────────────────────

pub fn library_oracle_proposes_matching_candidate_test() {
  let g_eq = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))
  let c_eq = term.Refl(term.Sort(1), term.Sort(0))
  let g_id = term.Pi(term.Sort(0), term.Pi(term.Var(0), term.Var(1)))
  let c_id = term.Lam(term.Sort(0), term.Lam(term.Var(0), term.Var(0)))
  let lib = oracle.library_oracle([#(g_eq, c_eq), #(g_id, c_id)])

  let make_goal = fn(t) { oracle.Goal(id: 7, cx: kernel.empty(), target: t) }
  lib(make_goal(g_eq))
  |> should.equal(Some(oracle.Proposal(hole: 7, term: c_eq)))
  lib(make_goal(g_id))
  |> should.equal(Some(oracle.Proposal(hole: 7, term: c_id)))
  // No matching candidate
  lib(make_goal(term.Sort(0)))
  |> should.equal(None)
}

pub fn library_oracle_wrong_store_fails_closed_test() {
  // Round 1: admit obj1 = Sort(0) at addr1.
  let obj1 = term.Sort(0)
  let addr1 = hash.hash(digest.Blake3, obj1)

  // Round 2: candidate Const(addr1) for goal Sort(1).
  // With the grown store: Const(addr1) resolves to Sort(0) : Sort(1), closes.
  let goal2 = term.Sort(1)
  let proof2 = term.Const(addr1)
  let lib = oracle.library_oracle([#(goal2, proof2)])

  let grown = make_store([#(addr1, obj1)])
  let r = oracle.solve(grown, lib, goal2)
  oracle.is_closed(r) |> should.be_true
  r.artifact |> should.equal(proof2)

  // With empty store: Const(addr1) is unresolvable, hole stays stuck.
  let r2 = oracle.solve(no_store(), lib, goal2)
  oracle.is_closed(r2) |> should.be_false
}

// ── verifying store ───────────────────────────────────────────────────────────

pub fn verifying_store_passes_honest_store_test() {
  let t = term.Pi(term.Sort(0), term.Var(0))
  let d = hash.hash(digest.Blake3, t)
  let inner = make_store([#(d, t)])
  let vs = oracle.verifying_store(inner)
  vs(d) |> should.equal(Some(t))
}

pub fn verifying_store_rejects_mislabeled_object_test() {
  // Store the address of Sort(5) but map it to Sort(0) -- a lie.
  let claimed = hash.hash(digest.Blake3, term.Sort(5))
  let lie = term.Sort(0)
  let inner = make_store([#(claimed, lie)])
  let vs = oracle.verifying_store(inner)
  // The verifying store detects the mismatch and returns None.
  vs(claimed) |> should.equal(None)
}

pub fn verifying_store_passes_none_through_test() {
  let d = hash.hash(digest.Blake3, term.Sort(3))
  let vs = oracle.verifying_store(no_store())
  vs(d) |> should.equal(None)
}

// ── solve ─────────────────────────────────────────────────────────────────────

pub fn solve_wraps_in_single_hole_test() {
  // solve(problem) = solve_state(Hole(0, problem))
  // If the oracle closes it, artifact has no holes.
  let problem = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))
  let out = oracle.solve(no_store(), oracle.refl_oracle(), problem)
  oracle.is_closed(out) |> should.be_true
}

pub fn unsolvable_goal_stuck_not_corrupted_test() {
  // The refl oracle cannot inhabit Sort(0); the hole stays open.
  let out = oracle.solve(no_store(), oracle.refl_oracle(), term.Sort(0))
  oracle.is_closed(out) |> should.be_false
  out.stuck |> list.length |> should.equal(1)
  out.stuck
  |> list.map(fn(pair) { pair.1 })
  |> should.equal([term.Sort(0)])
}

pub fn bad_proposal_never_corrupts_state_test() {
  // A library oracle with a wrong candidate (Sort(5) for a goal of Sort(0)).
  // The kernel rejects it; the hole stays stuck.
  let lib = oracle.library_oracle([#(term.Sort(0), term.Sort(5))])
  let out = oracle.solve(no_store(), lib, term.Sort(0))
  oracle.is_closed(out) |> should.be_false
  out.stuck |> list.length |> should.equal(1)
}

pub fn multiple_holes_filled_in_order_test() {
  // Two holes with the same goal type: Eq(Sort(1), Sort(0), Sort(0)).
  // refl_oracle closes each in pre-order.
  let eq_goal = term.Eq(term.Sort(1), term.Sort(0), term.Sort(0))
  let start = term.App(term.Hole(0, eq_goal), term.Hole(1, eq_goal))
  let out = oracle.solve_state(no_store(), oracle.refl_oracle(), start)
  oracle.is_closed(out) |> should.be_true
  let refl = term.Refl(term.Sort(1), term.Sort(0))
  out.artifact |> should.equal(term.App(refl, refl))
}

// ── is_closed ─────────────────────────────────────────────────────────────────

pub fn is_closed_no_holes_test() {
  let out =
    oracle.Outcome(artifact: term.Sort(0), stuck: [])
  oracle.is_closed(out) |> should.be_true
}

pub fn is_closed_with_hole_test() {
  let out =
    oracle.Outcome(
      artifact: term.Hole(0, term.Sort(0)),
      stuck: [#(0, term.Sort(0))],
    )
  oracle.is_closed(out) |> should.be_false
}
