/// The type-checking kernel.
///
/// This is the entire trusted surface of the system. Every function here is
/// pure: ill-typed terms, unresolvable references, universe overflow, and
/// a fuel-exhausted reduction are reported as TypeError, never a panic.
/// That liveness guarantee holds under `Limited(n)` Fuel by construction.
/// Under `Unlimited` Fuel it does not: a non-terminating rule
/// set can make whnf/normalize/def_eq/infer/check hang, exactly the way an
/// infinite loop in any other pure function would. That is a caller's
/// explicit, visible choice (see the Fuel doc comment below), never a
/// hidden kernel default.
///
/// shift/subst are the highest-risk code in the whole project. Most soundness
/// bugs live there. The implementations below are the deliberately obvious
/// ones. Do not optimize them.
///
/// Trusted surface (public functions called from outside the kernel):
///   whnf, normalize, def_eq, infer, check --
///   infer_reporting, check_reporting (the same derivations, returning a
///   Report of the reductions they performed instead of discarding it;
///   trust.gleam builds trust sets from those) --
///   whnf_with_uses, normalize_with_uses (reduction-scoped reporting, kept
///   for callers that want the uses of a reduction rather than of a check).
///
/// Reporting is observation, never decision. infer/check are wrappers over
/// the reporting implementations with the record thrown away, so no accept or
/// reject outcome depends on whether anybody is listening.
///
/// shift, subst, beta are also public because they are useful to callers
/// (e.g. elaboration, pretty-printing) and are pure/total regardless of Fuel.
import cronch/digest.{type Digest}
import cronch/pubkey.{type PublicKey}
import cronch/rewrite.{type Rule}
import cronch/term.{type Term}
import gleam/dict
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

/// Maximum allowed universe level (u32::MAX). Sort(max_universe) has no
/// successor: attempting to infer its type is UniverseOverflow.
const max_universe: Int = 4_294_967_295

// ── Store, SignatureStore, Environment, and Context ────────────────────────────────────

/// A pure read-only map from content address to term.
/// The only thing the kernel reads beyond its direct arguments.
pub type Store =
  fn(Digest) -> Option(Term)

/// A store that resolves nothing. Use for closed terms with no Const nodes.
pub fn no_store() -> Store {
  fn(_) { None }
}

/// The type of an axiomatic constant: a symbol with a declared type and no
/// body. Consulted before `definitions` by both `whnf` and `infer` -- an axiomatic
/// constant never delta-unfolds. It reduces, if at all, only through rules
/// in `RuleStore` (see rewrite.gleam). This is how new type formers (Sigma,
/// an equality eliminator, ...) get added without growing `Term` itself.
pub type SignatureStore =
  fn(Digest) -> Option(Term)

/// A signature store that resolves nothing.
pub fn empty_signatures() -> SignatureStore {
  fn(_) { None }
}

/// Re-exported so call sites that only need the RuleStore type or "no
/// rules" don't need a direct import of cronch/rewrite.
pub type RuleStore =
  rewrite.RuleStore

pub fn empty_rules() -> RuleStore {
  rewrite.empty_rules()
}

/// Everything the kernel reads beyond its direct term/context arguments,
/// bundled so it threads as one value through whnf/normalize/def_eq/infer/
/// check instead of three.
///
/// Precondition, not checked at runtime: `definitions` and `signatures` must be disjoint
/// -- no Digest may be a key in both. A digest is supposed to denote exactly
/// one thing (a definition with a body, or an axiom with none), never both.
/// Both `whnf` and `infer` consult `signatures` first, so if this precondition is
/// violated, `signatures` silently wins for that digest and `definitions`'s entry is
/// never seen. This is consistent with how a `Store` has always been "a
/// pure function the caller is responsible for constructing correctly" --
/// checking it here would add a lookup-time cost to every single Const
/// resolution to guard against a builder bug that content-addressing
/// already makes unlikely (an honest builder never assigns one digest two
/// different meanings).
///
/// Second precondition, same standing and a sharper hazard: `definitions`
/// and `rules` must be disjoint too -- no Digest may have both a body and a
/// rewrite rule keyed to it. `whnf_go` resolves a `Const` by trying
/// `signatures` (rules only), then `definitions` (delta unfold, and NO
/// rewrite attempt), then rules. So for a digest in both, whichever one is
/// present decides how it reduces: with the definition installed the rules
/// keyed to that digest never fire at all, and withholding the definition
/// brings them back. A verdict is then a function of which of two
/// interchangeable-looking descriptions of "what this digest means" the
/// caller happened to install, which is precisely the property a
/// content-addressed system exists to rule out -- and it can flip a
/// rejection into an acceptance (see kernel_test's
/// `withholding_a_conflicting_definition_flips_reject_to_accept_test`).
///
/// It is likewise not checked at runtime, for the reason above: the check
/// belongs where the environment is built, once, not on the resolution path
/// of every `Const` in every check forever. `definition_rule_conflicts`
/// below is that check, for a builder to call.
pub type Environment {
  Environment(definitions: Store, signatures: SignatureStore, rules: RuleStore)
}

/// Wrap a bare definitional store as an Environment with no axiomatic constants and
/// no rewrite rules -- the mechanical adaptation for every call site that
/// only ever needed a Store before Environment existed.
pub fn environment_from_store(definitions: Store) -> Environment {
  Environment(
    definitions: definitions,
    signatures: empty_signatures(),
    rules: empty_rules(),
  )
}

/// The digests in `candidates` that violate the definitions/rules
/// disjointness precondition: a body in `definitions` and at least one
/// rewrite rule in `rules`. `[]` means no violation among the candidates.
///
/// Takes the candidates explicitly because an `Environment` is three pure
/// functions with no key listing and cannot be enumerated. A builder knows
/// the digests it installed; nobody else can recover them.
///
/// Deliberately NOT called from `whnf`, `infer` or anything they reach. A
/// per-`Const`-resolution check would tax every lookup of every check
/// forever to catch, once, a bug in the code that assembled the
/// Environment -- the same trade the doc comment above declines for
/// definitions/signatures. This is the check that code runs on itself.
pub fn definition_rule_conflicts(
  environment: Environment,
  candidates: List(Digest),
) -> List(Digest) {
  list.filter(candidates, fn(d) {
    case environment.definitions(d) {
      None -> False
      Some(_) -> environment.rules(d) != []
    }
  })
}

/// A typing context: a stack of variable types, Var(0)'s type at the head.
pub opaque type Context {
  Context(types: List(Term))
}

/// The empty context.
pub fn empty() -> Context {
  Context([])
}

/// Extend the context: the new term becomes the type of Var(0).
pub fn push(cx: Context, typ: Term) -> Context {
  Context([typ, ..cx.types])
}

/// The type of Var(n) in cx, shifted into the current context.
///
/// The stored type was recorded n+1 binders ago, so its free variables must
/// be shifted up by n+1. Getting this wrong is the classic soundness bug.
fn type_of_var(cx: Context, n: Int) -> Option(Term) {
  lookup(cx.types, n, 0)
}

fn lookup(types: List(Term), n: Int, depth: Int) -> Option(Term) {
  case types {
    [] -> None
    [typ, ..] if n == 0 -> Some(shift(depth + 1, 0, typ))
    [_, ..rest] -> lookup(rest, n - 1, depth + 1)
  }
}

// ── Fuel ──────────────────────────────────────────────────────────────────────

/// A reduction budget. `Limited(n)` guarantees whnf/normalize/def_eq/infer/
/// check terminate -- reporting `FuelExhausted` rather than hanging -- even
/// against a rule set that turns out to be non-terminating in practice.
/// Confluence and termination of a rule set are never checked anywhere in
/// this codebase (see rewrite.gleam's Rule doc comment); Limited fuel is the
/// kernel's only defense against that. `Unlimited` turns the defense off: a
/// non-terminating rule set then hangs the caller's process, exactly like an
/// infinite loop in any other pure function would. That is a legitimate,
/// explicit choice ("I have already convinced myself this rule set
/// terminates, and I don't want an artificial ceiling on legitimate deep
/// reductions"), never a hidden default -- there is no bare-Int overload and
/// no default parameter; every entry point below takes a Fuel value.
pub type Fuel {
  Limited(Int)
  Unlimited
}

/// A generous, fixed budget for the test suite and any other call site that
/// is not specifically exercising fuel exhaustion. Large enough that no
/// legitimate reduction in this codebase's tests comes close (the deepest
/// reduction chains here are a few dozen steps); small enough that a
/// non-terminating rule set still fails in well under a second on the BEAM.
pub const test_fuel: Fuel = Limited(100_000)

// Consume one unit of fuel. Unlimited is never decremented and never runs
// out; Limited(0) is exhausted.
fn consume(fuel: Fuel) -> Result(Fuel, TypeError) {
  case fuel {
    Unlimited -> Ok(Unlimited)
    Limited(0) -> Error(FuelExhausted)
    Limited(n) -> Ok(Limited(n - 1))
  }
}

// ── RuleUse ───────────────────────────────────────────────────────────────────

/// One rule set invoked while reducing a term, identified by its signer and
/// content hash. Returned by whnf_with_uses/normalize_with_uses so
/// trust.gleam can recompute an artifact's rule-set trust dependencies by
/// re-running the exact reduction the kernel performs, rather than
/// statically guessing which rules a term *could* invoke (undecidable in
/// general, and would over- or under-report). See trust.gleam for how this
/// feeds into trust sets.
pub type RuleUse {
  RuleUse(author: PublicKey, rule_set: Digest)
}

/// How a caller says which signed rule set each rule belongs to.
///
/// A `Rule` carries no author and no rule-set hash, and `Environment.rules`
/// hands back bare rules, so nothing reachable from an Environment can
/// attribute a firing rule to a rule set. That attribution is a trust-layer
/// concern, so it arrives as a separate function rather than being baked into
/// the Environment the kernel reads.
///
/// For `check_reporting`/`infer_reporting` this is a TAGGING function and
/// nothing more. Those two reduce under `environment.rules`, and consult a
/// Provenance only to name the rule set a firing rule came from, so a caller
/// cannot substitute the rules a verdict is computed under by passing a
/// Provenance that disagrees with the Environment (see `attributed`).
/// `whnf_with_uses`/`normalize_with_uses` are the deliberate exception: they
/// are reduction-scoped tools whose question IS "what would these rules do to
/// this term", and they decide nothing.
pub type Provenance =
  fn(Digest) -> List(#(RuleUse, Rule))

// ── Report ────────────────────────────────────────────────────────────────────

/// What a typing derivation did, as opposed to what it decided.
///
/// `rule_uses` is every rule set invoked anywhere in the derivation, in firing
/// order and with repeats -- reducing the term, checking a binder's domain,
/// whnf-ing a function's type, converting during a def_eq. Callers that want a
/// set deduplicate it (trust.gleam does).
///
/// `fuel_used` is the number of reduction steps the derivation performed: one
/// per beta reduction, one per delta unfolding, one per rewrite-rule
/// application. It is NOT `Fuel` arithmetic. `Fuel` is a termination guard
/// that is consumed only by rule application and is never threaded back out of
/// a nested call, so "fuel remaining" does not exist to subtract from. This
/// counter observes steps the checker takes anyway; nothing here gates,
/// short-circuits, or is consulted by any decision.
///
/// Both fields are pure functions of the inputs: no clock, no process
/// identity, no map iteration, nothing that could differ between two runs of
/// the same check.
pub type Report {
  Report(rule_uses: List(RuleUse), fuel_used: Int)
}

// A derivation's accumulating record, generic over the tag carried alongside
// each rule so that the untracked entry points can run the identical code with
// the tag type Nil and discard the result. Private: `Report` is the public
// shape.
type Trace(u) {
  Trace(uses: List(u), steps: Int)
}

fn empty_trace() -> Trace(u) {
  Trace([], 0)
}

// One reduction step, no rule attributed to it (beta, delta).
fn step() -> Trace(u) {
  Trace([], 1)
}

// One reduction step attributed to a rule set.
fn used(tag: u) -> Trace(u) {
  Trace([tag], 1)
}

fn merge(traces: List(Trace(u))) -> Trace(u) {
  Trace(
    list.flat_map(traces, fn(t) { t.uses }),
    list.fold(traces, 0, fn(acc, t) { acc + t.steps }),
  )
}

// The rule source a REPORTING call reduces under: the Environment's own
// rules -- never the caller's -- each tagged with the RuleUse the caller's
// Provenance attributes to it, or with the digest itself when the caller
// attributed nothing. Same rules, same order, same reduction as `untracked`;
// only the tag differs, so there is one reduction path and a reported verdict
// is the plain verdict. A rule the caller offers but the Environment does not
// hold is not here and cannot fire; a rule the Environment holds but the
// caller did not attribute fires anyway and taints the trace.
fn attributed(
  environment: Environment,
  provenance: Provenance,
) -> fn(Digest) -> List(#(Result(RuleUse, Digest), Rule)) {
  fn(d) {
    let tags = provenance(d)
    list.map(environment.rules(d), fn(rule) {
      case list.find(tags, fn(tagged) { tagged.1 == rule }) {
        Ok(#(rule_use, _)) -> #(Ok(rule_use), rule)
        Error(Nil) -> #(Error(d), rule)
      }
    })
  }
}

// Fail closed: a derivation in which some rule fired unattributed has no
// honest Report, because the missing entry is exactly the one a policy would
// have refused. Reported as the digest whose rules could not be attributed.
fn report_of_attributed(
  trace: Trace(Result(RuleUse, Digest)),
) -> Result(Report, TypeError) {
  case result.all(trace.uses) {
    Ok(uses) -> Ok(Report(rule_uses: uses, fuel_used: trace.steps))
    Error(d) -> Error(Unresolved(d))
  }
}

// The provenance an untracked call uses: the Environment's own rules, each
// tagged with Nil. Same rules, same order, same reduction -- only the tag
// differs, so there is no second reduction path to drift.
fn untracked(environment: Environment) -> fn(Digest) -> List(#(Nil, Rule)) {
  fn(d) { list.map(environment.rules(d), fn(r) { #(Nil, r) }) }
}

// ── TypeError ─────────────────────────────────────────────────────────────────

/// Why a term failed to type-check. Never a panic.
pub type TypeError {
  UnboundVar(Int)
  ExpectedSort(Term)
  NotAFunction(Term)
  Mismatch(expected: Term, actual: Term)
  /// A Const in neither `definitions` nor `signatures` -- or, on the
  /// reporting path only, a digest whose rules fired unattributed by the
  /// caller's Provenance (see `check_reporting`). Both fail closed.
  Unresolved(Digest)
  UniverseOverflow
  TrustedProcNotAType(Term)
  TrustedProcNotPi(Term)
  TrustedCodomainMismatch(expected: Term, actual: Term)
  /// A rewrite-rule application ran out of Limited fuel. Never produced
  /// under Unlimited fuel -- see the Fuel doc comment.
  FuelExhausted
}

// ── Shift and substitution ────────────────────────────────────────────────────

/// shift(d, cutoff, t): add d to every free variable Var(k) with k >= cutoff.
/// The cutoff rises by one under each binder. d may be negative (used in beta).
pub fn shift(d: Int, cutoff: Int, t: Term) -> Term {
  case t {
    term.Var(k) ->
      case k >= cutoff {
        True -> term.Var(k + d)
        False -> term.Var(k)
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(shift(d, cutoff, a), shift(d, cutoff + 1, b))
    term.Lam(a, b) -> term.Lam(shift(d, cutoff, a), shift(d, cutoff + 1, b))
    term.App(f, a) -> term.App(shift(d, cutoff, f), shift(d, cutoff, a))
    term.Eq(typ, a, b) ->
      term.Eq(shift(d, cutoff, typ), shift(d, cutoff, a), shift(d, cutoff, b))
    term.Refl(typ, a) -> term.Refl(shift(d, cutoff, typ), shift(d, cutoff, a))
    term.Hole(id, typ) -> term.Hole(id, shift(d, cutoff, typ))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(host, proc, shift(d, cutoff, args), shift(d, cutoff, rty))
  }
}

/// subst(j, s, t): substitute s for Var(j) in t.
/// Under each binder, j becomes j+1 and s is shifted up by one.
pub fn subst(j: Int, s: Term, t: Term) -> Term {
  case t {
    term.Var(k) ->
      case k == j {
        True -> s
        False -> t
      }
    term.Sort(_) | term.Const(_) -> t
    term.Pi(a, b) -> term.Pi(subst(j, s, a), subst(j + 1, shift(1, 0, s), b))
    term.Lam(a, b) -> term.Lam(subst(j, s, a), subst(j + 1, shift(1, 0, s), b))
    term.App(f, a) -> term.App(subst(j, s, f), subst(j, s, a))
    term.Eq(typ, a, b) ->
      term.Eq(subst(j, s, typ), subst(j, s, a), subst(j, s, b))
    term.Refl(typ, a) -> term.Refl(subst(j, s, typ), subst(j, s, a))
    term.Hole(id, typ) -> term.Hole(id, subst(j, s, typ))
    term.Trusted(host, proc, args, rty) ->
      term.Trusted(host, proc, subst(j, s, args), subst(j, s, rty))
  }
}

/// Beta-reduce App(Lam(_, body), arg).
/// beta(arg, body) = shift(-1, 0, subst(0, shift(1, 0, arg), body))
pub fn beta(arg: Term, body: Term) -> Term {
  let arg_up = shift(1, 0, arg)
  let substituted = subst(0, arg_up, body)
  shift(-1, 0, substituted)
}

// ── Reduction ─────────────────────────────────────────────────────────────────
//
// whnf is implemented as whnf_go, generic over the "tag" carried alongside
// each rule (type parameter `u` below). The untracked, public `whnf` tags
// every rule with Nil and throws the tags away; the reporting entry points
// tag every rule with its owning rule set's RuleUse and return the tags that
// actually fired. There is exactly one reduction algorithm either way -- the
// public `whnf` is not a separate, simpler implementation that could drift
// from the one trust.gleam depends on for soundness-relevant accounting. The
// same is true one level up: infer/check are wrappers over infer_go/check_go,
// so a reported derivation and a plain one are the same derivation.
//
// Design note on Fuel and nesting: whnf_go does NOT thread an updated Fuel
// value back out of nested calls (e.g. reducing the function position of an
// App before trying rules on the resulting spine reuses the same Fuel value
// the caller passed in, rather than an amount reduced by whatever the
// nested call consumed). This is deliberately simpler than a single global
// counter threaded through the whole call. It is still safe: any single
// reduction chain that alternates forever between "reduce the head" and
// "try a rule on the result" is bounded by (structural depth of the
// original term) x (fuel), which is finite for a finite input term, so
// whnf_go still always terminates or reports FuelExhausted -- it just is
// not a perfectly tight bound on total work. Fuel exhaustion is a
// termination guard, not a precise cost accounting mechanism (see the Fuel
// doc comment); this trade favors simplicity. Trace.steps below is the
// separate, exact count -- it observes, it never gates.

/// Weak head normal form: beta/delta/rule-reduce the head until it is stuck.
/// Never reduces under binders or inside arguments.
/// An unresolvable Const is left in place (it is a type error in infer, not here).
pub fn whnf(
  environment: Environment,
  fuel: Fuel,
  t: Term,
) -> Result(Term, TypeError) {
  use #(term, _trace) <- result.try(whnf_go(
    environment,
    untracked(environment),
    fuel,
    t,
  ))
  Ok(term)
}

/// Like whnf, but also returns every RuleUse that fired while reducing t.
pub fn whnf_with_uses(
  environment: Environment,
  provenance: Provenance,
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(RuleUse)), TypeError) {
  use #(term, trace) <- result.try(whnf_go(environment, provenance, fuel, t))
  Ok(#(term, trace.uses))
}

fn whnf_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, Trace(u)), TypeError) {
  case t {
    term.App(f, a) -> {
      use #(fh, tr1) <- result.try(whnf_go(environment, provenance, fuel, f))
      case fh {
        term.Lam(_, body) -> {
          // A beta step. Counted, never gated: consume/Fuel is untouched
          // here, exactly as before.
          use #(final, tr2) <- result.try(whnf_go(
            environment,
            provenance,
            fuel,
            beta(a, body),
          ))
          Ok(#(final, merge([tr1, step(), tr2])))
        }
        stuck -> {
          use #(final, tr2) <- result.try(try_rewrite(
            environment,
            provenance,
            fuel,
            term.App(stuck, a),
          ))
          Ok(#(final, merge([tr1, tr2])))
        }
      }
    }
    // signatures is consulted first, same precondition as infer's Const case
    // (see Environment's doc comment): an axiomatic constant never delta-unfolds,
    // it only ever reduces through rules.
    term.Const(d) ->
      case environment.signatures(d) {
        Some(_) -> try_rewrite(environment, provenance, fuel, t)
        None ->
          case environment.definitions(d) {
            None -> try_rewrite(environment, provenance, fuel, t)
            Some(def) -> {
              // A delta step. Counted, never gated.
              use #(final, tr) <- result.try(whnf_go(
                environment,
                provenance,
                fuel,
                def,
              ))
              Ok(#(final, merge([step(), tr])))
            }
          }
      }
    other -> Ok(#(other, empty_trace()))
  }
}

// Try every rule keyed to t's head Const (if it has one) against t itself.
// On the first match, consume one unit of fuel and keep reducing the
// result. On no match, t is genuinely stuck -- returned unchanged, same as
// a plain unresolvable Const was before rules existed.
fn try_rewrite(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, Trace(u)), TypeError) {
  case head_const(t) {
    None -> Ok(#(t, empty_trace()))
    Some(d) ->
      case find_match(provenance(d), t) {
        None -> Ok(#(t, empty_trace()))
        Some(#(tag, rewritten)) -> {
          use fuel2 <- result.try(consume(fuel))
          use #(final, tr) <- result.try(whnf_go(
            environment,
            provenance,
            fuel2,
            rewritten,
          ))
          Ok(#(final, merge([used(tag), tr])))
        }
      }
  }
}

// The Const at the head of an application spine, e.g. head_const(f a b) =
// head_const(f). None for anything not headed by a Const (Lam, Sort, ...).
fn head_const(t: Term) -> Option(Digest) {
  case t {
    term.Const(d) -> Some(d)
    term.App(f, _) -> head_const(f)
    _ -> None
  }
}

fn find_match(tagged: List(#(u, Rule)), t: Term) -> Option(#(u, Term)) {
  case tagged {
    [] -> None
    [#(tag, rule), ..rest] ->
      case rewrite.match_pattern(rule.lhs, t, dict.new()) {
        Some(slots) -> Some(#(tag, rewrite.instantiate(rule.rhs, slots)))
        None -> find_match(rest, t)
      }
  }
}

/// Full normal form: whnf, then recurse into every subterm.
/// Trusted is inert: its fields are normalized but the node never reduces.
pub fn normalize(
  environment: Environment,
  fuel: Fuel,
  t: Term,
) -> Result(Term, TypeError) {
  use #(term, _trace) <- result.try(normalize_go(
    environment,
    untracked(environment),
    fuel,
    t,
  ))
  Ok(term)
}

/// Like normalize, but also returns every RuleUse that fired anywhere in
/// the term.
///
/// Reduction-scoped, and therefore NOT the right input to an authorization
/// decision: a rule set exercised only while checking a type annotation
/// never appears here, because no type annotation is normalized. Use
/// `infer_reporting` / `check_reporting` for that -- see trust.gleam.
pub fn normalize_with_uses(
  environment: Environment,
  provenance: Provenance,
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, List(RuleUse)), TypeError) {
  use #(term, trace) <- result.try(normalize_go(
    environment,
    provenance,
    fuel,
    t,
  ))
  Ok(#(term, trace.uses))
}

fn normalize_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  t: Term,
) -> Result(#(Term, Trace(u)), TypeError) {
  use #(h, tr1) <- result.try(whnf_go(environment, provenance, fuel, t))
  case h {
    term.Var(_) | term.Sort(_) | term.Const(_) -> Ok(#(h, tr1))
    term.Pi(a, b) -> {
      use #(na, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        a,
      ))
      use #(nb, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        b,
      ))
      Ok(#(term.Pi(na, nb), merge([tr1, tr2, tr3])))
    }
    term.Lam(a, b) -> {
      use #(na, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        a,
      ))
      use #(nb, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        b,
      ))
      Ok(#(term.Lam(na, nb), merge([tr1, tr2, tr3])))
    }
    term.App(f, a) -> {
      use #(nf, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        f,
      ))
      use #(na, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        a,
      ))
      Ok(#(term.App(nf, na), merge([tr1, tr2, tr3])))
    }
    term.Eq(typ, a, b) -> {
      use #(nty, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        typ,
      ))
      use #(na, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        a,
      ))
      use #(nb, tr4) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        b,
      ))
      Ok(#(term.Eq(nty, na, nb), merge([tr1, tr2, tr3, tr4])))
    }
    term.Refl(typ, a) -> {
      use #(nty, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        typ,
      ))
      use #(na, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        a,
      ))
      Ok(#(term.Refl(nty, na), merge([tr1, tr2, tr3])))
    }
    term.Hole(id, typ) -> {
      use #(nty, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        typ,
      ))
      Ok(#(term.Hole(id, nty), merge([tr1, tr2])))
    }
    term.Trusted(host, proc, args, rty) -> {
      use #(nargs, tr2) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        args,
      ))
      use #(nrty, tr3) <- result.try(normalize_go(
        environment,
        provenance,
        fuel,
        rty,
      ))
      Ok(#(term.Trusted(host, proc, nargs, nrty), merge([tr1, tr2, tr3])))
    }
  }
}

/// Definitional equality: whnf both sides, then compare heads structurally.
/// Up to beta, delta, and rewrite rules. No eta in v0.
/// Trusted nodes compare structurally: equal host/proc and def_eq args/result_typ.
///
/// Syntactically identical terms are answered `Ok(True)` without reducing
/// anything. `Term` carries de Bruijn indices and no names, so `==` on two
/// terms IS alpha-equivalence, and alpha-equivalent terms are definitionally
/// equal by reflexivity -- there is nothing for a reduction to discover.
///
/// DELIBERATE BEHAVIOUR CHANGE: a comparison of two equal terms whose
/// reduction would have exhausted `Limited` fuel used to report
/// `Error(FuelExhausted)` and now reports `Ok(True)`. That is the intended
/// direction. FuelExhausted is a termination guard, not a judgement (see the
/// Fuel doc comment); answering a question we can settle by reflexivity is
/// strictly more informative than refusing to answer it, it can only ever
/// turn a non-verdict into `True` and never a `False` into a `True`, and the
/// answer no longer depends on how much budget the caller happened to pass.
pub fn def_eq(
  environment: Environment,
  fuel: Fuel,
  a: Term,
  b: Term,
) -> Result(Bool, TypeError) {
  use #(eq, _trace) <- result.try(def_eq_go(
    environment,
    untracked(environment),
    fuel,
    a,
    b,
  ))
  Ok(eq)
}

fn def_eq_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  a: Term,
  b: Term,
) -> Result(#(Bool, Trace(u)), TypeError) {
  case a == b {
    // The fast path. The trace is empty because it is honest: no beta, delta
    // or rule application happened, so there is no step to count and no rule
    // set to attribute. That is exactly what `Report.fuel_used` documents
    // itself to be -- "the number of reduction steps the derivation
    // performed" -- so a check that takes this path reports a smaller
    // fuel_used than it used to, for work it genuinely no longer does.
    True -> Ok(#(True, empty_trace()))
    False -> def_eq_reduced(environment, provenance, fuel, a, b)
  }
}

// The general case: reduce both sides to whnf, then compare heads. Reached
// only when the two terms are not already syntactically equal.
fn def_eq_reduced(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  a: Term,
  b: Term,
) -> Result(#(Bool, Trace(u)), TypeError) {
  use #(wa, tr1) <- result.try(whnf_go(environment, provenance, fuel, a))
  use #(wb, tr2) <- result.try(whnf_go(environment, provenance, fuel, b))
  let here = merge([tr1, tr2])
  case wa, wb {
    term.Var(i), term.Var(j) -> Ok(#(i == j, here))
    term.Sort(i), term.Sort(j) -> Ok(#(i == j, here))
    term.Const(d1), term.Const(d2) -> Ok(#(d1 == d2, here))
    term.Pi(a1, b1), term.Pi(a2, b2) ->
      and_eq(environment, provenance, fuel, here, a1, a2, b1, b2)
    term.Lam(a1, b1), term.Lam(a2, b2) ->
      and_eq(environment, provenance, fuel, here, a1, a2, b1, b2)
    term.App(f1, x1), term.App(f2, x2) ->
      and_eq(environment, provenance, fuel, here, f1, f2, x1, x2)
    term.Eq(t1, a1, b1), term.Eq(t2, a2, b2) ->
      and3_eq(environment, provenance, fuel, here, t1, t2, a1, a2, b1, b2)
    term.Refl(t1, a1), term.Refl(t2, a2) ->
      and_eq(environment, provenance, fuel, here, t1, t2, a1, a2)
    term.Hole(i, t1), term.Hole(j, t2) ->
      case i == j {
        False -> Ok(#(False, here))
        True -> {
          use #(eq, tr) <- result.try(def_eq_go(
            environment,
            provenance,
            fuel,
            t1,
            t2,
          ))
          Ok(#(eq, merge([here, tr])))
        }
      }
    term.Trusted(h1, p1, a1, r1), term.Trusted(h2, p2, a2, r2) ->
      case h1 == h2 && p1 == p2 {
        False -> Ok(#(False, here))
        True -> and_eq(environment, provenance, fuel, here, a1, a2, r1, r2)
      }
    _, _ -> Ok(#(False, here))
  }
}

fn and_eq(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  acc: Trace(u),
  x1: Term,
  x2: Term,
  y1: Term,
  y2: Term,
) -> Result(#(Bool, Trace(u)), TypeError) {
  use #(e1, tr1) <- result.try(def_eq_go(environment, provenance, fuel, x1, x2))
  case e1 {
    // Short-circuit exactly where the untracked version always did: the
    // second comparison is not performed, so its reductions are not counted.
    False -> Ok(#(False, merge([acc, tr1])))
    True -> {
      use #(e2, tr2) <- result.try(def_eq_go(
        environment,
        provenance,
        fuel,
        y1,
        y2,
      ))
      Ok(#(e2, merge([acc, tr1, tr2])))
    }
  }
}

fn and3_eq(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  acc: Trace(u),
  x1: Term,
  x2: Term,
  y1: Term,
  y2: Term,
  z1: Term,
  z2: Term,
) -> Result(#(Bool, Trace(u)), TypeError) {
  use #(e1, tr1) <- result.try(def_eq_go(environment, provenance, fuel, x1, x2))
  case e1 {
    False -> Ok(#(False, merge([acc, tr1])))
    True ->
      and_eq(environment, provenance, fuel, merge([acc, tr1]), y1, y2, z1, z2)
  }
}

// ── Type checking ─────────────────────────────────────────────────────────────

/// Infer the type of t in context cx. Returns a well-formed type or an error.
/// The returned type is always valid; check relies on this invariant.
pub fn infer(
  environment: Environment,
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(Term, TypeError) {
  use #(typ, _trace) <- result.try(infer_go(
    environment,
    untracked(environment),
    fuel,
    cx,
    t,
  ))
  Ok(typ)
}

/// Check that t has type expected in context cx.
/// Sound because infer returns only well-formed types: success means expected
/// is def_eq to a genuine inferred type.
pub fn check(
  environment: Environment,
  fuel: Fuel,
  cx: Context,
  t: Term,
  expected: Term,
) -> Result(Nil, TypeError) {
  use _trace <- result.try(check_go(
    environment,
    untracked(environment),
    fuel,
    cx,
    t,
    expected,
  ))
  Ok(Nil)
}

/// `infer`, plus a Report of what the derivation did.
///
/// Same derivation, same verdict, same errors: this is not a second typing
/// path, it is the one path with its tags kept instead of discarded. Every
/// reduction the checker performs anywhere -- reducing the term, checking a
/// binder's domain, whnf-ing a function's type, converting during a
/// def_eq -- is recorded at the point it happens.
pub fn infer_reporting(
  environment: Environment,
  provenance: Provenance,
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(#(Term, Report), TypeError) {
  use #(typ, trace) <- result.try(infer_go(
    environment,
    attributed(environment, provenance),
    fuel,
    cx,
    t,
  ))
  use report <- result.try(report_of_attributed(trace))
  Ok(#(typ, report))
}

/// `check`, plus a Report of what the derivation did. See `infer_reporting`.
///
/// Reduces under `environment.rules`, exactly as plain `check` does:
/// `provenance` names rule sets, it does not supply them. So a caller cannot
/// have the verdict computed under one set of rules while the Basis records
/// another, and cannot reach an acceptance here that plain `check` against
/// the same Environment would not reach.
///
/// A rule that fires without `provenance` attributing it is
/// `Error(Unresolved(d))` on the digest it was keyed to -- fail-closed,
/// because the alternative is a Report omitting a rule set the acceptance
/// rested on. Reachable only when a caller's Provenance disagrees with its
/// own Environment.
pub fn check_reporting(
  environment: Environment,
  provenance: Provenance,
  fuel: Fuel,
  cx: Context,
  t: Term,
  expected: Term,
) -> Result(Report, TypeError) {
  use trace <- result.try(check_go(
    environment,
    attributed(environment, provenance),
    fuel,
    cx,
    t,
    expected,
  ))
  report_of_attributed(trace)
}

fn infer_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(#(Term, Trace(u)), TypeError) {
  case t {
    term.Var(n) ->
      case type_of_var(cx, n) {
        None -> Error(UnboundVar(n))
        Some(typ) -> Ok(#(typ, empty_trace()))
      }

    term.Sort(u) ->
      case u >= max_universe {
        True -> Error(UniverseOverflow)
        False -> Ok(#(term.Sort(u + 1), empty_trace()))
      }

    term.Pi(a, b) -> {
      use #(i, tr1) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx,
        a,
      ))
      let cx2 = push(cx, a)
      use #(j, tr2) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx2,
        b,
      ))
      Ok(#(term.Sort(int.max(i, j)), merge([tr1, tr2])))
    }

    term.Lam(a, b) -> {
      // The binder's domain is checked here, and any rule that fires while
      // checking it is recorded here. This is the reduction the old
      // reconstruct-by-normalizing trust set could not see.
      use #(_, tr1) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx,
        a,
      ))
      let cx2 = push(cx, a)
      use #(body_typ, tr2) <- result.try(infer_go(
        environment,
        provenance,
        fuel,
        cx2,
        b,
      ))
      Ok(#(term.Pi(a, body_typ), merge([tr1, tr2])))
    }

    term.App(f, x) -> {
      use #(f_typ, tr1) <- result.try(infer_go(
        environment,
        provenance,
        fuel,
        cx,
        f,
      ))
      use #(w, tr2) <- result.try(whnf_go(environment, provenance, fuel, f_typ))
      case w {
        term.Pi(domain, codomain) -> {
          use tr3 <- result.try(check_go(
            environment,
            provenance,
            fuel,
            cx,
            x,
            domain,
          ))
          Ok(#(beta(x, codomain), merge([tr1, tr2, tr3])))
        }
        other -> Error(NotAFunction(other))
      }
    }

    term.Eq(typ, a, b) -> {
      use #(i, tr1) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx,
        typ,
      ))
      use tr2 <- result.try(check_go(environment, provenance, fuel, cx, a, typ))
      use tr3 <- result.try(check_go(environment, provenance, fuel, cx, b, typ))
      Ok(#(term.Sort(i), merge([tr1, tr2, tr3])))
    }

    term.Refl(typ, a) -> {
      use #(_, tr1) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx,
        typ,
      ))
      use tr2 <- result.try(check_go(environment, provenance, fuel, cx, a, typ))
      Ok(#(term.Eq(typ, a, a), merge([tr1, tr2])))
    }

    // signatures is consulted first: an axiomatic constant's declared type is
    // returned directly, and it is never unfolded via definitions. See Environment's doc
    // comment for the precondition this relies on (definitions/signatures disjoint).
    term.Const(d) ->
      case environment.signatures(d) {
        Some(typ) -> Ok(#(typ, empty_trace()))
        None ->
          case environment.definitions(d) {
            None -> Error(Unresolved(d))
            Some(def) -> infer_go(environment, provenance, fuel, empty(), def)
          }
      }

    term.Hole(_, goal) -> {
      use #(_, tr) <- result.try(infer_sort_go(
        environment,
        provenance,
        fuel,
        cx,
        goal,
      ))
      Ok(#(goal, tr))
    }

    term.Trusted(_, proc, args, result_typ) ->
      infer_trusted(environment, provenance, fuel, cx, proc, args, result_typ)
  }
}

fn check_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  cx: Context,
  t: Term,
  expected: Term,
) -> Result(Trace(u), TypeError) {
  use #(actual, tr1) <- result.try(infer_go(
    environment,
    provenance,
    fuel,
    cx,
    t,
  ))
  // The conversion check. Rules firing here are recorded here -- this is the
  // other place the reconstructed trust set was blind to.
  use #(eq, tr2) <- result.try(def_eq_go(
    environment,
    provenance,
    fuel,
    actual,
    expected,
  ))
  case eq {
    True -> Ok(merge([tr1, tr2]))
    False -> Error(Mismatch(expected: expected, actual: actual))
  }
}

// ── Private helpers ───────────────────────────────────────────────────────────

fn infer_sort_go(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  cx: Context,
  t: Term,
) -> Result(#(Int, Trace(u)), TypeError) {
  use #(typ, tr1) <- result.try(infer_go(environment, provenance, fuel, cx, t))
  use #(w, tr2) <- result.try(whnf_go(environment, provenance, fuel, typ))
  case w {
    term.Sort(u) -> Ok(#(u, merge([tr1, tr2])))
    found -> Error(ExpectedSort(found))
  }
}

fn infer_trusted(
  environment: Environment,
  provenance: fn(Digest) -> List(#(u, Rule)),
  fuel: Fuel,
  cx: Context,
  proc: Digest,
  args: Term,
  result_typ: Term,
) -> Result(#(Term, Trace(u)), TypeError) {
  case environment.definitions(proc) {
    None -> Error(Unresolved(proc))
    Some(sig) ->
      case infer_go(environment, provenance, fuel, empty(), sig) {
        Error(_) -> Error(TrustedProcNotAType(sig))
        Ok(#(_, tr1)) -> {
          use #(w, tr2) <- result.try(whnf_go(
            environment,
            provenance,
            fuel,
            sig,
          ))
          case w {
            term.Pi(domain, codomain) -> {
              use tr3 <- result.try(check_go(
                environment,
                provenance,
                fuel,
                cx,
                args,
                domain,
              ))
              let expected = beta(args, codomain)
              use #(_, tr4) <- result.try(infer_sort_go(
                environment,
                provenance,
                fuel,
                cx,
                result_typ,
              ))
              use #(eq, tr5) <- result.try(def_eq_go(
                environment,
                provenance,
                fuel,
                result_typ,
                expected,
              ))
              case eq {
                True -> Ok(#(result_typ, merge([tr1, tr2, tr3, tr4, tr5])))
                False ->
                  Error(TrustedCodomainMismatch(
                    expected: expected,
                    actual: result_typ,
                  ))
              }
            }
            other -> Error(TrustedProcNotPi(other))
          }
        }
      }
  }
}
