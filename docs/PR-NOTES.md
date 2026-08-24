# PR notes — checker persistence

**Status: Part A only.** This PR currently contains the Part A deliverable (this
document) and nothing else. See [Blocker](#blocker-no-buildable-toolchain-in-this-environment)
at the bottom: the environment this branch was prepared in cannot resolve the
project's Hex dependencies, so `gleam build` / `gleam test` cannot be run here.
Per the standing rule that no part starts before the previous part's tests are
green, no code was written. Three findings below change the design of Parts B,
C and D and need a decision before implementation starts.

---

## 1. Name reconciliation

Names as used in the task description, versus what is actually in the source.

| Name in the request | Actual name / location | Verdict | Notes |
| --- | --- | --- | --- |
| Term constructors `Const` / `Hole` / `Trusted` | `term.Const(hash)`, `term.Hole(id, goal)`, `term.Trusted(host, proc, args, result_typ)` — `src/cronch/term.gleam` | **MATCH** | Full constructor set is `Var, Sort, Pi, Lam, App, Eq, Refl, Const, Hole, Trusted`. De Bruijn indices, so `==` is alpha-equivalence. |
| a `Digest` type | `digest.Digest(algorithm: HashAlgorithm, bytes: BitArray)` — `src/cronch/digest.gleam` | **DIFFERENT-SEMANTICS** | A Digest is *not* bare bytes: it carries an algorithm tag. Two digests can have equal `bytes` and differ. Affects constraint 5 ("sets sorted by raw digest bytes") — see §2.4. |
| content-addressed store | `kernel.Store = fn(Digest) -> Option(Term)`, bundled into `kernel.Environment(definitions, signatures, rules)` | **RENAMED** | There are three stores, not one: `definitions` (Store), `signatures` (SignatureStore — axioms, no body), `rules` (RuleStore). `trust.Store` and `oracle.Store` are separate type aliases of the same shape. |
| hash-verifying wrapper | `oracle.verifying_store` — `src/cronch/oracle.gleam:88` | **DIFFERENT-SEMANTICS** | It exists, but it is applied in exactly one place: `oracle.solve_state`. `kernel.check` / `kernel.infer` callers do **not** get a verifying store unless they wrap it themselves. See risk #2. |
| fuel-bounded `check` / `infer` | `kernel.check(env, fuel, cx, t, expected)`, `kernel.infer(env, fuel, cx, t)` — `src/cronch/kernel.gleam:701, 617` | **DIFFERENT-SEMANTICS** | Bounded, yes — but `Fuel` is a *budget value passed down*, not a counter threaded through. Nested calls reuse the caller's `Fuel` unchanged (documented at `kernel.gleam:264-276`). There is no "fuel used" quantity anywhere today. This is the single biggest gap for Part D — see §2.3. |
| normalization reporting rule uses (`RuleUse`) | `kernel.RuleUse(author: PublicKey, rule_set: Digest)`; `kernel.normalize_with_uses`, `kernel.whnf_with_uses` — `kernel.gleam:178, 410, 293` | **MATCH** | And the "one reduction implementation" constraint is already honoured: `whnf`/`whnf_with_uses` share `whnf_go`, generic over the tag type. |
| recomputable trust set | `trust.trust_set(store, t)` and `trust.trust_set_with_rules(env, fuel, provenance, t)` — `src/cronch/trust.gleam:73, 204` | **MATCH** | `TrustPair = HostTrust(host, proc) \| RuleSetTrust(author, hash)`. |
| opaque `Policy`, no default-trusted rule sets | `trust.Policy` (`pub opaque`), `trust.empty_policy()` — `trust.gleam:230, 235` | **MATCH** | Confirmed: `empty_policy` accepts only an empty trust set; the reference rule set has no privileged status. |
| Ed25519 signatures over content hashes, strictly outside the kernel | `trust.verify_host_result`, `trust.verify_rule_set_signature`, FFI `cronch_crypto:verify_ed25519` — `trust.gleam:308, 336`; `src/cronch_crypto.erl` | **MATCH** | `kernel.gleam` contains no reference to signatures, pubkey verification, or the crypto FFI. Verified by grep. |
| reference / fixture rule sets in `test/` | `test/support/reference_rules.gleam` (Sigma / pair / fst / snd / J) | **MATCH** | Five axiomatic constants + three rules; `rule_set_hash()` is the content address a policy authorizes. |
| kind tag `0x00 Term … 0x04 CapabilitySet` | — | **ABSENT** | To be introduced (Part B). Conflicts with digest stability as specified — see §2.1. |
| `Basis`, `Receipt`, `Ledger`, `Capability`, gas policy | — | **ABSENT** | Nothing resembling these exists. New modules, as specified. |
| CLI | `src/cronch.gleam` is a hardcoded end-to-end demo (`main()` parses a fixed source string and prints). There is no argument handling anywhere. | **ABSENT** | Part I builds this from scratch. |

Names present in the source that the request did not mention, and that any
implementation has to account for: `kernel.Environment`, `kernel.SignatureStore`
(axioms), `kernel.RuleStore`, `rewrite.Rule` / `rewrite.Pattern`,
`kernel.Fuel(Limited | Unlimited)`, `kernel.TypeError` (10 variants),
`serialize.DecodeError` (8 variants), the `syntax/` front end
(`lex`, `parse`, `elab`, `print`), and `src/cronch/bench.gleam`.

---

## 2. Findings that change the design

These are the "stop and say so rather than improvise" items.

### 2.1 Part B: the specified tag numbering cannot be domain-separating

Determination, as instructed: **adding a leading tag byte would change every
existing Term digest.** `hash.hash` hashes `serialize.encode(t)` directly, and
that byte string already begins with the term-constructor tag `0x00`–`0x09`.
Prefixing anything changes all of them — including the five constants in
`test/support/reference_rules.gleam` (whose digests are derived from their
declared types), the six hardcoded vectors in `test/hash_test.gleam`, and every
`Const` node in every stored artifact.

The instruction is explicit that digest stability wins, so `hash.hash` stays
byte-identical and the tagged encoding is a distinct function. **But that means
the specified tag values do not achieve the stated goal.** Legacy Term
encodings occupy leading bytes `0x00`–`0x09`. Assigning Basis `0x01`, Receipt
`0x02`, RuleSet `0x03`, CapabilitySet `0x04` puts all four new classes inside
that range, so "no encoding of any artifact class can equal an encoding of
another class, **by construction**" would hold only among the four new classes,
not between any of them and a Term. The cross-class collision channel the part
exists to close would remain open against precisely the class an attacker is
most likely to control.

**Proposed change, needs your call:** keep the ordering and meaning you
specified, but move the tag byte into a range disjoint from legacy Term
encodings:

```
0x80 Term (tagged)   0x81 Basis   0x82 Receipt   0x83 RuleSet   0x84 CapabilitySet
```

Then separation is by construction against every class including legacy Terms,
`hash.hash` is untouched, and the new `hash_tagged` is used only by code
introduced in this PR. The alternative — your literal numbering — is
implementable and I will do it if you prefer, but the by-construction test in
Part B would have to be weakened to "no two *new* classes can collide", and
that limitation belongs in the PR description rather than in a test that claims
more than it proves.

### 2.2 Part C: the bug is real, but the C1 construction as written does not exhibit it

The bypass is real and the source comment at `trust.gleam:185-195` is an
accurate description of it. But the specific artifact C1 asks for — "an
artifact whose only use of a given rule set occurs inside a binder's type
annotation" — **would not** produce an empty old trust set. `normalize_go`
recurses into `Pi`'s and `Lam`'s domain (`kernel.gleam:428-457`), so a redex
sitting in a binder's type annotation *within the artifact term* is reduced by
the existing `trust_set_with_rules` pass and its rule use is already recorded.

What the current reconstruction genuinely misses is every reduction over a type
that is **not a syntactic subterm of the artifact**:

1. the declared type passed to `check` as `expected` — never part of the term, and
   in Part F this is exactly `Receipt.spec`, the contract;
2. an axiom's declared type fetched from `SignatureStore` (`kernel.gleam:679`) —
   `trust.walk` does not consult `signatures` at all;
3. the type inferred for a `Const`'s definition (`kernel.gleam:684`);
4. conversion checks in `check` — `def_eq(env, fuel, actual, expected)`
   (`kernel.gleam:709`), where `actual` is *constructed by the checker*
   (e.g. `beta(x, codomain)` at `kernel.gleam:656`) and never appears in the term;
5. `whnf(env, fuel, f_typ)` in the `App` rule (`kernel.gleam:652`) and every
   `infer_sort` (`kernel.gleam:718`);
6. `infer_trusted`, which infers and whnfs the procedure signature pulled from
   the store (`kernel.gleam:740-751`).

So: the part stands, the required approach (derivation-integral reporting)
stands, and it is the right fix — it closes all six at once, which is precisely
the argument for it over a second normalization pass. Only C1's construction
needs replacing. I propose building C1 from case (1) or (4): an artifact that
typechecks against a declared spec whose reduction requires the reference rule
set, where the artifact's own normal form touches no rule at all. That yields
an empty old trust set, a non-empty new one, and a purist-policy refusal —
exactly the regression the part calls for, with a construction that actually
demonstrates it.

A second, smaller Part C note: `trust_set_with_rules` takes `provenance` as a
parameter separate from `Environment.rules`, and nothing checks that the two
enumerate the same rules (`trust.gleam:198-203` states it as a caller
obligation). A caller that passes a `provenance` narrower than
`environment.rules` gets a *silently under-reported* trust set from an
otherwise correct implementation. Re-expressing the trust set in terms of the
Report closes this too, since the Report comes from the same reduction the
kernel actually ran — worth calling out as a second bug fixed for free.

### 2.3 Part D: `fuel_used` does not exist and cannot be added naively

`Fuel` today is a budget handed downward, not a meter. `consume`
(`kernel.gleam:161`) returns a decremented `Fuel` to its immediate caller only;
`whnf_go` deliberately does **not** thread the reduced value back out of nested
calls, and `kernel.gleam:264-276` documents this as an intentional trade
("Fuel exhaustion is a termination guard, not a precise cost accounting
mechanism").

Consequence: introducing a single global fuel counter — the obvious way to get
`fuel_used` — **would change accept/reject outcomes.** A term that today passes
under `Limited(100_000)` because each nested reduction gets a fresh 100 000
could exhaust a single shared 100 000 budget. That is a direct violation of
constraint 2 (recording is not deciding).

**Resolution, no decision needed unless you disagree:** `fuel_used` must be a
pure *observation* accumulator — a count of `consume` events threaded alongside
the existing `Fuel` value, with the existing `Fuel` continuing to be passed down
exactly as it is today. Verdicts then provably cannot change (the budget
arithmetic is untouched), and `fuel_used` is still a deterministic function of
the inputs, which is what Parts D and F need it to be. It is *not* a bound on
work and must not be documented as one; `GasPolicy.max_fuel` is therefore a
declared-and-checked cost, not an enforcement mechanism. The `Exhausted`
verdict still comes from `FuelExhausted`, which is unchanged.

### 2.4 Constraint 5 vs. the actual `Digest` type

"Sets sorted by raw digest bytes (never by string rendering)" cannot mean the
`bytes` field alone: `Digest` carries a `HashAlgorithm`, so `bytes`-only
ordering is not a total order on `Digest` and is not stable if a second
algorithm is ever registered. I will sort on `algorithm_tag` then `bytes`,
comparing `BitArray`s directly.

Note also that the existing `trust.compare_pair` (`trust.gleam:138`) sorts by
`bit_array.base16_encode(...)` — i.e. **by string rendering**, exactly what
constraint 5 forbids. It is currently correct only because all digests and keys
are fixed-size and base16 is order-preserving on equal-length inputs. New code
will not copy this; whether to fix it in place is a separate question, since
changing it would change `trust_set`'s output ordering and could break existing
tests.

---

## 3. Trusted computing base — line counts before this PR

Measured with `wc -l` at `6d9c751`.

| Module | Lines | Trusted for |
| --- | ---: | --- |
| `src/cronch/kernel.gleam` | 772 | Soundness. The one irreducible trust act. |
| `src/cronch/term.gleam` | 31 | The meaning of what is being checked. |
| `src/cronch/rewrite.gleam` | 244 | Pattern matching / instantiation used inside reduction; also the load-bearing "no `PHole`/`PTrusted`" invariant. |
| `src/cronch/serialize.gleam` | 460 | Canonical, injective encoding — object identity. |
| `src/cronch/hash.gleam` | 82 | Content addressing built on that encoding. |
| `src/cronch/digest.gleam` | 57 | Algorithm tags and sizes. |
| `src/cronch/pubkey.gleam` | 46 | Key scheme tags and sizes. |
| **TCB total** | **1692** | |
| `src/cronch_crypto.erl` | 19 | Signature verification. Outside the kernel, but a lie here forges host/rule-set authority. |

Kernel proper: **772 lines**. Explicitly *not* in the TCB and confirmed
un-imported by `kernel.gleam`: `trust.gleam` (345), `oracle.gleam` (275),
`syntax/` (1272), `bench.gleam` (271), `cronch.gleam` (180).

**Test count before this PR: 229** test functions (`pub fn *_test()`), across 8
files — kernel 61, syntax 49, trust 33, serialize 31, rewrite 19, hash 15,
oracle 15, reference_rules 6. (`test/cronch_test.gleam` holds only
`gleeunit.main`.) This is a static count; it could not be confirmed against a
run — see the blocker below.

---

## 4. Top open risks found while reading

Ranked.

1. **Nothing enforces that `Trusted` is the sole effect channel — the guarantee
   Part H's admission property rests on is currently vacuous.** There is no
   runtime, no execution engine, and no effect discipline anywhere in the repo;
   `Trusted` is an inert node the kernel type-checks and never reduces
   (`kernel.gleam:521`). A capability set therefore bounds which host procedures
   are *named* by a term, and nothing more. Part H asks for this to be recorded
   as the top risk, and it is: the property is honest only as long as its
   own documentation says what it does not prove.
2. **`verifying_store` is not on the checking path.** `oracle.solve_state`
   wraps the store; `kernel.check` / `kernel.infer` callers do not. A store that
   returns a term whose hash does not match the requested `Const` address is
   believed by the kernel. Every guarantee in this PR is stated "under a stated
   basis", and a lying store silently changes that basis. `Receipt.replay`
   inherits this: replay recomputes against whatever store it is handed.
3. **Confluence and termination of rule sets are never checked, and
   `Unlimited` fuel is a public entry point.** Documented and deliberate
   (`rewrite.gleam:61-67`), but it means `Exhausted` is a load-bearing verdict,
   not an edge case — which is an argument *for* Part D's three-outcome
   discipline, and against anything that collapses exhaustion into rejection.

---

## Blocker: no buildable toolchain in this environment

`gleam` and Erlang/OTP were not present and were installed
(OTP 25 via apt, Gleam 1.16.0 from the GitHub release, matching CI). The build
then fails at dependency resolution:

```
$ gleam test
Downloading packages
error: HTTP error
  error sending request for url (https://repo.hex.pm/tarballs/b3-0.2.0.tar)
```

`repo.hex.pm` is refused by this session's egress policy (`403` to `CONNECT`),
as is `codeberg.org`, where `gblake3` — the transitive source of the project's
only hash implementation — is hosted. `github.com` is reachable for git reads,
but vendoring the dependencies out of git into `build/packages/` to work around
Hex was declined by the sandbox as untrusted-code integration, which is the
correct call and I did not attempt to route around it.

The practical consequence: **no part of this PR can be compiled, tested, or
`gleam format`-checked from this branch as things stand.** Parts B through K are
all test-gated by the task's own rules, and writing ~2 000 lines of
security-relevant Gleam that has never been type-checked would be worse than
writing none.

What unblocks it, in order of preference:

1. Allow `repo.hex.pm` through the egress policy. Nothing else is needed —
   `manifest.toml` pins exact versions and checksums, so `gleam deps download`
   verifies what it fetches.
2. Commit a vendored `deps/` (or a Hex cache tarball) to the repo, or grant a
   Bash permission rule allowing the vendored packages to be staged into
   `build/packages/`.
3. Confirm you want the code written unverified, with every part explicitly
   marked untested in the PR description. I do not recommend this and would
   want it in writing.
