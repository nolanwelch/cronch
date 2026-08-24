# The trusted computing base

What you have to believe to believe anything this system says, and in what
order to read it.

## The one irreducible trust act

**Kernel soundness.** You must believe that `src/cronch/kernel.gleam` accepts a
term only when that term genuinely inhabits the type it was checked against.

There is no way around this and no point pretending otherwise. Every other
guarantee here is conditional on it: a receipt is a record of what the kernel
did, a trust set names what the kernel's acceptance depended on, a ledger
computes consequences of those records. If the kernel is unsound, all of it is
an elaborate account of nothing.

What the design does about that is not to eliminate the trust act but to make
it **small, isolated, and singular**:

- **Small.** The kernel is 1092 lines, and a test fails if it grows past 1201
  (`test/invariant_test.gleam`, J1). It is meant to be read in one sitting by
  one person.
- **Isolated.** The kernel imports four project modules and five standard
  library modules, and a test fails if that list changes (J2). Nothing about
  policy, receipts, bases, ledgers, capabilities, signatures or the command
  line is reachable from it.
- **Singular.** There is exactly one reduction implementation and one typing
  implementation. The reporting entry points and the plain ones are the same
  functions with the record kept rather than discarded, so an audited path and
  an instrumented path cannot drift apart.

Everything else in this repository can be wrong without producing an unsound
acceptance. It can produce a *refusal* of something sound — a bug in the trust
set, the policy, the ledger or the CLI can deny you an artifact you should have
been allowed. That is the direction the errors are arranged to fall.

## What is trusted, and for what

### The kernel proper

| Module | Lines | Trusted for |
| --- | ---: | --- |
| `cronch/kernel.gleam` | 1092 | **Soundness.** Typing, reduction, definitional equality, universe levels, the fuel guard. `shift`/`subst` are the highest-risk code in the project; most soundness bugs in systems of this shape live there. |
| `cronch/term.gleam` | 31 | The term language. De Bruijn indices, so structural equality is alpha-equivalence and there is no name capture to get wrong. |
| `cronch/rewrite.gleam` | 244 | Pattern matching and instantiation, which run *inside* reduction. Also the load-bearing invariant that `Pattern` has no case for `Hole` or `Trusted` — a rule that could manufacture either would let a rule set reopen a closed proof or hide a trust dependency. |
| `cronch/digest.gleam` | 57 | Digest identity: which algorithm, which bytes, which wire tag. |
| `cronch/pubkey.gleam` | 46 | Key identity. |

### Content addressing

| Module | Lines | Trusted for |
| --- | ---: | --- |
| `cronch/serialize.gleam` | 501 | **Injectivity of the encoding.** A content address means nothing if two different terms can encode to the same bytes. Also canonicality: exactly one encoding per term, and decoding refuses every non-canonical byte string. |
| `cronch/hash.gleam` | 82 | Content addressing on top of `serialize`, and address parsing. |

These are trusted differently from the kernel. A bug here does not make an
ill-typed term typecheck; it makes two distinct objects share a name, which
means a store can serve you one thing when you asked for another. The
verifying-store wrapper (`oracle.verifying_store`) is the mitigation, and it is
only as good as `hash`.

**Total: 2053 lines.**

### The FFI

`src/cronch_crypto.erl` is trusted for signature *verification* only, and only
by `trust.gleam`, which is outside the TCB. The kernel does not know what a
signature is. A broken verifier can cause a signed rule set or host result to
be refused, or accepted when it should not be — but policy is checked *before*
the kernel runs, so it gates what the kernel is asked to do rather than what the
kernel concludes.

## What is NOT trusted

Everything else, and this is the point of the arrangement rather than an
accident of it:

| Module | Lines | Why a bug here cannot produce an unsound acceptance |
| --- | ---: | --- |
| `cronch/trust.gleam` | 433 | Trust sets and policy gate *whether to ask* the kernel. A wrong trust set refuses artifacts or fails to refuse them — the latter is a policy bypass, which is serious, but it is not an unsound proof. |
| `cronch/receipt.gleam` | 707 | A receipt records what the kernel decided. `replay` recomputes rather than believes, so a wrong receipt fails to replay. |
| `cronch/basis.gleam` | 325 | Names the context. Nothing here checks anything. |
| `cronch/ledger.gleam` | 293 | Computes consequences of receipts. Fails closed: unknown is not safe. |
| `cronch/capability.gleam` | 373 | A reachability bound over terms. Refuses; never admits anything the kernel would not. |
| `cronch/gas.gleam` | 192 | Meters. Can refuse a check; cannot make one succeed. |
| `cronch/canonical.gleam` | 335 | Encoding for the new artifact classes. A bug gives an artifact the wrong name. |
| `cronch/cli.gleam` | 903 | Argument parsing, file I/O, printing. |
| `cronch/oracle.gleam` | 275 | Proposes candidates. Every proposal is re-checked by the kernel, so a malicious oracle can only make holes stay open. |
| `cronch/syntax/*` | 1272 | Surface syntax. A wrong elaboration produces a *different* term, which is then checked on its own merits — you may prove something other than what you wrote, which is why the elaborated term's content address is what a receipt names, not the source text. |
| `cronch/bench.gleam` | 271 | Measurement. |

## Open risks

Ranked by how much of the design's claims they undermine.

### 1. `Trusted` is not enforced as the sole effect channel — by anything

`capability.gleam` bounds which host procedures an artifact can reach. That
bound is worth exactly as much as the guarantee that effects cannot enter by
any other route, **and no such guarantee is enforced anywhere in this
repository.** There is no plugin runtime, no host execution, nothing that
observes a running artifact, and nothing that checks a running artifact against
its declaration. Today the property is entirely static: it says something true
about terms and nothing at all about executions.

This is first because it is the one where a reader could reasonably come away
believing more than is true. If a runtime is ever built, the first thing it
needs is to make that guarantee real; until then, `admit` is a linting pass with
good manners.

### 2. Rule-set termination and confluence are checked nowhere, and fuel is a coarse guard

`rewrite.gleam` says plainly that confluence and termination are established
out-of-band by whoever signs a rule set. `Limited` fuel is the only defence, and
it is weak in a specific way: it is consumed **only** by rewrite-rule
application, so a rule set that drives cost through beta and delta rather than
through rule firings is barely metered by it. `kernel.Report.fuel_used` counts
the real cost and a receipt records it, but the counter *observes* — it is
`Fuel` that gates, and `Fuel` watches one of the three step kinds.

Worse in kind, though not in likelihood: a non-confluent rule set makes
definitional equality order-dependent, and `whnf` tries rules in list order. Two
rule sets with the same rules in different orders are already, deliberately,
different content addresses — which is right — but nothing warns an author that
their rule set's *behaviour* depends on that order.

### 3. `deps` and `axioms` disagree about transitivity, on purpose

`Receipt.deps` is direct references only, keeping each receipt O(its own term);
transitivity is the ledger's job. `Receipt.axioms` is the full transitive
closure, because an assumption set that omits assumptions is worse than no
assumption set. Both choices are right individually. Together they mean two
list-of-digest fields sitting next to each other in one record have different
reach, and nothing in the type system says so.

The concrete failure mode: a consumer that reasons about dependencies from
`deps` alone, without a ledger, sees a shallower graph than exists.
`ledger.blast_radius` is correct because it closes over `deps` across every
receipt it holds — but a receipt read in isolation invites the wrong reading.
Documented in the field comments; not enforced.

**Runners-up.** `revoke --kernel` fails closed by treating any receipt with an
unregistered basis as killed, which is the right direction but means one
unregistered basis makes a kernel revocation look catastrophic. And
`Environment`'s definitions/signatures disjointness is a precondition nothing
checks at runtime, so a store that assigns one digest two meanings silently
resolves to the signature.

## What a reader auditing this system should read, in order

**First — the audit surface itself, in one sitting.**

1. `src/cronch/term.gleam` (31 lines). Ten constructors. Read them all.
2. `src/cronch/kernel.gleam` (1092 lines), and within it, in this order:
   - `shift`, `subst`, `beta`. If these are wrong, nothing else matters. They
     are written in the deliberately obvious way; resist the urge to improve
     them.
   - `whnf_go` and `try_rewrite` — the one reduction implementation.
   - `infer_go` and `check_go` — the one typing implementation. Note that the
     public `infer`/`check` are wrappers that discard the `Report`, so
     reporting cannot change a verdict.
   - `Fuel` and `consume`. Understand that fuel is a **termination guard**, not
     a cost meter: it is consumed only by rewrite-rule application and is never
     threaded back out of nested calls.
3. `src/cronch/rewrite.gleam` (244 lines), especially the module comment
   explaining why `Pattern` has no `Hole` or `Trusted` case and never will.

**Second — what "the same object" means.**

4. `src/cronch/serialize.gleam`, the wire-layout comment at the top and then
   `encode`/`decode`. Satisfy yourself that the encoding is injective and that
   decoding refuses non-canonical input.
5. `src/cronch/hash.gleam`, and `oracle.verifying_store`, which is the only
   thing standing between you and a store that lies about content addresses.

**Third — what the system claims on top of that.**

6. `src/cronch/trust.gleam`. Trust sets and policy. Note the distinction
   between `trust_set_with_rules` (reduction-scoped, under-reports, not for
   authorization) and `trust_set_of_check` (derivation-integral, and what
   authorization actually consults).
7. `src/cronch/receipt.gleam`. In particular `replay`: read it until you are
   convinced that accepting a receipt requires trusting nobody.
8. `src/cronch/basis.gleam`, then `ledger.gleam`, then `capability.gleam`.

**Fourth — the guardrails.**

9. `test/invariant_test.gleam`. These are the claims above, stated as tests
   that fail when they lapse.

If you only have an hour, read step 1 and step 2. Everything else is downstream
of those, and nothing else can rescue them.
