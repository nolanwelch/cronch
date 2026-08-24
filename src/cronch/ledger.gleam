/// An append-only receipt set with the reverse indices a revocation needs.
///
/// Outside the kernel and outside the TCB.
///
/// Why this exists
/// ---------------
/// Because dependencies are hash-pinned and recorded, a revocation has an
/// exactly computable blast radius rather than a heuristic advisory. "Rule set
/// X turned out to be unsound" is not a mailing-list post here; it is a query
/// that returns the precise set of artifacts that lose their warrant, and the
/// precise set that does not.
///
/// Two rules make that answer trustworthy rather than merely fast:
///
///   1. Only `Accepted` receipts confer warrant. `Rejected` and `Exhausted`
///      receipts are recorded -- they are evidence, and a record that
///      something does not typecheck is worth keeping -- but they never put an
///      artifact in `survivors`.
///   2. An artifact with no `Accepted` receipt in the ledger is not a
///      survivor. Unknown is not safe. Silence is not a pass.
///
/// Termination
/// -----------
/// A well-formed store is acyclic, and nothing here relies on that. Receipts
/// are supplied by whoever wants their artifact believed, and a `deps` list is
/// just digests -- nothing stops an adversary submitting receipts that refer
/// to each other in a cycle. Propagation is a worklist over a set that only
/// grows, so each artifact is marked at most once and a cycle costs one pass,
/// not a stack overflow.
import cronch/basis.{type Basis}
import cronch/canonical
import cronch/digest.{type Digest}
import cronch/pubkey.{type PublicKey}
import cronch/receipt.{type Receipt}
import cronch/trust
import gleam/list
import gleam/option.{type Option, None, Some}

/// An append-only set of receipts, plus the bases they name.
///
/// Opaque: the invariant is that `receipts` holds no two entries with the same
/// receipt digest, and nothing outside this module can break it.
pub opaque type Ledger {
  Ledger(
    /// (receipt digest, receipt), most recently added first.
    receipts: List(#(Digest, Receipt)),
    /// (basis digest, basis) for every basis registered with `add_basis`.
    bases: List(#(Digest, Basis)),
  )
}

/// The empty ledger. Confers warrant on nothing.
pub fn new() -> Ledger {
  Ledger(receipts: [], bases: [])
}

/// Add a receipt. Idempotent by receipt digest: adding the same receipt again,
/// a hundred times, changes nothing.
pub fn add(l: Ledger, r: Receipt) -> Ledger {
  let d = receipt.digest(receipt.default_algorithm, r)
  case list.any(l.receipts, fn(e) { e.0 == d }) {
    True -> l
    False -> Ledger(..l, receipts: [#(d, r), ..l.receipts])
  }
}

/// Register a basis so that `RevokeKernel` can tell which receipts were issued
/// under which kernel.
///
/// A receipt names its basis by digest only, so without this the ledger cannot
/// see through a basis digest to the kernel behind it. Idempotent.
pub fn add_basis(l: Ledger, b: Basis) -> Ledger {
  let d = basis.digest(receipt.default_algorithm, b)
  case list.any(l.bases, fn(e) { e.0 == d }) {
    True -> l
    False -> Ledger(..l, bases: [#(d, basis.canonicalize(b)), ..l.bases])
  }
}

/// Every receipt in the ledger, ordered by receipt digest so that two ledgers
/// built by adding the same receipts in different orders enumerate alike.
pub fn all_receipts(l: Ledger) -> List(Receipt) {
  l.receipts
  |> list.sort(fn(a, b) { canonical.compare_digests(a.0, b.0) })
  |> list.map(fn(e) { e.1 })
}

/// Every artifact the ledger holds a receipt for, sorted and deduped.
pub fn artifacts(l: Ledger) -> List(Digest) {
  canonical.sort_digests(list.map(l.receipts, fn(e) { e.1.artifact }))
}

/// The receipt for an artifact, if the ledger has one.
///
/// An `Accepted` receipt wins over any other, since that is the one a caller
/// asking "is this thing checked?" means. Among equals, the smallest receipt
/// digest wins -- an arbitrary rule, but a deterministic one, so two ledgers
/// holding the same receipts answer identically regardless of insertion order.
pub fn get(l: Ledger, artifact: Digest) -> Option(Receipt) {
  let candidates =
    l.receipts
    |> list.filter(fn(e) { e.1.artifact == artifact })
    |> list.sort(fn(a, b) { canonical.compare_digests(a.0, b.0) })
    |> list.map(fn(e) { e.1 })
  case list.find(candidates, fn(r) { r.verdict == receipt.Accepted }) {
    Ok(r) -> Some(r)
    Error(_) ->
      case candidates {
        [r, ..] -> Some(r)
        [] -> None
      }
  }
}

/// Every receipt the ledger holds for one artifact, in receipt-digest order.
pub fn receipts_for(l: Ledger, artifact: Digest) -> List(Receipt) {
  l.receipts
  |> list.filter(fn(e) { e.1.artifact == artifact })
  |> list.sort(fn(a, b) { canonical.compare_digests(a.0, b.0) })
  |> list.map(fn(e) { e.1 })
}

// ── Revocation ────────────────────────────────────────────────────────────────

/// A thing that turned out not to be trustworthy after all.
pub type Revocation {
  /// A signed rule set, pinned by (author, content hash).
  RevokeRuleSet(PublicKey, Digest)
  /// A Trusted-node host, by key.
  RevokeHost(PublicKey)
  /// A postulate, by content address.
  RevokeAxiom(Digest)
  /// A whole checking context, by basis digest.
  RevokeBasis(Digest)
  /// A kernel, by identifier.
  RevokeKernel(String)
}

/// Every artifact that loses its warrant, directly or transitively.
///
/// An artifact is killed if its own receipt directly names a revoked thing --
/// in its trust set, axioms, capabilities, basis, or kernel -- or if anything
/// in its transitive `deps` closure is killed.
///
/// Sorted by digest bytes, deduped.
pub fn blast_radius(l: Ledger, revocations: List(Revocation)) -> List(Digest) {
  // The killed set is seeded with revoked objects as well as artifacts, so
  // that a dependency on a revoked axiom propagates. Only artifacts the ledger
  // actually holds a receipt for are reported: a revoked axiom is not itself
  // an artifact that lost warrant, it is the reason others did.
  let known = artifacts(l)
  killed(l, revocations)
  |> list.filter(fn(d) { list.contains(known, d) })
  |> canonical.sort_digests
}

/// Every artifact that still holds warrant after the revocations.
///
/// An artifact is a survivor only if the ledger holds an `Accepted` receipt
/// for it AND that artifact is not in the blast radius. An artifact with only
/// `Rejected` or `Exhausted` receipts is not a survivor, and neither is one
/// the ledger has never heard of. Unknown is not safe.
pub fn survivors(l: Ledger, revocations: List(Revocation)) -> List(Digest) {
  let dead = killed(l, revocations)
  l.receipts
  |> list.filter(fn(e) { e.1.verdict == receipt.Accepted })
  |> list.map(fn(e) { e.1.artifact })
  |> list.filter(fn(a) { !list.contains(dead, a) })
  |> canonical.sort_digests
}

// The killed set, unsorted. Seeded with every artifact whose own receipt names
// something revoked, then propagated up the dependency edges to fixpoint.
fn killed(l: Ledger, revocations: List(Revocation)) -> List(Digest) {
  let seed =
    l.receipts
    |> list.filter(fn(e) { directly_hit(l, e.1, revocations) })
    |> list.map(fn(e) { e.1.artifact })
    |> list.unique

  // A revoked axiom is a dead object in its own right, so anything depending
  // on it dies even if the dependent's own axiom set somehow omitted it.
  let revoked_axioms =
    list.filter_map(revocations, fn(r) {
      case r {
        RevokeAxiom(d) -> Ok(d)
        _ -> Error(Nil)
      }
    })

  propagate(l, list.unique(list.append(seed, revoked_axioms)), [])
}

// Worklist to fixpoint. `frontier` is what was newly killed on the last pass;
// `dead` is everything killed so far. Each artifact enters `dead` at most
// once, so this terminates on any graph -- cycles included -- without relying
// on the store being a DAG.
fn propagate(
  l: Ledger,
  frontier: List(Digest),
  dead: List(Digest),
) -> List(Digest) {
  case frontier {
    [] -> dead
    [d, ..rest] ->
      case list.contains(dead, d) {
        True -> propagate(l, rest, dead)
        False -> {
          let dead = [d, ..dead]
          // Everything that names `d` as a direct dependency now dies too.
          let dependents =
            l.receipts
            |> list.filter(fn(e) { list.contains(e.1.deps, d) })
            |> list.map(fn(e) { e.1.artifact })
            |> list.filter(fn(a) { !list.contains(dead, a) })
          propagate(l, list.append(dependents, rest), dead)
        }
      }
  }
}

// Whether a receipt names a revoked thing itself, without following deps.
fn directly_hit(l: Ledger, r: Receipt, revocations: List(Revocation)) -> Bool {
  list.any(revocations, fn(rev) {
    case rev {
      RevokeRuleSet(author, hash_val) ->
        list.contains(r.trust_set, trust.RuleSetTrust(author, hash_val))
      RevokeHost(host) ->
        list.any(r.trust_set, fn(p) {
          case p {
            trust.HostTrust(h, _) -> h == host
            trust.RuleSetTrust(_, _) -> False
          }
        })
      RevokeAxiom(d) ->
        list.contains(r.axioms, d) || list.contains(r.capabilities, d)
      RevokeBasis(d) -> r.basis == d
      RevokeKernel(id) -> under_kernel(l, r.basis, id)
    }
  })
}

// Whether a receipt's basis was issued under the named kernel.
//
// Fails CLOSED. If the basis is not registered, the ledger cannot show that
// this receipt was NOT issued under the revoked kernel, so it treats it as if
// it were. That is deliberately harsh -- revoking a kernel with no registered
// bases kills everything -- and it is the right direction: the alternative is
// an artifact surviving a kernel revocation because nobody wrote down which
// kernel checked it.
fn under_kernel(l: Ledger, basis_digest: Digest, id: String) -> Bool {
  case list.find(l.bases, fn(e) { e.0 == basis_digest }) {
    Ok(#(_, b)) -> b.kernel_id == id
    Error(_) -> True
  }
}

// ── Conflicts ─────────────────────────────────────────────────────────────────

/// Artifacts holding two receipts with the SAME basis but DIFFERENT verdicts.
///
/// Under one basis a check is a pure function, so two different answers means
/// either the kernel is nondeterministic or somebody is equivocating. Both are
/// serious and neither should be quiet, so this is a first-class query rather
/// than a log line. Sorted by artifact digest; the receipts within each entry
/// are in receipt-digest order.
///
/// Two receipts under DIFFERENT bases disagreeing is not a conflict -- that is
/// the system working, and is exactly what a basis is for.
pub fn conflicts(l: Ledger) -> List(#(Digest, List(Receipt))) {
  artifacts(l)
  |> list.filter_map(fn(a) {
    let rs = receipts_for(l, a)
    case list.any(rs, fn(x) { list.any(rs, fn(y) { equivocates(x, y) }) }) {
      True -> Ok(#(a, rs))
      False -> Error(Nil)
    }
  })
}

fn equivocates(x: Receipt, y: Receipt) -> Bool {
  x.basis == y.basis && x.verdict != y.verdict
}

/// Every artifact the ledger holds receipts for but no `Accepted` one. These
/// are not survivors under any revocation set, including the empty one; the
/// audit command reports them so "nobody looked" does not read as "fine".
pub fn without_accepted_verdict(l: Ledger) -> List(Digest) {
  artifacts(l)
  |> list.filter(fn(a) {
    !list.any(receipts_for(l, a), fn(r) { r.verdict == receipt.Accepted })
  })
}
