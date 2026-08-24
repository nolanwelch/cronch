/// Part E: the Basis.
import cronch/basis
import cronch/canonical
import cronch/digest
import cronch/kernel
import cronch/pubkey
import cronch/term
import gleam/bit_array
import gleam/list
import gleam/option
import gleeunit/should
import support/corpus
import support/reference_rules

const kernel_id = "cronch-kernel/0.1.0"

fn key(b: Int) -> pubkey.PublicKey {
  pubkey.PublicKey(pubkey.Ed25519, <<b:size(256)>>)
}

fn dig(b: Int) -> digest.Digest {
  digest.Digest(digest.Blake3, <<b:size(256)>>)
}

fn sample() -> basis.Basis {
  basis.Basis(
    kernel_id: kernel_id,
    axioms: [dig(3), dig(1), dig(2)],
    rule_sets: [#(key(2), dig(9)), #(key(1), dig(8))],
    hosts: [key(7), key(5)],
  )
}

// ── digest invariance under permutation ───────────────────────────────────────

pub fn digest_is_invariant_under_input_permutation_test() {
  // The same basis written down in a different order is the same basis. If
  // this fails, two honest verifiers computing the same context disagree
  // about its name.
  let a = sample()
  let b =
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(2), dig(3), dig(1)],
      rule_sets: [#(key(1), dig(8)), #(key(2), dig(9))],
      hosts: [key(5), key(7)],
    )
  basis.digest(digest.Blake3, a)
  |> should.equal(basis.digest(digest.Blake3, b))
  basis.encode(a) |> should.equal(basis.encode(b))
}

pub fn digest_is_invariant_under_duplication_test() {
  let a = sample()
  let b =
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(1), dig(1), dig(2), dig(3), dig(3)],
      rule_sets: [#(key(1), dig(8)), #(key(1), dig(8)), #(key(2), dig(9))],
      hosts: [key(5), key(5), key(7)],
    )
  basis.digest(digest.Blake3, a)
  |> should.equal(basis.digest(digest.Blake3, b))
}

pub fn digest_distinguishes_genuinely_different_bases_test() {
  let base = sample()
  let variants = [
    basis.Basis(..base, kernel_id: "cronch-kernel/0.2.0"),
    basis.Basis(..base, axioms: [dig(1), dig(2)]),
    basis.Basis(..base, axioms: [dig(1), dig(2), dig(3), dig(4)]),
    basis.Basis(..base, rule_sets: []),
    basis.Basis(..base, hosts: [key(7)]),
  ]
  let digests =
    list.map([base, ..variants], fn(b) { basis.digest(digest.Blake3, b) })
  list.length(list.unique(digests)) |> should.equal(6)
}

pub fn a_field_cannot_be_smuggled_across_a_boundary_test() {
  // Length-prefixed fields, so moving content from one field to the next
  // changes the bytes. Without prefixes these two would encode identically.
  let a = basis.Basis(kernel_id: "ab", axioms: [], rule_sets: [], hosts: [])
  let b = basis.Basis(kernel_id: "a", axioms: [], rule_sets: [], hosts: [])
  { basis.encode(a) == basis.encode(b) } |> should.be_false
}

// ── canonicalize ──────────────────────────────────────────────────────────────

pub fn canonicalize_is_idempotent_test() {
  let once = basis.canonicalize(sample())
  basis.canonicalize(once) |> should.equal(once)
  basis.canonicalize(basis.canonicalize(once)) |> should.equal(once)
}

pub fn canonicalize_sorts_and_dedupes_every_field_test() {
  let c =
    basis.canonicalize(
      basis.Basis(
        kernel_id: kernel_id,
        axioms: [dig(3), dig(1), dig(3)],
        rule_sets: [#(key(2), dig(9)), #(key(2), dig(9))],
        hosts: [key(9), key(1)],
      ),
    )
  c.axioms |> should.equal([dig(1), dig(3)])
  c.rule_sets |> should.equal([#(key(2), dig(9))])
  c.hosts |> should.equal([key(1), key(9)])
}

pub fn canonicalize_leaves_kernel_id_alone_test() {
  // The kernel identifier is not a set and must not be reordered or folded.
  basis.canonicalize(sample()).kernel_id |> should.equal(kernel_id)
}

// ── encode / decode ───────────────────────────────────────────────────────────

pub fn encode_decode_round_trips_test() {
  basis.decode(basis.encode(sample()))
  |> should.equal(Ok(basis.canonicalize(sample())))
}

pub fn empty_basis_round_trips_test() {
  let empty = basis.Basis(kernel_id: "", axioms: [], rule_sets: [], hosts: [])
  basis.decode(basis.encode(empty)) |> should.equal(Ok(empty))
}

pub fn decode_rejects_a_foreign_kind_tag_test() {
  // The domain separation is enforced on the way in, not merely on the way
  // out: a Receipt's bytes are not a Basis, whatever they contain.
  let assert <<_, rest:bits>> = basis.encode(sample())
  basis.decode(<<0x02, rest:bits>>) |> should.be_error
  basis.decode(<<0x00, rest:bits>>) |> should.be_error
}

pub fn decode_rejects_truncation_at_every_length_test() {
  let bytes = basis.encode(sample())
  truncations(bytes, bit_array.byte_size(bytes) - 1)
  |> list.each(fn(prefix) { basis.decode(prefix) |> should.be_error })
}

pub fn decode_rejects_trailing_bytes_test() {
  let bytes = basis.encode(sample())
  basis.decode(<<bytes:bits, 0x00>>) |> should.be_error
}

pub fn decode_rejects_absurd_list_lengths_test() {
  // A declared count of four billion must fail on the first element it cannot
  // read, not attempt to reserve for it.
  basis.decode(<<
    0x01, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
  >>)
  |> should.be_error
}

fn truncations(b: BitArray, n: Int) -> List(BitArray) {
  case n <= 0 {
    True -> [<<>>]
    False -> [take(b, n), ..truncations(b, n - 1)]
  }
}

fn take(b: BitArray, n: Int) -> BitArray {
  let bits = n * 8
  case b {
    <<head:bits-size(bits), _:bits>> -> head
    _ -> b
  }
}

// ── from_environment ──────────────────────────────────────────────────────────

pub fn from_environment_finds_the_artifacts_axioms_test() {
  // `lam (x : S) => x` reaches S, whose declared type is W. Both are
  // signatures with no definition, so both are postulates -- including W,
  // which the artifact never mentions directly.
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [#(corpus.author(), corpus.rule_set_hash())],
      [corpus.host()],
      corpus.annotation_only_artifact(),
    )
  b.axioms
  |> should.equal(canonical.sort_digests([corpus.s(), corpus.w()]))
  b.kernel_id |> should.equal(kernel_id)
}

pub fn from_environment_reports_no_axioms_for_a_closed_term_test() {
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [],
      [],
      term.Lam(term.Sort(0), term.Var(0)),
    )
  b.axioms |> should.equal([])
}

pub fn a_defined_constant_is_not_an_axiom_test() {
  // id_def has a body, so it is not a postulate -- but the body refers to the
  // axiom A, which is.
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [],
      [],
      term.Const(corpus.id_def()),
    )
  list.contains(b.axioms, corpus.id_def()) |> should.be_false
  list.contains(b.axioms, corpus.atom()) |> should.be_true
}

pub fn an_unresolvable_reference_is_recorded_as_an_axiom_test() {
  // Fail closed: a name nobody can supply is an assumption, not an absence.
  // Dropping it would let an artifact understate what it is assuming.
  let missing = dig(0xEE)
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [],
      [],
      term.Const(missing),
    )
  b.axioms |> should.equal([missing])
}

pub fn axioms_are_found_through_a_trusted_procedure_test() {
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [],
      [corpus.host()],
      term.Trusted(
        corpus.host(),
        corpus.proc(),
        term.Const(corpus.elem()),
        term.Const(corpus.atom()),
      ),
    )
  // proc has a definition (its signature `A -> A`), which mentions the axiom A.
  list.contains(b.axioms, corpus.atom()) |> should.be_true
}

pub fn axiom_collection_terminates_on_a_cyclic_store_test() {
  // An adversary supplies the store. Termination must not rest on the graph
  // being acyclic.
  let a = dig(1)
  let b = dig(2)
  let cyclic =
    kernel.Environment(
      definitions: fn(d) {
        case d == a, d == b {
          True, _ -> option.Some(term.Const(b))
          _, True -> option.Some(term.Const(a))
          _, _ -> option.None
        }
      },
      signatures: kernel.empty_signatures(),
      rules: kernel.empty_rules(),
    )
  basis.axioms_of(cyclic, term.Const(a)) |> should.equal([])
}

pub fn from_environment_output_is_already_canonical_test() {
  let b =
    basis.from_environment(
      kernel_id,
      corpus.environment(),
      [#(corpus.author(), corpus.rule_set_hash())],
      [corpus.host(), corpus.other_host()],
      corpus.annotation_only_artifact(),
    )
  basis.canonicalize(b) |> should.equal(b)
}

// ── the floor ─────────────────────────────────────────────────────────────────

pub fn a_basis_one_axiom_over_the_limit_fails_test() {
  let floor =
    basis.BasisFloor(
      required_kernel: kernel_id,
      max_axioms: 2,
      forbidden_axioms: [],
      forbidden_hosts: [],
    )
  let ok =
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(1), dig(2)],
      rule_sets: [],
      hosts: [],
    )
  let over = basis.Basis(..ok, axioms: [dig(1), dig(2), dig(3)])
  basis.satisfies(ok, floor) |> should.be_true
  basis.satisfies(over, floor) |> should.be_false
  basis.failures(over, floor)
  |> should.equal([basis.TooManyAxioms(limit: 2, found: 3)])
}

pub fn duplicates_do_not_count_toward_the_axiom_limit_test() {
  // The count is over the canonical set, so listing an axiom twice cannot
  // push an honest basis over the cap.
  let floor =
    basis.BasisFloor(
      required_kernel: kernel_id,
      max_axioms: 1,
      forbidden_axioms: [],
      forbidden_hosts: [],
    )
  basis.satisfies(
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(1), dig(1), dig(1)],
      rule_sets: [],
      hosts: [],
    ),
    floor,
  )
  |> should.be_true
}

pub fn a_forbidden_host_fails_even_an_otherwise_minimal_basis_test() {
  // No axioms, no rule sets, right kernel -- and still refused, because a
  // single forbidden host is disqualifying on its own.
  let floor =
    basis.BasisFloor(
      required_kernel: kernel_id,
      max_axioms: 0,
      forbidden_axioms: [],
      forbidden_hosts: [key(5)],
    )
  let minimal =
    basis.Basis(kernel_id: kernel_id, axioms: [], rule_sets: [], hosts: [key(5)])
  basis.satisfies(minimal, floor) |> should.be_false
  basis.failures(minimal, floor)
  |> should.equal([basis.ForbiddenHost(key(5))])

  basis.satisfies(basis.Basis(..minimal, hosts: []), floor) |> should.be_true
}

pub fn a_forbidden_axiom_fails_test() {
  let floor =
    basis.BasisFloor(
      required_kernel: kernel_id,
      max_axioms: 10,
      forbidden_axioms: [dig(2)],
      forbidden_hosts: [],
    )
  let b =
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(1), dig(2)],
      rule_sets: [],
      hosts: [],
    )
  basis.satisfies(b, floor) |> should.be_false
  basis.failures(b, floor) |> should.equal([basis.ForbiddenAxiom(dig(2))])
}

pub fn a_different_kernel_fails_test() {
  let floor = basis.purist_floor(kernel_id)
  let b =
    basis.Basis(
      kernel_id: "some-other-kernel/9.9",
      axioms: [],
      rule_sets: [],
      hosts: [],
    )
  basis.satisfies(b, floor) |> should.be_false
  basis.failures(b, floor)
  |> should.equal([
    basis.WrongKernel(required: kernel_id, found: "some-other-kernel/9.9"),
  ])
}

pub fn the_purist_floor_admits_only_an_assumption_free_basis_test() {
  let floor = basis.purist_floor(kernel_id)
  basis.satisfies(
    basis.Basis(kernel_id: kernel_id, axioms: [], rule_sets: [], hosts: []),
    floor,
  )
  |> should.be_true
  basis.satisfies(
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [dig(1)],
      rule_sets: [],
      hosts: [],
    ),
    floor,
  )
  |> should.be_false
}

pub fn failures_is_empty_exactly_when_satisfies_is_true_test() {
  let floors = [
    basis.purist_floor(kernel_id),
    basis.BasisFloor(
      required_kernel: kernel_id,
      max_axioms: 5,
      forbidden_axioms: [dig(1)],
      forbidden_hosts: [key(5)],
    ),
    basis.BasisFloor(
      required_kernel: "other",
      max_axioms: 0,
      forbidden_axioms: [],
      forbidden_hosts: [],
    ),
  ]
  let bases = [
    sample(),
    basis.Basis(kernel_id: kernel_id, axioms: [], rule_sets: [], hosts: []),
    basis.Basis(kernel_id: kernel_id, axioms: [dig(1)], rule_sets: [], hosts: [
      key(5),
    ]),
  ]
  list.each(floors, fn(f) {
    list.each(bases, fn(b) {
      { basis.failures(b, f) == [] } |> should.equal(basis.satisfies(b, f))
    })
  })
}

pub fn satisfies_is_deterministic_across_repeated_calls_test() {
  let floor = basis.purist_floor(kernel_id)
  let b = sample()
  let first = basis.satisfies(b, floor)
  list.each(list.repeat(Nil, 20), fn(_) {
    basis.satisfies(b, floor) |> should.equal(first)
  })
}

// ── the reference rule set as a basis field ───────────────────────────────────

pub fn rule_sets_are_pinned_by_content_hash_test() {
  // A basis names a rule set by (author, exact content hash), so a tampered
  // rule set is a different basis rather than the same one.
  let a =
    basis.Basis(
      kernel_id: kernel_id,
      axioms: [],
      rule_sets: [#(corpus.author(), reference_rules.rule_set_hash())],
      hosts: [],
    )
  let b =
    basis.Basis(..a, rule_sets: [#(corpus.author(), corpus.rule_set_hash())])
  { basis.digest(digest.Blake3, a) == basis.digest(digest.Blake3, b) }
  |> should.be_false
}
