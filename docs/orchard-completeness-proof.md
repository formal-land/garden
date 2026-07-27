# The Orchard circuit-completeness theorem: statement, domain, and scope

Every soundness theorem in the development reads `circuit_holds` in one
direction: assume a satisfying assignment `Γ`, derive functional correctness.
None of them constructs an `Assignment.t`, so on their own they leave open
whether `Holds Γ` is satisfiable at all — a constraint system that accepts
nothing satisfies every soundness statement vacuously.

This document describes the machine-checked theorem in the other direction:
**honest witnesses are accepted**. For every valid, non-degenerate auxiliary
input to a Zcash Orchard action, the witness generator produces an assignment
that the whole action circuit accepts and from which the input reads back.
This is the in-model residue of protocol §4.1.13 completeness at the §4.18.4
Action statement, and it is the non-vacuity certificate for `circuit_holds`:
the accepted set of the deployed action circuit is exhibited as inhabited, by
a generator that is a function of the honest input.

It does not by itself discharge the four witness-honesty premises
(`merkle_witness_ok`, `note_commit_witness_ok`, `old_note_witness_ok`,
`commit_ivk_witness_ok`) that the Action-statement theorem carries. The
`nondegenerate` clauses below are *shaped* so that reading the generated
assignment back turns them into those predicates, but the implications are
not proved; establishing them is what would make this theorem a non-vacuity
certificate for the Action statement itself rather than for `circuit_holds`.

The companion document for the other direction is
[`orchard-soundness-proof.md`](orchard-soundness-proof.md). Both sit on the
relational model of [`chip-model-caveats.md`](chip-model-caveats.md).

## The theorem

`OrchardCompletenessAssembly.orchard_completeness`
(`Garden/Orchard/circuit_completeness/forward/assembly.v`) proves
`OrchardHonestAssignment.orchard_completeness_statement`, which is
`OrchardWitnessInput.completeness_statement` at the generator:

```coq
Definition completeness_statement
    (honest_assignment : HonestInput -> Assignment.t columns RegionId.t) : Prop :=
  forall w : HonestInput,
    valid w -> nondegenerate w ->
    circuit_holds (honest_assignment w) Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
    read_action_inputs (honest_assignment w) = inputs_of w.
```

The first conjunct is acceptance: the generated assignment satisfies, at every
row of every region the circuit's own synthesis program produces, all
configured gates, the copy constraints, the constant bindings and the lookup
arguments. The second is faithfulness of the encoding: the free-witness
readers of `circuit_proof/inputs.v` — the same readers the soundness theorem
uses to define "the genuine inputs" — recover the input record from the
generated assignment. Without it the theorem could be satisfied by a
generator that ignores its input.

The theorem is unconditional and `Qed`.

## The domain

**`valid w`** is the type envelope: the witnessed scalars and Merkle path
entries lie in their declared ranges, the witnessed points are on the curve,
the note values are 64-bit, and the windowed scalars are below `8⁸⁵`. It is
the honest-prover-side counterpart of the input typing that the soundness
theorem derives from circuit satisfaction.

**`nondegenerate w`** excludes the exceptional cases of the incomplete
additions: the chords along the Sinsemilla folds and the variable-base ladder
are non-vertical, so each incomplete-add gate is at a point where it
constrains. These are exactly the conditions under which the deployed circuit
is itself complete; Halo 2's incomplete-add gates are by design unconstraining
on their exceptional pairs.

The ⊥/degenerate branch of §4.18.4 — the `∈ {cm, ⊥}` allowance, the Merkle
hash-outputs-0 case, exceptional incomplete-add pairs — is outside the domain,
which is the same shape as the `*_witness_ok` predicates on the soundness
side. This restricts the theorem's *domain*, not its faithfulness: within the
domain, acceptance is proved for the deployed circuit with no weakening of the
constraint system.

## The gluing lemma

`Complete.circuit_holds_intro` (`Garden/Halo2/complete.v`) is the dual of the
soundness extraction bridges: it reduces `circuit_holds Γ program system` to
finitely many obligations, and is section-parameterized over decidable
equality for the column types and `RegionId`, so it stays chip-generic.

```coq
Theorem circuit_holds_intro {A : Set}
    (Γ : Assignment.t columns RegionId)
    (program : 𝓛 columns RegionId A)
    (system : ConstraintSystem.t columns)
    (Hguarded  : selector_guarded system = true)
    (Hconflict : no_conflicting_writes (layouter_facts program) = true)
    (Hdefaults : lookup_defaults_ok system (layouter_facts program)
                   (layouter_table_rows program) = true)
    (Hplanes   : honest_planes Γ program)
    (Hwitness  : interpret_facts Γ (witness_facts (layouter_facts program)))
    (Hgates    : ... one constraint instance per enabled point ...)
    (Hlookups  : ... one lookup obligation per (enabled point, argument) ...) :
  circuit_holds Γ program system.
```

`honest_planes Γ program` fixes the three determined planes of `Γ` to the
synthesis program's facts. The load-bearing conjunct is that the selector
plane is the **enabled-point indicator**, zero off the points the program
enables. That is the well-formedness property the relational model leaves
implicit, and it makes `satisfies_gates` — which quantifies over *all*
`(region, row)` — vacuous away from the enabled points, so the residual gate
obligation is one constraint instance per enabled point. Advice and instance
planes stay abstract; a witness generator supplies them.

The three Boolean premises are section-closed checkers, discharged per
instance by `vm_compute`: `selector_guarded` (every constraint's top
constructor is `Constraint.Select`), `no_conflicting_writes` (no two
`FixedIs`/`SelectorOn` facts pin one cell to different values), and
`lookup_defaults_ok` (each lookup argument's off-selector padding tuple is a
genuine table row). A Boolean reflection layer lets the finite `Hwitness` /
`Hgates` / `Hlookups` obligations discharge by `vm_compute` on a computable
`Γ`.

`CompleteAdditionCompleteness.completeness`
(`Garden/Halo2/halo2_gadgets/ecc/chip/add_complete.v`) instantiates the lemma
on the complete-addition chip: for any four inputs each on-curve-or-identity
there exists a `Γ` with `circuit_holds` over the add chip whose row-0 cells
read the inputs and whose row 1 reads `CompleteAddition.output`. It needs two
Pallas certificates — the 5-nonresidue and the cubic non-residue
`pallas_neg_b_cubic_nonresidue`; on-curve `y ≠ 0` is load-bearing, since the
gate polynomial is unsatisfiable at a 2-torsion point.

## The witness generator

`OrchardHonestAssignment.honest_assignment`
(`circuit_completeness/generator/honest_assignment.v`) maps a §4.18.4
auxiliary input to an `Assignment.t`: the three determined planes over
`layouter_facts circuit.synthesize`, the advice plane routed per `RegionId`
family to four per-gadget sub-generators, and the instance plane carrying the
nine-element public sequence. `honest_planes_ok` proves the plane conditions
by reflexivity, the fields being the exact honest-plane builders.

`generator/tables.v` hoists the per-family derivation record `tables_of w`
that keeps the whole-circuit `vm_compute` certificates feasible (see
[`compile-performance.md`](compile-performance.md)), with two cell layers:
`tables_vb.v` (the variable-base ladder and overflow block, built by one
linear fold — two field inversions per bit, never a per-cell `Pallas.mul`)
and `tables_nc.v` (the `NoteCommit`/`Commit^ivk` decomposition, y-canonicity,
range-check and lookup cells as div/mod slices of the packed §5.4.8.4
messages).

`generator/certificates.v` instantiates the three checkers at the Orchard
circuit — `selector_guarded_certificate`, `no_conflicting_writes_certificate`
over the 14,773 `layouter_facts`, and `lookup_defaults_certificate` — together
with `layouter_table_rows_eq` (= 1024 = `2^sinsemilla_k`).

## The concrete instance

`OrchardCompletenessInstance.orchard_completeness_instance`
(`circuit_completeness/instance/cert.v`) is the theorem at one explicit
input:

```coq
Theorem orchard_completeness_instance :
  circuit_holds Γtest Garden.Orchard.circuit.synthesize
    (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
  read_action_inputs Γtest = inputs_of test_input.
```

with `Γtest = honest_assignment test_input`. All 4,858 enabled gate points and
all 2,964 witness facts are verified by `vm_compute`, sharded by `RegionId`
family across `instance/shards_*.v` and `instance/witness.v`, with the
domain and nondegeneracy certificates in `instance/domain.v` and the
read-back in `instance/read.v`. It is a
special case of the universal theorem, retained because it is a fully
computational witness: every cell is a closed literal.

## The forward decomposition

`forward/api.v` states the universal obligations: `family_gates_ok` and
`family_lookups_ok` (the `Hgates`/`Hlookups` premises at `honest_assignment
w`, restricted to a list of `family_index` values and quantified over every
valid, non-degenerate input), `witness_facts_forward_ok`, `read_back_ok`, the
coverage layer (`covers`, `all_families`, `all_families_covers`) over the
family partition, the union combinators `family_gates_ok_app` and
`family_lookups_ok_app`, and the join
`completeness_statement_of_families`, which composes covering gate and lookup
obligations with the witness facts and the read-back through
`circuit_holds_intro`.

Per-family lemmas discharge the obligations, each stated either at a family
index or as a selector-keyed refinement:

- **`forward/poseidon.v`** — the permutation family (`[33]`). Its 37 enabled
  points are pinned by an input-independent inventory certificate, then
  discharged as full rounds, partial-round pairs and the pad-and-add row
  against the hoisted schedule, with `poseidon_state` kept `Opaque` so the
  `3^36` round chain is never normalized.
- **`forward/ecc_add.v`** — the addition and witness-point gates over
  `QEccAdd` (21 points), `QAddIncomplete` (518), `QWitnessPoint` and
  `QWitnessPointNonId`. It reuses the witness polynomials of the add-chip
  soundness proof verbatim. Every other family dispatches into it, so it
  exports persistent `Strategy opaque` sets.
- **`forward/fixed_base.v`** — the fixed-base windows: the 850 full-width
  window points, the window-coordinates check, magnitude/sign, and the
  base-field canonicity row, proved from pasted window/on-curve certificate
  tables and the running-sum digit identities of the six legs.
- **`forward/running_sums.v`** — the decomposition and range-check families:
  the bitshift gate through the five `1024·inv_two_pow_s ≡ 2^{10−s}`
  constants, the base-8 digit identity `z_i − 8·z_{i+1} = z_i mod 8`, and the
  range-check lookup whose telescoping step resolves to rows of the 1024-row
  `TableIdx` table.
- **`forward/sinsemilla.v`** — the hash-round family over the 32 Merkle
  regions and the three commitment regions. The round identities are proved
  as congruences modulo the Pallas prime (`ya_row_eqm`, `chord_next_eqm`),
  each resting on the non-vertical second chord that `nondegenerate w`
  supplies; one region-generic lemma pair is instantiated at each hash family.
- **`forward/var_base_ladder.v`** — the variable-base family (`[37]`), 293
  points. `ladder_go_chain` identifies the emitted step rows with the
  specification accumulators `macc α B i = repr ([2^(255−i) + 2 z_i + 1] B)`,
  and the three gate bodies are discharged over *abstract* row values, so no
  ring step ever reifies a `tables_of` projection.
- **`forward/canonicity.v`** — the `Commit^ivk` and `NoteCommit`
  decomposition, canonicity and y-canonicity families (`[38; 39; 40]`). Every
  decomposition constraint is an exact integer recombination of div/mod
  slices, and every clause conditioned on a top bit follows from
  `x < p = 2^254 + t_P` pinning the low 254 bits below `t_P`.
- **`forward/residual.v`** — the families no other file reaches: `QOrchard`
  (the whole-circuit checks gate), `QAdd`, the Merkle cond-swap and node
  decomposition gates — 66 points across families 1..32, 35 and 42.
- **`forward/read_back.v`** — the second conjunct, resolved symbolically: each
  field's residue is the identity because the honest cell is already a field
  element, the windowed scalars are reconstructed from their base-8 window
  cells, and the public anchor row is identified with the specification root
  through the layer-chain bridge.

`forward/lookups_witness.v` carries the whole-circuit lookup obligation
`lookups_forward_ok : family_lookups_ok all_families`. The site inventory is
one input-independent scan over the enabled points; the 20 running-sum and 89
short range-check sites are proved symbolically from the honest cells' div/mod
bounds; and the five Sinsemilla generator-table site leaves reduce, through
one generic site lemma, to a per-row obligation where the loaded table's three
columns read back as the row index and the two `sinsemilla_s` coordinates.

The same file carries the witness-fact obligation, split by the Boolean
`fact_trivial`: the 2,076 self-copy facts hold of any assignment, and the 888
remaining facts (716 cross-region copies, 166 pinned constants, 6 instance
rows) are pinned as a literal whose coverage of the reified `witness_facts` is
one input-independent scan. Of those, 791 are closed in place — the copies
whose two cell addresses the advice dispatch sends to the same reader
expression, the four blinding-leg boundaries, and the 64 Merkle-chain facts.
The residual 97, whose two sides are *different derivations* of one value, are
proved by the five group lemmas of `forward/witness/`, split by proof shape:
`bits_column.v` (38), `chain_outputs.v` (8), `slice_bounds.v` (32),
`fixed_legs.v` (12) and `var_base.v` (7). The partition is sound because the
coverage scan is an order-insensitive `existsb` over the fact multiset, so any
regrouping that preserves that multiset re-runs unchanged.

`forward/assembly.v` composes the lanes. Its gate side is proved by case
analysis on the guarding selector of an enabled point, routing each of the 56
`Selector.t` constructors to the lane that proves its bodies. Selector
coverage is total, so the family hypothesis is never needed and the obligation
holds at `all_families` — every family index `0..42`, including the vacuous
`41`. The three lanes stated at a family index need the converse fact, that an
enabled point guarded by one of their selectors lies in one of their families,
supplied by a single input-independent scan over the 4,858 enabled points.

## The operational layer

`orchard_completeness` is a statement about the relational model.
`circuit_completeness/operational/` carries it across the bridge of
[`operational-soundness.md`](operational-soundness.md) to the ideal
`mock_prover_accepts` checker that mirrors Rust Halo 2's `MockProver` on the
serialized circuit. It is the mirror of `orchard_operational_sound`, at the
same checker and the same event stream:

```coq
Theorem orchard_operational_complete (w : HonestInput) (g : RawGrid.t) :
  valid w -> nondegenerate w ->
  apply_events orchard_events
    (initial_grid (orchard_advice w) (orchard_instance w)) = Some g ->
  mock_prover_accepts orchard_indexed_system orchard_events g
    orchard_table_rows.
```

The two free planes are chosen from the honest generator — `orchard_advice`
pulls the honest advice plane back along the placement through an
input-independent address map, `orchard_instance` is the honest instance plane
— and the Orchard event stream is replayed onto them.
`orchard_operational_complete_ex` is the unconditional form, replay success
being grid-independent.

The substance is the **grid identification**, and the direct route does not
work: total pointwise agreement between `honest_assignment w` and
`realize idx rs g` is false. `region_start_of` is not row-injective (region
indices 1 and 26 both start at 1766, 4 and 43 at 1760 — 127 colliding index
pairs among the 394 placed regions) and regions are densely packed, so an
offset outside one region's extent can land on the absolute row of another
region's enabled point, where the realized selector plane reads 1 while
`Complete.enabled_memb` is false. The realized lookup plane diverges past
`orchard_usable_rows`. `Complete.honest_planes` is therefore *false* at the
realized assignment, and `circuit_holds_intro` does not apply to it.

The replacement is a **placed re-derivation** (`operational/placed_intro.v`,
generic in the columns, placement and program): `placed_selector_off` replaces
the region-local selector conjunct with "the selector plane is 0 at every
absolute address that is not an enabled point's", the lookup conjunct shrinks
to the single row-0 equation the padding branch reads, and the residual
per-point obligations are stated at every `(region, row)` whose *absolute* row
is an enabled point's, then moved to the point by `realize_eval_expression` on
both sides. `placed_circuit_holds_intro` assembles those with the determined
facts, which follow from replay success alone.

The supporting layers are `operational/replay_planes.v` (the replay never
writes the advice or instance plane, so both are the chosen planes verbatim;
the write-frame converses turn a Boolean "no such event" scan into a plane
reading), `operational/agreement_congruences.v` (query extractors on
expressions, constraints and lookup arguments, the agreement congruences over
them, and the realized row shift), and `operational/certs.v` — nine
certificates, every one input-independent, mentioning only `layouter_facts`,
the configured system, the event stream and the placement, never `tables_of
w`. Because the certificate layer is input-independent, the concrete and
universal rungs share it verbatim and nothing in it is proportional to the
witness values.

The full stream is not a literal instance of `realize/sound.v`'s
`operational_complete`: that theorem's replay premise names the synthesis-only
stream at the same grid, while the Orchard honest grid replays
`orchard_synthesis_events ++ orchard_constants_events`, whose 166 trailing
`AssignFixed` events change the fixed plane. The headline therefore goes
through `operational_complete_events_app` — strictly fewer premises, a longer
stream, the same conclusion — with the tail's 166 `Copy` obligations
discharged separately. `orchard_operational_complete_sound` is the literal
instance on the synthesis-only stream.

## What this does not ensure

- **Cryptographic completeness.** The theorem is about the constraint system:
  an honest witness satisfies it. It says nothing about the proving system —
  that a prover holding such a witness produces a proof a verifier accepts is
  a property of Halo 2, not of the circuit.
- **The degenerate branch.** Inputs outside `valid`/`nondegenerate` are not
  covered, as described under "The domain".
- **The model caveats.** The operational layer closes the completeness
  direction against the *same* ideal checker the soundness direction uses; it
  does not narrow the gap recorded in
  [`operational-soundness.md`](operational-soundness.md).
  `mock_prover_accepts` still quantifies over all integer rows rather than the
  `2^k` cyclic domain.

## Model caveats inherited by the theorem

The relational model idealizes real Halo 2 in the ways documented in
[`chip-model-caveats.md`](chip-model-caveats.md). Completeness is affected by
them in the opposite direction from soundness: a model that is more permissive
than reality makes acceptance *easier* to prove. The two that bear on how to
read this theorem are the abstraction of regions into independent integer
address spaces, and the dropping of the cyclic evaluation domain — both of
which the operational layer addresses for the placement, by replaying onto a
single absolute-row grid and proving acceptance there.

The lookup-table fill on the blinding rows is keygen-faithful; see
[`realize-overfill-fix.md`](realize-overfill-fix.md).

## Assumption audit

`Print Assumptions` on every theorem named in this document, run against a
full `.vo` build, reports exactly `PrimString.string : Set` (a primitive-string
artifact of the string-keyed column maps) plus the impredicative `Set` the
development is compiled with. There is no `Admitted`, `Axiom` or `admit`
anywhere under `Garden/Orchard/` or `Garden/Halo2/`.
