# Completeness of `circuit_holds`: the honest-witness surface

Every soundness theorem in the development uses `circuit_holds` in one
direction: assume a satisfying `Γ`, derive functional correctness. Nothing
there constructs an `Assignment.t`, so nothing shows `Holds Γ` is even
satisfiable. This note records the **completeness** direction — *honest
witnesses are accepted* — the in-model residue of protocol §4.1.13
completeness at the §4.18.4 Action statement, plus a non-vacuity certificate
for the whole soundness surface (including satisfiability of the
`merkle_witness_ok` / `note_commit_witness_ok` honesty hypotheses). It sits on
the relational model of [`chip-model-caveats.md`](chip-model-caveats.md); the
planning record is `docs-local/circuit-completeness-plan.md`.

The ⊥/degenerate branch of §4.18.4 (`∈ {cm, ⊥}`, the Merkle hash-outputs-0
allowance, exceptional incomplete-add pairs) is out of scope: the completeness
domain is restricted to non-degenerate honest inputs, the same shape as the
existing `*_witness_ok` predicates. This weakens the theorem's *domain*, not
its faithfulness.

## The generic gluing intro lemma

`Complete.circuit_holds_intro` (`Garden/Halo2/complete.v`) is the dual of the
soundness extraction bridges: it reduces `circuit_holds Γ program system` to
finitely many obligations. It is section-parameterized over decidable equality
for the column types and `RegionId`, so it stays chip-generic.

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
    (Hgates    : forall selector region row,
       In (selector, region, row) (enabled_points (layouter_facts program)) ->
       ... one constraint instance per enabled point ...)
    (Hlookups  : forall selector region row,
       In (selector, region, row) (enabled_points (layouter_facts program)) ->
       ... one lookup obligation per (enabled point, mentioning argument) ...) :
  circuit_holds Γ program system.
```

The key is `honest_planes Γ program`: a predicate fixing the three
concrete planes of `Γ` to the synthesis program's facts — critically, the
selector plane is the **enabled-point indicator** (0 off the points the
program enables). This is exactly the well-formedness fact the relational
model did not previously track, and it makes `satisfies_gates` (quantified
over *all* `(region, row)`) vacuous off the enabled points, so the residual
gate obligation is one constraint instance per enabled point. Advice and
instance planes stay abstract in the predicate; a witness generator provides
them downstream.

The three Boolean premises are section-closed checkers discharged by
`vm_compute` per instance:

- `selector_guarded system` — every constraint's top constructor is
  `Constraint.Select` (all gates build through `Constraints.with_selector`).
- `no_conflicting_writes facts` — no two `FixedIs`/`SelectorOn` facts pin one
  cell to different values.
- `lookup_defaults_ok system facts nb_table_rows` — each lookup argument's
  off-selector padding tuple is a genuine table row (row 0). Lookup-free chips
  (`system.lookups = []`) pass unconditionally.

A Boolean reflection layer (`check_constraint` / `check_gate` /
`check_lookup` / `check_witness_facts`, each with a soundness lemma) lets the
finite `Hwitness` / `Hgates` / `Hlookups` obligations discharge by
`vm_compute` on a computable `Γ`.

Assumption audit (full-`.vo` `Print Assumptions`): exactly `PrimString.string`
+ impredicative `Set`.

## Add-chip smoke test

`CompleteAdditionCompleteness.completeness`
(`Garden/Halo2/halo2_gadgets/ecc/chip/add_complete.v`) validates the Stage-A
API end to end on the complete-addition chip: for any four inputs each
on-curve-or-identity, there **exists** a `Γ` with `circuit_holds` over the
`add` chip's `synthesize`/`configure`, whose cells at row 0 read the four
inputs and whose row 1 reads `CompleteAddition.output`. `Γ` is explicit
(chord/tangent/zero-case λ, `mod_inverse` inverse witnesses), one region with
one enabled point, discharged through `circuit_holds_intro`. The proof needs
two Pallas certificates — the existing 5-nonresidue and a new cubic
non-residue `pallas_neg_b_cubic_nonresidue` (on-curve `y ≠ 0` is load-bearing:
the gate polynomial is unsatisfiable for a 2-torsion point). All `Qed`;
assumption audit exactly `PrimString.string` + impredicative `Set`.

## The Orchard whole-circuit instance

### Supporting infrastructure (all `Qed`, clean audit)

- `Garden/Orchard/decidable_eq.v` — decidable equality for the Orchard column
  types and the nested `RegionId.t` (`selector_eqb`, `fixed_eqb`,
  `lookup_eqb`, `region_id_eqb`, with their `_eq` reflection lemmas), used
  verbatim by both the certificates and the generator.
- `Garden/Orchard/circuit_completeness/certificates.v`
  (`OrchardCompletenessCertificates`) — the three section-closed checkers
  instantiated at the Orchard circuit: `selector_guarded_certificate`,
  `no_conflicting_writes_certificate` (over the 14,773 `layouter_facts`),
  `lookup_defaults_certificate` (the three configured lookups collapse to
  table row 0), plus `layouter_table_rows_eq` (= 1024 = `2^sinsemilla_k`) and
  `enabled_points_sound`.
- `Garden/Orchard/circuit_completeness/honest_assignment.v`
  (`OrchardHonestAssignment`) — the witness generator
  `honest_assignment : HonestInput -> Assignment.t columns RegionId.t`: the
  three concrete planes over `layouter_facts circuit.synthesize`, the advice
  plane routed per `RegionId` family to the per-gadget sub-generators, the
  instance plane reading the §4.18.4 public sequence. `honest_planes_ok`
  proves the three plane conditions by reflexivity (the fields are the exact
  honest-plane builders).
- `Garden/Orchard/circuit_completeness/tables.v` — the hoisted per-family
  derivation record (`tables_of w`) that keeps the whole-circuit `vm_compute`
  certificates feasible (see [`compile-performance.md`](compile-performance.md),
  "Per-cell witness generators…"), together with its two cell layers:
  `tables_vb.v` (the variable-base double-and-add ladder and overflow block,
  built by one linear fold — two field inversions per bit, never a per-cell
  `Pallas.mul`) and `tables_nc.v` (the `NoteCommit`/`Commit^ivk`
  decomposition, y-canonicity, range-check and lookup cells as pure
  div/mod bit slices of the packed §5.4.8.4 messages).

### The constructive C1 instance (`Qed`, clean audit)

`OrchardCompletenessInstance.orchard_completeness_instance`
(`Garden/Orchard/circuit_completeness/instance_cert.v`):

```coq
Theorem orchard_completeness_instance :
  circuit_holds Γtest Garden.Orchard.circuit.synthesize
    (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
  read_action_inputs Γtest = inputs_of test_input.
```

for one concrete valid, nondegenerate `test_input` with
`Γtest = honest_assignment test_input`. It is proved through
`circuit_holds_intro`: the three checker certificates, `honest_planes_ok`, and
a sharded `check_point` truth table over the 4,858 enabled gate points and
2,964 witness facts (sharded by `RegionId` family across
`instance_shards_merkle.v`, `instance_shards_misc.v`,
`instance_shards_blocked.v`, `instance_witness.v`; the domain/nondegeneracy
certificates in `instance_domain.v` + `instance_mul_{a..d}.v`; read-back in
`instance_read.v`).

**All 4,858 enabled points and all 2,964 witness facts are machine-verified
by `vm_compute`.** The full-`.vo` `Print Assumptions` audit of
`orchard_completeness_instance` reports exactly `PrimString.string` +
impredicative `Set`.

### The universally quantified target (stated only)

`OrchardHonestAssignment.orchard_completeness_statement` is
`OrchardWitnessInput.completeness_statement honest_assignment`:

```coq
Definition completeness_statement
    (honest_assignment : HonestInput -> Assignment.t columns RegionId.t) : Prop :=
  forall w : HonestInput,
    valid w -> nondegenerate w ->
    circuit_holds (honest_assignment w) Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
    read_action_inputs (honest_assignment w) = inputs_of w.
```

It is stated as a `Prop` only (well-formedness checked). Its proof is the C2
follow-up campaign.

The statement API of that campaign is
`Garden/Orchard/circuit_completeness/forward/api.v`
(`OrchardCompletenessForward`, all `Qed`): the per-family symbolic
obligations `family_gates_ok` / `family_lookups_ok` (the `Hgates` /
`Hlookups` premises of `circuit_holds_intro` at `honest_assignment w`,
restricted to a list of `family_index` values and quantified over every
valid, nondegenerate input), `witness_facts_forward_ok` and `read_back_ok`,
the coverage layer (`covers`, `all_families`, `all_families_covers`) over
the `instance_defs.v` family partition, union/anti-monotonicity combinators
(`family_gates_ok_app` / `_incl`, likewise for lookups), and the assembly
skeleton `completeness_statement_of_families`: covering gate and lookup
obligations plus the witness facts and the read-back compose through
`circuit_holds_intro` (with the three checker certificates and
`honest_planes_ok`) into `orchard_completeness_statement`. The per-family
forward lemmas plug into this join as they are proved.

`forward/lookups_witness.v` (`OrchardForwardLookupsWitness`) carries the
lookup and witness-fact sides of that join:

- `lookups_forward_ok : family_lookups_ok all_families` — the whole-circuit
  lookup obligation. The site inventory is certified by one input-independent
  `vm_compute` scan over the 4,858 enabled points (`lookup_scan`), and every
  10-bit range-check site is proved symbolically: the 20 running-sum lookup
  sites (nullifier α canonicity, variable-base overflow, `Commit^ivk` and
  `NoteCommit` canonicity, y-canonicity `j`/`j′`) through
  `running_site_lemma`, and the 89 short range-check sites (the 64 Merkle
  `b_1`/`b_2` checks, the `Commit^ivk` `b_0`/`b_2`/`d_0` checks, the
  `NoteCommit` sub-piece and `k_0`/`k_2` checks) through `short_site_lemma`,
  with the honest cells' div/mod bounds. Open: the five Sinsemilla
  generator-table site leaves (`sins_site_merkle_1`/`_2`, `sins_site_civk`,
  `sins_site_nc_old`/`_new`, currently `Admitted`) — the hash-region round
  tuples `(word, x_p, y_p)`, whose closure needs the `bits`-column
  telescoping and the `y_p` reconstruction algebra over the non-vertical
  chords of `nondegenerate w`.
- `witness_facts_ok : witness_facts_forward_ok` — split by the Boolean
  `fact_trivial`: the 2,076 self-copy facts hold of any assignment
  (`fact_trivial_sound`); the residue (716 cross-region copies, 166 pinned
  constants, 6 instance rows) is the open leaf `nontrivial_witness_facts`
  (`Admitted`).

`forward/running_sums.v` (`OrchardForwardRunningSums`, all `Qed`) carries the
running-sum decomposition and lookup range-check gate families, stated as the
selector-keyed refinement of the api obligations
(`selector_gates_ok`/`selector_lookups_ok` fix the point's guarding selector
instead of its region family; the family joins follow by case analysis on the
selector). Delivered: `qbitshift_gates_ok` (the short-lookup bitshift gate —
the honest row-1 cells satisfy `word·2^10·inv_two_pow_s = shifted` via the
five `1024·inv_two_pow_s ≡ 2^{10−s}` constants), `qmulfixedrs_range_gates_ok`
(the range-check constraint at every enabled `QMulFixedRunningSum` point —
the honest `A4` cells are the base-8 running sums `z_i = k/8^i`, so
`z_i − 8·z_{i+1} = z_i mod 8` is a genuine digit; the coordinates-check
constraints under the same selector are split off to the fixed-base window
family by `qmulfixedrs_body_eq`), `qlookup_lookups_ok`/`qrunning_lookups_ok`
(the range-check lookup argument: the `q_running` telescoping step
`z_i − 2^10·z_{i+1} = z_i mod 2^10` and the bounded short-row element resolve
to rows of the 1024-row `TableIdx` table), and the vacuous complements
(`QLookup`/`QRunning` guard no gate; no lookup argument mentions
`QBitshift`/`QMulFixedRunningSum`). Each selector's enabled-point domain and
constraint/argument classification is pinned by one input-independent
`vm_compute` certificate over the reified synthesis facts.

## Status and what remains

Proved and clean (`PrimString.string` + impredicative `Set`):

- `Complete.circuit_holds_intro` — the generic gluing lemma.
- `CompleteAdditionCompleteness.completeness` — the add-chip instance.
- The Orchard supporting infrastructure: `decidable_eq.v`, the three
  `certificates.v` checkers, the `honest_assignment` generator with
  `honest_planes_ok`, and the cell layers `tables.v` / `tables_vb.v` /
  `tables_nc.v`.
- `orchard_completeness_instance` — the whole-circuit C1 instance.

Remaining:

1. The universally quantified theorem
   `completeness_statement honest_assignment` — the per-gate forward lemmas,
   per-region-family generator↔gate lemmas, and assembly (the C2 campaign).
