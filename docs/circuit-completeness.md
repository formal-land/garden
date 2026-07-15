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
  "Per-cell witness generators…").

### The constructive C1 instance (statement `Qed`, audit not yet clean)

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

**The theorem is `Qed`, but its assumption audit is not yet clean.** It rests
on 5 `Admitted` leaf certificates, which `Print Assumptions` reports alongside
`PrimString.string` + impredicative `Set`:

- `instance_shards_blocked.shard_37_ok` … `shard_40_ok` — 17 of the 4,858
  enabled gate points: the variable-base-mul ladder interior rows
  (`AddressIntegrity`, families 37) and the `NoteCommit` / `Commit^ivk`
  decomposition + canonicity subregions (families 38/39/40). The exact failing
  points are listed in the file.
- `instance_witness.witness_facts_ok` — 84 of the 2,964 copy/constant witness
  facts, the copies between those same stubbed decomposition/canonicity cells
  and their generated sources.

All are the same root cause: the C2-scale sub-generator cells (var-base
double-and-add interior, NoteCommit/CommitIvk decomposition + canonicity) are
deliberately left at 0 in the current generator. **4,841 enabled points and
2,880 witness facts are machine-verified by `vm_compute`.** No statement was
weakened; completing these is generator work, not a test-vector or layout bug.

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

## Status and what remains

Proved and clean (`PrimString.string` + impredicative `Set`):

- `Complete.circuit_holds_intro` — the generic gluing lemma.
- `CompleteAdditionCompleteness.completeness` — the add-chip instance.
- The Orchard supporting infrastructure: `decidable_eq.v`, the three
  `certificates.v` checkers, the `honest_assignment` generator with
  `honest_planes_ok`.

Delivered but not yet axiom-free:

- `orchard_completeness_instance` — `Qed`, but resting on the 5 `Admitted`
  leaf certificates above (17 enabled points + 84 witness facts of the stubbed
  C2-scale sub-generator cells).

Remaining:

1. Complete the stubbed sub-generator cells (var-base ladder interior,
   NoteCommit/CommitIvk decomposition + canonicity) so the 5 `Admitted` leaves
   close and the C1 instance becomes axiom-free.
2. The universally quantified theorem
   `completeness_statement honest_assignment` — the per-gate forward lemmas,
   per-region-family generator↔gate lemmas, and assembly (the C2 campaign).
