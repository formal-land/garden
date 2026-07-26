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

### The universally quantified statement

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

It is the C2 target. `OrchardCompletenessAssembly.orchard_completeness`
(`forward/assembly.v`) proves it from the four `forward/api.v` obligations;
the composition and all four obligations audit at the repo baseline, so the
theorem is unconditional (see "Status and what remains").

The statement API of the campaign is
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
  with the honest cells' div/mod bounds. The five Sinsemilla generator-table
  site leaves (`sins_site_merkle_1`/`_2`, `sins_site_civk`,
  `sins_site_nc_old`/`_new`) — the hash-region round tuples
  `(word, x_p, y_p)` — are `Qed` through the nested module
  `SinsemillaSites`: one generic site lemma (`sins_site_generic`) reduces a
  region to its per-row pair obligation (`sins_row`), where the loaded
  table's three columns read back as the row index and the two
  `sinsemilla_s` coordinates (`lookup_plane_idx` / `lookup_plane_x` /
  `lookup_plane_y`, on the `table_x_entry` / `table_y_entry` `vm_compute`
  certificates and the 1,024-entry reducedness scan `s_entries_ok`), the
  `bits`-column telescoping supplies the round word against the
  `q_sinsemilla2` piece schedule (`bits_step` over the piece-length layout,
  matched to the fixed plane by the per-row certificates
  `merkle_row_certs` / `civk_row_certs` / `nc_old_row_certs` /
  `nc_new_row_certs`), and the `y_p` reconstruction
  `(λ₁+λ₂)·(x_a − x_r)·2⁻¹ − λ₁·(x_a − x_p) = y_p` runs as a linear
  combination of the round algebra of `forward/sinsemilla.v` (`mid_x_eqm`,
  `mid_y_eqm`, `chord2_mul`) with the first chord's exactness (`chord1_mul`)
  and `2·2⁻¹ ≡ 1`, under the non-vertical chords of `nondegenerate w`. The
  export is therefore complete: `lookups_forward_ok` audits at the repo
  baseline (`PrimString.string` + impredicative Set).
- `witness_facts_ok : witness_facts_forward_ok` — split by the Boolean
  `fact_trivial`: the 2,076 self-copy facts hold of any assignment
  (`fact_trivial_sound`), and the 888 non-self-copy facts (716 cross-region
  copies, 166 pinned constants, 6 instance rows) are pinned as a literal
  whose coverage of the reified `witness_facts` is one input-independent
  `vm_compute` scan (`nt_cover`, through the structural `fact_beq`). 791 of
  them are proved (`nt_closed_ok`): the 723 copies whose two cell addresses
  the advice dispatch sends to the same reader expression — the goal is a
  syntactic identity between two stuck projections of the hoisted record,
  with `tables_of`, the field inverse, the complete-addition output and the
  scalar multiplications held opaque so no spec fold is normalized
  (`wf_fact`); the four blinding-leg boundaries, where the commitment
  region's second summand is the leg sum of the last window row
  (`t_nco_pt_shape` / `t_ncn_pt_shape`); and the 64 Merkle-chain facts —
  every layer's hash region starts at the domain point (`merkle_h2p_init`)
  and ends at the next running node (`merkle_h2p_out` against
  `merkle_node_read`, on `t_layers_nth`, `merkle_hash_len` and
  `merkle_node_succ`), the chain starting at the old note commitment
  (`merkle_node_zero`). The remaining 97 facts — the ones whose two sides are
  *different derivations* of one value — are `open_witness_facts`, stated over
  the residue list `nt_open` and proved by the five group lemmas of
  `forward/witness/` (below).

`forward/witness/` holds the residue, split by proof shape into five files
that each pin their own facts and prove them, and are joined by `nt_open`:
`bits_column.v` (38 facts: the `NoteCommit` / `Commit^ivk` message-piece,
input-decomposition and witness cells against the hash region's `bits`
column, through one closed form for a `bits_column` index inside a piece),
`chain_outputs.v` (8: a hoisted fold's final row read from the consuming
region — the three hash outputs, the anchor against layer 31, the Poseidon
state), `slice_bounds.v` (32: `Z` div/mod identities between two readers of
one value, needing only the `valid w` ranges), `fixed_legs.v` (12: the
fixed-base legs identified with the specification scalar multiplications,
including the six `InstanceIs` rows) and `var_base.v` (7: the variable-base
ladder and overflow-block boundaries). None of them may `Require`
`lookups_witness.v` — it requires them.

`forward/poseidon.v` (`OrchardForwardPoseidon`, all `Qed`) carries the
Poseidon permutation family and delivers both api obligations at their family
index directly: `poseidon_gates_ok : family_gates_ok [33]` and
`poseidon_lookups_ok : family_lookups_ok [33]`. The family's 37 enabled points
— the `AddInput` pad-and-add row and the 36 `PermuteState` rows — are pinned
by the input-independent `vm_compute` inventory `poseidon_points_eq`, and each
selector's guarded constraint bodies by `guarded_full_eq` /
`guarded_partial_eq` / `guarded_pad_eq`; the rows are then discharged as
full rounds (`full_round_complete`), partial-round pairs
(`partial_round_complete`) and the pad-and-add row (`pad_input_ok`) against
the hoisted Poseidon schedule, with `poseidon_state` / `pose_states_of` kept
`Opaque` so the `3^36` round chain is never normalized. The lookup obligation
is vacuous (`poseidon_no_lookup_mentions`). This file is the shape every other
family follows.

`forward/ecc_add.v` (`OrchardCompletenessForwardEccAdd`, all `Qed`) carries
the elliptic-curve addition and witness-point gates, stated as the
selector-keyed refinement `ecc_selector_gates_ok` over `QEccAdd` (the 12
complete-addition polynomials, 21 points), `QAddIncomplete` (518 points),
`QWitnessPoint` and `QWitnessPointNonId`. It reuses the witness polynomials
of the add-chip soundness proof (`add_complete.v`) verbatim, so the honest
cells satisfy the complete-addition case analysis by construction;
`ecc_add_lookups_forward` is vacuous. This file is dispatched into by the
`QEccAdd`/`QAddIncomplete` points of every other family, so it exports
persistent `Strategy opaque` sets (see `docs/compile-performance.md`).

`forward/fixed_base.v` (`OrchardForwardFixedBase`, all `Qed`, on the window
tables of `forward/fixed_base_certs.v`) carries the fixed-base scalar
multiplication windows, stated as the same selector-keyed refinement:
`q_mul_fixed_full_gates_ok` (the 850 full-width window points),
`q_mul_fixed_running_sum_gates_ok` (the window coordinates check),
`q_mul_fixed_short_gates_ok` (magnitude/sign) and
`q_mul_fixed_base_field_gates_ok` (the base-field-element canonicity row),
with all four lookup complements vacuous (`fb_lookups_vacuous`). The window
rows are proved from the pasted window/on-curve certificate tables and the
running-sum digit identities of the six fixed-base legs.

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

`forward/sinsemilla.v` (`OrchardForwardSinsemilla`, all `Qed`) carries the
Sinsemilla hash-round gate family — the 32 Merkle `HashToPoint` regions and
the old/new `NoteCommit` and `Commit^ivk` hash regions. It delivers
`sinsemilla_gates_forward : sins_selector_gates_ok`, the same selector-keyed
refinement of the api obligation (the four Sinsemilla selectors
`QSinsemilla1_1`/`1_2`/`4_1`/`4_2` are enabled exactly on those regions' hash
rows, so this is the hash-round slice of the Merkle and
`Commit^ivk`/`NoteCommit` family gate obligations). The chain is: the
`hash_go` fold bridge identifies the hoisted table rows with the per-round
accumulator, generator and chord gradients of the specification fold; the
round identities are proved as congruences modulo the Pallas prime
(`ya_row_eqm`: the chip's doubled ordinate `y_a` at a round row is twice the
accumulator's ordinate; `chord_next_eqm`: the second gradient times the run
across the round is the sum of the two ordinates), each resting on the
non-vertical second chord that `nondegenerate w` supplies (`chord2_nonzero`);
the three gate bodies are discharged over an abstract assignment
(`secant_eval`, `ycheck_interior_eval`, `ycheck_final_eval`, `init_eval`),
the interior/final split keyed by the `q_sinsemilla2` schedule; and one
region-generic lemma pair (`hash_region_gates`/`hash_region_init`) is
instantiated at each of the four hash families from the generator's advice
dispatch, the region's `vm_compute` fixed-plane certificates (the piece
schedule and the domain ordinate), and the message-length identities.

`forward/var_base_ladder.v` (`OrchardVarBaseForward`, all `Qed`) carries the
variable-base multiplication family — the `AddressIntegrity` regions — and
delivers the two api obligations at their family index directly:
`var_base_gates_ok : family_gates_ok [37]` and
`var_base_lookups_ok : family_lookups_ok [37]`. The family's 293 enabled
points are classified by one input-independent `vm_compute` inventory
(`pt37_cert`) over the reified synthesis facts, and dispatched per selector:
the 253 `QMulIncomplete{Hi,Lo}{1,2,3}` ladder rows, the three
`QMulDecomposeVar` complete-round rows, the `QMulLsb` row, the
`QMulOverflow` canonicity row, the witnessed `pk_d_old` point
(`QWitnessPointNonId`), and the range-check rows of the overflow block; the
family's `QEccAdd` points reuse the selector-sliced
`ecc_add_gates_forward`. The ladder rows are proved from the hoisted record
of `tables_vb.v`: `ladder_go_chain` identifies the emitted step rows with
the specification accumulators `macc alpha B i = repr ([2^(255−i) + 2 z_i +
1] B)` under the per-step nondegeneracy of `nondegenerate w`, `step_alg`
turns one such row into the four gate-level identities (`y_a` recovers the
accumulator ordinate, `λ₁` multiplies back to the first chord, the next
accumulator abscissa is `next_x_a`, and the second chord closes), and the
three gate bodies (`q_mul_1_gate` / `q_mul_2_gate` / `q_mul_3_gate`) are
discharged over *abstract* row values — no ring step ever reifies a
`tables_of` projection. Both halves are the same generic step site
(`site_step1` / `site_step2` / `site_step3`) at their own columns and bit
indices (`z = A9`, `x_a = A3`, `λ₁ = A4`, `λ₂ = A5` for bits 254..130;
`z = A6`, `x_a = A7`, `λ₁ = A8`, `λ₂ = A2` for bits 129..4), with the row
guards of the generator's dispatch resolved symbolically by the cell
readers. The lookup obligation is the 13 running-sum rows of the overflow
block through `site_ovl_lookup`, plus the `vm_compute` scan
`vb_mentions_cert` showing no configured argument mentions any of the
family's gate selectors.

`forward/canonicity.v` (`OrchardCanonicityForward`, all `Qed`) carries the
`Commit^ivk` and `NoteCommit` decomposition, canonicity and y-canonicity
families and delivers `canonicity_gates_ok : family_gates_ok [38; 39; 40]`.
The 1,711 enabled points of the three families are split by one
input-independent `vm_compute` certificate (`shard_classify`) into the 25
canonicity gate rows proved here and the points whose guarding selector
belongs to another lane — `QEccAdd`/`QAddIncomplete`
(`ecc_add_gates_forward`), `QMulFixedFull`
(`q_mul_fixed_full_gates_ok`), `QLookup`/`QRunning`/`QBitshift`
(`qlookup_gates_ok` / `qrunning_gates_ok` / `qbitshift_gates_ok`), and the
four Sinsemilla selectors of the hash regions
(`sinsemilla_gates_forward`). Each of the 23 canonicity selectors' gate
bodies is pinned by a `vm_compute` certificate against the configured
system (`guarded_civk_eq`, `guarded_old_*`, `guarded_new_*`); the gate
bodies themselves are discharged over an abstract assignment, one lemma
per gate shape (`mpb_gate_eval` … `mph_gate_eval`, `gd_gate_eval`,
`pkd_rho_gate_eval`, `value_gate_eval`, `psi_gate_eval`,
`ycanon_gate_eval`, `civk_gate_eval`), from the packed-message slice
identities of `tables_nc.v`: every decomposition constraint is an exact
integer recombination (`recomb_*`) of div/mod slices, and every clause
conditioned on a top bit follows from `x < p = 2^254 + t_P` pinning the low
254 bits below `t_P` (`top1_low`, `top1_slice_zero`, `top1_mod_low`,
`prime_of_zero`). The generator's cells are identified with those slices
by the `nc_*_eq` / `civk_*_eq` projections, and the per-point instances are
routed through the two note-block dispatch equations
(`disp_old` / `disp_new`).

`forward/residual.v` (`OrchardForwardResidual`, all `Qed`) covers the gate
families no other `forward/` file reaches:
`QOrchard` (the whole-circuit checks gate — the magnitude/sign split of the
net value, the anchor equality on an active spend, and the two enable-flag
clauses), `QAdd` (the nullifier scalar sum of the add chip), `QCondSwap1` /
`QCondSwap2` (the Merkle cond-swap gate) and `QMerkleDecompose1` /
`QMerkleDecompose2` (the Merkle node decomposition gate) — 66 enabled points
in total, spread across families 1..32, 35 and 42. It delivers
`residual_gates_forward : residual_selector_gates_ok`, the selector-keyed
refinement of the api obligation over those six selectors. The guarded
constraint bodies of all six are pinned by `vm_compute` certificates
(`guarded_orchard_eq`, `guarded_add_eq`, `guarded_cs1_eq` / `_cs2_eq`,
`guarded_md1_eq` / `_md2_eq`) and the enabled points by the
input-independent shape certificate `residual_shape_cert`, which resolves
each point to its region and row (and, for the Merkle selectors, to the
layer's configuration variant). The gate bodies are discharged over an
abstract assignment (`orchard_point`, `add_point`, `cs_gate_eval`,
`md_gate_eval`) and instantiated at the generator's cells by the Merkle cell
dispatch (`cs_point_1` / `_2`, `md_point_1` / `_2`), the 52-word packing
identities of §5.4.1.3 (`mbits_*`, `merkle_pieces_eq`, the `b_1`/`b_2` split
`mb1_low` / `mb2_high`) and the child/index range lemmas.

`forward/read_back.v` (`OrchardForwardReadBack`, all `Qed`) carries the
second conjunct of `completeness_statement` and delivers
`read_back_forward : read_back_ok` — the free-witness readers of
`circuit_proof/inputs.v` reproduce the input record on every valid,
nondegenerate input. It is the universal form of the concrete C1 certificate
`instance_read.v`, resolved symbolically instead of by `vm_compute`: the
plane readers (`read_advice_cell` / `read_instance_cell`) project the
generator's advice and instance planes, and each field's residue is the
identity because the honest cell is already a field element — the `valid`
type envelope bounds the witnessed scalars and path entries, `point_ok`
bounds the witnessed point coordinates, and the derived values end in the
chord formulas' field reductions (`padd_inc_coords` / `s2p_coords` for the
Sinsemilla accumulators, `padd_coords` / `mul_gen_coords` for the blinded
commitment). The three windowed scalars are reconstructed from their base-8
window cells (`sfw_digits` inverts the 85-window decomposition below
`8^85`); the Merkle path reader collects the cond-swap regions' sibling and
position cells through the layer-index round trip; and the public anchor row
is identified with the specification root by `t_anchor_root`, which reads the
hoisted layer chain's last output through the layer-chain bridge of
`forward/sinsemilla.v` (`t_layers_nth`, `hd_out_of`) and the Merkle fold
identities of `witness_input.v` (`merkle_node_succ`,
`merkle_layer_words_spec`).

`forward/assembly.v` (`OrchardCompletenessAssembly`, all `Qed`) composes the
lanes. Its gate side is `gates_all : family_gates_ok all_families`, proved by
case analysis on the guarding selector of an enabled point: each of the 56
`Selector.t` constructors is routed to the lane that proves its bodies —
`residual.v` for `QOrchard`, `QAdd` and the four Merkle cond-swap /
decomposition selectors, `running_sums.v` for `QLookup` / `QRunning` /
`QBitshift`, `ecc_add.v` for the two witness-point and two addition
selectors, `var_base_ladder.v` for the six `QMulIncomplete*` selectors and
`QMulDecomposeVar` / `QMulOverflow` / `QMulLsb`, `fixed_base.v` for the four
window selectors, `poseidon.v` for the three round selectors, `sinsemilla.v`
for the four round selectors, and `canonicity.v` for `QCommitIvk` and the 22
`QNoteCommit*` selectors. Selector coverage is total, so the family
hypothesis of `family_gates_ok` is never needed and the obligation holds at
`all_families` — every family index `0..42` is discharged, including the
vacuous `41` (`GadgetLocal`, no enabled point) and the families whose points
are split across several lanes. The three lanes stated at a family index
(`poseidon.v` at `[33]`, `var_base_ladder.v` at `[37]`, `canonicity.v` at
`[38; 39; 40]`) need the converse fact — an enabled point guarded by one of
their selectors lies in one of their families — supplied by `fam_in` from the
single input-independent `vm_compute` scan `point_family_cert` over the 4,858
enabled points.

The lookup side is `lookups_all = lookups_forward_ok`, the read-back is
`read_back_forward`, and the witness-fact side is the hypothesis of
`completeness_of_witness_facts : witness_facts_forward_ok ->
orchard_completeness_statement`, which applies
`completeness_statement_of_families` at `all_families` with
`all_families_covers` for both coverage premises.
`orchard_completeness : orchard_completeness_statement` instantiates that
hypothesis with `witness_facts_ok`.

## Status and what remains

Proved and clean (`PrimString.string` + impredicative `Set`):

- `Complete.circuit_holds_intro` — the generic gluing lemma.
- `CompleteAdditionCompleteness.completeness` — the add-chip instance.
- The Orchard supporting infrastructure: `decidable_eq.v`, the three
  `certificates.v` checkers, the `honest_assignment` generator with
  `honest_planes_ok`, and the cell layers `tables.v` / `tables_vb.v` /
  `tables_nc.v`.
- `orchard_completeness_instance` — the whole-circuit C1 instance.
- `lookups_forward_ok : family_lookups_ok all_families` — the whole-circuit
  lookup side of the C2 join, including the five Sinsemilla generator-table
  site leaves.
- The C2 statement API `forward/api.v`, including the join
  `completeness_statement_of_families`.
- The per-family gate obligations stated at their family index:
  `poseidon_gates_ok`/`poseidon_lookups_ok` (`[33]`),
  `var_base_gates_ok`/`var_base_lookups_ok` (`[37]`), and
  `canonicity_gates_ok` (`[38; 39; 40]`).
- The selector-keyed gate obligations covering the remaining lanes:
  `ecc_add_gates_forward`, the four `q_mul_fixed_*_gates_ok`, the
  `running_sums.v` selector obligations, `sinsemilla_gates_forward` and
  `residual_gates_forward` — together with their vacuous lookup
  complements.
- `read_back_forward : read_back_ok` — the free-witness read-back conjunct of
  the C2 join (`forward/read_back.v`).
- `gates_all : family_gates_ok all_families` and
  `lookups_all : family_lookups_ok all_families` — the whole-circuit gate and
  lookup obligations (`forward/assembly.v`).
- `completeness_of_witness_facts : witness_facts_forward_ok ->
  orchard_completeness_statement` — the C2 composition with the witness-fact
  lane as its only hypothesis (`forward/assembly.v`).

Every item above audits at the repo baseline on a full `.vo` build.

`orchard_completeness : orchard_completeness_statement`
(`forward/assembly.v`) is `Qed` and **unconditional**: its assumption audit
reports exactly the repo baseline (`PrimString.string : Set` and impredicative
`Set`). There is no `Admitted`, `Axiom` or `admit` anywhere under
`Garden/Orchard/` or `Garden/Halo2/`.

`open_witness_facts` rests on the five `forward/witness/` group lemmas:
the 97 facts are partitioned by proof shape into disjoint groups, each
pinned and proved in its own file, and `nt_open` is their concatenation.
The partition is sound because `nt_cover` — the coverage scan tying the
pinned list to the reified `Complete.witness_facts` — is an
order-insensitive `existsb` scan over the fact multiset, so any regrouping
that preserves that multiset re-runs unchanged.

Open: nothing on the C2 surface. The completeness direction of
`circuit_holds` is closed for the whole Orchard Action circuit, at every
valid, nondegenerate honest input.
