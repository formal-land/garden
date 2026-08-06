# Operational soundness: from the serialized circuit to the Action statement

This document describes the relational ↔ operational consistency bridge —
what it is, how it is built, and what it changes about the assurance the
development can claim for the Orchard action circuit. The headline result:
the `Holds` hypothesis consumed by every theorem of the Orchard action
surface (`circuit_proof/main.v`) is derived, for the whole circuit under its
concrete placement, from a single operational assumption — acceptance of the
serialized circuit by an ideal checker that mirrors Rust Halo2's
`MockProver` — with every layout and bookkeeping premise discharged by
machine-checked computation.

## The problem: two interpreters, one trusted

The synthesis DSL (`Halo2/Synthesis.v`) has two interpreters:

- **Relational** (`Halo2/proof.v`). Regions stay abstract (`RegionId` is
  never resolved to rows); a synthesis program is read as a value plus a
  list of reified facts, and `circuit_holds` says an assignment satisfies
  those facts and all gates. Every gadget proof and the whole Orchard
  action development live in this model.
- **Operational** (`Halo2/serialize.v`). The same program is lowered
  through a concrete placement — column indexes and a floor-planner
  `region_start` map — to a stream of `Raw.Event.t`s over absolute rows:
  selector enables, fixed assignments, copy constraints, table fills. This
  is the faithful mirror of what Rust Halo2 does during synthesis, and it
  is the layer the JSON comparison pipeline checks byte-for-byte against
  the Rust implementation's configure/synthesis dumps
  (see `docs/halo2-translation.md`).

Until the bridge, no theorem connected the two: the entire proof stack
rested on the relational reading, and its faithfulness to the operational
circuit — independent per-region coordinate spaces, no write collisions
between regions, constants actually pinned — was a trusted idealization,
recorded as the largest open gap in `docs/chip-model-caveats.md`.

## How the bridge works

### Event replay and the operational grid (`Halo2/realize/main.v`)

`apply_events` replays an event stream onto a flat grid (`RawGrid.t`:
selector, fixed, advice, instance planes over `Z`-indexed columns and
absolute rows). Replay is partial: a write that would change an
already-written cell to a different value fails the whole replay. The
conflict check reads a threaded log of performed writes, never the grid
planes, so the verdict is decidable by `vm_compute` even when the advice
and instance planes are symbolic — advice is free witness, not an event.
`realize idx rs` reads a relational `Assignment.t` back off the grid,
re-imposing region addressing through the placement.

Fills are keygen-faithful: `Raw.Event.FillFromRow` carries an upper bound
and writes the half-open range `[from_row, usable_rows)`, mirroring Halo2
keygen's `fill_from_row`, which iterates over the usable rows only. A
lookup table's default band therefore stops at `usable_rows` and the
`l_last` + blinding rows stay at `0` — the column as the deployed
verifying key commits it. The relational `Fact.LookupTableLoaded` is
correspondingly narrow (it pins the assigned rows `[0, length values)`);
the default band and the zero tail are pinned operationally by the
fill-replay lemmas of `realize/facts.v`.

### The ideal checker (`Halo2/realize/sound.v`)

`mock_prover_accepts` is the in-model counterpart of Rust Halo2's
`MockProver`, the checker every Halo2 circuit test runs: it takes the
filled grid and directly checks, with no cryptography,

1. every gate of the indexed, flattened constraint system at every row,
2. every lookup argument at every row against the loaded table, and
3. every `Raw.Event.Copy` obligation — the permutation argument — as an
   equality of the two grid cells.

### The bridge theorems (`Halo2/realize/sound.v` and its lemma files)

`operational_sound`: if replay of a program's event stream succeeds and
`mock_prover_accepts` holds of the resulting grid, then `circuit_holds`
holds of the realized assignment — the exact hypothesis the relational
proof stack consumes. `operational_complete` is the converse: a relational
assignment satisfying `circuit_holds` is accepted operationally. The two are
not symmetric in the stream they cover: `operational_sound` takes the
constants block as an extra event input (below), while
`operational_complete` is stated at the synthesis stream alone, so a circuit
whose checked stream carries a constants tail discharges that tail's copy
obligations separately (`orchard-completeness-proof.md`, "Which bridge theorem
applies"). Three
supporting layers carry the proof: value agreement of the two interpreters
(`realize/value.v`), the program-determined facts pinned by the replay
write log (`realize/facts.v`), and the field-algebra equivalence of each
relational gate constraint with its flattened polynomial
(`constraint_to_expression_correct`, `realize/constraints.v`).

Two decidable side conditions scope the statement: `instance_free` (gate
and lookup expressions never mention instance columns, whose relational
and operational row addressing differ) and `flattening_ok` (no
`Constraint.Range _ 0`, whose flattening is the empty product). Both
compute by `vm_compute` on a concrete system.

One structural subtlety is handled explicitly rather than assumed: Rust's
V1 floor planner materializes `constrain_constant` obligations as a
trailing block of fixed-column assignments and copies *after* synthesis,
and the serializer emits no event for the `ConstrainConstant` instruction
itself. `operational_sound` therefore takes the constants block as an
explicit extra event input with a `constants_materialized` premise — each
`CellIsConstant` fact must have a `Copy` linking its cell to a
fixed-column cell pinned by an `AssignFixed` — which is exactly what the
recorded constants tail provides.

### Placement-generic replay success (`Halo2/realize/disjoint.v`)

Replay success is also characterized without running the replay:
`replay_is_ok` equals a decidable pairwise `conflict_free` verdict on the
stream, at every initial grid. On top of that, the block layer proves the
placement-generic sufficient conditions: if each region's writes are
single-assignment at bounded local offsets (`block_ok`,
placement-independent) and blocks are pairwise compatible — distinct
regions placed on disjoint absolute row intervals, table and constants
blocks on disjoint column slots (`blocks_compatible_all`) — then the whole
lowered stream replays successfully at that placement
(`layouter_replay_succeeds`, and `layouter_with_tail_replay_succeeds` with
a trailing global block). This replaces one whole-stream quadratic check
with per-region reasoning plus interval disjointness, and is the reusable
form for other circuits and placements.

### The Orchard instantiation (`Orchard/circuit_operational.v`)

The bridge is instantiated on the full Orchard action circuit under its
concrete placement: the column indexes (`Orchard/columns.v`), the V1
floor-planner region starts (`Orchard/circuit_synthesis_layout.v`), and
the recorded constants tail (`Orchard/circuit_synthesis_constants.v`).
Every decidable premise is discharged by a `vm_compute` certificate:

- `orchard_replay_ok` — replay of the full 19,679-event stream (15,067
  writes, constants tail included) succeeds on *any* witness planes;
- `orchard_instance_free` / `orchard_flattening_ok` — the Orchard
  constraint system passes both decision procedures;
- `orchard_constants_materialized` — every `CellIsConstant` obligation of
  the synthesis program is covered by an `AssignFixed` + `Copy` pair of
  the constants tail, via a boolean coverage check over the
  `ConstantsCheck` extraction of the `ConstrainConstant` leaves.

The headline theorems:

- `orchard_operational_sound` — from replay success and
  `mock_prover_accepts` of the resulting grid, `circuit_holds` of the
  realized assignment for the Orchard synthesis program and system;
- `orchard_action_statement_operational` — the composition with
  `OrchardAction.action_statement`: the protocol Action statement
  (§ 4.18.4) and `ValidActionInputs` hold of the realized assignment, from
  replay success, mock acceptance, and the four witness-honesty side
  conditions of `docs/orchard-soundness-proof.md`.

### Closing the short-lookup side conditions (`Orchard/circuit_adversarial.v`)

Three of those four side conditions are a nondegeneracy conjunct paired
with a short-lookup range conjunct, and the short-lookup halves are
artifacts of the relational selector model rather than real assumptions.
At this level they are derivable. The realized assignment reads its
selector plane from the replayed grid at absolute rows, so the pinned event
stream decides `q_running` at every row; a `forallb` certificate over the
19,679 events shows it is enabled at none of the twenty-five short-range
rows, the circuit's single range-check lookup argument
(`lookup_range_check.configure 10 QLookup QRunning QBitshift A9 TableIdx`)
therefore collapses to a bare cell read against `table_idx`, and
`RangeTable.short_word_sound` gives the ten-bit bound, tightened to the
site's width by the companion bitshift gate.

- `Orchard/circuit_proof/lookup_closure.v` — the selector-absence lemma
  (`replay_selector_unset`), the extraction (`ten_bit_bound_at`), the
  width-tightening lemma (`short_range_bound`), the generic per-site lemma
  `site_short_bound` over an arbitrary `ShortSite` list, and the eleven
  new-note sites (`note_commit_new_short_lookup_ok_operational`);
- `Orchard/circuit_proof/lookup_closure_old_note.v`,
  `Orchard/circuit_proof/lookup_closure_ivk.v` — the eleven `Which.Old`
  sites and the three `Commit^ivk` sites, each four `forallb` certificates
  plus a composition through `site_short_bound`;
- `Orchard/circuit_adversarial.v` — `OrchardAdversarialAction`, the two
  acceptance-level Action statements restated without those conjuncts:
  `orchard_action_statement_operational_short_closed` here and
  `orchard_algebraic_action_statement_short_closed` at the
  polynomial-identity layer below. The residual hypotheses are named one
  predicate per package (`note_commit_nondegenerate`,
  `old_note_nondegenerate`, `commit_ivk_nondegenerate`) plus
  `merkle_witness_ok`, which is not narrowed there: its
  `merkle_layer_canonical` conjunct bounds 255-bit reconstructions that no
  acceptance level derives. The same file also carries the adversarial
  statement — the §4.18.4 clauses in the protocol's own disjunctive form —
  where none of those residues survives at all
  (`orchard_action_statement_adversarial_operational` /
  `…_algebraic`, under `WellTypedInstance` alone); see
  `docs/orchard-soundness-proof.md`.

## What this strengthens

**The trusted reading of the circuit moves from the model to the mirror of
the implementation.** Before the bridge, every Orchard action theorem was
conditioned on `circuit_holds` — a statement *in the relational model*,
whose fidelity to the real circuit was itself a trusted idealization. After
the bridge, the same theorems are conditioned on `mock_prover_accepts` of
the *serialized* circuit: the event stream and indexed constraint system
that the extraction pipeline compares against Rust Halo2's own
configure/synthesis dumps. An error in the relational idealization of
regions, placement, collisions, or constants pinning can no longer silently
weaken the theorems — those properties are now proved (generic bridge) or
computed (certificates), not assumed.

**Layout idealizations become checked computations.** "Regions do not
collide", "the constants are really pinned", "the tables are really
loaded" were modeling assumptions; they are now `vm_compute` certificates
on the concrete Orchard stream, with a placement-generic fallback
(`realize/disjoint.v`) characterizing exactly which placements are safe.

**The assumption audit is unchanged.** `Print Assumptions` on every new
theorem — through `orchard_action_statement_operational` — reports exactly
the tree-wide baseline (`PrimString.string` and impredicative `Set`); no
axiom, no `Admitted`, and the pre-existing Orchard action surface is
untouched.

## The compiled plonkish layer (reaching L2)

`mock_prover_accepts` is the raw event-grid checker (L3). Below it sits the
compiled circuit the deployed keygen actually produces: the selector columns
packed into *combination* fixed columns, the copy list closed into an explicit
permutation σ, and the finite cyclic domain `Z / 2^k Z` with its
usable/blinding rows. That layer is now modeled in Rocq and connected upward to
this bridge:

- `Halo2/plonkish/main.v` — `Domain` (n = 2^k rows, `usable_rows`,
  `l_0`/`l_last`/`l_blind`), `CompiledSystem` (numeric columns, selectors
  gone), `Compile.compile_from_metadata` (the `compress_selectors` packing
  plus configure-order queries, equality columns, constants, and minimum
  degree), and `Sigma.sigma_of_copies` (union-find cycle closure).
- `Orchard/configure_metadata.v` / `compiled/configuration.v` — the typed
  configure trace and its ordered interpreter. They derive 14 base fixed / 10
  advice / 1 instance columns, 56 selector kinds, exact query order, all 15
  equality-enabled columns, constants `[3]`, and `minimum_degree = None`.
- `Halo2/plonkish/compile.v` — `compile_correct` / `compile_correct_domain`:
  compiled-gate satisfaction on the cyclic domain ↔ selector-gated gate
  satisfaction on usable rows, allocation-independent, under the
  indicator-value distinctness and blinding-row vacuity side conditions.
- `Halo2/plonkish/sigma.v` (with the generic finite-orbit theory
  `Halo2/plonkish/orbit.v`) — `sigma_correct`: the grid is invariant under
  `sigma_of_copies copies` ↔ every copy holds as value equality. Both
  directions `Qed`; the forward orbit lemma `sigma_copies_connected` is closed
  (no `Admitted`).
- `Halo2/plonkish/mock.v` — `plonkish_of_mock_prover`: `mock_prover_accepts`
  ↔ compiled-plonkish satisfaction restricted to `[0, n)`, under the decidable
  `finite_domain_ok_b` layout checks.

The whole-circuit composition is `Orchard/compiled/main.v`: from compiled
algebraic acceptance of `OrchardCompiledCheck.compiled` (the compiled Orchard
system) together with grid invariance under the σ built from the Orchard
copies, `orchard_compiled_sound` derives `mock_prover_accepts` of the replayed
grid, which `orchard_operational_sound` (this bridge) turns into
`circuit_holds`; `orchard_compiled_operational_sound` and
`orchard_compiled_action_statement` then compose down to the § 4.18.4 surface.
Every computable side condition is a `vm_compute` certificate on the concrete
instance (k = 11, n = 2048): the four-way-sharded indicator certificate, the
σ-construction certificate over the 3 004 copies on 15 × 2048 cells, and
`finite_domain_ok_b`. The replay-plane links (`compile_correct`'s selector- and
fixed-plane hypotheses) are discharged by structural replay lemmas over
`orchard_events`, not by symbolic-grid `vm_compute`.

The compiled system is anchored to the deployed verifying key by parity:
`Orchard/compiled/certificate.v` packages the closed checks that
`Compile.compile_from_metadata` applied to the model's constraint system and
formal configure trace produces the deployed counts, 56-selector compression,
193 gate polynomials, exact ordered query tables, complete permutation-column
order, three lookups, constants `[3]`, and unset minimum degree. The deployed
values are equality targets, not compiler arguments. `vk/print.v` prints the
derived gate AST directly; the precise either-zero constructor preserves the
two left-associated curve-check trees, so no printer-only rotation remains.
Assumption audit on every new theorem:
exactly `PrimString.string` + impredicative `Set` (the two `sigma.v`/`orbit.v`
orbit theorems are cleaner still — impredicative `Set` only).

This closes the L3 ↔ L2 arrow of the refinement ladder; the
polynomial-identity layer below it is the next section.

## The polynomial-identity layer (reaching L1)

Compiled acceptance is still a row-by-row grid statement. The deployed
verifier instead checks *polynomial identities* over the cyclic domain: the
vanishing quotient for the gate plane, and the permutation and lookup grand
products. That layer is proved in the all-challenge reading — every
equivalence quantifies the challenges (y, β, γ, θ) universally, so no
probabilistic reasoning enters the statements; the random-challenge gap is
isolated as the counting lemmas of the R4 package:

- `Halo2/plonkish/poly.v` / `poly_domain.v` / `poly_smoke.v` — the
  univariate polynomial library over the `Field/Field.v` mod-p arithmetic:
  monic division (`pdivmod_spec` / `pdivmod_unique`), the root bound
  (`roots_le_pdeg`), Lagrange interpolation (`lagrange_eval` /
  `interpolant_unique`), and the Orchard domain — the cached vk value of ω,
  now derived by `vk/setup.v` from the Pasta root-of-unity schedule, with
  order-`2^11` certificates, the repetition-free `H = ⟨ω⟩`, and
  `X^2048 − 1 = ∏_{j<2048}(X − ω^j)`.
- `Halo2/plonkish/vanishing.v` — `vanishing_sound`: `(∀ y, ∃ h,
  Σ_i y^i·E_i = h·(X^n − 1)) ↔ ∀ i, ∀ j < n, E_i(ω^j) = 0`.
- `Halo2/plonkish/permutation_poly.v` — `permutation_sound` /
  `permutation_complete`: the four product rules (`l_0` boot, the main
  `Z(ωX)` rule, chunk chaining, `q_last` boolean) holding on `H` for all
  β, γ ↔ grid σ-invariance on usable rows, by telescoping the running
  products and the multiset argument over the integral domain.
- `Halo2/plonkish/lookup_poly.v` — `lookup_sound` / `lookup_complete`: the
  five lookup rules for all θ, β, γ ↔ every usable-row input tuple appears
  among the table rows — the set-membership reading `eval_lookup_argument`
  uses, closing the lookup `Prop`-model loop of
  `docs/chip-model-caveats.md`.
- `Halo2/plonkish/lookup_compile.v` — the value-preserving
  lookup-substitution seam: acceptance's lookup conjunct restated over
  `CompiledSystem.lookups` (`plonkish_accepts_compiled_iff`).
- `Halo2/plonkish/algebraic.v` — `algebraic_accepts` (the three argument
  families over a `CompiledSystem`, all challenges quantified, stated over
  column polynomials agreeing with the grid on `H`) and `algebraic_sound`:
  algebraic acceptance implies compiled-plonkish satisfaction.
  `algebraic_complete` is the converse, over
  `algebraic_accepts_regular` — the reading whose permutation conjunct is
  asked only at challenges where no identity-side factor vanishes on a
  usable cell, matching the restriction the lookup conjunct already
  carried. `algebraic_sound_regular` concludes from that same predicate,
  so the two directions meet there; `algebraic_sound` / `algebraic_accepts`
  are the all-challenge weakenings.
- `Orchard/compiled/algebraic.v` — the configure-derived composition:
  `orchard_algebraic_sound` → `orchard_algebraic_mock_accepts` →
  `orchard_algebraic_operational_sound` →
  `orchard_algebraic_action_statement` — algebraic acceptance of the
  derived compiled system ends at the § 4.18.4 Action surface, with the new
  computable side conditions (the σ-mapping scans, the δ-coset labels,
  lookup replacement exactness, tables-as-prefix coherence) discharged as
  `vm_compute` certificates on the concrete instance.
  `orchard_algebraic_complete` runs the same rung the other way, on the
  σ injectivity `sigma_of_copies_inj` exports from the assembly invariant.

The completeness direction reaches the same rung: `orchard_compiled_complete`
(`Orchard/compiled/main.v`) and `circuit_completeness/algebraic.v` carry an
honest witness from `mock_prover_accepts` to `algebraic_accepts_regular`, and
`orchard_honest_algebraic_accepts_ex` exhibits the gate-polynomial witness,
making the L1 soundness surface non-vacuous. See
[`orchard-completeness-proof.md`](orchard-completeness-proof.md).

Assumption audit on every new theorem: exactly `PrimString.string` +
impredicative `Set` (several endpoints cleaner — impredicative `Set`
only). This closes the L2 ↔ L1 arrow; what remains external is recorded
below.

## The random-challenge counting layer and the byte-level anchor (R4)

The L1 theorems above quantify the challenges (y, β, γ, θ) universally,
while the deployed transcript samples *one* tuple. R4 closes that gap
from both ends: it names the residual gap as an in-model finite-cardinality
statement, and it anchors the pinned circuit description to the deployed
verifier at the byte level.

- `Halo2/plonkish/counting.v` — the Schwartz–Zippel counting lemmas. For
  each argument family the all-challenge equivalence is recast as: a
  counting theorem over an arbitrary repetition-free challenge list (built
  on `Poly.roots_le_pdeg`, a nonzero polynomial having strictly fewer
  distinct roots than its degree), an explicit *bad set* (accepts-and-
  property-fails) with a `card_at_most` bound (vanishing ≤ #gates − 1 per
  domain point; permutation the nested-pair reading over the `2·|all_cells|`
  budget; lookup ≤ u·m at the θ level plus the 2u-per-side (β, γ) grid
  bound), and a constructive case corollary via the finite-grid
  decidability procedures (`gates_vanish_dec`, `perm_usable_invariant_dec`,
  `lookup_membership_dec`) — no classical axioms.
- `Halo2/plonkish/boundary.v` — the composed single-challenge corollary
  `algebraic_sound_at_challenge`: acceptance at one tuple *outside* the
  three bad sets yields the exact R2 satisfaction triple `algebraic_sound`
  gives from the all-challenge reading; `algebraic_accepts_at_cases` is the
  disjunctive form carrying each bad set with its cardinality bound. The
  genuinely external boundary is named here in the `SignatureKnowledge`
  style, never as axioms: `IPABinding` (one commitment opens to at most one
  polynomial), `MultiopenReduction` (an accepted opening pins the column
  polynomials), and `FiatShamirChallengeGood` (a transcript-derived
  challenge avoids a density-bounded bad set) — `Definition`s over an
  abstract commitment space, to be instantiated by a future L0.

The byte-level anchor upgrades the pinned-vk trust from offline
transcription to certified bytes (`Orchard/vk/*.v`,
`Orchard/vk/transcript_repr.v`):

- **T1 (dump parity)** — `vk_pinned_dump_parity`: a verified Debug printer
  over the model's metadata-derived compiled Orchard system (real
  `Expression` trees, ordered queries, lookups, constants, and permutation
  columns), setup-derived moduli/domain values, and the 44 deployed
  commitment targets emits the pretty rendering, proved
  primitive-string-equal to all 1,285,701 bytes of the in-tree
  `circuit_description_post_nu6_3` (the Debug dump of `vk.pinned()`). This
  retires the offline-transcription trust of `compiled/pinned.v` as a source
  of compiler inputs: those literals stay only as checker targets, now backed
  by certified bytes.
- **T2 (Fiat–Shamir scalar)** — `transcript_repr_spec`: the same printer's
  alternate (compact `{:?}`) flag yields `s`; `transcript_repr` is
  `le64(len s) ∥ s` hashed with BLAKE2b-512 personalized
  `"Halo2-Verify-Key"`, the 64-byte digest read little-endian mod
  `pallas_p` — the exact `plonk.rs` `from_parts` pipeline, delivering the
  binding scalar a future L0 composition consumes. The ≈ 2 228-block fold
  is sharded per the `compile-performance.md` discipline; a personalized
  BLAKE2b reference vector guards the parameter-block wiring.

The generated full aggregate transports both statements to
`derived_commitment_coordinates`. Its coordinate certificate proves that
view equal to the deployed targets and pointwise equal to mathematical
`commit_lagrange`. T2's public statement uses `transcript_input s`, so its
prefix is the computed `length s`.

`Orchard/vk/provenance/` completes the VK provenance graph. Its premise-free
`orchard_vk_commit_lagrange_refined` theorem proves that all 29 fixed and 15
permutation points equal Garden's mathematical `commit_lagrange` for the
configured column vectors and modeled `Params::new(11)` SRS.
`fixed_values_compiled_grid` identifies the fixed vectors with every
successfully replayed grid after `with_combinations`; the permutation vectors
are derived from `orchard_sigma` in the complete order recorded by the formal
configure trace. `OrchardVkSetupCompiled.certified` connects degree 9 to the
actual compiled system and derives `extended_k`, `omega`, and both modulus
strings. The generated premise-free `orchard_vk_fully_derived` packages those
facts with the configure/compilation certificate and T1/T2. The 2026-08-05
four-worker run of `make -C Garden orchard-vk-provenance` completed the full
generated-certificate `.vo` replay, with the final aggregate serialized. A
`.vos` build remains only a development type-check and is not evidence of
that kernel replay.

Assumption audit: the counting lemmas are at impredicative `Set` only (no
`PrimString`); the boundary corollaries, T1, and T2 add exactly the
`PrimString`/`PrimInt63` primitive family; no classical axioms appear, and
`orchard_algebraic_action_statement` / `OrchardAction.action_statement`
re-audit unchanged at their baselines. Both
`orchard_vk_commit_lagrange_refined` and `orchard_vk_fully_derived` are
premise-free. After the completed full `.vo` replay, `Print Assumptions` on
the combined theorem reported 52 standard `PrimString`, `PrimInt63`,
`PrimArray`, `Uint63Axioms`, and `ArrayAxioms` interface declarations,
together with impredicative `Set`; there is no Garden-specific or classical
axiom.

## What this does not claim

The bridge and the compiled layer stop at algebraic acceptance; the remaining
distance to a deployed prover is recorded, not hidden:

- `mock_prover_accepts` quantifies over **all** integer rows; the finite
  `2^k` cyclic domain and its usable/blinding rows are now modeled one level
  down (`Halo2/plonkish/main.v`'s `Domain`), and `plonkish_of_mock_prover`
  restricts acceptance to `[0, n)` with the layout checks. What remains is
  that the relational `proof.v` model itself still uses plain integer rows —
  the cyclic-domain refinement of `docs/chip-model-caveats.md` is discharged
  at the compiled level but not folded back into the relational reading.
- Both directions are now instantiated on Orchard, but they say different
  things: soundness says acceptance implies the theorems, completeness says
  the honest witness is accepted. Completeness is a non-vacuity result — it
  does not constrain what else the checker accepts. See
  [`orchard-completeness-proof.md`](orchard-completeness-proof.md).
- The compiled and polynomial layers prove the *algebraic* content of the
  system — selector compression, the permutation construction, the
  cyclic-domain/blinding discipline, and the vanishing / permutation /
  lookup identities in the all-challenge reading (L1) — and T1 anchors the
  pinned description byte-for-byte while T2 supplies the modeled
  Fiat–Shamir binding scalar. The R4 cryptographic boundary consists of:
  (i) *challenge instantiation*, expressed by the in-model finite-cardinality
  statement in `counting.v` and consumed through
  `FiatShamirChallengeGood`; (ii) `IPABinding` (polynomial-commitment
  binding); and (iii) Fiat–Shamir / the multiopen reduction
  (`MultiopenReduction`) at L0. Each is a named `SignatureKnowledge`-style
  hypothesis, never an axiom. The VK-provenance theorem provides the
  mathematical commitment equation for Garden's configured columns; it does
  not discharge IPA binding, the multiopen reduction, or Fiat–Shamir.
- The witness-honesty side conditions of the action surface, and the
  model caveats of `docs/chip-model-caveats.md`, apply unchanged, with
  two narrowings: at the operational and algebraic levels the short-lookup
  halves of three of the four packages are derived rather than assumed
  (`Orchard/circuit_adversarial.v`), leaving the incomplete-add
  nondegeneracy residue and `merkle_witness_ok`; and the adversarial
  statement in the same file carries no witness-honesty side condition at
  all, at the cost of the protocol's own disjunctive conclusion.

## Theorem index

| File | Key results |
| --- | --- |
| `Halo2/realize/main.v` | `RawGrid`, `apply_events`, `realize`, decision procedures |
| `Halo2/realize/value.v` | `operational_sound_value` (value agreement) |
| `Halo2/realize/facts.v` | `operational_sound_determined_facts` (replay pins the program facts) |
| `Halo2/realize/constraints.v` | `constraint_to_expression_correct` (gate ↔ flattened polynomial) |
| `Halo2/realize/sound.v` | `mock_prover_accepts`, `operational_sound`, `operational_complete` |
| `Halo2/realize/disjoint.v` | `replay_is_ok_conflict_free`, `layouter_replay_succeeds` |
| `Orchard/circuit_operational.v` | `orchard_replay_ok`, `orchard_operational_sound`, `orchard_action_statement_operational` |
| `Orchard/circuit_completeness/operational/` | the completeness mirror: `orchard_grid_identification`, `orchard_operational_complete` (see `orchard-completeness-proof.md`) |
| `Halo2/plonkish/main.v` | `Domain`, `CompiledSystem`, `Compile.compile_from_metadata`, `Sigma.sigma_of_copies` |
| `Halo2/plonkish/compile.v` | `compile_correct`, `compile_correct_domain` |
| `Halo2/plonkish/orbit.v` | `FiniteOrbit` (generic finite-orbit / two-orbit merge theory) |
| `Halo2/plonkish/sigma.v` | `sigma_correct`, `sigma_copies_connected`, `sigma_of_copies_dom` / `sigma_of_copies_inj` |
| `Halo2/plonkish/mock.v` | `plonkish_of_mock_prover` |
| `Orchard/configure_metadata.v` / `compiled/configuration.v` | typed configure operations; derived counts, selector kinds, ordered queries, equality columns, constants, and minimum degree |
| `Orchard/compiled/pinned.v` / `compiled/check.v` / `compiled/certificate.v` | deployed comparison targets + closed metadata-driven compilation certificate |
| `Orchard/compiled/main.v` | `orchard_compiled_sound`, `orchard_compiled_complete`, `orchard_compiled_operational_sound`, `orchard_compiled_action_statement` |
| `Halo2/plonkish/poly.v` / `poly_domain.v` | univariate polynomial library; cached ω, `H`, `X^n − 1` factorization |
| `Halo2/plonkish/lookup_compile.v` | `lookup_compile_correct`, `plonkish_accepts_compiled_iff` |
| `Halo2/plonkish/vanishing.v` | `vanishing_sound` |
| `Halo2/plonkish/permutation_poly.v` | `permutation_sound` / `permutation_sound_regular`, `permutation_complete`, `challenge_regular` |
| `Halo2/plonkish/lookup_poly.v` | `lookup_sound`, `lookup_complete` |
| `Halo2/plonkish/algebraic.v` | `algebraic_accepts` / `algebraic_accepts_regular`, `algebraic_sound` / `algebraic_sound_regular`, `algebraic_complete` |
| `Orchard/compiled/algebraic.v` | `orchard_algebraic_sound`, `orchard_algebraic_complete`, `orchard_algebraic_action_statement` |
| `Orchard/circuit_proof/lookup_closure.v` | `replay_selector_unset`, `ten_bit_bound_at`, `short_range_bound`, `site_short_bound`, `note_commit_new_short_lookup_ok_operational` |
| `Orchard/circuit_proof/lookup_closure_old_note.v` / `lookup_closure_ivk.v` | `old_note_short_lookup_ok_operational`, `commit_ivk_short_lookup_ok_operational` |
| `Orchard/circuit_proof/protocol_spec_bot.v` | ⊥-carrying spec variants; `hash_to_point_bot_iff`, the `option_map` commitment shells |
| `Orchard/circuit_proof/adversarial_api.v` | the four disjunctive §4.18.4 obligations, `typed_inputs_extended`, `WellTypedInstance`, the named Sinsemilla dlog reductions |
| `Orchard/circuit_proof/note_commit_bot.v` / `ownership_bot.v` / `merkle_bot.v` | `cmx_obligation_of_holds`, `old_note_obligation_of_holds`, `diversified_address_obligation_of_holds`, `mul_nondegenerate_of_holds`, `anchor_obligation_of_holds`, `merkle_b_range_ok_operational` |
| `Orchard/circuit_proof/adversarial.v` | `action_statement_adversarial`, `deterministic_adversarial`, `typed_inputs_extended_of_holds` |
| `Orchard/circuit_adversarial.v` | `orchard_action_statement_operational_short_closed`, `orchard_algebraic_action_statement_short_closed`, `orchard_action_statement_adversarial_operational` / `…_algebraic`, `orchard_deterministic_adversarial_operational` / `…_algebraic`, `action_ok_operational` |
| `Orchard/circuit_completeness/algebraic.v` | `orchard_honest_algebraic_accepts`, `orchard_honest_algebraic_accepts_ex` (L1 non-vacuity) |
| `Halo2/plonkish/counting.v` | `vanishing_counting`, `permutation_counting`, `lookup_counting`, per-family bad-set `card_at_most` bounds, `*_accept_cases` |
| `Halo2/plonkish/boundary.v` | `algebraic_sound_at_challenge`, `algebraic_accepts_at_cases`; named `IPABinding` / `MultiopenReduction` / `FiatShamirChallengeGood` |
| `Orchard/vk/setup.v` / `setup_compiled.v` | compiled degree, extended-domain, root-of-unity, and modulus provenance |
| `Orchard/vk/print.v` / `vk/data.v` / `vk/bytes.v` | derived `vk.pinned()` Debug printer + deployed equality targets and dump bytes |
| `Orchard/vk/parity.v` | `vk_pinned_dump_parity` (T1: printed pretty form = `circuit_description_post_nu6_3`, all 1,285,701 bytes) |
| `Orchard/vk/transcript_repr.v` | `transcript_repr_spec` (T2: the BLAKE2b Fiat–Shamir binding scalar) |
| `Orchard/vk/full_abstract.v` / `vk/provenance/generated/certificates/Main.v` | `OrchardVkFullAbstract.certificate`, generated `orchard_vk_fully_derived` aggregate |
