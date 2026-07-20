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

- `orchard_replay_ok` — replay of the full 19,617-event stream (15,047
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
  gone), `Compile.compile` (the `compress_selectors` packing with the
  indicator polynomial), and `Sigma.sigma_of_copies` (union-find cycle
  closure).
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

The whole-circuit composition is `Orchard/circuit_compiled.v`: from compiled
algebraic acceptance of `OrchardCompiledCheck.compiled` (the compiled Orchard
system) together with grid invariance under the σ built from the Orchard
copies, `orchard_compiled_sound` derives `mock_prover_accepts` of the replayed
grid, which `orchard_operational_sound` (this bridge) turns into
`circuit_holds`; `orchard_compiled_operational_sound` and
`orchard_compiled_action_statement` then compose down to the § 4.18.4 surface.
Every computable side condition is a `vm_compute` certificate on the concrete
instance (k = 11, n = 2048): the four-way-sharded indicator certificate, the
σ-construction certificate over the 2 964 copies on 15 × 2048 cells, and
`finite_domain_ok_b`. The replay-plane links (`compile_correct`'s selector- and
fixed-plane hypotheses) are discharged by structural replay lemmas over
`orchard_events`, not by symbolic-grid `vm_compute`.

The compiled system is anchored to the deployed verifying key by parity:
`Orchard/circuit_compiled_check.v` proves twelve `vm_cast_no_check`
certificates that `Compile.compile` applied to the model's `ConstraintSystem.t`
makes byte-identical choices to the deployed keygen — gate polynomials and
counts, the 56-selector → combination-column assignment, query tables,
permutation columns, constants column — against `circuit_description_fixed`, the
in-tree Debug dump of `vk.pinned()`. Assumption audit on every new theorem:
exactly `PrimString.string` + impredicative `Set` (the two `sigma.v`/`orbit.v`
orbit theorems are cleaner still — impredicative `Set` only).

This closes the L3 ↔ L2 arrow of the refinement ladder in
`docs-local/circuit-compilation-plan.md`; the polynomial-identity layer
below it is the next section.

## The polynomial-identity layer (reaching L1)

Compiled acceptance is still a row-by-row grid statement. The deployed
verifier instead checks *polynomial identities* over the cyclic domain: the
vanishing quotient for the gate plane, and the permutation and lookup grand
products. That layer is proved in the all-challenge reading — every
equivalence quantifies the challenges (y, β, γ, θ) universally, so no
probabilistic reasoning enters the statements; the random-challenge gap is
isolated as the counting lemmas of the R4 package (pending):

- `Halo2/plonkish/poly.v` / `poly_domain.v` / `poly_smoke.v` — the
  univariate polynomial library over the `Field/Field.v` mod-p arithmetic:
  monic division (`pdivmod_spec` / `pdivmod_unique`), the root bound
  (`roots_le_pdeg`), Lagrange interpolation (`lagrange_eval` /
  `interpolant_unique`), and the pinned Orchard domain — the vk's ω with
  `vm_compute` order-`2^11` certificates, the repetition-free `H = ⟨ω⟩`,
  and `X^2048 − 1 = ∏_{j<2048}(X − ω^j)`.
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
- `Orchard/circuit_compiled_algebraic.v` — the pinned composition:
  `orchard_algebraic_sound` → `orchard_algebraic_mock_accepts` →
  `orchard_algebraic_operational_sound` →
  `orchard_algebraic_action_statement` — algebraic acceptance of the
  pinned compiled system ends at the § 4.18.4 Action surface, with the new
  computable side conditions (the σ-mapping scans, the δ-coset labels,
  lookup replacement exactness, tables-as-prefix coherence) discharged as
  `vm_compute` certificates on the concrete instance.

Assumption audit on every new theorem: exactly `PrimString.string` +
impredicative `Set` (several endpoints cleaner — impredicative `Set`
only). This closes the L2 ↔ L1 arrow; what remains external is recorded
below.

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
  lookup identities in the all-challenge reading (L1) — pinned to the
  deployed vk by the parity certificates. What stays external is the
  challenge instantiation (the deployed transcript samples one challenge
  tuple where the L1 theorems quantify them all), polynomial commitments
  with IPA binding, and Fiat–Shamir (L0).
- The four witness-honesty side conditions of the action surface, and the
  model caveats of `docs/chip-model-caveats.md`, apply unchanged.

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
| `Halo2/plonkish/main.v` | `Domain`, `CompiledSystem`, `Compile.compile`, `Sigma.sigma_of_copies` |
| `Halo2/plonkish/compile.v` | `compile_correct`, `compile_correct_domain` |
| `Halo2/plonkish/orbit.v` | `FiniteOrbit` (generic finite-orbit / two-orbit merge theory) |
| `Halo2/plonkish/sigma.v` | `sigma_correct`, `sigma_copies_connected` |
| `Halo2/plonkish/mock.v` | `plonkish_of_mock_prover` |
| `Orchard/circuit_compiled_pinned.v` / `circuit_compiled_check.v` | pinned-vk data + 12 parity certificates |
| `Orchard/circuit_compiled.v` | `orchard_compiled_sound`, `orchard_compiled_operational_sound`, `orchard_compiled_action_statement` |
| `Halo2/plonkish/poly.v` / `poly_domain.v` | univariate polynomial library; the pinned ω, `H`, `X^n − 1` factorization |
| `Halo2/plonkish/lookup_compile.v` | `lookup_compile_correct`, `plonkish_accepts_compiled_iff` |
| `Halo2/plonkish/vanishing.v` | `vanishing_sound` |
| `Halo2/plonkish/permutation_poly.v` | `permutation_sound`, `permutation_complete` |
| `Halo2/plonkish/lookup_poly.v` | `lookup_sound`, `lookup_complete` |
| `Halo2/plonkish/algebraic.v` | `algebraic_accepts`, `algebraic_sound` |
| `Orchard/circuit_compiled_algebraic.v` | `orchard_algebraic_sound`, `orchard_algebraic_action_statement` |
