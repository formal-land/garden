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
assignment satisfying `circuit_holds` is accepted operationally. Three
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

## What this does not claim

The bridge deliberately stops at the ideal checker; the remaining distance
to a deployed prover is recorded, not hidden:

- `mock_prover_accepts` quantifies over **all** integer rows, not the
  `2^k` cyclic row domain of the real prover, and blinding rows are not
  modeled (the cyclic-domain refinement gap of
  `docs/chip-model-caveats.md`).
- It is the *soundness* direction that is instantiated on Orchard: honest
  acceptance implies the theorems. The completeness direction (honest
  witnesses are accepted) is a separate tracked effort.
- No cryptography is verified here: connecting mock acceptance to real
  proof verification — selector compression, the permutation argument's
  grand products, polynomial commitments, Fiat–Shamir — is the verified
  circuit-compilation track, for which this bridge is the bottom anchor.
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
| `Halo2/realize/smoke.v` | add-chip replay instance |
| `Orchard/circuit_operational.v` | `orchard_replay_ok`, `orchard_operational_sound`, `orchard_action_statement_operational` |
