# The `constrain_constant` gap: issue, cause, and fix

Found 2026-07-02, fixed 2026-07-04: the Rocq synthesis model
silently dropped every Halo2 `constrain_constant` /
`assign_advice_from_constant` site, making the relational model strictly more
permissive than the real circuit. This document records the issue, its cause
in the translation pipeline, the per-site emission status, and the fix with
its validation gates. For how the mechanism sits in the overall model, see
[`chip-model-caveats.md`](chip-model-caveats.md).

## The issue

### What the Rust mechanism is

Halo2 has a layouter-level way to pin a cell to a public constant, distinct
from gate polynomials. `ConstraintSystem::enable_constant` designates a fixed
column as a *constants column* (equality-enabled in the permutation argument);
`region.constrain_constant(cell, c)` asks the layouter to write `c` into a
fresh cell of that column and add a permutation copy between it and `cell`;
`region.assign_advice_from_constant(…, c)` is assign-plus-pin in one call. To
the verifier this is exactly as strong as a gate `cell = c`: the constants
column is part of the fixed circuit data.

### What the model had

The synthesis DSL (`Garden/Halo2/Synthesis.v`) had no counterpart: `𝓡` offered
only `EnableSelector`, `AssignFixed`, and `Copy`; `Expression.Constant`
existed only inside gate polynomials. Every translated `constrain_constant`
site was therefore simply absent from the relational model. The model being
*more permissive* than reality kept all existing `Qed`s true, but made the
affected *bridge* statements unprovable — or outright false, because a
countermodel could assign the unpinned cell any value.

### How it was found

While discharging the `value_commit_v` leg of the witness-elimination lemma
`action_spec_us_free`: upstream's strict-mode running-sum decomposition pins
the short scalar's final running-sum cell to zero
(`decompose_running_sum.rs:201`), but the synthesized region in `circuit.v`
had no such constraint, so `A4[22] = 0` was not derivable from `Holds Γ`.
Without it the folded window digits are unanchored to the magnitude — the
`8²²·z₂₂` term absorbs any discrepancy mod p. The fact had to be carried as an
explicit side condition (`OrchardActionFixedBase.value_commit_v_z_boundary`),
and the `cv_net_*` / `nf_old` bridges were falsifiable in the model as stated.
This was not version skew: `strict = true` has been passed by the short
scalar's `copy_decompose` since 2021-07-10 (zcash/halo2 `a8bd2d6a`), and
`constrain_constant(z_last, 0)` is in the helper's original commit
(`ee062bae`, 2021-07-09), years before this translation (2026-06).

In total the action circuit exercises **166** such constant bindings (the site
table below), including the Poseidon initial state, every Sinsemilla domain
point `x_Q`, all short-range-check `2^{-n}` pins, the Merkle layer constant,
and both strict running-sum tails.

## The affected sites (halo2_gadgets 0.5.0)

Per-site emission status, from the floor-planner constant tail of the
implementation dump. Attribution used the floor planner's FIFO discipline: the
trailing block's order mirrors synthesis order, so aligning it with the region
sequence assigns every one of the 166 bindings to a source site.

| Rust site | What it pins | Consumer in this development | Emission |
|---|---|---|---|
| `utilities/decompose_running_sum.rs:201` (strict) | running-sum tail `z_W = 0` → windows are the scalar's digits + `< 2^{KW}` bound | `value_commit_v` (short, the found instance) and the `nullifier_k` base-field region — the `cv_net_*`/`nf_old` bridges | emitted: `circuit.v` short (`A4[22]`) and base-field (`A4[85]`) regions |
| `utilities/lookup_range_check.rs:237` (strict) | lookup-decomposition tail = 0 → K·W-bit range *bounds* | the four `note_commit` y-canonicity `j` decompositions (25 words each) | emitted: `note_commit.v` `synthesize_running_lookup` with a `strict` flag |
| `utilities/lookup_range_check.rs:482` (`short_range_check`; missed by the first survey) | `2^{-num_bits}` into the running-sum column at offset 2 — without it the bitshift gate is vacuous | every short range check: 64 Merkle `b_1`/`b_2`, 22 note-commit piece/y-canon checks, 3 commit_ivk checks (89 total; `2^{-s}` for s ∈ {4,5,6,8,9}) | emitted: `lookup_range_check.v`/`note_commit.v`/`commit_ivk.v` short-range regions take `inv_two_pow_s` (literals in `ecc/chip/constants.v`) |
| `poseidon/pow5.rs:287` | initial-state constants `(0, 0, 2^65)` | Poseidon soundness → `nf_old` | emitted: `pow5.v` `synthesize_initial_state` |
| `sinsemilla/chip/hash_to_point.rs:163` | the domain point's `x_Q` into the initial `x_a` (35 hashes: 32 Merkle, 2 note commits, 1 commit_ivk; `y_Q` goes through the already-modeled `fixed y_q` `AssignFixed`) | the ANCHOR and CMX public outputs | emitted: the three `hash_to_point` region functions in `sinsemilla/chip.v` pin `x_a[0] = q_x` |
| `sinsemilla/chip/hash_to_point.rs:140` | `variable y_q` (init-from-private-point branch) | — | not exercised by the action circuit (absent from the dump); not emitted |
| `sinsemilla/merkle/chip.rs:349` | the layer constant `l` | ANCHOR | emitted: `circuit.v` `synthesize_merkle_decomposition_instance` pins `right_col[1] = layer` |
| `ecc/chip/witness_point.rs:112,115` | constant-point variant | — (no point-coordinate constants in the dump) | not exercised by the action circuit; not emitted |
| `ecc/chip/mul.rs:201` | variable-base `z_init = 0` | address integrity (`[ivk] g_d_old`) | emitted: `mul.v` variable-base region pins `A9[1] = 0` |
| `ecc/chip/mul_fixed/short.rs:262` | `u = 0` in the sign row | none (upstream comments it irrelevant) | not exercised by the action circuit (absent from the dump); not emitted |

## The cause

The root cause is a **level mismatch** between where the model sits and where
the faithfulness check looks, cemented by a repair at the wrong layer:

1. **The DSL models the region/layouter API, minus its one deferred-effect
   op.** `constrain_constant` is unusual: at the region-API level nothing is
   written — the V1 floor planner only queues the request
   (`floor_planner/v1.rs:462`) and materializes it *after all regions*, as a
   trailing block of constants-column `AssignFixed` + `Copy` events with
   allocator-chosen rows (`v1.rs:118–135`). Every other region op maps 1:1 to
   immediate events; this one crosses the region/floor-planner boundary, and
   the translation dropped it.

2. **The synthesis JSON recorder sits below the floor planner.** The Rust dump
   (`SynthesisJsonRecorder`, formal-land/orchard `src/circuit.rs`) instruments
   the `Assignment` trait, where the desugared trailing block *is* visible —
   the implementation snapshot contains all 166 bindings as raw events.

3. **The parity gap was patched at the artifact level.** When the model-side
   and implementation-side JSON first diverged by exactly that trailing block,
   the fix was `scripts/generate_orchard_synthesis_constants.py`: peel the
   trailing `(AssignFixed col 3, Copy)` pairs off the *implementation* dump,
   render them into `Garden/Orchard/circuit_synthesis_constants.v`, and append
   them to the model's serialized stream (`circuit.v`, `synthesize_events`).
   The script's rationale — "these events are mechanical" — misjudged them:
   each `Copy` is a permutation *constraint*, not layout bookkeeping.

4. **Consequently no check could catch the gap.** The strict JSON parity
   comparison passed by construction — for the constants block it compared the
   Rust dump against a table generated *from* the Rust dump. And the
   relational interpreter (`layouter_facts`) walks only the free-monad
   program, never the spliced raw events, so `Holds Γ` never saw the
   constraints. The events existed in both JSON files and in neither
   semantics.

## The fix (landed 2026-07-04)

### The semantics extension

- `Garden/Halo2/Synthesis.v`: new region op `𝓡.ConstrainConstant (cell, value)`
  plus the translation-prelude alias `assign_advice_from_constant` (builds the
  advice cell, emits the op, returns the cell). `value` must be a reduced
  literal in `[0, p)`: the Rust layouter writes the canonical representative
  and the permutation forces raw equality.
- `Garden/Halo2/proof.v`: new fact `Fact.CellIsConstant cell value`,
  interpreted as `eval_cell Γ cell = value` (raw-value pinning, in the style
  of `Fact.FixedIs`); `region_value`/`region_facts` cases.
- `Garden/Halo2/serialize.v`: `V1.eval_region` emits **no raw event** for the
  op. Faithfully reproducing the floor-planner allocator is deferred to the
  relational↔operational bridge; the trailing block stays replayed from the
  generated table, and the gap this splice leaves in the comparison is closed
  by a dedicated certificate (below).

Gate passed: the whole tree recompiled with zero proof changes.

### Emission at the translated sites

`ConstrainConstant` is emitted at every site the action circuit exercises,
per the table above: the strict running-sum tails `z₂₂`/`z₈₅` in `circuit.v`;
the Poseidon initial state `(0, 0, 2⁶⁵)` in `poseidon/pow5.v`; the
domain-point `x_Q` pin in all three `hash_to_point` region functions
(`sinsemilla/chip.v`, 35 hashes); the Merkle layer constant `l` (`circuit.v`);
the variable-base `z_init = 0` (`ecc/chip/mul.v`); the four strict
y-canonicity `j` tails and all 89 short-range-check `2^{-n}` pins
(`utilities/lookup_range_check.v`, `circuit/note_commit.v`,
`circuit/commit_ivk.v`, with reduced literals `inv_two_pow_{4,5,6,8,9}` in
`ecc/chip/constants.v`). During attribution a **ninth site missed by the
original survey** was found: `lookup_range_check.rs:482`, the `2^{-num_bits}`
pin without which the bitshift gate is vacuous. Two sites are not exercised by
the action circuit (`witness_point` constant variant; `mul_fixed/short.rs`'s
`u = 0`) and are documented, not emitted.

One proof-shape repair was needed: three positional `bind_right`/`in_or_app`
navigations in `circuit_proof/fixed_base/main.v` gained a step for the
inserted op.

### The validation gates

- the serialize JSON parity re-run against a **fresh** extraction (the
  extraction loads `.vo`; the first re-run silently used a stale
  `circuit.vo` — rebuild it first or the comparison tests the old model);
- **`Garden/Orchard/circuit_synthesis_constants_check.v`** — a
  `vm_compute` certificate proving the program's `ConstrainConstant` ops,
  resolved through the serializer's `indices`/`region_start_of`, equal the
  replay table as a multiset of (absolute cell, value) pairs. Because the
  replay table is generated from the Rust dump, this is the Rust-independent
  check the parity comparison structurally could not provide.

### Discharging the side conditions

- `value_commit_v_z_boundary_of_holds` (`circuit_proof/fixed_base/main.v`,
  `Qed`): the `A4[22] = 0` boundary now follows from `Holds Γ`. The `Hz`
  hypothesis is dropped from `value_commit_v_table_eq`,
  `action_spec_us_free_of_nullifier_k` and the window-digit lemmas, leaving
  the base-field canonicity digit match as `action_spec_us_free`'s only
  remaining trusted leg (since discharged separately).
- `nullifier_k_z_boundary_of_holds` (`Qed`): the base-field analogue
  `A4[85] = 0`, ready for the canonicity route.

### Build and audit

Full `make` passes (the heavy QR certificates do not depend on the edited
sources, so none re-ran). `Print Assumptions`: the boundary lemmas and the
witness-elimination reduction rest on `pallas_p_prime` + `PrimString.string`
only — the assumption set is unchanged with the side condition
internalized — and `constant_copies_certificate` is axiom-free modulo
`PrimString.string`.

## Residual items

- `V1.eval_region` still emits no events for the op. The
  relational↔operational bridge must either model the constants-column
  allocator (making the trailing block honest) or take the replay table as an
  input; there, `CellIsConstant` splits into a program-determined write into
  the constants column plus a witness-dependent permutation obligation.
- The new facts feed downstream proof work — the K·W-bit range bounds from
  the strict tails, and the Poseidon initial-state and Sinsemilla `Q`-point
  consumers; their status is tracked with those proofs, not here.
