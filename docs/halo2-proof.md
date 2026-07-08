# Halo2 Proof Workflow

This document records the proof-facing conventions for the Halo2/Orchard
translation. Keep it current when proof statements, semantic definitions, or
tactic patterns change.

## Main Files

The shared proof semantics live in:

```text
Garden/Halo2/proof.v
```

Poseidon chip proof work lives in:

```text
Garden/Halo2/halo2_gadgets/poseidon/pow5_proof.v
```

The Orchard-level Poseidon hash determinism proof (the nullifier's
`poseidon_hash2`, built from the chip lemmas) lives in:

```text
Garden/Orchard/circuit_proof/poseidon.v
```

The translated Poseidon configure gates live in:

```text
Garden/Halo2/halo2_gadgets/poseidon/pow5.v
```

The high-level synthesis DSL lives in:

```text
Garden/Halo2/Synthesis.v
```

The Pallas prime and field operations live in:

```text
Garden/Field/Field.v
```

That file defines the `Primes` module (prime constants and `Prime` instances),
the `Prime` class, the `UnOp`/`BinOp` field operations, and the `+F`/`-F`/`*F`
notations. `Garden/Plonky3/M.v` re-exports the same `Primes` module as an
alias, so proof files reach it through either import.

Use the Pallas instance locally in proof files:

```coq
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.
```

## Evaluation Semantics

`Garden/Halo2/proof.v` defines the proof-side evaluator.

The evaluator covers configured expressions, constraints, gates, and
constraint systems. The high-level synthesis DSL is a pair of free-monad
syntax trees, `𝓡` for region programs and `𝓛` for layouter programs.
`Garden/Halo2/serialize.v` gives the executable raw-JSON interpretation;
`proof.v` gives the same syntax a relational reading:
`region_facts`/`layouter_facts` reify the facts established by running
synthesis (selector enables, fixed assignments, copies, instance and constant
pinning, lookup-table loads), `interpret_facts` turns those facts into a
`Prop`, and `satisfies_gates`/`satisfies_lookups`/`Satisfies` state gate and
lookup satisfaction of the configured constraint system. `circuit_holds`
packages both halves — the synthesis facts plus `Satisfies` — and is the
hypothesis of the chip-level theorems. What this relational model captures and
idealizes is described in `docs/chip-model-caveats.md`.

`Assignment.t columns RegionId` gives concrete values for selectors, fixed
columns, advice columns, instance columns, and lookup-table columns:

```coq
selector : columns.(Columns.Selector) -> RegionId -> Z -> Z;
fixed : columns.(Columns.Fixed) -> RegionId -> Z -> Z;
advice : columns.(Columns.Advice) -> RegionId -> Z -> Z;
instance_ : columns.(Columns.Instance_) -> Z -> Z;
lookup : columns.(Columns.Lookup) -> Z -> Z;
```

Selector, fixed, and advice values are region-scoped: they are addressed by an
abstract `RegionId` plus a region-local row offset, never by an absolute row.
Instance and lookup-table values are global and addressed by an absolute row.

Lookup table columns are a separate `columns.(Columns.Lookup)` family. They do
not appear in `Expression.t`; they are consumed by `eval_lookup_argument` and
`satisfies_lookups`, where a lookup argument holds when the tuple of queried
expressions equals some table row below the `nb_table_rows` bound, and by
`Fact.LookupTableLoaded`, which pins `Assignment.lookup` to the loaded table
values.

`Evaluation.C` is a typeclass whose `eval` field takes an assignment, an
index, and the syntax to evaluate:

```coq
Module Evaluation.
  Class C {columns : Columns.t} {RegionId : Set} {p : Z} `{Prime p}
      (Index A B : Type) : Type := {
    eval : Assignment.t columns RegionId -> Index -> A -> B;
  }.
End Evaluation.
```

Instances exist for selectors, expressions, constraints, named constraints,
constraint lists, gates, and gate lists. Use the notation:

```coq
Γ ⊢ ⟦ expression_or_gate ⟧ (region, row)
```

where `Γ` is the assignment and the index is a `(region, row)` pair.

Selectors are evaluated at the current `(region, row)` with no rotation.
Rotated fixed/advice/instance queries do not wrap around; they use:

```coq
rotated_row row rotation =
  row + rotation.(Rotation.offset)
```

Rows are plain unbounded integers: there is no `nb_rows`, no modulo wrapping,
and `satisfies_gates` quantifies over every `(region, row)` pair. See
`docs/chip-model-caveats.md` for what this idealizes.

Expression evaluation returns `Z` reduced modulo the active prime through
`UnOp.from`, `+F`, `-F`, and `*F`.

## Constraint Semantics

The semantic constraint constructors are:

```coq
Constraint.Select selector constraint
Constraint.Equal lhs rhs
Constraint.Boolean expression
Constraint.Range expression range
Constraint.Either left right
Constraint.EqualZeroToPrecise expression
```

Their intended readings are:

```coq
Constraint.Select selector constraint
```

means: if the selector evaluates to a nonzero field value, then the nested
constraint must hold. Use `<> 0` for selector activity.

```coq
Constraint.Equal lhs rhs
```

means: the two evaluated expressions are equal.

```coq
Constraint.Boolean expression
```

means: the evaluated expression is boolean.

```coq
Constraint.Range expression range
```

means: the evaluated expression is in `[0, range)`.

```coq
Constraint.Either left right
```

means: either nested constraint holds. This is used for product-zero-style
constraints after they have been given a proof-facing disjunctive shape.

```coq
Constraint.EqualZeroToPrecise expression
```

means: the evaluated expression is zero. This remains as a fallback for
constraints that have not yet been refined into one of the semantic forms above.

`eval_constraints` and `eval_gates` are `Fixpoint`s that build `/\` directly,
with a special one-element list case. This is intentional: after `cbn in *`, a
gate with three constraints should become a three-way conjunction rather than a
`List.Forall` goal.

Record field projections use clear implicits where possible so expressions such
as `gate.(Gate.constraints)` do not need explicit column parameters.

## Gate Operation Functions

Configure files should expose named `Gate.t` definitions for each gate created
by the monadic `configure`. Proof-facing operation functions belong in sibling
`*_proof.v` files, following `pow5_proof.v`.

Use executable `Z` functions and records for gates that compute or reconstruct
target cells. If a gate is only a range, boolean, canonicity, on-curve, or
branch-conditional check, keep the named gate but do not invent an output
function. Shared Z-level helpers for proof-side gate operations live in:

```text
Garden/Halo2/halo2_gadgets/utilities_proof.v
```

For reconstruction constraints, mirror the syntactic target:

```text
target - expression = 0
expression - target = 0
```

becomes an `output` field `target := expression`, using field operations such
as `+F`, `-F`, `*F`, and `UnOp.from`.

## Determinism Statements

For a gate-level deterministic theorem, prefer a statement with:

```coq
{RegionId : Set} (Γ : Assignment.t columns RegionId)
(region : RegionId) (row : Z)
(Hselector : Γ ⊢ ⟦ selector ⟧ (region, row) <> 0)
(Hgate : Γ ⊢ ⟦ gate ⟧ (region, row))
```

and a conclusion comparing whole state records, not separate coordinate
equalities:

```coq
{|
  State.x0 := Γ ⊢ ⟦ next_0 ⟧ (region, row);
  State.x1 := Γ ⊢ ⟦ next_1 ⟧ (region, row);
  State.x2 := Γ ⊢ ⟦ next_2 ⟧ (region, row);
|} =
  output current_values round_constants.
```

Define the `output` function with `Definition ... := ...` when the operation is
understood. If the operation is not ready, a temporary admitted `output` is
acceptable, but the goal is to move the concrete computation into `output` and
prove the main `deterministic` theorem directly.

Name theorem hypotheses as they would appear after `intros`, for example
`Hselector` and `Hgate`.

Each gate-level `deterministic` theorem should have a chip-level
`synthesize_correct` companion whose hypothesis is `circuit_holds` for the
chip's `synthesize` program and configured system. Its proof discharges
`Hselector` with the `enabled_nonzero` bridge (a `Fact.SelectorOn` from the
synthesis facts gives a nonzero selector) and `Hgate` with
`satisfies_gates_at` (gate membership in the configured gate list plus
`satisfies_gates`). The three Poseidon gates in `pow5_proof.v` follow this
pattern.

## Poseidon Full Round

The full round gate in `pow5.v` constrains:

```text
next[row] = MDS[row] * pow5(state + round_constant)
```

In `pow5_proof.v`, `FullRound.output` is defined as an executable state-level
function. Its helper `output_coordinate` intentionally mirrors the translated
gate expression:

```coq
state_0_sbox *F UnOp.from (p128pow5t3.mds_coeff row 0) +F
state_1_sbox *F UnOp.from (p128pow5t3.mds_coeff row 1) +F
state_2_sbox *F UnOp.from (p128pow5t3.mds_coeff row 2)
```

This syntactic alignment avoids needing field commutativity just to connect the
configured gate expression to the proof-level output function.

The deterministic proof uses:

```coq
unfold output, output_coordinate, pow5.
with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
  cbn in *.
hauto lq: on.
```

`pow5` should follow the circuit expression shape:

```coq
let value_2 := value *F value in
let value_4 := value_2 *F value_2 in
value_4 *F value
```

## Poseidon Partial Round

The partial round proof mirrors the full-round pattern:

```text
PartialRound.output : concrete definition
PartialRound.deterministic : proved
PartialRound.synthesize_correct : proved
```

`PartialRound.output` composes the two half-rounds of the folded gate: each
half adds its round constants, applies `pow5` to coordinate 0 only
(`sbox_partial`), and multiplies by the MDS matrix (`mds_mul`).

The `deterministic` proof extracts:

- the intermediate S-box value in advice column `A5`;
- the equality between the MDS-inverse view of the next row and the computed
  post-round values.

It then folds the extracted constraints back into `output` using `dot3` (a
commutation lemma between the two dot-product orientations), `mds_roundtrip`,
and the MDS inverse identities below.

## Poseidon Pad-And-Add

`PadAndAdd.output` is concrete:

```coq
State.x0 := previous_state_0 +F current_state_0;
State.x1 := previous_state_1 +F current_state_1;
State.x2 := previous_state_2;
```

The deterministic proof uses the compact pattern:

```coq
unfold output.
with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
  cbn in *.
hauto lq: on.
```

After reduction, the gate hypothesis has the shape:

```coq
(Hselector -> prev_0 +F cur_0 = next_0) /\
(Hselector -> prev_1 +F cur_1 = next_1) /\
(Hselector -> prev_2 = next_2)
```

and the goal is a record equality between the next-state record and the
computed output record.

## MDS Matrix Facts

`pow5_proof.v` contains matrix helpers:

```coq
mds_mul
mds_inv_mul
```

The inverse identities are proved:

```coq
mds_mul_mds_inv_identity
mds_inv_mul_mds_identity
```

Both go through `MatrixInverse.matrix_compose_identity`, which reduces the
composition to nine per-entry congruences discharged with `now vm_compute`:
the hard-coded MDS and inverse matrices are inverses modulo the Pallas prime.
`mds_inv_mul_injective` and `mds_roundtrip` (the `mds_mul (mds_inv_mul s) = s`
form used on reduced states) are proved from those identities.

## Reduction and Automation

Use `with_strategy` to prevent field arithmetic from unfolding during `cbn`:

```coq
with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
  cbn in *.
```

This keeps goals at the field-operation level instead of expanding into raw
`Z.modulo` arithmetic.

Do not assume `best` should stay in committed proofs. A useful workflow is:

```coq
best.
```

or, on a larger goal:

```coq
best time: 10.
```

Then use Hammer's suggested replacement, such as:

```coq
hauto lq: on.
```

For FullRound, plain `best` failed with the default time limit, while
`best time: 10` found `hauto lq: on`.

For PadAndAdd, `best` also suggested `hauto lq: on`.

Measure local tactic speed with Rocq's `Time`, not shell `time` around the whole
file, when comparing proof scripts:

```coq
Time hauto lq: on.
```

Shell `time coqc ...` measures imports, other proofs, and `.vo` writing too.

In one FullRound measurement, wrapping Hammer itself in `with_strategy` was
slower than leaving only the preceding `cbn` under `with_strategy`:

```text
Time hauto lq: on.                                  about 1.6s
Time with_strategy opaque [...] hauto lq: on.       about 1.8s
```

So the preferred pattern is:

```coq
with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
  cbn in *.
hauto lq: on.
```

### `mod_ring_solve` for mod-p ring identities

For goals that are pure mod-p *polynomial identities* over field operations
(both sides built from `+F`/`-F`/`*F`/`UnOp.from` with possibly nested
`mod`s), use `mod_ring_solve` (`Garden/Halo2/lemmas.v`) instead of
`field_solve`:

```coq
mod_ring_solve.
```

It unfolds the field ops, strips every inner `mod` at any depth via
`setoid_rewrite (Zdiv.Zmod_eqm p)` under the `#[export]`-registered `eqm`
morphism instances, and closes with `f_equal; ring` — milliseconds where
`field_solve` (which is `lia` over euclidean-division equations with the
255-bit modulus) takes tens of seconds or diverges. Plain
`Z.*_mod_idemp_*` rewriting cannot substitute: it only reaches a `mod` that
is an immediate operand of the enclosing modded node, and greedy rewriting
strands alternating-depth `mod`s; the `eqm`-setoid route is complete at any
depth.

Rule of thumb: `mod_ring_solve` for polynomial identities; `field_solve`
only where genuine linear arithmetic (bounds, cell solving) is needed.

## Compile Commands

From `garden/Garden`, compile one file with:

```sh
opam exec -- coqc -impredicative-set -R . Garden -w -stdlib-vector \
  Halo2/halo2_gadgets/poseidon/pow5_proof.v
```

These flags match `_CoqProject`; a full build is `make -C Garden`. For the
`-vos`/`-vok` fast development loop that skips the heavy `vm_compute`
certificates, see `docs/compile-performance.md`.
