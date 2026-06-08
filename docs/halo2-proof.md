# Halo2 Proof Workflow

This document records the proof-facing conventions for the Halo2/Orchard
translation. Keep it current when proof statements, semantic definitions, or
tactic patterns change.

## Main Files

The shared proof semantics live in:

```text
Garden/Halo2/proof.v
```

Poseidon proof work currently lives in:

```text
Garden/Halo2/Gadgets/Poseidon/Pow5_proof.v
```

The translated Poseidon configure gates live in:

```text
Garden/Halo2/Gadgets/Poseidon/Pow5.v
```

The high-level synthesis DSL lives in:

```text
Garden/Halo2/Synthesis.v
```

The Pallas prime and field operations live in:

```text
Garden/Plonky3/M.v
```

Use the Pallas instance locally in proof files:

```coq
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.
```

## Evaluation Semantics

`Garden/Halo2/proof.v` defines the proof-side evaluator.

This evaluator is currently for configured expressions, constraints, gates, and
constraint systems. The high-level synthesis DSL records raw events and logical
cells, but it does not yet define proof obligations connecting synthesized
assignments to gate evaluation.

`Assignment.t columns` gives concrete values for selectors, fixed columns,
advice columns, and instance columns:

```coq
selector : columns.(Columns.Selector) -> Z -> Z;
fixed : columns.(Columns.Fixed) -> Z -> Z;
advice : columns.(Columns.Advice) -> Z -> Z;
instance_ : columns.(Columns.Instance_) -> Z -> Z;
```

`Evaluation.t columns` packages an assignment, a current row, and the number of
rows:

```coq
Record t {columns : Columns.t} : Set := {
  assignment : Assignment.t columns;
  row : Z;
  nb_rows : Z;
}.
```

Use the notation:

```coq
⟦ expression_or_gate ⟧ ρ
```

Selectors are evaluated at `row mod nb_rows`. Rotated fixed/advice/instance
queries use:

```coq
rotated_row row nb_rows rotation =
  (row + rotation.(Rotation.offset)) mod nb_rows
```

Expression evaluation returns `Z` reduced modulo the active prime through
`UnOp.from`, `+F`, `-F`, and `*F`.

## Constraint Semantics

The semantic constraint constructors are:

```coq
Constraint.Select selector constraint
Constraint.Equal lhs rhs
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
Constraint.EqualZeroToPrecise expression
```

means: the evaluated expression is zero. This is still a coarse constructor;
future passes can replace uses with more semantic constructors when the proof
needs the stronger shape.

`eval_constraints` and `eval_gates` are `Fixpoint`s that build `/\` directly,
with a special one-element list case. This is intentional: after `cbn in *`, a
gate with three constraints should become a three-way conjunction rather than a
`List.Forall` goal.

Record field projections use clear implicits where possible so expressions such
as `gate.(Gate.constraints)` do not need explicit column parameters.

## Determinism Statements

For a gate-level deterministic theorem, prefer a statement with:

```coq
(ρ : Evaluation.t columns)
(Hselector : ⟦ selector ⟧ ρ <> 0)
(Hgate : ⟦ gate ⟧ ρ)
```

and a conclusion comparing whole state records, not separate coordinate
equalities:

```coq
{|
  State.x0 := ⟦ next_0 ⟧ ρ;
  State.x1 := ⟦ next_1 ⟧ ρ;
  State.x2 := ⟦ next_2 ⟧ ρ;
|} =
  output current_values round_constants.
```

Define the `output` function with `Definition ... := ...` when the operation is
understood. If the operation is not ready, a temporary admitted `output` is
acceptable, but the goal is to move the concrete computation into `output` and
prove the main `deterministic` theorem directly.

Name theorem hypotheses as they would appear after `intros`, for example
`Hselector` and `Hgate`.

## Poseidon Full Round

The full round gate in `Pow5.v` constrains:

```text
next[row] = MDS[row] * pow5(state + round_constant)
```

In `Pow5_proof.v`, `FullRound.output` is defined as an executable state-level
function. Its helper `output_coordinate` intentionally mirrors the translated
gate expression:

```coq
state_0_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 0) +F
state_1_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 1) +F
state_2_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 2)
```

This syntactic alignment avoids needing field commutativity just to connect the
configured gate expression to the proof-level output function.

The proof currently uses:

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

The partial round proof currently has:

```text
PartialRound.output : admitted
PartialRound.deterministic : admitted
PartialRound.deterministic_from_evaluation : proved
```

The proved theorem extracts:

- the intermediate S-box value in advice column `A5`;
- the equality between the MDS-inverse view of the next row and the computed
  post-round values.

The next cleanup should mirror the full-round pattern: define the concrete
`PartialRound.output`, then move the proof into `PartialRound.deterministic` and
remove `deterministic_from_evaluation`.

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

`Pow5_proof.v` contains matrix helpers:

```coq
mds_mul
mds_inv_mul
```

The inverse identities are currently admitted:

```coq
mds_mul_mds_inv_identity
mds_inv_mul_mds_identity
```

`mds_inv_mul_injective` is proved from those identities. When completing the
Poseidon proof, these admitted identity lemmas should be replaced by concrete
proofs that the hard-coded MDS and inverse matrices are inverses modulo the
Pallas prime.

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

So the current preference is:

```coq
with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
  cbn in *.
hauto lq: on.
```

## Compile Commands

From `garden/Garden`, compile one file with:

```sh
opam exec -- coqc -impredicative-set -R . Garden Halo2/Gadgets/Poseidon/Pow5_proof.v
```

The project currently uses `-impredicative-set` for these checks.
