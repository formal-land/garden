# Halo2 Translation Conventions

This file records the current conventions for translating Halo2 Rust circuit
code into Garden/Rocq. Keep it current with the code: update this when the Rocq
DSL or translation style changes.

## File Layout

Shared Halo2 concepts live in:

```text
Garden/Halo2/main.v
```

High-level synthesis concepts live in:

```text
Garden/Halo2/Synthesis.v
```

Orchard files mirror the Rust module path where practical:

```text
orchard/src/circuit.rs
  -> Garden/Orchard/circuit.v

orchard/src/circuit_data/action_circuit.highlevel.json
  -> Garden/Orchard/circuit_generated.v

orchard/src/circuit/gadget/add_chip.rs
  -> Garden/Orchard/circuit/gadget/add_chip.v

orchard/src/circuit/commit_ivk.rs
  -> Garden/Orchard/circuit/commit_ivk.v

orchard/src/circuit/note_commit.rs
  -> Garden/Orchard/circuit/note_commit.v

halo2_gadgets/src/utilities/lookup_range_check.rs
  -> Garden/Halo2/Gadgets/LookupRangeCheck.v

halo2_gadgets/src/ecc/chip/*.rs
  -> Garden/Halo2/Gadgets/Ecc/chip/*.v

halo2_gadgets/src/poseidon/pow5.rs
  -> Garden/Halo2/Gadgets/Poseidon/Pow5.v

halo2_poseidon/src/p128pow5t3.rs and halo2_poseidon/src/fp.rs
  -> Garden/Halo2/Gadgets/Poseidon/P128Pow5T3.v

halo2_gadgets/src/sinsemilla/chip.rs
  -> Garden/Halo2/Gadgets/Sinsemilla/chip.v

halo2_gadgets/src/sinsemilla/merkle/chip.rs
  -> Garden/Halo2/Gadgets/Sinsemilla/merkle/chip.v

halo2_gadgets/src/utilities/cond_swap.rs
  -> Garden/Halo2/Gadgets/Utilities/CondSwap.v
```

Generated comparison bridges live next to the translated circuit:

```text
Garden/Orchard/circuit_generated_proof.v
```

When Rust submodules need to share translated column bundles without creating
cycles, put those bundles in a small local `common.v` file under the mirrored
directory.

Configure and synthesize translations for the same Rust module should live in
the same Rocq file. Keep the configure definitions first, then add the
corresponding `synthesize`, `synthesize_instance`, `synthesize_1`, or
`synthesize_2` definitions below them.

## Imports

Translated files should import the shared Halo2 DSL:

```coq
Require Import Garden.Halo2.main.
```

Files that define synthesis programs should also import:

```coq
Require Import Garden.Halo2.Synthesis.
```

Prefer adding further imports only when the translated file really needs them.

## Columns

Rust column families become Rocq modules with explicit constructors:

```coq
Module Advice.
  Inductive t : Set :=
  | A0
  | A1.
End Advice.
```

The current families are:

```text
Advice
Selector
Fixed
Instance_
Lookup
```

`Instance_` is used instead of `Instance` because `Instance` is reserved.

Concrete circuits group their column families with `Columns.t`. For Orchard,
the physical columns live in:

```text
Garden/Orchard/columns.v
```

That file defines the absolute constructors used by the Orchard circuit and by
Orchard-specialized gadgets such as ECC.

`Garden/Orchard/columns.v` also defines `Index.indices`, a reusable
interpretation from absolute Orchard columns to the numeric column indices used
by generated traces.

Concrete circuit column files group their column families with `Columns.t`:

```coq
Definition columns : Columns.t := {|
  Columns.Selector := Selector.t;
  Columns.Fixed := Fixed.t;
  Columns.Advice := Advice.t;
  Columns.Instance_ := Instance_.t;
|}.
Canonical columns.
```

Use `Empty_set` for a column family that is not present in the translated
component.

Halo2 `TableColumn`s are represented through the fixed-column family for now.
When a circuit has an explicit lookup-table column type, wrap it in the fixed
column type:

```coq
Module Fixed.
  Inductive t : Set :=
  | LagrangeCoeffs0
  | Lookup (lookup : Lookup.t).
End Fixed.
```

## Configure Functions

Rust `configure` mutates `meta`. In Rocq, we thread a pure value:

```coq
Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {| ... |} in
  meta.
```

For polymorphic gadgets, make `configure` polymorphic in `columns` and pass the
used selector and advice columns as parameters:

```coq
Definition configure {columns : Columns.t}
    (meta : ConstraintSystem.t columns)
    (q_add : columns.(Columns.Selector))
    (a b c : columns.(Columns.Advice))
    : ConstraintSystem.t columns := ...
```

The caller chooses whether to keep the returned configuration data. For now, we
only thread and return the updated `meta`.

For Orchard-only gadgets, use the absolute Orchard columns directly:

```coq
Require Import Garden.Orchard.columns.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns := ...
```

This is the current style for the ECC, Poseidon, Sinsemilla, and Merkle
translations, because the active proof target is Orchard rather than reusable
generic gadgets.

`meta.enable_equality(...)` is currently omitted from the Rocq semantics. Do not
add a placeholder event for it unless the shared DSL starts tracking equality
state.

## Generated Configure Snapshot

`Garden/Orchard/circuit_generated.v` is generated from the Halo2
`ConstraintSystem` data by Rust code in `halo2_proofs::dev`, through an ignored
Orchard test:

```sh
cd orchard
cargo +1.85.1 test generate_action_circuit_configure_rocq -- --ignored --nocapture
cargo +1.85.1 test generate_action_circuit_synthesis_json -- --ignored --nocapture
```

The generated file defines:

```coq
Definition indexed_columns : Columns.t := {|
  Columns.Selector := Z;
  Columns.Fixed := Z;
  Columns.Advice := Z;
  Columns.Instance_ := Z;
|}.
Canonical indexed_columns.

Definition configure : ConstraintSystem.t indexed_columns := ...
```

The `configure` definition contains only configure-time gates and lookups, using
numeric Halo2 column and selector indices. The full synthesis trace from the
Rust implementation is generated separately into
`Garden/Orchard/circuit_synthesis_generated_from_implementation.json`; it
records the same raw synthesis events that Rocq extraction regenerates into
`Garden/Orchard/circuit_synthesis_generated_from_model.json` for comparison.

The generated files intentionally do not encode the extra Halo2 metadata such as
query tables, equality/permutation columns, constants, or minimum degree; those
remain available in the high-level JSON artifact.

The generated file declares `indexed_columns` as a canonical structure so Rocq
can infer the `Columns.t` parameter from numeric `Z` column arguments. This
keeps generated expressions readable, for example `Expression.Selector 0`
instead of `@Expression.Selector indexed_columns 0`.

`Garden/Orchard/circuit_generated_proof.v` is the bridge between the handwritten
Orchard configure translation and the generated numeric-index snapshot. The only
choice made in that file is assigning numeric Halo2 indices to the absolute
Orchard column constructors. Generic structural mapping lives in
`Garden/Halo2/main.v`: expressions are mapped homomorphically, and semantic
constraints are converted with `Constraint.to_expression` into generated
`Constraint.EqualZeroToPrecise` constraints. Do not add gadget-specific
expression rewrites to the bridge; any mismatch in expression shape or names
should stay visible as a translation or generator issue to fix at the source.

Current comparison status: `configure_eq_generated` closes by
`vm_compute; reflexivity`. Keep the handwritten translation's expression shapes
aligned with the generated Halo2 AST, including cases where Rust uses explicit
products instead of `Constraints::with_selector`, or `Expression::Scaled` instead
of multiplication by a constant.

## Synthesize Functions

`Garden/Halo2/Synthesis.v` defines the high-level representation for
`synthesize`.

The raw events mirror the generated synthesis trace:

```coq
Raw.Event.EnterRegion
Raw.Event.ExitRegion
Raw.Event.PushNamespace
Raw.Event.PopNamespace
Raw.Event.EnableSelector
Raw.Event.AssignFixed
Raw.Event.Copy
Raw.Event.FillFromRow
```

Advice assignments are represented in the high-level state so later copies can
refer to cells, but they intentionally emit no raw event for now. This matches
the current Rust recorder, which omits advice values from
`circuit_synthesis_generated_from_implementation.json`.

Use `Layouter.t columns A` for layouter-level programs and
`Region.t columns A` for region bodies. Use `let_ℒ` and `return_ℒ` for
layouter sequencing, and `let_ℛ` and `return_ℛ` for region sequencing.

The basic one-step pattern is:

```coq
Definition synthesize
    : Layouter.t columns unit :=
  Layouter.assign_region "gate name" (
    Region.enable_selector Selector.QExample 0 "").
```

For multi-step programs:

```coq
Definition synthesize
    : Layouter.t columns unit :=
  let_ℒ _ := first_layouter_step in
  second_layouter_step.

Definition synthesize_region
    : Region.t columns (Cell.t columns) :=
  let_ℛ _ := Region.enable_selector Selector.QExample 0 "" in
  let_ℛ cell := Region.assign_advice "value" Advice.A0 0 Value.Unknown in
  return_ℛ cell.
```

For gadgets with several configured instances, mirror the configure naming:

```coq
synthesize_instance
synthesize_1
synthesize_2
```

The current Orchard synthesis translation is intentionally structural: it
creates the same ownership points as configure and records selector/table/copy
events where they are already modeled, but most witness computations are still
skeletal. The next refinement step is to translate each Rust witness function
inside these existing in-file synthesis definitions until `synthesize_events`
matches the generated raw trace.

Run a top-level high-level synthesis trace with:

```coq
Garden.Orchard.circuit.synthesize_events
  Garden.Orchard.columns.Index.indices
```

The current runner is a lightweight state transformer. It records regions and
events and exposes `V1.run`; exact Halo2 V1 two-pass placement and generated
array parity are still future work.

Generate the Rocq-model JSON with:

```sh
opam exec -- make -C Garden orchard-synthesis-json-from-model
```

Compare it against the Rust implementation JSON with:

```sh
opam exec -- make -C Garden orchard-synthesis-json-compare
```

The comparison intentionally ignores the top-level `source` string, because the
model and implementation are generated by different programs, and compares the
schema, default event, and event list.

## Gates

Rust:

```rust
meta.create_gate("name", |meta| {
    let q = meta.query_selector(q);
    let a = meta.query_advice(a, Rotation::cur());

    Constraints::with_selector(q, [expr])
});
```

Rocq:

```coq
let meta := ConstraintSystem.create_gate meta {|
  Gate.name := "name";
  Gate.constraints :=
    let a := Expression.Advice a Rotation.cur in
    Constraints.with_selector q [
      (None, Constraint.EqualZeroToPrecise expr)
    ];
|} in
meta
```

Put query-like `let` bindings inside `Gate.constraints`, matching the Rust gate
closure body.

## Lookups

Rust:

```rust
meta.lookup(|meta| {
    let q = meta.query_selector(q);
    let value = meta.query_advice(advice, Rotation::cur());

    vec![(q * value, table_idx)]
});
```

Rocq:

```coq
let meta := ConstraintSystem.create_lookup meta {|
  LookupArgument.pairs :=
    let q := Expression.Selector q in
    let value := Expression.Advice advice Rotation.cur in
    [
      (q ✖️ value, table_idx)
    ];
|} in
meta
```

Lookup arguments are stored separately from gates in `ConstraintSystem.t`.
`LookupArgument.pairs` contains expression/table-column pairs, where the table
column is represented as a fixed column.

## Constraint Names

Individual constraint names are optional:

```coq
Constraints.t columns = list (option string * Constraint.t columns)
```

Use `Some "name"` when the source gives a meaningful label. Use `None` when the
Rust source has an unlabeled expression such as `Some(a + b - c)`.

For now, translate ordinary Halo2 expression constraints explicitly as:

```coq
Constraint.EqualZeroToPrecise expression
```

Later proof passes may replace these with more precise semantic constructors,
such as equality or product-zero forms.

## Expressions

Use the shared expression constructors and notations from `Garden.Halo2.main`:

```coq
Expression.Advice Advice.A0 Rotation.cur
Expression.Constant 1
x ➕ y
x ➖ y
x ✖️ y
x ● y
```

For selected constraints, use:

```coq
Constraints.with_selector selector constraints
```

This wraps each semantic constraint with `Constraint.Select selector`. Do not
translate selected gates by multiplying the expression by
`Expression.Selector selector`.

Gate semantics for proof work live in:

```text
Garden/Halo2/proof.v
```

That file evaluates expressions modulo a prime and interprets
`Constraint.Select`, `Constraint.Equal`, and `Constraint.EqualZeroToPrecise` as
propositions.

Shared algebraic helpers that correspond to `halo2_gadgets/src/utilities.rs`
live in:

```text
Garden/Halo2/Gadgets/Utilities.v
```

Examples include `square`, `range_check`, `bool_check`, `ternary`, and
`pow_expr`.

## Proof Workflow

The detailed proof-facing conventions live in:

```text
docs/halo2-proof.md
```

Use that document for the current patterns around `Evaluation.t`,
`⟦ x ⟧ ρ`, selector-active determinism theorems, Poseidon output functions,
`with_strategy opaque [...] cbn`, Hammer replacement tactics, and local proof
timing with Rocq `Time`.
