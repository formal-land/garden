# Halo2 Translation Conventions

This file records the current conventions for translating Halo2 Rust circuit
code into Garden/Rocq. Keep it current with the code: update this when the Rocq
DSL or translation style changes.

## Code Pointers

Shared translation infrastructure:

```text
Garden/Halo2/main.v
  shared Halo2 DSL for columns, expressions, gates, lookups, and constraint systems

Garden/Halo2/serialize.v
  shared indexed configure projection plus raw synthesis JSON types and
  typed-event-to-raw serializers

Garden/Halo2/Synthesis.v
  high-level Halo2 synthesis DSL with typed cells and free region/layouter
  programs

Garden/Halo2/proof.v
  proof-facing semantics for expressions, gates, and semantic constraints
```

Top-level Orchard translation and generated comparison artifacts:

```text
Garden/Orchard/columns.v
  absolute Orchard column constructors and shared column-index map

Garden/Orchard/circuit.v
  top-level Orchard configure translation and synthesize entry point

Garden/Orchard/circuit_synthesis_json_extract.v
  extraction entry point for compiling Rocq configure and synthesis models to OCaml

Garden/Orchard/Snapshots/circuit_configure_generated_from_model.json
  configure gates and lookups generated from the structured Rocq model

Garden/Orchard/Snapshots/circuit_configure_generated_from_implementation.json
  configure gates and lookups generated from the Rust/Halo2 implementation

Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json
  V1 synthesis trace generated from the structured Rocq model

Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json
  full V1 synthesis trace generated from the Rust/Halo2 implementation
```

## File Layout

Orchard files mirror the Rust module path where practical:

```text
orchard/src/circuit.rs
  -> Garden/Orchard/circuit.v

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
by generated configure snapshots and synthesis JSON comparison.

Concrete circuit column files group their column families with `Columns.t`:

```coq
Definition columns : Columns.t := {|
  Columns.Selector := Selector.t;
  Columns.Fixed := Fixed.t;
  Columns.Lookup := Lookup.t;
  Columns.Advice := Advice.t;
  Columns.Instance_ := Instance_.t;
|}.
Canonical columns.
```

Use `Empty_set` for a column family that is not present in the translated
component.

Halo2 `TableColumn`s are represented through the `Lookup` column family, not
through ordinary `Fixed` columns. Lookup arguments pair a queried expression
with a table-side lookup column:

```coq
Module Lookup.
  Inductive t : Set :=
  | TableIdx
  | TableX
  | TableY.
End Lookup.

LookupArgument.pairs :
  list (Expression.t columns * columns.(Columns.Lookup)).
```

The serializer has a separate `Indices.lookup` function. For Orchard, lookup
table columns still use raw indices `0`, `1`, and `2` in the JSON snapshots,
while ordinary fixed columns start after them. This mirrors Halo2's
`TableColumn` distinction without changing the current raw JSON shape.

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

## Generated Configure Snapshots

Configure snapshots are generated as JSON only. The Rust/Halo2 implementation
snapshot is produced by ignored Orchard tests, and the structured Rocq model
snapshot is produced by extraction:

```sh
cd orchard
cargo +1.85.1 test generate_action_circuit_configure_json -- --ignored --nocapture
cargo +1.85.1 test generate_action_circuit_synthesis_json -- --ignored --nocapture

cd ../garden
opam exec -- make -C Garden orchard-json-from-model
opam exec -- make -C Garden orchard-configure-json-compare
```

The configure JSON contains only configure-time gates and lookups, using numeric
Halo2 column and selector indices. The implementation snapshot lives at
`Garden/Orchard/Snapshots/circuit_configure_generated_from_implementation.json`;
the extracted Rocq model snapshot lives at
`Garden/Orchard/Snapshots/circuit_configure_generated_from_model.json`.
In the configure JSON, `Constraint.EqualZeroToPrecise expression` is serialized
as the inner expression directly; there is no `EqualZeroToPrecise` wrapper node
in the JSON format.

The full synthesis trace from the Rust implementation is generated separately into
`Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json`; it
records the same raw synthesis events that Rocq extraction regenerates into
`Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json` for comparison.

The generated files intentionally do not encode the extra Halo2 metadata such as
query tables, equality/permutation columns, constants, or minimum degree; those
remain available in the high-level JSON artifact.

`Garden/Halo2/serialize.v` defines the typed-to-indexed projection used by the
Rocq model JSON extraction. Keep the handwritten translation's expression shapes
aligned with the generated Halo2 AST, including cases where Rust uses explicit
products instead of `Constraints::with_selector`, or `Expression::Scaled` instead
of multiplication by a constant.

## Synthesize Functions

`Garden/Halo2/Synthesis.v` defines the high-level representation for
`synthesize`. It owns the typed synthesis syntax:

```coq
ColumnRef.t columns
Cell.t columns RegionId.t
𝓡 columns RegionId.t A
𝓛 columns RegionId.t A
```

`𝓡` is the region-level free-monad type and `𝓛` is the layouter-level
free-monad type. Their constructors live in the `ℛ` and `ℒ` modules.
Both are constructor-only syntax trees: `Ret` and `Bind` are constructors, and
the primitive Halo2 actions are constructors too. `Synthesis.v` does not define
an event trace type.

`Garden/Halo2/serialize.v` requires `Synthesis.v` and owns the raw JSON-facing
schema:

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

It also defines serializers such as `ColumnRef.to_raw` and `Cell.to_raw`, plus
an evaluator for `ℛ` and `ℒ`. The serializer is the only place where typed cells
are converted into raw numeric columns and absolute rows.

Advice assignments are represented in the high-level state so later copies can
refer to cells, but they intentionally emit no raw JSON event for now. This matches
the current Rust recorder, which omits advice values from
`Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json`.

Large fixed-table data should be produced by structured Rocq model code rather
than pasted generated Rocq traces. Table and fill-from-row replay are currently
deferred in the free-monad synthesis model.

`Garden/Halo2/Gadgets/Sinsemilla/SConstants.v` contains the translated
`SINSEMILLA_S` coordinate table from the Rust `sinsemilla` crate. This is data
used by the structured table loader, not a raw generated synthesis event dump.

`Garden/Orchard/circuit_synthesis_constants.v` contains the generated replay
table for Halo2 V1 floor-planner constant fixed-column bindings. It is generated
by `scripts/generate_orchard_synthesis_constants.py` from the Rust
implementation JSON. The data is currently inert for the free-monad model; the
logical Orchard synthesis regions remain hand-written in the Rocq circuit and
gadget files.

`Garden/Orchard/circuit_synthesis_layout.v` contains the generated V1
floor-planner region starts emitted by the Rust Orchard generator. Its public
`region_start_of` function takes the typed Orchard region identifier from
`Garden/Orchard/regions.v`, and the Rocq model uses those starts for strict
JSON extraction so that row mismatches point to incorrect modeled cell
dependencies.

Use `𝓛 columns RegionId.t A` for layouter-level programs and
`𝓡 columns RegionId.t A` for region bodies. Both use the shared `let🞵` and
`return🞵` notations; Rocq infers the concrete monad from the surrounding type.
Cells carry typed region ownership:

```coq
Cell.t columns RegionId.t
```

The region id is converted to an absolute row only when emitting raw synthesis
events, by `Garden.Halo2.serialize.V1.run_with_region_start`.

The basic one-step pattern is:

```coq
Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion (RegionId.of_index 0) "gate name" (
    ℛ.EnableSelector Selector.QExample 0 "").
```

For multi-step programs:

```coq
Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  let🞵 _ := first_layouter_step in
  second_layouter_step.

Definition synthesize_region
    : 𝓡 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 _ := ℛ.EnableSelector Selector.QExample 0 "" in
  let🞵 cell := ℛ.AssignAdvice "value" Advice.A0 0 0 in
  return🞵 cell.

Definition synthesize_pair
    : 𝓛 columns RegionId.t unit :=
  let🞵 '(left, right) := returns_pair in
  use_pair left right.
```

Each `ℒ.AddRegion` must pass the concrete Orchard region id for that
Rust region occurrence. Reused gadgets should expose a region parameter or a
small base index so the caller decides the concrete occurrence.

For gadgets with several configured instances, mirror the configure naming:

```coq
synthesize_instance
synthesize_1
synthesize_2
```

The current Orchard `synthesize_events` entry point is backed by a structured
hand-written Rocq synthesis program:

```coq
Definition synthesize_events
    (indices : Garden.Halo2.serialize.Indices.t columns)
    : list Garden.Halo2.serialize.Raw.Event.t :=
  let '(_, events) :=
    Garden.Halo2.serialize.V1.run_with_region_start
      indices
      Garden.Orchard.circuit_synthesis_layout.region_start_of
      synthesize in
  events.
```

The hand-written monadic synthesis definitions in the circuit and gadget files
are still intentionally structural. They record typed ownership points and the
modeled synthesis operations. Keep refining those definitions toward the Rust
witness functions; do not restore a raw generated Rocq event dump as the model
source.

Run a top-level high-level synthesis trace with:

```coq
Garden.Orchard.circuit.synthesize_events
  Garden.Orchard.columns.Index.indices
```

The current runner is `serialize.V1.run_with_region_start`. It interprets the
`ℛ`/`ℒ` syntax into raw JSON events using the supplied column indices and
generated region starts. Region placement is supplied as generated data rather
than computed inside the model.

Generate the Rocq-model configure and synthesis JSON files with:

```sh
opam exec -- make -C Garden orchard-json-from-model
```

Compare configure JSON against the Rust implementation JSON with:

```sh
opam exec -- make -C Garden orchard-configure-json-compare
```

Compare synthesis JSON against the Rust implementation JSON with:

```sh
opam exec -- make -C Garden orchard-synthesis-json-compare
```

Compare only the structural event stream, ignoring floor-planner row placement,
with:

```sh
opam exec -- make -C Garden orchard-synthesis-json-compare-normalized
```

The comparison intentionally ignores the top-level `source` string, because the
model and implementation are generated by different programs, and compares the
schema and event list.

Current comparison status: strict synthesis JSON comparison succeeds. The model
and implementation both emit 19617 events, and
`opam exec -- make -C Garden orchard-synthesis-json-compare` verifies equality
of the schema and event list. The only ignored top-level field is `source`,
because the model JSON is produced by the Rocq extractor while the implementation
JSON is produced by the Rust generator.

The strict comparison uses the generated Rust V1 layout so row mismatches now
represent actual source-cell dependency mistakes. The NoteCommit message-piece
and input gates currently thread the concrete message, range-check, Sinsemilla
running-sum, and canonicity cells needed for strict parity.

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
