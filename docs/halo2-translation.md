# Halo2 Translation Conventions

This file records the current conventions for translating Halo2 Rust circuit
code into Garden/Rocq. Keep it current with the code: update this when the Rocq
DSL or translation style changes.

## Code Pointers

Shared translation infrastructure:

```text
Garden/Halo2/main.v
  shared Halo2 DSL for columns, expressions, gates, lookups, constraint
  systems, and configure free-monad programs

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

Garden/Orchard/regions.v
  absolute Orchard synthesis region constructors and gadget-local region names

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

## Rocq Formatting

Do not leave an empty line immediately before a module-closing `End Name.` line.
Keep the last definition, proof, or declaration adjacent to the enclosing
`End`.

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

## Configure Programs

Rust `configure` mutates `meta`. In Rocq, write `configure` as a monadic
configure program of type `𝓒 columns unit`:

```coq
Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate {| ... |} in
  return🞵 tt.
```

For polymorphic gadgets, make `configure` polymorphic in `columns` and pass the
used selector and advice columns as parameters:

```coq
Definition configure {columns : Columns.t}
    (q_add : columns.(Columns.Selector))
    (a b c : columns.(Columns.Advice))
    : 𝓒 columns unit := ...
```

Nested configure calls should sequence the child `configure` with `do🞵`.
Call `𝓒.run_unit` only at extraction or comparison boundaries that need an
actual `ConstraintSystem.t`.

For Orchard-only gadgets, use the absolute Orchard columns directly:

```coq
Require Import Garden.Orchard.columns.

Definition configure
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate name_gate in
  return🞵 tt.
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
In the configure JSON, semantic constraints are lowered to their polynomial
expression form. For example, `Constraint.Equal lhs rhs` serializes as
`lhs - rhs`, `Constraint.Boolean x` serializes as the boolean range-check
polynomial, and `Constraint.Either left right` serializes as the product of the
two lowered branch expressions. There are no semantic constraint wrapper nodes
in the JSON format. Configure expressions use flattened associative nodes:
additions are `{"tag":"Sum","args":[...]}`, multiplications are
`{"tag":"Product","args":[...]}`, and all other expression nodes keep their
direct shape.

The full synthesis trace from the Rust implementation is generated separately into
`Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json`; it
records the same raw synthesis events that Rocq extraction regenerates into
`Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json` for comparison.

The generated files intentionally do not encode the extra Halo2 metadata such as
query tables, equality/permutation columns, constants, or minimum degree; those
remain available in the high-level JSON artifact.

`Garden/Halo2/serialize.v` owns the typed-to-indexed projection used by the Rocq
model JSON extraction. This includes the column-family map, expression map,
semantic-constraint lowering to polynomial expressions, gate map, lookup map,
and constraint-system map. Keep these mapping functions out of
`Garden/Halo2/main.v` so the core DSL and proof semantics stay typed and
semantic.

Keep the handwritten translation's expression shapes aligned with the generated
Halo2 AST, including cases where Rust uses explicit products instead of
`Constraints::with_selector`, or `Expression::Scaled` instead of multiplication
by a constant.

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
free-monad type. Their constructors live in the `𝓡` and `𝓛` modules.
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
an evaluator for `𝓡` and `𝓛`. The serializer is the only place where typed cells
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
dependencies. Numeric region indices are confined to this file: `region_index_of`
maps semantic region constructors back to the legacy snapshot index before
selecting a start row.

`Garden/Orchard/regions.v` is the source of truth for synthesis region names.
It defines a true inductive hierarchy instead of wrapping raw `Z` indices:

```coq
RegionId.WitnessInput RegionId.WitnessInput.PsiOld
RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint
RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi
RegionId.AddressIntegrity
  (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck)
```

Repeated Rust gadgets should receive explicit semantic region IDs from their
caller. For example, the variable-base ECC mul synthesize function takes
separate region IDs for the main multiplication and each overflow-check region.
Standalone gadget smoke models use `RegionId.GadgetLocal ...`; these still map
to snapshot index `0` because they are not part of the full Orchard floor-plan.

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
  𝓛.AddRegion (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip) "gate name" (
    𝓡.EnableSelector Selector.QExample 0 "").
```

For multi-step programs:

```coq
Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  let🞵 _ := first_layouter_step in
  second_layouter_step.

Definition synthesize_region
    : 𝓡 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 _ := 𝓡.EnableSelector Selector.QExample 0 "" in
  let🞵 cell := 𝓡.AssignAdvice "value" Advice.A0 0 0 in
  return🞵 cell.

Definition synthesize_pair
    : 𝓛 columns RegionId.t unit :=
  let🞵 '(left, right) := returns_pair in
  use_pair left right.
```

Each `𝓛.AddRegion` must pass the concrete semantic region id for that Rust
region occurrence. Reused gadgets should expose region parameters, or a small
record/function of region parameters, so the caller decides the concrete
occurrence without arithmetic on snapshot indices.

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
`𝓡`/`𝓛` syntax into raw JSON events using the supplied column indices and
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

The comparison checks the payload directly. Configure snapshots contain only the
`configure` object; synthesis snapshots contain only the `events` list.

Current comparison status: strict synthesis JSON comparison succeeds. The model
and implementation both emit 19617 events, and
`opam exec -- make -C Garden orchard-synthesis-json-compare` verifies equality
of the event list.

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
    let b = meta.query_advice(b, Rotation::cur());

    Constraints::with_selector(q, [a - b])
});
```

Rocq:

```coq
Definition name_gate : Gate.t columns := {|
  Gate.name := "name";
  Gate.constraints :=
    let a := Expression.Advice a Rotation.cur in
    let b := Expression.Advice b Rotation.cur in
    Constraints.with_selector q [
      (None, Constraint.Equal a b)
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate name_gate in
  return🞵 tt.
```

For parameterized gadgets, make the named gate take the selector, fixed, advice,
or instance columns used inside the gate:

```coq
Definition name_gate {columns : Columns.t}
    (q : columns.(Columns.Selector))
    (a : columns.(Columns.Advice))
    : Gate.t columns := {|
  Gate.name := "name";
  Gate.constraints := ...;
|}.

Definition configure {columns : Columns.t}
    (q : columns.(Columns.Selector))
    (a : columns.(Columns.Advice))
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate (name_gate q a) in
  return🞵 tt.
```

Put query-like `let` bindings inside `Gate.constraints`, matching the Rust gate
closure body. Configure programs should call `𝓒.CreateGate name_gate` rather
than building anonymous gate records inline. This keeps configure output stable
while giving proof files a stable gate name to reference.

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
do🞵 𝓒.CreateLookup {|
  LookupArgument.pairs :=
    let q := Expression.Selector q in
    let value := Expression.Advice advice Rotation.cur in
    [
      (q ✖️ value, table_idx)
    ];
|} in
return🞵 tt
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

Translate constraints using the most precise semantic constructor available:

```coq
Constraint.Equal lhs rhs
Constraint.Boolean expression
Constraint.Range expression range
Constraint.Either left right
```

Use `Constraint.EqualZeroToPrecise expression` only as a fallback for constraints
that have not yet been refined.

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

That file evaluates expressions modulo a prime and interprets the semantic
`Constraint` constructors as propositions.

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
