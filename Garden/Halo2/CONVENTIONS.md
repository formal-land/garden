# Halo2 Translation Conventions

This file records the current conventions for translating Halo2 Rust circuit
code into Garden/Rocq. Keep it close to the code: update this when the Rocq DSL
or translation style changes.

## File Layout

Shared Halo2 concepts live in:

```text
Garden/Halo2/main.v
```

Orchard files mirror the Rust module path where practical:

```text
orchard/src/circuit.rs
  -> Garden/Orchard/circuit.v

orchard/src/circuit/gadget/add_chip.rs
  -> Garden/Orchard/circuit/gadget/add_chip.v
```

## Imports

Translated files should import the shared Halo2 DSL:

```coq
Require Import Garden.Halo2.main.
```

Prefer adding further imports only when the translated file really needs them.

## Columns

Rust column families become Rocq modules with explicit constructors:

```coq
Module Advice.
  Inductive t : Set :=
  | A0
  | A1.

  Definition to_index (self : t) : Z :=
    match self with
    | A0 => 0
    | A1 => 1
    end.
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

Concrete circuits group their column families with `Columns.t`:

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
      (None, expr)
    ];
|} in
meta
```

Put query-like `let` bindings inside `Gate.constraints`, matching the Rust gate
closure body.

## Constraint Names

Individual constraint names are optional:

```coq
Constraints.t columns = list (option string * Expression.t columns)
```

Use `Some "name"` when the source gives a meaningful label. Use `None` when the
Rust source has an unlabeled expression such as `Some(a + b - c)`.

## Expressions

Use the shared expression constructors and notations from `Garden.Halo2.main`:

```coq
Expression.Advice Advice.A0 Rotation.cur
Expression.Constant 1
x +E y
x -E y
x *E y
```

For selected constraints, use:

```coq
Constraints.with_selector selector constraints
```

This represents multiplying each constraint by the selector expression.
