Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module ColumnKind.
  Inductive t : Set :=
  | Advice
  | Fixed
  | Instance
  | LookupTable.
End ColumnKind.

Module Column.
  Record t : Set := {
    kind : ColumnKind.t;
    index : Z;
    label : string;
  }.

  Definition make (kind : ColumnKind.t) (index : Z) (label : string) : t := {|
    kind := kind;
    index := index;
    label := label;
  |}.

  Definition advice (index : Z) (label : string) : t :=
    make ColumnKind.Advice index label.

  Definition fixed (index : Z) (label : string) : t :=
    make ColumnKind.Fixed index label.

  Definition instance (index : Z) (label : string) : t :=
    make ColumnKind.Instance index label.

  Definition lookup_table (index : Z) (label : string) : t :=
    make ColumnKind.LookupTable index label.
End Column.

Module Selector.
  Record t : Set := {
    index : Z;
    label : string;
    complex : bool;
  }.

  Definition make (index : Z) (label : string) : t := {|
    index := index;
    label := label;
    complex := false;
  |}.

  Definition complex_selector (index : Z) (label : string) : t := {|
    index := index;
    label := label;
    complex := true;
  |}.
End Selector.

Module Rotation.
  Inductive t : Set :=
  | Cur
  | Prev
  | Next
  | At (offset : Z).
End Rotation.

Module Query.
  Inductive t : Set :=
  | Advice (column : Column.t) (rotation : Rotation.t)
  | Fixed (column : Column.t) (rotation : Rotation.t)
  | Instance (column : Column.t) (rotation : Rotation.t)
  | Selector (selector : Selector.t)
  | Challenge (name : string)
  | NamedCell (name : string).
End Query.

Module Expr.
  Inductive t : Set :=
  | Constant (value : Z)
  | Query (query : Query.t)
  | Add (x y : t)
  | Sub (x y : t)
  | Neg (x : t)
  | Mul (x y : t)
  | Named (name : string) (body : t).

  Definition zero : t := Constant 0.
  Definition one : t := Constant 1.
  Definition minus_one : t := Constant (-1).

  Definition advice (column : Column.t) (rotation : Rotation.t) : t :=
    Query (Query.Advice column rotation).

  Definition fixed (column : Column.t) (rotation : Rotation.t) : t :=
    Query (Query.Fixed column rotation).

  Definition instance (column : Column.t) (rotation : Rotation.t) : t :=
    Query (Query.Instance column rotation).

  Definition selector (selector : Selector.t) : t :=
    Query (Query.Selector selector).

  Definition named_cell (name : string) : t :=
    Query (Query.NamedCell name).
End Expr.

Notation "x +H y" := (Expr.Add x y) (at level 50, left associativity).
Notation "x -H y" := (Expr.Sub x y) (at level 50, left associativity).
Notation "x *H y" := (Expr.Mul x y) (at level 40, left associativity).
Notation "-H x" := (Expr.Neg x) (at level 35, right associativity).

Module GateConstraint.
  Record t : Set := {
    name : string;
    expression : Expr.t;
  }.

  Definition make (name : string) (expression : Expr.t) : t := {|
    name := name;
    expression := expression;
  |}.
End GateConstraint.

Module Gate.
  Record t : Set := {
    name : string;
    selector : option Selector.t;
    constraints : list GateConstraint.t;
  }.

  Definition make (name : string) (selector : option Selector.t)
      (constraints : list GateConstraint.t) : t := {|
    name := name;
    selector := selector;
    constraints := constraints;
  |}.
End Gate.

Module Lookup.
  Record pair : Set := {
    input : Expr.t;
    table : Column.t;
  }.

  Record t : Set := {
    name : string;
    selector : option Selector.t;
    pairs : list pair;
  }.

  Definition make (name : string) (selector : option Selector.t) (pairs : list pair) : t := {|
    name := name;
    selector := selector;
    pairs := pairs;
  |}.

  Definition pair_make (input : Expr.t) (table : Column.t) : pair := {|
    input := input;
    table := table;
  |}.
End Lookup.

Module Config.
  Module Event.
    Inductive t : Set :=
    | AdviceColumn (column : Column.t)
    | FixedColumn (column : Column.t)
    | InstanceColumn (column : Column.t)
    | LookupTableColumn (column : Column.t)
    | Selector (selector : Selector.t)
    | EnableEquality (column : Column.t)
    | EnableConstant (column : Column.t)
    | CreateGate (gate : Gate.t)
    | CreateLookup (lookup : Lookup.t)
    | ConfigureChip
        (chip_name : string)
        (summary : string)
        (dependencies : list string).
  End Event.

  Definition Trace : Set := list Event.t.
End Config.

Module CellRef.
  Record t : Set := {
    name : string;
    column : option Column.t;
    row : option Z;
  }.

  Definition make (name : string) (column : option Column.t) (row : option Z) : t := {|
    name := name;
    column := column;
    row := row;
  |}.

  Definition named (name : string) : t :=
    make name None None.

  Definition located (name : string) (column : Column.t) (row : Z) : t :=
    make name (Some column) (Some row).
End CellRef.

Module RegionEvent.
  Inductive t : Set :=
  | EnableSelector (selector : Selector.t) (offset : Z)
  | AssignAdvice (annotation : string) (column : Column.t) (offset : Z)
  | AssignFixed (annotation : string) (column : Column.t) (offset : Z)
  | AssignAdviceFromInstance
      (annotation : string)
      (instance_column : Column.t)
      (instance_row : Z)
      (advice_column : Column.t)
      (offset : Z)
  | CopyAdvice
      (annotation : string)
      (source : CellRef.t)
      (column : Column.t)
      (offset : Z)
  | ConstrainEqual
      (annotation : string)
      (left right : CellRef.t)
  | Note (message : string).
End RegionEvent.

Module TableEvent.
  Inductive t : Set :=
  | AssignCell (annotation : string) (column : Column.t) (offset : Z)
  | Note (message : string).
End TableEvent.

Module Synth.
  Module Event.
    Inductive t : Set :=
    | Namespace (name : string) (events : list t)
    | Region (name : string) (events : list RegionEvent.t)
    | Table (name : string) (events : list TableEvent.t)
    | LoadTable (name : string)
    | ConstructChip (name : string)
    | ConstrainInstance
        (annotation : string)
        (cell : CellRef.t)
        (instance_column : Column.t)
        (row : Z)
    | ConstrainEqual
        (annotation : string)
        (left right : CellRef.t)
    | Call
        (name : string)
        (arguments : list string)
    | Witness
        (name : string)
        (kind : string)
    | Return
        (name : string)
    | Note
        (message : string).
  End Event.

  Definition Trace : Set := list Event.t.
End Synth.

Module Chip.
  Record t : Set := {
    name : string;
    config_name : string;
    dependencies : list string;
    configure : Config.Trace;
    synthesize : Synth.Trace;
  }.
End Chip.

Module Circuit.
  Record t : Set := {
    name : string;
    dependencies : list string;
    configure : Config.Trace;
    synthesize : Synth.Trace;
  }.
End Circuit.

Definition trace_of_chip (chip : Chip.t) : Circuit.t := {|
  Circuit.name := chip.(Chip.name);
  Circuit.dependencies := chip.(Chip.dependencies);
  Circuit.configure := chip.(Chip.configure);
  Circuit.synthesize := chip.(Chip.synthesize);
|}.
