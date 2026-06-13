Require Export Garden.Halo2.main.

Require Export Stdlib.Lists.List.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module ColumnRef.
  Inductive t (columns : Columns.t) : Set :=
  | Advice (column : columns.(Columns.Advice))
  | Fixed (column : columns.(Columns.Fixed))
  | Instance_ (column : columns.(Columns.Instance_)).
  Arguments Advice {_}.
  Arguments Fixed {_}.
  Arguments Instance_ {_}.
End ColumnRef.

Module Cell.
  Record t {columns : Columns.t} {RegionId : Set} : Set := {
    column : ColumnRef.t columns;
    region : RegionId;
    row_offset : Z;
  }.
  Arguments t : clear implicits.

  Definition advice {columns : Columns.t} {RegionId : Set}
      (region : RegionId)
      (column : columns.(Columns.Advice))
      (offset : Z) : t columns RegionId := {|
    column := ColumnRef.Advice column;
    region := region;
    row_offset := offset;
  |}.

  Definition fixed {columns : Columns.t} {RegionId : Set}
      (region : RegionId)
      (column : columns.(Columns.Fixed))
      (offset : Z) : t columns RegionId := {|
    column := ColumnRef.Fixed column;
    region := region;
    row_offset := offset;
  |}.

  Definition instance {columns : Columns.t} {RegionId : Set}
      (region : RegionId)
      (column : columns.(Columns.Instance_))
      (row : Z) : t columns RegionId := {|
    column := ColumnRef.Instance_ column;
    region := region;
    row_offset := row;
  |}.
End Cell.

Module LookupTableColumn.
  (** One lookup-table column to be initialized by the layouter.  The
      serializer emits the concrete fixed-column assignments and then
      fills rows after [values] with [default_value]. *)
  Record t {columns : Columns.t} : Set := {
    lookup : columns.(Columns.Lookup);
    annotation : string;
    values : list Z;
    default_value : Z;
  }.
  Arguments t : clear implicits.
  Arguments lookup {_} _.
  Arguments annotation {_} _.
  Arguments values {_} _.
  Arguments default_value {_} _.
End LookupTableColumn.

Module 𝓡.
  (** Free syntax tree for computations inside a Halo2 region.  The
      serializer interprets this syntax into raw assignment/copy events;
      later proofs can interpret the same syntax into a relational
      semantics. *)
  Inductive t (columns : Columns.t) (RegionId : Set) : Set -> Set :=
  | Ret {A : Set} (value : A) : t columns RegionId A
  | Bind {A B : Set}
      (first : t columns RegionId A)
      (second : A -> t columns RegionId B) : t columns RegionId B
  | EnableSelector
      (selector : columns.(Columns.Selector))
      (offset : Z)
      (annotation : string) : t columns RegionId unit
  | AssignFixed
      (annotation : string)
      (column : columns.(Columns.Fixed))
      (offset : Z)
      (value : Z) : t columns RegionId unit
  | Copy
      (left right : Cell.t columns RegionId) : t columns RegionId unit.
  Arguments Ret {_ _ _}.
  Arguments Bind {_ _ _ _}.
  Arguments EnableSelector {_ _}.
  Arguments AssignFixed {_ _}.
  Arguments Copy {_ _}.
End 𝓡.

Definition 𝓡 := 𝓡.t.

Global Instance RegionIsMonad {columns : Columns.t} {RegionId : Set}
    : Monad.C (𝓡.t columns RegionId) := {|
  Monad.ret := @𝓡.Ret columns RegionId;
  Monad.bind := @𝓡.Bind columns RegionId;
|}.

Module 𝓛.
  (** Free syntax tree for layouter-level computations.  These programs
      create named regions and namespaces, while the region body itself is
      represented by [𝓡]. *)
  Inductive t (columns : Columns.t) (RegionId : Set) : Set -> Set :=
  | Ret {A : Set} (value : A) : t columns RegionId A
  | Bind {A B : Set}
      (first : t columns RegionId A)
      (second : A -> t columns RegionId B) : t columns RegionId B
  | AddRegion {A : Set}
      (region : RegionId)
      (name : string)
      (program : RegionId -> 𝓡 columns RegionId A) : t columns RegionId A
  | ConstrainInstance
      (cell : Cell.t columns RegionId)
      (instance : columns.(Columns.Instance_))
      (row : Z) : t columns RegionId unit
  | InitLookupTables
      (name : string)
      (entries : list (LookupTableColumn.t columns)) : t columns RegionId unit
  | InNamespace {A : Set}
      (name : string)
      (program : t columns RegionId A) : t columns RegionId A.
  Arguments Ret {_ _ _}.
  Arguments Bind {_ _ _ _}.
  Arguments AddRegion {_ _ _}.
  Arguments ConstrainInstance {_ _}.
  Arguments InitLookupTables {_ _}.
  Arguments InNamespace {_ _ _}.
End 𝓛.

Definition 𝓛 := 𝓛.t.

Global Instance LayouterIsMonad {columns : Columns.t} {RegionId : Set}
    : Monad.C (𝓛.t columns RegionId) := {|
  Monad.ret := @𝓛.Ret columns RegionId;
  Monad.bind := @𝓛.Bind columns RegionId;
|}.
