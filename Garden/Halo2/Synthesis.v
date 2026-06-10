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

Module ℛ.
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
  | AssignAdvice
      (annotation : string)
      (column : columns.(Columns.Advice))
      (offset : Z)
      (value : Z) : t columns RegionId (Cell.t columns RegionId)
  | AssignFixed
      (annotation : string)
      (column : columns.(Columns.Fixed))
      (offset : Z)
      (value : Z) : t columns RegionId (Cell.t columns RegionId)
  | Copy
      (left right : Cell.t columns RegionId) : t columns RegionId unit.
  Arguments Ret {_ _ _}.
  Arguments Bind {_ _ _ _}.
  Arguments EnableSelector {_ _}.
  Arguments AssignAdvice {_ _}.
  Arguments AssignFixed {_ _}.
  Arguments Copy {_ _}.
End ℛ.

Definition 𝓡 := ℛ.t.

Module Monad.
  Class C (M : Set -> Set) : Set := {
    ret : forall {A : Set}, A -> M A;
    bind : forall {A B : Set}, M A -> (A -> M B) -> M B;
  }.
End Monad.

Arguments Monad.ret {M} {_} {A} _.
Arguments Monad.bind {M} {_} {A B} _ _.

Global Instance RegionIsMonad {columns : Columns.t} {RegionId : Set}
    : Monad.C (ℛ.t columns RegionId) := {|
  Monad.ret := @ℛ.Ret columns RegionId;
  Monad.bind := @ℛ.Bind columns RegionId;
|}.

Notation "'return🞵' x" :=
  (Monad.ret x)
  (at level 100).

Notation "'let🞵' x ':=' a 'in' b" :=
  (Monad.bind a (fun x => b))
  (at level 200, x name, a at level 100, b at level 200).

Notation "'let🞵' ' x ':=' a 'in' b" :=
  (Monad.bind a (fun x => b))
  (at level 200, x pattern, a at level 100, b at level 200).

Definition copy_advice {columns : Columns.t} {RegionId : Set}
    (annotation : string)
    (source : Cell.t columns RegionId)
    (column : columns.(Columns.Advice))
    (offset : Z)
    (value : Z) : 𝓡 columns RegionId (Cell.t columns RegionId) :=
  let🞵 target := ℛ.AssignAdvice annotation column offset value in
  let🞵 _ := ℛ.Copy target source in
  return🞵 target.

Definition assign_advice_from_constant {columns : Columns.t} {RegionId : Set}
    (annotation : string)
    (column : columns.(Columns.Advice))
    (offset : Z)
    (constant : Z) : 𝓡 columns RegionId (Cell.t columns RegionId) :=
  ℛ.AssignAdvice annotation column offset constant.

Module ℒ.
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
      (program : 𝓡 columns RegionId A) : t columns RegionId A
  | InitLookupTables
      (name : string)
      (entries : list (LookupTableColumn.t columns)) : t columns RegionId unit
  | InNamespace {A : Set}
      (name : string)
      (program : t columns RegionId A) : t columns RegionId A.
  Arguments Ret {_ _ _}.
  Arguments Bind {_ _ _ _}.
  Arguments AddRegion {_ _ _}.
  Arguments InitLookupTables {_ _}.
  Arguments InNamespace {_ _ _}.
End ℒ.

Definition 𝓛 := ℒ.t.

Global Instance LayouterIsMonad {columns : Columns.t} {RegionId : Set}
    : Monad.C (ℒ.t columns RegionId) := {|
  Monad.ret := @ℒ.Ret columns RegionId;
  Monad.bind := @ℒ.Bind columns RegionId;
|}.
