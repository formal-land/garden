Require Import Garden.Halo2.main.

Require Export Stdlib.Lists.List.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module Raw.
  Module ColumnKind.
    Inductive t : Set :=
    | Advice
    | Fixed
    | Instance_.
  End ColumnKind.

  Module ColumnRef.
    Record t : Set := {
      kind : ColumnKind.t;
      index : Z;
    }.
  End ColumnRef.

  Module Cell.
    Record t : Set := {
      column : ColumnRef.t;
      row : Z;
    }.
  End Cell.

  Module Event.
    Inductive t : Set :=
    | EnterRegion (name : string)
    | ExitRegion (name : string)
    | PushNamespace (name : string)
    | PopNamespace (name : string)
    | EnableSelector
        (selector : Z)
        (row : Z)
        (annotation : string)
    | AssignFixed
        (column : Z)
        (row : Z)
        (annotation : string)
        (value : Z)
    | Copy
        (left right : Cell.t)
    | FillFromRow
        (column : Z)
        (from_row : Z)
        (value : Z).

    Definition default : t := EnterRegion "".
  End Event.
End Raw.

Module Indices.
  Record t {columns : Columns.t} : Set := {
    selector : columns.(Columns.Selector) -> Z;
    fixed : columns.(Columns.Fixed) -> Z;
    advice : columns.(Columns.Advice) -> Z;
    instance_ : columns.(Columns.Instance_) -> Z;
  }.
  Arguments t : clear implicits.
  Arguments selector {_} _ _.
  Arguments fixed {_} _ _.
  Arguments advice {_} _ _.
  Arguments instance_ {_} _ _.
End Indices.

Module Value.
  Inductive t : Set :=
  | Known (value : Z)
  | Unknown.

  Definition default : t := Unknown.

  Definition to_z (value : t) : Z :=
    match value with
    | Known value => value
    | Unknown => 0
    end.
End Value.

Module ColumnRef.
  Inductive t (columns : Columns.t) : Set :=
  | Advice (column : columns.(Columns.Advice))
  | Fixed (column : columns.(Columns.Fixed))
  | Instance_ (column : columns.(Columns.Instance_)).
  Arguments Advice {_}.
  Arguments Fixed {_}.
  Arguments Instance_ {_}.

  Definition to_raw {columns : Columns.t}
      (indices : Indices.t columns)
      (column : t columns) : Raw.ColumnRef.t :=
    match column with
    | Advice column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Advice;
        Raw.ColumnRef.index := indices.(Indices.advice) column;
      |}
    | Fixed column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
        Raw.ColumnRef.index := indices.(Indices.fixed) column;
      |}
    | Instance_ column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Instance_;
        Raw.ColumnRef.index := indices.(Indices.instance_) column;
      |}
    end.
End ColumnRef.

Module Cell.
  Record t {columns : Columns.t} : Set := {
    column : ColumnRef.t columns;
    region_index : Z;
    row_offset : Z;
  }.
  Arguments t : clear implicits.
  Arguments column {_} _.
  Arguments region_index {_} _.
  Arguments row_offset {_} _.

  Definition to_raw {columns : Columns.t}
      (indices : Indices.t columns)
      (region_start : Z -> Z)
      (cell : t columns) : Raw.Cell.t := {|
    Raw.Cell.column := ColumnRef.to_raw indices cell.(column);
    Raw.Cell.row := region_start cell.(region_index) + cell.(row_offset);
  |}.
End Cell.

Module RegionShape.
  Record t {columns : Columns.t} : Set := {
    index : Z;
    used_columns : list (ColumnRef.t columns);
    row_count : Z;
  }.
  Arguments t : clear implicits.
  Arguments index {_} _.
  Arguments used_columns {_} _.
  Arguments row_count {_} _.

  Definition empty {columns : Columns.t} (index : Z) : t columns := {|
    index := index;
    used_columns := [];
    row_count := 0;
  |}.

  Definition touch {columns : Columns.t}
      (shape : t columns)
      (column : ColumnRef.t columns)
      (offset : Z) : t columns := {|
    index := shape.(index);
    used_columns := column :: shape.(used_columns);
    row_count := Z.max shape.(row_count) (offset + 1);
  |}.
End RegionShape.

Module Region.
  Record state {columns : Columns.t} : Set := {
    indices : Indices.t columns;
    region_index : Z;
    region_start : Z;
    region_start_of : Z -> Z;
    shape : RegionShape.t columns;
    events : list Raw.Event.t;
  }.
  Arguments state : clear implicits.
  Arguments indices {_} _.
  Arguments region_index {_} _.
  Arguments region_start {_} _.
  Arguments region_start_of {_} _.
  Arguments shape {_} _.
  Arguments events {_} _.

  Definition t (columns : Columns.t) (A : Type) : Type :=
    state columns -> A * state columns.

  Definition ret {columns : Columns.t} {A : Type}
      (value : A) : t columns A :=
    fun state => (value, state).

  Definition bind {columns : Columns.t} {A B : Type}
      (first : t columns A)
      (second : A -> t columns B) : t columns B :=
    fun state =>
      let '(value, state) := first state in
      second value state.

  Definition emit {columns : Columns.t}
      (event : Raw.Event.t) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := state.(shape);
        events := state.(events) ++ [event];
      |}).

  Definition touch {columns : Columns.t}
      (column : ColumnRef.t columns)
      (offset : Z) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) column offset;
        events := state.(events);
      |}).

  Definition make_cell {columns : Columns.t}
      (state : state columns)
      (column : ColumnRef.t columns)
      (offset : Z) : Cell.t columns := {|
    Cell.column := column;
    Cell.region_index := state.(region_index);
    Cell.row_offset := offset;
  |}.

  Definition enable_selector {columns : Columns.t}
      (selector : columns.(Columns.Selector))
      (offset : Z)
      (annotation : string) : t columns unit :=
    fun state =>
      let row := state.(region_start) + offset in
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := state.(shape);
        events :=
          state.(events) ++ [
            Raw.Event.EnableSelector
              (state.(indices).(Indices.selector) selector)
              row
              annotation
          ];
      |}).

  Definition assign_advice {columns : Columns.t}
      (annotation : string)
      (column : columns.(Columns.Advice))
      (offset : Z)
      (_value : Value.t) : t columns (Cell.t columns) :=
    fun state =>
      let column_ref := ColumnRef.Advice column in
      let cell := make_cell state column_ref offset in
      (cell, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) column_ref offset;
        events := state.(events);
      |}).

  Definition assign_fixed {columns : Columns.t}
      (annotation : string)
      (column : columns.(Columns.Fixed))
      (offset : Z)
      (value : Value.t) : t columns (Cell.t columns) :=
    fun state =>
      let column_ref := ColumnRef.Fixed column in
      let row := state.(region_start) + offset in
      let cell := make_cell state column_ref offset in
      (cell, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) column_ref offset;
        events :=
          state.(events) ++ [
            Raw.Event.AssignFixed
              (state.(indices).(Indices.fixed) column)
              row
              annotation
              (Value.to_z value)
          ];
      |}).

  Definition copy {columns : Columns.t}
      (left right : Cell.t columns) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := state.(shape);
        events :=
          state.(events) ++ [
            Raw.Event.Copy
              (Cell.to_raw state.(indices) state.(region_start_of) left)
              (Cell.to_raw state.(indices) state.(region_start_of) right)
          ];
      |}).

  Definition copy_advice {columns : Columns.t}
      (annotation : string)
      (source : Cell.t columns)
      (column : columns.(Columns.Advice))
      (offset : Z)
      (value : Value.t) : t columns (Cell.t columns) :=
    bind
      (assign_advice annotation column offset value)
      (fun target =>
        bind (copy source target) (fun _ =>
        ret target)).

End Region.

Notation "'let_ℛ' x ':=' a 'in' b" :=
  (Region.bind a (fun x => b))
  (at level 200, x name, a at level 100, b at level 200).

Notation "'return_ℛ' x" :=
  (Region.ret x)
  (at level 100).

Module Layouter.
  Record state {columns : Columns.t} : Set := {
    indices : Indices.t columns;
    next_region : Z;
    region_start_of : Z -> Z;
    shapes : list (RegionShape.t columns);
    events : list Raw.Event.t;
  }.
  Arguments state : clear implicits.
  Arguments indices {_} _.
  Arguments next_region {_} _.
  Arguments region_start_of {_} _.
  Arguments shapes {_} _.
  Arguments events {_} _.

  Definition t (columns : Columns.t) (A : Type) : Type :=
    state columns -> A * state columns.

  Definition ret {columns : Columns.t} {A : Type}
      (value : A) : t columns A :=
    fun state => (value, state).

  Definition bind {columns : Columns.t} {A B : Type}
      (first : t columns A)
      (second : A -> t columns B) : t columns B :=
    fun state =>
      let '(value, state) := first state in
      second value state.

  Definition emit {columns : Columns.t}
      (event : Raw.Event.t) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        next_region := state.(next_region);
        region_start_of := state.(region_start_of);
        shapes := state.(shapes);
        events := state.(events) ++ [event];
      |}).

  Definition initial_state {columns : Columns.t}
      (indices : Indices.t columns) : state columns := {|
    indices := indices;
    next_region := 0;
    region_start_of := fun _ => 0;
    shapes := [];
    events := [];
  |}.

  Definition assign_region {columns : Columns.t} {A : Type}
      (name : string)
      (program : Region.t columns A) : t columns A :=
    fun state =>
      let region_index := state.(next_region) in
      let region_start := state.(region_start_of) region_index in
      let initial_region_state := {|
        Region.indices := state.(indices);
        Region.region_index := region_index;
        Region.region_start := region_start;
        Region.region_start_of := state.(region_start_of);
        Region.shape := RegionShape.empty region_index;
        Region.events := [];
      |} in
      let '(value, region_state) := program initial_region_state in
      (value, {|
        indices := state.(indices);
        next_region := region_index + 1;
        region_start_of := state.(region_start_of);
        shapes := state.(shapes) ++ [region_state.(Region.shape)];
        events :=
          state.(events)
            ++ [Raw.Event.EnterRegion name]
            ++ region_state.(Region.events)
            ++ [Raw.Event.ExitRegion name];
      |}).

  Definition assign_table {columns : Columns.t}
      (name : string)
      (table_events : list Raw.Event.t) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        next_region := state.(next_region);
        region_start_of := state.(region_start_of);
        shapes := state.(shapes);
        events :=
          state.(events)
            ++ [Raw.Event.EnterRegion name]
            ++ table_events
            ++ [Raw.Event.ExitRegion name];
      |}).

  Definition push_namespace {columns : Columns.t}
      (name : string) : t columns unit :=
    emit (Raw.Event.PushNamespace name).

  Definition pop_namespace {columns : Columns.t}
      (name : string) : t columns unit :=
    emit (Raw.Event.PopNamespace name).

  Definition namespace {columns : Columns.t} {A : Type}
      (name : string)
      (program : t columns A) : t columns A :=
    bind (push_namespace name) (fun _ =>
    bind program (fun value =>
    bind (pop_namespace name) (fun _ =>
    ret value))).

  Definition constrain_instance {columns : Columns.t}
      (cell : Cell.t columns)
      (instance : columns.(Columns.Instance_))
      (row : Z) : t columns unit :=
    fun state =>
      let instance_cell := {|
        Raw.Cell.column := {|
          Raw.ColumnRef.kind := Raw.ColumnKind.Instance_;
          Raw.ColumnRef.index := state.(indices).(Indices.instance_) instance;
        |};
        Raw.Cell.row := row;
      |} in
      (tt, {|
        indices := state.(indices);
        next_region := state.(next_region);
        region_start_of := state.(region_start_of);
        shapes := state.(shapes);
        events :=
          state.(events) ++ [
            Raw.Event.Copy
              (Cell.to_raw state.(indices) state.(region_start_of) cell)
              instance_cell
          ];
      |}).

  Definition fill_from_row {columns : Columns.t}
      (column : columns.(Columns.Fixed))
      (from_row : Z)
      (value : Value.t) : t columns unit :=
    fun state =>
      (tt, {|
        indices := state.(indices);
        next_region := state.(next_region);
        region_start_of := state.(region_start_of);
        shapes := state.(shapes);
        events :=
          state.(events) ++ [
            Raw.Event.FillFromRow
              (state.(indices).(Indices.fixed) column)
              from_row
              (Value.to_z value)
          ];
      |}).

End Layouter.

Notation "'let_ℒ' x ':=' a 'in' b" :=
  (Layouter.bind a (fun x => b))
  (at level 200, x name, a at level 100, b at level 200).

Notation "'return_ℒ' x" :=
  (Layouter.ret x)
  (at level 100).

Module V1.
  Definition run {columns : Columns.t} {A : Type}
      (indices : Indices.t columns)
      (program : Layouter.t columns A) : A * list Raw.Event.t :=
    let '(value, state) := program (Layouter.initial_state indices) in
    (value, state.(Layouter.events)).
End V1.
