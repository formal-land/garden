Require Import Garden.Halo2.main.

Require Export Stdlib.Lists.List.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

(** Concrete, serialization-facing synthesis data. The typed synthesis code
    below converts circuit-specific columns and cells into these raw numeric
    references before emitting events. *)
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
  End Event.
End Raw.

(** Maps typed circuit columns and selectors to the concrete numeric indexes
    used when emitting raw synthesis events. *)
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

Module RegionColumn.
  Inductive t : Set :=
  | Column (column : Raw.ColumnRef.t)
  | Selector (selector : Z).

  Definition of_column_ref {columns : Columns.t}
      (indices : Indices.t columns)
      (column : ColumnRef.t columns) : t :=
    Column (ColumnRef.to_raw indices column).

  Definition of_selector {columns : Columns.t}
      (indices : Indices.t columns)
      (selector : columns.(Columns.Selector)) : t :=
    Selector (indices.(Indices.selector) selector).

  Definition column_kind_eqb
      (lhs rhs : Raw.ColumnKind.t) : bool :=
    match lhs, rhs with
    | Raw.ColumnKind.Advice, Raw.ColumnKind.Advice => true
    | Raw.ColumnKind.Fixed, Raw.ColumnKind.Fixed => true
    | Raw.ColumnKind.Instance_, Raw.ColumnKind.Instance_ => true
    | _, _ => false
    end.

  Definition column_ref_eqb
      (lhs rhs : Raw.ColumnRef.t) : bool :=
    column_kind_eqb lhs.(Raw.ColumnRef.kind) rhs.(Raw.ColumnRef.kind)
      && Z.eqb lhs.(Raw.ColumnRef.index) rhs.(Raw.ColumnRef.index).

  Definition eqb (lhs rhs : t) : bool :=
    match lhs, rhs with
    | Column lhs, Column rhs => column_ref_eqb lhs rhs
    | Selector lhs, Selector rhs => Z.eqb lhs rhs
    | _, _ => false
    end.

  Definition is_advice (column : t) : bool :=
    match column with
    | Column raw =>
        match raw.(Raw.ColumnRef.kind) with
        | Raw.ColumnKind.Advice => true
        | _ => false
        end
    | Selector _ => false
    end.

  Fixpoint mem (column : t) (columns : list t) : bool :=
    match columns with
    | [] => false
    | head :: tail => eqb column head || mem column tail
    end.

  Fixpoint unique (columns : list t) : list t :=
    match columns with
    | [] => []
    | head :: tail =>
        let tail := unique tail in
        if mem head tail then tail else head :: tail
    end.
End RegionColumn.

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

  Definition instance_raw {columns : Columns.t}
      (indices : Indices.t columns)
      (instance : columns.(Columns.Instance_))
      (row : Z) : Raw.Cell.t := {|
    Raw.Cell.column := {|
      Raw.ColumnRef.kind := Raw.ColumnKind.Instance_;
      Raw.ColumnRef.index := indices.(Indices.instance_) instance;
    |};
    Raw.Cell.row := row;
  |}.
End Cell.

Module RegionShape.
  Record t {columns : Columns.t} : Set := {
    index : Z;
    used_columns : list RegionColumn.t;
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
      (column : RegionColumn.t)
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
      let region_column :=
        RegionColumn.of_column_ref state.(indices) column in
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) region_column offset;
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
      let region_column :=
        RegionColumn.of_selector state.(indices) selector in
      (tt, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) region_column offset;
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
      let region_column :=
        RegionColumn.of_column_ref state.(indices) column_ref in
      let cell := make_cell state column_ref offset in
      (cell, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) region_column offset;
        events := state.(events);
      |}).

  Definition assign_fixed {columns : Columns.t}
      (annotation : string)
      (column : columns.(Columns.Fixed))
      (offset : Z)
      (value : Value.t) : t columns (Cell.t columns) :=
    fun state =>
      let column_ref := ColumnRef.Fixed column in
      let region_column :=
        RegionColumn.of_column_ref state.(indices) column_ref in
      let row := state.(region_start) + offset in
      let cell := make_cell state column_ref offset in
      (cell, {|
        indices := state.(indices);
        region_index := state.(region_index);
        region_start := state.(region_start);
        region_start_of := state.(region_start_of);
        shape := RegionShape.touch state.(shape) region_column offset;
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

  Definition copy_to_raw {columns : Columns.t}
      (left : Cell.t columns)
      (right : Raw.Cell.t) : t columns unit :=
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
              right
          ];
      |}).

  Definition copy_to_instance {columns : Columns.t}
      (left : Cell.t columns)
      (instance : columns.(Columns.Instance_))
      (row : Z) : t columns unit :=
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
              (Cell.instance_raw state.(indices) instance row)
          ];
      |}).

  Definition constrain_equal {columns : Columns.t}
      (left right : Cell.t columns) : t columns unit :=
    copy left right.

  Definition constrain_constant {columns : Columns.t}
      (_cell : Cell.t columns)
      (_constant : Z) : t columns unit :=
    ret tt.

  Definition copy_advice {columns : Columns.t}
      (annotation : string)
      (source : Cell.t columns)
      (column : columns.(Columns.Advice))
      (offset : Z)
      (value : Value.t) : t columns (Cell.t columns) :=
    bind
      (assign_advice annotation column offset value)
      (fun target =>
        bind (copy target source) (fun _ =>
        ret target)).

  Definition assign_advice_from_constant {columns : Columns.t}
      (annotation : string)
      (column : columns.(Columns.Advice))
      (offset : Z)
      (constant : Z) : t columns (Cell.t columns) :=
    bind
      (assign_advice annotation column offset (Value.Known constant))
      (fun cell =>
        bind (constrain_constant cell constant) (fun _ =>
        ret cell)).

  Definition assign_advice_from_instance {columns : Columns.t}
      (annotation : string)
      (instance : columns.(Columns.Instance_))
      (row : Z)
      (advice : columns.(Columns.Advice))
      (offset : Z) : t columns (Cell.t columns * Value.t) :=
    bind
      (assign_advice annotation advice offset Value.Unknown)
      (fun cell =>
        bind (copy_to_instance cell instance row) (fun _ =>
        ret (cell, Value.Unknown))).

  Definition instance_value {columns : Columns.t}
      (_instance : columns.(Columns.Instance_))
      (_row : Z) : t columns Value.t :=
    ret Value.Unknown.

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

  Definition initial_state_with_region_start {columns : Columns.t}
      (indices : Indices.t columns)
      (region_start_of : Z -> Z) : state columns := {|
    indices := indices;
    next_region := 0;
    region_start_of := region_start_of;
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

  Definition assign_table_with_fills {columns : Columns.t}
      (name : string)
      (table_events fill_events : list Raw.Event.t) : t columns unit :=
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
            ++ [Raw.Event.ExitRegion name]
            ++ fill_events;
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

Module Planner.
  Module Interval.
    Record t : Set := {
      start : Z;
      length : Z;
    }.
  End Interval.

  Definition allocation : Set :=
    list (RegionColumn.t * list Interval.t).

  Definition interval_end (interval : Interval.t) : Z :=
    interval.(Interval.start) + interval.(Interval.length).

  Definition overlaps
      (start length : Z)
      (interval : Interval.t) : bool :=
    negb
      ((start + length <=? interval.(Interval.start))
        || (interval_end interval <=? start)).

  Fixpoint intervals_for
      (column : RegionColumn.t)
      (allocations : allocation) : list Interval.t :=
    match allocations with
    | [] => []
    | (allocated_column, intervals) :: tail =>
        if RegionColumn.eqb column allocated_column
        then intervals
        else intervals_for column tail
    end.

  Fixpoint column_is_free
      (column : RegionColumn.t)
      (start length : Z)
      (intervals : list Interval.t) : bool :=
    match intervals with
    | [] => true
    | interval :: tail =>
        negb (overlaps start length interval)
          && column_is_free column start length tail
    end.

  Fixpoint all_columns_are_free
      (columns : list RegionColumn.t)
      (allocations : allocation)
      (start length : Z) : bool :=
    match columns with
    | [] => true
    | column :: tail =>
        column_is_free column start length (intervals_for column allocations)
          && all_columns_are_free tail allocations start length
    end.

  Fixpoint max_allocated_end_in_intervals
      (intervals : list Interval.t) : Z :=
    match intervals with
    | [] => 0
    | interval :: tail =>
        Z.max (interval_end interval) (max_allocated_end_in_intervals tail)
    end.

  Fixpoint max_allocated_end
      (allocations : allocation) : Z :=
    match allocations with
    | [] => 0
    | (_, intervals) :: tail =>
        Z.max
          (max_allocated_end_in_intervals intervals)
          (max_allocated_end tail)
    end.

  Fixpoint find_start_with_fuel
      (fuel : nat)
      (columns : list RegionColumn.t)
      (allocations : allocation)
      (length start : Z) : Z :=
    match fuel with
    | O => start
    | S fuel =>
        if all_columns_are_free columns allocations start length
        then start
        else find_start_with_fuel fuel columns allocations length (start + 1)
    end.

  Definition first_fit_start
      (columns : list RegionColumn.t)
      (allocations : allocation)
      (length : Z) : Z :=
    if length <=? 0
    then 0
    else
      find_start_with_fuel
        (Z.to_nat (max_allocated_end allocations + 2))
        columns
        allocations
        length
        0.

  Fixpoint add_interval
      (column : RegionColumn.t)
      (interval : Interval.t)
      (allocations : allocation) : allocation :=
    match allocations with
    | [] => [(column, [interval])]
    | (allocated_column, intervals) :: tail =>
        if RegionColumn.eqb column allocated_column
        then (allocated_column, interval :: intervals) :: tail
        else (allocated_column, intervals) :: add_interval column interval tail
    end.

  Fixpoint add_interval_to_columns
      (columns : list RegionColumn.t)
      (interval : Interval.t)
      (allocations : allocation) : allocation :=
    match columns with
    | [] => allocations
    | column :: tail =>
        add_interval_to_columns tail interval (add_interval column interval allocations)
    end.

  Fixpoint count_advice_columns
      (columns : list RegionColumn.t) : Z :=
    match columns with
    | [] => 0
    | column :: tail =>
        (if RegionColumn.is_advice column then 1 else 0)
          + count_advice_columns tail
    end.

  Definition advice_area {columns : Columns.t}
      (shape : RegionShape.t columns) : Z :=
    count_advice_columns (RegionColumn.unique shape.(RegionShape.used_columns))
      * shape.(RegionShape.row_count).

  Fixpoint insert_by_advice_area {columns : Columns.t}
      (shape : RegionShape.t columns)
      (shapes : list (RegionShape.t columns)) : list (RegionShape.t columns) :=
    match shapes with
    | [] => [shape]
    | head :: tail =>
        if advice_area shape <? advice_area head
        then shape :: shapes
        else head :: insert_by_advice_area shape tail
    end.

  Fixpoint sort_by_advice_area {columns : Columns.t}
      (shapes : list (RegionShape.t columns)) : list (RegionShape.t columns) :=
    match shapes with
    | [] => []
    | shape :: tail =>
        insert_by_advice_area shape (sort_by_advice_area tail)
    end.

  Definition place_shape {columns : Columns.t}
      (state : list (Z * Z) * allocation)
      (shape : RegionShape.t columns) : list (Z * Z) * allocation :=
    let '(starts, allocations) := state in
    let used_columns := RegionColumn.unique shape.(RegionShape.used_columns) in
    let length := shape.(RegionShape.row_count) in
    let start := first_fit_start used_columns allocations length in
    let interval := {|
      Interval.start := start;
      Interval.length := length;
    |} in
    let allocations :=
      if length <=? 0
      then allocations
      else add_interval_to_columns used_columns interval allocations in
    ((shape.(RegionShape.index), start) :: starts, allocations).

  Definition slot_in_biggest_advice_first {columns : Columns.t}
      (shapes : list (RegionShape.t columns)) : list (Z * Z) :=
    fst
      (List.fold_left
        place_shape
        (List.rev (sort_by_advice_area shapes))
        ([], [])).

  Fixpoint region_start_of
      (starts : list (Z * Z))
      (region_index : Z) : Z :=
    match starts with
    | [] => 0
    | (index, start) :: tail =>
        if Z.eqb index region_index
        then start
        else region_start_of tail region_index
    end.
End Planner.

Module V1.
  Definition run_with_region_start {columns : Columns.t} {A : Type}
      (indices : Indices.t columns)
      (region_start_of : Z -> Z)
      (program : Layouter.t columns A) : A * list Raw.Event.t :=
    let '(value, state) :=
      program
        (Layouter.initial_state_with_region_start
          indices
          region_start_of) in
    (value, state.(Layouter.events)).

  Definition run {columns : Columns.t} {A : Type}
      (indices : Indices.t columns)
      (program : Layouter.t columns A) : A * list Raw.Event.t :=
    let '(_, measurement_state) := program (Layouter.initial_state indices) in
    let region_starts :=
      Planner.slot_in_biggest_advice_first measurement_state.(Layouter.shapes) in
    let '(value, state) :=
      run_with_region_start
        indices
        (Planner.region_start_of region_starts)
        program in
    (value, state).
End V1.
