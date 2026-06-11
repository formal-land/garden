Require Export Garden.Halo2.main.
Require Garden.Halo2.Synthesis.

Require Export Stdlib.Lists.List.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

(** Concrete, serialization-facing synthesis data. The typed synthesis code
    converts circuit-specific columns and cells into these raw numeric
    references before emitting JSON events. *)
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
    used when emitting raw configure and synthesis data. *)
Module Indices.
  Record t {columns : Columns.t} : Set := {
    selector : columns.(Columns.Selector) -> Z;
    fixed : columns.(Columns.Fixed) -> Z;
    lookup : columns.(Columns.Lookup) -> Z;
    advice : columns.(Columns.Advice) -> Z;
    instance_ : columns.(Columns.Instance_) -> Z;
  }.
  Arguments t : clear implicits.
  Arguments selector {_} _ _.
  Arguments fixed {_} _ _.
  Arguments lookup {_} _ _.
  Arguments advice {_} _ _.
  Arguments instance_ {_} _ _.
End Indices.

Module ColumnRef.
  Definition t := Garden.Halo2.Synthesis.ColumnRef.t.

  Definition to_raw {columns : Columns.t}
      (indices : Indices.t columns)
      (column : t columns) : Raw.ColumnRef.t :=
    match column with
    | Garden.Halo2.Synthesis.ColumnRef.Advice column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Advice;
        Raw.ColumnRef.index := indices.(Indices.advice) column;
      |}
    | Garden.Halo2.Synthesis.ColumnRef.Fixed column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
        Raw.ColumnRef.index := indices.(Indices.fixed) column;
      |}
    | Garden.Halo2.Synthesis.ColumnRef.Instance_ column => {|
        Raw.ColumnRef.kind := Raw.ColumnKind.Instance_;
        Raw.ColumnRef.index := indices.(Indices.instance_) column;
      |}
    end.
End ColumnRef.

Module Cell.
  Definition t := Garden.Halo2.Synthesis.Cell.t.

  Definition to_raw {columns : Columns.t} {RegionId : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (cell : t columns RegionId) : Raw.Cell.t := {|
    Raw.Cell.column :=
      ColumnRef.to_raw
        indices
        (Garden.Halo2.Synthesis.Cell.column cell);
    Raw.Cell.row :=
      match Garden.Halo2.Synthesis.Cell.column cell with
      | Garden.Halo2.Synthesis.ColumnRef.Instance_ _ =>
          Garden.Halo2.Synthesis.Cell.row_offset cell
      | _ =>
          region_start (Garden.Halo2.Synthesis.Cell.region cell)
            + Garden.Halo2.Synthesis.Cell.row_offset cell
      end;
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

Module LookupTableColumn := Garden.Halo2.Synthesis.LookupTableColumn.

Module Configure.
  Definition indexed_columns : Columns.t := {|
    Columns.Selector := Z;
    Columns.Fixed := Z;
    Columns.Lookup := Z;
    Columns.Advice := Z;
    Columns.Instance_ := Z;
  |}.
  Canonical indexed_columns.

  Definition column_map {columns : Columns.t}
      (indices : Indices.t columns)
      : Columns.map columns indexed_columns :=
    @Columns.Build_map
      columns
      indexed_columns
      indices.(Indices.selector)
      indices.(Indices.fixed)
      indices.(Indices.lookup)
      indices.(Indices.advice)
      indices.(Indices.instance_).

  Definition to_indexed {columns : Columns.t}
      (indices : Indices.t columns)
      (system : ConstraintSystem.t columns)
      : ConstraintSystem.t indexed_columns :=
    ConstraintSystem.map (column_map indices) system.
End Configure.

Module V1.
  Definition make_cell {columns : Columns.t} {RegionId : Set}
      (region : RegionId)
      (column : Garden.Halo2.Synthesis.ColumnRef.t columns)
      (offset : Z) : Garden.Halo2.Synthesis.Cell.t columns RegionId := {|
    Garden.Halo2.Synthesis.Cell.column := column;
    Garden.Halo2.Synthesis.Cell.region := region;
    Garden.Halo2.Synthesis.Cell.row_offset := offset;
  |}.

  Fixpoint eval_region {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (region : RegionId)
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A) {struct program}
      : A * list Raw.Event.t :=
    match program with
    | Garden.Halo2.Synthesis.ℛ.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.ℛ.Bind first second =>
        let '(value, events_first) :=
          eval_region indices region_start region first in
        let '(value, events_second) :=
          eval_region indices region_start region (second value) in
        (value, events_first ++ events_second)
    | Garden.Halo2.Synthesis.ℛ.EnableSelector selector offset annotation =>
        (
          tt,
          [
            Raw.Event.EnableSelector
              (indices.(Indices.selector) selector)
              (region_start region + offset)
              annotation
          ])
    | Garden.Halo2.Synthesis.ℛ.AssignFixed annotation column offset value =>
        (
          tt,
          [
            Raw.Event.AssignFixed
              (indices.(Indices.fixed) column)
              (region_start region + offset)
              annotation
              value
          ])
    | Garden.Halo2.Synthesis.ℛ.Copy lhs rhs =>
        (
          tt,
          [
            Raw.Event.Copy
              (Cell.to_raw indices region_start lhs)
              (Cell.to_raw indices region_start rhs)
          ])
    end.

  Fixpoint value_at_row (row : nat) (values : list Z) {struct row}
      : option Z :=
    match row, values with
    | O, [] => None
    | O, value :: _ => Some value
    | S row, [] => None
    | S row, _ :: values => value_at_row row values
    end.

  Fixpoint max_entry_length {columns : Columns.t}
      (entries : list (LookupTableColumn.t columns)) : nat :=
    match entries with
    | [] => 0%nat
    | entry :: entries =>
        Nat.max
          (List.length (LookupTableColumn.values entry))
          (max_entry_length entries)
    end.

  Definition assign_lookup_entry_at_row {columns : Columns.t}
      (indices : Indices.t columns)
      (row : nat)
      (entry : LookupTableColumn.t columns) : list Raw.Event.t :=
    match value_at_row row (LookupTableColumn.values entry) with
    | None => []
    | Some value =>
        [
          Raw.Event.AssignFixed
            (indices.(Indices.lookup) (LookupTableColumn.lookup entry))
            (Z.of_nat row)
            (LookupTableColumn.annotation entry)
            value
        ]
    end.

  Fixpoint assign_lookup_row {columns : Columns.t}
      (indices : Indices.t columns)
      (row : nat)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    match entries with
    | [] => []
    | entry :: entries =>
        assign_lookup_entry_at_row indices row entry
          ++ assign_lookup_row indices row entries
    end.

  Fixpoint assign_lookup_rows {columns : Columns.t}
      (indices : Indices.t columns)
      (rows_remaining row : nat)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    match rows_remaining with
    | O => []
    | S rows_remaining =>
        assign_lookup_row indices row entries
          ++ assign_lookup_rows indices rows_remaining (S row) entries
    end.

  Fixpoint fill_lookup_entries {columns : Columns.t}
      (indices : Indices.t columns)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    match entries with
    | [] => []
    | entry :: entries =>
        [
          Raw.Event.FillFromRow
            (indices.(Indices.lookup) (LookupTableColumn.lookup entry))
            (Z.of_nat (List.length (LookupTableColumn.values entry)))
            (LookupTableColumn.default_value entry)
        ] ++ fill_lookup_entries indices entries
    end.

  Definition init_lookup_table_events {columns : Columns.t}
      (indices : Indices.t columns)
      (name : string)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    [Raw.Event.EnterRegion name]
      ++ assign_lookup_rows indices (max_entry_length entries) 0%nat entries
      ++ [Raw.Event.ExitRegion name]
      ++ fill_lookup_entries indices entries.

  Fixpoint eval_layouter {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A) {struct program}
      : A * list Raw.Event.t :=
    match program with
    | Garden.Halo2.Synthesis.ℒ.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.ℒ.Bind first second =>
        let '(value, events_first) :=
          eval_layouter indices region_start first in
        let '(value, events_second) :=
          eval_layouter indices region_start (second value) in
        (value, events_first ++ events_second)
    | Garden.Halo2.Synthesis.ℒ.AddRegion region name region_program =>
        let '(value, events) :=
          eval_region indices region_start region (region_program region) in
        (
          value,
          [Raw.Event.EnterRegion name]
            ++ events
            ++ [Raw.Event.ExitRegion name])
    | Garden.Halo2.Synthesis.ℒ.ConstrainInstance cell instance row =>
        (
          tt,
          [
            Raw.Event.Copy
              (Cell.to_raw indices region_start cell)
              (Cell.instance_raw indices instance row)
          ])
    | Garden.Halo2.Synthesis.ℒ.InitLookupTables name entries =>
        (tt, init_lookup_table_events indices name entries)
    | Garden.Halo2.Synthesis.ℒ.InNamespace name nested =>
        let '(value, events) :=
          eval_layouter indices region_start nested in
        (
          value,
          [Raw.Event.PushNamespace name]
            ++ events
            ++ [Raw.Event.PopNamespace name])
    end.

  Definition run_with_region_start {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      : A * list Raw.Event.t :=
    eval_layouter indices region_start program.
End V1.
