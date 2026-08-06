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
        (to_row : Z)
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

  Definition to_metadata {columns : Columns.t}
      (self : t columns) : Metadata.IndexMap.t columns := {|
    Metadata.IndexMap.selector := self.(selector);
    Metadata.IndexMap.fixed := self.(fixed);
    Metadata.IndexMap.lookup := self.(lookup);
    Metadata.IndexMap.advice := self.(advice);
    Metadata.IndexMap.instance_ := self.(instance_);
  |}.
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

  Module ColumnMap.
    Record t (source target : Columns.t) : Set := {
      selector : source.(Columns.Selector) -> target.(Columns.Selector);
      fixed : source.(Columns.Fixed) -> target.(Columns.Fixed);
      lookup : source.(Columns.Lookup) -> target.(Columns.Lookup);
      advice : source.(Columns.Advice) -> target.(Columns.Advice);
      instance_ : source.(Columns.Instance_) -> target.(Columns.Instance_);
    }.
    Arguments t : clear implicits.
    Arguments selector {_ _} _ _.
    Arguments fixed {_ _} _ _.
    Arguments lookup {_ _} _ _.
    Arguments advice {_ _} _ _.
    Arguments instance_ {_ _} _ _.
  End ColumnMap.

  Definition indices_to_column_map {columns : Columns.t}
      (indices : Indices.t columns)
      : ColumnMap.t columns indexed_columns := {|
    ColumnMap.selector := indices.(Indices.selector);
    ColumnMap.fixed := indices.(Indices.fixed);
    ColumnMap.lookup := indices.(Indices.lookup);
    ColumnMap.advice := indices.(Indices.advice);
    ColumnMap.instance_ := indices.(Indices.instance_);
  |}.

  Fixpoint map_expression {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (expression : Expression.t source) : Expression.t target :=
    match expression with
    | Expression.Constant value =>
        Expression.Constant value
    | Expression.Selector selector =>
        Expression.Selector (column_map.(ColumnMap.selector) selector)
    | Expression.Fixed fixed rotation =>
        Expression.Fixed (column_map.(ColumnMap.fixed) fixed) rotation
    | Expression.Advice advice rotation =>
        Expression.Advice (column_map.(ColumnMap.advice) advice) rotation
    | Expression.Instance_ instance rotation =>
        Expression.Instance_ (column_map.(ColumnMap.instance_) instance) rotation
    | Expression.Negated expression =>
        Expression.Negated (map_expression column_map expression)
    | Expression.Sum lhs rhs =>
        Expression.Sum
          (map_expression column_map lhs)
          (map_expression column_map rhs)
    | Expression.Product lhs rhs =>
        Expression.Product
          (map_expression column_map lhs)
          (map_expression column_map rhs)
    | Expression.Scaled expression scale =>
        Expression.Scaled (map_expression column_map expression) scale
    end.

  Definition range_check_expression {columns : Columns.t}
      (word : Expression.t columns)
      (range : nat)
      : Expression.t columns :=
    List.fold_left
      (fun acc i =>
        Expression.Product
          acc
          (Expression.Sum
            (Expression.Constant (Z.of_nat i))
            (Expression.Negated word)))
      (List.seq 1 (Nat.pred range))
      word.

  Fixpoint constraint_to_expression {columns : Columns.t}
      (constraint : Constraint.t columns) : Expression.t columns :=
    match constraint with
    | Constraint.Select selector constraint =>
        match constraint with
        | Constraint.EitherZeroToPrecise lhs rhs =>
            Expression.Product
              (Expression.Product (Expression.Selector selector) lhs)
              rhs
        | _ =>
            Expression.Product
              (Expression.Selector selector)
              (constraint_to_expression constraint)
        end
    | Constraint.Equal lhs rhs =>
        Expression.Sum lhs (Expression.Negated rhs)
    | Constraint.Boolean expression =>
        range_check_expression expression 2
    | Constraint.Range expression range =>
        range_check_expression expression range
    | Constraint.Either lhs rhs =>
        Expression.Product
          (constraint_to_expression lhs)
          (constraint_to_expression rhs)
    | Constraint.EitherZeroToPrecise lhs rhs =>
        Expression.Product lhs rhs
    | Constraint.EqualZeroToPrecise expression =>
        expression
    end.

  Definition map_constraint_to_equal_zero_to_precise
      {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (constraint : Constraint.t source) : Constraint.t target :=
    Constraint.EqualZeroToPrecise
      (map_expression column_map (constraint_to_expression constraint)).

  Definition map_constraints {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (constraints : Constraints.t source) : Constraints.t target :=
    List.map
      (fun constraint =>
        let '(name, constraint) := constraint in
        (name, map_constraint_to_equal_zero_to_precise column_map constraint))
      constraints.

  Definition map_gate {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (gate : Gate.t source) : Gate.t target := {|
    Gate.name := gate.(Gate.name);
    Gate.constraints := map_constraints column_map gate.(Gate.constraints);
  |}.

  Definition map_lookup_argument {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (lookup : LookupArgument.t source) : LookupArgument.t target := {|
    LookupArgument.pairs :=
      List.map
        (fun '(expression, lookup) =>
          (map_expression column_map expression,
            column_map.(ColumnMap.lookup) lookup))
        lookup.(LookupArgument.pairs);
  |}.

  Definition map_constraint_system {source target : Columns.t}
      (column_map : ColumnMap.t source target)
      (system : ConstraintSystem.t source) : ConstraintSystem.t target := {|
    ConstraintSystem.gates :=
      List.map (map_gate column_map) system.(ConstraintSystem.gates);
    ConstraintSystem.lookups :=
      List.map
        (map_lookup_argument column_map)
        system.(ConstraintSystem.lookups);
  |}.

  Definition to_indexed {columns : Columns.t}
      (indices : Indices.t columns)
      (system : ConstraintSystem.t columns)
      : ConstraintSystem.t indexed_columns :=
    map_constraint_system (indices_to_column_map indices) system.
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
    | Garden.Halo2.Synthesis.𝓡.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        let '(value, events_first) :=
          eval_region indices region_start region first in
        let '(value, events_second) :=
          eval_region indices region_start region (second value) in
        (value, events_first ++ events_second)
    | Garden.Halo2.Synthesis.𝓡.EnableSelector selector offset annotation =>
        (
          tt,
          [
            Raw.Event.EnableSelector
              (indices.(Indices.selector) selector)
              (region_start region + offset)
              annotation
          ])
    | Garden.Halo2.Synthesis.𝓡.AssignFixed annotation column offset value =>
        (
          tt,
          [
            Raw.Event.AssignFixed
              (indices.(Indices.fixed) column)
              (region_start region + offset)
              annotation
              value
          ])
    | Garden.Halo2.Synthesis.𝓡.Copy lhs rhs =>
        (
          tt,
          [
            Raw.Event.Copy
              (Cell.to_raw indices region_start lhs)
              (Cell.to_raw indices region_start rhs)
          ])
    | Garden.Halo2.Synthesis.𝓡.ConstrainConstant _ _ =>
        (* The Rust V1 floor planner queues [constrain_constant] requests and
           materializes them only after synthesis, as a trailing block of
           constants-column [AssignFixed] + [Copy] events with
           allocator-chosen rows.  That trailing block is replayed from the
           generated table ([Garden/Orchard/circuit_synthesis_constants.v]),
           so the inline op contributes no raw event of its own. *)
        (tt, [])
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
      (usable_rows : Z)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    match entries with
    | [] => []
    | entry :: entries =>
        [
          Raw.Event.FillFromRow
            (indices.(Indices.lookup) (LookupTableColumn.lookup entry))
            (Z.of_nat (List.length (LookupTableColumn.values entry)))
            usable_rows
            (LookupTableColumn.default_value entry)
        ] ++ fill_lookup_entries indices usable_rows entries
    end.

  Definition init_lookup_table_events {columns : Columns.t}
      (indices : Indices.t columns)
      (usable_rows : Z)
      (name : string)
      (entries : list (LookupTableColumn.t columns)) : list Raw.Event.t :=
    [Raw.Event.EnterRegion name]
      ++ assign_lookup_rows indices (max_entry_length entries) 0%nat entries
      ++ [Raw.Event.ExitRegion name]
      ++ fill_lookup_entries indices usable_rows entries.

  Fixpoint eval_layouter {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (usable_rows : Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A) {struct program}
      : A * list Raw.Event.t :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        let '(value, events_first) :=
          eval_layouter indices region_start usable_rows first in
        let '(value, events_second) :=
          eval_layouter indices region_start usable_rows (second value) in
        (value, events_first ++ events_second)
    | Garden.Halo2.Synthesis.𝓛.AddRegion region name region_program =>
        let '(value, events) :=
          eval_region indices region_start region (region_program region) in
        (
          value,
          [Raw.Event.EnterRegion name]
            ++ events
            ++ [Raw.Event.ExitRegion name])
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance cell instance row =>
        (
          tt,
          [
            Raw.Event.Copy
              (Cell.to_raw indices region_start cell)
              (Cell.instance_raw indices instance row)
          ])
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables name entries =>
        (tt, init_lookup_table_events indices usable_rows name entries)
    | Garden.Halo2.Synthesis.𝓛.InNamespace name nested =>
        let '(value, events) :=
          eval_layouter indices region_start usable_rows nested in
        (
          value,
          [Raw.Event.PushNamespace name]
            ++ events
            ++ [Raw.Event.PopNamespace name])
    end.

  Definition run_with_region_start {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (usable_rows : Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      : A * list Raw.Event.t :=
    eval_layouter indices region_start usable_rows program.
End V1.
