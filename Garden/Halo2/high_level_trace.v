(** Structural traces for the configure and synthesis free monads.

    This module is deliberately parallel to [serialize.v].  The operational
    serializer remains the source of the raw event stream used by parity and
    soundness proofs; this evaluator retains the higher-level namespace,
    semantic-region, and [ConstrainConstant] structure for documentation and
    visualization artifacts.

    [Ret] values are threaded through [Bind] exactly as in [V1.eval_region]
    and [V1.eval_layouter], but are not reified: the result type is arbitrary
    and carries no serialization dictionary. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.serialize.

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Import ListNotations.
Global Open Scope Z_scope.

Module HighLevelTrace.
  Module Cell.
    (** A semantic cell keeps both its region-relative identity and the
        absolute row used by the concrete V1 placement.  Instance cells are
        global, so their [region_index] is [None] and [offset] is their public
        row. *)
    Record t : Set := {
      column : Raw.ColumnRef.t;
      region_index : option Z;
      offset : Z;
      absolute_row : Z;
    }.

    Definition of_typed {columns : Columns.t} {RegionId : Set}
        (indices : Indices.t columns)
        (region_index_of : RegionId -> Z)
        (region_start_of : RegionId -> Z)
        (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) : t :=
      let column := Garden.Halo2.Synthesis.Cell.column cell in
      let region := Garden.Halo2.Synthesis.Cell.region cell in
      let offset := Garden.Halo2.Synthesis.Cell.row_offset cell in
      match column with
      | Garden.Halo2.Synthesis.ColumnRef.Advice advice => {|
          column := {|
            Raw.ColumnRef.kind := Raw.ColumnKind.Advice;
            Raw.ColumnRef.index := indices.(Indices.advice) advice;
          |};
          region_index := Some (region_index_of region);
          offset := offset;
          absolute_row := region_start_of region + offset;
        |}
      | Garden.Halo2.Synthesis.ColumnRef.Fixed fixed => {|
          column := {|
            Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
            Raw.ColumnRef.index := indices.(Indices.fixed) fixed;
          |};
          region_index := Some (region_index_of region);
          offset := offset;
          absolute_row := region_start_of region + offset;
        |}
      | Garden.Halo2.Synthesis.ColumnRef.Instance_ instance => {|
          column := {|
            Raw.ColumnRef.kind := Raw.ColumnKind.Instance_;
            Raw.ColumnRef.index := indices.(Indices.instance_) instance;
          |};
          region_index := None;
          offset := offset;
          absolute_row := offset;
        |}
      end.
  End Cell.

  Module ConfigureOp.
    Inductive t : Set :=
    | CreateGate (gate : Gate.t Configure.indexed_columns)
    | CreateLookup (lookup : LookupArgument.t Configure.indexed_columns)
    | Metadata
        (operations :
          list (Garden.Halo2.main.Metadata.Operation.t
            Configure.indexed_columns)).
  End ConfigureOp.

  Module RegionOp.
    Inductive t : Set :=
    | EnableSelector
        (selector offset absolute_row : Z)
        (annotation : string)
    | AssignFixed
        (cell : Cell.t)
        (annotation : string)
        (value : Z)
    | Copy (lhs rhs : Cell.t)
    | ConstrainConstant (cell : Cell.t) (value : Z).
  End RegionOp.

  Module LookupTableEntry.
    (** Lookup payloads already live in the raw synthesis artifact.  The
        structural trace carries the information useful to the circuit map
        without duplicating the three large table arrays. *)
    Record t : Set := {
      column : Z;
      annotation : string;
      value_count : nat;
      default_value : Z;
    }.
  End LookupTableEntry.

  Module LayoutNode.
    Inductive t : Set :=
    | Namespace (name : string) (children : list t)
    | Region
        (region_index start_row : Z)
        (name : string)
        (operations : list RegionOp.t)
    | ConstrainInstance
        (cell : Cell.t)
        (instance_column row : Z)
    | InitLookupTables
        (name : string)
        (entries : list LookupTableEntry.t).
  End LayoutNode.

  Fixpoint map_constraint {source target : Columns.t}
      (column_map : Configure.ColumnMap.t source target)
      (constraint : Constraint.t source) : Constraint.t target :=
    match constraint with
    | Constraint.Select selector constraint =>
        Constraint.Select
          (column_map.(Configure.ColumnMap.selector) selector)
          (map_constraint column_map constraint)
    | Constraint.Equal lhs rhs =>
        Constraint.Equal
          (Configure.map_expression column_map lhs)
          (Configure.map_expression column_map rhs)
    | Constraint.Boolean expression =>
        Constraint.Boolean (Configure.map_expression column_map expression)
    | Constraint.Range expression range =>
        Constraint.Range (Configure.map_expression column_map expression) range
    | Constraint.Either lhs rhs =>
        Constraint.Either
          (map_constraint column_map lhs)
          (map_constraint column_map rhs)
    | Constraint.EitherZeroToPrecise lhs rhs =>
        Constraint.EitherZeroToPrecise
          (Configure.map_expression column_map lhs)
          (Configure.map_expression column_map rhs)
    | Constraint.EqualZeroToPrecise expression =>
        Constraint.EqualZeroToPrecise
          (Configure.map_expression column_map expression)
    end.

  Definition map_constraints {source target : Columns.t}
      (column_map : Configure.ColumnMap.t source target)
      (constraints : Constraints.t source) : Constraints.t target :=
    List.map
      (fun '(name, constraint) =>
        (name, map_constraint column_map constraint))
      constraints.

  Definition map_gate {source target : Columns.t}
      (column_map : Configure.ColumnMap.t source target)
      (gate : Gate.t source) : Gate.t target := {|
    Gate.name := gate.(Gate.name);
    Gate.constraints := map_constraints column_map gate.(Gate.constraints);
  |}.

  Definition map_metadata_operation {source target : Columns.t}
      (column_map : Configure.ColumnMap.t source target)
      (operation : Garden.Halo2.main.Metadata.Operation.t source)
      : Garden.Halo2.main.Metadata.Operation.t target :=
    match operation with
    | Garden.Halo2.main.Metadata.Operation.AllocateAdvice column =>
        Garden.Halo2.main.Metadata.Operation.AllocateAdvice
          (column_map.(Configure.ColumnMap.advice) column)
    | Garden.Halo2.main.Metadata.Operation.AllocateFixed column =>
        Garden.Halo2.main.Metadata.Operation.AllocateFixed
          (column_map.(Configure.ColumnMap.fixed) column)
    | Garden.Halo2.main.Metadata.Operation.AllocateLookupTable column =>
        Garden.Halo2.main.Metadata.Operation.AllocateLookupTable
          (column_map.(Configure.ColumnMap.lookup) column)
    | Garden.Halo2.main.Metadata.Operation.AllocateInstance column =>
        Garden.Halo2.main.Metadata.Operation.AllocateInstance
          (column_map.(Configure.ColumnMap.instance_) column)
    | Garden.Halo2.main.Metadata.Operation.AllocateSelector selector kind =>
        Garden.Halo2.main.Metadata.Operation.AllocateSelector
          (column_map.(Configure.ColumnMap.selector) selector)
          kind
    | Garden.Halo2.main.Metadata.Operation.QueryAdvice column rotation =>
        Garden.Halo2.main.Metadata.Operation.QueryAdvice
          (column_map.(Configure.ColumnMap.advice) column)
          rotation
    | Garden.Halo2.main.Metadata.Operation.QueryFixed column =>
        Garden.Halo2.main.Metadata.Operation.QueryFixed
          (column_map.(Configure.ColumnMap.fixed) column)
    | Garden.Halo2.main.Metadata.Operation.QueryLookup column =>
        Garden.Halo2.main.Metadata.Operation.QueryLookup
          (column_map.(Configure.ColumnMap.lookup) column)
    | Garden.Halo2.main.Metadata.Operation.QueryInstance column rotation =>
        Garden.Halo2.main.Metadata.Operation.QueryInstance
          (column_map.(Configure.ColumnMap.instance_) column)
          rotation
    | Garden.Halo2.main.Metadata.Operation.EnableEqualityAdvice column =>
        Garden.Halo2.main.Metadata.Operation.EnableEqualityAdvice
          (column_map.(Configure.ColumnMap.advice) column)
    | Garden.Halo2.main.Metadata.Operation.EnableEqualityFixed column =>
        Garden.Halo2.main.Metadata.Operation.EnableEqualityFixed
          (column_map.(Configure.ColumnMap.fixed) column)
    | Garden.Halo2.main.Metadata.Operation.EnableEqualityInstance column =>
        Garden.Halo2.main.Metadata.Operation.EnableEqualityInstance
          (column_map.(Configure.ColumnMap.instance_) column)
    | Garden.Halo2.main.Metadata.Operation.EnableConstant column =>
        Garden.Halo2.main.Metadata.Operation.EnableConstant
          (column_map.(Configure.ColumnMap.fixed) column)
    | Garden.Halo2.main.Metadata.Operation.SetMinimumDegree degree =>
        Garden.Halo2.main.Metadata.Operation.SetMinimumDegree degree
    end.

  Fixpoint eval_configure {columns : Columns.t} {A : Set}
      (indices : Indices.t columns)
      (program : Garden.Halo2.main.𝓒 columns A) {struct program}
      : A * list ConfigureOp.t :=
    let column_map := Configure.indices_to_column_map indices in
    match program with
    | Garden.Halo2.main.𝓒.Ret value =>
        (value, [])
    | Garden.Halo2.main.𝓒.Bind first second =>
        let '(value, first_trace) := eval_configure indices first in
        let '(value, second_trace) :=
          eval_configure indices (second value) in
        (value, first_trace ++ second_trace)
    | Garden.Halo2.main.𝓒.CreateGate gate =>
        (tt, [ConfigureOp.CreateGate (map_gate column_map gate)])
    | Garden.Halo2.main.𝓒.CreateLookup lookup =>
        (tt, [ConfigureOp.CreateLookup
          (Configure.map_lookup_argument column_map lookup)])
    | Garden.Halo2.main.𝓒.Metadata operations =>
        (tt, [ConfigureOp.Metadata
          (List.map (map_metadata_operation column_map) operations)])
    end.

  Fixpoint eval_region {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_index_of : RegionId -> Z)
      (region_start_of : RegionId -> Z)
      (region : RegionId)
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      {struct program}
      : A * list RegionOp.t :=
    match program with
    | Garden.Halo2.Synthesis.𝓡.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        let '(value, first_trace) :=
          eval_region indices region_index_of region_start_of region first in
        let '(value, second_trace) :=
          eval_region indices region_index_of region_start_of region
            (second value) in
        (value, first_trace ++ second_trace)
    | Garden.Halo2.Synthesis.𝓡.EnableSelector selector offset annotation =>
        (tt, [RegionOp.EnableSelector
          (indices.(Indices.selector) selector)
          offset
          (region_start_of region + offset)
          annotation])
    | Garden.Halo2.Synthesis.𝓡.AssignFixed annotation column offset value =>
        let cell := Garden.Halo2.Synthesis.Cell.fixed region column offset in
        (tt, [RegionOp.AssignFixed
          (Cell.of_typed indices region_index_of region_start_of cell)
          annotation
          value])
    | Garden.Halo2.Synthesis.𝓡.Copy lhs rhs =>
        (tt, [RegionOp.Copy
          (Cell.of_typed indices region_index_of region_start_of lhs)
          (Cell.of_typed indices region_index_of region_start_of rhs)])
    | Garden.Halo2.Synthesis.𝓡.ConstrainConstant cell value =>
        (tt, [RegionOp.ConstrainConstant
          (Cell.of_typed indices region_index_of region_start_of cell)
          value])
    end.

  Definition lookup_table_entry {columns : Columns.t}
      (indices : Indices.t columns)
      (entry : Garden.Halo2.Synthesis.LookupTableColumn.t columns)
      : LookupTableEntry.t := {|
    LookupTableEntry.column :=
      indices.(Indices.lookup)
        entry.(Garden.Halo2.Synthesis.LookupTableColumn.lookup);
    LookupTableEntry.annotation :=
      entry.(Garden.Halo2.Synthesis.LookupTableColumn.annotation);
    LookupTableEntry.value_count :=
      List.length entry.(Garden.Halo2.Synthesis.LookupTableColumn.values);
    LookupTableEntry.default_value :=
      entry.(Garden.Halo2.Synthesis.LookupTableColumn.default_value);
  |}.

  Fixpoint eval_layouter {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_index_of : RegionId -> Z)
      (region_start_of : RegionId -> Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : A * list LayoutNode.t :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret value =>
        (value, [])
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        let '(value, first_trace) :=
          eval_layouter indices region_index_of region_start_of first in
        let '(value, second_trace) :=
          eval_layouter indices region_index_of region_start_of
            (second value) in
        (value, first_trace ++ second_trace)
    | Garden.Halo2.Synthesis.𝓛.AddRegion region name region_program =>
        let '(value, operations) :=
          eval_region indices region_index_of region_start_of region
            (region_program region) in
        (value, [LayoutNode.Region
          (region_index_of region)
          (region_start_of region)
          name
          operations])
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance cell instance row =>
        (tt, [LayoutNode.ConstrainInstance
          (Cell.of_typed indices region_index_of region_start_of cell)
          (indices.(Indices.instance_) instance)
          row])
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables name entries =>
        (tt, [LayoutNode.InitLookupTables name
          (List.map (lookup_table_entry indices) entries)])
    | Garden.Halo2.Synthesis.𝓛.InNamespace name nested =>
        let '(value, children) :=
          eval_layouter indices region_index_of region_start_of nested in
        (value, [LayoutNode.Namespace name children])
    end.
End HighLevelTrace.
