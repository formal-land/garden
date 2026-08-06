(** Focused computation tests for [HighLevelTrace]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.high_level_trace.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module HighLevelTraceTest.
  Definition test_columns : Columns.t := {|
    Columns.Selector := unit;
    Columns.Fixed := unit;
    Columns.Lookup := unit;
    Columns.Advice := unit;
    Columns.Instance_ := unit;
  |}.

  Definition test_indices : Indices.t test_columns := {|
    Indices.selector := fun _ => 10;
    Indices.fixed := fun _ => 20;
    Indices.lookup := fun _ => 30;
    Indices.advice := fun _ => 40;
    Indices.instance_ := fun _ => 50;
  |}.

  Definition test_gate : Gate.t test_columns := {|
    Gate.name := "test gate";
    Gate.constraints := [
      (Some "boolean",
        Constraint.Boolean
          (Expression.Advice (columns := test_columns) tt Rotation.cur))
    ];
  |}.

  Definition test_lookup : LookupArgument.t test_columns := {|
    LookupArgument.pairs := [
      (Expression.Constant (columns := test_columns) 5, tt)
    ];
  |}.

  Definition configure_program : 𝓒 test_columns Z :=
    𝓒.Bind (𝓒.Ret 6) (fun seed =>
    𝓒.Bind (𝓒.CreateGate test_gate) (fun _ =>
    𝓒.Bind (𝓒.CreateLookup test_lookup) (fun _ =>
    𝓒.Ret (seed + 1)))).

  Definition precise_selected_constraint : Constraint.t test_columns :=
    Constraint.Select (columns := test_columns) tt
      (Constraint.EitherZeroToPrecise
        (Expression.Advice (columns := test_columns) tt Rotation.cur)
        (Expression.Constant (columns := test_columns) 5)).

  (** The precise zero-product disjunction retains Rust's left-associated
      selected multiplication tree. *)
  Example precise_selected_constraint_polynomial :
    Configure.constraint_to_expression precise_selected_constraint =
      ((Expression.Selector (columns := test_columns) tt ✖️
        Expression.Advice (columns := test_columns) tt Rotation.cur) ✖️
        Expression.Constant (columns := test_columns) 5).
  Proof. reflexivity. Qed.

  Definition expected_gate : Gate.t Configure.indexed_columns := {|
    Gate.name := "test gate";
    Gate.constraints := [
      (Some "boolean",
        Constraint.Boolean
          (Expression.Advice
            (columns := Configure.indexed_columns) 40 Rotation.cur))
    ];
  |}.

  Definition expected_lookup :
      LookupArgument.t Configure.indexed_columns := {|
    LookupArgument.pairs := [
      (Expression.Constant (columns := Configure.indexed_columns) 5, 30)
    ];
  |}.

  (** Covers configure [Ret], [Bind], [CreateGate], and [CreateLookup],
      including continuation-value threading and operation order. *)
  Example eval_configure_smoke :
    HighLevelTrace.eval_configure test_indices configure_program =
      (7, [
        HighLevelTrace.ConfigureOp.CreateGate expected_gate;
        HighLevelTrace.ConfigureOp.CreateLookup expected_lookup
      ]).
  Proof. reflexivity. Qed.

  Definition metadata_indices : Metadata.IndexMap.t test_columns := {|
    Metadata.IndexMap.selector := fun _ => 0;
    Metadata.IndexMap.fixed := fun _ => 1;
    Metadata.IndexMap.lookup := fun _ => 0;
    Metadata.IndexMap.advice := fun _ => 0;
    Metadata.IndexMap.instance_ := fun _ => 0;
  |}.

  Definition metadata_operations : list (Metadata.Operation.t test_columns) := [
    Metadata.Operation.AllocateLookupTable
      (tt : test_columns.(Columns.Lookup));
    Metadata.Operation.AllocateFixed
      (tt : test_columns.(Columns.Fixed));
    Metadata.Operation.AllocateAdvice
      (tt : test_columns.(Columns.Advice));
    Metadata.Operation.AllocateInstance
      (tt : test_columns.(Columns.Instance_));
    Metadata.Operation.allocate_simple_selector
      (tt : test_columns.(Columns.Selector));
    Metadata.Operation.QueryLookup
      (tt : test_columns.(Columns.Lookup));
    Metadata.Operation.QueryFixed
      (tt : test_columns.(Columns.Fixed));
    Metadata.Operation.QueryAdvice
      (tt : test_columns.(Columns.Advice)) Rotation.prev;
    Metadata.Operation.QueryAdvice
      (tt : test_columns.(Columns.Advice)) Rotation.prev;
    Metadata.Operation.QueryInstance
      (tt : test_columns.(Columns.Instance_)) Rotation.next;
    Metadata.Operation.EnableEqualityAdvice
      (tt : test_columns.(Columns.Advice));
    Metadata.Operation.EnableEqualityAdvice
      (tt : test_columns.(Columns.Advice));
    Metadata.Operation.EnableEqualityInstance
      (tt : test_columns.(Columns.Instance_));
    Metadata.Operation.EnableConstant
      (tt : test_columns.(Columns.Fixed));
    Metadata.Operation.EnableConstant
      (tt : test_columns.(Columns.Fixed));
    Metadata.Operation.SetMinimumDegree 9
  ].

  Definition metadata_program : 𝓒 test_columns unit :=
    𝓒.Metadata metadata_operations.

  Definition expected_metadata_state : Metadata.State.t := {|
    Metadata.State.counts := {|
      Metadata.Counts.fixed := 2;
      Metadata.Counts.advice := 1;
      Metadata.Counts.instance_ := 1;
      Metadata.Counts.selectors := 1;
    |};
    Metadata.State.selector_types := [true];
    Metadata.State.lookup_columns := [0];
    Metadata.State.queries := {|
      Metadata.Queries.advice := [(0, -1); (0, 0)];
      Metadata.Queries.fixed := [(0, 0); (1, 0)];
      Metadata.Queries.instance_ := [(0, 1); (0, 0)];
    |};
    Metadata.State.permutation_columns := [
      {| Metadata.IndexedColumn.kind := Metadata.IndexedColumn.Advice;
         Metadata.IndexedColumn.index := 0 |};
      {| Metadata.IndexedColumn.kind := Metadata.IndexedColumn.Instance_;
         Metadata.IndexedColumn.index := 0 |};
      {| Metadata.IndexedColumn.kind := Metadata.IndexedColumn.Fixed;
         Metadata.IndexedColumn.index := 1 |}
    ];
    Metadata.State.constants := [1];
    Metadata.State.minimum_degree := Some 9%nat;
    Metadata.State.valid := true;
  |}.

  (** Lookup-table and ordinary fixed allocations share one counter.  Queries,
      equality columns, and constants retain first-use order and suppress
      duplicates as Halo2 does. *)
  Example run_metadata_smoke :
    𝓒.run_metadata_unit
      metadata_indices metadata_program Metadata.State.empty =
      expected_metadata_state.
  Proof. reflexivity. Qed.

  (** Configure metadata has no gate-or-lookup effect. *)
  Example run_metadata_erased :
    𝓒.run_unit metadata_program ConstraintSystem.empty =
      ConstraintSystem.empty.
  Proof. reflexivity. Qed.

  Example metadata_rejects_out_of_order_allocation :
    (Metadata.run
      (Indices.to_metadata test_indices)
      [Metadata.Operation.AllocateAdvice
        (tt : test_columns.(Columns.Advice))]
      Metadata.State.empty).(Metadata.State.valid) = false.
  Proof. reflexivity. Qed.

  Definition mapped_metadata_operations :
      list (Metadata.Operation.t Configure.indexed_columns) := [
    Metadata.Operation.AllocateLookupTable
      (30 : Configure.indexed_columns.(Columns.Lookup));
    Metadata.Operation.AllocateFixed
      (20 : Configure.indexed_columns.(Columns.Fixed));
    Metadata.Operation.AllocateAdvice
      (40 : Configure.indexed_columns.(Columns.Advice));
    Metadata.Operation.AllocateInstance
      (50 : Configure.indexed_columns.(Columns.Instance_));
    Metadata.Operation.allocate_simple_selector
      (10 : Configure.indexed_columns.(Columns.Selector));
    Metadata.Operation.QueryLookup
      (30 : Configure.indexed_columns.(Columns.Lookup));
    Metadata.Operation.QueryFixed
      (20 : Configure.indexed_columns.(Columns.Fixed));
    Metadata.Operation.QueryAdvice
      (40 : Configure.indexed_columns.(Columns.Advice)) Rotation.prev;
    Metadata.Operation.QueryAdvice
      (40 : Configure.indexed_columns.(Columns.Advice)) Rotation.prev;
    Metadata.Operation.QueryInstance
      (50 : Configure.indexed_columns.(Columns.Instance_)) Rotation.next;
    Metadata.Operation.EnableEqualityAdvice
      (40 : Configure.indexed_columns.(Columns.Advice));
    Metadata.Operation.EnableEqualityAdvice
      (40 : Configure.indexed_columns.(Columns.Advice));
    Metadata.Operation.EnableEqualityInstance
      (50 : Configure.indexed_columns.(Columns.Instance_));
    Metadata.Operation.EnableConstant
      (20 : Configure.indexed_columns.(Columns.Fixed));
    Metadata.Operation.EnableConstant
      (20 : Configure.indexed_columns.(Columns.Fixed));
    Metadata.Operation.SetMinimumDegree 9
  ].

  Example eval_configure_metadata_smoke :
    HighLevelTrace.eval_configure test_indices metadata_program =
      (tt, [HighLevelTrace.ConfigureOp.Metadata mapped_metadata_operations]).
  Proof. reflexivity. Qed.

  Definition region_index_of (region : Z) : Z := region.

  Definition region_start_of (region : Z) : Z := 100 * region.

  Definition region_program (region : Z) : 𝓡 test_columns Z Z :=
    𝓡.Bind (𝓡.Ret 4) (fun seed =>
    𝓡.Bind
      (𝓡.EnableSelector
        (columns := test_columns) (RegionId := Z)
        tt seed "selector")
      (fun _ =>
    𝓡.Bind
      (𝓡.AssignFixed
        (columns := test_columns) (RegionId := Z)
        "fixed" tt (seed + 1) 8)
      (fun _ =>
    𝓡.Bind
      (𝓡.Copy (columns := test_columns) (RegionId := Z)
        (Cell.advice
          (columns := test_columns) (RegionId := Z)
          region tt (seed + 2))
        (Cell.fixed
          (columns := test_columns) (RegionId := Z)
          region tt (seed + 3)))
      (fun _ =>
    𝓡.Bind
      (𝓡.ConstrainConstant (columns := test_columns) (RegionId := Z)
        (Cell.advice
          (columns := test_columns) (RegionId := Z)
          region tt (seed + 4))
        9)
      (fun _ =>
    𝓡.Ret (seed + 5)))))).

  Definition expected_cell
      (kind : Raw.ColumnKind.t)
      (column region offset absolute_row : Z)
      : HighLevelTrace.Cell.t := {|
    HighLevelTrace.Cell.column := {|
      Raw.ColumnRef.kind := kind;
      Raw.ColumnRef.index := column;
    |};
    HighLevelTrace.Cell.region_index := Some region;
    HighLevelTrace.Cell.offset := offset;
    HighLevelTrace.Cell.absolute_row := absolute_row;
  |}.

  Definition expected_region_trace : list HighLevelTrace.RegionOp.t := [
    HighLevelTrace.RegionOp.EnableSelector 10 4 304 "selector";
    HighLevelTrace.RegionOp.AssignFixed
      (expected_cell Raw.ColumnKind.Fixed 20 3 5 305)
      "fixed"
      8;
    HighLevelTrace.RegionOp.Copy
      (expected_cell Raw.ColumnKind.Advice 40 3 6 306)
      (expected_cell Raw.ColumnKind.Fixed 20 3 7 307);
    HighLevelTrace.RegionOp.ConstrainConstant
      (expected_cell Raw.ColumnKind.Advice 40 3 8 308)
      9
  ].

  (** Covers region [Ret], [Bind], [EnableSelector], [AssignFixed], [Copy],
      and [ConstrainConstant], including relative and absolute cell rows. *)
  Example eval_region_smoke :
    HighLevelTrace.eval_region
      test_indices region_index_of region_start_of 3 (region_program 3) =
      (9, expected_region_trace).
  Proof. reflexivity. Qed.

  Definition test_lookup_table : LookupTableColumn.t test_columns := {|
    LookupTableColumn.lookup := (tt : test_columns.(Columns.Lookup));
    LookupTableColumn.annotation := "table";
    LookupTableColumn.values := [11; 12];
    LookupTableColumn.default_value := 13;
  |}.

  Definition layouter_program : 𝓛 test_columns Z Z :=
    𝓛.Bind (𝓛.Ret 2) (fun seed =>
    𝓛.Bind
      (𝓛.InNamespace "outer"
        (𝓛.InNamespace "inner"
          (𝓛.AddRegion 3 "region" region_program)))
      (fun region_value =>
    𝓛.Bind
      (𝓛.ConstrainInstance (columns := test_columns) (RegionId := Z)
        (Cell.advice
          (columns := test_columns) (RegionId := Z)
          3 tt 8)
        tt 1)
      (fun _ =>
    𝓛.Bind
      (𝓛.InitLookupTables (columns := test_columns) (RegionId := Z)
        "tables" [test_lookup_table])
      (fun _ =>
    𝓛.Ret (seed + region_value))))).

  Definition expected_lookup_table_entry :
      HighLevelTrace.LookupTableEntry.t := {|
    HighLevelTrace.LookupTableEntry.column := 30;
    HighLevelTrace.LookupTableEntry.annotation := "table";
    HighLevelTrace.LookupTableEntry.value_count := 2%nat;
    HighLevelTrace.LookupTableEntry.default_value := 13;
  |}.

  Definition expected_layout_trace : list HighLevelTrace.LayoutNode.t := [
    HighLevelTrace.LayoutNode.Namespace "outer" [
      HighLevelTrace.LayoutNode.Namespace "inner" [
        HighLevelTrace.LayoutNode.Region
          3 300 "region" expected_region_trace
      ]
    ];
    HighLevelTrace.LayoutNode.ConstrainInstance
      (expected_cell Raw.ColumnKind.Advice 40 3 8 308)
      50
      1;
    HighLevelTrace.LayoutNode.InitLookupTables
      "tables"
      [expected_lookup_table_entry]
  ].

  (** Covers layouter [Ret], [Bind], [AddRegion], [ConstrainInstance],
      [InitLookupTables], and nested [InNamespace] nodes. *)
  Example eval_layouter_smoke :
    HighLevelTrace.eval_layouter
      test_indices region_index_of region_start_of layouter_program =
      (11, expected_layout_trace).
  Proof. reflexivity. Qed.
End HighLevelTraceTest.
