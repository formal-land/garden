Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.complete.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.overflow.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.configure
      meta
      Selector.QMulIncompleteHi1
      Selector.QMulIncompleteHi2
      Selector.QMulIncompleteHi3
      Advice.A9
      Advice.A3
      Advice.A0
      Advice.A1
      Advice.A4
      Advice.A5 in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.configure
      meta
      Selector.QMulIncompleteLo1
      Selector.QMulIncompleteLo2
      Selector.QMulIncompleteLo3
      Advice.A6
      Advice.A7
      Advice.A0
      Advice.A1
      Advice.A8
      Advice.A2 in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.complete.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.overflow.configure
      meta in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "LSB check";
    Gate.constraints :=
      let z_1 := Expression.Advice Advice.A9 Rotation.cur in
      let z_0 := Expression.Advice Advice.A9 Rotation.next in
      let x_p := Expression.Advice Advice.A0 Rotation.cur in
      let y_p := Expression.Advice Advice.A1 Rotation.cur in
      let base_x := Expression.Advice Advice.A0 Rotation.next in
      let base_y := Expression.Advice Advice.A1 Rotation.next in
      let lsb := z_0 ➖ (z_1 ● 2) in
      let bool_check := Garden.Halo2.Gadgets.Utilities.bool_check lsb in
      let lsb_x :=
        Garden.Halo2.Gadgets.Utilities.ternary
          lsb
          x_p
          (x_p ➖ base_x) in
      let lsb_y :=
        Garden.Halo2.Gadgets.Utilities.ternary
          lsb
          y_p
          (y_p ➕ base_y) in
      Constraints.with_selector
        Selector.QMulLsb
        [
          (Some "bool_check", Constraint.EqualZeroToPrecise bool_check);
          (Some "lsb_x", Constraint.EqualZeroToPrecise lsb_x);
          (Some "lsb_y", Constraint.EqualZeroToPrecise lsb_y)
        ];
  |} in
  meta.

Fixpoint enable_selector_rows
    (selector : Selector.t)
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ := Region.enable_selector selector offset "" in
      enable_selector_rows selector (offset + 1) count
  end.

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ := Region.enable_selector Selector.QLookup offset "" in
      let_ℛ _ := Region.enable_selector Selector.QRunning offset "" in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition copy_advice_column
    (source_column target_column : Advice.t)
    (source_offset target_offset : Z)
    : Region.t columns (Cell.t columns) :=
  let_ℛ source :=
    Region.assign_advice "source" source_column source_offset Value.Unknown in
  Region.copy_advice "copy" source target_column target_offset Value.Unknown.

Definition raw_advice_cell
    (column row : Z)
    : Raw.Cell.t := {|
  Raw.Cell.column := {|
    Raw.ColumnRef.kind := Raw.ColumnKind.Advice;
    Raw.ColumnRef.index := column;
  |};
  Raw.Cell.row := row;
|}.

Definition copy_raw_advice
    (source_column source_row : Z)
    (target_column : Advice.t)
    (target_offset : Z)
    : Region.t columns (Cell.t columns) :=
  let_ℛ target :=
    Region.assign_advice "copy" target_column target_offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_to_raw target (raw_advice_cell source_column source_row) in
  return_ℛ target.

Module OverflowSources.
  Record t : Set := {
    z_2 : Cell.t columns;
    z_126 : Cell.t columns;
    z_136 : Cell.t columns;
  }.
End OverflowSources.

Module MulResult.
  Record t : Set := {
    x : Cell.t columns;
    y : Cell.t columns;
    overflow_sources : OverflowSources.t;
  }.
End MulResult.

Definition synthesize_variable_base_scalar_mul_region
    (base_x base_y : Cell.t columns)
    : Region.t columns MulResult.t :=
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 0 "" in
  let_ℛ _ := Region.copy_advice "x_p" base_x Advice.A0 0 Value.Unknown in
  let_ℛ _ := Region.copy_advice "y_p" base_y Advice.A1 0 Value.Unknown in
  let_ℛ _ := Region.copy_advice "x_q" base_x Advice.A2 0 Value.Unknown in
  let_ℛ _ := Region.copy_advice "y_q" base_y Advice.A3 0 Value.Unknown in
  let_ℛ z_2 := Region.assign_advice "z_2" Advice.A9 2 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QMulIncompleteHi1 1 "" in
  let_ℛ _ := enable_selector_rows Selector.QMulIncompleteHi2 2 124%nat in
  let_ℛ _ := Region.enable_selector Selector.QMulIncompleteHi3 126 "" in
  let_ℛ z_126 := Region.assign_advice "z_126" Advice.A9 126 Value.Unknown in
  let_ℛ _ := copy_advice_column Advice.A9 Advice.A9 1 1 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A3 1 2 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A4 1 1 in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 2 Value.Unknown in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A1 2 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QMulIncompleteLo1 1 "" in
  let_ℛ _ := enable_selector_rows Selector.QMulIncompleteLo2 2 125%nat in
  let_ℛ _ := Region.enable_selector Selector.QMulIncompleteLo3 127 "" in
  let_ℛ _ := copy_advice_column Advice.A9 Advice.A6 126 1 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A7 127 2 in
  let_ℛ _ := copy_advice_column Advice.A4 Advice.A8 127 1 in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 2 Value.Unknown in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A1 2 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QMulDecomposeVar 130 "" in
  let_ℛ _ := Region.enable_selector Selector.QMulDecomposeVar 132 "" in
  let_ℛ _ := Region.enable_selector Selector.QMulDecomposeVar 134 "" in
  let_ℛ _ := copy_advice_column Advice.A6 Advice.A9 127 129 in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A9 130 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 129 "" in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 129 Value.Unknown in
  let_ℛ _ := copy_advice_column Advice.A1 Advice.A1 129 129 in
  let_ℛ _ := copy_advice_column Advice.A7 Advice.A2 128 129 in
  let_ℛ _ := copy_advice_column Advice.A8 Advice.A3 128 129 in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 130 "" in
  let_ℛ _ := copy_advice_column Advice.A7 Advice.A0 128 130 in
  let_ℛ _ := copy_advice_column Advice.A8 Advice.A1 128 130 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 130 130 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 130 130 in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A9 132 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 131 "" in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 131 Value.Unknown in
  let_ℛ _ := copy_advice_column Advice.A1 Advice.A1 131 131 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 131 131 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 131 131 in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 132 "" in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A0 131 132 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A1 131 132 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 132 132 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 132 132 in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A9 134 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 133 "" in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 133 Value.Unknown in
  let_ℛ _ := copy_advice_column Advice.A1 Advice.A1 133 133 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 133 133 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 133 133 in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 134 "" in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A0 133 134 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A1 133 134 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 134 134 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 134 134 in
  let_ℛ _ := Region.enable_selector Selector.QMulLsb 135 "" in
  let_ℛ z_136 := Region.assign_advice "z_136" Advice.A9 136 Value.Unknown in
  let_ℛ _ := Region.copy_advice "copy" base_x Advice.A0 136 Value.Unknown in
  let_ℛ _ := Region.copy_advice "copy" base_y Advice.A1 136 Value.Unknown in
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 135 "" in
  let_ℛ _ := copy_advice_column Advice.A0 Advice.A0 135 135 in
  let_ℛ _ := copy_advice_column Advice.A1 Advice.A1 135 135 in
  let_ℛ _ := copy_advice_column Advice.A2 Advice.A2 135 135 in
  let_ℛ _ := copy_advice_column Advice.A3 Advice.A3 135 135 in
  let_ℛ x := Region.assign_advice "result x" Advice.A2 136 Value.Unknown in
  let_ℛ y := Region.assign_advice "result y" Advice.A3 136 Value.Unknown in
  return_ℛ {|
    MulResult.x := x;
    MulResult.y := y;
    MulResult.overflow_sources := {|
      OverflowSources.z_2 := z_2;
      OverflowSources.z_126 := z_126;
      OverflowSources.z_136 := z_136;
    |};
  |}.

Definition synthesize_running_sum_decomposition
    (s : Cell.t columns)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace "decompose s_{0..=129}" (
    Layouter.namespace "Decompose low 130 bits of s" (
      Layouter.assign_region "13 words range check" (
        let_ℛ _ := Region.copy_advice "copy" s Advice.A9 0 Value.Unknown in
        let_ℛ _ := enable_lookup_running_rows 0 13%nat in
        Region.assign_advice "z_13" Advice.A9 13 Value.Unknown))).

Definition synthesize_overflow_check
    (sources : OverflowSources.t)
    : Layouter.t columns unit :=
  Layouter.namespace "overflow check" (
    let_ℒ s :=
      Layouter.assign_region "s = alpha + k_254 ⋅ 2^130" (
        Region.assign_advice "s" Advice.A6 0 Value.Unknown) in
    let_ℒ z_13 := synthesize_running_sum_decomposition s in
    Layouter.assign_region "overflow check" (
      let_ℛ _ := Region.enable_selector Selector.QMulOverflow 1 "" in
      let_ℛ _ :=
        Region.copy_advice
          "copy" sources.(OverflowSources.z_136) Advice.A6 0 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "copy" sources.(OverflowSources.z_126) Advice.A6 1 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "copy" sources.(OverflowSources.z_2) Advice.A7 0 Value.Unknown in
      let_ℛ _ := copy_raw_advice 2 1688 Advice.A7 1 in
      let_ℛ _ :=
        Region.copy_advice "copy" z_13 Advice.A7 2 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice "copy" s Advice.A8 1 Value.Unknown in
      return_ℛ tt)).

Definition synthesize
    (base_x base_y : Cell.t columns)
    : Layouter.t columns MulResult.t :=
  Layouter.namespace "variable-base scalar mul" (
    let_ℒ result :=
      Layouter.assign_region
        "variable-base scalar mul"
        (synthesize_variable_base_scalar_mul_region base_x base_y) in
    let_ℒ _ :=
      synthesize_overflow_check result.(MulResult.overflow_sources) in
    return_ℒ result).
