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
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      let🞵 _ := ℛ.EnableSelector selector offset "" in
      enable_selector_rows selector (offset + 1) count
  end.

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      let🞵 _ := ℛ.EnableSelector Selector.QLookup offset "" in
      let🞵 _ := ℛ.EnableSelector Selector.QRunning offset "" in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition copy_advice_column
    (source_column target_column : Advice.t)
    (source_offset target_offset : Z)
    : 𝓡 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 source :=
    ℛ.AssignAdvice "source" source_column source_offset 0 in
  copy_advice "copy" source target_column target_offset 0.

Definition copy_raw_advice
    (source_column source_row : Z)
    (target_column : Advice.t)
    (target_offset : Z)
    : 𝓡 columns RegionId.t (Cell.t columns RegionId.t) :=
  ℛ.AssignAdvice "copy" target_column target_offset 0.

Module OverflowSources.
  Record t : Set := {
    z_2 : Cell.t columns RegionId.t;
    z_126 : Cell.t columns RegionId.t;
    z_136 : Cell.t columns RegionId.t;
  }.
End OverflowSources.

Module MulResult.
  Record t : Set := {
    x : Cell.t columns RegionId.t;
    y : Cell.t columns RegionId.t;
    overflow_sources : OverflowSources.t;
  }.
End MulResult.

Definition synthesize_variable_base_scalar_mul_region
    (base_x base_y : Cell.t columns RegionId.t)
    : 𝓡 columns RegionId.t MulResult.t :=
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 0 "" in
  let🞵 _ := copy_advice "x_p" base_x Advice.A0 0 0 in
  let🞵 _ := copy_advice "y_p" base_y Advice.A1 0 0 in
  let🞵 _ := copy_advice "x_q" base_x Advice.A2 0 0 in
  let🞵 _ := copy_advice "y_q" base_y Advice.A3 0 0 in
  let🞵 z_2 := ℛ.AssignAdvice "z_2" Advice.A9 2 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QMulIncompleteHi1 1 "" in
  let🞵 _ := enable_selector_rows Selector.QMulIncompleteHi2 2 124%nat in
  let🞵 _ := ℛ.EnableSelector Selector.QMulIncompleteHi3 126 "" in
  let🞵 z_126 := ℛ.AssignAdvice "z_126" Advice.A9 126 0 in
  let🞵 _ := copy_advice_column Advice.A9 Advice.A9 1 1 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A3 1 2 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A4 1 1 in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 2 0 in
  let🞵 _ := copy_advice "copy" base_y Advice.A1 2 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QMulIncompleteLo1 1 "" in
  let🞵 _ := enable_selector_rows Selector.QMulIncompleteLo2 2 125%nat in
  let🞵 _ := ℛ.EnableSelector Selector.QMulIncompleteLo3 127 "" in
  let🞵 _ := copy_advice_column Advice.A9 Advice.A6 126 1 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A7 127 2 in
  let🞵 _ := copy_advice_column Advice.A4 Advice.A8 127 1 in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 2 0 in
  let🞵 _ := copy_advice "copy" base_y Advice.A1 2 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QMulDecomposeVar 130 "" in
  let🞵 _ := ℛ.EnableSelector Selector.QMulDecomposeVar 132 "" in
  let🞵 _ := ℛ.EnableSelector Selector.QMulDecomposeVar 134 "" in
  let🞵 _ := copy_advice_column Advice.A6 Advice.A9 127 129 in
  let🞵 _ := copy_advice "copy" base_y Advice.A9 130 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 129 "" in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 129 0 in
  let🞵 _ := copy_advice_column Advice.A1 Advice.A1 129 129 in
  let🞵 _ := copy_advice_column Advice.A7 Advice.A2 128 129 in
  let🞵 _ := copy_advice_column Advice.A8 Advice.A3 128 129 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 130 "" in
  let🞵 _ := copy_advice_column Advice.A7 Advice.A0 128 130 in
  let🞵 _ := copy_advice_column Advice.A8 Advice.A1 128 130 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 130 130 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 130 130 in
  let🞵 _ := copy_advice "copy" base_y Advice.A9 132 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 131 "" in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 131 0 in
  let🞵 _ := copy_advice_column Advice.A1 Advice.A1 131 131 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 131 131 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 131 131 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 132 "" in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A0 131 132 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A1 131 132 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 132 132 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 132 132 in
  let🞵 _ := copy_advice "copy" base_y Advice.A9 134 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 133 "" in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 133 0 in
  let🞵 _ := copy_advice_column Advice.A1 Advice.A1 133 133 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 133 133 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 133 133 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 134 "" in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A0 133 134 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A1 133 134 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 134 134 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 134 134 in
  let🞵 _ := ℛ.EnableSelector Selector.QMulLsb 135 "" in
  let🞵 z_136 := ℛ.AssignAdvice "z_136" Advice.A9 136 0 in
  let🞵 _ := copy_advice "copy" base_x Advice.A0 136 0 in
  let🞵 _ := copy_advice "copy" base_y Advice.A1 136 0 in
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 135 "" in
  let🞵 _ := copy_advice_column Advice.A0 Advice.A0 135 135 in
  let🞵 _ := copy_advice_column Advice.A1 Advice.A1 135 135 in
  let🞵 _ := copy_advice_column Advice.A2 Advice.A2 135 135 in
  let🞵 _ := copy_advice_column Advice.A3 Advice.A3 135 135 in
  let🞵 x := ℛ.AssignAdvice "result x" Advice.A2 136 0 in
  let🞵 y := ℛ.AssignAdvice "result y" Advice.A3 136 0 in
  return🞵 {|
    MulResult.x := x;
    MulResult.y := y;
    MulResult.overflow_sources := {|
      OverflowSources.z_2 := z_2;
      OverflowSources.z_126 := z_126;
      OverflowSources.z_136 := z_136;
    |};
  |}.

Definition synthesize_running_sum_decomposition
    (region : RegionId.t)
    (s : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  ℒ.InNamespace "decompose s_{0..=129}" (
    ℒ.InNamespace "Decompose low 130 bits of s" (
      ℒ.AddRegion region "13 words range check" (
        let🞵 _ := copy_advice "copy" s Advice.A9 0 0 in
        let🞵 _ := enable_lookup_running_rows 0 13%nat in
        ℛ.AssignAdvice "z_13" Advice.A9 13 0))).

Definition synthesize_overflow_check
    (first_region_index : Z)
    (sources : OverflowSources.t)
    : 𝓛 columns RegionId.t unit :=
  ℒ.InNamespace "overflow check" (
    let🞵 s :=
      ℒ.AddRegion
        (RegionId.of_index first_region_index)
        "s = alpha + k_254 ⋅ 2^130" (
        ℛ.AssignAdvice "s" Advice.A6 0 0) in
    let🞵 z_13 :=
      synthesize_running_sum_decomposition
        (RegionId.of_index (first_region_index + 1))
        s in
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 2))
      "overflow check" (
      let🞵 _ := ℛ.EnableSelector Selector.QMulOverflow 1 "" in
      let🞵 _ :=
        copy_advice
          "copy" sources.(OverflowSources.z_136) Advice.A6 0 0 in
      let🞵 _ :=
        copy_advice
          "copy" sources.(OverflowSources.z_126) Advice.A6 1 0 in
      let🞵 _ :=
        copy_advice
          "copy" sources.(OverflowSources.z_2) Advice.A7 0 0 in
      let🞵 _ := copy_raw_advice 2 1688 Advice.A7 1 in
      let🞵 _ :=
        copy_advice "copy" z_13 Advice.A7 2 0 in
      let🞵 _ :=
        copy_advice "copy" s Advice.A8 1 0 in
      return🞵 tt)).

Definition synthesize
    (first_region_index : Z)
    (base_x base_y : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t MulResult.t :=
  ℒ.InNamespace "variable-base scalar mul" (
    let🞵 result :=
      ℒ.AddRegion
        (RegionId.of_index first_region_index)
        "variable-base scalar mul"
        (synthesize_variable_base_scalar_mul_region base_x base_y) in
    let🞵 _ :=
      synthesize_overflow_check
        (first_region_index + 1)
        result.(MulResult.overflow_sources) in
    return🞵 result).
