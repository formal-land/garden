Require Import Garden.Halo2.main.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.common.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition lsb_check_gate : Gate.t columns := {|
  Gate.name := "LSB check";
  Gate.constraints :=
    let z_1 := Expression.Advice Advice.A9 Rotation.cur in
    let z_0 := Expression.Advice Advice.A9 Rotation.next in
    let x_p := Expression.Advice Advice.A0 Rotation.cur in
    let y_p := Expression.Advice Advice.A1 Rotation.cur in
    let base_x := Expression.Advice Advice.A0 Rotation.next in
    let base_y := Expression.Advice Advice.A1 Rotation.next in
    let lsb := z_0 ➖ (z_1 ● 2) in
    let lsb_x :=
      Garden.Halo2.halo2_gadgets.utilities.ternary
        lsb
        x_p
        (x_p ➖ base_x) in
    let lsb_y :=
      Garden.Halo2.halo2_gadgets.utilities.ternary
        lsb
        y_p
        (y_p ➕ base_y) in
    Constraints.with_selector
      Selector.QMulLsb
      [
        (Some "bool_check", Constraint.Boolean lsb);
        (Some "lsb_x", Constraint.EqualZeroToPrecise lsb_x);
        (Some "lsb_y", Constraint.EqualZeroToPrecise lsb_y)
      ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵
    Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
      Selector.QMulIncompleteHi1
      Selector.QMulIncompleteHi2
      Selector.QMulIncompleteHi3
      Advice.A9
      Advice.A3
      Advice.A0
      Advice.A1
      Advice.A4
      Advice.A5 in
  do🞵
    Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
      Selector.QMulIncompleteLo1
      Selector.QMulIncompleteLo2
      Selector.QMulIncompleteLo3
      Advice.A6
      Advice.A7
      Advice.A0
      Advice.A1
      Advice.A8
      Advice.A2 in
  do🞵 Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.configure in
  do🞵 Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.configure in
  do🞵 𝓒.CreateGate lsb_check_gate in
  return🞵 tt.

Fixpoint enable_selector_rows
    (selector : Selector.t)
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵 𝓡.EnableSelector selector offset "" in
      enable_selector_rows selector (offset + 1) count
  end.

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵 𝓡.EnableSelector Selector.QLookup offset "" in
      do🞵 𝓡.EnableSelector Selector.QRunning offset "" in
      enable_lookup_running_rows (offset + 1) count
  end.

Module OverflowSources.
  Record t : Set := {
    alpha : Cell.t columns RegionId.t;
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
    (region : RegionId.t)
    (alpha : Cell.t columns RegionId.t)
    (base_x base_y : Cell.t columns RegionId.t)
    : 𝓡 columns RegionId.t MulResult.t :=
  do🞵 𝓡.EnableSelector Selector.QEccAdd 0 "" in
  let target := Cell.advice region Advice.A0 0 in
  do🞵 𝓡.Copy target base_x in
  let target := Cell.advice region Advice.A1 0 in
  do🞵 𝓡.Copy target base_y in
  let target := Cell.advice region Advice.A2 0 in
  do🞵 𝓡.Copy target base_x in
  let target := Cell.advice region Advice.A3 0 in
  do🞵 𝓡.Copy target base_y in
  let z_2 := Cell.advice region Advice.A9 2 in
  (* The running sum for the scalar decomposition starts at zero
     ([mul.rs] [z_init], [assign_advice_from_constant]). *)
  do🞵 𝓡.ConstrainConstant (Cell.advice region Advice.A9 1) 0 in
  do🞵 𝓡.EnableSelector Selector.QMulIncompleteHi1 1 "" in
  do🞵 enable_selector_rows Selector.QMulIncompleteHi2 2 124%nat in
  do🞵 𝓡.EnableSelector Selector.QMulIncompleteHi3 126 "" in
  let z_126 := Cell.advice region Advice.A9 126 in
  let source := Cell.advice region Advice.A9 1 in
  let target := Cell.advice region Advice.A9 1 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 1 in
  let target := Cell.advice region Advice.A3 2 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 1 in
  let target := Cell.advice region Advice.A4 1 in
  do🞵 𝓡.Copy target source in
  let target := Cell.advice region Advice.A0 2 in
  do🞵 𝓡.Copy target base_x in
  let target := Cell.advice region Advice.A1 2 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QMulIncompleteLo1 1 "" in
  do🞵 enable_selector_rows Selector.QMulIncompleteLo2 2 125%nat in
  do🞵 𝓡.EnableSelector Selector.QMulIncompleteLo3 127 "" in
  let source := Cell.advice region Advice.A9 126 in
  let target := Cell.advice region Advice.A6 1 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 127 in
  let target := Cell.advice region Advice.A7 2 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A4 127 in
  let target := Cell.advice region Advice.A8 1 in
  do🞵 𝓡.Copy target source in
  let target := Cell.advice region Advice.A0 2 in
  do🞵 𝓡.Copy target base_x in
  let target := Cell.advice region Advice.A1 2 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QMulDecomposeVar 130 "" in
  do🞵 𝓡.EnableSelector Selector.QMulDecomposeVar 132 "" in
  do🞵 𝓡.EnableSelector Selector.QMulDecomposeVar 134 "" in
  let source := Cell.advice region Advice.A6 127 in
  let target := Cell.advice region Advice.A9 129 in
  do🞵 𝓡.Copy target source in
  let target := Cell.advice region Advice.A9 130 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 129 "" in
  let target := Cell.advice region Advice.A0 129 in
  do🞵 𝓡.Copy target base_x in
  let source := Cell.advice region Advice.A1 129 in
  let target := Cell.advice region Advice.A1 129 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A7 128 in
  let target := Cell.advice region Advice.A2 129 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A8 128 in
  let target := Cell.advice region Advice.A3 129 in
  do🞵 𝓡.Copy target source in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 130 "" in
  let source := Cell.advice region Advice.A7 128 in
  let target := Cell.advice region Advice.A0 130 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A8 128 in
  let target := Cell.advice region Advice.A1 130 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 130 in
  let target := Cell.advice region Advice.A2 130 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 130 in
  let target := Cell.advice region Advice.A3 130 in
  do🞵 𝓡.Copy target source in
  let target := Cell.advice region Advice.A9 132 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 131 "" in
  let target := Cell.advice region Advice.A0 131 in
  do🞵 𝓡.Copy target base_x in
  let source := Cell.advice region Advice.A1 131 in
  let target := Cell.advice region Advice.A1 131 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 131 in
  let target := Cell.advice region Advice.A2 131 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 131 in
  let target := Cell.advice region Advice.A3 131 in
  do🞵 𝓡.Copy target source in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 132 "" in
  let source := Cell.advice region Advice.A2 131 in
  let target := Cell.advice region Advice.A0 132 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 131 in
  let target := Cell.advice region Advice.A1 132 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 132 in
  let target := Cell.advice region Advice.A2 132 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 132 in
  let target := Cell.advice region Advice.A3 132 in
  do🞵 𝓡.Copy target source in
  let target := Cell.advice region Advice.A9 134 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 133 "" in
  let target := Cell.advice region Advice.A0 133 in
  do🞵 𝓡.Copy target base_x in
  let source := Cell.advice region Advice.A1 133 in
  let target := Cell.advice region Advice.A1 133 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 133 in
  let target := Cell.advice region Advice.A2 133 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 133 in
  let target := Cell.advice region Advice.A3 133 in
  do🞵 𝓡.Copy target source in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 134 "" in
  let source := Cell.advice region Advice.A2 133 in
  let target := Cell.advice region Advice.A0 134 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 133 in
  let target := Cell.advice region Advice.A1 134 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 134 in
  let target := Cell.advice region Advice.A2 134 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 134 in
  let target := Cell.advice region Advice.A3 134 in
  do🞵 𝓡.Copy target source in
  do🞵 𝓡.EnableSelector Selector.QMulLsb 135 "" in
  let z_136 := Cell.advice region Advice.A9 136 in
  let target := Cell.advice region Advice.A0 136 in
  do🞵 𝓡.Copy target base_x in
  let target := Cell.advice region Advice.A1 136 in
  do🞵 𝓡.Copy target base_y in
  do🞵 𝓡.EnableSelector Selector.QEccAdd 135 "" in
  let source := Cell.advice region Advice.A0 135 in
  let target := Cell.advice region Advice.A0 135 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A1 135 in
  let target := Cell.advice region Advice.A1 135 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A2 135 in
  let target := Cell.advice region Advice.A2 135 in
  do🞵 𝓡.Copy target source in
  let source := Cell.advice region Advice.A3 135 in
  let target := Cell.advice region Advice.A3 135 in
  do🞵 𝓡.Copy target source in
  let x := Cell.advice region Advice.A2 136 in
  let y := Cell.advice region Advice.A3 136 in
  return🞵 {|
    MulResult.x := x;
    MulResult.y := y;
    MulResult.overflow_sources := {|
      OverflowSources.alpha := alpha;
      OverflowSources.z_2 := z_2;
      OverflowSources.z_126 := z_126;
      OverflowSources.z_136 := z_136;
    |};
  |}.

Definition synthesize_running_sum_decomposition
    (region : RegionId.t)
    (s : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace "decompose s_{0..=129}" (
    𝓛.InNamespace "Decompose low 130 bits of s" (
      𝓛.AddRegion region "13 words range check" (fun region =>
        let target := Cell.advice region Advice.A9 0 in
        do🞵 𝓡.Copy target s in
        do🞵 enable_lookup_running_rows 0 13%nat in
        return🞵 (Cell.advice region Advice.A9 13)))).

Definition synthesize_overflow_check
    (overflow_s_region overflow_lookup_region overflow_check_region : RegionId.t)
    (sources : OverflowSources.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.InNamespace "overflow check" (
    let🞵 s :=
      𝓛.AddRegion
        overflow_s_region
        "s = alpha + k_254 ⋅ 2^130" (fun region =>
        return🞵 (Cell.advice region Advice.A6 0)) in
    let🞵 z_13 :=
      synthesize_running_sum_decomposition
        overflow_lookup_region
        s in
    𝓛.AddRegion
      overflow_check_region
      "overflow check" (fun region =>
      do🞵 𝓡.EnableSelector Selector.QMulOverflow 1 "" in
      let target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy target sources.(OverflowSources.z_136) in
      let target := Cell.advice region Advice.A6 1 in
      do🞵 𝓡.Copy target sources.(OverflowSources.z_126) in
      let target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy target sources.(OverflowSources.z_2) in
      let target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy target sources.(OverflowSources.alpha) in
      let target := Cell.advice region Advice.A7 2 in
      do🞵 𝓡.Copy target z_13 in
      let target := Cell.advice region Advice.A8 1 in
      do🞵 𝓡.Copy target s in
      return🞵 tt)).

Definition synthesize
    (variable_base_region
      overflow_s_region
      overflow_lookup_region
      overflow_check_region : RegionId.t)
    (alpha : Cell.t columns RegionId.t)
    (base_x base_y : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t MulResult.t :=
  𝓛.InNamespace "variable-base scalar mul" (
    let🞵 result :=
      𝓛.AddRegion
        variable_base_region
        "variable-base scalar mul"
        (fun region =>
          synthesize_variable_base_scalar_mul_region region alpha base_x base_y) in
    do🞵
      synthesize_overflow_check
        overflow_s_region
        overflow_lookup_region
        overflow_check_region
        result.(MulResult.overflow_sources) in
    return🞵 result).
