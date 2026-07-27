Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Halo2.halo2_gadgets.utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition range_check_gate {columns : Columns.t}
    (window_num_bits : Z)
    (q_range_check : columns.(Columns.Selector))
    (z : columns.(Columns.Advice))
    : Gate.t columns := {|
  Gate.name := "range check";
  Gate.constraints :=
    let z_cur := Expression.Advice z Rotation.cur in
    let z_next := Expression.Advice z Rotation.next in
    let two_pow_k := 2 ^ window_num_bits in
    let word := z_cur ➖ (z_next ● two_pow_k) in
    Constraints.with_selector q_range_check [
      (None,
        Constraint.Range word (Z.to_nat two_pow_k))
    ];
|}.

Definition configure {columns : Columns.t}
    (window_num_bits : Z)
    (q_range_check : columns.(Columns.Selector))
    (z : columns.(Columns.Advice))
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate (range_check_gate window_num_bits q_range_check z) in
  return🞵 tt.

Definition synthesize {columns : Columns.t} {RegionId : Set}
    : 𝓛 columns RegionId unit :=
  return🞵 tt.
