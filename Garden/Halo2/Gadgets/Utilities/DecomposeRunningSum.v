Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure {columns : Columns.t}
    (window_num_bits : Z)
    (meta : ConstraintSystem.t columns)
    (q_range_check : columns.(Columns.Selector))
    (z : columns.(Columns.Advice))
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "range check";
    Gate.constraints :=
      let z_cur := Expression.Advice z Rotation.cur in
      let z_next := Expression.Advice z Rotation.next in
      let two_pow_k := 2 ^ window_num_bits in
      let word := z_cur ➖ (z_next ● two_pow_k) in
      Constraints.with_selector q_range_check [
        (None,
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.range_check
              word
              (Z.to_nat two_pow_k)))
      ];
  |} in
  meta.

Definition synthesize {columns : Columns.t}
    : Layouter.t columns unit :=
  return_ℒ tt.
