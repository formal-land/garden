Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Decompose scalar for complete bits of variable-base mul";
    Gate.constraints :=
      let z_prev := Expression.Advice Advice.A9 Rotation.prev in
      let z_next := Expression.Advice Advice.A9 Rotation.next in
      let k := z_next -E (z_prev *Z 2) in
      let bool_check := Garden.Halo2.Gadgets.Utilities.bool_check k in
      let base_y := Expression.Advice Advice.A9 Rotation.cur in
      let y_p := Expression.Advice Advice.A1 Rotation.prev in
      let y_switch :=
        Garden.Halo2.Gadgets.Utilities.ternary
          k
          (base_y -E y_p)
          (base_y +E y_p) in
      Constraints.with_selector Selector.QMulDecomposeVar [
        (Some "bool_check", Constraint.EqualZeroToPrecise bool_check);
        (Some "y_switch", Constraint.EqualZeroToPrecise y_switch)
      ];
  |} in
  meta.
