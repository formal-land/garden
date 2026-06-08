Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.
Require Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.

Import ListNotations.
Global Open Scope pstring_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Full-width fixed-base scalar mul";
    Gate.constraints :=
      let window := Expression.Advice Advice.A4 Rotation.cur in
      Constraints.with_selector
        Selector.QMulFixedFull
        (Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.coords_check
          window
        ++ [
          (Some "window range check",
            Constraint.EqualZeroToPrecise
              (Garden.Halo2.Gadgets.Utilities.range_check
                window
                Garden.Halo2.Gadgets.Ecc.chip.constants.h_nat))
        ]);
  |} in
  meta.

Definition synthesize
    : Layouter.t columns unit :=
  Layouter.assign_region "Full-width fixed-base scalar mul" (
    Region.enable_selector Selector.QMulFixedFull 0 "").
