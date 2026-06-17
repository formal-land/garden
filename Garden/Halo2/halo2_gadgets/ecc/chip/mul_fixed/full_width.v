Require Import Garden.Halo2.main.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.common.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.

Import ListNotations.
Global Open Scope pstring_scope.

Definition full_width_fixed_base_scalar_mul_gate : Gate.t columns := {|
  Gate.name := "Full-width fixed-base scalar mul";
  Gate.constraints :=
    let window := Expression.Advice Advice.A4 Rotation.cur in
    Constraints.with_selector
      Selector.QMulFixedFull
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.coords_check
        window
      ++ [
        (Some "window range check",
          Constraint.Range
            window
            Garden.Halo2.halo2_gadgets.ecc.chip.constants.h_nat)
      ]);
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate full_width_fixed_base_scalar_mul_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedFullWidth)
    "Full-width fixed-base scalar mul" (fun _ =>
    𝓡.EnableSelector Selector.QMulFixedFull 0 "").
