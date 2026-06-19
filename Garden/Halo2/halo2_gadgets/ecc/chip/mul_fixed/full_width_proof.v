Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module FullWidthFixedBaseScalarMul.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z : Z)
      : Garden.Halo2.halo2_gadgets.utilities_proof.Point.t :=
    CoordsCheck.output c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z.
End FullWidthFixedBaseScalarMul.
