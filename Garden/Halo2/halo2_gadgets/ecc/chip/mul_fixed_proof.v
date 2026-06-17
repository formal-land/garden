Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Definition interpolated_x {p : Z} `{Prime p}
    (c0 c1 c2 c3 c4 c5 c6 c7 window : Z)
    : Z :=
  UnOp.from c0 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 1 *F UnOp.from c1 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 2 *F UnOp.from c2 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 3 *F UnOp.from c3 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 4 *F UnOp.from c4 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 5 *F UnOp.from c5 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 6 *F UnOp.from c6 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 7 *F UnOp.from c7.

Module CoordsCheck.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z : Z)
      : Garden.Halo2.halo2_gadgets.utilities_proof.Point.t := {|
    Garden.Halo2.halo2_gadgets.utilities_proof.Point.x :=
      interpolated_x c0 c1 c2 c3 c4 c5 c6 c7 window;
    Garden.Halo2.halo2_gadgets.utilities_proof.Point.y :=
      Garden.Halo2.halo2_gadgets.utilities_proof.square u -F fixed_z;
  |}.
End CoordsCheck.

Module RunningSumCoordinatesCheck.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 z_cur z_next u fixed_z : Z)
      : Garden.Halo2.halo2_gadgets.utilities_proof.Point.t :=
    let window :=
      z_cur -F
        z_next *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h in
    CoordsCheck.output c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z.
End RunningSumCoordinatesCheck.
