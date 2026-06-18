Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module LsbCheck.
  Record t : Set := {
    lsb : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (z_0 z_1 : Z)
      : t := {|
    lsb := z_0 -F z_1 *F UnOp.from 2;
  |}.
End LsbCheck.
