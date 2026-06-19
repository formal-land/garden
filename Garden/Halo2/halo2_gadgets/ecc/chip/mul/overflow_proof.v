Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module OverflowChecks.
  Record t : Set := {
    s : Z;
    z_0 : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (alpha k_254 : Z)
      : t := {|
    s := alpha +F k_254 *F UnOp.from (2 ^ 130);
    z_0 :=
      alpha +F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q;
  |}.
End OverflowChecks.
