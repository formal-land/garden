Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module DecomposeScalarComplete.
  Record t : Set := {
    k : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (z_prev z_next : Z)
      : t := {|
    k := z_next -F UnOp.from 2 *F z_prev;
  |}.
End DecomposeScalarComplete.
