Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module ShortFixedBaseMul.
  Record t : Set := {
    y_a : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (y_p sign : Z)
      : t := {|
    y_a := sign *F y_p;
  |}.
End ShortFixedBaseMul.
