Require Import Garden.Halo2.Gadgets.Utilities_proof.
Require Garden.Halo2.Gadgets.Sinsemilla.chip.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Definition x_r {p : Z} `{Prime p}
    (x_a x_p lambda_1 : Z)
    : Z :=
  Garden.Halo2.Gadgets.Utilities_proof.square lambda_1 -F x_a -F x_p.

Definition y_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  (lambda_1 +F lambda_2) *F
    (x_a -F x_r x_a x_p lambda_1).

Module InitialYQ.
  Record t : Set := {
    y_a : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (y_q : Z)
      : t := {|
    y_a := y_q *F UnOp.from 2;
  |}.
End InitialYQ.

Module Sinsemilla.
  Record t : Set := {
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_cur x_p_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_a_next :=
      Garden.Halo2.Gadgets.Utilities_proof.square lambda_2_cur -F
        x_r x_a_cur x_p_cur lambda_1_cur -F
        x_a_cur;
  |}.
End Sinsemilla.
