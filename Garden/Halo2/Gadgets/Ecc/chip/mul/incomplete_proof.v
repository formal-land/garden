Require Import Garden.Halo2.Gadgets.Utilities_proof.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Definition x_r {p : Z} `{Prime p}
    (x_a x_p lambda_1 : Z)
    : Z :=
  Garden.Halo2.Gadgets.Utilities_proof.square lambda_1 -F x_a -F x_p.

Definition y_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  ((lambda_1 +F lambda_2) *F
    (x_a -F x_r x_a x_p lambda_1)) *F
    UnOp.from Garden.Halo2.Gadgets.Ecc.chip.constants.two_inv.

Definition next_x_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  Garden.Halo2.Gadgets.Utilities_proof.square lambda_2 -F
    x_r x_a x_p lambda_1 -F
    x_a.

Module QMul1Checks.
  Record t : Set := {
    y_a_witnessed : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_next x_p_next lambda_1_next lambda_2_next : Z)
      : t := {|
    y_a_witnessed :=
      y_a x_a_next x_p_next lambda_1_next lambda_2_next;
  |}.
End QMul1Checks.

Module QMul2Checks.
  Record t : Set := {
    x_p_next : Z;
    y_p_next : Z;
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_p_cur y_p_cur x_a_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_p_next := x_p_cur;
    y_p_next := y_p_cur;
    x_a_next := next_x_a x_a_cur x_p_cur lambda_1_cur lambda_2_cur;
  |}.
End QMul2Checks.

Module QMul3Checks.
  Record t : Set := {
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_cur x_p_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_a_next := next_x_a x_a_cur x_p_cur lambda_1_cur lambda_2_cur;
  |}.
End QMul3Checks.
