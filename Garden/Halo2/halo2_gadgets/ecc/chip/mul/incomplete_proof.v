Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Definition x_r {p : Z} `{Prime p}
    (x_a x_p lambda_1 : Z)
    : Z :=
  Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_1 -F x_a -F x_p.

Definition y_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  ((lambda_1 +F lambda_2) *F
    (x_a -F x_r x_a x_p lambda_1)) *F
    UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv.

Definition next_x_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_2 -F
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

  (* The witnessed [y_a] on the current row (read off [lambda_1]) is uniquely
     determined by the next-row coordinates and gradients, via the "init y_a"
     constraint of [q_mul_1_checks_gate]. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_mul_1 : Selector.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : ⟦ q_mul_1 ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_1_checks_gate q_mul_1 x_a x_p lambda_1 lambda_2 ⟧ ρ) :
      {|
        y_a_witnessed := ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice x_a Rotation.next ⟧ ρ)
          (⟦ Expression.Advice x_p Rotation.next ⟧ ρ)
          (⟦ Expression.Advice lambda_1 Rotation.next ⟧ ρ)
          (⟦ Expression.Advice lambda_2 Rotation.next ⟧ ρ).
  Proof.
  Admitted.
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

  (* The next-row base point is copied unchanged ([x_p_check]/[y_p_check]) and the
     next accumulator [x_a] is the secant-line image of the current row, so the
     three next-row cells are uniquely determined by the current row. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_mul_2 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hselector : ⟦ q_mul_2 ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_2_checks_gate q_mul_2 z x_a x_p y_p lambda_1 lambda_2 ⟧ ρ) :
      {|
        x_p_next := ⟦ Expression.Advice x_p Rotation.next ⟧ ρ;
        y_p_next := ⟦ Expression.Advice y_p Rotation.next ⟧ ρ;
        x_a_next := ⟦ Expression.Advice x_a Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice x_p Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice y_p Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice x_a Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_2 Rotation.cur ⟧ ρ).
  Proof.
  Admitted.
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

  (* The final iteration's next accumulator [x_a] is the secant-line image of the
     current row, uniquely determined by the current-row coordinates and
     gradients via [q_mul_3_checks_gate]. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_mul_3 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hselector : ⟦ q_mul_3 ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_3_checks_gate q_mul_3 z x_a x_p y_p lambda_1 lambda_2 ⟧ ρ) :
      {|
        x_a_next := ⟦ Expression.Advice x_a Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice x_a Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice x_p Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_2 Rotation.cur ⟧ ρ).
  Proof.
  Admitted.
End QMul3Checks.
