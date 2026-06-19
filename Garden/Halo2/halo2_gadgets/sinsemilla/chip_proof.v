Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
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

  (* The running ordinate [y_a] at the start of a message (the derived
     combination of the current-row cells) is forced to twice the fixed seed
     [y_q] by the single "init_y_q_check" constraint of [initial_y_q_gate]. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_sinsemilla4 : Selector.t)
      (fixed_y_q : Fixed.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : ⟦ q_sinsemilla4 ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .initial_y_q_gate q_sinsemilla4 fixed_y_q x_a x_p lambda_1 lambda_2 ⟧ ρ) :
      {|
        y_a :=
          ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
              .y_a x_a x_p lambda_1 lambda_2 Rotation.cur ⟧ ρ;
      |} =
        output (⟦ Expression.Fixed fixed_y_q Rotation.cur ⟧ ρ).
  Proof.
    (* The single "init_y_q_check" constraint states [y_q * 2 = y_a_cur], which
       is exactly the (flipped) record equality to prove. *)
    unfold output, x_r, Garden.Halo2.halo2_gadgets.utilities_proof.square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    specialize (Hgate Hselector).
    f_equal.
    symmetry.
    exact Hgate.
  Qed.
End InitialYQ.

Module Sinsemilla.
  Record t : Set := {
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_cur x_p_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_a_next :=
      Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_2_cur -F
        x_r x_a_cur x_p_cur lambda_1_cur -F
        x_a_cur;
  |}.

  (* The next-row accumulator [x_a] is uniquely determined by the current row:
     the "Secant line" constraint of [sinsemilla_gate] gives
     [x_a_next = lambda_2^2 - x_r - x_a] directly (no division, no precondition),
     where [x_r = lambda_1^2 - x_a - x_p]. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_sinsemilla1 : Selector.t)
      (q_sinsemilla2 : Fixed.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : ⟦ q_sinsemilla1 ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧ ρ) :
      {|
        x_a_next := ⟦ Expression.Advice x_a Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice x_a Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice x_p Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice lambda_2 Rotation.cur ⟧ ρ).
  Proof.
    (* The "Secant line" constraint gives [lambda_2^2 = x_a_next + x_r + x_a]
       directly; solving for [x_a_next] needs no division and no precondition. *)
    unfold output, x_r, Garden.Halo2.halo2_gadgets.utilities_proof.square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as [Hc1 Hc2].
    specialize (Hc1 Hselector).
    clear Hc2.
    f_equal.
    field_solve.
  Qed.
End Sinsemilla.
