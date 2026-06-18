Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

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

  (* The next-row values constrained by the overflow-check gate are uniquely
     determined by the witnessed [alpha] and [k_254]: [s] is recovered from the
     [s_check] constraint and [z_0] from the [recovery] constraint. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QMulOverflow ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.overflow_checks_gate ⟧
          ρ) :
      {|
        s := ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ ρ;
        z_0 := ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.prev ⟧ ρ).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from Primes.pallas_p]
      cbn in *.
    destruct Hgate as (h1 & h2 & _ & _ & _).
    specialize (h1 Hselector).
    specialize (h2 Hselector).
    (* [s_check] gives [s] up to the identity [2^124 * 2^6 = 2^130]. *)
    assert (Hpow : UnOp.from 21267647932558653966460912964485513216 *F UnOp.from 64 =
        UnOp.from 1361129467683753853853498429727072845824).
    { unfold BinOp.mul, UnOp.from.
      now rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r. }
    (* [recovery] gives [z_0] by moving [alpha] back across the subtraction. *)
    assert (add_sub_cancel : forall z alpha : Z, alpha +F (z -F alpha) = UnOp.from z).
    { intros z alpha. unfold BinOp.add, BinOp.sub, UnOp.from.
      rewrite Zplus_mod_idemp_r. f_equal. ring. }
    f_equal.
    - rewrite h1. now rewrite Hpow.
    - now rewrite <- h2, add_sub_cancel, FieldRewrite.from_from.
  Qed.
End OverflowChecks.
