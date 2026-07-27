(** * The point-level Sinsemilla round, final row ([q_s3 = 2])

    [SinsemillaHashRoundFinal.round_correct_final], the final-row consumer of
    the shared common core [SinsemillaHashRound.round_pins]
    ([hash_to_point_round_proof.v]); the shared definitions live in
    [hash_to_point_proof.v] (module [SinsemillaHash], imported here). *)

Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_round_proof.

Module SinsemillaHashRoundFinal.
  Import SinsemillaHash.

  (** The [q_s3 = 2] "y check" endgame as a field identity over named cell
      values: the collapsed constraint
      [4 lambda_2 (x_a - x_a') = 2 y_a + 4 lambda_1'] only determines the
      quadrupled next-row [lambda_1'] cell, so the target ordinate equality
      is quadrupled and the invertible factor [4] cancelled.
      [(l1 + l2) (xa - xr)] is the current-row [y_a] combination, halved by
      [two_inv] into the actual accumulator ordinate. *)
  Lemma y_check_two (l1 l2 l1' xa xa' xr : Z)
      (Hl1'_red : UnOp.from l1' = l1')
      (Hy : l2 *F UnOp.from 4 *F (xa -F xa') =
        (l1 +F l2) *F (xa -F xr) *F UnOp.from 2 +F UnOp.from 4 *F l1') :
    l1' =
      l2 *F (xr -F xa') -F
        (l1 *F (xa -F xr) -F
          (l1 +F l2) *F (xa -F xr) *F
            Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv).
  Proof.
    set (Y := (l1 +F l2) *F (xa -F xr)) in *.
    set (tinv := constants.two_inv) in *.
    set (yv := Y *F tinv) in *.
    assert (HY_red : UnOp.from Y = Y) by (unfold Y; apply from_mul_reduced).
    assert (H2yv : UnOp.from 2 *F yv = Y).
    { unfold yv, tinv. rewrite double_half. apply HY_red. }
    assert (HYexp : Y = l1 *F (xa -F xr) +F l2 *F (xa -F xr)).
    { unfold Y, BinOp.mul, BinOp.add.
      rewrite Zmult_mod_idemp_l, <- Zplus_mod.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      f_equal; ring. }
    rewrite (field_mul_comm l2 (UnOp.from 4)) in Hy.
    rewrite (field_mul_assoc (UnOp.from 4) l2 (xa -F xa')) in Hy.
    rewrite (FieldRewrite.mul_from_left 4 (l2 *F (xa -F xa'))) in Hy.
    rewrite (FieldRewrite.mul_from_right Y 2) in Hy.
    rewrite (FieldRewrite.mul_from_left 4 l1') in Hy.
    rewrite (field_mul_sub_distr l2 xa xa') in Hy.
    rewrite (field_mul_sub_distr l1 xa xr),
      (field_mul_sub_distr l2 xa xr) in HYexp.
    assert (H4ne : UnOp.from (UnOp.from 4) <> 0).
    { rewrite FieldRewrite.from_from.
      unfold UnOp.from, Primes.pallas_p, Primes.t_p. lia. }
    assert (Hquad : l1' *F UnOp.from 4 =
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)) *F UnOp.from 4).
    { rewrite (field_mul_sub_distr l2 xr xa'), (field_mul_sub_distr l1 xa xr).
      rewrite !(FieldRewrite.mul_from_right _ 4).
      clear - Hy H2yv HYexp. field_solve. }
    pose proof (field_mul_cancel_r l1'
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)) (UnOp.from 4)
        H4ne Hquad)
      as Hyfin0.
    exact (eq_trans (eq_sym Hl1'_red)
      (eq_trans Hyfin0 (from_sub_reduced _ _))).
  Qed.

  (** The final-row variant ([q_s3 = 2], i.e. [q_s2 = 2] on the last word of
      the message): the "y check" then pins the *witnessed* [lambda_1] at the
      next row directly to the accumulator ordinate, so the output point is
      read off the [(x_a, lambda_1)] cells of row [row + 1] — the pair the
      hash-to-point synthesis returns. Same nondegeneracy preconditions as
      [round_correct]. *)
  Theorem round_correct_final
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (row : Z)
      (q_sinsemilla1 : Selector.t) (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hactive : Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, row) = 1)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧
          (region, row))
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hlookup :
        eval_lookup_argument Γ (region, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2))
      (Hq_s3 :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q_sinsemilla2 ⟧
          (region, row) = 2)
      (Hdeg1 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (SinsemillaSpec.generator
          (word_at Γ q_sinsemilla2 bits region row)))
      (Hdeg2 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (EccSpec.point_add_incomplete
          (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
          (SinsemillaSpec.generator
            (word_at Γ q_sinsemilla2 bits region row)))) :
    {|
      Point.x := Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row + 1);
      Point.y := Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row + 1);
    |} =
      SinsemillaSpec.round
        (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
        (word_at Γ q_sinsemilla2 bits region row).
  Proof.
    (* [round_pins] pins the abscissa and expresses the round ordinate in
       cell terms; the collapsed [q_s3 = 2] "y check" then hands the
       quadrupled next-row [lambda_1] cell to [y_check_two]. *)
    pose proof (SinsemillaHashRound.round_pins Γ region row q_sinsemilla1
        q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
        Hactive Hgate Hload Hlookup Hdeg1 Hdeg2)
      as (_ & _ & Hxpin & Hypin).
    clear Hload Hlookup Hdeg1 Hdeg2.
    apply SinsemillaHashRound.point_ext; [exact Hxpin |].
    rewrite Hypin.
    clear Hxpin Hypin.
    unfold acc_at.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv]
      cbn in Hactive, Hgate, Hq_s3 |- *.
    rewrite (SinsemillaHashRound.rotated_row_next row).
    destruct Hgate as [_ Hy].
    specialize (Hy (SinsemillaHashRound.one_nonzero _ Hactive)).
    (* On a [q_s3 = 2] row the "y check" collapses to
       [4 lambda_2 (x_a - x_a') = 2 y_a + 4 lambda_1'], the next-row [y_a]
       combination dropping out entirely. *)
    rewrite Hq_s3 in Hy.
    replace (UnOp.from 2 -F 2) with (0 : Z) in Hy by (vm_compute; reflexivity).
    rewrite FieldRewrite.mul_zero_left in Hy.
    rewrite FieldRewrite.add_zero_right in Hy.
    rewrite FieldRewrite.add_from_left in Hy.
    replace ((2 : Z) *F UnOp.from 2) with (UnOp.from 4) in Hy
      by (vm_compute; reflexivity).
    exact (y_check_two _ _ _ _ _ _ (FieldRewrite.from_from _) Hy).
  Qed.
End SinsemillaHashRoundFinal.
