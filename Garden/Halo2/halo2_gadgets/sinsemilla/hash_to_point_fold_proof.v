(** * The row fold over the per-row rounds

    [SinsemillaHashFold.hash_to_point_rows_correct], consuming the two
    per-row round theorems ([SinsemillaHashRound.round_correct] /
    [SinsemillaHashRoundFinal.round_correct_final]) and the word-list algebra
    of [hash_to_point_proof.v] (module [SinsemillaHash], imported here). *)

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
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_round_final_proof.

Module SinsemillaHashFold.
  Import SinsemillaHash.

  (** The row fold (generic over the piece schedule): [n] active
      rows with the uniform [q_s3 = 0 / final q_s3 = 2] schedule fold the
      per-row [round] into [sinsemilla_hash_to_point], provided the message
      is nondegenerate for [Q].  The output point is read off the
      [(x_a, lambda_1)] cells of row [n] — the cells
      [synthesize_hash_to_point_region] returns. *)
  Theorem hash_to_point_rows_correct
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (q_sinsemilla1 : Selector.t) (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (n : nat) (Hn : (0 < n)%nat)
      (Q : Point.t)
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hsel : forall j : nat, (j < n)%nat ->
        Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, Z.of_nat j) = 1)
      (Hgate : forall j : nat, (j < n)%nat ->
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧
          (region, Z.of_nat j))
      (Hlookup : forall j : nat, (j < n)%nat ->
        eval_lookup_argument Γ (region, Z.of_nat j) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2))
      (Hq3 : forall j : nat, (S j < n)%nat ->
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q_sinsemilla2 ⟧
          (region, Z.of_nat j) = 0)
      (Hq3_final :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q_sinsemilla2 ⟧
          (region, Z.of_nat (n - 1)) = 2)
      (Hinit : acc_at Γ x_a x_p lambda_1 lambda_2 region 0 = Q)
      (Hnondeg :
        nondegenerate Q (hash_words Γ q_sinsemilla2 bits region n)) :
    {|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, Z.of_nat n);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, Z.of_nat n);
    |} =
      SinsemillaSpec.sinsemilla_hash_to_point Q
        (hash_words Γ q_sinsemilla2 bits region n).
  Proof.
    (* Invariant: below the final row, the accumulator at row [k] is the fold
       of the first [k] words. *)
    assert (Hacc : forall k : nat, (k < n)%nat ->
      acc_at Γ x_a x_p lambda_1 lambda_2 region (Z.of_nat k) =
        SinsemillaSpec.sinsemilla_hash_to_point Q
          (hash_words Γ q_sinsemilla2 bits region k)).
    { induction k as [| k IH]; intros Hk.
      - exact Hinit.
      - assert (Hk' : (k < n)%nat) by lia.
        specialize (IH Hk').
        pose proof (Hnondeg k) as Hnd.
        rewrite hash_words_length in Hnd.
        specialize (Hnd Hk').
        cbv zeta in Hnd.
        rewrite hash_words_firstn in Hnd by lia.
        rewrite hash_words_nth in Hnd by exact Hk'.
        destruct Hnd as [Hnd1 Hnd2].
        rewrite <- IH in Hnd1, Hnd2.
        pose proof (SinsemillaHashRound.round_correct Γ region (Z.of_nat k) q_sinsemilla1
          q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
          (Hsel k Hk') (Hgate k Hk') Hload (Hlookup k Hk')
          (Hq3 k Hk) Hnd1 Hnd2) as Hstep.
        replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
        rewrite Hstep, IH.
        rewrite hash_words_S.
        now rewrite SinsemillaSpec.sinsemilla_hash_to_point_app. }
    (* Final row: the [q_s3 = 2] round variant produces the output cells. *)
    destruct n as [| m]; [lia |].
    assert (Hm : (m < S m)%nat) by lia.
    pose proof (Hnondeg m) as Hnd.
    rewrite hash_words_length in Hnd.
    specialize (Hnd Hm).
    cbv zeta in Hnd.
    rewrite hash_words_firstn in Hnd by lia.
    rewrite hash_words_nth in Hnd by exact Hm.
    destruct Hnd as [Hnd1 Hnd2].
    rewrite <- (Hacc m Hm) in Hnd1, Hnd2.
    replace (Z.of_nat (S m - 1)) with (Z.of_nat m) in Hq3_final by lia.
    pose proof (SinsemillaHashRoundFinal.round_correct_final Γ region (Z.of_nat m) q_sinsemilla1
      q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      (Hsel m Hm) (Hgate m Hm) Hload (Hlookup m Hm)
      Hq3_final Hnd1 Hnd2) as Hstep.
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    rewrite Hstep, (Hacc m Hm).
    rewrite hash_words_S.
    now rewrite SinsemillaSpec.sinsemilla_hash_to_point_app.
  Qed.
End SinsemillaHashFold.
