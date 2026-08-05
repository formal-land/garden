(** * Refinement of primitive sigma evaluations to public column values

    The executable permutation calibration reads a packed target cell and
    multiplies cached powers of [delta] and [omega].  This module connects
    those caches, through their kernel certificates, to the direct
    [OrchardCompiled.orchard_sigma] definition used by [commit_lagrange]. *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Orchard.vk.provenance.ColumnValues.
Require Import Garden.Orchard.vk.provenance.Domain.
Require Import Garden.Orchard.vk.provenance.DomainRefinement.
Require Import Garden.Orchard.vk.provenance.Sigma.
Require Import Garden.Orchard.vk.provenance.SigmaRefinement.

Import ListNotations.
Local Open Scope Z_scope.

Module VkPermutationValuesCorrect.
  Module F := PallasP.
  Module FR := PallasPRefinement.

  Theorem evaluation_refines
      (domain_certificate : VkDomain.certificate)
      (column row : nat) :
    VkSigma.column_check column = true ->
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    F.canonical (VkSigma.evaluation column row) /\
    F.denote (VkSigma.evaluation column row) =
      VkCommitmentColumns.permutation_evaluation column row.
  Proof.
    intros Hcheck Hcolumn Hrow.
    pose proof (VkSigmaRefinement.model_target_bounds
      column row Hcolumn Hrow) as Htarget_bounds.
    destruct (VkSigmaRefinement.model_target column row)
      as [target_column target_row] eqn:Htarget.
    cbn [fst snd] in Htarget_bounds.
    destruct Htarget_bounds as [Htarget_column Htarget_row].
    pose proof (VkSigmaRefinement.pack_cell_decode
      (target_column, target_row) Htarget_column Htarget_row)
      as [Hpacked_column Hpacked_row].
    unfold VkSigma.evaluation.
    rewrite (VkSigmaRefinement.packed_target_refines_model
      column row Hcheck Hcolumn Hrow).
    rewrite Htarget.
    cbn [fst snd].
    cbn [fst snd] in Hpacked_column, Hpacked_row.
    rewrite Hpacked_column, Hpacked_row.
    fold VkDomain.delta_powers_array VkDomain.omega_powers_array.
    split.
    - apply FR.mul_canonical.
      apply VkDomainRefinement.omega_powers_canonical;
        assumption.
    - rewrite FR.mul_denote by
        (apply VkDomainRefinement.omega_powers_canonical; assumption).
      rewrite (VkDomainRefinement.delta_powers_denote
        domain_certificate target_column Htarget_column).
      rewrite (VkDomainRefinement.omega_powers_denote
        domain_certificate target_row Htarget_row).
      change PallasPConfig.modulus_Z with Primes.pallas_p.
      unfold VkCommitmentColumns.permutation_evaluation,
        VkCommitmentColumns.permutation_target.
      rewrite <- (VkSigmaRefinement.model_target_is_perm
        column row Hcolumn Hrow), Htarget.
      cbn [fst snd].
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by
        (pose proof Primes.pallas_p_pos; lia).
      reflexivity.
  Qed.

  Corollary evaluation_canonical
      (domain_certificate : VkDomain.certificate)
      (column row : nat) :
    VkSigma.column_check column = true ->
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    F.canonical (VkSigma.evaluation column row).
  Proof.
    intros Hcheck Hcolumn Hrow.
    exact (proj1 (evaluation_refines domain_certificate column row
      Hcheck Hcolumn Hrow)).
  Qed.

  Corollary evaluation_denote
      (domain_certificate : VkDomain.certificate)
      (column row : nat) :
    VkSigma.column_check column = true ->
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    F.denote (VkSigma.evaluation column row) =
      VkCommitmentColumns.permutation_evaluation column row.
  Proof.
    intros Hcheck Hcolumn Hrow.
    exact (proj2 (evaluation_refines domain_certificate column row
      Hcheck Hcolumn Hrow)).
  Qed.

  Theorem field_evaluation_values_exact
      (domain_certificate : VkDomain.certificate)
      (column : nat) :
    VkSigma.column_check column = true ->
    (column < VkSigma.width_nat)%nat ->
    VkDomainRefinement.field_evaluation_values
        (VkSigma.evaluation column) =
      VkCommitmentColumns.permutation_values column.
  Proof.
    intros Hcheck Hcolumn.
    unfold VkDomainRefinement.field_evaluation_values,
      VkDomainRefinement.tabulate,
      VkCommitmentColumns.permutation_values.
    apply List.map_ext_in.
    intros row Hrow.
    apply List.in_seq in Hrow.
    destruct Hrow as [_ Hrow].
    apply evaluation_denote; try assumption.
  Qed.
End VkPermutationValuesCorrect.
