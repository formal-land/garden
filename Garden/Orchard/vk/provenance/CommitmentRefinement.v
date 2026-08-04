(** * End-to-end refinement of one executable VK commitment *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.AssemblyCheck.
Require Import Garden.Orchard.vk.provenance.Calibration.
Require Import Garden.Orchard.vk.provenance.Checks.
Require Import Garden.Orchard.vk.provenance.ColumnValues.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Domain.
Require Import Garden.Orchard.vk.provenance.DomainRefinement.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.FixedCalibration.
Require Import Garden.Orchard.vk.provenance.JacobianRefinement.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.MsmRefinement.
Require Import Garden.Orchard.vk.provenance.ModelColumns.
Require Import Garden.Orchard.vk.provenance.PermutationCalibration.
Require Import Garden.Orchard.vk.provenance.PinnedCorrect.
Require Import Garden.Orchard.vk.provenance.PinnedSpec.
Require Import Garden.Orchard.vk.provenance.PermutationValuesCorrect.
Require Import Garden.Orchard.vk.provenance.SrsDataView.
Require Import Garden.Orchard.vk.provenance.Sigma.

Import ListNotations.
Local Open Scope Z_scope.

Module VkCommitmentRefinement.
  Module JR := VkJacobianRefinement.

  Lemma coefficient_length
      (coefficients : list Prim63Words.words5) (values : list Z) :
    List.length values = 2048%nat ->
    VkMsmRefinement.scalar_values coefficients = VkMsm.intt values ->
    List.length coefficients = 2048%nat.
  Proof.
    intros Hvalues Hcoefficients.
    unfold VkMsmRefinement.scalar_values in Hcoefficients.
    apply (f_equal (@List.length Z)) in Hcoefficients.
    rewrite List.length_map, VkMsm.intt_length in Hcoefficients by
      exact Hvalues.
    exact Hcoefficients.
  Qed.

  Lemma coefficient_range
      (coefficients : list Prim63Words.words5) (values : list Z) :
    VkMsmRefinement.scalar_values coefficients = VkMsm.intt values ->
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (VkMsmRefinement.scalar_values coefficients).
  Proof.
    intros Hcoefficients.
    rewrite Hcoefficients.
    eapply List.Forall_impl; [|exact (VkMsm.intt_range values)].
    intros scalar Hscalar.
    assert (Hp : VkMsm.scalar_p < 2 ^ 256) by
      (vm_compute; reflexivity).
    lia.
  Qed.

  Theorem certificate_abstract_sound
      (kind : VkColumnKinds.column_kind) (index : nat)
      (coefficients : list Prim63Words.words5)
      (low high : VkProvenanceDataTypes.point_words)
      (values : list Z) :
    VkProvenanceChecks.commitment_certificate
      kind index coefficients low high ->
    VkSrsDataView.refinement ->
    VkMsm.params_well_formed ->
    List.length values = 2048%nat ->
    List.Forall (fun value => 0 <= value) values ->
    VkMsmRefinement.scalar_values coefficients = VkMsm.intt values ->
    VkMsm.commit_lagrange values = VkPinnedSpec.point kind index.
  Proof.
    intros Hcertificate Hsrs Hparams Hvalues_length Hvalues_nonnegative
      Hcoefficients.
    assert (Hcoefficient_length : List.length coefficients = 2048%nat).
    { now apply (coefficient_length coefficients values). }
    assert (Hcoefficient_range :
      List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
        (VkMsmRefinement.scalar_values coefficients)).
    { now apply (coefficient_range coefficients values). }
    pose proof (VkMsmRefinement.assemble_halves_commit_lagrange_sound
      coefficients values Hcoefficient_length Hsrs Hcoefficient_range
      Hparams Hvalues_length Hvalues_nonnegative Hcoefficients) as Hrepresents.
    pose proof (VkProvenanceChecks.commitment_certificate_sound
      kind index coefficients low high Hcertificate) as Hequal.
    pose proof (JR.equal_affine_true
      (VkProvenanceChecks.committed_point coefficients)
      (VkAssemblyCheck.pinned_affine kind index)
      (VkMsm.commit_lagrange values)
      Hrepresents (VkPinnedCorrect.pinned_affine_canonical kind index)
      Hequal) as Hpoint.
    rewrite VkPinnedCorrect.pinned_affine_denote in Hpoint.
    exact Hpoint.
  Qed.

  Theorem fixed_abstract_sound
      (domain_certificate : VkDomain.certificate)
      (srs_refinement : VkSrsDataView.refinement)
      (params_well_formed : VkMsm.params_well_formed)
      (index : nat) (coefficients : list Prim63Words.words5)
      (low high : VkProvenanceDataTypes.point_words) :
    VkProvenanceChecks.commitment_certificate VkColumnKinds.Fixed
      index coefficients low high ->
    VkMsm.commit_lagrange (VkCommitmentColumns.fixed_values index) =
      VkPinnedSpec.fixed_point index.
  Proof.
    intros Hcertificate.
    destruct Hcertificate as [Hcalibration Hlow Hhigh Hassembly].
    assert (Hcertificate :
      VkProvenanceChecks.commitment_certificate VkColumnKinds.Fixed
        index coefficients low high).
    { constructor; assumption. }
    unfold VkCalibration.check in Hcalibration.
    pose proof (VkDomainRefinement.coefficients_match_sound
      domain_certificate (VkModelColumns.fixed_evaluation index)
      coefficients Hcalibration) as Hcoefficients.
    rewrite <- VkCommitmentColumns.fixed_values_map in Hcoefficients.
    eapply certificate_abstract_sound; try exact Hcertificate;
      try exact srs_refinement; try exact params_well_formed.
    - apply VkCommitmentColumns.fixed_values_length.
    - apply VkCommitmentColumns.values_nonnegative.
    - exact Hcoefficients.
  Qed.

  Theorem permutation_abstract_sound
      (domain_certificate : VkDomain.certificate)
      (srs_refinement : VkSrsDataView.refinement)
      (params_well_formed : VkMsm.params_well_formed)
      (index : nat) (coefficients : list Prim63Words.words5)
      (low high : VkProvenanceDataTypes.point_words) :
    VkSigma.column_check index = true ->
    (index < VkSigma.width_nat)%nat ->
    VkProvenanceChecks.commitment_certificate VkColumnKinds.Permutation
      index coefficients low high ->
    VkMsm.commit_lagrange (VkCommitmentColumns.permutation_values index) =
      VkPinnedSpec.permutation_point index.
  Proof.
    intros Hsigma Hindex Hcertificate.
    destruct Hcertificate as [Hcalibration Hlow Hhigh Hassembly].
    assert (Hcertificate :
      VkProvenanceChecks.commitment_certificate VkColumnKinds.Permutation
        index coefficients low high).
    { constructor; assumption. }
    unfold VkCalibration.check in Hcalibration.
    pose proof (VkDomainRefinement.coefficients_match_field_sound
      domain_certificate (VkSigma.evaluation index) coefficients
      ltac:(intros row Hrow;
        apply VkPermutationValuesCorrect.evaluation_canonical
          with (domain_certificate := domain_certificate);
        try assumption;
        unfold VkIFFT.size_nat, VkSigma.rows_nat in Hrow |- *;
        exact Hrow)
      Hcalibration) as Hcoefficients.
    change
      VkMsmRefinement.scalar_values coefficients =
        VkMsm.intt
          (VkDomainRefinement.field_evaluation_values
            (VkSigma.evaluation index)) in Hcoefficients.
    rewrite (VkPermutationValuesCorrect.field_evaluation_values_exact
      domain_certificate index Hsigma Hindex) in Hcoefficients.
    eapply certificate_abstract_sound; try exact Hcertificate;
      try exact srs_refinement; try exact params_well_formed.
    - apply VkCommitmentColumns.permutation_values_length.
    - apply VkCommitmentColumns.values_nonnegative.
    - exact Hcoefficients.
  Qed.
End VkCommitmentRefinement.
