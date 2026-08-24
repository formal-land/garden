(** * Concrete SRS assurance boundary for the Orchard verifier

    The executable well-formedness check lives in the lightweight
    [Garden.Orchard.Verifier.Eval.Checked] module.  This module intentionally
    sits outside the executable verifier dependency graph: it imports the
    generated SRS certificate and instantiates the generic refinement theorem
    with the pinned Orchard data. *)

Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Eval.Commitment.
Require Import Garden.Orchard.Verifier.Eval.Checked.
Require Import Garden.Orchard.vk.provenance.SrsDataView.
Require Import Garden.Orchard.vk.provenance.generated.certificates.Srs.

Module OrchardVerifierAssurance.
  Module Checked := OrchardVerifierChecked.
  Module Reference := CommitmentVerifier.

  (** The concrete generated certificate pins the evaluator's primitive-word
      SRS view to the reference verifier's [VkMsm] parameter lists. *)
  Definition concrete_srs_refinement : VkSrsDataView.refinement :=
    VkSrsCertificate.data_view_refinement VkSrsCertificate.checked.

  Corollary eval_srs_refines_concrete_reference (state : Reference.msm) :
    Checked.final_terms_well_formedb state = true ->
    CommitmentEval.eval_srs state =
      Reference.eval CommitmentEval.reference_srs_parameters state.
  Proof.
    apply Checked.eval_srs_refines_reference_srs.
    exact concrete_srs_refinement.
  Qed.

  Theorem eval_srs_checked_refines (state : Reference.msm) :
    Checked.eval_srs_checked state = Checked.eval_reference_checked state.
  Proof.
    apply Checked.eval_srs_checked_refines.
    exact concrete_srs_refinement.
  Qed.
End OrchardVerifierAssurance.
