(** * Concrete refinement of the optimized Orchard instance commitment

    This proof-only module instantiates the evaluator's generic FFT and SRS
    obligations with the checked data generated for the deployed Orchard
    verifying key.  Keeping these certificates outside [PostNu6_3] prevents
    their large proof-data dependency graph from entering extracted code. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.Orchard.Verifier.PostNu6_3.
Require Import Garden.Orchard.Verifier.Eval.InstanceCommitment.
Require Import Garden.Orchard.vk.parameters.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Domain.
Require Import Garden.Orchard.vk.provenance.SrsDataView.
Require Import Garden.Orchard.vk.provenance.generated.certificates.Domain.
Require Import Garden.Orchard.vk.provenance.generated.certificates.Srs.

Module OrchardInstanceCommitmentAssurance.

  Definition concrete_domain_certificate : VkDomain.certificate :=
    VkDomainCertificate.checked.

  Definition concrete_srs_refinement : VkSrsDataView.refinement :=
    VkSrsCertificate.data_view_refinement VkSrsCertificate.checked.

  Definition concrete_params_well_formed : VkMsm.params_well_formed :=
    VkSrsCertificate.params_well_formed VkSrsCertificate.checked.

  Corollary evaluate_checked_refines_concrete (values : list Z) :
    OrchardInstanceCommitmentEval.preconditionsb values = true ->
    OrchardInstanceCommitmentEval.evaluate_checked values =
      Some (OrchardInstanceCommitmentEval.reference_commitment values).
  Proof.
    exact (OrchardInstanceCommitmentEval.evaluate_checked_refines
      concrete_domain_certificate concrete_srs_refinement
      concrete_params_well_formed values).
  Qed.

  Lemma reference_padded_eq (values : list Z) :
    OrchardInstanceCommitmentEval.reference_commitment
        (OrchardPostNu63.zero_pad_instance values) =
      OrchardPostNu63.instance_commitment_reference values.
  Proof.
    unfold OrchardPostNu63.instance_commitment_reference.
    reflexivity.
  Qed.

  Lemma preconditionsb_zero_pad (values : list Z) :
    List.length values = OrchardPostNu63.action_width ->
    List.Forall
      (fun value => 0 <= value < Primes.pallas_p) values ->
    OrchardInstanceCommitmentEval.preconditionsb
      (OrchardPostNu63.zero_pad_instance values) = true.
  Proof.
    intros Hlength Hcanonical.
    unfold OrchardInstanceCommitmentEval.preconditionsb,
      OrchardPostNu63.zero_pad_instance.
    assert (Horiginal :
      List.forallb OrchardInstanceCommitmentEval.scalar_canonicalb values =
        true).
    { rewrite List.forallb_forall.
      intros value Hin.
      unfold OrchardInstanceCommitmentEval.scalar_canonicalb.
      pose proof
        (proj1 (List.Forall_forall _ _) Hcanonical value Hin) as Hrange.
      rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt.
      exact Hrange. }
    assert (Hpadding :
      List.forallb OrchardInstanceCommitmentEval.scalar_canonicalb
        (List.repeat 0
          (OrchardVkParameters.n - List.length values)) = true).
    { induction
        (OrchardVkParameters.n - List.length values)%nat
        as [|remaining IH]; cbn; [reflexivity | exact IH]. }
    assert (Hlengthb :
      Nat.eqb
        (List.length
          (values ++ List.repeat 0
            (OrchardVkParameters.n - List.length values)))
        OrchardInstanceCommitmentEval.vector_size = true).
    { rewrite Nat.eqb_eq, List.length_app, List.repeat_length.
      change
        (List.length values + (2048 - List.length values) = 2048)%nat.
      rewrite Hlength. reflexivity. }
    rewrite Hlengthb, List.forallb_app, Horiginal, Hpadding.
    reflexivity.
  Qed.

  (** Every validated Orchard action takes the primitive branch and produces
      exactly the Rust-shaped reference commitment.  Inputs outside these
      premises take the reference fallback directly by definition. *)
  Theorem instance_commitment_refines (values : list Z) :
    List.length values = OrchardPostNu63.action_width ->
    List.Forall
      (fun value => 0 <= value < Primes.pallas_p) values ->
    OrchardPostNu63.instance_commitment values =
      OrchardPostNu63.instance_commitment_reference values.
  Proof.
    intros Hlength Hcanonical.
    pose proof (preconditionsb_zero_pad values Hlength Hcanonical)
      as Hchecked.
    unfold OrchardPostNu63.instance_commitment.
    rewrite (evaluate_checked_refines_concrete
      (OrchardPostNu63.zero_pad_instance values) Hchecked).
    exact (reference_padded_eq values).
  Qed.

End OrchardInstanceCommitmentAssurance.
