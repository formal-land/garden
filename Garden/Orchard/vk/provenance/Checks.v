(** * Shard-sized executable checkers for the 44 VK commitments *)

From Stdlib Require Import Lists.List.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.Calibration.
Require Import Garden.Orchard.vk.provenance.MsmChecks.
Require Import Garden.Orchard.vk.provenance.AssemblyCheck.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Module VkProvenanceChecks.
  Record commitment_certificate (kind : VkColumnKinds.column_kind)
      (index : nat) (coefficients : list Prim63Words.words5)
      (low high : VkProvenanceDataTypes.point_words) : Prop := {
    calibration_checked : VkCalibration.check kind index coefficients = true;
    low_checked : VkMsmChecks.low_exact coefficients low;
    high_checked : VkMsmChecks.high_exact coefficients high;
    assembly_checked : VkAssemblyCheck.check kind index low high = true;
  }.

  Definition committed_point (coefficients : list Prim63Words.words5)
      : VkJacobian.point :=
    VkJacobian.assemble_halves
      (VkMsmChecks.low_msm coefficients)
      (VkMsmChecks.high_msm coefficients) VkSrsDataView.w.

  (** This is the executable commitment equation.  The expensive
      halves are proved equal to exact generated Jacobian representatives in
      separate leaves; rewriting them makes the final assembly proof cheap. *)
  Theorem commitment_certificate_sound
      (kind : VkColumnKinds.column_kind) (index : nat)
      (coefficients : list Prim63Words.words5)
      (low high : VkProvenanceDataTypes.point_words) :
    commitment_certificate kind index coefficients low high ->
    VkJacobian.equal_affine (committed_point coefficients)
      (VkAssemblyCheck.pinned_affine kind index) = true.
  Proof.
    intros certificate.
    destruct certificate as [_ Hlow Hhigh Hassembly].
    unfold committed_point.
    unfold VkAssemblyCheck.check in Hassembly.
    unfold VkMsmChecks.low_exact in Hlow.
    unfold VkMsmChecks.high_exact in Hhigh.
    now rewrite Hlow, Hhigh.
  Qed.

End VkProvenanceChecks.
