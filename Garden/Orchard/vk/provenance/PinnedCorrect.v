(** * Semantic view of the primitive pinned commitment coordinates *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Orchard.vk.provenance.AssemblyCheck.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.JacobianRefinement.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.PinnedSpec.

Local Open Scope Z_scope.

Module VkPinnedCorrect.
  Theorem pinned_affine_canonical
      (kind : VkColumnKinds.column_kind) (index : nat) :
    VkJacobianRefinement.affine_canonical
      (VkAssemblyCheck.pinned_affine kind index).
  Proof.
    unfold VkJacobianRefinement.affine_canonical,
      VkAssemblyCheck.pinned_affine.
    destruct (VkAssemblyCheck.pinned_pair kind index) as [x y].
    cbn [VkJacobian.affine_x VkJacobian.affine_y].
    split; apply PallasQFacts.from_Z_canonical.
  Qed.

  Theorem pinned_affine_denote
      (kind : VkColumnKinds.column_kind) (index : nat) :
    VkJacobianRefinement.affine_denote
        (VkAssemblyCheck.pinned_affine kind index) =
      VkPinnedSpec.point kind index.
  Proof.
    destruct kind;
      unfold VkJacobianRefinement.affine_denote,
        VkAssemblyCheck.pinned_affine, VkAssemblyCheck.pinned_pair,
        VkPinnedSpec.point, VkPinnedSpec.pair;
      destruct (List.nth index _ (0, 0)) as [x y];
      cbn [VkJacobian.affine_x VkJacobian.affine_y];
      rewrite !PallasQFacts.from_Z_denote;
      unfold Vesta.affine, UnOp.from, Vesta.vesta_p;
      rewrite !Z.mod_mod by
        (pose proof (@prime_range Primes.pallas_q Primes.PallasQIsPrime);
         lia);
      reflexivity.
  Qed.
End VkPinnedCorrect.
