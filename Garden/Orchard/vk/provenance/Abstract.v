(** * Public mathematical statement of Orchard VK commitment provenance *)

From Stdlib Require Import Arith.PeanoNat.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.ColumnValues.
Require Import Garden.Orchard.vk.provenance.PinnedSpec.

Module OrchardVkAbstract.
  Definition fixed_commitment (index : nat) : VkMsm.point :=
    VkMsm.commit_lagrange (VkCommitmentColumns.fixed_values index).

  Definition permutation_commitment (index : nat) : VkMsm.point :=
    VkMsm.commit_lagrange (VkCommitmentColumns.permutation_values index).

  (** Unlike the executable aggregate, this statement is phrased entirely
      through the mathematical group-IFFT definition of Halo2
      [commit_lagrange]. *)
  Record certificate : Prop := {
    params_new_11_well_formed : VkMsm.params_well_formed;
    fixed_commitments_refined :
      forall index, (index < 29)%nat ->
        fixed_commitment index = VkPinnedSpec.fixed_point index;
    permutation_commitments_refined :
      forall index, (index < 15)%nat ->
        permutation_commitment index =
          VkPinnedSpec.permutation_point index;
  }.
End OrchardVkAbstract.
