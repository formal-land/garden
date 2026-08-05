(** * The two independently compiled halves of a width-8 Pippenger MSM *)

From Corelib Require Import PrimArray.
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Module VkMsmChecks.
  Definition affine (value : VkProvenanceDataTypes.affine_words)
      : VkJacobian.affine := VkSrsDataView.affine_of_words value.

  Definition point_of_words (value : VkProvenanceDataTypes.point_words)
      : VkJacobian.point :=
    {| VkJacobian.x := value.(VkProvenanceDataTypes.jacobian_x_words);
       VkJacobian.y := value.(VkProvenanceDataTypes.jacobian_y_words);
       VkJacobian.z := value.(VkProvenanceDataTypes.jacobian_z_words) |}.

  Definition scalar_array (coefficients : list Prim63Words.words5)
      : PrimArray.array Prim63Words.words5 :=
    VkJacobian.array_of_list Prim63Words.zero5 coefficients.

  Definition low_msm (coefficients : list Prim63Words.words5)
      : VkJacobian.point :=
    VkJacobian.low_half (scalar_array coefficients) VkSrsDataView.g_array.

  Definition high_msm (coefficients : list Prim63Words.words5)
      : VkJacobian.point :=
    VkJacobian.high_half (scalar_array coefficients) VkSrsDataView.g_array.

  Definition low_exact (coefficients : list Prim63Words.words5)
      (expected : VkProvenanceDataTypes.point_words) : Prop :=
    low_msm coefficients = point_of_words expected.

  Definition high_exact (coefficients : list Prim63Words.words5)
      (expected : VkProvenanceDataTypes.point_words) : Prop :=
    high_msm coefficients = point_of_words expected.

  Definition low_check (coefficients : list Prim63Words.words5)
      (expected : VkProvenanceDataTypes.affine_words) : bool :=
    (List.length coefficients =? 2048)%nat
      && VkJacobian.equal_affine (low_msm coefficients) (affine expected).

  Definition high_check (coefficients : list Prim63Words.words5)
      (expected : VkProvenanceDataTypes.affine_words) : bool :=
    (List.length coefficients =? 2048)%nat
      && VkJacobian.equal_affine (high_msm coefficients) (affine expected).
End VkMsmChecks.
