(** * Reassemble split MSMs, add the default blinding generator, and
    compare with the deployed verifying-key coordinate. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Orchard.vk.data.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.MsmChecks.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Local Open Scope Z_scope.

Module VkAssemblyCheck.
  Definition affine (value : VkProvenanceDataTypes.affine_words)
      : VkJacobian.affine := VkSrsDataView.affine_of_words value.

  Definition pinned_pair (kind : VkColumnKinds.column_kind) (index : nat)
      : Z * Z :=
    match kind with
    | VkColumnKinds.Fixed =>
        List.nth index VkPinnedData.fixed_commitments (0, 0)
    | VkColumnKinds.Permutation =>
        List.nth index VkPinnedData.permutation_commitments (0, 0)
    end.

  Definition pinned_affine (kind : VkColumnKinds.column_kind) (index : nat)
      : VkJacobian.affine :=
    let '(x, y) := pinned_pair kind index in
    {| VkJacobian.affine_x := PallasQ.from_Z x;
       VkJacobian.affine_y := PallasQ.from_Z y |}.

  Definition check (kind : VkColumnKinds.column_kind) (index : nat)
      (low high : VkProvenanceDataTypes.point_words) : bool :=
    VkJacobian.equal_affine
      (VkJacobian.assemble_halves
        (VkMsmChecks.point_of_words low)
        (VkMsmChecks.point_of_words high) VkSrsDataView.w)
      (pinned_affine kind index).
End VkAssemblyCheck.
