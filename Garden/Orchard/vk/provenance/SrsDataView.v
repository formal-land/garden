(** * Aggregate executable view of the generated Orchard SRS

    The generic checker in [Srs] intentionally does not import this module:
    an individual provenance certificate can load one 64-entry shard instead
    of retaining all 2,048 generated entries.  Commitment computation is the
    consumer that needs the aggregate [g_array]. *)

From Corelib Require Import PrimArray.
From Stdlib Require Import Lists.List Bool.Bool.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinatesAll.

Module VkSrsDataView.
  Import VkProvenanceDataTypes.

  Definition affine_of_words (coordinates : affine_words)
      : VkJacobian.affine :=
    {| VkJacobian.affine_x := coordinates.(x_words);
       VkJacobian.affine_y := coordinates.(y_words) |}.

  Definition g : list VkJacobian.affine :=
    List.map affine_of_words VkSrsCoordinatesAll.g.
  Definition w : VkJacobian.affine :=
    affine_of_words VkSrsCoordinatesAll.w.
  Definition u : VkJacobian.affine :=
    affine_of_words VkSrsCoordinatesAll.u.

  Definition g_array : PrimArray.array VkJacobian.affine :=
    VkJacobian.array_of_list
      {| VkJacobian.affine_x := PallasQ.zero;
         VkJacobian.affine_y := PallasQ.zero |}
      g.
End VkSrsDataView.
