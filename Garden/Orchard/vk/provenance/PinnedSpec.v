(** * Abstract Vesta view of the pinned Orchard commitment coordinates *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Orchard.vk.data.
Require Import Garden.Orchard.vk.provenance.Kinds.

Module VkPinnedSpec.
  Definition pair (kind : VkColumnKinds.column_kind) (index : nat) : Z * Z :=
    match kind with
    | VkColumnKinds.Fixed =>
        List.nth index VkPinnedData.fixed_commitments (0, 0)
    | VkColumnKinds.Permutation =>
        List.nth index VkPinnedData.permutation_commitments (0, 0)
    end.

  Definition point (kind : VkColumnKinds.column_kind) (index : nat)
      : Vesta.point :=
    let '(x, y) := pair kind index in Vesta.affine x y.

  Definition fixed_point (index : nat) : Vesta.point :=
    point VkColumnKinds.Fixed index.

  Definition permutation_point (index : nat) : Vesta.point :=
    point VkColumnKinds.Permutation index.
End VkPinnedSpec.
