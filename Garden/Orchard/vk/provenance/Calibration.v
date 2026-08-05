(** * Uniform view of the two inverse-FFT calibration checkers *)

From Stdlib Require Import Lists.List.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.FixedCalibration.
Require Import Garden.Orchard.vk.provenance.PermutationCalibration.

Module VkCalibration.
  Definition check (kind : VkColumnKinds.column_kind) (index : nat)
      (coefficients : list Prim63Words.words5) : bool :=
    match kind with
    | VkColumnKinds.Fixed => VkFixedCalibration.check index coefficients
    | VkColumnKinds.Permutation =>
        VkPermutationCalibration.check index coefficients
    end.
End VkCalibration.
