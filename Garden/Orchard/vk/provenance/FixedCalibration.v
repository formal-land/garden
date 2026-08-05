(** * Inverse-FFT calibration for one model-derived fixed column *)

From Stdlib Require Import Lists.List.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.ModelColumns.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.

Module VkFixedCalibration.
  Definition check (index : nat) (coefficients : list Prim63Words.words5)
      : bool :=
    VkIFFT.coefficients_match
      VkDomainData.bit_reversed_array
      VkDomainData.inverse_roots_array
      VkDomainData.n_inverse
      (VkModelColumns.fixed_evaluation index) coefficients.
End VkFixedCalibration.
