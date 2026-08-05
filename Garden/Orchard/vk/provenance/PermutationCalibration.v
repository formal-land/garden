(** * Inverse-FFT calibration for one model-derived permutation column *)

From Stdlib Require Import Lists.List.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.Sigma.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.

Module VkPermutationCalibration.
  Definition check (index : nat) (coefficients : list Prim63Words.words5)
      : bool :=
    VkIFFT.coefficients_match_field
      VkDomainData.bit_reversed_array
      VkDomainData.inverse_roots_array
      VkDomainData.n_inverse
      (VkSigma.evaluation index) coefficients.
End VkPermutationCalibration.
