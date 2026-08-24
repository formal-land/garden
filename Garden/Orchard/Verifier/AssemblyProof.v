(** * Fixed Post-NU6.3 single-proof expression stream

    This file turns the values read by [Reference.read_plonk_prefix] into the
    Gate, permutation, and lookup constraints are concatenated per proof in
    the same order as the Rust verifier. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Permutation.
Require Import Garden.Halo2.Verifier.Lookup.
Require Import Garden.Halo2.Verifier.Vanishing.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Reference.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.Verifier.PostNu6_3.
Require Import Garden.Orchard.Verifier.AssemblyData.
Require Import Garden.Orchard.Verifier.AssemblyPermutation.
Require Import Garden.Orchard.Verifier.AssemblyLookup.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Definition combine_expression_options
    (gates permutation lookups : option (list VerifierField.t)) :
    option (list VerifierField.t) :=
  match gates with
  | None => None
  | Some gate_values =>
      match permutation with
      | None => None
      | Some permutation_values =>
          match lookups with
          | None => None
          | Some lookup_values =>
              Some (gate_values ++ permutation_values ++ lookup_values)
          end
      end
  end.

Definition proof_expressions (descriptions : list LookupVerifier.argument)
    (actions proof : nat) (parsed : ReferenceVerifier.plonk_prefix)
    (l_0 l_last l_blind x : VerifierField.t) : option (list VerifierField.t) :=
  let values := evaluations_for parsed proof in
  combine_expression_options
    (gate_expressions values)
    (permutation_expressions actions proof parsed values
      l_0 l_last l_blind x)
    (lookup_expressions_from actions proof 0 descriptions
      (nth proof parsed.(ReferenceVerifier.parsed_lookup_evals) []) parsed
      values l_0 l_last l_blind).
