(** * Fixed Post-NU6.3 proof expression stream

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
Require Import Garden.Orchard.Verifier.AssemblyProof.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Definition append_expression_options
    (head tail : option (list VerifierField.t)) :
    option (list VerifierField.t) :=
  match head with
  | None => None
  | Some head_values =>
      match tail with
      | None => None
      | Some tail_values => Some (head_values ++ tail_values)
      end
  end.

Fixpoint all_proof_expressions_from
    (descriptions : list LookupVerifier.argument)
    (actions proof_count proof : nat)
    (parsed : ReferenceVerifier.plonk_prefix) (l_0 l_last l_blind x : VerifierField.t) :
    option (list VerifierField.t) :=
  match proof_count with
  | O => Some []
  | S proof_count' =>
      append_expression_options
        (proof_expressions descriptions actions proof parsed
          l_0 l_last l_blind x)
        (all_proof_expressions_from descriptions actions proof_count'
          (S proof) parsed l_0 l_last l_blind x)
  end.
