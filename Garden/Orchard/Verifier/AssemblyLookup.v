(** * Fixed Post-NU6.3 lookup evaluation

    This file turns the values read by [Reference.read_plonk_prefix] into the
    Lookup commitments/evaluations follow the Rust verifier's allocation and
    expression order. *)

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

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.
Definition lookup_proof (actions proof lookup : nat) (parsed : ReferenceVerifier.plonk_prefix)
    (value : ReferenceVerifier.lookup_evals) : LookupVerifier.evaluated :=
  {|
    LookupVerifier.evaluated_committed := {|
      LookupVerifier.permuted := {|
        LookupVerifier.permuted_input_commitment := lookup_permuted_key actions proof lookup 0;
        LookupVerifier.permuted_table_commitment := lookup_permuted_key actions proof lookup 1
      |};
      LookupVerifier.product_commitment := lookup_product_key actions proof lookup
    |};
    LookupVerifier.product_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.lookup_product_eval);
    LookupVerifier.product_next_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.lookup_product_next_eval);
    LookupVerifier.permuted_input_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.lookup_permuted_input_eval);
    LookupVerifier.permuted_input_inv_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.lookup_permuted_input_inv_eval);
    LookupVerifier.permuted_table_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.lookup_permuted_table_eval)
  |}.

Fixpoint lookup_expressions_from (actions proof index : nat)
    (descriptions : list LookupVerifier.argument)
    (proofs : list ReferenceVerifier.lookup_evals) (parsed : ReferenceVerifier.plonk_prefix)
    (values : PlonkVerifier.evaluations) (l_0 l_last l_blind : VerifierField.t) : option (list VerifierField.t) :=
  match descriptions, proofs with
  | [], [] => Some []
  | description :: descriptions', proof_value :: proofs' =>
      match LookupVerifier.expressions l_0 l_last l_blind
        (ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_theta))
        (ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_beta))
        (ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_gamma))
        description values
        (lookup_proof actions proof index parsed proof_value),
        lookup_expressions_from actions proof (S index) descriptions' proofs'
          parsed values l_0 l_last l_blind with
      | LookupVerifier.LookupExpressions expressions, Some tail => Some (expressions ++ tail)
      | _, _ => None
      end
  | _, _ => None
  end.
