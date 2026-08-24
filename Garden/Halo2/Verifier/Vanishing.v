(** * PLONK vanishing argument

    The quotient commitment is reconstructed by Horner folding the quotient
    pieces in the reverse order used by [vanishing/verifier.rs].  The symbolic
    linear combination is later inserted into the concrete MSM by
    [Commitment]. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.

Import ListNotations.
Local Open Scope Z_scope.

Module VanishingVerifier.

Module F := VerifierField.
Module P := PlonkVerifier.

Record committed : Type := {
  random_poly_commitment : P.commitment_key;
}.

Record constructed : Type := {
  h_commitments : list P.commitment_key;
  constructed_random_poly_commitment : P.commitment_key;
}.

Record partially_evaluated : Type := {
  partial_h_commitments : list P.commitment_key;
  partial_random_poly_commitment : P.commitment_key;
  random_eval : F.t;
}.

Definition linear_combination : Type := list (F.t * P.commitment_key).

Record evaluated : Type := {
  h_allocation : nat;
  h_terms : linear_combination;
  evaluated_random_poly_commitment : P.commitment_key;
  expected_h_eval : F.t;
  evaluated_random_eval : F.t;
}.

Definition scale_terms (factor : F.t) (terms : linear_combination) :
    linear_combination :=
  map (fun term => (F.mul factor (fst term), snd term)) terms.

Definition quotient_terms (xn : F.t) (commitments : list P.commitment_key) :
    linear_combination :=
  fold_left
    (fun terms commitment => (F.one, commitment) :: scale_terms xn terms)
    (rev commitments) [].

Inductive verify_result : Type :=
| VanishingEvaluated (value : evaluated)
| VanishingPanickedAtQuotientInverse.

Definition verify (msm_allocation : nat) (expressions : list F.t)
    (y xn : F.t) (proof : partially_evaluated) : verify_result :=
  let compressed := F.compress y expressions in
  match F.invert (F.sub xn F.one) with
  | None => VanishingPanickedAtQuotientInverse
  | Some denominator_inverse =>
      VanishingEvaluated {|
        h_allocation := msm_allocation;
        h_terms := quotient_terms xn proof.(partial_h_commitments);
        evaluated_random_poly_commitment :=
          proof.(partial_random_poly_commitment);
        expected_h_eval := F.mul compressed denominator_inverse;
        evaluated_random_eval := proof.(random_eval);
      |}
  end.

Definition queries (x : F.t) (proof : evaluated) : list P.verifier_query := [
  {| P.query_commitment := P.MsmCommitment proof.(h_allocation);
     P.query_point := x;
     P.query_eval := proof.(expected_h_eval) |};
  {| P.query_commitment := proof.(evaluated_random_poly_commitment);
     P.query_point := x;
     P.query_eval := proof.(evaluated_random_eval) |}
].

End VanishingVerifier.
