(** * PLONK lookup verifier

    This is the five-expression lookup check and five-query schedule from
    [plonk/lookup/verifier.rs].  The state transitions remain explicit so a
    transcript trace can be compared phase-by-phase with Rust. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.

Import ListNotations.
Local Open Scope Z_scope.

Module LookupVerifier.

Module F := VerifierField.
Module P := PlonkVerifier.

Record argument : Type := {
  input_expressions : list P.expression;
  table_expressions : list P.expression;
}.

Record permutation_commitments : Type := {
  permuted_input_commitment : P.commitment_key;
  permuted_table_commitment : P.commitment_key;
}.

Record committed : Type := {
  permuted : permutation_commitments;
  product_commitment : P.commitment_key;
}.

Record evaluated : Type := {
  evaluated_committed : committed;
  product_eval : F.t;
  product_next_eval : F.t;
  permuted_input_eval : F.t;
  permuted_input_inv_eval : F.t;
  permuted_table_eval : F.t;
}.

Definition point_reads_before_beta : nat := 2.
Definition point_reads_after_gamma : nat := 1.
Definition scalar_reads_after_x : nat := 5.

Fixpoint evaluate_and_compress_from (theta accumulator : F.t)
    (values : P.evaluations) (expressions : list P.expression) :
    P.expression_result :=
  match expressions with
  | [] => P.ExpressionValue accumulator
  | expression :: expressions' =>
      match P.evaluate_expression values expression with
      | P.ExpressionPanicked failure => P.ExpressionPanicked failure
      | P.ExpressionValue value =>
          evaluate_and_compress_from theta (F.add (F.mul accumulator theta) value)
            values expressions'
      end
  end.

Definition evaluate_and_compress (theta : F.t) (values : P.evaluations)
    (expressions : list P.expression) : P.expression_result :=
  evaluate_and_compress_from theta F.zero values expressions.

Inductive expressions_result : Type :=
| LookupExpressions (values : list F.t)
| LookupExpressionPanicked (failure : P.expression_failure).

Definition expressions (l_0 l_last l_blind theta beta gamma : F.t)
    (description : argument) (values : P.evaluations) (proof : evaluated) :
    expressions_result :=
  match evaluate_and_compress theta values description.(input_expressions),
        evaluate_and_compress theta values description.(table_expressions) with
  | P.ExpressionPanicked failure, _
  | _, P.ExpressionPanicked failure => LookupExpressionPanicked failure
  | P.ExpressionValue compressed_input, P.ExpressionValue compressed_table =>
      let active := F.sub F.one (F.add l_last l_blind) in
      let product_left :=
        F.mul
          (F.mul proof.(product_next_eval)
            (F.add proof.(permuted_input_eval) beta))
          (F.add proof.(permuted_table_eval) gamma) in
      let product_right :=
        F.mul
          (F.mul proof.(product_eval) (F.add compressed_input beta))
          (F.add compressed_table gamma) in
      LookupExpressions [
        F.mul l_0 (F.sub F.one proof.(product_eval));
        F.mul l_last
          (F.sub (F.square proof.(product_eval)) proof.(product_eval));
        F.mul (F.sub product_left product_right) active;
        F.mul l_0
          (F.sub proof.(permuted_input_eval) proof.(permuted_table_eval));
        F.mul
          (F.mul
            (F.sub proof.(permuted_input_eval) proof.(permuted_table_eval))
            (F.sub proof.(permuted_input_eval)
              proof.(permuted_input_inv_eval)))
          active
      ]
  end.

Definition queries (omega x : F.t) (proof : evaluated) :
    option (list P.verifier_query) :=
  match P.rotate_omega omega x (-1), P.rotate_omega omega x 1 with
  | Some x_inv, Some x_next =>
      let commitments := proof.(evaluated_committed) in
      let permuted := commitments.(permuted) in
      Some [
        {| P.query_commitment := commitments.(product_commitment);
           P.query_point := x;
           P.query_eval := proof.(product_eval) |};
        {| P.query_commitment := permuted.(permuted_input_commitment);
           P.query_point := x;
           P.query_eval := proof.(permuted_input_eval) |};
        {| P.query_commitment := permuted.(permuted_table_commitment);
           P.query_point := x;
           P.query_eval := proof.(permuted_table_eval) |};
        {| P.query_commitment := permuted.(permuted_input_commitment);
           P.query_point := x_inv;
           P.query_eval := proof.(permuted_input_inv_eval) |};
        {| P.query_commitment := commitments.(product_commitment);
           P.query_point := x_next;
           P.query_eval := proof.(product_next_eval) |}
      ]
  | _, _ => None
  end.

End LookupVerifier.
