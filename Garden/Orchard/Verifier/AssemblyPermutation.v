(** * Fixed Post-NU6.3 gate, permutation, and lookup evaluation

    This file turns the values read by [Reference.read_plonk_prefix] into the
    vanishing expressions are evaluated in Rust order.  The transparent
    executable layer is split from commitment allocation and query assembly so
    Rocq can serialize it without copying one monolithic environment. *)

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

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.
Fixpoint evaluate_terms (values : PlonkVerifier.evaluations)
    (terms : list PlonkVerifier.expression) :
    option (list VerifierField.t) :=
  match terms with
  | [] => Some []
  | term :: terms' =>
      match PlonkVerifier.evaluate_expression values term, evaluate_terms values terms' with
      | PlonkVerifier.ExpressionValue value, Some tail => Some (value :: tail)
      | _, _ => None
      end
  end.

Definition gate_expressions (values : PlonkVerifier.evaluations) : option (list VerifierField.t) :=
  evaluate_terms values
    (concat OrchardPostNu63.gate_polynomials).

Definition physical_eval (values : PlonkVerifier.evaluations) (column : Raw.ColumnRef.t) :
    option VerifierField.t :=
  let pair := (column.(Raw.ColumnRef.index), 0) in
  let '(kind, queries, evals) :=
    match column.(Raw.ColumnRef.kind) with
    | Raw.ColumnKind.Advice =>
        (PlonkVerifier.Advice, OrchardPostNu63.advice_query_pairs,
          values.(PlonkVerifier.advice_values))
    | Raw.ColumnKind.Fixed =>
        (PlonkVerifier.Fixed, OrchardPostNu63.fixed_query_pairs,
          values.(PlonkVerifier.fixed_values))
    | Raw.ColumnKind.Instance_ =>
        (PlonkVerifier.Instance, OrchardPostNu63.instance_query_pairs,
          values.(PlonkVerifier.instance_values))
    end in
  match OrchardPostNu63.query_index_from pair queries 0 with
  | Some index => nth_error evals index
  | None => None
  end.

Fixpoint map_physical_evals (values : PlonkVerifier.evaluations)
    (columns : list Raw.ColumnRef.t) : option (list VerifierField.t) :=
  match columns with
  | [] => Some []
  | column :: columns' =>
      match physical_eval values column, map_physical_evals values columns' with
      | Some value, Some tail => Some (value :: tail)
      | _, _ => None
      end
  end.

Definition three_chunks (values : list VerifierField.t) : list (list VerifierField.t) :=
  [firstn 7 values; firstn 7 (skipn 7 values); skipn 14 values].

Fixpoint permutation_sets_from (actions proof index : nat)
    (values : list ReferenceVerifier.permutation_set_evals) : list PermutationVerifier.evaluated_set :=
  match values with
  | [] => []
  | value :: values' => {|
      PermutationVerifier.product_commitment := permutation_product_key actions proof index;
      PermutationVerifier.product_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.permutation_product_eval);
      PermutationVerifier.product_next_eval := ReferenceVerifier.scalar_Z value.(ReferenceVerifier.permutation_product_next_eval);
      PermutationVerifier.product_last_eval := option_map ReferenceVerifier.scalar_Z
        value.(ReferenceVerifier.permutation_product_last_eval)
    |} :: permutation_sets_from actions proof (S index) values'
  end.

Definition permutation_expressions (actions proof : nat) (parsed : ReferenceVerifier.plonk_prefix)
    (values : PlonkVerifier.evaluations) (l_0 l_last l_blind x : VerifierField.t) : option (list VerifierField.t) :=
  match map_physical_evals values OrchardPostNu63.permutation_columns with
  | None => None
  | Some column_evals =>
      let proof_argument := {|
        PermutationVerifier.sets := permutation_sets_from actions proof 0
          (nth proof parsed.(ReferenceVerifier.parsed_permutation_evals) [])
      |} in
      match PermutationVerifier.expressions
        (ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_beta))
        (ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_gamma)) x
        OrchardCompiledAlgebraic.delta l_0 l_last l_blind proof_argument
        (three_chunks column_evals)
        (three_chunks (scalar_values parsed.(ReferenceVerifier.parsed_common_permutation_evals))) 7 with
      | PermutationVerifier.PermutationExpressions expressions => Some expressions
      | PermutationVerifier.PermutationPanicked _ => None
      end
  end.
