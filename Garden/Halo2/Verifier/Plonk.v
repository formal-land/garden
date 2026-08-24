(** * Rust-shaped PLONK verifier data and expression evaluation

    This file mirrors the data consumed by [plonk::verify_proof].  It does not
    claim equivalence with that Rust function: commitment decoding and the
    transcript are connected in [Reference].  In particular, commitment
    references carry an explicit allocation identifier.  Equality of those
    identifiers models Rust's [std::ptr::eq], which is deliberately different
    from equality of the represented curve points. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Algebra.

Import ListNotations.
Local Open Scope Z_scope.

Module PlonkVerifier.

Module F := VerifierField.

Inductive column_kind : Type :=
| Advice
| Fixed
| Instance.

Record column : Type := {
  column_type : column_kind;
  column_index : nat;
}.

Record query_spec : Type := {
  query_column : column;
  query_rotation : Z;
}.

Inductive expression : Type :=
| Constant (value : F.t)
| Selector (selector_index : nat)
| Query (query : query_spec)
| Negated (inner : expression)
| Sum (lhs rhs : expression)
| Product (lhs rhs : expression)
| Scaled (inner : expression) (factor : F.t).

Record evaluations : Type := {
  advice_values : list F.t;
  fixed_values : list F.t;
  instance_values : list F.t;
}.

Inductive expression_failure : Type :=
| VirtualSelectorSurvived
| QueryIndexOutOfBounds (kind : column_kind) (index : nat).

Inductive expression_result : Type :=
| ExpressionValue (value : F.t)
| ExpressionPanicked (failure : expression_failure).

Definition map_expression (f : F.t -> F.t) (r : expression_result) :
    expression_result :=
  match r with
  | ExpressionValue x => ExpressionValue (f x)
  | ExpressionPanicked failure => ExpressionPanicked failure
  end.

Definition map_expression2 (f : F.t -> F.t -> F.t)
    (lhs rhs : expression_result) : expression_result :=
  match lhs, rhs with
  | ExpressionValue x, ExpressionValue y => ExpressionValue (f x y)
  | ExpressionPanicked failure, _ => ExpressionPanicked failure
  | _, ExpressionPanicked failure => ExpressionPanicked failure
  end.

Definition query_value (values : evaluations) (query : query_spec) :
    expression_result :=
  let column := query.(query_column) in
  let index := column.(column_index) in
  let source :=
    match column.(column_type) with
    | Advice => values.(advice_values)
    | Fixed => values.(fixed_values)
    | Instance => values.(instance_values)
    end in
  match nth_error source index with
  | Some value => ExpressionValue value
  | None => ExpressionPanicked
      (QueryIndexOutOfBounds column.(column_type) index)
  end.

Fixpoint evaluate_expression (values : evaluations) (term : expression) :
    expression_result :=
  match term with
  | Constant value => ExpressionValue (F.canon value)
  | Selector _ => ExpressionPanicked VirtualSelectorSurvived
  | Query query => query_value values query
  | Negated inner => map_expression F.opp (evaluate_expression values inner)
  | Sum lhs rhs =>
      map_expression2 F.add
        (evaluate_expression values lhs) (evaluate_expression values rhs)
  | Product lhs rhs =>
      map_expression2 F.mul
        (evaluate_expression values lhs) (evaluate_expression values rhs)
  | Scaled inner factor =>
      map_expression (fun value => F.mul value factor)
        (evaluate_expression values inner)
  end.

Fixpoint evaluate_expressions (values : evaluations) (terms : list expression) :
    expression_result :=
  match terms with
  | [] => ExpressionValue F.zero
  | term :: terms' =>
      match evaluate_expression values term with
      | ExpressionPanicked failure => ExpressionPanicked failure
      | ExpressionValue value =>
          match evaluate_expressions values terms' with
          | ExpressionPanicked failure => ExpressionPanicked failure
          | ExpressionValue tail => ExpressionValue (F.add value tail)
          end
      end
  end.

(** Direct and MSM references occupy disjoint identity spaces, just as the
    two Rust enum variants do.  [allocation] is assigned by the verifier when
    it constructs each commitment object; it is not derived from coordinates. *)
Inductive commitment_key : Type :=
| DirectCommitment (allocation : nat)
| MsmCommitment (allocation : nat).

Definition commitment_key_eqb (left right : commitment_key) : bool :=
  match left, right with
  | DirectCommitment x, DirectCommitment y
  | MsmCommitment x, MsmCommitment y => Nat.eqb x y
  | _, _ => false
  end.

Record verifier_query : Type := {
  query_commitment : commitment_key;
  query_point : F.t;
  query_eval : F.t;
}.

Record verifying_key_shape : Type := {
  vk_k : nat;
  vk_n : nat;
  vk_cs_degree : nat;
  vk_num_instance_columns : nat;
  vk_num_advice_columns : nat;
  vk_instance_queries : list query_spec;
  vk_advice_queries : list query_spec;
  vk_fixed_queries : list query_spec;
  vk_gate_polynomials : list (list expression);
  vk_permutation_columns : list column;
  vk_lookup_count : nat;
  vk_blinding_factors : nat;
  vk_quotient_poly_degree : nat;
}.

Inductive instance_check : Type :=
| InstancesValid
| InvalidInstanceColumnCount (proof_index expected actual : nat)
| InstanceColumnTooLarge (proof_index column_index maximum actual : nat).

Fixpoint check_column_lengths (proof_index column_index maximum : nat)
    (columns : list (list F.t)) : instance_check :=
  match columns with
  | [] => InstancesValid
  | column :: columns' =>
      if Nat.leb (List.length column) maximum
      then check_column_lengths proof_index (S column_index) maximum columns'
      else InstanceColumnTooLarge proof_index column_index maximum
        (List.length column)
  end.

Fixpoint check_instances_from (shape : verifying_key_shape) (proof_index : nat)
    (proofs : list (list (list F.t))) : instance_check :=
  match proofs with
  | [] => InstancesValid
  | columns :: proofs' =>
      if Nat.eqb (List.length columns) shape.(vk_num_instance_columns) then
        match check_column_lengths proof_index 0
            (shape.(vk_n) - (shape.(vk_blinding_factors) + 1)) columns with
        | InstancesValid => check_instances_from shape (S proof_index) proofs'
        | failure => failure
        end
      else InvalidInstanceColumnCount proof_index
        shape.(vk_num_instance_columns) (List.length columns)
  end.

Definition check_instances (shape : verifying_key_shape)
    (proofs : list (list (list F.t))) : instance_check :=
  check_instances_from shape 0 proofs.

(** Halo2 evaluates a column at [omega^rotation * x].  Negative Rust [i32]
    rotations are represented by inversion rather than by silently converting
    them to a natural number. *)
Definition rotate_omega (omega x : F.t) (rotation : Z) : option F.t :=
  if (rotation <? 0)%Z then
    match F.invert (F.pow_nat omega (Z.to_nat (-rotation))) with
    | Some factor => Some (F.mul x factor)
    | None => None
    end
  else Some (F.mul x (F.pow_nat omega (Z.to_nat rotation))).

Definition expected_proof_size (action_count : nat) : nat :=
  2720 + 2272 * action_count.

End PlonkVerifier.
