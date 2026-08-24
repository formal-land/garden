(** * PLONK permutation verifier

    The records follow [plonk/permutation/verifier.rs]: commitments are first
    read per degree-sized set, then each set is evaluated at [x], [omega*x],
    and (except the final set) [omega^last*x]. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.

Import ListNotations.
Local Open Scope Z_scope.

Module PermutationVerifier.

Module F := VerifierField.
Module P := PlonkVerifier.

Record committed : Type := {
  product_commitments : list P.commitment_key;
}.

Record evaluated_set : Type := {
  product_commitment : P.commitment_key;
  product_eval : F.t;
  product_next_eval : F.t;
  product_last_eval : option F.t;
}.

Record common_evaluated : Type := {
  permutation_evals : list F.t;
}.

Record evaluated : Type := {
  sets : list evaluated_set;
}.

Definition chunk_len (shape : P.verifying_key_shape) : nat :=
  shape.(P.vk_cs_degree) - 2.

Definition chunk_count_go {A : Type} (size : nat) (xs : list A) : nat :=
  match size with
  | O => O
  | S _ => (List.length xs + size - 1) / size
  end.

Definition product_commitment_count (shape : P.verifying_key_shape) : nat :=
  chunk_count_go (chunk_len shape) shape.(P.vk_permutation_columns).

(** Number of scalar reads in [Committed::evaluate]: two for every set and a
    third "last" evaluation for every non-final set. *)
Definition evaluated_scalar_count (set_count : nat) : nat :=
  match set_count with O => O | S n => 2 * (S n) + n end.

Definition active_rows (l_last l_blind : F.t) : F.t :=
  F.sub F.one (F.add l_last l_blind).

Definition first_expression (l_0 : F.t) (first : evaluated_set) : F.t :=
  F.mul l_0 (F.sub F.one first.(product_eval)).

Definition last_expression (l_last : F.t) (last : evaluated_set) : F.t :=
  F.mul
    (F.sub (F.square last.(product_eval)) last.(product_eval)) l_last.

Inductive permutation_failure : Type :=
| MissingPreviousLastEvaluation
| MissingRotatedPoint.

Inductive expressions_result : Type :=
| PermutationExpressions (values : list F.t)
| PermutationPanicked (failure : permutation_failure).

Fixpoint linkage_expressions_from
    (l_0 : F.t) (previous : evaluated_set) (rest : list evaluated_set) :
    expressions_result :=
  match rest with
  | [] => PermutationExpressions []
  | current :: tail =>
      match previous.(product_last_eval) with
      | None => PermutationPanicked MissingPreviousLastEvaluation
      | Some previous_last =>
          match linkage_expressions_from l_0 current tail with
          | PermutationPanicked failure => PermutationPanicked failure
          | PermutationExpressions values =>
              PermutationExpressions
                (F.mul (F.sub current.(product_eval) previous_last) l_0
                  :: values)
          end
      end
  end.

Definition linkage_expressions (l_0 : F.t) (sets : list evaluated_set) :
    expressions_result :=
  match sets with
  | [] => PermutationExpressions []
  | previous :: rest => linkage_expressions_from l_0 previous rest
  end.

Definition product_expression
    (beta gamma x delta l_last l_blind : F.t)
    (set : evaluated_set) (chunk_index chunk_size : nat)
    (column_evals permutation_evals : list F.t) : F.t :=
  let left :=
    fold_left
      (fun acc pair =>
        F.mul acc (F.add (F.add (fst pair) (F.mul beta (snd pair))) gamma))
      (combine column_evals permutation_evals) set.(product_next_eval) in
  let first_delta :=
    F.mul (F.mul beta x) (F.pow_nat delta (chunk_index * chunk_size)) in
  let right_state :=
    fold_left
      (fun state value =>
        (F.mul (fst state) (F.add (F.add value (snd state)) gamma),
         F.mul (snd state) delta))
      column_evals (set.(product_eval), first_delta) in
  F.mul (F.sub left (fst right_state)) (active_rows l_last l_blind).

Fixpoint product_expressions_from
    (beta gamma x delta l_last l_blind : F.t) (chunk_size index : nat)
    (sets : list evaluated_set) (column_chunks permutation_chunks : list (list F.t))
    : list F.t :=
  match sets, column_chunks, permutation_chunks with
  | set :: sets', columns :: columns', sigmas :: sigmas' =>
      product_expression beta gamma x delta l_last l_blind set index chunk_size
        columns sigmas
      :: product_expressions_from beta gamma x delta l_last l_blind chunk_size
           (S index) sets' columns' sigmas'
  | _, _, _ => []
  end.

Definition expressions
    (beta gamma x delta l_0 l_last l_blind : F.t)
    (argument : evaluated) (column_chunks permutation_chunks : list (list F.t))
    (chunk_size : nat) : expressions_result :=
  match argument.(sets) with
  | [] => PermutationExpressions []
  | first :: tail =>
      let final_set := List.last tail first in
      match linkage_expressions l_0 argument.(sets) with
      | PermutationPanicked failure => PermutationPanicked failure
      | PermutationExpressions links =>
          PermutationExpressions
            ([first_expression l_0 first; last_expression l_last final_set] ++
             links ++
             product_expressions_from beta gamma x delta l_last l_blind
               chunk_size 0 argument.(sets) column_chunks permutation_chunks)
      end
  end.

Fixpoint set_queries (x x_next : F.t) (sets : list evaluated_set) :
    list P.verifier_query :=
  match sets with
  | [] => []
  | set :: sets' =>
      {| P.query_commitment := set.(product_commitment);
         P.query_point := x;
         P.query_eval := set.(product_eval) |}
      :: {| P.query_commitment := set.(product_commitment);
            P.query_point := x_next;
            P.query_eval := set.(product_next_eval) |}
      :: set_queries x x_next sets'
  end.

Fixpoint last_queries_all (x_last : F.t) (sets : list evaluated_set) :
    option (list P.verifier_query) :=
  match sets with
  | [] => Some []
  | set :: rest =>
      match set.(product_last_eval), last_queries_all x_last rest with
      | Some value, Some tail =>
          Some ({| P.query_commitment := set.(product_commitment);
                   P.query_point := x_last;
                   P.query_eval := value |} :: tail)
      | _, _ => None
      end
  end.

(** Rust iterates [self.sets.iter().rev().skip(1)]: the final set has no
    [last] evaluation, and the remaining sets are opened from the penultimate
    back to the first. *)
Definition last_queries (x_last : F.t) (sets : list evaluated_set) :
    option (list P.verifier_query) :=
  match rev sets with
  | [] => Some []
  | _final :: nonfinal_reversed =>
      last_queries_all x_last nonfinal_reversed
  end.

Definition queries (omega x : F.t) (blinding_factors : nat)
    (argument : evaluated) : option (list P.verifier_query) :=
  match P.rotate_omega omega x 1,
        P.rotate_omega omega x (- Z.of_nat (blinding_factors + 1)),
        last_queries
          (match P.rotate_omega omega x (- Z.of_nat (blinding_factors + 1)) with
           | Some value => value | None => F.zero end)
          argument.(sets) with
  | Some x_next, Some x_last, Some last =>
      Some (set_queries x x_next argument.(sets) ++ last)
  | _, _, _ => None
  end.

Definition common_queries (commitments : list P.commitment_key) (x : F.t)
    (common : common_evaluated) : list P.verifier_query :=
  map (fun pair =>
    {| P.query_commitment := fst pair;
       P.query_point := x;
       P.query_eval := snd pair |})
    (combine commitments common.(permutation_evals)).

End PermutationVerifier.
