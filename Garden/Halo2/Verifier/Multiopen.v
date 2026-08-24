(** * Halo2 multi-opening verifier

    [construct_intermediate_sets] is the subtle part of this module.  Rust
    groups queries by *allocation identity* ([std::ptr::eq]), assigns point
    indices in first-observation order, preserves commitment insertion order
    ([IndexMap]), and sorts each set of point indices ([BTreeSet]).  The model
    below makes all four choices explicit. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.

Import ListNotations.
Local Open Scope Z_scope.

Module MultiopenVerifier.

Module F := VerifierField.
Module P := PlonkVerifier.

Record commitment_points : Type := {
  cp_commitment : P.commitment_key;
  cp_point_indices : list nat;
}.

Record point_binding : Type := {
  pb_point : F.t;
  pb_index : nat;
}.

Record set_binding : Type := {
  sb_point_indices : list nat;
  sb_index : nat;
}.

Record commitment_data : Type := {
  cd_commitment : P.commitment_key;
  cd_set_index : nat;
  cd_point_indices : list nat;
  cd_evals : list F.t;
}.

Record intermediate_sets : Type := {
  is_commitments : list commitment_data;
  is_point_sets : list (list F.t);
}.

Fixpoint find_point (point : F.t) (bindings : list point_binding) : option nat :=
  match bindings with
  | [] => None
  | binding :: bindings' =>
      if F.eqb point binding.(pb_point) then Some binding.(pb_index)
      else find_point point bindings'
  end.

Definition find_or_insert_point (point : F.t) (bindings : list point_binding) :
    nat * list point_binding :=
  match find_point point bindings with
  | Some index => (index, bindings)
  | None =>
      let index := List.length bindings in
      (index, bindings ++ [{| pb_point := F.canon point; pb_index := index |}])
  end.

Fixpoint add_commitment_point (key : P.commitment_key) (point_index : nat)
    (commitments : list commitment_points) : list commitment_points :=
  match commitments with
  | [] => [{| cp_commitment := key; cp_point_indices := [point_index] |}]
  | commitment :: commitments' =>
      if P.commitment_key_eqb key commitment.(cp_commitment) then
        {| cp_commitment := commitment.(cp_commitment);
           cp_point_indices := commitment.(cp_point_indices) ++ [point_index] |}
        :: commitments'
      else commitment :: add_commitment_point key point_index commitments'
  end.

Fixpoint first_pass (queries : list P.verifier_query)
    (points : list point_binding) (commitments : list commitment_points) :
    list point_binding * list commitment_points :=
  match queries with
  | [] => (points, commitments)
  | query :: queries' =>
      let '(point_index, points') :=
        find_or_insert_point query.(P.query_point) points in
      first_pass queries' points'
        (add_commitment_point query.(P.query_commitment) point_index commitments)
  end.

Fixpoint insert_nat (value : nat) (values : list nat) : list nat :=
  match values with
  | [] => [value]
  | head :: tail =>
      if Nat.eqb value head then values
      else if Nat.ltb value head then value :: values
      else head :: insert_nat value tail
  end.

Definition sort_unique_nat (values : list nat) : list nat :=
  fold_left (fun acc value => insert_nat value acc) values [].

Fixpoint nat_list_eqb (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && nat_list_eqb xs ys
  | _, _ => false
  end.

Fixpoint find_set (indices : list nat) (sets : list set_binding) : option nat :=
  match sets with
  | [] => None
  | set :: sets' =>
      if nat_list_eqb indices set.(sb_point_indices) then Some set.(sb_index)
      else find_set indices sets'
  end.

Definition find_or_insert_set (indices : list nat) (sets : list set_binding) :
    nat * list set_binding :=
  match find_set indices sets with
  | Some index => (index, sets)
  | None =>
      let index := List.length sets in
      (index, sets ++ [{| sb_point_indices := indices; sb_index := index |}])
  end.

Fixpoint build_sets (commitments : list commitment_points)
    (sets : list set_binding) : list set_binding :=
  match commitments with
  | [] => sets
  | commitment :: commitments' =>
      let indices := sort_unique_nat commitment.(cp_point_indices) in
      let '(_, sets') := find_or_insert_set indices sets in
      build_sets commitments' sets'
  end.

Definition query_matches (key : P.commitment_key) (point : F.t)
    (query : P.verifier_query) : bool :=
  P.commitment_key_eqb key query.(P.query_commitment) &&
  F.eqb point query.(P.query_point).

Fixpoint matching_evals (key : P.commitment_key) (point : F.t)
    (queries : list P.verifier_query) : list F.t :=
  match queries with
  | [] => []
  | query :: queries' =>
      if query_matches key point query
      then query.(P.query_eval) :: matching_evals key point queries'
      else matching_evals key point queries'
  end.

Fixpoint point_at_index (index : nat) (points : list point_binding) : option F.t :=
  match points with
  | [] => None
  | binding :: points' =>
      if Nat.eqb index binding.(pb_index) then Some binding.(pb_point)
      else point_at_index index points'
  end.

Inductive construction_result : Type :=
| IntermediateSets (value : intermediate_sets)
| DuplicateCommitmentPointQuery
| InternalGroupingFailure.

Fixpoint evals_for_indices (key : P.commitment_key) (indices : list nat)
    (points : list point_binding) (queries : list P.verifier_query) :
    option (list F.t) :=
  match indices with
  | [] => Some []
  | index :: indices' =>
      match point_at_index index points with
      | None => None
      | Some point =>
          match matching_evals key point queries,
                evals_for_indices key indices' points queries with
          | [value], Some tail => Some (value :: tail)
          | _, _ => None
          end
      end
  end.

Fixpoint finalize_commitments (commitments : list commitment_points)
    (sets : list set_binding) (points : list point_binding)
    (queries : list P.verifier_query) : construction_result :=
  match commitments with
  | [] => IntermediateSets {|
      is_commitments := [];
      is_point_sets := []
    |}
  | commitment :: commitments' =>
      let indices := sort_unique_nat commitment.(cp_point_indices) in
      match find_set indices sets,
            evals_for_indices commitment.(cp_commitment) indices points queries,
            finalize_commitments commitments' sets points queries with
      | Some set_index, Some evals, IntermediateSets tail =>
          IntermediateSets {|
            is_commitments :=
              {| cd_commitment := commitment.(cp_commitment);
                 cd_set_index := set_index;
                 cd_point_indices := commitment.(cp_point_indices);
                 cd_evals := evals |} :: tail.(is_commitments);
            is_point_sets := []
          |}
      | Some _, None, _ => DuplicateCommitmentPointQuery
      | _, _, DuplicateCommitmentPointQuery => DuplicateCommitmentPointQuery
      | _, _, _ => InternalGroupingFailure
      end
  end.

Fixpoint points_for_indices (indices : list nat) (points : list point_binding) :
    option (list F.t) :=
  match indices with
  | [] => Some []
  | index :: indices' =>
      match point_at_index index points, points_for_indices indices' points with
      | Some point, Some tail => Some (point :: tail)
      | _, _ => None
      end
  end.

Fixpoint materialize_point_sets (sets : list set_binding)
    (points : list point_binding) : option (list (list F.t)) :=
  match sets with
  | [] => Some []
  | set :: sets' =>
      match points_for_indices set.(sb_point_indices) points,
            materialize_point_sets sets' points with
      | Some point_set, Some tail => Some (point_set :: tail)
      | _, _ => None
      end
  end.

Definition construct_intermediate_sets (queries : list P.verifier_query) :
    construction_result :=
  let '(points, commitments) := first_pass queries [] [] in
  let sets := build_sets commitments [] in
  match finalize_commitments commitments sets points queries,
        materialize_point_sets sets points with
  | IntermediateSets partial, Some point_sets =>
      IntermediateSets {|
        is_commitments := partial.(is_commitments);
        is_point_sets := point_sets
      |}
  | DuplicateCommitmentPointQuery, _ => DuplicateCommitmentPointQuery
  | _, _ => InternalGroupingFailure
  end.

Definition symbolic_msm : Type := list (F.t * P.commitment_key).

Record compressed_set : Type := {
  cs_terms : symbolic_msm;
  cs_evals : list F.t;
  cs_next_power : F.t;
}.

Definition empty_compressed_set (point_count : nat) : compressed_set := {|
  cs_terms := [];
  cs_evals := F.repeat_scalar F.zero point_count;
  cs_next_power := F.one;
|}.

Fixpoint zip_scaled_add (factor : F.t) (values accumulator : list F.t) :
    list F.t :=
  match values, accumulator with
  | value :: values', current :: accumulator' =>
      F.add current (F.mul value factor) ::
        zip_scaled_add factor values' accumulator'
  | _, _ => []
  end.

Fixpoint update_compressed_at (index : nat) (data : commitment_data) (x_1 : F.t)
    (sets : list compressed_set) : option (list compressed_set) :=
  match index, sets with
  | O, set :: sets' => Some ({|
      cs_terms := set.(cs_terms) ++ [(set.(cs_next_power), data.(cd_commitment))];
      cs_evals := zip_scaled_add set.(cs_next_power) data.(cd_evals) set.(cs_evals);
      cs_next_power := F.mul set.(cs_next_power) x_1
    |} :: sets')
  | S index', set :: sets' =>
      match update_compressed_at index' data x_1 sets' with
      | Some tail => Some (set :: tail)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint accumulate_commitments (x_1 : F.t) (commitments : list commitment_data)
    (sets : list compressed_set) : option (list compressed_set) :=
  match commitments with
  | [] => Some sets
  | data :: commitments' =>
      match update_compressed_at data.(cd_set_index) data x_1 sets with
      | Some sets' => accumulate_commitments x_1 commitments' sets'
      | None => None
      end
  end.

Definition compress_intermediate (x_1 : F.t) (sets : intermediate_sets) :
    option (list compressed_set) :=
  let initial := map (fun points => empty_compressed_set (List.length points))
    sets.(is_point_sets) in
  (* Rust iterates the IndexMap in reverse so the last-seen commitment gets
     x_1^0. *)
  accumulate_commitments x_1 (rev sets.(is_commitments)) initial.

Definition polynomial : Type := list F.t.

Fixpoint poly_add (left right : polynomial) : polynomial :=
  match left, right with
  | [], values | values, [] => values
  | x :: xs, y :: ys => F.add x y :: poly_add xs ys
  end.

Definition poly_scale (factor : F.t) (poly : polynomial) : polynomial :=
  map (F.mul factor) poly.

Fixpoint poly_mul_linear (root : F.t) (poly : polynomial) : polynomial :=
  match poly with
  | [] => []
  | coefficient :: coefficients =>
      poly_add [F.mul (F.opp root) coefficient]
        (F.zero :: poly_mul_linear root coefficients)
  end.

Fixpoint basis_numerator (skip : nat) (points : list F.t) : polynomial :=
  match points with
  | [] => [F.one]
  | point :: points' =>
      let tail := basis_numerator
        (match skip with O => O | S skip' => skip' end) points' in
      match skip with
      | O => tail
      | S _ => poly_mul_linear point tail
      end
  end.

(** A direct, executable Lagrange evaluation, used here in place of building
    coefficient vectors.  The zero-denominator branch remains explicit. *)
Fixpoint lagrange_eval_from (index : nat) (x : F.t) (points evals : list F.t) :
    option F.t :=
  match evals with
  | [] => Some F.zero
  | value :: evals' =>
      match nth_error points index with
      | None => None
      | Some point_i =>
          let others := firstn index points ++ skipn (S index) points in
          let numerator := F.product (map (fun point => F.sub x point) others) in
          let denominator := F.product
            (map (fun point => F.sub point_i point) others) in
          match F.invert denominator,
                lagrange_eval_from (S index) x points evals' with
          | Some denominator_inv, Some tail =>
              Some (F.add (F.mul value (F.mul numerator denominator_inv)) tail)
          | _, _ => None
          end
      end
  end.

Definition lagrange_eval (points evals : list F.t) (x : F.t) : option F.t :=
  if Nat.eqb (List.length points) (List.length evals)
  then lagrange_eval_from 0 x points evals
  else None.

Inductive expected_eval_result : Type :=
| ExpectedEval (value : F.t)
| X3CollidesWithOpeningPoint
| InvalidInterpolationShape.

Fixpoint divide_by_points (x_3 : F.t) (points : list F.t) (value : F.t) :
    expected_eval_result :=
  match points with
  | [] => ExpectedEval value
  | point :: points' =>
      match F.invert (F.sub x_3 point) with
      | None => X3CollidesWithOpeningPoint
      | Some inverse => divide_by_points x_3 points' (F.mul value inverse)
      end
  end.

Fixpoint expected_msm_eval_from (x_2 x_3 accumulator : F.t)
    (point_sets : list (list F.t)) (compressed : list compressed_set)
    (u : list F.t) : expected_eval_result :=
  match point_sets, compressed, u with
  | [], [], [] => ExpectedEval accumulator
  | points :: point_sets', set :: compressed', proof_eval :: u' =>
      match lagrange_eval points set.(cs_evals) x_3 with
      | None => InvalidInterpolationShape
      | Some r_eval =>
          match divide_by_points x_3 points (F.sub proof_eval r_eval) with
          | ExpectedEval quotient =>
              expected_msm_eval_from x_2 x_3
                (F.add (F.mul accumulator x_2) quotient)
                point_sets' compressed' u'
          | failure => failure
          end
      end
  | _, _, _ => InvalidInterpolationShape
  end.

Definition expected_msm_eval (x_2 x_3 : F.t) (sets : intermediate_sets)
    (compressed : list compressed_set) (u : list F.t) : expected_eval_result :=
  expected_msm_eval_from x_2 x_3 F.zero sets.(is_point_sets) compressed u.

Definition scale_symbolic (factor : F.t) (terms : symbolic_msm) : symbolic_msm :=
  map (fun term => (F.mul (fst term) factor, snd term)) terms.

Fixpoint final_fold (x_4 : F.t) (sets : list compressed_set) (u : list F.t)
    (terms : symbolic_msm) (value : F.t) : option (symbolic_msm * F.t) :=
  match sets, u with
  | [], [] => Some (terms, value)
  | set :: sets', proof_eval :: u' =>
      final_fold x_4 sets' u'
        (scale_symbolic x_4 terms ++ set.(cs_terms))
        (F.add (F.mul value x_4) proof_eval)
  | _, _ => None
  end.

Record opening_claim : Type := {
  claim_terms : symbolic_msm;
  claim_point : F.t;
  claim_value : F.t;
}.

Definition make_opening_claim (q_prime : P.commitment_key) (x_3 x_4 : F.t)
    (compressed : list compressed_set) (u : list F.t)
    (initial_terms : symbolic_msm) (msm_eval : F.t) : option opening_claim :=
  match final_fold x_4 compressed u (initial_terms ++ [(F.one, q_prime)]) msm_eval with
  | None => None
  | Some (terms, value) => Some {|
      claim_terms := terms;
      claim_point := x_3;
      claim_value := value
    |}
  end.

End MultiopenVerifier.
