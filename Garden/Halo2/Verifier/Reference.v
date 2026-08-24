(** * Executable reference control flow for [plonk::verify_proof]

    This module owns proof read order and transcript challenge order.  Circuit-
    specific expression/query assembly is supplied as an ordinary record of
    functions; there are no axioms.  This makes the generic Halo2 control flow
    executable while keeping the Post-NU6.3 adapter auditable in a separate
    file. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Reader.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Transcript.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Multiopen.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.IPA.

Import ListNotations.
Local Open Scope Z_scope.

Module ReferenceVerifier.

Module F := VerifierField.
Module P := PlonkVerifier.
Module M := MultiopenVerifier.
Module C := CommitmentVerifier.
Module I := IpaVerifier.

Local Notation "x <- result ;; next" :=
  (Result.bind result (fun x => next))
  (at level 100, result at next level, right associativity).

Fixpoint read_n_points (count : nat) (transcript : Transcript.t) :
    Result.t (list Point.t * Transcript.t) :=
  match count with
  | O => Result.Ok ([], transcript)
  | S count' =>
      Result.bind (Transcript.read_point transcript)
        (fun '(point, transcript') =>
          Result.map (fun '(points, final_transcript) =>
            (point :: points, final_transcript))
            (read_n_points count' transcript'))
  end.

Fixpoint read_n_scalars (count : nat) (transcript : Transcript.t) :
    Result.t (list Scalar.t * Transcript.t) :=
  match count with
  | O => Result.Ok ([], transcript)
  | S count' =>
      Result.bind (Transcript.read_scalar transcript)
        (fun '(scalar, transcript') =>
          Result.map (fun '(scalars, final_transcript) =>
            (scalar :: scalars, final_transcript))
            (read_n_scalars count' transcript'))
  end.

Fixpoint read_point_matrix (rows columns : nat) (transcript : Transcript.t) :
    Result.t (list (list Point.t) * Transcript.t) :=
  match rows with
  | O => Result.Ok ([], transcript)
  | S rows' =>
      Result.bind (read_n_points columns transcript)
        (fun '(row, transcript') =>
          Result.map (fun '(tail, final_transcript) =>
            (row :: tail, final_transcript))
            (read_point_matrix rows' columns transcript'))
  end.

Fixpoint read_scalar_matrix (rows columns : nat) (transcript : Transcript.t) :
    Result.t (list (list Scalar.t) * Transcript.t) :=
  match rows with
  | O => Result.Ok ([], transcript)
  | S rows' =>
      Result.bind (read_n_scalars columns transcript)
        (fun '(row, transcript') =>
          Result.map (fun '(tail, final_transcript) =>
            (row :: tail, final_transcript))
            (read_scalar_matrix rows' columns transcript'))
  end.

Record lookup_permuted : Type := {
  lookup_input_commitment : Point.t;
  lookup_table_commitment : Point.t;
}.

Fixpoint read_lookup_permuted (count : nat) (transcript : Transcript.t) :
    Result.t (list lookup_permuted * Transcript.t) :=
  match count with
  | O => Result.Ok ([], transcript)
  | S count' =>
      Result.bind (Transcript.read_point transcript)
        (fun '(input, transcript') =>
          Result.bind (Transcript.read_point transcript')
            (fun '(table, transcript'') =>
              Result.map (fun '(tail, final_transcript) =>
                ({| lookup_input_commitment := input;
                    lookup_table_commitment := table |} :: tail,
                 final_transcript))
                (read_lookup_permuted count' transcript'')))
  end.

Fixpoint read_lookup_permuted_matrix (proofs lookups : nat)
    (transcript : Transcript.t) :
    Result.t (list (list lookup_permuted) * Transcript.t) :=
  match proofs with
  | O => Result.Ok ([], transcript)
  | S proofs' =>
      Result.bind (read_lookup_permuted lookups transcript)
        (fun '(row, transcript') =>
          Result.map (fun '(tail, final_transcript) =>
            (row :: tail, final_transcript))
            (read_lookup_permuted_matrix proofs' lookups transcript'))
  end.

Record permutation_set_evals : Type := {
  permutation_product_eval : Scalar.t;
  permutation_product_next_eval : Scalar.t;
  permutation_product_last_eval : option Scalar.t;
}.

Fixpoint read_permutation_set_evals (set_count : nat)
    (transcript : Transcript.t) :
    Result.t (list permutation_set_evals * Transcript.t) :=
  match set_count with
  | O => Result.Ok ([], transcript)
  | S O =>
      Result.bind (Transcript.read_scalar transcript)
        (fun '(value, transcript') =>
          Result.map (fun '(next, final_transcript) =>
            ([{| permutation_product_eval := value;
                 permutation_product_next_eval := next;
                 permutation_product_last_eval := None |}],
             final_transcript))
            (Transcript.read_scalar transcript'))
  | S (S remaining as tail_count) =>
      Result.bind (Transcript.read_scalar transcript)
        (fun '(value, transcript') =>
          Result.bind (Transcript.read_scalar transcript')
            (fun '(next, transcript'') =>
              Result.bind (Transcript.read_scalar transcript'')
                (fun '(last, transcript''') =>
                  Result.map (fun '(tail, final_transcript) =>
                    ({| permutation_product_eval := value;
                        permutation_product_next_eval := next;
                        permutation_product_last_eval := Some last |} :: tail,
                     final_transcript))
                    (read_permutation_set_evals tail_count transcript'''))))
  end.

Fixpoint read_permutation_eval_matrix (proofs set_count : nat)
    (transcript : Transcript.t) :
    Result.t (list (list permutation_set_evals) * Transcript.t) :=
  match proofs with
  | O => Result.Ok ([], transcript)
  | S proofs' =>
      Result.bind (read_permutation_set_evals set_count transcript)
        (fun '(row, transcript') =>
          Result.map (fun '(tail, final_transcript) =>
            (row :: tail, final_transcript))
            (read_permutation_eval_matrix proofs' set_count transcript'))
  end.

Record lookup_evals : Type := {
  lookup_product_eval : Scalar.t;
  lookup_product_next_eval : Scalar.t;
  lookup_permuted_input_eval : Scalar.t;
  lookup_permuted_input_inv_eval : Scalar.t;
  lookup_permuted_table_eval : Scalar.t;
}.

Definition lookup_evals_of_list (values : list Scalar.t) : option lookup_evals :=
  match values with
  | [product; product_next; input; input_inv; table] => Some {|
      lookup_product_eval := product;
      lookup_product_next_eval := product_next;
      lookup_permuted_input_eval := input;
      lookup_permuted_input_inv_eval := input_inv;
      lookup_permuted_table_eval := table
    |}
  | _ => None
  end.

Fixpoint read_lookup_evals (count : nat) (transcript : Transcript.t) :
    Result.t (list lookup_evals * Transcript.t) :=
  match count with
  | O => Result.Ok ([], transcript)
  | S count' =>
      Result.bind (read_n_scalars 5 transcript)
        (fun '(values, transcript') =>
          match lookup_evals_of_list values with
          | None => Reader.panic Panic.InternalInvariant transcript'.(Transcript.reader)
          | Some value =>
              Result.map (fun '(tail, final_transcript) =>
                (value :: tail, final_transcript))
                (read_lookup_evals count' transcript')
          end)
  end.

Fixpoint read_lookup_eval_matrix (proofs lookups : nat)
    (transcript : Transcript.t) :
    Result.t (list (list lookup_evals) * Transcript.t) :=
  match proofs with
  | O => Result.Ok ([], transcript)
  | S proofs' =>
      Result.bind (read_lookup_evals lookups transcript)
        (fun '(row, transcript') =>
          Result.map (fun '(tail, final_transcript) =>
            (row :: tail, final_transcript))
            (read_lookup_eval_matrix proofs' lookups transcript'))
  end.

Record plonk_prefix : Type := {
  parsed_advice_commitments : list (list Point.t);
  challenge_theta : Scalar.t;
  parsed_lookup_permuted : list (list lookup_permuted);
  challenge_beta : Scalar.t;
  challenge_gamma : Scalar.t;
  parsed_permutation_product_commitments : list (list Point.t);
  parsed_lookup_product_commitments : list (list Point.t);
  parsed_random_poly_commitment : Point.t;
  challenge_y : Scalar.t;
  parsed_h_commitments : list Point.t;
  challenge_x : Scalar.t;
  parsed_instance_evals : list (list Scalar.t);
  parsed_advice_evals : list (list Scalar.t);
  parsed_fixed_evals : list Scalar.t;
  parsed_random_eval : Scalar.t;
  parsed_common_permutation_evals : list Scalar.t;
  parsed_permutation_evals : list (list permutation_set_evals);
  parsed_lookup_evals : list (list lookup_evals);
}.

(** This nesting is intentionally linear: its source order is the Rust read
    order, and each transcript state is consumed exactly once. *)
Definition read_plonk_prefix (shape : P.verifying_key_shape) (num_proofs : nat)
    (transcript : Transcript.t) : Result.t (plonk_prefix * Transcript.t) :=
  let permutation_sets :=
    ((List.length shape.(P.vk_permutation_columns) +
      (shape.(P.vk_cs_degree) - 2) - 1) /
      (shape.(P.vk_cs_degree) - 2))%nat in
  advice_read <-
    read_point_matrix num_proofs shape.(P.vk_num_advice_columns) transcript ;;
  let '(advice, t1) := advice_read in
  let '(theta, t2) := Transcript.squeeze_challenge t1 in
  lookup_permuted_read <-
    read_lookup_permuted_matrix num_proofs shape.(P.vk_lookup_count) t2 ;;
  let '(lookup_permuted, t3) := lookup_permuted_read in
  let '(beta, t4) := Transcript.squeeze_challenge t3 in
  let '(gamma, t5) := Transcript.squeeze_challenge t4 in
  permutation_products_read <-
    read_point_matrix num_proofs permutation_sets t5 ;;
  let '(permutation_products, t6) := permutation_products_read in
  lookup_products_read <-
    read_point_matrix num_proofs shape.(P.vk_lookup_count) t6 ;;
  let '(lookup_products, t7) := lookup_products_read in
  random_read <- Transcript.read_point t7 ;;
  let '(random_commitment, t8) := random_read in
  let '(y, t9) := Transcript.squeeze_challenge t8 in
  h_read <- read_n_points shape.(P.vk_quotient_poly_degree) t9 ;;
  let '(h_commitments, t10) := h_read in
  let '(x, t11) := Transcript.squeeze_challenge t10 in
  instance_read <- read_scalar_matrix num_proofs
    (List.length shape.(P.vk_instance_queries)) t11 ;;
  let '(instance_evals, t12) := instance_read in
  advice_evals_read <- read_scalar_matrix num_proofs
    (List.length shape.(P.vk_advice_queries)) t12 ;;
  let '(advice_evals, t13) := advice_evals_read in
  fixed_read <- read_n_scalars (List.length shape.(P.vk_fixed_queries)) t13 ;;
  let '(fixed_evals, t14) := fixed_read in
  random_eval_read <- Transcript.read_scalar t14 ;;
  let '(random_eval, t15) := random_eval_read in
  common_read <- read_n_scalars
    (List.length shape.(P.vk_permutation_columns)) t15 ;;
  let '(common_permutation_evals, t16) := common_read in
  permutation_evals_read <-
    read_permutation_eval_matrix num_proofs permutation_sets t16 ;;
  let '(permutation_evals, t17) := permutation_evals_read in
  lookup_evals_read <-
    read_lookup_eval_matrix num_proofs shape.(P.vk_lookup_count) t17 ;;
  let '(lookup_evals, final_transcript) := lookup_evals_read in
  Result.Ok ({|
    parsed_advice_commitments := advice;
    challenge_theta := theta;
    parsed_lookup_permuted := lookup_permuted;
    challenge_beta := beta;
    challenge_gamma := gamma;
    parsed_permutation_product_commitments := permutation_products;
    parsed_lookup_product_commitments := lookup_products;
    parsed_random_poly_commitment := random_commitment;
    challenge_y := y;
    parsed_h_commitments := h_commitments;
    challenge_x := x;
    parsed_instance_evals := instance_evals;
    parsed_advice_evals := advice_evals;
    parsed_fixed_evals := fixed_evals;
    parsed_random_eval := random_eval;
    parsed_common_permutation_evals := common_permutation_evals;
    parsed_permutation_evals := permutation_evals;
    parsed_lookup_evals := lookup_evals
  |}, final_transcript).

Definition scalar_Z (scalar : Scalar.t) : F.t := scalar.(Scalar.value).

Record multiopen_prefix : Type := {
  challenge_x_1 : Scalar.t;
  challenge_x_2 : Scalar.t;
  q_prime_commitment : Point.t;
  challenge_x_3 : Scalar.t;
  proof_u : list Scalar.t;
  challenge_x_4 : Scalar.t;
}.

Definition read_multiopen_after_x_2 (point_set_count : nat)
    (x_1 x_2 : Scalar.t) (transcript : Transcript.t) :
    Result.t (multiopen_prefix * Transcript.t) :=
  Result.bind (Transcript.read_point transcript)
    (fun '(q_prime, t3) =>
      let '(x_3, t4) := Transcript.squeeze_challenge t3 in
      Result.map (fun '(u, t5) =>
        let '(x_4, t6) := Transcript.squeeze_challenge t5 in
        ({| challenge_x_1 := x_1; challenge_x_2 := x_2;
            q_prime_commitment := q_prime; challenge_x_3 := x_3;
            proof_u := u; challenge_x_4 := x_4 |}, t6))
        (read_n_scalars point_set_count t4)).

Definition read_multiopen_prefix (point_set_count : nat)
    (transcript : Transcript.t) : Result.t (multiopen_prefix * Transcript.t) :=
  let '(x_1, t1) := Transcript.squeeze_challenge transcript in
  let '(x_2, t2) := Transcript.squeeze_challenge t1 in
  read_multiopen_after_x_2 point_set_count x_1 x_2 t2.

Fixpoint read_ipa_rounds (count : nat) (transcript : Transcript.t) :
    Result.t (list I.round * Transcript.t) :=
  match count with
  | O => Result.Ok ([], transcript)
  | S count' =>
      Result.bind (Transcript.read_point transcript)
        (fun '(l, t1) =>
          Result.bind (Transcript.read_point t1)
            (fun '(r, t2) =>
              let '(u, t3) := Transcript.squeeze_challenge t2 in
              Result.map (fun '(tail, final_transcript) =>
                ({| I.round_l := l; I.round_r := r; I.round_u := scalar_Z u |}
                  :: tail, final_transcript))
                (read_ipa_rounds count' t3)))
  end.

Definition read_ipa (k : nat) (transcript : Transcript.t) :
    Result.t (I.proof * Transcript.t) :=
  Result.bind (Transcript.read_point transcript)
    (fun '(s, t1) =>
      let '(xi, t2) := Transcript.squeeze_challenge t1 in
      let '(z, t3) := Transcript.squeeze_challenge t2 in
      Result.bind (read_ipa_rounds k t3)
        (fun '(rounds, t4) =>
          Result.bind (Transcript.read_scalar t4)
            (fun '(c, t5) =>
              Result.map (fun '(f, t6) =>
                ({| I.s_poly_commitment := s; I.xi := scalar_Z xi;
                    I.z := scalar_Z z; I.rounds := rounds;
                    I.c := scalar_Z c; I.f := scalar_Z f |}, t6))
                (Transcript.read_scalar t5)))).

Inductive resolved_commitment : Type :=
| ResolvedPoint (point : C.point)
| ResolvedMsm (msm : C.msm).

Record assembly : Type := {
  assembly_queries : list P.verifier_query;
  assembly_initial_terms : M.symbolic_msm;
  assembly_q_prime_key : P.commitment_key;
  assembly_resolve : P.commitment_key -> option resolved_commitment;
}.

Inductive assembly_result : Type :=
| AssemblyReady (value : assembly)
| AssemblyUnavailable
| AssemblyPanicked (reason : Panic.reason).

Record backend : Type := {
  assemble_plonk : plonk_prefix -> assembly_result;
}.

Fixpoint resolve_terms (resolve : P.commitment_key -> option resolved_commitment)
    (terms : M.symbolic_msm) (state : C.msm) : C.msm_result :=
  match terms with
  | [] => C.MsmOk state
  | (scalar, key) :: terms' =>
      match resolve key with
      | None => C.MsmPanicked (C.GeneratorScalarLengthMismatch 0 1)
      | Some (ResolvedPoint point) =>
          match C.append_term scalar point state with
          | C.MsmPanicked failure => C.MsmPanicked failure
          | C.MsmOk state' => resolve_terms resolve terms' state'
          end
      | Some (ResolvedMsm value) =>
          match C.add_msm (C.scale scalar value) state with
          | C.MsmPanicked failure => C.MsmPanicked failure
          | C.MsmOk state' => resolve_terms resolve terms' state'
          end
      end
  end.

Definition reject_here {A : Type} (transcript : Transcript.t) : Result.t A :=
  Reader.reject Reject.VerificationFailure transcript.(Transcript.reader).

Definition panic_here {A : Type} (reason : Panic.reason)
    (transcript : Transcript.t) : Result.t A :=
  Reader.panic reason transcript.(Transcript.reader).

(** Execute multiopen through IPA from an already assembled PLONK state. *)
Definition finish (shape : P.verifying_key_shape) (assembled : assembly)
    (transcript : Transcript.t) : Result.t (C.msm * Transcript.t) :=
  (** Rust samples both compression challenges before attempting the
      allocation-identity grouping.  This ordering is observable on the
      duplicate-query rejection path through the transcript trace. *)
  let '(x_1, t_x_1) := Transcript.squeeze_challenge transcript in
  let '(x_2, t_x_2) := Transcript.squeeze_challenge t_x_1 in
  match M.construct_intermediate_sets assembled.(assembly_queries) with
  | M.DuplicateCommitmentPointQuery | M.InternalGroupingFailure => reject_here t_x_2
  | M.IntermediateSets intermediate =>
      let point_set_count := List.length intermediate.(M.is_point_sets) in
      match M.compress_intermediate (scalar_Z x_1) intermediate with
      | None => panic_here Panic.InternalInvariant t_x_2
      | Some compressed =>
          Result.bind (Transcript.read_point t_x_2)
            (fun '(q_prime, t3) =>
              let '(x_3, t4) := Transcript.squeeze_challenge t3 in
              Result.bind (read_n_scalars point_set_count t4)
                (fun '(u, t5) =>
                  let u_values := map scalar_Z u in
                  match M.expected_msm_eval
                    (scalar_Z x_2) (scalar_Z x_3) intermediate compressed
                    u_values with
                  | M.X3CollidesWithOpeningPoint =>
                      panic_here Panic.DivisionByZero t5
                  | M.InvalidInterpolationShape =>
                      panic_here Panic.InternalInvariant t5
                  | M.ExpectedEval msm_eval =>
                      let '(x_4, t6) := Transcript.squeeze_challenge t5 in
                      match M.make_opening_claim
                        assembled.(assembly_q_prime_key)
                        (scalar_Z x_3) (scalar_Z x_4) compressed u_values
                        assembled.(assembly_initial_terms) msm_eval with
                      | None => panic_here
                          (Panic.LengthMismatch (List.length compressed)
                            (List.length u)) t6
                      | Some claim =>
                          match resolve_terms
                            (fun key =>
                              if P.commitment_key_eqb key
                                   assembled.(assembly_q_prime_key)
                              then Some (ResolvedPoint q_prime)
                              else assembled.(assembly_resolve) key)
                            claim.(M.claim_terms) (C.empty shape.(P.vk_n)) with
                          | C.MsmPanicked _ =>
                              panic_here Panic.InternalInvariant t6
                          | C.MsmOk state =>
                              Result.bind (read_ipa shape.(P.vk_k) t6)
                                (fun '(ipa, t7) =>
                                  match I.verify claim.(M.claim_point)
                                    claim.(M.claim_value) ipa state with
                                  | I.IpaPanicked _ =>
                                      panic_here Panic.InternalInvariant t7
                                  | I.IpaGuard guard =>
                                      match I.use_challenges guard with
                                      | I.IpaPanicked _ =>
                                          panic_here Panic.InternalInvariant t7
                                      | I.IpaGuard final =>
                                          Result.Ok (final.(I.guard_msm), t7)
                                      end
                                  end)
                          end
                      end
                  end)
            )
      end
  end.

End ReferenceVerifier.
