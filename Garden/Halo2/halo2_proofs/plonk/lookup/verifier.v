(** * Lookup-argument verifier

    Transcription of [halo2_proofs/src/plonk/lookup/verifier.rs]. Each
    lookup contributes five expressions and five opening queries, in the
    Rust iterator order. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.multiopen.
Require Import Garden.Halo2.halo2_proofs.plonk.

Import List.ListNotations.
Global Open Scope Z_scope.

Module LookupVerifier.

  Record PermutationCommitments : Set := {
    permuted_input_commitment : VestaCurve.point;
    permuted_table_commitment : VestaCurve.point;
  }.

  Record Committed : Set := {
    permuted : PermutationCommitments;
    product_commitment : VestaCurve.point;
  }.

  Record Evaluated : Set := {
    committed : Committed;
    product_eval : Z;
    product_next_eval : Z;
    permuted_input_eval : Z;
    permuted_input_inv_eval : Z;
    permuted_table_eval : Z;
  }.

  Definition read_permuted_commitments (tr : Blake2bRead.t) :
      Result.t (PermutationCommitments * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(a, tr) =>
    Result.and_then (fun '(s, tr) =>
      Result.Ok ({| permuted_input_commitment := a; permuted_table_commitment := s |}, tr))
      (Blake2bRead.read_point tr))
      (Blake2bRead.read_point tr).

  Definition read_product_commitment (self : PermutationCommitments) (tr : Blake2bRead.t) :
      Result.t (Committed * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(p, tr) =>
      Result.Ok ({| permuted := self; product_commitment := p |}, tr))
      (Blake2bRead.read_point tr).

  Definition evaluate (self : Committed) (tr : Blake2bRead.t) :
      Result.t (Evaluated * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(product_eval, tr) =>
    Result.and_then (fun '(product_next_eval, tr) =>
    Result.and_then (fun '(permuted_input_eval, tr) =>
    Result.and_then (fun '(permuted_input_inv_eval, tr) =>
    Result.and_then (fun '(permuted_table_eval, tr) =>
      Result.Ok
        ({| committed := self;
            product_eval := product_eval;
            product_next_eval := product_next_eval;
            permuted_input_eval := permuted_input_eval;
            permuted_input_inv_eval := permuted_input_inv_eval;
            permuted_table_eval := permuted_table_eval |}, tr))
      (Blake2bRead.read_scalar tr))
      (Blake2bRead.read_scalar tr))
      (Blake2bRead.read_scalar tr))
      (Blake2bRead.read_scalar tr))
      (Blake2bRead.read_scalar tr).

  Definition compress_expressions (theta : Z) (exprs : list Expression.t)
      (advice_evals fixed_evals instance_evals : list Z) : Z :=
    List.fold_left (fun acc e =>
      acc *s theta +s Expression.evaluate e fixed_evals advice_evals instance_evals)
      exprs 0.

  Definition expressions (self : Evaluated) (argument : LookupArgument.t)
      (l_0 l_last l_blind theta beta gamma : Z)
      (advice_evals fixed_evals instance_evals : list Z) : list Z :=
    let active_rows := 1 -s (l_last +s l_blind) in
    let left :=
      self.(product_next_eval)
        *s (self.(permuted_input_eval) +s beta)
        *s (self.(permuted_table_eval) +s gamma) in
    let right :=
      self.(product_eval)
        *s (compress_expressions theta argument.(LookupArgument.input_expressions)
              advice_evals fixed_evals instance_evals +s beta)
        *s (compress_expressions theta argument.(LookupArgument.table_expressions)
              advice_evals fixed_evals instance_evals +s gamma) in
    [ l_0 *s (1 -s self.(product_eval));
      l_last *s (self.(product_eval) *s self.(product_eval) -s self.(product_eval));
      (left -s right) *s active_rows;
      l_0 *s (self.(permuted_input_eval) -s self.(permuted_table_eval));
      (self.(permuted_input_eval) -s self.(permuted_table_eval))
        *s (self.(permuted_input_eval) -s self.(permuted_input_inv_eval))
        *s active_rows ].

  Definition queries (self : Evaluated) (vk : VerifyingKey.t) (x : Z)
      (prod_id input_id table_id : nat) : list Multiopen.VerifierQuery :=
    let x_inv := EvaluationDomain.rotate_omega vk.(VerifyingKey.domain) x Rotation.prev in
    let x_next := EvaluationDomain.rotate_omega vk.(VerifyingKey.domain) x Rotation.next in
    [ Multiopen.new_commitment prod_id self.(committed).(product_commitment) x self.(product_eval);
      Multiopen.new_commitment input_id
        self.(committed).(permuted).(permuted_input_commitment) x self.(permuted_input_eval);
      Multiopen.new_commitment table_id
        self.(committed).(permuted).(permuted_table_commitment) x self.(permuted_table_eval);
      Multiopen.new_commitment input_id
        self.(committed).(permuted).(permuted_input_commitment) x_inv self.(permuted_input_inv_eval);
      Multiopen.new_commitment prod_id
        self.(committed).(product_commitment) x_next self.(product_next_eval) ].
End LookupVerifier.
