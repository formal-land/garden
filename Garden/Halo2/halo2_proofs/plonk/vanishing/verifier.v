(** * Vanishing-argument verifier

    Transcription of [halo2_proofs/src/plonk/vanishing/verifier.rs].
    The Horner fold [h_eval * y + v] is a list fold; the [h] commitment
    is accumulated as an MSM by scaling by [x^n] and appending each
    piece, in reverse. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Import Garden.Halo2.halo2_proofs.poly.multiopen.
Require Import Garden.Halo2.halo2_proofs.plonk.

Import List.ListNotations.
Global Open Scope Z_scope.

Module VanishingVerifier.

  Record Committed : Set := {
    random_poly_commitment : VestaCurve.point;
  }.

  Record Constructed : Set := {
    h_commitments : list VestaCurve.point;
    constructed_random : VestaCurve.point;
  }.

  Record PartiallyEvaluated : Set := {
    pe_h_commitments : list VestaCurve.point;
    pe_random_poly_commitment : VestaCurve.point;
    random_eval : Z;
  }.

  Record Evaluated : Set := {
    h_commitment : MSM.t;
    ev_random_poly_commitment : VestaCurve.point;
    expected_h_eval : Z;
    ev_random_eval : Z;
  }.

  Definition read_commitments_before_y (tr : Blake2bRead.t) :
      Result.t (Committed * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(P, tr) =>
      Result.Ok ({| random_poly_commitment := P |}, tr))
      (Blake2bRead.read_point tr).

  Definition read_commitments_after_y (self : Committed) (vk : VerifyingKey.t)
      (tr : Blake2bRead.t) :
      Result.t (Constructed * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(hs, tr) =>
      Result.Ok
        ({| h_commitments := hs;
            constructed_random := self.(random_poly_commitment) |}, tr))
      (Blake2bRead.read_n_points tr
        (EvaluationDomain.get_quotient_poly_degree vk.(VerifyingKey.domain))).

  Definition evaluate_after_x (self : Constructed) (tr : Blake2bRead.t) :
      Result.t (PartiallyEvaluated * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(random_eval, tr) =>
      Result.Ok
        ({| pe_h_commitments := self.(h_commitments);
            pe_random_poly_commitment := self.(constructed_random);
            random_eval := random_eval |}, tr))
      (Blake2bRead.read_scalar tr).

  Definition verify (self : PartiallyEvaluated) (params : Params.t)
      (expressions : list Z) (y xn : Z) : Evaluated :=
    let expected_h_eval :=
      List.fold_left (fun h_eval v => h_eval *s y +s v) expressions 0 in
    let expected_h_eval :=
      match Fp.invert (xn -s 1) with
      | Some inv => expected_h_eval *s inv
      | None => expected_h_eval
      end in
    let h_commitment :=
      List.fold_left (fun acc commitment =>
        let acc := MSM.scale acc xn in
        MSM.append_term acc 1 commitment)
        (List.rev self.(pe_h_commitments))
        (empty_msm params) in
    {| h_commitment := h_commitment;
       ev_random_poly_commitment := self.(pe_random_poly_commitment);
       expected_h_eval := expected_h_eval;
       ev_random_eval := self.(random_eval) |}.

  Definition queries (self : Evaluated) (x : Z) (h_id rand_id : nat) :
      list Multiopen.VerifierQuery :=
    [ Multiopen.new_msm h_id self.(h_commitment) x self.(expected_h_eval);
      Multiopen.new_commitment rand_id self.(ev_random_poly_commitment) x self.(ev_random_eval) ].
End VanishingVerifier.
