(** * Post-NU6.3 Orchard adapter for the Halo2 verifier model

    The public statement is one ten-scalar instance column per Orchard action.
    This module fixes the deployed domain, query tables, selector-compressed
    gate expressions, VK commitments, and SRS from Garden's existing certified
    data.  [verify_post_nu6_3_report_Z] is the deliberately parser-only
    diagnostic retained for read-schedule snapshots: successful parsing
    returns [BackendUnavailable], never [Verified].
    [verify_post_nu6_3_with_backend_Z] can only return [Verified] after its
    explicit PLONK assembly backend and the final Garden MSM both succeed;
    [Garden.Orchard.Verifier.Verifier] installs the fixed backend as the
    user-facing default. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Reader.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Transcript.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Lookup.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Eval.Commitment.
Require Import Garden.Halo2.Verifier.IPA.
Require Import Garden.Halo2.Verifier.Reference.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.vk.parameters.
Require Import Garden.Orchard.vk.data.
Require Import Garden.Orchard.vk.transcript_repr.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.Verifier.Eval.Checked.
Require Import Garden.Orchard.Verifier.Eval.InstanceCommitment.
Require Import Garden.Orchard.Verifier.PostNu6_3Data.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module OrchardPostNu63.

Module F := VerifierField.
Module P := PlonkVerifier.
Module C := CommitmentVerifier.
Module R := ReferenceVerifier.
Module I := IpaVerifier.

Definition query_of_pair (kind : P.column_kind) (query : Z * Z) : P.query_spec := {|
  P.query_column := {|
    P.column_type := kind;
    P.column_index := Z.to_nat (fst query)
  |};
  P.query_rotation := snd query
|}.

Definition raw_column (column : Raw.ColumnRef.t) : P.column := {|
  P.column_type :=
    match column.(Raw.ColumnRef.kind) with
    | Raw.ColumnKind.Advice => P.Advice
    | Raw.ColumnKind.Fixed => P.Fixed
    | Raw.ColumnKind.Instance_ => P.Instance
    end;
  P.column_index := Z.to_nat column.(Raw.ColumnRef.index)
|}.

Fixpoint query_index_from (needle : Z * Z) (queries : list (Z * Z))
    (index : nat) : option nat :=
  match queries with
  | [] => None
  | query :: queries' =>
      if (fst needle =? fst query) && (snd needle =? snd query)
      then Some index
      else query_index_from needle queries' (S index)
  end.

(** Named leaves keep executable clients from projecting through the large
    transparent compiled-system and verifying-key records. *)
Definition instance_query_pairs : list (Z * Z) :=
  OrchardCompiledPinned.instance_queries.
Definition advice_query_pairs : list (Z * Z) :=
  OrchardCompiledPinned.advice_queries.
Definition fixed_query_pairs : list (Z * Z) :=
  OrchardCompiledPinned.fixed_queries.
Definition permutation_columns : list Raw.ColumnRef.t :=
  OrchardCompiledPinned.permutation_columns.

(** Compact runtime leaves are checked against the formal circuit derivation
    in [PostNu6_3Materialization.v], outside this executable dependency
    closure. *)
Definition lookup_descriptions : list LookupVerifier.argument :=
  OrchardPostNu63Data.lookup_descriptions.

Definition instance_query_specs : list P.query_spec :=
  map (query_of_pair P.Instance) instance_query_pairs.
Definition advice_query_specs : list P.query_spec :=
  map (query_of_pair P.Advice) advice_query_pairs.
Definition fixed_query_specs : list P.query_spec :=
  map (query_of_pair P.Fixed) fixed_query_pairs.
Definition domain_n : nat := OrchardVkParameters.n.
Definition blinding_factors : nat := 5.

Definition gate_polynomials : list (list P.expression) :=
  OrchardPostNu63Data.gate_polynomials.

Definition shape : P.verifying_key_shape := {|
  P.vk_k := OrchardVkParameters.k;
  P.vk_n := domain_n;
  P.vk_cs_degree := 9;
  P.vk_num_instance_columns := 1;
  P.vk_num_advice_columns := 10;
  P.vk_instance_queries := instance_query_specs;
  P.vk_advice_queries := advice_query_specs;
  P.vk_fixed_queries := fixed_query_specs;
  P.vk_gate_polynomials := gate_polynomials;
  P.vk_permutation_columns := map raw_column permutation_columns;
  P.vk_lookup_count := 3;
  P.vk_blinding_factors := blinding_factors;
  P.vk_quotient_poly_degree := 8;
|}.

Definition fixed_commitments : list Point.t :=
  map (fun coordinates => Point.affine (fst coordinates) (snd coordinates))
    VkPinnedData.fixed_commitments.

Definition permutation_commitments : list Point.t :=
  map (fun coordinates => Point.affine (fst coordinates) (snd coordinates))
    VkPinnedData.permutation_commitments.

Definition parameters : C.parameters := {|
  C.parameter_g := VkMsm.g_points;
  C.parameter_w := VkMsm.w_point;
  C.parameter_u := VkMsm.u_point;
|}.

Definition action_width : nat := 10.
Definition maximum_instance_rows : nat := 2042.

Inductive input_error : Type :=
| InvalidProofByte
    (position : nat) (value : Z)
| InvalidActionWidth
    (action expected actual : nat)
| NonCanonicalActionScalar
    (action field : nat) (value : Z)
| NonBooleanActionFlag
    (action field : nat) (value : Z).

Fixpoint first_invalid_scalar (field : nat) (values : list Z) :
    option (nat * Z) :=
  match values with
  | [] => None
  | value :: values' =>
      if (0 <=? value) && (value <? Primes.pallas_p)
      then first_invalid_scalar (S field) values'
      else Some (field, value)
  end.

Definition boolean_scalarb (value : Z) : bool :=
  (value =? 0) || (value =? 1).

Definition first_invalid_flag (values : list Z) : option (nat * Z) :=
  match nth_error values 7, nth_error values 8, nth_error values 9 with
  | Some spend, Some output, Some disable_cross_address =>
      if boolean_scalarb spend then
        if boolean_scalarb output then
          if boolean_scalarb disable_cross_address then None
          else Some (9%nat, disable_cross_address)
        else Some (8%nat, output)
      else Some (7%nat, spend)
  | _, _, _ => None
  end.

Fixpoint validate_actions_from (action : nat) (actions : list (list Z)) :
    option input_error :=
  match actions with
  | [] => None
  | values :: actions' =>
      if Nat.eqb (List.length values) action_width then
        match first_invalid_scalar 0 values with
        | Some (field, value) =>
            Some (NonCanonicalActionScalar action field value)
        | None =>
            match first_invalid_flag values with
            | Some (field, value) => Some (NonBooleanActionFlag action field value)
            | None => validate_actions_from (S action) actions'
            end
        end
      else Some (InvalidActionWidth action action_width (List.length values))
  end.

Fixpoint first_invalid_byte (position : nat) (bytes : list Z) :
    option input_error :=
  match bytes with
  | [] => None
  | byte :: bytes' =>
      if (0 <=? byte) && (byte <=? 255)
      then first_invalid_byte (S position) bytes'
      else Some (InvalidProofByte position byte)
  end.

Definition zero_pad_instance (values : list Z) : list Z :=
  values ++ List.repeat 0 (OrchardVkParameters.n - List.length values).

(** Rust-shaped coefficient-side [commit_lagrange] retained as the auditable
    reference and as the fallback for inputs outside the optimized kernel's
    checked boundary. *)
Definition instance_commitment_reference (values : list Z) : Point.t :=
  OrchardInstanceCommitmentEval.reference_commitment
    (zero_pad_instance values).

(** The primitive evaluator checks that padding produced exactly 2^11
    canonical Pallas scalars before using its array FFT and fixed-SRS
    Pippenger kernel.  Its refinement to [instance_commitment_reference] is
    instantiated with the generated Orchard certificates in the proof-only
    assurance layer.  The unchecked case follows the reference definition. *)
Definition instance_commitment (values : list Z) : Point.t :=
  let padded_values := zero_pad_instance values in
  match OrchardInstanceCommitmentEval.evaluate_checked padded_values with
  | Some commitment => commitment
  | None => instance_commitment_reference values
  end.

Fixpoint absorb_instance_commitments (actions : list (list Z))
    (transcript : Transcript.t) : Result.t Transcript.t :=
  match actions with
  | [] => Result.Ok transcript
  | values :: actions' =>
      Result.bind (Transcript.common_point (instance_commitment values) transcript)
        (absorb_instance_commitments actions')
  end.

Definition initialize_transcript (proof : list Z) (actions : list (list Z)) :
    Result.t Transcript.t :=
  Result.bind (Transcript.init_Z proof)
    (fun transcript =>
      Result.bind
        (Transcript.common_scalar (Scalar.of_Z VkTranscriptRepr.transcript_repr)
          transcript)
        (absorb_instance_commitments actions)).

Inductive verification_report : Type :=
| InputRejected (failure : input_error)
| TranscriptRejected (reason : Reject.reason) (offset : nat)
| OpeningRejected (reason : Reject.reason) (offset : nat)
| VerifierPanicked (reason : Panic.reason) (offset : nat)
| BackendUnavailable
    (actions consumed remaining : nat)
| VerificationRejected (offset : nat)
| Verified (consumed trailing : nat).

Definition report_result {A : Type} (on_ok : A -> verification_report)
    (result : Result.t A) : verification_report :=
  match result with
  | Result.Ok value => on_ok value
  | Result.Rejected failure =>
      TranscriptRejected failure.(Reject.reason_of) failure.(Reject.offset)
  | Result.Panicked failure =>
      VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
  end.

Definition parse_post_nu6_3_Z (proof : list Z) (actions : list (list Z)) :
    Result.t (R.plonk_prefix * Transcript.t) :=
  Result.bind (initialize_transcript proof actions)
    (R.read_plonk_prefix shape (List.length actions)).

Record full_parse : Type := {
  full_plonk : R.plonk_prefix;
  full_multiopen : R.multiopen_prefix;
  full_ipa : I.proof;
  full_transcript : Transcript.t;
}.

(** Read-schedule diagnostic for ordinary nonzero evaluation challenges.  The
    concrete backend derives point sets dynamically: for adversarial [x = 0],
    rotated points can coincide and this fixed count is intentionally not used
    as a verification boundary. *)
Definition post_nu6_3_point_set_count : nat := 5.

Definition parse_full_post_nu6_3_Z (proof : list Z)
    (actions : list (list Z)) : Result.t full_parse :=
  Result.bind (parse_post_nu6_3_Z proof actions)
    (fun '(plonk, transcript) =>
      Result.bind
        (R.read_multiopen_prefix post_nu6_3_point_set_count transcript)
        (fun '(multiopen, transcript') =>
          Result.map
            (fun '(ipa, final_transcript) => {|
              full_plonk := plonk;
              full_multiopen := multiopen;
              full_ipa := ipa;
              full_transcript := final_transcript
            |})
            (R.read_ipa shape.(P.vk_k) transcript'))).

(** Stable snapshot boundary.  Trailing bytes are intentionally not checked:
    low-level Orchard [Proof::verify] leaves them unread. *)
Definition verify_post_nu6_3_report_Z (proof : list Z)
    (actions : list (list Z)) : verification_report :=
  match first_invalid_byte 0 proof with
  | Some failure => InputRejected failure
  | None =>
      match validate_actions_from 0 actions with
      | Some failure => InputRejected failure
      | None =>
          match initialize_transcript proof actions with
          | Result.Rejected failure =>
              TranscriptRejected failure.(Reject.reason_of) failure.(Reject.offset)
          | Result.Panicked failure =>
              VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
          | Result.Ok transcript =>
              match R.read_plonk_prefix shape (List.length actions) transcript with
              | Result.Rejected failure =>
                  TranscriptRejected failure.(Reject.reason_of) failure.(Reject.offset)
              | Result.Panicked failure =>
                  VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
              | Result.Ok (_, transcript') =>
                  match R.read_multiopen_prefix post_nu6_3_point_set_count transcript' with
                  | Result.Rejected failure =>
                      OpeningRejected failure.(Reject.reason_of) failure.(Reject.offset)
                  | Result.Panicked failure =>
                      VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
                  | Result.Ok (_, transcript'') =>
                      match R.read_ipa shape.(P.vk_k) transcript'' with
                      | Result.Rejected failure =>
                          OpeningRejected failure.(Reject.reason_of) failure.(Reject.offset)
                      | Result.Panicked failure =>
                          VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
                      | Result.Ok (_, final_transcript) =>
                          BackendUnavailable (List.length actions)
                            (Transcript.consumed final_transcript)
                            (List.length (Transcript.remaining final_transcript))
                      end
                  end
              end
          end
      end
  end.

Definition finish_report (result : Result.t (C.msm * Transcript.t)) :
    verification_report :=
  match result with
  | Result.Rejected failure =>
      OpeningRejected failure.(Reject.reason_of) failure.(Reject.offset)
  | Result.Panicked failure =>
      VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
  | Result.Ok (state, transcript) =>
      (** The state is the unchanged Rust-shaped MSM.  The checked evaluator
          validates every proof-supplied affine point before entering the
          fixed-SRS primitive-word kernel; [eval_srs_checked_refines] pins
          that result to the reference evaluator and certified SRS. *)
      match OrchardVerifierChecked.eval_srs_checked state with
      | None => VerifierPanicked
          (Panic.LengthMismatch shape.(P.vk_n)
            (match state.(C.g_scalars) with
             | Some scalars => List.length scalars
             | None => 0%nat
             end))
          (Transcript.consumed transcript)
      | Some false => VerificationRejected (Transcript.consumed transcript)
      | Some true => Verified (Transcript.consumed transcript)
          (List.length (Transcript.remaining transcript))
      end
  end.

Definition verify_post_nu6_3_with_backend_Z (backend : R.backend)
    (proof : list Z) (actions : list (list Z)) : verification_report :=
  match first_invalid_byte 0 proof with
  | Some failure => InputRejected failure
  | None =>
      match validate_actions_from 0 actions with
      | Some failure => InputRejected failure
      | None =>
          match parse_post_nu6_3_Z proof actions with
          | Result.Rejected failure =>
              TranscriptRejected failure.(Reject.reason_of) failure.(Reject.offset)
          | Result.Panicked failure =>
              VerifierPanicked failure.(Panic.reason_of) failure.(Panic.offset)
          | Result.Ok (parsed, transcript) =>
              match backend.(R.assemble_plonk) parsed with
              | R.AssemblyUnavailable => BackendUnavailable (List.length actions)
                  (Transcript.consumed transcript)
                  (List.length (Transcript.remaining transcript))
              | R.AssemblyPanicked reason =>
                  VerifierPanicked reason (Transcript.consumed transcript)
              | R.AssemblyReady assembled =>
                  finish_report (R.finish shape assembled transcript)
              end
          end
      end
  end.

End OrchardPostNu63.
