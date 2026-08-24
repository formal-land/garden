(** * Executable replay of the Orchard verifier differential corpus

    The generated module is deliberately data-only.  This module resolves its
    proof and input references, applies the recorded byte mutation, invokes the
    public Post-NU6.3 verifier, and compares a normalized report with the
    outcome captured from Rust.

    [BackendUnavailable] and malformed replay metadata are not normalized to a
    Rust outcome.  In particular, they compare false against [Verified]; this
    prevents a parser-only implementation from being reported as verifier
    parity. *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Orchard.Verifier.Verifier.
Require Import Garden.Orchard.Verifier.Snapshots.Schema.
Require Import Garden.Orchard.Verifier.Snapshots.Generated.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardVerifierSnapshotReplay.
  Module S := OrchardVerifierSnapshot.
  Module G := OrchardVerifierGeneratedSnapshots.

  Inductive replay_result : Type :=
  | MissingProof
  | MissingInput
  | MutationFailed
  | Executed (report : OrchardPostNu63.verification_report).

  Definition resolve_proof (snapshot : S.case) : option S.proof_source :=
    List.nth_error G.proofs snapshot.(S.case_proof_index).

  Definition resolve_input (snapshot : S.case) : option S.input_source :=
    List.nth_error G.inputs snapshot.(S.case_input_index).

  Definition prepare_case (snapshot : S.case) :
      option (list Z * list (list Z)) :=
    match resolve_proof snapshot with
    | None => None
    | Some proof =>
        match resolve_input snapshot with
        | None => None
        | Some input =>
            match S.apply_mutation snapshot.(S.case_mutation)
              proof.(S.proof_bytes) with
            | None => None
            | Some proof_bytes =>
                Some (proof_bytes, input.(S.input_instances))
            end
        end
    end.

  Definition replay (snapshot : S.case) : replay_result :=
    match resolve_proof snapshot with
    | None => MissingProof
    | Some proof =>
        match resolve_input snapshot with
        | None => MissingInput
        | Some input =>
            match S.apply_mutation snapshot.(S.case_mutation)
              proof.(S.proof_bytes) with
            | None => MutationFailed
            | Some proof_bytes =>
                Executed
                  (OrchardVerifier.verify_post_nu6_3_report_Z proof_bytes
                    input.(S.input_instances))
            end
        end
    end.

  Definition transcript_cause_of_reason
      (reason : Reject.reason) : option S.transcript_cause :=
    match reason with
    | Reject.UnexpectedEof _ _ => Some S.UnexpectedEof
    | Reject.InvalidScalarEncoding => Some S.InvalidScalarEncoding
    | Reject.InvalidPointEncoding => Some S.InvalidPointEncoding
    | Reject.PointAtInfinity => Some S.PointAtInfinity
    | Reject.TrailingBytes _ | Reject.VerificationFailure => None
    end.

  Definition normalize_report
      (report : OrchardPostNu63.verification_report) : option S.expected_outcome :=
    match report with
    | OrchardPostNu63.InputRejected _ => None
    | OrchardPostNu63.TranscriptRejected reason _ =>
        match transcript_cause_of_reason reason with
        | Some cause => Some (S.Rejected (S.Transcript cause))
        | None => None
        end
    | OrchardPostNu63.OpeningRejected _ _ => Some (S.Rejected S.Opening)
    | OrchardPostNu63.VerifierPanicked _ _ => Some S.Panicked
    | OrchardPostNu63.BackendUnavailable _ _ _ => None
    | OrchardPostNu63.VerificationRejected _ =>
        Some (S.Rejected S.ConstraintSystemFailure)
    | OrchardPostNu63.Verified _ _ => Some S.Verified
    end.

  Definition transcript_cause_eqb
      (left right : S.transcript_cause) : bool :=
    match left, right with
    | S.UnexpectedEof, S.UnexpectedEof
    | S.InvalidScalarEncoding, S.InvalidScalarEncoding
    | S.InvalidPointEncoding, S.InvalidPointEncoding
    | S.PointAtInfinity, S.PointAtInfinity => true
    | _, _ => false
    end.

  Definition plonk_error_eqb (left right : S.plonk_error) : bool :=
    match left, right with
    | S.InvalidInstances, S.InvalidInstances
    | S.InstanceTooLarge, S.InstanceTooLarge
    | S.Opening, S.Opening
    | S.ConstraintSystemFailure, S.ConstraintSystemFailure => true
    | S.Transcript left_cause, S.Transcript right_cause =>
        transcript_cause_eqb left_cause right_cause
    | _, _ => false
    end.

  Definition outcome_eqb (left right : S.expected_outcome) : bool :=
    match left, right with
    | S.Verified, S.Verified | S.Panicked, S.Panicked => true
    | S.Rejected left_error, S.Rejected right_error =>
        plonk_error_eqb left_error right_error
    | _, _ => false
    end.

  Definition report_matchesb
      (report : OrchardPostNu63.verification_report)
      (expected : S.expected_outcome) : bool :=
    match normalize_report report with
    | Some actual => outcome_eqb actual expected
    | None => false
    end.

  Definition case_matchesb (snapshot : S.case) : bool :=
    match replay snapshot with
    | Executed report => report_matchesb report snapshot.(S.case_expected)
    | MissingProof | MissingInput | MutationFailed => false
    end.

  Definition case_preparesb (snapshot : S.case) : bool :=
    match prepare_case snapshot with
    | Some _ => true
    | None => false
    end.

  Definition replayed_cases : list replay_result :=
    List.map replay G.cases.

  Definition case_match_vector : list bool :=
    List.map case_matchesb G.cases.

  Definition case_matches_at (index : nat) : bool :=
    match List.nth_error G.cases index with
    | Some snapshot => case_matchesb snapshot
    | None => false
    end.

  Definition all_cases_matchb : bool :=
    List.forallb (fun matched => matched) case_match_vector.

  Definition all_cases_prepareb : bool :=
    List.forallb case_preparesb G.cases.

  (** Every checked-in case resolves and every recorded mutation is executable.
      This is intentionally separate from verifier parity. *)
  Example all_generated_cases_prepare : all_cases_prepareb = true.
  Proof. vm_compute. reflexivity. Qed.

  Example transcript_eof_normalization :
    normalize_report
      (OrchardPostNu63.TranscriptRejected
        (Reject.UnexpectedEof 32%nat 0%nat) 0%nat) =
      Some (S.Rejected (S.Transcript S.UnexpectedEof)).
  Proof. reflexivity. Qed.

  Example opening_normalization :
    normalize_report
      (OrchardPostNu63.OpeningRejected
        Reject.InvalidPointEncoding 4032%nat) =
      Some (S.Rejected S.Opening).
  Proof. reflexivity. Qed.

  Example verification_failure_normalization :
    normalize_report (OrchardPostNu63.VerificationRejected 4992%nat) =
      Some (S.Rejected S.ConstraintSystemFailure).
  Proof. reflexivity. Qed.

  Example verified_normalization :
    normalize_report (OrchardPostNu63.Verified 4992%nat 0%nat) =
      Some S.Verified.
  Proof. reflexivity. Qed.

  Example panic_normalization :
    normalize_report
      (OrchardPostNu63.VerifierPanicked Panic.InternalInvariant 0%nat) =
      Some S.Panicked.
  Proof. reflexivity. Qed.

  (** An unavailable backend is an explicit differential mismatch.  It must
      never be treated as a verified Rust outcome. *)
  Example backend_unavailable_does_not_match_verified :
    report_matchesb
      (OrchardPostNu63.BackendUnavailable 1%nat 4992%nat 0%nat)
      S.Verified = false.
  Proof. reflexivity. Qed.
End OrchardVerifierSnapshotReplay.
