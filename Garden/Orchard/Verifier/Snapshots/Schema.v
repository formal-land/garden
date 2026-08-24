(** * Versioned differential snapshots for the Orchard verifier

    The neutral JSON corpus stores proof bytes and canonical public inputs from
    the pinned Rust verifier.  Generated Rocq files use this small schema.  A
    case refers to a proof and an input independently so the wrong-instance
    test does not duplicate a multi-kilobyte proof.

    Mutations are applied to 32-byte transcript chunks.  Their definitions are
    executable and use the same little-endian scalar representation as the
    verifier. *)

From Stdlib Require Import ZArith Lists.List Strings.String Strings.PrimString
  Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Encoding.Bytes.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardVerifierSnapshot.
  Definition chunk_bytes : nat := 32%nat.

  (** Compact exact representation for generated proof fixtures.  Hex uses
      printable primitive strings, so extraction emits one flat OCaml string
      instead of thousands of nested [Z] constructors and list cells.  The
      decoder remains a Rocq definition and the public snapshot API continues
      to expose [list Z]. *)
  Definition hex_nibble (value : Z) : option Z :=
    if (48 <=? value) && (value <=? 57) then Some (value - 48) else
    if (97 <=? value) && (value <=? 102) then Some (value - 87) else
    if (65 <=? value) && (value <=? 70) then Some (value - 55) else
    None.

  Definition pstring_byte_at (encoded : PrimString.string) (offset : Z) : Z :=
    Uint63.to_Z (PrimString.get encoded (Uint63.of_Z offset)).

  Fixpoint hex_bytes_from (encoded : PrimString.string) (offset : Z)
      (fuel : nat) : list Z :=
    match fuel with
    | O => []
    | S fuel' =>
        match hex_nibble (pstring_byte_at encoded offset),
              hex_nibble (pstring_byte_at encoded (offset + 1)) with
        | Some high, Some low =>
            (16 * high + low) :: hex_bytes_from encoded (offset + 2) fuel'
        | _, _ => []
        end
    end.

  Definition bytes_of_hex (encoded : PrimString.string) : list Z :=
    let encoded_length := Uint63.to_Z (PrimString.length encoded) in
    if Z.even encoded_length
    then hex_bytes_from encoded 0 (Z.to_nat (encoded_length / 2))
    else [].

  Inductive transcript_cause : Set :=
  | UnexpectedEof
  | InvalidScalarEncoding
  | InvalidPointEncoding
  | PointAtInfinity.

  Inductive plonk_error : Set :=
  | InvalidInstances
  | InstanceTooLarge
  | Transcript (cause : transcript_cause)
  | Opening
  | ConstraintSystemFailure.

  Inductive expected_outcome : Set :=
  | Verified
  | Rejected (error : plonk_error)
  | Panicked.

  Record proof_source : Set := {
    proof_num_actions : nat;
    proof_cross_address_enabled : bool;
    proof_bytes : list Z;
  }.

  Record input_source : Set := {
    (** One flat ten-scalar public-input column per aggregated proof. *)
    input_instances : list (list Z);
  }.

  Inductive mutation : Set :=
  | Identity
  | Append (bytes : list Z)
  | Truncate (length : nat)
  | ReplaceChunk (index : nat) (bytes : list Z)
  | RemoveChunk (index : nat)
  | IncrementScalar (index : nat)
  | FlipPointSign (index : nat).

  Record case : Set := {
    case_proof_index : nat;
    case_input_index : nat;
    case_mutation : mutation;
    case_expected : expected_outcome;
  }.

  Definition valid_byteb (byte : Z) : bool :=
    (0 <=? byte) && (byte <=? 255).

  Definition valid_bytesb (bytes : list Z) : bool :=
    List.forallb valid_byteb bytes.

  Definition replace_slice {A : Type} (start count : nat)
      (replacement values : list A) : option (list A) :=
    if Nat.eqb (List.length replacement) count &&
       Nat.leb (start + count) (List.length values)
    then Some (List.firstn start values ++ replacement ++
               List.skipn (start + count) values)
    else None.

  Definition chunk_start (index : nat) : nat :=
    (index * chunk_bytes)%nat.

  Definition chunk (index : nat) (bytes : list Z) : option (list Z) :=
    let start := chunk_start index in
    if Nat.leb (start + chunk_bytes) (List.length bytes)
    then Some (List.firstn chunk_bytes (List.skipn start bytes))
    else None.

  Definition replace_chunk (index : nat) (replacement bytes : list Z) :
      option (list Z) :=
    if valid_bytesb replacement
    then replace_slice (chunk_start index) chunk_bytes replacement bytes
    else None.

  Definition remove_chunk (index : nat) (bytes : list Z) : option (list Z) :=
    let start := chunk_start index in
    if Nat.leb (start + chunk_bytes) (List.length bytes)
    then Some (List.firstn start bytes ++
               List.skipn (start + chunk_bytes) bytes)
    else None.

  Definition increment_scalar (index : nat) (bytes : list Z) :
      option (list Z) :=
    match chunk index bytes with
    | None => None
    | Some encoded =>
        match Bytes.value_of_le_Z encoded with
        | None => None
        | Some value =>
            if (0 <=? value) && (value <? Scalar.modulus)
            then replace_chunk index
              (Bytes.values_of_Z chunk_bytes ((value + 1) mod Scalar.modulus))
              bytes
            else None
        end
    end.

  Definition flip_point_sign (index : nat) (bytes : list Z) :
      option (list Z) :=
    match chunk index bytes with
    | None => None
    | Some encoded =>
        match List.rev encoded with
        | [] => None
        | final :: prefix_rev =>
            replace_chunk index
              (List.rev prefix_rev ++ [Z.lxor final 128]) bytes
        end
    end.

  Definition apply_mutation (change : mutation) (bytes : list Z) :
      option (list Z) :=
    match change with
    | Identity => if valid_bytesb bytes then Some bytes else None
    | Append suffix =>
        if valid_bytesb bytes && valid_bytesb suffix
        then Some (bytes ++ suffix)
        else None
    | Truncate length =>
        if Nat.leb length (List.length bytes)
        then Some (List.firstn length bytes)
        else None
    | ReplaceChunk index replacement =>
        replace_chunk index replacement bytes
    | RemoveChunk index => remove_chunk index bytes
    | IncrementScalar index => increment_scalar index bytes
    | FlipPointSign index => flip_point_sign index bytes
    end.

  Definition expected_proof_size (actions : nat) : nat :=
    (2720 + 2272 * actions)%nat.

  Definition source_well_formedb (source : proof_source) : bool :=
    valid_bytesb source.(proof_bytes) &&
    Nat.eqb (List.length source.(proof_bytes))
      (expected_proof_size source.(proof_num_actions)).

  Definition canonical_scalarb (value : Z) : bool :=
    (0 <=? value) && (value <? Scalar.modulus).

  Definition boolean_scalarb (value : Z) : bool :=
    (value =? 0) || (value =? 1).

  Definition input_instance_well_formedb (instance : list Z) : bool :=
    Nat.eqb (List.length instance) 10%nat &&
    List.forallb canonical_scalarb instance &&
    match List.nth_error instance 7%nat,
          List.nth_error instance 8%nat,
          List.nth_error instance 9%nat with
    | Some enable_spend, Some enable_output, Some disable_cross_address =>
        boolean_scalarb enable_spend &&
        boolean_scalarb enable_output &&
        boolean_scalarb disable_cross_address
    | _, _, _ => false
    end.

  Definition inputs_well_formedb (source : input_source) : bool :=
    List.forallb input_instance_well_formedb source.(input_instances).

  Example noncanonical_input_scalar_is_not_well_formed :
    input_instance_well_formedb
      (Scalar.modulus :: List.repeat 0 9%nat) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example nonboolean_input_flag_is_not_well_formed :
    input_instance_well_formedb
      (List.repeat 0 7%nat ++ [2; 0; 0]) = false.
  Proof. vm_compute. reflexivity. Qed.
End OrchardVerifierSnapshot.
