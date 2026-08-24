(** * Executable boundary and framing tests for the verifier foundation *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Bytes.
Require Import Garden.Halo2.Verifier.Encoding.Reader.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Transcript.

Import ListNotations.
Local Open Scope Z_scope.

Module VerifierFoundationTests.
  Definition bytes (values : list Z) : list Byte.t := Byte.wrapping_list values.

  Example reader_unexpected_eof_consumes_available :
    Reader.read_exact 4%nat (Reader.init (bytes [7; 8])) =
      Result.Rejected
        {| Reject.reason_of := Reject.UnexpectedEof 4%nat 2%nat;
           Reject.offset := 2%nat;
           Reject.trace := [Trace.ReadExact 0%nat 4%nat 2%nat] |}.
  Proof. vm_compute. reflexivity. Qed.

  Definition impossible_u8 : Byte.t :=
    Byte.RustInteger.of_Z_unchecked Byte.kind 256.

  Example out_of_range_u8_is_a_panic :
    Reader.read_exact 1%nat (Reader.init [impossible_u8]) =
      Result.Panicked
        {| Panic.reason_of := Panic.InvalidByte 0%nat 256;
           Panic.offset := 1%nat;
           Panic.trace := [Trace.ReadExact 0%nat 1%nat 1%nat] |}.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_zero_is_canonical :
    Scalar.decode_bytes (Bytes.of_Z Scalar.byte_length 0) = Some Scalar.zero.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_modulus_minus_one_is_canonical :
    Scalar.decode_bytes
      (Bytes.of_Z Scalar.byte_length (Scalar.modulus - 1)) =
      Some {| Scalar.value := Scalar.modulus - 1 |}.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_modulus_is_rejected :
    Scalar.decode_bytes (Bytes.of_Z Scalar.byte_length Scalar.modulus) = None.
  Proof. vm_compute. reflexivity. Qed.

  Example bypassed_scalar_constructor_is_a_panic :
    Transcript.common_scalar
      {| Scalar.value := Scalar.modulus |} (Transcript.init []) =
      Result.Panicked
        {| Panic.reason_of := Panic.NonCanonicalScalarInvariant;
           Panic.offset := 0%nat;
           Panic.trace := [Trace.AbsorbScalar Scalar.modulus] |}.
  Proof. vm_compute. reflexivity. Qed.

  Definition scalar_modulus_read : Result.t (Scalar.t * Reader.t) :=
    Scalar.read (Reader.init (Bytes.of_Z Scalar.byte_length Scalar.modulus)).

  Example scalar_rejection_consumes_representation :
    scalar_modulus_read =
      Result.Rejected
        {| Reject.reason_of := Reject.InvalidScalarEncoding;
           Reject.offset := 32%nat;
           Reject.trace :=
             [Trace.ReadScalar 0%nat; Trace.ReadExact 0%nat 32%nat 32%nat] |}.
  Proof. vm_compute. reflexivity. Qed.

  Example point_identity_encoding :
    Point.decode_bytes (List.repeat Byte.zero Point.byte_length) =
      Some Point.identity.
  Proof. vm_compute. reflexivity. Qed.

  Example point_noncanonical_x_is_rejected :
    Point.decode_bytes
      (Bytes.of_Z Point.byte_length Point.base_modulus) = None.
  Proof. vm_compute. reflexivity. Qed.

  (** The high bit alone requests an odd square root of 5 at x = 0.  Five is
      a quadratic non-residue in PallasQ, so this takes the ordinary curve
      branch and fails instead of aliasing the reserved identity encoding. *)
  Example point_sign_bit_does_not_alias_identity :
    Point.decode_bytes
      (List.repeat Byte.zero Point.coordinate_bytes
        ++ [Byte.wrapping Point.sign_bit]) = None.
  Proof. vm_compute. reflexivity. Qed.

  Definition generator : Point.t :=
    Point.affine (Point.base_modulus - 1) 2.

  Definition negative_generator : Point.t :=
    Point.affine (Point.base_modulus - 1) (Point.base_modulus - 2).

  Example point_even_parity_roundtrip :
    Point.decode_bytes (Point.to_bytes generator) = Some generator.
  Proof. vm_compute. reflexivity. Qed.

  Example point_odd_parity_roundtrip :
    Point.decode_bytes (Point.to_bytes negative_generator) =
      Some negative_generator.
  Proof. vm_compute. reflexivity. Qed.

  Definition identity_read : Result.t (Point.t * Transcript.t) :=
    Transcript.read_point
      (Transcript.init (List.repeat Byte.zero Point.byte_length)).

  Example decoded_identity_is_rejected_as_common_point :
    identity_read =
      Result.Rejected
        {| Reject.reason_of := Reject.PointAtInfinity;
           Reject.offset := 32%nat;
           Reject.trace :=
             [Trace.ReadPoint 0%nat;
              Trace.ReadExact 0%nat 32%nat 32%nat;
              Trace.AbsorbPointIdentity] |}.
  Proof. vm_compute. reflexivity. Qed.

  Definition empty_challenge : Scalar.t :=
    fst (Transcript.squeeze_challenge (Transcript.init [])).

  (** Independent reference: Python [hashlib.blake2b], digest size 64,
      personalization [b"Halo2-Transcript"], message [00], interpreted as a
      512-bit little-endian integer and reduced modulo PallasP. *)
  Example empty_squeeze_vector :
    empty_challenge.(Scalar.value) =
      3906794317365064007503458283393700187134131643498139400953322572614894537858.
  Proof. vm_compute. reflexivity. Qed.

  Definition scalar_one_challenge : option Scalar.t :=
    match Transcript.common_scalar Scalar.one (Transcript.init []) with
    | Result.Ok transcript =>
        Some (fst (Transcript.squeeze_challenge transcript))
    | Result.Rejected _ | Result.Panicked _ => None
    end.

  (** Message framing is [02 || le32(1) || 00]. *)
  Example scalar_framing_vector :
    option_map Scalar.value scalar_one_challenge =
      Some
        18393823389843113942615214097299710775767725194999549034246103742226487083231.
  Proof. vm_compute. reflexivity. Qed.

  Definition generator_challenge : option Scalar.t :=
    match Transcript.common_point generator (Transcript.init []) with
    | Result.Ok transcript =>
        Some (fst (Transcript.squeeze_challenge transcript))
    | Result.Rejected _ | Result.Panicked _ => None
    end.

  (** Message framing is [01 || le32(q-1) || le32(2) || 00]. *)
  Example point_framing_vector :
    option_map Scalar.value generator_challenge =
      Some
        8705869321163031968375298420732904640991054978253905432662990517509604514197.
  Proof. vm_compute. reflexivity. Qed.

  Definition repeated_squeeze_values : Z * Z :=
    let '(first, transcript) :=
      Transcript.squeeze_challenge (Transcript.init []) in
    let '(second, _) := Transcript.squeeze_challenge transcript in
    (first.(Scalar.value), second.(Scalar.value)).

  Example squeeze_prefix_remains_in_live_state :
    fst repeated_squeeze_values =
      3906794317365064007503458283393700187134131643498139400953322572614894537858 /\
    snd repeated_squeeze_values =
      15214391434488923553326364186328399897332548233647065309844094603782792976479.
  Proof. vm_compute. split; reflexivity. Qed.
End VerifierFoundationTests.
