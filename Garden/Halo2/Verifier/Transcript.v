(** * Halo2's personalized BLAKE2b verifier transcript

    The transcript is the [Blake2bRead] construction from
    [halo2_proofs/src/transcript.rs].  Its BLAKE2b-512 personalization is the
    16-byte string ["Halo2-Transcript"].  A challenge, point, and scalar are
    framed by the one-byte tags 0, 1, and 2 respectively.  Points enter the
    hash as canonical x followed by canonical y, while scalars enter as their
    canonical 32-byte little-endian representation.

    [squeeze_challenge] appends tag 0 to the live state, finalizes a clone, and
    reduces the resulting 512-bit little-endian integer modulo PallasP.  The
    digest is not absorbed back into the state.  Storing the absorbed byte
    string gives the same behavior with the existing one-shot BLAKE2b model
    and keeps the reference implementation directly executable. *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Bytes.
Require Import Garden.Halo2.Verifier.Encoding.Reader.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.

Import ListNotations.
Local Open Scope Z_scope.

Module Transcript.
  Definition personalization : list Z :=
    [0x48; 0x61; 0x6c; 0x6f; 0x32; 0x2d; 0x54; 0x72;
     0x61; 0x6e; 0x73; 0x63; 0x72; 0x69; 0x70; 0x74].

  Definition prefix_challenge : Byte.t := Byte.wrapping 0.
  Definition prefix_point : Byte.t := Byte.wrapping 1.
  Definition prefix_scalar : Byte.t := Byte.wrapping 2.

  Record t : Set := {
    reader : Reader.t;
    absorbed : list Byte.t;
  }.

  Definition init (proof : list Byte.t) : t :=
    {| reader := Reader.init proof; absorbed := [] |}.

  Definition init_Z (proof : list Z) : Result.t t :=
    Result.map (fun reader => {| reader := reader; absorbed := [] |})
      (Reader.init_Z proof).

  Definition consumed (transcript : t) : nat :=
    transcript.(reader).(Reader.consumed).

  Definition remaining (transcript : t) : list Byte.t :=
    transcript.(reader).(Reader.remaining).

  Definition trace (transcript : t) : Trace.t :=
    transcript.(reader).(Reader.trace).

  Definition with_reader (reader : Reader.t) (transcript : t) : t :=
    {| reader := reader; absorbed := transcript.(absorbed) |}.

  Definition common_scalar (scalar : Scalar.t) (transcript : t) : Result.t t :=
    let reader := Reader.record (Trace.AbsorbScalar scalar.(Scalar.value))
                    transcript.(reader) in
    if Scalar.canonicalb scalar then
      Result.Ok
        {| reader := reader;
           absorbed := transcript.(absorbed)
             ++ prefix_scalar :: Scalar.to_bytes scalar |}
    else
      Reader.panic Panic.NonCanonicalScalarInvariant reader.

  Definition common_point (point : Point.t) (transcript : t) : Result.t t :=
    let prefixed := transcript.(absorbed) ++ [prefix_point] in
    match Point.coordinates point with
    | None =>
        let reader := Reader.record Trace.AbsorbPointIdentity transcript.(reader) in
        Reader.reject Reject.PointAtInfinity reader
    | Some (x, y) =>
        let reader := Reader.record (Trace.AbsorbPoint x y) transcript.(reader) in
        if Point.canonicalb point then
          Result.Ok
            {| reader := reader;
               absorbed := prefixed
                 ++ Bytes.of_Z Point.byte_length x
                 ++ Bytes.of_Z Point.byte_length y |}
        else
          Reader.panic Panic.NonCanonicalPointInvariant reader
    end.

  Definition read_scalar (transcript : t) :
      Result.t (Scalar.t * t) :=
    Result.bind (Scalar.read transcript.(reader))
      (fun '(scalar, reader) =>
        Result.map (fun transcript => (scalar, transcript))
          (common_scalar scalar (with_reader reader transcript))).

  Definition read_point (transcript : t) :
      Result.t (Point.t * t) :=
    Result.bind (Point.read transcript.(reader))
      (fun '(point, reader) =>
        Result.map (fun transcript => (point, transcript))
          (common_point point (with_reader reader transcript))).

  Definition squeeze_challenge (transcript : t) : Scalar.t * t :=
    let absorbed := transcript.(absorbed) ++ [prefix_challenge] in
    let digest :=
      Blake2b.blake2b 64 Blake2b.zero16 personalization
        (Byte.values absorbed) in
    let challenge := Scalar.of_Z (Bytes.values_of_le digest) in
    let reader :=
      Reader.record (Trace.SqueezeChallenge challenge.(Scalar.value))
        transcript.(reader) in
    (challenge, {| reader := reader; absorbed := absorbed |}).

  Definition finish (transcript : t) : Result.t unit :=
    Reader.finish transcript.(reader).
End Transcript.

