(** * Halo 2 Fiat–Shamir transcript, specialized to Vesta + Blake2b

    Transcription of [halo2_proofs/src/transcript.rs] for the Orchard
    verifier: [Blake2bRead] over a byte buffer, [Challenge255], and
    [read_point]/[read_scalar]/[squeeze_challenge]/[common_point]/
    [common_scalar]. The hasher is unkeyed BLAKE2b-512 personalized
    [b"Halo2-Transcript"]. Absorbing is represented by accumulating the
    prefix-tagged message; a squeeze clones that prefix, finalizes, and
    keeps the prefix in the running state — the same clone-and-finalize
    as [blake2b_simd::State]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.Halo2.halo2_proofs.pasta.

Import List.ListNotations.
Global Open Scope Z_scope.

Module TranscriptError.
  Inductive t : Set :=
  | InvalidPointEncoding
  | InvalidScalarEncoding
  | PointAtInfinity
  | BufferUnderrun.
End TranscriptError.

Definition BLAKE2B_PREFIX_CHALLENGE : Z := 0.
Definition BLAKE2B_PREFIX_POINT : Z := 1.
Definition BLAKE2B_PREFIX_SCALAR : Z := 2.

Definition halo2_transcript_personal : list Z :=
  (* "Halo2-Transcript" as 16 bytes *)
  [72; 97; 108; 111; 50; 45; 84; 114; 97; 110; 115; 99; 114; 105; 112; 116].

Module Challenge255.
  (** Packed 32-byte encoding of a Vesta scalar challenge. *)
  Record t : Set := {
    bytes : list Z;
  }.

  Definition new (challenge_input : list Z) : t :=
    let s := Fp.from_uniform_bytes challenge_input in
    {| bytes := Fp.to_repr s |}.

  Definition get_scalar (c : t) : Z :=
    match Fp.from_repr c.(bytes) with
    | Some s => s
    | None => 0
    end.
End Challenge255.

Module Blake2bRead.
  Record t : Set := {
    (** Bytes absorbed into the running hasher, including squeeze prefixes. *)
    absorbed : list Z;
    (** Remaining proof bytes. *)
    reader : list Z;
  }.

  Definition init (reader : list Z) : t := {|
    absorbed := [];
    reader := reader;
  |}.

  Definition hash_absorbed (absorbed : list Z) : list Z :=
    Blake2b.blake2b 64 Blake2b.zero16 halo2_transcript_personal absorbed.

  Definition update (tr : t) (bs : list Z) : t :=
    {| absorbed := tr.(absorbed) ++ bs; reader := tr.(reader) |}.

  Definition take (tr : t) (n : nat) : Result.t (list Z * t) TranscriptError.t :=
    if Nat.ltb (List.length tr.(reader)) n then
      Result.Err TranscriptError.BufferUnderrun
    else
      Result.Ok
        (List.firstn n tr.(reader),
         {| absorbed := tr.(absorbed);
            reader := List.skipn n tr.(reader) |}).

  Definition squeeze_challenge (tr : t) : Challenge255.t * t :=
    let tr := update tr [BLAKE2B_PREFIX_CHALLENGE] in
    let digest := hash_absorbed tr.(absorbed) in
    (Challenge255.new digest, tr).

  Definition squeeze_challenge_scalar (tr : t) : Z * t :=
    let '(c, tr) := squeeze_challenge tr in
    (Challenge255.get_scalar c, tr).

  Definition common_point (tr : t) (P : VestaCurve.point) : Result.t t TranscriptError.t :=
    match VestaEncoding.coordinates P with
    | None => Result.Err TranscriptError.PointAtInfinity
    | Some (x, y) =>
      Result.Ok (update tr
        ([BLAKE2B_PREFIX_POINT] ++ Fq.to_repr x ++ Fq.to_repr y))
    end.

  Definition common_scalar (tr : t) (s : Z) : t :=
    update tr ([BLAKE2B_PREFIX_SCALAR] ++ Fp.to_repr s).

  Definition read_point (tr : t) : Result.t (VestaCurve.point * t) TranscriptError.t :=
    Result.and_then (fun '(bs, tr) =>
      match VestaEncoding.from_bytes bs with
      | None => Result.Err TranscriptError.InvalidPointEncoding
      | Some P =>
        Result.and_then (fun tr => Result.Ok (P, tr)) (common_point tr P)
      end) (take tr 32%nat).

  Definition read_scalar (tr : t) : Result.t (Z * t) TranscriptError.t :=
    Result.and_then (fun '(bs, tr) =>
      match Fp.from_repr bs with
      | None => Result.Err TranscriptError.InvalidScalarEncoding
      | Some s => Result.Ok (s, common_scalar tr s)
      end) (take tr 32%nat).

  Fixpoint read_n_points (tr : t) (n : nat) :
      Result.t (list VestaCurve.point * t) TranscriptError.t :=
    match n with
    | O => Result.Ok ([], tr)
    | S n =>
      Result.and_then (fun '(P, tr) =>
        Result.and_then (fun '(Ps, tr) => Result.Ok (P :: Ps, tr))
          (read_n_points tr n))
        (read_point tr)
    end.

  Fixpoint read_n_scalars (tr : t) (n : nat) :
      Result.t (list Z * t) TranscriptError.t :=
    match n with
    | O => Result.Ok ([], tr)
    | S n =>
      Result.and_then (fun '(s, tr) =>
        Result.and_then (fun '(ss, tr) => Result.Ok (s :: ss, tr))
          (read_n_scalars tr n))
        (read_scalar tr)
    end.
End Blake2bRead.

Module TranscriptTests.
  (** Empty-transcript squeeze: BLAKE2b-512 of a single challenge prefix
      byte, personalized, then [from_uniform_bytes]. *)
  Definition empty_squeeze : Z :=
    let '(s, _) := Blake2bRead.squeeze_challenge_scalar (Blake2bRead.init []) in
    s.

  Lemma empty_squeeze_canonical :
    Fp.from empty_squeeze = empty_squeeze.
  Proof. vm_compute. reflexivity. Qed.

  Lemma personal_length : List.length halo2_transcript_personal = 16%nat.
  Proof. reflexivity. Qed.

  Lemma read_underrun :
    Result.is_ok (Blake2bRead.read_scalar (Blake2bRead.init [])) = false.
  Proof. vm_compute. reflexivity. Qed.
End TranscriptTests.
