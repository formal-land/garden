(** * Rust-shaped values and outcomes for the executable Halo2 verifier

    Proof bytes use rocq-of-rust's [u8] carrier.  The carrier is deliberately
    not treated as a dependent range type: rocq-of-rust represents Rust
    integers by a kind-indexed record over [Z], with validity supplied by the
    operation that constructs a value.  [Byte.checked] is the wire-boundary
    constructor, while [Byte.wrapping] models Rust's release-mode conversion.

    Verification distinguishes an ordinary rejection from a Rust panic.
    Failures retain the byte offset and the chronological execution trace, so
    truncated and malformed proofs expose the same consumption boundary even
    though no successful reader state is returned. *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Garden.RustCompat.Integer.

Import ListNotations.
Local Open Scope Z_scope.

Module Byte.
  (** A small forwarding module preserves the public [Byte.RustInteger]
      names used by boundary tests without aliasing the whole
      [Garden.RustCompat.Integer] file module.  Rocq's monolithic OCaml
      extractor cannot represent aliases to file modules; forwarding the
      handful of operations used here is definitionally equivalent and keeps
      the executable dependency precise. *)
  Module RustInteger.
    Module Kind := Garden.RustCompat.Integer.Kind.
    Module Semantics := Garden.RustCompat.Integer.Semantics.

    Definition t (kind : Kind.t) : Set :=
      Garden.RustCompat.Integer.t kind.

    Definition value {kind : Kind.t} (x : t kind) : Z :=
      Garden.RustCompat.Integer.value x.

    Definition of_Z_unchecked (kind : Kind.t) (z : Z) : t kind :=
      Garden.RustCompat.Integer.of_Z_unchecked kind z.

    Definition validb {kind : Kind.t} (x : t kind) : bool :=
      Garden.RustCompat.Integer.validb x.

    Definition of_Z_checked (kind : Kind.t) (z : Z) : option (t kind) :=
      Garden.RustCompat.Integer.of_Z_checked kind z.

    Definition of_Z_wrapping (kind : Kind.t) (z : Z) : t kind :=
      Garden.RustCompat.Integer.of_Z_wrapping kind z.
  End RustInteger.

  Definition kind : RustInteger.Kind.t := RustInteger.Kind.U8.
  Definition t : Set := RustInteger.t kind.

  Definition min_value : Z :=
    RustInteger.Semantics.min kind.

  Definition max_value : Z :=
    RustInteger.Semantics.max kind.

  Definition value (byte : t) : Z := RustInteger.value byte.

  Definition validb (byte : t) : bool := RustInteger.validb byte.

  Definition checked (z : Z) : option t :=
    RustInteger.of_Z_checked kind z.

  Definition wrapping (z : Z) : t :=
    RustInteger.of_Z_wrapping kind z.

  Definition zero : t := wrapping 0.

  Definition eqb (left right : t) : bool :=
    Z.eqb (value left) (value right).

  Definition values (bytes : list t) : list Z := List.map value bytes.

  Fixpoint checked_list (values : list Z) : option (list t) :=
    match values with
    | [] => Some []
    | value :: values =>
        match checked value, checked_list values with
        | Some byte, Some bytes => Some (byte :: bytes)
        | _, _ => None
        end
    end.

  Definition wrapping_list (values : list Z) : list t :=
    List.map wrapping values.
End Byte.

Module Trace.
  (** [ReadExact start requested actual] records partial consumption on an
      unexpected end of input.  The remaining events record the semantic
      operations that frame the Halo2 transcript. *)
  Inductive event : Set :=
  | ReadExact (start requested actual : nat)
  | ReadScalar (start : nat)
  | ReadPoint (start : nat)
  | AbsorbScalar (value : Z)
  | AbsorbPoint (x y : Z)
  | AbsorbPointIdentity
  | SqueezeChallenge (value : Z).

  Definition t : Set := list event.
End Trace.

Module Reject.
  Inductive reason : Set :=
  | UnexpectedEof (requested available : nat)
  | InvalidScalarEncoding
  | InvalidPointEncoding
  | PointAtInfinity
  | TrailingBytes (remaining : nat)
  | VerificationFailure.

  Record t : Set := {
    reason_of : reason;
    offset : nat;
    trace : Trace.t;
  }.
End Reject.

Module Panic.
  (** [InvalidByte] is unreachable from a Rust [u8] slice.  It remains an
      explicit panic in Rocq because rocq-of-rust's integer carrier can be
      constructed directly with an out-of-range [Z]. *)
  Inductive reason : Set :=
  | InvalidByte (position : nat) (value : Z)
  | NonCanonicalScalarInvariant
  | NonCanonicalPointInvariant
  | DivisionByZero
  | IndexOutOfBounds (index length : nat)
  | LengthMismatch (expected actual : nat)
  | InternalInvariant.

  Record t : Set := {
    reason_of : reason;
    offset : nat;
    trace : Trace.t;
  }.
End Panic.

Module Result.
  Inductive t (A : Type) : Type :=
  | Ok (value : A)
  | Rejected (failure : Reject.t)
  | Panicked (failure : Panic.t).

  Arguments Ok {A} _.
  Arguments Rejected {A} _.
  Arguments Panicked {A} _.

  Definition map {A B : Type} (f : A -> B) (result : t A) : t B :=
    match result with
    | Ok value => Ok (f value)
    | Rejected failure => Rejected failure
    | Panicked failure => Panicked failure
    end.

  Definition bind {A B : Type} (result : t A) (f : A -> t B) : t B :=
    match result with
    | Ok value => f value
    | Rejected failure => Rejected failure
    | Panicked failure => Panicked failure
    end.

  Definition join {A : Type} (result : t (t A)) : t A :=
    bind result (fun inner => inner).

  Definition is_ok {A : Type} (result : t A) : bool :=
    match result with
    | Ok _ => true
    | Rejected _ | Panicked _ => false
    end.

  Definition rejected {A : Type}
      (reason : Reject.reason) (offset : nat) (trace : Trace.t) : t A :=
    Rejected {| Reject.reason_of := reason;
                Reject.offset := offset;
                Reject.trace := trace |}.

  Definition panicked {A : Type}
      (reason : Panic.reason) (offset : nat) (trace : Trace.t) : t A :=
    Panicked {| Panic.reason_of := reason;
                Panic.offset := offset;
                Panic.trace := trace |}.
End Result.
