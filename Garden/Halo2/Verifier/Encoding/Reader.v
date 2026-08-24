(** * Slice reader with Rust [read_exact] consumption semantics *)

From Stdlib Require Import Lists.List Arith.PeanoNat ZArith Bool.
Require Import Garden.Halo2.Verifier.Types.

Import ListNotations.
Local Open Scope Z_scope.

Module Reader.
  (** [consumed] is an observational offset, not a translated mutable Rust
      integer.  A Rust slice already has a [usize]-bounded length, and
      [read_exact] advances within that length, so the operation contains no
      wrapping counter arithmetic.  [nat] records the mathematical amount
      consumed without introducing an overflow branch absent from the Rust
      reader. *)
  Record t : Set := {
    remaining : list Byte.t;
    consumed : nat;
    trace : Trace.t;
  }.

  Definition init (proof : list Byte.t) : t :=
    {| remaining := proof; consumed := O; trace := [] |}.

  Fixpoint checked_from (position : nat) (values : list Z) : Result.t (list Byte.t) :=
    match values with
    | [] => Result.Ok []
    | value :: values =>
        match Byte.checked value with
        | None => Result.panicked (Panic.InvalidByte position value) position []
        | Some byte =>
            Result.map (fun bytes => byte :: bytes)
              (checked_from (S position) values)
        end
    end.

  (** Convenience boundary for generated [list Z] fixtures.  Verifier code
      consumes [list Byte.t] through [init], matching Rust's &[u8] type. *)
  Definition init_Z (proof : list Z) : Result.t t :=
    Result.map init (checked_from O proof).

  Definition remaining_length (reader : t) : nat :=
    List.length reader.(remaining).

  Definition record (event : Trace.event) (reader : t) : t :=
    {| remaining := reader.(remaining);
       consumed := reader.(consumed);
       trace := reader.(trace) ++ [event] |}.

  Definition reject {A : Type} (reason : Reject.reason) (reader : t) : Result.t A :=
    Result.rejected reason reader.(consumed) reader.(trace).

  Definition panic {A : Type} (reason : Panic.reason) (reader : t) : Result.t A :=
    Result.panicked reason reader.(consumed) reader.(trace).

  Fixpoint first_invalid (index : nat) (bytes : list Byte.t) : option (nat * Z) :=
    match bytes with
    | [] => None
    | byte :: bytes =>
        if Byte.validb byte
        then first_invalid (S index) bytes
        else Some (index, Byte.value byte)
    end.

  (** Rust's [Read::read_exact] over a byte slice consumes every available
      byte before returning [UnexpectedEof].  The resulting failure offset is
      therefore [start + available], not [start]. *)
  Definition read_exact (count : nat) (reader : t) :
      Result.t (list Byte.t * t) :=
    let start := reader.(consumed) in
    let available := List.length reader.(remaining) in
    let actual := Nat.min count available in
    let bytes := List.firstn count reader.(remaining) in
    let next :=
      {| remaining := List.skipn count reader.(remaining);
         consumed := (start + actual)%nat;
         trace := reader.(trace) ++ [Trace.ReadExact start count actual] |} in
    if Nat.leb count available then
      match first_invalid O bytes with
      | None => Result.Ok (bytes, next)
      | Some (index, value) =>
          Result.panicked
            (Panic.InvalidByte (start + index)%nat value)
            next.(consumed) next.(trace)
      end
    else
      Result.rejected (Reject.UnexpectedEof count available)
        next.(consumed) next.(trace).

  Definition read_byte (reader : t) : Result.t (Byte.t * t) :=
    Result.bind (read_exact 1 reader)
      (fun '(bytes, next) =>
        match bytes with
        | [byte] => Result.Ok (byte, next)
        | _ => panic (Panic.LengthMismatch 1 (List.length bytes)) next
        end).

  Definition finish (reader : t) : Result.t unit :=
    match reader.(remaining) with
    | [] => Result.Ok tt
    | remaining => reject (Reject.TrailingBytes (List.length remaining)) reader
    end.
End Reader.
