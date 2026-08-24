(** * Canonical Pallas-scalar encoding used by the Vesta verifier

    A Vesta proof scalar is a canonical 32-byte little-endian representative
    of [F_p] for [p = Primes.pallas_p].  In particular, decoding rejects the
    modulus instead of reducing it.  Arithmetic constructors reduce modulo
    [p], while [canonicalb] detects a value built by bypassing those
    constructors. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Bytes.
Require Import Garden.Halo2.Verifier.Encoding.Reader.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Module Scalar.
  Definition modulus : Z := Primes.pallas_p.
  Definition byte_length : nat := 32%nat.

  Record t : Set := {
    value : Z;
  }.

  Definition canonicalb (scalar : t) : bool :=
    (0 <=? scalar.(value)) && (scalar.(value) <? modulus).

  Definition of_Z (value : Z) : t :=
    {| value := value mod modulus |}.

  Definition of_canonical_Z (value : Z) : option t :=
    if (0 <=? value) && (value <? modulus)
    then Some {| value := value |}
    else None.

  Definition zero : t := of_Z 0.
  Definition one : t := of_Z 1.

  Definition add (left right : t) : t :=
    of_Z (left.(value) + right.(value)).

  Definition sub (left right : t) : t :=
    of_Z (left.(value) - right.(value)).

  Definition mul (left right : t) : t :=
    of_Z (left.(value) * right.(value)).

  Definition opp (scalar : t) : t := of_Z (- scalar.(value)).
  Definition square (scalar : t) : t := mul scalar scalar.

  Definition eqb (left right : t) : bool :=
    Z.eqb left.(value) right.(value).

  Definition is_zerob (scalar : t) : bool := eqb scalar zero.

  Definition pow (base : t) (exponent : Z) : t :=
    match exponent with
    | Zpos positive_exponent =>
        of_Z (fast_pow_modulo_positive
          1 base.(value) modulus positive_exponent)
    | _ => one
    end.

  Definition pow_nat (base : t) (exponent : nat) : t :=
    pow base (Z.of_nat exponent).

  Definition inv (scalar : t) : option t :=
    if is_zerob scalar
    then None
    else Some (of_Z (mod_inverse scalar.(value) modulus)).

  Definition to_bytes (scalar : t) : list Byte.t :=
    Bytes.of_Z byte_length scalar.(value).

  Definition decode_bytes (bytes : list Byte.t) : option t :=
    if Nat.eqb (List.length bytes) byte_length
       && List.forallb Byte.validb bytes
    then of_canonical_Z (Bytes.value_of_le bytes)
    else None.

  Definition from_uniform_bytes (bytes : list Byte.t) : option t :=
    if Nat.eqb (List.length bytes) 64%nat
       && List.forallb Byte.validb bytes
    then Some (of_Z (Bytes.value_of_le bytes))
    else None.

  Definition from_uniform_values (bytes : list Z) : option t :=
    match Byte.checked_list bytes with
    | Some bytes => from_uniform_bytes bytes
    | None => None
    end.

  Definition read (reader : Reader.t) : Result.t (t * Reader.t) :=
    let start := reader.(Reader.consumed) in
    let reader := Reader.record (Trace.ReadScalar start) reader in
    Result.bind (Reader.read_exact byte_length reader)
      (fun '(bytes, next) =>
        match decode_bytes bytes with
        | Some scalar => Result.Ok (scalar, next)
        | None => Reader.reject Reject.InvalidScalarEncoding next
        end).
End Scalar.
