(** * Compressed Vesta point encoding

    The Pasta encoding stores a canonical Vesta x-coordinate in 255 little-
    endian bits and the parity of y in the remaining top bit.  The all-zero
    representation decodes to the group identity before the curve equation is
    considered.  This matches [pasta_curves::EqAffine::from_bytes], including
    the asymmetry that [x = 0, sign = 1] follows the ordinary square-root path.

    Decoding accepts the identity.  Halo2's transcript rejects it separately
    because affine coordinates do not exist for a common point. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Bytes.
Require Import Garden.Halo2.Verifier.Encoding.Reader.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module Point.
  Definition t : Set := Vesta.point.
  Definition base_modulus : Z := Primes.pallas_q.
  Definition byte_length : nat := 32%nat.
  Definition coordinate_bytes : nat := 31%nat.
  Definition sign_bit : Z := 128.
  Definition coordinate_mask : Z := 127.

  Definition identity : t := Vesta.identity.
  Definition affine (x y : Z) : t := Vesta.affine x y.

  Definition coordinates (point : t) : option (Z * Z) :=
    match point with
    | Weierstrass.Infinity => None
    | Weierstrass.Affine x y => Some (x, y)
    end.

  Definition is_identityb (point : t) : bool :=
    match coordinates point with
    | None => true
    | Some _ => false
    end.

  Definition on_curveb (point : t) : bool := Vesta.on_curveb point.

  Definition canonicalb (point : t) : bool :=
    match coordinates point with
    | None => true
    | Some (x, y) =>
        (0 <=? x) && (x <? base_modulus)
          && ((0 <=? y) && (y <? base_modulus))
          && on_curveb point
    end.

  Definition curve_rhs (x : Z) : Z :=
    BinOp.add (p := base_modulus)
      (BinOp.mul (p := base_modulus)
        (BinOp.mul (p := base_modulus) x x) x)
      Vesta.b.

  Definition choose_parity (odd : bool) (root : Z) : Z :=
    if Bool.eqb (Z.odd root) odd
    then UnOp.from (p := base_modulus) root
    else UnOp.opp (p := base_modulus) root.

  Definition decode_bytes (bytes : list Byte.t) : option t :=
    if Nat.eqb (List.length bytes) byte_length
       && List.forallb Byte.validb bytes
    then
      let values := Byte.values bytes in
      let final := List.nth coordinate_bytes values 0 in
      let odd := sign_bit <=? final in
      let x_values :=
        List.firstn coordinate_bytes values
          ++ [Z.land final coordinate_mask] in
      let x := Bytes.values_of_le x_values in
      if x <? base_modulus then
        if (x =? 0) && negb odd then Some identity
        else
          let rhs := curve_rhs x in
          let root := field_sqrt (p := base_modulus) rhs in
          if Z.eqb
               (BinOp.mul (p := base_modulus) root root)
               (UnOp.from (p := base_modulus) rhs)
          then Some (affine x (choose_parity odd root))
          else None
      else None
    else None.

  Definition to_bytes (point : t) : list Byte.t :=
    match coordinates point with
    | None => List.repeat Byte.zero byte_length
    | Some (x, y) =>
        let values := Bytes.values_of_Z byte_length x in
        let sign := if Z.odd y then sign_bit else 0 in
        Byte.wrapping_list
          (List.firstn coordinate_bytes values
             ++ [Z.lor (List.nth coordinate_bytes values 0) sign])
    end.

  (** Halo2 absorbs uncompressed canonical affine coordinates, not the
      compressed proof representation. *)
  Definition transcript_bytes (point : t) : option (list Byte.t) :=
    match coordinates point with
    | None => None
    | Some (x, y) =>
        Some (Bytes.of_Z byte_length x ++ Bytes.of_Z byte_length y)
    end.

  Definition read (reader : Reader.t) : Result.t (t * Reader.t) :=
    let start := reader.(Reader.consumed) in
    let reader := Reader.record (Trace.ReadPoint start) reader in
    Result.bind (Reader.read_exact byte_length reader)
      (fun '(bytes, next) =>
        match decode_bytes bytes with
        | Some point => Result.Ok (point, next)
        | None => Reader.reject Reject.InvalidPointEncoding next
        end).
End Point.
