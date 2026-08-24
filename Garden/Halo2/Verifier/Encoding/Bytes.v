(** * Fixed-width little-endian byte conversions *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.Halo2.Verifier.Types.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Module Bytes.
  Definition value_of_le (bytes : list Byte.t) : Z :=
    List.fold_right (fun byte acc => Byte.value byte + 256 * acc) 0 bytes.

  Definition values_of_le (values : list Z) : Z :=
    List.fold_right (fun byte acc => byte + 256 * acc) 0 values.

  Definition values_of_Z (count : nat) (value : Z) : list Z :=
    List.map
      (fun index => Z.land (Z.shiftr value (8 * Z.of_nat index)) 255)
      (List.seq O count).

  Definition of_Z (count : nat) (value : Z) : list Byte.t :=
    Byte.wrapping_list (values_of_Z count value).

  Definition valid_valuesb (values : list Z) : bool :=
    List.forallb
      (fun value =>
        (Byte.min_value <=? value) && (value <=? Byte.max_value))
      values.

  Definition value_of_le_Z (values : list Z) : option Z :=
    if valid_valuesb values then Some (values_of_le values) else None.
End Bytes.
