(** * Fixed-width hexadecimal rendering of field elements *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.PrimString.

Global Open Scope Z_scope.

Module FieldHex.

Definition digit (value : Z) : PrimString.string :=
  if value =? 0 then "0" else if value =? 1 then "1"
  else if value =? 2 then "2" else if value =? 3 then "3"
  else if value =? 4 then "4" else if value =? 5 then "5"
  else if value =? 6 then "6" else if value =? 7 then "7"
  else if value =? 8 then "8" else if value =? 9 then "9"
  else if value =? 10 then "a" else if value =? 11 then "b"
  else if value =? 12 then "c" else if value =? 13 then "d"
  else if value =? 14 then "e" else "f".

Fixpoint fixed_hex_go
    (fuel : nat) (value : Z) (accumulator : PrimString.string)
    : PrimString.string :=
  match fuel with
  | O => accumulator
  | S fuel =>
      fixed_hex_go fuel (value / 16)
        (PrimString.cat (digit (value mod 16)) accumulator)
  end.

(** Pasta field Debug output uses [0x] followed by exactly 64 lowercase
    hexadecimal digits in big-endian display order. *)
Definition hex64 (value : Z) : PrimString.string :=
  PrimString.cat "0x" (fixed_hex_go 64 value ""%pstring).

End FieldHex.
