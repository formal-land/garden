Require Import Garden.Plonky3.M.

Module ByteOpcode.
  Inductive t : Set :=
  | AND
  | OR
  | XOR
  | SLL
  | ShrCarry
  | LTU
  | MSB
  | U8Range
  | U16Range.

  Definition to_Z (self : t) : Z :=
    match self with
    | AND => 0
    | OR => 1
    | XOR => 2
    | SLL => 3
    | ShrCarry => 4
    | LTU => 5
    | MSB => 6
    | U8Range => 7
    | U16Range => 8
    end.
End ByteOpcode.
