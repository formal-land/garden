Require Import Garden.Plonky3.M.

Module LookupType.
  Inductive t : Set :=
  | Memory
  | Program
  | Instruction
  | Alu
  | Byte
  | Range
  | Field
  | Syscall
  | Poseidon2
  | Global.
End LookupType.

Module LookupScope.
  Inductive t : Set :=
  | Global
  | Regional.
End LookupScope.

Module SymbolicLookup.
  Record t : Set := {
    values : list Z;
    multiplicity : Z;
    kind : LookupType.t;
    scope : LookupScope.t;
  }.
End SymbolicLookup.
