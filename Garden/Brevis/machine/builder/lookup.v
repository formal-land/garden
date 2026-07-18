Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.M.
Require Import Garden.Brevis.compiler.riscv.opcode.
Require Import Garden.Brevis.compiler.word.
Require Import Garden.Brevis.machine.lookup.

Definition looked_alu
    (opcode : Z)
    (a : Word.t)
    (b : Word.t)
    (c : Word.t)
    (multiplicity : Z) :
    M.t unit :=
  let values :=
    [opcode] ++
    Array.to_list a ++
    Array.to_list b ++
    Array.to_list c in
  looked {|
    SymbolicLookup.values := values;
    SymbolicLookup.multiplicity := multiplicity;
    SymbolicLookup.kind := LookupType.Alu;
    SymbolicLookup.scope := LookupScope.Regional;
  |}.

Definition looking_byte_pair
    (opcode : Z)
    (a1 : Z)
    (a2 : Z)
    (b : Z)
    (c : Z)
    (multiplicity : Z) :
    M.t unit :=
  looking {|
    SymbolicLookup.values := [ opcode; a1; a2; b; c];
    SymbolicLookup.multiplicity := multiplicity;
    SymbolicLookup.kind := LookupType.Byte;
    SymbolicLookup.scope := LookupScope.Regional;
  |}.

Definition looking_rangecheck
    (opcode : ByteOpcode.t)
    (a1 : Z)
    (a2 : Z)
    (b : Z)
    (c : Z)
    (multiplicity : Z) :
    M.t unit :=
  let opcode := ByteOpcode.to_Z opcode in
  looking_byte_pair opcode a1 a2 b c multiplicity.
