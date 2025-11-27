Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.compiler.riscv.opcode.
Require Import Garden.Brevis.machine.builder.lookup.

Definition slice_range_check_u8 {p} `{Prime p} {N : Z} (input : Array.t Z N) (mult : Z) :
    M.t unit :=
  M.for_in_zero_to_n N (fun i =>
    if i mod 2 =? 0 then
      let b := input.[i] in
      let c :=
        if i + 1 <? N then
          input.[i + 1]
        else
          0 in
      looking_rangecheck
        ByteOpcode.U8Range
        0
        0
        b
        c
        mult
    else
      M.pure tt
  ).
