Require Import Garden.Plonky3.M.

Module Opcode.
  Inductive t : Set :=
  | ADD
  | SUB
  | XOR
  | OR
  | AND
  | SLL
  | SRL
  | SRA
  | SLT
  | SLTU
  | LB
  | LH
  | LW
  | LBU
  | LHU
  | SB
  | SH
  | SW
  | BEQ
  | BNE
  | BLT
  | BGE
  | BLTU
  | BGEU
  | JAL
  | JALR
  | AUIPC
  | ECALL
  | EBREAK
  | MUL
  | MULH
  | MULHU
  | MULHSU
  | DIV
  | DIVU
  | REM
  | REMU
  | UNIMP.

  Definition to_Z (self : t) : Z :=
    match self with
    | ADD => 0
    | SUB => 1
    | XOR => 2
    | OR => 3
    | AND => 4
    | SLL => 5
    | SRL => 6
    | SRA => 7
    | SLT => 8
    | SLTU => 9
    | LB => 10
    | LH => 11
    | LW => 12
    | LBU => 13
    | LHU => 14
    | SB => 15
    | SH => 16
    | SW => 17
    | BEQ => 18
    | BNE => 19
    | BLT => 20
    | BGE => 21
    | BLTU => 22
    | BGEU => 23
    | JAL => 24
    | JALR => 25
    | AUIPC => 27
    | ECALL => 28
    | EBREAK => 29
    | MUL => 30
    | MULH => 31
    | MULHU => 32
    | MULHSU => 33
    | DIV => 34
    | DIVU => 35
    | REM => 36
    | REMU => 37
    | UNIMP => 39
    end.
End Opcode.

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
