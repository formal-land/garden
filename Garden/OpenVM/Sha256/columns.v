Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.Sha256.utils.

(*
pub struct Sha256FlagsCols<T> {
    pub is_round_row: T,
    pub is_first_4_rows: T,
    pub is_digest_row: T,
    pub is_last_block: T,
    pub row_idx: [T; SHA256_ROW_VAR_CNT],
    pub global_block_idx: T,
    pub local_block_idx: T,
}
*)
Module Sha256FlagsCols.
  Record t {T : Set} : Set := {
    is_round_row : T;
    is_first_4_rows : T;
    is_digest_row : T;
    is_last_block : T;
    row_idx : Array.t T SHA256_ROW_VAR_CNT;
    global_block_idx : T;
    local_block_idx : T;
  }.
  Arguments t : clear implicits.

  Definition map {T1 T2 : Set} (f : T1 -> T2) (self : t T1) : t T2 := {|
    Sha256FlagsCols.is_round_row := f self.(Sha256FlagsCols.is_round_row);
    Sha256FlagsCols.is_first_4_rows := f self.(Sha256FlagsCols.is_first_4_rows);
    Sha256FlagsCols.is_digest_row := f self.(Sha256FlagsCols.is_digest_row);
    Sha256FlagsCols.is_last_block := f self.(Sha256FlagsCols.is_last_block);
    Sha256FlagsCols.row_idx := Array.map f self.(Sha256FlagsCols.row_idx);
    Sha256FlagsCols.global_block_idx := f self.(Sha256FlagsCols.global_block_idx);
    Sha256FlagsCols.local_block_idx := f self.(Sha256FlagsCols.local_block_idx);
  |}.

  Global Instance IsGenerateVar : MGenerateVar.C (t Var.t) := {
    generate :=
      [[
        {|
          Sha256FlagsCols.is_round_row := MGenerateVar.generate (||);
          Sha256FlagsCols.is_first_4_rows := MGenerateVar.generate (||);
          Sha256FlagsCols.is_digest_row := MGenerateVar.generate (||);
          Sha256FlagsCols.is_last_block := MGenerateVar.generate (||);
          Sha256FlagsCols.row_idx := MGenerateVar.generate (||);
          Sha256FlagsCols.global_block_idx := MGenerateVar.generate (||);
          Sha256FlagsCols.local_block_idx := MGenerateVar.generate (||);
        |}
      ]];
  }.
End Sha256FlagsCols.

(*
pub struct Sha256WorkVarsCols<T> {
    /// `a` and `e` after each iteration as 32-bits
    pub a: [[T; SHA256_WORD_BITS]; SHA256_ROUNDS_PER_ROW],
    pub e: [[T; SHA256_WORD_BITS]; SHA256_ROUNDS_PER_ROW],
    /// The carry's used for addition during each iteration when computing `a` and `e`
    pub carry_a: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW],
    pub carry_e: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW],
}
*)
Module Sha256WorkVarsCols.
  Record t {T : Set} : Set := {
    a : Array.t (Array.t T SHA256_WORD_BITS) SHA256_ROUNDS_PER_ROW;
    e : Array.t (Array.t T SHA256_WORD_BITS) SHA256_ROUNDS_PER_ROW;
    carry_a : Array.t (Array.t T SHA256_WORD_U16S) SHA256_ROUNDS_PER_ROW;
    carry_e : Array.t (Array.t T SHA256_WORD_U16S) SHA256_ROUNDS_PER_ROW;
  }.
  Arguments t : clear implicits.

  Global Instance IsGenerateVar : MGenerateVar.C (t Var.t) := {
    generate :=
      [[
        {|
          Sha256WorkVarsCols.a := MGenerateVar.generate (||);
          Sha256WorkVarsCols.e := MGenerateVar.generate (||);
          Sha256WorkVarsCols.carry_a := MGenerateVar.generate (||);
          Sha256WorkVarsCols.carry_e := MGenerateVar.generate (||);
        |}
      ]];
  }.
End Sha256WorkVarsCols.

(*
pub struct Sha256MessageHelperCols<T> {
    pub w_3: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW - 1],
    pub intermed_4: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW],
    pub intermed_8: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW],
    pub intermed_12: [[T; SHA256_WORD_U16S]; SHA256_ROUNDS_PER_ROW],
}
*)
Module Sha256MessageHelperCols.
  Record t {T : Set} : Set := {
    w_3 : Array.t (Array.t T SHA256_WORD_U16S) (SHA256_ROUNDS_PER_ROW - 1);
    intermed_4 : Array.t (Array.t T SHA256_WORD_U16S) SHA256_ROUNDS_PER_ROW;
    intermed_8 : Array.t (Array.t T SHA256_WORD_U16S) SHA256_ROUNDS_PER_ROW;
    intermed_12 : Array.t (Array.t T SHA256_WORD_U16S) SHA256_ROUNDS_PER_ROW;
  }.
  Arguments t : clear implicits.

  Global Instance IsGenerateVar : MGenerateVar.C (t Var.t) := {
    generate :=
      [[
        {|
          Sha256MessageHelperCols.w_3 := MGenerateVar.generate (||);
          Sha256MessageHelperCols.intermed_4 := MGenerateVar.generate (||);
          Sha256MessageHelperCols.intermed_8 := MGenerateVar.generate (||);
          Sha256MessageHelperCols.intermed_12 := MGenerateVar.generate (||);
        |}
      ]];
  }.
End Sha256MessageHelperCols.
(*
pub struct Sha256DigestCols<T> {
    pub flags: Sha256FlagsCols<T>,
    pub hash: Sha256WorkVarsCols<T>,
    pub schedule_helper: Sha256MessageHelperCols<T>,
    pub final_hash: [[T; SHA256_WORD_U8S]; SHA256_HASH_WORDS],
    pub prev_hash: [[T; SHA256_WORD_U16S]; SHA256_HASH_WORDS],
}
*)
Module Sha256DigestCols.
  Record t {T : Set} : Set := {
    flags : Sha256FlagsCols.t T;
    hash : Sha256WorkVarsCols.t T;
    schedule_helper : Sha256MessageHelperCols.t T;
    final_hash : Array.t (Array.t T SHA256_WORD_U8S) SHA256_HASH_WORDS;
    prev_hash : Array.t (Array.t T SHA256_WORD_U16S) SHA256_HASH_WORDS;
  }.
  Arguments t : clear implicits.

  Global Instance IsGenerateVar : MGenerateVar.C (t Var.t) := {
    generate :=
      [[
        {|
          Sha256DigestCols.flags := MGenerateVar.generate (||);
          Sha256DigestCols.hash := MGenerateVar.generate (||);
          Sha256DigestCols.schedule_helper := MGenerateVar.generate (||);
          Sha256DigestCols.final_hash := MGenerateVar.generate (||);
          Sha256DigestCols.prev_hash := MGenerateVar.generate (||);
        |}
      ]];
  }.
End Sha256DigestCols.
