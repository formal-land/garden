Require Import Garden.Plonky3.M.

(* pub const SHA256_ROW_VAR_CNT: usize = 5; *)
Definition SHA256_ROW_VAR_CNT : Z := 5.

(* pub const SHA256_ROUNDS_PER_ROW: usize = 4; *)
Definition SHA256_ROUNDS_PER_ROW : Z := 4.

(* pub const SHA256_WORD_BITS: usize = 32; *)
Definition SHA256_WORD_BITS : Z := 32.

(* pub const SHA256_WORD_U16S: usize = SHA256_WORD_BITS / 16; *)
Definition SHA256_WORD_U16S : Z := SHA256_WORD_BITS / 16.

(* pub const SHA256_WORD_U8S: usize = SHA256_WORD_BITS / 8; *)
Definition SHA256_WORD_U8S : Z := SHA256_WORD_BITS / 8.

(* pub const SHA256_HASH_WORDS: usize = 8; *)
Definition SHA256_HASH_WORDS : Z := 8.
