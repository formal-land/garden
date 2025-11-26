Require Import Garden.Plonky3.M.

(** For word and bytes *)
Definition BYTE_SIZE : Z := 8.
Definition WORD_SIZE : Z := 4.
Definition LONG_WORD_SIZE : Z := 2 * WORD_SIZE.

(** Chip Data Parallelism *)
Definition ADD_SUB_DATAPAR : Z := 1.
Definition MUL_DATAPAR : Z := 1.
Definition DIVREM_DATAPAR : Z := 1.
Definition LT_DATAPAR : Z := 1.
Definition SLL_DATAPAR : Z := 1.
Definition SR_DATAPAR : Z := 1.
Definition BITWISE_DATAPAR : Z := 1.
Definition MEMORY_RW_DATAPAR : Z := 1.
Definition LOCAL_MEMORY_DATAPAR : Z := 4.
Definition RISCV_POSEIDON2_DATAPAR : Z := 4.

Definition BASE_ALU_DATAPAR : Z := 2.
Definition EXT_ALU_DATAPAR : Z := 4.
Definition VAR_MEM_DATAPAR : Z := 4.
Definition CONST_MEM_DATAPAR : Z := 1.
Definition SELECT_DATAPAR : Z := 2.
Definition POSEIDON2_DATAPAR : Z := 1.

Definition NUM_BITS : Z := 31.
