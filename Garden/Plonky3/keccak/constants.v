Require Import Garden.Plonky3.M.

(* pub const NUM_ROUNDS: usize = 24; *)
Definition NUM_ROUNDS : Z := 24.

(* const BITS_PER_LIMB: usize = 16; *)
Definition BITS_PER_LIMB : Z := 16.

(* pub const U64_LIMBS: usize = 64 / BITS_PER_LIMB; *)
Definition U64_LIMBS : Z := 64 / BITS_PER_LIMB.

(* const RATE_BITS: usize = 1088; *)
Definition RATE_BITS : Z := 1088.

(* const RATE_LIMBS: usize = RATE_BITS / BITS_PER_LIMB; *)
Definition RATE_LIMBS : Z := RATE_BITS / BITS_PER_LIMB.
