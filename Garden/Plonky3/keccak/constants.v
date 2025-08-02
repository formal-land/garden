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

(*
pub(crate) const R: [[u8; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
*)
Definition R : Array.t (Array.t Z 5) 5 :=
  let content := [
    [0; 36; 3; 41; 18];
    [1; 44; 10; 45; 2];
    [62; 6; 43; 15; 61];
    [28; 55; 25; 21; 56];
    [27; 20; 39; 8; 14]
  ] in
  {|
    Array.get a := {|
      Array.get b :=
        List.nth (Z.to_nat b) (List.nth (Z.to_nat a) content []) 0
    |}
  |}.

(*
pub const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
*)
Definition RC : list Z := [
  0x0000000000000001;
  0x0000000000008082;
  0x800000000000808A;
  0x8000000080008000;
  0x000000000000808B;
  0x0000000080000001;
  0x8000000080008081;
  0x8000000000008009;
  0x000000000000008A;
  0x0000000000000088;
  0x0000000080008009;
  0x000000008000000A;
  0x000000008000808B;
  0x800000000000008B;
  0x8000000000008089;
  0x8000000000008003;
  0x8000000000008002;
  0x8000000000000080;
  0x000000000000800A;
  0x800000008000000A;
  0x8000000080008081;
  0x8000000000008080;
  0x0000000080000001;
  0x8000000080008008
].

(* pub(crate) const fn rc_value_bit(round: usize, bit_index: usize) -> u8 *)
Definition rc_value_bit (round : Z) (bit_index : Z) : bool :=
  let round_constant := List.nth (Z.to_nat round) RC 0 in
  Z.testbit round_constant bit_index.
