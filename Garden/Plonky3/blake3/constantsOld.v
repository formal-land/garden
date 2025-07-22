Require Import Garden.Plonky3.M.

(* pub const BITS_PER_LIMB: usize = 16; *)
Definition BITS_PER_LIMB : Z := 16.

(* pub const U32_LIMBS: usize = 32 / BITS_PER_LIMB; *)
Definition U32_LIMBS : Z := 32 / BITS_PER_LIMB.

(*
// The constants from the reference implementation.
// Saved as pairs of 16 bit integers in [lo, hi] format.
pub(crate) const IV: [[u16; 2]; 8] = [
    [0xE667, 0x6A09],
    [0xAE85, 0xBB67],
    [0xF372, 0x3C6E],
    [0xF53A, 0xA54F],
    [0x527F, 0x510E],
    [0x688C, 0x9B05],
    [0xD9AB, 0x1F83],
    [0xCD19, 0x5BE0],
];
*)
Definition IV : Array.t (Array.t Z 2) 8 :=
  {| Array.value := [
      {| Array.value := [0xE667; 0x6A09] |};
      {| Array.value := [0xAE85; 0xBB67] |};
      {| Array.value := [0xF372; 0x3C6E] |};
      {| Array.value := [0xF53A; 0xA54F] |};
      {| Array.value := [0x527F; 0x510E] |};
      {| Array.value := [0x688C; 0x9B05] |};
      {| Array.value := [0xD9AB; 0x1F83] |};
      {| Array.value := [0xCD19; 0x5BE0] |}
    ]
  |}.

(* const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]; *)
Definition MSG_PERMUTATION : Array.t Z 16 :=
  {| Array.value := [
      2; 6; 3; 10; 7; 0; 4; 13;
      1; 11; 12; 5; 9; 14; 15; 8
    ]
  |}.

(* 
Applying MSG_PERMUTATION to an array of 16 elements.
pub(crate) fn permute<T: Clone>(m: &mut [T; 16]) {
    let mut permuted = m.clone();
    for i in 0..16 {
        permuted[i] = m[MSG_PERMUTATION[i]].clone();
    }
    *m = permuted;
}
 *)
Definition permute {T : Set} (m : Array.t T 16) : M.t (Array.t T 16) :=
  [[
    Array.from_fn (N := 16) (| fun i => [[
      let* idx := [[ Array.get (| MSG_PERMUTATION, i |) ]] in
      [[ Array.get (| m, idx |) ]]
    ]] |)
  ]].