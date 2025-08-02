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

Definition double_val (val1 val2 : Z) : Array.t Z 2 :=
  {| Array.get i := 
        match i with
        | 0 => val1
        | 1 => val2
        | _ => 0 (* Default case, should not happen *)
        end
  |}.

Definition IV : Array.t (Array.t Z 2) 8 :=
  {|
    Array.get i :=
        match i with
        | 0 => double_val 0xE667 0x6A09
        | 1 => double_val 0xAE85 0xBB67
        | 2 => double_val 0xF372 0x3C6E
        | 3 => double_val 0xF53A 0xA54F
        | 4 => double_val 0x527F 0x510E
        | 5 => double_val 0x688C 0x9B05
        | 6 => double_val 0xD9AB 0x1F83
        | 7 => double_val 0xCD19 0x5BE0
        | _ => double_val 0 0 (* Default case, should not happen *)
        end
  |}.



(* const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]; *)
Definition MSG_PERMUTATION : Array.t Z 16 :=
  {| Array.get i :=
        match i with
        | 0 => 2
        | 1 => 6
        | 2 => 3
        | 3 => 10
        | 4 => 7
        | 5 => 0   
        | 6 => 4
        | 7 => 13
        | 8 => 1
        | 9 => 11
        | 10 => 12
        | 11 => 5
        | 12 => 9
        | 13 => 14
        | 14 => 15
        | 15 => 8
        | _ => -1 (* Default case, should not happen *)
        end
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
Definition permute {T : Set} (m : Array.t T 16) : Array.t T 16 :=
  {|
    Array.get i :=
      let idx := Array.get MSG_PERMUTATION i in
      Array.get m idx
  |}.