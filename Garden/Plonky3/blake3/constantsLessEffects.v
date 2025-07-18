Require Import Garden.Plonky3.MLessEffects.

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

Definition IV_val (val1 val2 : Z) : Array.t Z 2 :=
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
        | 0 => IV_val 0xE667 0x6A09
        | 1 => IV_val 0xAE85 0xBB67
        | 2 => IV_val 0xF372 0x3C6E
        | 3 => IV_val 0xF53A 0xA54F
        | 4 => IV_val 0x527F 0x510E
        | 5 => IV_val 0x688C 0x9B05
        | 6 => IV_val 0xD9AB 0x1F83
        | 7 => IV_val 0xCD19 0x5BE0
        | _ => IV_val 0 0 (* Default case, should not happen *)
        end
  |}.
