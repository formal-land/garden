Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.constants.

(*
pub struct KeccakCols<T> {
    pub step_flags: [T; NUM_ROUNDS],
    pub export: T,
    pub preimage: [[[T; U64_LIMBS]; 5]; 5],
    pub a: [[[T; U64_LIMBS]; 5]; 5],
    pub c: [[T; 64]; 5],
    pub c_prime: [[T; 64]; 5],
    pub a_prime: [[[T; 64]; 5]; 5],
    pub a_prime_prime: [[[T; U64_LIMBS]; 5]; 5],
    pub a_prime_prime_0_0_bits: [T; 64],
    pub a_prime_prime_prime_0_0_limbs: [T; U64_LIMBS],
}
*)
Module KeccakCols.
  Record t : Set := {
    step_flags : Array.t Z NUM_ROUNDS;
    export : Z;
    preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    c : Array.t (Array.t Z 64) 5;
    c_prime : Array.t (Array.t Z 64) 5;
    a_prime : Array.t (Array.t (Array.t Z 64) 5) 5;
    a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a_prime_prime_0_0_bits : Array.t Z 64;
    a_prime_prime_prime_0_0_limbs : Array.t Z U64_LIMBS;
  }.

  Module Valid.
    Record t (x : t) : Prop := {
      step_flags : Array.Valid.t (fun _ => True) x.(step_flags);
      preimage : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun _ => True))) x.(preimage);
      a : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun _ => True))) x.(a);
      c : Array.Valid.t (Array.Valid.t (fun _ => True)) x.(c);
      c_prime : Array.Valid.t (Array.Valid.t (fun _ => True)) x.(c_prime);
      a_prime : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun _ => True))) x.(a_prime);
      a_prime_prime : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun _ => True))) x.(a_prime_prime);
      a_prime_prime_0_0_bits : Array.Valid.t (fun _ => True) x.(a_prime_prime_0_0_bits);
      a_prime_prime_prime_0_0_limbs : Array.Valid.t (fun _ => True) x.(a_prime_prime_prime_0_0_limbs);
    }.
  End Valid.
End KeccakCols.
