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

Module KeccakColsExplicit.
  Record t : Set := {
    step_flags : ExplicitArray.t Z NUM_ROUNDS;
    export : Z;
    preimage : ExplicitArray.t (ExplicitArray.t (ExplicitArray.t Z U64_LIMBS) 5) 5;
    a : ExplicitArray.t (ExplicitArray.t (ExplicitArray.t Z U64_LIMBS) 5) 5;
    c : ExplicitArray.t (ExplicitArray.t Z 64) 5;
    c_prime : ExplicitArray.t (ExplicitArray.t Z 64) 5;
    a_prime : ExplicitArray.t (ExplicitArray.t (ExplicitArray.t Z 64) 5) 5;
    a_prime_prime : ExplicitArray.t (ExplicitArray.t (ExplicitArray.t Z U64_LIMBS) 5) 5;
    a_prime_prime_0_0_bits : ExplicitArray.t Z 64;
    a_prime_prime_prime_0_0_limbs : ExplicitArray.t Z U64_LIMBS;
  }.
End KeccakColsExplicit.

Module StepFlagsInput.
  Record t : Set := {
    step_flag0 : Z;
    step_flag1 : Z;
    step_flag2 : Z;
    step_flag3 : Z;
    step_flag4 : Z;
    step_flag5 : Z;
    step_flag6 : Z;
    step_flag7 : Z;
    step_flag8 : Z;
    step_flag9 : Z;
    step_flag10 : Z;
    step_flag11 : Z;
    step_flag12 : Z;
    step_flag13 : Z;
    step_flag14 : Z;
    step_flag15 : Z;
    step_flag16 : Z;
    step_flag17 : Z;
    step_flag18 : Z;
    step_flag19 : Z;
    step_flag20 : Z;
    step_flag21 : Z;
    step_flag22 : Z;
    step_flag23 : Z;
  }.

  Definition to_value (x : t) : Array.t Z NUM_ROUNDS :=
    {|
      Array.value :=
        [ x.(step_flag0); x.(step_flag1); x.(step_flag2); x.(step_flag3); x.(step_flag4); x.(step_flag5);
          x.(step_flag6); x.(step_flag7); x.(step_flag8); x.(step_flag9); x.(step_flag10); x.(step_flag11);
          x.(step_flag12); x.(step_flag13); x.(step_flag14); x.(step_flag15); x.(step_flag16); x.(step_flag17);
          x.(step_flag18); x.(step_flag19); x.(step_flag20); x.(step_flag21); x.(step_flag22); x.(step_flag23)
        ]
    |}.
End StepFlagsInput.

Module StepFlagsOutput.
  Definition t : Set :=
    Z.

  Definition to_value (x : t) : Array.t Z NUM_ROUNDS :=
    Array.from_fn_pure (fun i =>
      if i =? x then 1 else 0
    ).
End StepFlagsOutput.
