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

  Global Instance IsMapMod {p} `{Prime p} : MapMod KeccakCols.t := {
    map_mod x := {|
      KeccakCols.step_flags := x.(KeccakCols.step_flags);
      KeccakCols.export := x.(KeccakCols.export);
      KeccakCols.preimage := x.(KeccakCols.preimage);
      KeccakCols.a := x.(KeccakCols.a);
      KeccakCols.c := x.(KeccakCols.c);
      KeccakCols.c_prime := x.(KeccakCols.c_prime);
      KeccakCols.a_prime := x.(KeccakCols.a_prime);
      KeccakCols.a_prime_prime := x.(KeccakCols.a_prime_prime);
      KeccakCols.a_prime_prime_0_0_bits := x.(KeccakCols.a_prime_prime_0_0_bits);
      KeccakCols.a_prime_prime_prime_0_0_limbs := x.(KeccakCols.a_prime_prime_prime_0_0_limbs);
    |};
  }.
End KeccakCols.

Module Impl_KeccakCols.
  (*
  pub fn b(&self, x: usize, y: usize, z: usize) -> T {
      debug_assert!(x < 5);
      debug_assert!(y < 5);
      debug_assert!(z < 64);

      // B is just a rotation of A', so these are aliases for A' registers.
      // From the spec,
      //     B[y, (2x + 3y) % 5] = ROT(A'[x, y], r[x, y])
      // So,
      //     B[x, y] = f((x + 3y) % 5, x)
      // where f(a, b) = ROT(A'[a, b], r[a, b])
      let a = (x + 3 * y) % 5;
      let b = x;
      let rot = R[a][b] as usize;
      self.a_prime[b][a][(z + 64 - rot) % 64]
  }
  *)
  Definition b (self : KeccakCols.t) (x y z : Z) : Z :=
    let a := (x + 3 * y) mod 5 in
    let b := x in
    let rot := (R.(Array.get) a).(Array.get) b in
    ((self.(KeccakCols.a_prime).(Array.get) b).(Array.get) a).(Array.get) ((z + 64 - rot) mod 64).

  (*
  pub fn a_prime_prime_prime(&self, y: usize, x: usize, limb: usize) -> T {
      debug_assert!(y < 5);
      debug_assert!(x < 5);
      debug_assert!(limb < U64_LIMBS);

      if y == 0 && x == 0 {
          self.a_prime_prime_prime_0_0_limbs[limb]
      } else {
          self.a_prime_prime[y][x][limb]
      }
  }
  *)
  Definition a_prime_prime_prime (self : KeccakCols.t) (y x limb : Z) : Z :=
    if (y =? 0) && (x =? 0) then
      (self.(KeccakCols.a_prime_prime_prime_0_0_limbs).(Array.get) limb)
    else
      ((self.(KeccakCols.a_prime_prime).(Array.get) y).(Array.get) x).(Array.get) limb.
End Impl_KeccakCols.

Module U64.
  Definition t : Set :=
    Z.

  Definition to_bits (x : t) : Array.t Z 64 :=
    {|
      Array.get i := Z.b2z (Z.testbit x i)
    |}.
End U64.
