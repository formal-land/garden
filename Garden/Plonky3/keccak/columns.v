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
      KeccakCols.step_flags := M.map_mod x.(KeccakCols.step_flags);
      KeccakCols.export := M.map_mod x.(KeccakCols.export);
      KeccakCols.preimage := M.map_mod x.(KeccakCols.preimage);
      KeccakCols.a := M.map_mod x.(KeccakCols.a);
      KeccakCols.c := M.map_mod x.(KeccakCols.c);
      KeccakCols.c_prime := M.map_mod x.(KeccakCols.c_prime);
      KeccakCols.a_prime := M.map_mod x.(KeccakCols.a_prime);
      KeccakCols.a_prime_prime := M.map_mod x.(KeccakCols.a_prime_prime);
      KeccakCols.a_prime_prime_0_0_bits := M.map_mod x.(KeccakCols.a_prime_prime_0_0_bits);
      KeccakCols.a_prime_prime_prime_0_0_limbs := M.map_mod x.(KeccakCols.a_prime_prime_prime_0_0_limbs);
    |};
  }.

  Global Instance IsGenerate : MGenerate.C KeccakCols.t := {
    generate :=
      [[
        {|
          KeccakCols.step_flags := MGenerate.generate (||);
          KeccakCols.export := MGenerate.generate (||);
          KeccakCols.preimage := MGenerate.generate (||);
          KeccakCols.a := MGenerate.generate (||);
          KeccakCols.c := MGenerate.generate (||);
          KeccakCols.c_prime := MGenerate.generate (||);
          KeccakCols.a_prime := MGenerate.generate (||);
          KeccakCols.a_prime_prime := MGenerate.generate (||);
          KeccakCols.a_prime_prime_0_0_bits := MGenerate.generate (||);
          KeccakCols.a_prime_prime_prime_0_0_limbs := MGenerate.generate (||);
        |}
      ]];
  }.

  Module Eq.
    Record t (x y : KeccakCols.t): Prop := {
      step_flags : Equal.t x.(KeccakCols.step_flags) y.(KeccakCols.step_flags);
      export : Equal.t x.(KeccakCols.export) y.(KeccakCols.export);
      preimage : Equal.t x.(KeccakCols.preimage) y.(KeccakCols.preimage);
      a : Equal.t x.(KeccakCols.a) y.(KeccakCols.a);
      c : Equal.t x.(KeccakCols.c) y.(KeccakCols.c);
      c_prime : Equal.t x.(KeccakCols.c_prime) y.(KeccakCols.c_prime);
      a_prime : Equal.t x.(KeccakCols.a_prime) y.(KeccakCols.a_prime);
      a_prime_prime : Equal.t x.(KeccakCols.a_prime_prime) y.(KeccakCols.a_prime_prime);
      a_prime_prime_0_0_bits : Equal.t x.(KeccakCols.a_prime_prime_0_0_bits) y.(KeccakCols.a_prime_prime_0_0_bits);
      a_prime_prime_prime_0_0_limbs : Equal.t x.(KeccakCols.a_prime_prime_prime_0_0_limbs) y.(KeccakCols.a_prime_prime_prime_0_0_limbs);
    }.
  End Eq.

  Global Instance IsEqual : Equal.C KeccakCols.t := {
    Equal.t := Eq.t;
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
  Definition b_of_a_prime {T : Set}
      (a_prime : Array.t (Array.t (Array.t T 64) 5) 5)
      (x y z : Z) :
      T :=
    let a := (x + 3 * y) mod 5 in
    let b := x in
    let rot := R.[a].[b] in
    a_prime.[b].[a].[(z + 64 - rot) mod 64].

  Definition b (self : KeccakCols.t) (x y z : Z) : Z :=
    b_of_a_prime self.(KeccakCols.a_prime) x y z.

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
      self.(KeccakCols.a_prime_prime_prime_0_0_limbs).[limb]
    else
      self.(KeccakCols.a_prime_prime).[y].[x].[limb].

  Global Instance IsInField {p} `{Prime p} (self' : KeccakCols.t) (y x limb : Z) :
    let self := M.map_mod self' in
    InField.C (a_prime_prime_prime self y x limb).
  Proof.
    unfold a_prime_prime_prime; cbn.
    destruct (_ && _); typeclasses eauto.
  Qed.
End Impl_KeccakCols.

Module a.
  Module Valid.
    Definition t (local : KeccakCols.t) (a : Array.t (Array.t (Array.t bool 64) 5) 5): Prop :=
      forall x, 0 <= x < 5 ->
      forall y, 0 <= y < 5 ->
      forall limb, 0 <= limb < U64_LIMBS ->
      local.(KeccakCols.a).[y].[x].[limb] =
      Limbs.of_bools BITS_PER_LIMB (Array.get a.[y].[x]) limb.
  End Valid.
End a.
