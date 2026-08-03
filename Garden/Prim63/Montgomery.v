(** * Five-word radix-[2^63] Montgomery arithmetic

    The executable path uses only primitive [Uint63] operations.  Each CIOS
    round performs two complete MAC sweeps.  The carry beyond word five from
    the first sweep is retained and combined with the second sweep's carry
    before the radix-word shift. *)

From Stdlib Require Import ZArith Bool.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.

Local Open Scope Z_scope.

Module Type Prim63MontgomeryConfig.
  Import Prim63Words.

  Parameter modulus_Z : Z.
  Parameter modulus : words5.
  Parameter n0_prime : word.
  Parameter montgomery_one : words5.
  Parameter r2 : words5.
  Parameter r_inverse_Z : Z.

  Parameter modulus_words_correct : eval5 modulus = modulus_Z.
  Parameter modulus_positive : 0 < modulus_Z.
  Parameter twice_modulus_fits : 2 * modulus_Z < radix5.
  Parameter n0_prime_correct :
    (Uint63.to_Z modulus.(w0) * Uint63.to_Z n0_prime + 1) mod radix = 0.
  Parameter montgomery_one_correct :
    eval5 montgomery_one = radix5 mod modulus_Z.
  Parameter r2_correct :
    eval5 r2 = (radix5 * radix5) mod modulus_Z.
  Parameter r_inverse_correct :
    (radix5 * r_inverse_Z) mod modulus_Z = 1.
End Prim63MontgomeryConfig.

Module Prim63Montgomery (C : Prim63MontgomeryConfig).
  Import Prim63Words.

  Definition t := words5.

  Definition zero : t := zero5.
  Definition one : t := C.montgomery_one.

  Definition equal (a b : t) : bool :=
    andb (PrimInt63.eqb a.(w0) b.(w0))
      (andb (PrimInt63.eqb a.(w1) b.(w1))
        (andb (PrimInt63.eqb a.(w2) b.(w2))
          (andb (PrimInt63.eqb a.(w3) b.(w3))
            (PrimInt63.eqb a.(w4) b.(w4))))).

  (** Unsigned little-endian comparison. *)
  Definition less_than (a b : t) : bool :=
    if PrimInt63.eqb a.(w4) b.(w4) then
      if PrimInt63.eqb a.(w3) b.(w3) then
        if PrimInt63.eqb a.(w2) b.(w2) then
          if PrimInt63.eqb a.(w1) b.(w1) then
            PrimInt63.ltb a.(w0) b.(w0)
          else PrimInt63.ltb a.(w1) b.(w1)
        else PrimInt63.ltb a.(w2) b.(w2)
      else PrimInt63.ltb a.(w3) b.(w3)
    else PrimInt63.ltb a.(w4) b.(w4).

  Definition less_equal (a b : t) : bool :=
    orb (less_than a b) (equal a b).

  Definition add_step (a b : word) (carry : bool) : word * bool :=
    match if carry then PrimInt63.addcarryc a b else PrimInt63.addc a b with
    | C0 r => (r, false)
    | C1 r => (r, true)
    end.

  Definition sub_step (a b : word) (borrow : bool) : word * bool :=
    match if borrow then PrimInt63.subcarryc a b else PrimInt63.subc a b with
    | C0 r => (r, false)
    | C1 r => (r, true)
    end.

  Definition add_raw (a b : t) : t * bool :=
    let '(r0, c0) := add_step a.(w0) b.(w0) false in
    let '(r1, c1) := add_step a.(w1) b.(w1) c0 in
    let '(r2, c2) := add_step a.(w2) b.(w2) c1 in
    let '(r3, c3) := add_step a.(w3) b.(w3) c2 in
    let '(r4, c4) := add_step a.(w4) b.(w4) c3 in
    ({| w0 := r0; w1 := r1; w2 := r2; w3 := r3; w4 := r4 |}, c4).

  Definition sub_raw (a b : t) : t * bool :=
    let '(r0, c0) := sub_step a.(w0) b.(w0) false in
    let '(r1, c1) := sub_step a.(w1) b.(w1) c0 in
    let '(r2, c2) := sub_step a.(w2) b.(w2) c1 in
    let '(r3, c3) := sub_step a.(w3) b.(w3) c2 in
    let '(r4, c4) := sub_step a.(w4) b.(w4) c3 in
    ({| w0 := r0; w1 := r1; w2 := r2; w3 := r3; w4 := r4 |}, c4).

  Definition subtract_modulus (a : t) : t := fst (sub_raw a C.modulus).

  Definition reduce_once (a : t) : t :=
    if less_equal C.modulus a then subtract_modulus a else a.

  (** One CIOS round.  [top1] is the carry beyond the sixth word from the
      multiplication sweep; [sweep2] adds rather than overwrites it. *)
  Definition montgomery_step (b : t) (a_i : word) (acc : words6) : words6 :=
    let '(s1, top1) := sweep acc a_i b in
    let u := PrimInt63.mul s1.(x0) C.n0_prime in
    let '(s2, top2) := sweep2 s1 top1 u C.modulus in
    shift7 s2 top2.

  Definition montgomery_reduce (a b : t) : t :=
    let s0 := zero6 in
    let s1 := montgomery_step b a.(w0) s0 in
    let s2 := montgomery_step b a.(w1) s1 in
    let s3 := montgomery_step b a.(w2) s2 in
    let s4 := montgomery_step b a.(w3) s3 in
    let s5 := montgomery_step b a.(w4) s4 in
    reduce_once (low5 s5).

  Definition mul : t -> t -> t := montgomery_reduce.
  Definition square (a : t) : t := mul a a.

  Definition add (a b : t) : t :=
    let '(s, _) := add_raw a b in
    reduce_once s.

  Definition sub (a b : t) : t :=
    let '(d, borrow) := sub_raw a b in
    if borrow then fst (add_raw d C.modulus) else d.

  Definition neg (a : t) : t :=
    if equal a zero then zero else fst (sub_raw C.modulus a).

  Definition words_of_nonnegative (z : Z) : words5 :=
    {| w0 := Uint63.of_Z z;
       w1 := Uint63.of_Z (z / radix);
       w2 := Uint63.of_Z (z / radix ^ 2);
       w3 := Uint63.of_Z (z / radix ^ 3);
       w4 := Uint63.of_Z (z / radix ^ 4) |}.

  Definition standard_of_Z (z : Z) : words5 :=
    words_of_nonnegative (z mod C.modulus_Z).

  Definition encode (standard : words5) : t := mul standard C.r2.
  Definition decode (a : t) : words5 := mul a one5.

  Definition from_Z (z : Z) : t := encode (standard_of_Z z).
  Definition to_Z (a : t) : Z := eval5 (decode a).

  (** Logical interpretation of a Montgomery word tuple.  Unlike [to_Z],
      this does not run a Montgomery multiplication and is intended for
      refinement theorem statements. *)
  Definition denote (a : t) : Z :=
    (eval5 a * C.r_inverse_Z) mod C.modulus_Z.

  Definition canonical (a : t) : Prop := eval5 a < C.modulus_Z.

  Definition get_word (a : words5) (i : word) : word :=
    if PrimInt63.eqb i 0%uint63 then a.(w0) else
    if PrimInt63.eqb i 1%uint63 then a.(w1) else
    if PrimInt63.eqb i 2%uint63 then a.(w2) else
    if PrimInt63.eqb i 3%uint63 then a.(w3) else
    if PrimInt63.eqb i 4%uint63 then a.(w4) else 0%uint63.

  (** Extract an eight-bit digit from a standard (non-Montgomery) tuple.
      Windows 0--31 cover the 255 potentially used bits. *)
  Definition window8_standard (a : words5) (window : word) : word :=
    let bit := PrimInt63.mul window 8%uint63 in
    let limb := PrimInt63.div bit 63%uint63 in
    let offset := PrimInt63.mod bit 63%uint63 in
    let lo := PrimInt63.lsr (get_word a limb) offset in
    let joined :=
      if PrimInt63.leb offset 55%uint63 then lo
      else
        PrimInt63.lor lo
          (PrimInt63.lsl (get_word a (PrimInt63.add limb 1%uint63))
            (PrimInt63.sub 63%uint63 offset)) in
    PrimInt63.land joined 255%uint63.

  Definition window8 (a : t) (window : word) : word :=
    window8_standard (decode a) window.

End Prim63Montgomery.
