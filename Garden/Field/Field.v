(** * The scalar field [Z/pZ]

    Primality ([IsPrime := Znumtheory.prime]) and the field-element layer over
    [Z] reduced [mod p]: arithmetic ([UnOp]/[BinOp], notations [+F] [-F] [*F],
    [mod_inverse]), the integral-domain lemma ([mul_zero_implies_zero]), and small
    modular-arithmetic helpers. Companion files:
    [Field.Fermat] (Fermat's little theorem), [Field.Div] (field division)
    and [Field.Pow2] (generic [Z] power and division facts, no modulus). *)

Require Export Stdlib.PArith.BinPosDef.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.
Require Export Stdlib.ZArith.Znumtheory.

Require Export RecordUpdate.

From Stdlib Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.
Require Garden.Field.Primality.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

(** Primality is the number-theoretic predicate from the standard library, so
    [Prime p] carries field content (no zero divisors, inverses, Fermat). *)
Definition IsPrime : Z -> Prop := Znumtheory.prime.
Require Export Stdlib.Strings.PrimString.
Class Prime (p : Z) : Prop := {
  is_prime : IsPrime p;
}.

Lemma prime_range : forall {p} `{Prime p}, 1 < p.
Proof.
  intros p [Hp]. apply Znumtheory.prime_ge_2 in Hp. lia.
Qed.
Module Primes.
  Definition t_q : Z := 45560315531506369815346746415080538113.

  Definition t_p : Z := 45560315531419706090280762371685220353.

  Definition pallas_p : Z := 2 ^ 254 + t_p.

  Definition pallas_q : Z := 2 ^ 254 + t_q.

  Definition mersenne31 : Z := 2 ^ 31 - 1.

  Definition baby_bear : Z := 2 ^ 31 - 2 ^ 27 + 1.

  Definition koala_bear : Z := 2 ^ 31 - 2 ^ 24 + 1.

  Definition goldilocks : Z := 2 ^ 64 - 2 ^ 32 + 1.

  (* Size bounds on the Pallas base-field modulus.  The two forms are named
     apart because the callers differ: slice arguments need only positivity,
     while the ladder needs [2 <] to place a residue strictly inside the
     field. *)
  Lemma pallas_p_pos : 0 < pallas_p.
  Proof. unfold pallas_p, t_p; lia. Qed.

  Lemma pallas_p_gt_2 : 2 < pallas_p.
  Proof. unfold pallas_p, t_p; lia. Qed.

  (* The following six facts are [Znumtheory.prime c] statements for concrete
     constants, discharged by the Coqprime Pocklington certificates of
     [Garden.Field.Primality] (axiom-free reflexive checks). *)
  Lemma pallas_p_prime : IsPrime pallas_p.
  Proof. exact Primality.pallas_p_is_prime. Qed.

  Lemma pallas_q_prime : IsPrime pallas_q.
  Proof. exact Primality.pallas_q_is_prime. Qed.

  Lemma mersenne31_prime : IsPrime mersenne31.
  Proof. exact Primality.mersenne31_is_prime. Qed.

  Lemma baby_bear_prime : IsPrime baby_bear.
  Proof. exact Primality.baby_bear_is_prime. Qed.

  Lemma koala_bear_prime : IsPrime koala_bear.
  Proof. exact Primality.koala_bear_is_prime. Qed.

  Lemma goldilocks_prime : IsPrime goldilocks.
  Proof. exact Primality.goldilocks_is_prime. Qed.

  Global Instance PallasPIsPrime : Prime pallas_p := {
    is_prime := pallas_p_prime;
  }.

  Global Instance PallasQIsPrime : Prime pallas_q := {
    is_prime := pallas_q_prime;
  }.

  Global Instance Mersenne31IsPrime : Prime mersenne31 := {
    is_prime := mersenne31_prime;
  }.

  Global Instance BabyBearIsPrime : Prime baby_bear := {
    is_prime := baby_bear_prime;
  }.

  Global Instance KoalaBearIsPrime : Prime koala_bear := {
    is_prime := koala_bear_prime;
  }.

  Global Instance GoldilocksIsPrime : Prime goldilocks := {
    is_prime := goldilocks_prime;
  }.
End Primes.
Class MapMod {p : Z} `{Prime p} (A : Set) : Set := {
  map_mod : A -> A;
}.
Module InField.
  Class C {p} `{Prime p} (z : Z) : Prop := {
    make : z = z mod p;
  }.

  Global Instance mod_is_in_field {p} `{Prime p} (z : Z) : InField.C (z mod p).
  Proof.
    constructor.
    pose proof (prime_range (p := p)).
    now rewrite Z.mod_mod by lia.
  Qed.
End InField.

(* Square-and-multiply modular exponentiation, a general
   modular-exponentiation primitive (e.g. behind the quadratic-nonresidue check
   in [ecc/chip/spec.v]). *)
Fixpoint fast_pow_modulo_positive (acc base modulus : Z) (exponent : positive) : Z :=
  match exponent with
  | xH => (acc * base) mod modulus
  | xO p =>
    fast_pow_modulo_positive acc ((base * base) mod modulus) modulus p
  | xI p =>
    let acc := (acc * base) mod modulus in
    fast_pow_modulo_positive acc ((base * base) mod modulus) modulus p
  end.

(* Extended-Euclid modular inverse. [mod_inv_loop] runs the extended Euclidean
   algorithm on [(r, newr)] carrying the Bezout coefficients [(t, newt)] of the
   first component: it maintains [r ≡ t * a' (mod p)]. On termination
   ([newr = 0]) the current [r] is [gcd] of the initial pair, so for a prime [p]
   and [a' = a mod p <> 0] the returned [t] satisfies [t * a' ≡ 1 (mod p)]. The
   operands shrink through the recursion, so heavy [vm_compute] ladders avoid
   full-width modular exponentiation.
   Correctness ([mod_inverse] inverts a nonzero element) is proved in
   [Field.Div] via the Bezout loop invariant. *)
Fixpoint mod_inv_loop (fuel : nat) (t newt r newr : Z) : Z :=
  match fuel with
  | O => t
  | S f =>
    if newr =? 0 then t
    else
      let q := r / newr in
      mod_inv_loop f newt (t - q * newt) newr (r - q * newr)
  end.

(* A fuel bound of [O(log p)] steps: the extended Euclidean algorithm on values
   below [p] terminates in at most [2 * log2 p + O(1)] steps (each pair of steps
   at least halves the running remainder). *)
Definition mod_inv_fuel (p : Z) : nat := 2 * Z.to_nat (Z.log2 p) + 4.

Definition mod_inverse (a p : Z) : Z :=
  match p with
  | Zpos _ =>
    let a' := a mod p in
    if a' =? 0 then 0
    else (mod_inv_loop (mod_inv_fuel p) 0 1 p a') mod p
  | _ => 0 (* We will always have 1 <= p *)
  end.
Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.

  Definition from {p} `{Prime p} (x : Z) : Z := 
    x mod p.
End UnOp.

Module BinOp.
  Definition add {p} `{Prime p} (x y : Z) : Z :=
    (x + y) mod p.

  Definition sub {p} `{Prime p} (x y : Z) : Z :=
    (x - y) mod p.

  Definition mul {p} `{Prime p} (x y : Z) : Z :=
    (x * y) mod p.

  (* Field division [x *F y^{-1}] via the modular inverse. *)
  Definition div {p} `{Prime p} (x y : Z) : Z :=
    mul x (mod_inverse y p).

  Definition mod_ {p} `{Prime p} (x y : Z) : Z :=
    (x mod y) mod p.
End BinOp.

(* Notations *)
Notation "x +F y" := (BinOp.add x y) (at level 50, left associativity).
Notation "x -F y" := (BinOp.sub x y) (at level 50, left associativity).
Notation "-F x" := (UnOp.opp x) (at level 35, right associativity).
Notation "x *F y" := (BinOp.mul x y) (at level 40, left associativity).

Global Instance ZIsMapMod {p} `{Prime p} : MapMod Z := {
  map_mod := UnOp.from;
}.

Module IsInField.
  Global Instance from_is_in_field {p} `{Prime p} (x : Z) : InField.C (UnOp.from x).
  Proof. typeclasses eauto. Qed.

  Global Instance opp_is_in_field {p} `{Prime p} (x : Z) : InField.C (UnOp.opp x).
  Proof. typeclasses eauto. Qed.

  Global Instance add_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.add x y).
  Proof. typeclasses eauto. Qed.

  Global Instance sub_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.sub x y).
  Proof. typeclasses eauto. Qed.

  Global Instance mul_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.mul x y).
  Proof. typeclasses eauto. Qed.

  Global Instance div_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.div x y).
  Proof. typeclasses eauto. Qed.

  Global Instance mod_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.mod_ x y).
  Proof. typeclasses eauto. Qed.
End IsInField.
Ltac show_equality_modulo :=
  unfold
    UnOp.from,
    BinOp.add,
    BinOp.sub,
    BinOp.mul,
    BinOp.div,
    BinOp.mod_;
  repeat (
    (
      (
        apply Zplus_eqm ||
        apply Zmult_eqm ||
        apply Zopp_eqm
      );
      unfold eqm
    ) ||
    rewrite Zmod_eqm ||
    reflexivity
  ).

(* The integral-domain property, by Euclid's lemma ([prime_mult]): a product is
   zero in the field iff one of the factors is. *)
Lemma mul_zero_implies_zero {p} `{Prime p} (x y : Z) :
  BinOp.mul x y = 0 <->
  UnOp.from x = 0 \/ UnOp.from y = 0.
Proof.
  pose proof (@is_prime p _) as Hpr. unfold IsPrime in Hpr.
  pose proof (@prime_range p _) as Hp1. assert (p <> 0) as Hp0 by lia.
  unfold BinOp.mul, UnOp.from.
  rewrite !Z.mod_divide by exact Hp0.
  split.
  - intros Hd. exact (Znumtheory.prime_mult p Hpr x y Hd).
  - intros [Hd | Hd].
    + apply Z.divide_mul_l. exact Hd.
    + apply Z.divide_mul_r. exact Hd.
Qed.

Lemma mul_zero_implies_zero_3 {p} `{Prime p} (x y z : Z) :
  BinOp.mul (BinOp.mul x y) z = 0 <->
  UnOp.from x = 0 \/ UnOp.from y = 0 \/ UnOp.from z = 0.
Proof.
  rewrite mul_zero_implies_zero.
  replace (UnOp.from _) with (BinOp.mul x y) by show_equality_modulo.
  rewrite mul_zero_implies_zero.
  tauto.
Qed.

(** This lemma is often useful when the value we are comparing to zero is small and known. *)
Lemma is_zero_small {p} `{Prime p} (x : Z) :
  -p < x < p ->
  UnOp.from x = 0 <->
  x = 0.
Proof.
  intros.
  unfold UnOp.from.
  split; intros; [|now subst].
  assert (-p < x < 0 \/ 0 <= x < p) as [] by lia.
  { rewrite <- (Z.mod_unique x p (-1) (p + x)) in *; lia. }
  { rewrite <- (Z.mod_unique x p 0 x) in *; lia. }
Qed.

Lemma sub_zero_equiv {p} `{Prime p} (x y : Z) :
  BinOp.sub x y = 0 <->
  UnOp.from x = UnOp.from y.
Proof.
  unfold BinOp.sub, UnOp.from.
  symmetry.
  apply Z.cong_iff_0.
Qed.
(* could be later moved together to a single module doing modulo arithmetics. *)

(* Utilities used for modulo arithmetics *)
Lemma mod_when_smaller {p : Z} (x : Z) (Hx : 0 <= x < p) :
  x mod p = x.
Proof.
  apply Zmod_small; auto.
Qed.

(* possible referencehttps://math.stackexchange.com/questions/2542245/how-to-prove-chinese-remainder-theorem-by-coq *)
Lemma chinese_remainder_simpler: forall n p a b : Z,
    n <> 0 ->
    p <> 0 ->
    Znumtheory.rel_prime n p ->
    exists x:Z, (x mod n = a mod n) /\ (x mod p = b mod p). 
Proof.
  intros n p a b npos ppos coprime. 
  destruct (Znumtheory.rel_prime_bezout _ _ coprime) as [u v H0].
  exists (a * v * p + b * u * n). split.
  - rewrite Z.mod_add. 2: exact npos.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod n = 1 mod n) as H.
    rewrite H0. reflexivity.
    rewrite Z.add_comm, Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    reflexivity. exact npos.
  - rewrite Z.add_comm, Z.mod_add. 2: exact ppos.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod p = 1 mod p) as H.
    rewrite H0. reflexivity.
    rewrite Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    reflexivity. exact ppos.  
Qed.

(** Binary Chinese Remainder Theorem: if p, q are coprime, then the equation system 
    "x mod p = a /\ x mod q = b" has a unique solution modulo p * q *)
Axiom binary_chinese_remainder_alt : forall (p q x t : Z),
  p <> 0 ->
  q <> 0 ->
  Znumtheory.rel_prime p q ->
  x mod p = t mod p ->
  x mod q = t mod q ->
  x mod (p * q) = t mod (p * q).

Lemma mod_0_range (k : Z) (x : Z) :
    k > 0 ->
    -k < x < k ->
    x mod k = 0 ->
    x = 0.
Proof.
  intros.
  apply Z.mod_divide in H1; [|lia].
  destruct H1 as [c ->].
  assert (c = 0) by nia.
  lia.
Qed.

Module Test_mod_inverse.
  Definition test1 : Z := mod_inverse 3 7.
  Goal test1 = 5.
  Proof.
    now vm_compute.
  Qed.

  Definition test2 : Z := mod_inverse 2 11. 
  Goal test2 = 6.
  Proof.
    now vm_compute.
  Qed.

  Definition test3 : Z := mod_inverse 5 17.
  Goal test3 = 7.
  Proof.
    now vm_compute.
  Qed.

  Definition test4 : Z := mod_inverse 5 (2 ^ 31 - 1).
  Goal test4 = 858993459.
  Proof.
    now vm_compute.
  Qed.
End Test_mod_inverse.
