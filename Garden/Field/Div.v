(** * Correctness of [BinOp.div] as field division

    [BinOp.div x y = x *F mod_inverse y p] (see [Field.Field]). This file proves
    that [mod_inverse] (the extended-Euclid loop [mod_inv_loop]) inverts a
    nonzero field element, and hence the field-division law
    [(x / y) *F y = x] (mod p). The inverse correctness rests on the Bezout
    invariant of the loop ([mod_inv_loop_correct]), with coprimality of a
    nonzero residue to the prime modulus supplied by
    [Zgcd_1_rel_prime]/[prime_rel_prime]. The file also proves the
    square-and-multiply exponentiation primitive correct
    ([fast_pow_correct]). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.

Open Scope Z_scope.

(** ** Correctness of the square-and-multiply primitive [fast_pow_modulo_positive] *)

(** Square-and-multiply is correct modulo [m]. *)
Lemma fast_pow_correct (m : Z) (Hm : 0 < m) :
  forall (e : positive) (acc base : Z),
    fast_pow_modulo_positive acc base m e = (acc * base ^ (Z.pos e)) mod m.
Proof.
  induction e as [p IH | p IH | ]; intros acc base; cbn [fast_pow_modulo_positive].
  - rewrite IH.
    rewrite Pos2Z.inj_xI.
    rewrite Zmult_mod.
    rewrite Z.mod_mod by lia.
    rewrite <- (Zpower_mod (base * base) (Z.pos p) m Hm).
    rewrite <- Zmult_mod.
    replace (base * base) with (base ^ 2) by (rewrite Z.pow_2_r; reflexivity).
    rewrite <- Z.pow_mul_r by lia.
    f_equal.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring.
  - rewrite IH.
    rewrite Pos2Z.inj_xO.
    rewrite Zmult_mod.
    rewrite <- (Zpower_mod (base * base) (Z.pos p) m Hm).
    rewrite <- Zmult_mod.
    replace (base * base) with (base ^ 2) by (rewrite Z.pow_2_r; reflexivity).
    rewrite <- Z.pow_mul_r by lia.
    reflexivity.
  - rewrite Z.pow_1_r. reflexivity.
Qed.

(** ** Correctness of the extended-Euclid inverse loop

    [mod_inv_loop] maintains the Bezout invariant [r ≡ t * a' (mod p)] and
    [newr ≡ newt * a' (mod p)]; the pair [(r, newr)] runs the Euclidean
    algorithm, so its gcd is preserved. Once [newr = 0] the current [r] is that
    gcd, and for a prime modulus with [a' <> 0] the gcd is [1], so the returned
    coefficient [t] is the modular inverse. Termination inside the fuel bound
    follows because each pair of steps at least halves the running remainder. *)
Lemma mod_inv_loop_correct (p a' : Z) (Hp : 1 < p) :
  forall (m fuel : nat) (t newt r newr : Z),
    0 <= newr < r ->
    Z.gcd r newr = 1 ->
    r mod p = (t * a') mod p ->
    newr mod p = (newt * a') mod p ->
    newr < 2 ^ (Z.of_nat m) ->
    (2 * m + 1 <= fuel)%nat ->
    (mod_inv_loop fuel t newt r newr * a') mod p = 1.
Proof.
  induction m as [|m' IH]; intros fuel t newt r newr Hrng Hgcd Hr Hnr Hbnd Hfuel.
  - (* [m = 0]: [newr < 2^0 = 1], so [newr = 0] and [r] is the gcd, namely [1]. *)
    change (2 ^ Z.of_nat 0) with 1 in Hbnd.
    assert (Hnewr0 : newr = 0) by lia.
    destruct fuel as [|f]; [lia|].
    cbn [mod_inv_loop]. subst newr. cbn [Z.eqb].
    (* [Z.gcd r 0 = |r| = r] (as [r > 0]) equals [1]. *)
    rewrite Z.gcd_0_r in Hgcd. assert (Hr1 : r = 1) by lia.
    subst r. rewrite (Z.mod_1_l p Hp) in Hr. now rewrite <- Hr.
  - (* [m = S m']: peel two Euclidean steps to halve the remainder. *)
    destruct (Z.eqb_spec newr 0) as [Hz | Hz].
    + (* [newr = 0]: same terminal reasoning as the base case. *)
      subst newr. destruct fuel as [|f]; [lia|].
      cbn [mod_inv_loop Z.eqb].
      rewrite Z.gcd_0_r in Hgcd. assert (Hr1 : r = 1) by lia.
      subst r. rewrite (Z.mod_1_l p Hp) in Hr. now rewrite <- Hr.
    + assert (Hnewr_pos : 0 < newr) by lia.
      destruct fuel as [|f1]; [lia|].
      cbn [mod_inv_loop]. rewrite (proj2 (Z.eqb_neq newr 0) Hz).
      set (q := r / newr).
      set (newt1 := t - q * newt). set (t1 := newt).
      set (newr1 := r - q * newr). set (r1 := newr).
      (* [newr1 = r mod newr]. *)
      assert (Hnewr1 : newr1 = r mod newr).
      { unfold newr1, q. rewrite (Z.mod_eq r newr) by lia. ring. }
      assert (Hr1_rng : 0 <= newr1 < r1).
      { unfold r1. rewrite Hnewr1. apply Z.mod_pos_bound. lia. }
      (* Bezout invariant preserved by one step. *)
      assert (Hr1_inv : r1 mod p = (t1 * a') mod p) by (unfold r1, t1; exact Hnr).
      assert (Hnewr1_inv : newr1 mod p = (newt1 * a') mod p).
      { unfold newr1, newt1.
        rewrite Zminus_mod, Hr, (Zmult_mod q), Hnr, <- (Zmult_mod q).
        rewrite <- Zminus_mod. f_equal. ring. }
      (* gcd preserved: [gcd newr (r mod newr) = gcd r newr]. *)
      assert (Hgcd1 : Z.gcd r1 newr1 = 1).
      { unfold r1. rewrite Hnewr1, Z.gcd_comm, Z.gcd_mod by lia.
        rewrite Z.gcd_comm. exact Hgcd. }
      destruct (Z.eqb_spec newr1 0) as [Hz1 | Hz1].
      * (* Second remainder already zero: [r1 = newr] is the gcd [= 1]. *)
        destruct f1 as [|f2]; [exfalso; clear -Hfuel; lia|].
        cbn [mod_inv_loop]. rewrite Hz1. cbn [Z.eqb].
        rewrite Hz1, Z.gcd_0_r in Hgcd1. unfold r1 in Hgcd1.
        assert (Hnewr_eq1 : newr = 1) by (clear -Hgcd1 Hnewr_pos; lia).
        rewrite Hnewr_eq1, (Z.mod_1_l p Hp) in Hnr.
        unfold t1. now rewrite <- Hnr.
      * assert (Hnewr1_pos : 0 < newr1) by (clear -Hr1_rng Hz1; lia).
        destruct f1 as [|f2]; [exfalso; clear -Hfuel; lia|].
        cbn [mod_inv_loop]. rewrite (proj2 (Z.eqb_neq newr1 0) Hz1).
        set (q2 := r1 / newr1).
        set (newt2 := t1 - q2 * newt1). set (t2 := newt1).
        set (newr2 := r1 - q2 * newr1). set (r2 := newr1).
        assert (Hnewr2 : newr2 = r1 mod newr1).
        { unfold newr2, q2. rewrite (Z.mod_eq r1 newr1) by lia. ring. }
        (* Apply the induction hypothesis to the twice-reduced state. *)
        apply (IH f2 t2 newt2 r2 newr2).
        -- unfold r2. rewrite Hnewr2.
           split; [apply Z.mod_pos_bound; clear -Hnewr1_pos; lia|].
           apply Z.mod_pos_bound. clear -Hnewr1_pos; lia.
        -- unfold r2. rewrite Hnewr2, Z.gcd_comm, Z.gcd_mod
             by (clear -Hz1 Hnewr1_pos; lia).
           rewrite Z.gcd_comm. exact Hgcd1.
        -- unfold r2, t2. exact Hnewr1_inv.
        -- unfold newr2, newt2.
           rewrite Zminus_mod, Hr1_inv, (Zmult_mod q2), Hnewr1_inv,
             <- (Zmult_mod q2), <- Zminus_mod. f_equal. ring.
        -- (* Halving: [2 * newr2 < newr]. *)
           rewrite Hnewr2. unfold r1.
           assert (Hhalf : 2 * (newr mod newr1) < newr).
           { clear -Hnewr1 Hnewr_pos Hnewr1_pos.
             pose proof (Z.mod_pos_bound newr newr1 Hnewr1_pos).
             assert (newr1 < newr) by (rewrite Hnewr1; apply Z.mod_pos_bound; lia).
             pose proof (Z.mod_eq newr newr1 ltac:(lia)) as Hme.
             assert (Hk : 1 <= newr / newr1)
               by (apply Z.div_le_lower_bound; lia).
             assert (Hmul : newr1 * 1 <= newr1 * (newr / newr1))
               by (apply Z.mul_le_mono_nonneg_l; lia).
             lia. }
           replace (Z.of_nat (S m')) with (Z.of_nat m' + 1) in Hbnd
             by (clear - m'; lia).
           rewrite Z.pow_add_r in Hbnd by (clear - m'; lia).
           clear -Hhalf Hbnd Hnewr1_pos. lia.
        -- clear -Hfuel; lia.
Qed.

(** ** The field-inverse and field-division laws *)

(** Reduction of [mod_inverse] for a positive modulus and a nonzero residue,
    stated on a plain [Z] so it can be unfolded without disturbing the [Prime]
    instance. *)
Lemma mod_inverse_pos (a p : Z) :
  0 < p -> a mod p <> 0 ->
  mod_inverse a p = (mod_inv_loop (mod_inv_fuel p) 0 1 p (a mod p)) mod p.
Proof.
  intros Hp Hnz. unfold mod_inverse.
  destruct p as [|p'|p']; try lia.
  now rewrite (proj2 (Z.eqb_neq (a mod Zpos p') 0) Hnz).
Qed.

(** [mod_inverse y p] is a two-sided inverse of [y] for any prime modulus. *)
Lemma mod_inverse_mul_prime {p} `{Prime p} (y : Z) :
  y mod p <> 0 -> BinOp.mul (mod_inverse y p) y = 1.
Proof.
  intros Hnz.
  pose proof (@is_prime p _) as Hpr. unfold IsPrime in Hpr.
  pose proof (@prime_range p _) as Hp1.
  assert (Hp0 : 0 < p) by lia.
  set (a' := y mod p) in *.
  assert (Ha'rng : 0 <= a' < p) by (apply Z.mod_pos_bound; lia).
  assert (Ha'pos : 0 < a') by lia.
  (* [gcd p a' = 1] since [p] is prime and [0 < a' < p]. *)
  assert (Hgcd : Z.gcd p a' = 1).
  { apply Zgcd_1_rel_prime. apply Znumtheory.prime_rel_prime; [exact Hpr|].
    intros Hdiv. pose proof (Z.divide_pos_le _ _ Ha'pos Hdiv). lia. }
  (* The loop returns a Bezout coefficient [L] with [L * a' ≡ 1 (mod p)]. *)
  set (L := mod_inv_loop (mod_inv_fuel p) 0 1 p a').
  assert (HL : (L * a') mod p = 1).
  { unfold L.
    apply (mod_inv_loop_correct p a' Hp1 (S (Z.to_nat (Z.log2 p)))).
    - lia.
    - exact Hgcd.
    - rewrite Z.mod_same by lia. now rewrite Z.mul_0_l, Z.mod_0_l by lia.
    - rewrite Z.mul_1_l. unfold a'. now rewrite Z.mod_mod by lia.
    - rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.log2_nonneg).
      pose proof (Z.log2_spec p Hp0) as [_ Hup]. lia.
    - unfold mod_inv_fuel. lia. }
  (* Package [L] as [mod_inverse y p] and conclude. *)
  unfold BinOp.mul.
  rewrite (mod_inverse_pos y p Hp0 Hnz).
  fold a'. fold L.
  rewrite Zmult_mod_idemp_l.
  rewrite <- (Zmult_mod_idemp_r y L). fold a'. exact HL.
Qed.

(** [mod_inverse y p] is a two-sided inverse of [y] in the field. *)
Lemma mod_inverse_mul {p} `{Prime p} (y : Z) :
  2 < p -> y mod p <> 0 -> BinOp.mul (mod_inverse y p) y = 1.
Proof.
  intros _ Hnz. exact (mod_inverse_mul_prime y Hnz).
Qed.

(** The defining law of field division: [(x / y) *F y = x] (reduced) for a
    nonzero divisor [y]. *)
Lemma div_mul {p} `{Prime p} (x y : Z) :
  2 < p -> y mod p <> 0 -> BinOp.mul (BinOp.div x y) y = x mod p.
Proof.
  intros Hp2 Hnz.
  pose proof (mod_inverse_mul (p := p) y Hp2 Hnz) as Hinv.
  unfold BinOp.mul in Hinv.
  unfold BinOp.div, BinOp.mul.
  rewrite Zmult_mod_idemp_l.
  replace (x * mod_inverse y p * y) with (x * (mod_inverse y p * y)) by ring.
  rewrite <- Zmult_mod_idemp_r.
  rewrite Hinv.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.
