(** * Γ-free generic core of the table-fold = group-multiple bridges

    The assignment-free (Γ-free) composition layer behind the per-base
    [<base>_mul_protocol] theorems
    ([Garden/Orchard/circuit_proof/protocol_equiv.v]): over an abstract
    prime-order base point [G], window count [S m], spec table and the three
    per-base certificate hooks (Lagrange x-coordinate agreement, positive QR
    window-sign, non-residue window discriminant), the [EccSpec] windowed
    Lagrange-table fold with the canonical square-root witnesses equals the
    group multiple [PallasModel.repr (Pallas.mul k G)].

    The layer has three independent pieces plus their composition
    ([Section ProtocolMulGen], mirroring the parameterization of the
    [PerBaseTable]/[PerBaseChain] sections of [circuit_proof/ladder/main.v]):

    - WINDOW ([window_point_eq_mul]): each canonical-witness window point
      equals the [repr] of its Weierstrass multiple
      [window_scalar (S m) w d · G].  The x-coordinate is the u-independent
      [fixed_window_point_x_eq_mul_gen]; the y-coordinate is forced through
      [window_y_forced_of_disc] at the multiple, whose hypotheses come from
      the sign-cert hook (transported through [full_table_entry_eq_mul_gen]),
      the disc-cert hook, and the group law.  The multiple's on-curve side
      condition is discharged Γ-free: the window scalar is not divisible by
      [pallas_q] ([mul_window_scalar_ne_identity] — non-last windows by
      magnitude, the last window by a mod-8 residue check), so the multiple
      is not the identity.
    - FOLD ([fixed_scalar_mul_eq_mul_gen]): the Γ-free analogue of
      [partial_sum_eq_mul_gen] over [EccSpec.fixed_scalar_mul_aux] — when
      every window point is the [repr] of a multiple, the complete-addition
      fold from the identity is the [repr] of the summed multiple
      ([Weierstrass.mul_add] through [pallas_repr_add], with the
      [reduced]/[on_curve] closure of [Pallas.mul]).
    - TELESCOPING ([partial_sum_window_scalar_eq]): the window scalars of the
      base-8 digits of [k] sum to [k] for [0 <= k < 8^n] — the [(d + 2)·8^w]
      non-last / offset-correcting last window convention telescopes through
      the base-8 digit recomposition [window_digit_recompose].  Generic in
      the window count [n] (used at [n = 85] and [n = 22]).
    - WRAPPER ([fixed_scalar_mul_canonical_eq_mul]): under the hooks,
      [fixed_scalar_mul tbl k (canonical_us_for tbl k) = repr ([k] G)] for
      [0 <= k < 8^(S m)].

    The per-base instantiations (feeding [<Base>FixedWindowCert.x_check_entry],
    [<Base>WindowSignCert.y_check_entry], [window_disc_qr_<base>_all_Z] and
    the [PallasGenerators]/[PallasGeneratorsOrder] facts) live in
    [circuit_proof/protocol_mul/<base>.v]. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so [is_square]/[field_sqrt]/[fixed_window_point] below are at
   [pallas_p] (every other EC and Orchard file sets this). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   up-to-conversion matching in the forcing-lemma composition below never
   evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent (see
   [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module ProtocolMulCore.
  Import FixedBaseLadder.
  Import OrchardActionInputs.

  (** ** Numeric layer: powers of 8, the window offset sum, and [pallas_q]

      Γ-free integer facts about the signed-radix-8 encoding.  The window
      offset sum [2·(8^m − 1)/7] is bounded by [8^m] and, for [m >= 1], is
      [≡ 2 (mod 8)]; the last-window scalar is therefore [≡ 6 (mod 8)],
      which separates it from [0], [pallas_q] and [−pallas_q] in the
      divisibility check [mul_window_scalar_ne_identity] below. *)

  Lemma pow8_nat_pos (m : nat) : 0 < 8 ^ Z.of_nat m.
  Proof.
    apply Z.pow_pos_nonneg; [lia | apply Nat2Z.is_nonneg].
  Qed.

  (** The one-step unfolding of the offset sum (definitional). *)
  Lemma window_offset_sum_succ (m : nat) :
    FixedBaseTableDefs.window_offset_sum (S m) =
    2 * 8 ^ Z.of_nat m + FixedBaseTableDefs.window_offset_sum m.
  Proof. reflexivity. Qed.

  Lemma window_offset_sum_bound (m : nat) :
    0 <= FixedBaseTableDefs.window_offset_sum m < 8 ^ Z.of_nat m.
  Proof.
    induction m as [| m IH].
    - cbn [FixedBaseTableDefs.window_offset_sum].
      change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
    - rewrite window_offset_sum_succ.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
      pose proof (pow8_nat_pos m). lia.
  Qed.

  Lemma pow8_nat_mod8 (m : nat) :
    (1 <= m)%nat -> 8 ^ Z.of_nat m mod 8 = 0.
  Proof.
    destruct m as [| m]; intro Hm; [lia |].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  Qed.

  Lemma window_offset_sum_mod8 (m : nat) :
    (1 <= m)%nat -> FixedBaseTableDefs.window_offset_sum m mod 8 = 2.
  Proof.
    induction m as [| m IH]; intro Hm; [lia |].
    destruct m as [| m'].
    - reflexivity.
    - rewrite window_offset_sum_succ.
      rewrite Zplus_mod, (IH ltac:(lia)).
      rewrite Zmult_mod, (pow8_nat_mod8 (S m') ltac:(lia)), Z.mul_0_r, Zmod_0_l.
      reflexivity.
  Qed.

  (** The last-window scalar's residue class modulo 8 (for [m >= 1]). *)
  Lemma window_scalar_last_mod8 (m : nat) (d : Z)
      (Hm : (1 <= m)%nat) (Hd : 0 <= d < 8) :
    (d * 8 ^ Z.of_nat m - FixedBaseTableDefs.window_offset_sum m) mod 8 = 6.
  Proof.
    rewrite Zminus_mod.
    rewrite Zmult_mod, (pow8_nat_mod8 m Hm), Z.mul_0_r, Zmod_0_l.
    rewrite (window_offset_sum_mod8 m Hm).
    reflexivity.
  Qed.

  (** The [pallas_q] headroom facts (one [vm_compute] each; [11·8^83 < q] is
      [FixedBaseLadder.pow8_83_lt_pallas_q]). *)
  Lemma pallas_q_mod8 : Pallas.pallas_q mod 8 = 1.
  Proof.
    unfold Pallas.pallas_q, Primes.pallas_q, Primes.t_q. vm_compute. reflexivity.
  Qed.

  Lemma pow8_85_lt_two_pallas_q : 8 ^ 85 < 2 * Pallas.pallas_q.
  Proof.
    unfold Pallas.pallas_q, Primes.pallas_q, Primes.t_q. vm_compute. reflexivity.
  Qed.

  (** ** Partial-sum plumbing *)

  (** Pointwise congruence of [partial_sum] on the summed range. *)
  Lemma partial_sum_ext (f g : nat -> Z) :
    forall n : nat,
      (forall j : nat, (j < n)%nat -> f j = g j) ->
      partial_sum f n = partial_sum g n.
  Proof.
    induction n as [| n IH]; intro Hfg.
    - reflexivity.
    - cbn [partial_sum].
      rewrite IH by (intros j Hj; apply Hfg; lia).
      rewrite (Hfg n ltac:(lia)). reflexivity.
  Qed.

  (** ** TELESCOPING: the window scalars of [k]'s base-8 digits sum to [k]

      [Σ_{w<n} window_scalar n w (window_digit k w) = k] for [0 <= k < 8^n]:
      the non-last windows accumulate [k mod 8^m] plus the offset sum
      ([partial_sum_window_scalar_prefix], by the base-8 digit recomposition
      [window_digit_recompose]), and the last window's [−window_offset_sum]
      cancels the accumulated offset. *)

  (** Base-8 digit recomposition:
      [k mod 8^(m+1) = k mod 8^m + 8^m · digit_m k]. *)
  Lemma window_digit_recompose (k : Z) (m : nat) :
    k mod 8 ^ Z.of_nat (S m) =
    k mod 8 ^ Z.of_nat m + 8 ^ Z.of_nat m * EccSpec.window_digit k m.
  Proof.
    unfold EccSpec.window_digit.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    replace (8 * 8 ^ Z.of_nat m) with (8 ^ Z.of_nat m * 8) by ring.
    apply Z.rem_mul_r.
    - pose proof (pow8_nat_pos m). lia.
    - lia.
  Qed.

  (** The non-last prefix identity: after [m < n] windows the partial sum is
      [k mod 8^m] plus the accumulated offset. *)
  Lemma partial_sum_window_scalar_prefix (n : nat) (k : Z) :
    forall m : nat,
      (m < n)%nat ->
      partial_sum (fun w => window_scalar n w (EccSpec.window_digit k w)) m =
      k mod 8 ^ Z.of_nat m + FixedBaseTableDefs.window_offset_sum m.
  Proof.
    induction m as [| m IH]; intro Hm.
    - cbn [partial_sum FixedBaseTableDefs.window_offset_sum].
      change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r.
      reflexivity.
    - cbn [partial_sum].
      rewrite (IH ltac:(lia)).
      rewrite (window_scalar_nonlast_gen n m (EccSpec.window_digit k m)
                 ltac:(lia)).
      rewrite window_offset_sum_succ.
      rewrite (window_digit_recompose k m).
      ring.
  Qed.

  (** The full telescoping identity, generic in the window count [n]. *)
  Lemma partial_sum_window_scalar_eq (n : nat) (k : Z)
      (Hn : (0 < n)%nat) (Hk : 0 <= k < 8 ^ Z.of_nat n) :
    partial_sum (fun w => window_scalar n w (EccSpec.window_digit k w)) n = k.
  Proof.
    destruct n as [| m]; [lia |].
    cbn [partial_sum].
    rewrite (partial_sum_window_scalar_prefix (S m) k m ltac:(lia)).
    rewrite (window_scalar_last_gen m (EccSpec.window_digit k m)).
    pose proof (window_digit_recompose k m) as Hrec.
    rewrite (Z.mod_small k (8 ^ Z.of_nat (S m)) Hk) in Hrec.
    clear -Hrec. lia.
  Qed.

  (** ** Field helpers for the canonical square-root read-back *)

  Lemma from_add_comm (a b : Z) : UnOp.from (a +F b) = UnOp.from (b +F a).
  Proof.
    unfold BinOp.add, UnOp.from. rewrite Z.add_comm. reflexivity.
  Qed.

  (** [(a + b) − b] reduces to [a] modulo [p]. *)
  Lemma from_add_sub_r (a b : Z) : UnOp.from (a +F b) -F b = UnOp.from a.
  Proof.
    unfold BinOp.add, BinOp.sub, UnOp.from.
    rewrite Zmod_mod, Zminus_mod_idemp_l.
    f_equal. ring.
  Qed.

  (** ** The generic Γ-free composition

      Parameterized like the [PerBaseTable] section of
      [circuit_proof/ladder/main.v]: an abstract on-curve reduced prime-order
      base [G], the last window index [m] (window count [S m], with
      [1 <= m <= 84] — both the 85- and the 22-window Orchard bases satisfy
      it), the per-base spec table, and the three certificate hooks in the
      exact shapes their per-base [vm_compute] certificates export
      ([FixedBaseXCert.x_check_entry], [FixedBaseSignCert.y_check_entry],
      [window_disc_qr_<base>_all_Z]). *)
  Section ProtocolMulGen.
    Variable G : Pallas.point.
    Hypothesis HG_on_curve : Pallas.on_curve G.
    Hypothesis HG_reduced : Pallas.reduced G.

    (** *** FOLD: [fixed_scalar_mul_aux] over per-window multiples

        The Γ-free analogue of [partial_sum_eq_mul_gen]: the accumulator
        invariant is [acc = repr ([s] G)], each step adds one window multiple
        through the [repr] homomorphism ([pallas_repr_add]) and the group
        composition law ([pallas_mul_add]). *)
    Lemma fixed_scalar_mul_aux_eq_mul_gen (k : Z) (us : list Z) (ks : nat -> Z) :
      forall (ws : list EccSpec.fixed_window) (i : nat) (acc : Point.t) (s : Z),
        acc = PallasModel.repr (Pallas.mul s G) ->
        (forall j : nat,
          (j < List.length ws)%nat ->
          EccSpec.fixed_window_point
            (List.nth j ws OrchardActionFixedBase.fixed_window_default)
            (EccSpec.window_digit k (i + j)) (List.nth (i + j)%nat us 0) =
          PallasModel.repr (Pallas.mul (ks (i + j)%nat) G)) ->
        EccSpec.fixed_scalar_mul_aux ws k us i acc =
        PallasModel.repr
          (Pallas.mul
            (s + partial_sum (fun j => ks (i + j)%nat) (List.length ws)) G).
    Proof using HG_on_curve HG_reduced.
      induction ws as [| w ws' IH]; intros i acc s Hacc Hwin.
      - cbn [EccSpec.fixed_scalar_mul_aux List.length partial_sum].
        rewrite Hacc.
        apply (f_equal PallasModel.repr), mul_scalar_eq. lia.
      - cbn [EccSpec.fixed_scalar_mul_aux].
        pose proof (Hwin 0%nat ltac:(cbn [List.length]; lia)) as Hw0.
        rewrite Nat.add_0_r in Hw0.
        cbn [List.nth] in Hw0.
        rewrite Hw0, Hacc.
        rewrite <- (pallas_repr_add (Pallas.mul s G) (Pallas.mul (ks i) G)
          (pallas_mul_reduced s G HG_reduced)
          (pallas_mul_reduced (ks i) G HG_reduced)
          (pallas_mul_on_curve s G HG_on_curve)
          (pallas_mul_on_curve (ks i) G HG_on_curve)).
        rewrite <- (pallas_mul_add s (ks i) G HG_reduced HG_on_curve).
        assert (Hwin' : forall j : nat,
          (j < List.length ws')%nat ->
          EccSpec.fixed_window_point
            (List.nth j ws' OrchardActionFixedBase.fixed_window_default)
            (EccSpec.window_digit k (S i + j)) (List.nth (S i + j)%nat us 0) =
          PallasModel.repr (Pallas.mul (ks (S i + j)%nat) G)).
        { intros j Hj.
          replace (S i + j)%nat with (i + S j)%nat by lia.
          apply (Hwin (S j)). cbn [List.length]. lia. }
        rewrite (IH (S i) _ (s + ks i) eq_refl Hwin').
        apply (f_equal PallasModel.repr), mul_scalar_eq.
        cbn [List.length].
        rewrite <- (partial_sum_shift (fun j => ks (i + j)%nat)
                      (List.length ws')).
        cbn beta.
        rewrite (partial_sum_ext (fun j => ks (i + S j)%nat)
                   (fun j => ks (S i + j)%nat) (List.length ws'))
          by (intros j _; f_equal; lia).
        rewrite Nat.add_0_r. lia.
    Qed.

    (** The FOLD wrapper over [fixed_scalar_mul]: when every window point of
        the [n]-window table [tbl] is the [repr] of the multiple [ks w · G],
        the fold is the [repr] of the summed multiple. *)
    Lemma fixed_scalar_mul_eq_mul_gen
        (tbl : EccSpec.fixed_table) (n : nat) (Hlen : List.length tbl = n)
        (k : Z) (us : list Z) (ks : nat -> Z)
        (Hwindows : forall w : nat,
          (w < n)%nat ->
          EccSpec.fixed_window_point
            (List.nth w tbl OrchardActionFixedBase.fixed_window_default)
            (EccSpec.window_digit k w) (List.nth w us 0) =
          PallasModel.repr (Pallas.mul (ks w) G)) :
      EccSpec.fixed_scalar_mul tbl k us =
      PallasModel.repr (Pallas.mul (partial_sum ks n) G).
    Proof using HG_on_curve HG_reduced.
      assert (Hid : EccSpec.identity = PallasModel.repr (Pallas.mul 0 G))
        by reflexivity.
      assert (Hwin0 : forall j : nat,
        (j < List.length tbl)%nat ->
        EccSpec.fixed_window_point
          (List.nth j tbl OrchardActionFixedBase.fixed_window_default)
          (EccSpec.window_digit k (0 + j)) (List.nth (0 + j)%nat us 0) =
        PallasModel.repr (Pallas.mul (ks (0 + j)%nat) G)).
      { intros j Hj. cbn [Nat.add]. apply Hwindows. lia. }
      unfold EccSpec.fixed_scalar_mul.
      rewrite (fixed_scalar_mul_aux_eq_mul_gen k us ks tbl 0%nat
                 EccSpec.identity 0 Hid Hwin0).
      apply (f_equal PallasModel.repr), mul_scalar_eq.
      rewrite Hlen.
      rewrite (partial_sum_ext (fun j => ks (0 + j)%nat) ks n)
        by (intros j _; f_equal; lia).
      lia.
    Qed.

    (** *** The per-base window layer: table, window count, certificate hooks *)

    (** The last window index; the decomposition has [S m] windows
        ([m = 84] for the full-width bases, [m = 21] for ValueCommitV). *)
    Variable m : nat.
    Hypothesis Hm_ge1 : (1 <= m)%nat.
    Hypothesis Hm_le : (m <= 84)%nat.

    (** The prime-order facts of the base ([PallasGenerators.<base>_ne_identity]
        and [PallasGeneratorsOrder.<base>_order] per base). *)
    Hypothesis HG_ne : G <> Pallas.identity.
    Hypothesis HG_order : Pallas.mul Pallas.pallas_q G = Pallas.identity.

    (** No window scalar is annihilated by [G]: modulo [pallas_q] the non-last
        scalars are separated by magnitude ([0 < (d+2)·8^w <= 9·8^83 < q]) and
        the last scalar by its residue class modulo 8
        ([≡ 6], vs [0 ≡ 0], [q ≡ 1] and [−q ≡ 7], with [|scalar| < 2q]). *)
    Lemma mul_window_scalar_ne_identity (w : nat) (d : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      Pallas.mul (window_scalar (S m) w d) G <> Pallas.identity.
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hm_ge1 Hm_le.
      intro Heq.
      pose proof (proj1 (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p)
        Pallas.a Pallas.b G Pallas.pallas_q Pallas.eleven_lt_p Pallas.nonsingular
        HG_reduced HG_on_curve HG_ne Pallas.pallas_q_is_prime HG_order
        (window_scalar (S m) w d)) Heq) as Hdiv.
      pose proof pow8_83_lt_pallas_q as HQ.
      assert (H83pos : 0 < 8 ^ 83) by (apply Z.pow_pos_nonneg; lia).
      assert (Hq_pos : 0 < Pallas.pallas_q) by lia.
      destruct (Nat.lt_ge_cases w m) as [Hwm | Hwm].
      - (* Non-last window: [0 < (d+2)·8^w < q]. *)
        rewrite (window_scalar_nonlast_gen (S m) w d ltac:(lia)) in Hdiv.
        assert (HP0 : 0 < 8 ^ Z.of_nat w) by apply pow8_nat_pos.
        assert (HPQ : 8 ^ Z.of_nat w <= 8 ^ 83).
        { change 83 with (Z.of_nat 83). apply Z.pow_le_mono_r; lia. }
        assert (Hs_pos : 0 < (d + 2) * 8 ^ Z.of_nat w)
          by (clear -HP0 Hd; nia).
        assert (Hs_ub : (d + 2) * 8 ^ Z.of_nat w <= 9 * 8 ^ Z.of_nat w)
          by (clear -HP0 Hd; nia).
        assert (Hs_lt : (d + 2) * 8 ^ Z.of_nat w < Pallas.pallas_q) by lia.
        pose proof (Z.divide_pos_le _ _ Hs_pos Hdiv) as Hle.
        lia.
      - (* Last window: [d·8^m − offset ≡ 6 (mod 8)] separates it from
           [0], [q] and [−q] inside [(−q, 2q)]. *)
        assert (Hw_eq : w = m) by lia. subst w.
        rewrite (window_scalar_last_gen m d) in Hdiv.
        destruct Hdiv as [t Ht].
        pose proof (window_offset_sum_bound m) as Hoff.
        pose proof (window_scalar_last_mod8 m d Hm_ge1 Hd) as Hs8.
        assert (HP0 : 0 < 8 ^ Z.of_nat m) by apply pow8_nat_pos.
        assert (HP84 : 8 ^ Z.of_nat m <= 8 ^ 84).
        { change 84 with (Z.of_nat 84). apply Z.pow_le_mono_r; lia. }
        assert (Hpow84 : 8 ^ 84 = 8 * 8 ^ 83)
          by (change 84 with (Z.succ 83); apply Z.pow_succ_r; lia).
        assert (Hpow85 : 8 ^ 85 = 8 * 8 ^ 84)
          by (change 85 with (Z.succ 84); apply Z.pow_succ_r; lia).
        assert (Hq_gt84 : 8 ^ 84 < Pallas.pallas_q) by lia.
        pose proof pow8_85_lt_two_pallas_q as H2q.
        assert (Hd_ub : d * 8 ^ Z.of_nat m <= 7 * 8 ^ Z.of_nat m)
          by (clear -HP0 Hd; nia).
        assert (Hd_lb : 0 <= d * 8 ^ Z.of_nat m)
          by (clear -HP0 Hd; nia).
        assert (Hcase : t <= -1 \/ t = 0 \/ t = 1 \/ 2 <= t) by lia.
        destruct Hcase as [Hc | [Hc | [Hc | Hc]]].
        + (* [t <= −1]: the scalar would be [<= −q], below its lower bound. *)
          assert (Htq : t * Pallas.pallas_q <= - Pallas.pallas_q)
            by (clear -Hc Hq_pos; nia).
          lia.
        + (* [t = 0]: the scalar would be [0 ≡ 0 (mod 8)]. *)
          subst t. rewrite Z.mul_0_l in Ht.
          rewrite Ht, Zmod_0_l in Hs8. discriminate Hs8.
        + (* [t = 1]: the scalar would be [q ≡ 1 (mod 8)]. *)
          subst t. rewrite Z.mul_1_l in Ht.
          rewrite Ht, pallas_q_mod8 in Hs8. discriminate Hs8.
        + (* [2 <= t]: the scalar would be [>= 2q], above its upper bound. *)
          assert (Htq : 2 * Pallas.pallas_q <= t * Pallas.pallas_q)
            by (clear -Hc Hq_pos; nia).
          lia.
    Qed.

    (** The multiple's [repr] satisfies the curve polynomial (Γ-free: the
        identity case of [repr] is excluded by
        [mul_window_scalar_ne_identity], replacing the circuit-witnessed
        [x <> 0] route of [repr_mul_on_curve_gen]). *)
    Lemma repr_mul_window_on_curve (w : nat) (d : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      Point.y (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G)) *F
        Point.y (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G)) -F
        (Point.x (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G)) *F
         Point.x (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G)) *F
         Point.x (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G))) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0.
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hm_ge1 Hm_le.
      pose proof (mul_window_scalar_ne_identity w d Hw Hd) as Hne.
      pose proof (pallas_mul_on_curve (window_scalar (S m) w d) G HG_on_curve)
        as Hoc.
      destruct (Pallas.mul (window_scalar (S m) w d) G) as [| x y] eqn:E.
      - exfalso. exact (Hne eq_refl).
      - cbn [PallasModel.repr Point.x Point.y].
        exact (PallasModel.on_curve_affine_poly x y Hoc).
    Qed.

    (** The per-base spec table (the concrete circuit constant). *)
    Variable spec_table : list EccSpec.fixed_window.
    Hypothesis Hspec_len : List.length spec_table = S m.

    (** The Lagrange x-coordinate certificate hook
        ([<Base>FixedWindowCert.x_check_entry], the same shape as the
        [Hx_cert] hypothesis of [PerBaseTable] in
        [circuit_proof/ladder/main.v]). *)
    Hypothesis Hx_cert :
      forall (w i : nat), (w < S m)%nat -> (i < 8)%nat ->
        Point.x
          (EccSpec.fixed_window_point
            (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
            (Z.of_nat i) 0) =
        Point.x
          (PallasModel.repr
            (List.nth i
              (List.nth w
                (FixedBaseTableDefs.nonlast_points m G ++
                 [FixedBaseTableDefs.last_row (FixedBaseTableDefs.base_pow8 m G)
                    (Pallas.mul (FixedBaseTableDefs.window_offset_sum m) G)]) [])
              Pallas.identity)).

    (** The positive QR window-sign certificate hook
        ([<Base>WindowSignCert.y_check_entry]). *)
    Hypothesis Hsign_cert :
      forall (w i : nat), (w < S m)%nat -> (i < 8)%nat ->
        is_square
          (UnOp.from
            (EccSpec.fw_z
              (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
             +F Point.y
                  (PallasModel.repr
                    (List.nth i
                      (List.nth w
                        (FixedBaseTableDefs.nonlast_points m G ++
                         [FixedBaseTableDefs.last_row
                            (FixedBaseTableDefs.base_pow8 m G)
                            (Pallas.mul
                              (FixedBaseTableDefs.window_offset_sum m) G)]) [])
                      Pallas.identity)))) = true.

    (** The non-residue window-discriminant certificate hook
        ([window_disc_qr_<base>_all_Z]). *)
    Hypothesis Hdisc_cert :
      forall (w : nat) (digit : Z), (w < S m)%nat -> 0 <= digit < 8 ->
        is_square
          (window_disc
            (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
            digit) = false.

    (** The positive QR fact at the multiple: the sign-cert hook transported
        through the table-entry bridge [full_table_entry_eq_mul_gen]. *)
    Lemma window_qr_at_mul (w : nat) (d : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      is_square
        (UnOp.from
          (EccSpec.fw_z
            (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
           +F Point.y
                (PallasModel.repr
                  (Pallas.mul (window_scalar (S m) w d) G)))) = true.
    Proof using HG_on_curve HG_reduced Hsign_cert.
      pose proof (Hsign_cert w (Z.to_nat d) Hw ltac:(clear -Hd; lia)) as Hqr.
      rewrite (full_table_entry_eq_mul_gen G HG_on_curve HG_reduced m w d Hw Hd)
        in Hqr.
      exact Hqr.
    Qed.

    (** *** WINDOW: the canonical window point is the multiple

        [window_y_forced_of_disc] applied at
        [M := repr ([window_scalar (S m) w d] G)]: [M]'s x is the window's
        Lagrange interpolation ([fixed_window_point_x_eq_mul_gen]), [M] is on
        the curve ([repr_mul_window_on_curve]), [fw_z + y M] is a residue
        ([window_qr_at_mul]) and the window discriminant is a non-residue
        ([Hdisc_cert]), so [M] is the canonical (QR-sign-selected) window
        point. *)
    Lemma window_point_canonical_eq_mul (w : nat) (d : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G) =
      fixed_window_point_canonical
        (List.nth w spec_table OrchardActionFixedBase.fixed_window_default) d.
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hdisc_cert Hm_ge1 Hm_le
      Hsign_cert Hx_cert.
      apply (window_y_forced_of_disc
        (List.nth w spec_table OrchardActionFixedBase.fixed_window_default) d
        (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G))).
      - (* Hx: the multiple's x is the Lagrange interpolation. *)
        pose proof (fixed_window_point_x_eq_mul_gen G HG_on_curve HG_reduced m
          spec_table Hx_cert w d 0 Hw Hd) as Hx.
        cbn [EccSpec.fixed_window_point Point.x] in Hx.
        exact (eq_sym Hx).
      - exact (repr_mul_window_on_curve w d Hw Hd).
      - exact (window_qr_at_mul w d Hw Hd).
      - exact (Hdisc_cert w d Hw Hd).
      - apply repr_y_reduced. apply pallas_mul_reduced. exact HG_reduced.
    Qed.

    (** WINDOW at the canonical witness: the spec window point at digit
        [window_digit k w] and the canonical square root
        ([canonical_us_for]'s [w]-th entry) is the [repr] of its Weierstrass
        multiple.  The x-coordinate is u-independent; the y-coordinate reads
        the canonical root back through [field_sqrt_sound]
        ([u² − z = y M]). *)
    Lemma window_point_eq_mul (k : Z) (w : nat) (Hw : (w < S m)%nat) :
      EccSpec.fixed_window_point
        (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
        (EccSpec.window_digit k w)
        (List.nth w (canonical_us_for spec_table k) 0) =
      PallasModel.repr
        (Pallas.mul (window_scalar (S m) w (EccSpec.window_digit k w)) G).
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hdisc_cert Hm_ge1 Hm_le
      Hsign_cert Hspec_len Hx_cert.
      pose proof (window_digit_bound k w) as Hd.
      pose proof (window_point_canonical_eq_mul w (EccSpec.window_digit k w)
        Hw Hd) as Hcanon.
      rewrite (canonical_us_for_nth OrchardActionFixedBase.fixed_window_default
        spec_table k w ltac:(rewrite Hspec_len; lia)).
      rewrite <- Hcanon.
      apply point_eq.
      - exact (fixed_window_point_x_eq_mul_gen G HG_on_curve HG_reduced m
          spec_table Hx_cert w (EccSpec.window_digit k w) _ Hw Hd).
      - cbn [EccSpec.fixed_window_point Point.y].
        assert (Hfrom :
          UnOp.from
            (Point.y
              (PallasModel.repr
                (Pallas.mul (window_scalar (S m) w (EccSpec.window_digit k w))
                  G)) +F
             EccSpec.fw_z
               (List.nth w spec_table
                 OrchardActionFixedBase.fixed_window_default)) =
          UnOp.from
            (UnOp.from
              (EccSpec.fw_z
                (List.nth w spec_table
                  OrchardActionFixedBase.fixed_window_default) +F
               Point.y
                 (PallasModel.repr
                   (Pallas.mul
                     (window_scalar (S m) w (EccSpec.window_digit k w)) G))))).
        { rewrite from_idem. apply from_add_comm. }
        assert (Hsq :
          is_square
            (Point.y
              (PallasModel.repr
                (Pallas.mul (window_scalar (S m) w (EccSpec.window_digit k w))
                  G)) +F
             EccSpec.fw_z
               (List.nth w spec_table
                 OrchardActionFixedBase.fixed_window_default)) = true).
        { rewrite (is_square_cong _ _ Hfrom).
          exact (window_qr_at_mul w (EccSpec.window_digit k w) Hw Hd). }
        rewrite (field_sqrt_sound _ Hsq).
        rewrite from_add_sub_r.
        apply repr_y_reduced. apply pallas_mul_reduced. exact HG_reduced.
    Qed.

    (** *** WRAPPER: the canonical-witness fold is the group multiple

        WINDOW + FOLD + TELESCOPING: for [0 <= k < 8^(S m)],
        [fixed_scalar_mul spec_table k (canonical_us_for spec_table k) =
        repr ([k] G)]. *)
    Lemma fixed_scalar_mul_canonical_eq_mul (k : Z)
        (Hk : 0 <= k < 8 ^ Z.of_nat (S m)) :
      EccSpec.fixed_scalar_mul spec_table k (canonical_us_for spec_table k) =
      PallasModel.repr (Pallas.mul k G).
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hdisc_cert Hm_ge1 Hm_le
      Hsign_cert Hspec_len Hx_cert.
      rewrite (fixed_scalar_mul_eq_mul_gen spec_table (S m) Hspec_len k
        (canonical_us_for spec_table k)
        (fun w => window_scalar (S m) w (EccSpec.window_digit k w))
        (fun w Hw => window_point_eq_mul k w Hw)).
      apply (f_equal PallasModel.repr), mul_scalar_eq.
      exact (partial_sum_window_scalar_eq (S m) k ltac:(lia) Hk).
    Qed.
  End ProtocolMulGen.
End ProtocolMulCore.
