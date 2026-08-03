(** * Soundness of the witnessed Vesta SSWU evaluator

    This file connects the inexpensive square-root-witness checker to the
    canonical [field_sqrt]-based definition.  The proof is symbolic: no
    concrete hash, square root, or SRS entry is evaluated here. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Sqrt.
Require Import Garden.Field.Lemmas.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.sswu_vesta.
Require Import Garden.GroupHash.group_hash_vesta.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module SswuVestaWitness.
  (** The final SSWU sign-selection operation, factored out only for proofs. *)
  Definition normalize_sign (target : bool) (y : Z) : Z :=
    if xorb target (SswuVesta.sgn0 y) then -F y else UnOp.from y.

  Lemma pallas_q_odd : Z.odd Primes.pallas_q = true.
  Proof. reflexivity. Qed.

  Lemma normalize_sign_congr (target : bool) (a b : Z) :
    UnOp.from a = UnOp.from b ->
    normalize_sign target a = normalize_sign target b.
  Proof.
    intros Hab.
    unfold normalize_sign, SswuVesta.sgn0.
    rewrite Hab.
    destruct (xorb target (Z.odd (UnOp.from b))); [|reflexivity].
    unfold UnOp.opp, UnOp.from in *.
    rewrite <- (Z.sub_0_l a), <- (Z.sub_0_l b).
    rewrite Zminus_mod, Hab, <- Zminus_mod.
    reflexivity.
  Qed.

  Lemma normalize_sign_opp (target : bool) (a : Z) :
    normalize_sign target (UnOp.opp a) = normalize_sign target a.
  Proof.
    unfold normalize_sign, SswuVesta.sgn0, UnOp.opp, UnOp.from.
    pose proof (prime_range (p := Primes.pallas_q)) as Hp.
    destruct (Z.eq_dec (a mod Primes.pallas_q) 0) as [Ha0 | Ha0].
    - assert (Hopp0 : (- a) mod Primes.pallas_q = 0).
      { apply Z.mod_opp_l_z; lia. }
      rewrite Hopp0, Z.mod_0_l by lia.
      rewrite Ha0.
      destruct target; reflexivity.
    - assert (Hoppnz : (- a) mod Primes.pallas_q =
                     Primes.pallas_q - a mod Primes.pallas_q).
      { apply Z.mod_opp_l_nz.
        - lia.
        - exact Ha0. }
      assert (Hodd : Z.odd (Primes.pallas_q - a mod Primes.pallas_q) =
                     negb (Z.odd (a mod Primes.pallas_q))).
      { rewrite Z.odd_sub, pallas_q_odd.
        destruct (Z.odd (a mod Primes.pallas_q)); reflexivity. }
      rewrite Z.mod_mod by lia.
      rewrite Hoppnz, Hodd.
      destruct target; destruct (Z.odd (a mod Primes.pallas_q));
        cbn [xorb negb].
      all: try reflexivity.
      all: rewrite <- Hoppnz; apply Z.mod_opp_mod_opp.
  Qed.

  Lemma square_eq_roots (a b : Z) :
    a *F a = b *F b ->
    UnOp.from a = UnOp.from b \/ UnOp.from a = UnOp.opp b.
  Proof.
    intros Hsq.
    pose proof (prime_range (p := Primes.pallas_q)) as Hp.
    assert (Hprod : (a -F b) *F (a +F b) = 0).
    { unfold BinOp.mul, BinOp.sub, BinOp.add in *.
      rewrite !Zmult_mod_idemp_l, !Zmult_mod_idemp_r.
      replace ((a - b) * (a + b)) with (a * a - b * b) by ring.
      rewrite Zminus_mod, Hsq, Z.sub_diag.
      rewrite Z.mod_0_l by lia.
      reflexivity. }
    rewrite mul_zero_implies_zero in Hprod.
    destruct Hprod as [Hsub | Hadd].
    - left. rewrite from_sub_reduced in Hsub.
      now apply sub_zero_equiv in Hsub.
    - right.
      replace (a +F b) with (a -F (- b)) in Hadd.
      2: { unfold BinOp.add, BinOp.sub. f_equal. ring. }
      rewrite from_sub_reduced in Hadd.
      apply sub_zero_equiv in Hadd.
      exact Hadd.
  Qed.

  Lemma normalize_sign_square_eq (target : bool) (a b : Z) :
    a *F a = b *F b ->
    normalize_sign target a = normalize_sign target b.
  Proof.
    intros Hsq.
    destruct (square_eq_roots a b Hsq) as [Hab | Hab].
    - exact (normalize_sign_congr target a b Hab).
    - transitivity (normalize_sign target (UnOp.opp b)).
      + apply normalize_sign_congr. rewrite Hab.
        unfold UnOp.opp, UnOp.from.
        rewrite Z.mod_mod by (pose proof
          (prime_range (p := Primes.pallas_q)); lia).
        reflexivity.
      + apply normalize_sign_opp.
  Qed.

  Lemma pallas_q_gt_2 : 2 < Primes.pallas_q.
  Proof. unfold Primes.pallas_q, Primes.t_q; lia. Qed.

  Lemma from_div_reduced (a b : Z) :
    UnOp.from (BinOp.div a b) = BinOp.div a b.
  Proof. unfold BinOp.div. apply from_mul_reduced. Qed.

  Lemma ratio_nonzero (num div : Z) :
    UnOp.from num <> 0 ->
    UnOp.from div <> 0 ->
    UnOp.from (BinOp.div num div) <> 0.
  Proof.
    intros Hnum Hdiv Hr.
    assert (Hr0 : BinOp.div num div = 0).
    { rewrite <- from_div_reduced. exact Hr. }
    pose proof (div_mul (p := Primes.pallas_q) num div pallas_q_gt_2 Hdiv)
      as Hmul.
    rewrite Hr0 in Hmul.
    unfold BinOp.mul in Hmul. rewrite Z.mul_0_l in Hmul.
    rewrite Z.mod_0_l in Hmul by
      (pose proof (prime_range (p := Primes.pallas_q)); lia).
    exact (Hnum (eq_sym Hmul)).
  Qed.

  Lemma square_equation_to_ratio (num div root : Z) :
    UnOp.from div <> 0 ->
    root *F root *F div = UnOp.from num ->
    root *F root = BinOp.div num div.
  Proof.
    intros Hdiv Heq.
    pose proof
      (field_mul_cancel_r
         (p := Primes.pallas_q)
         (root *F root) (BinOp.div num div) div Hdiv)
      as Hcancel.
    assert (Hright : BinOp.div num div *F div = UnOp.from num).
    { apply div_mul; [exact pallas_q_gt_2 | exact Hdiv]. }
    specialize (Hcancel (eq_trans Heq (eq_sym Hright))).
    rewrite from_mul_reduced, from_div_reduced in Hcancel.
    exact Hcancel.
  Qed.

  Lemma scaled_square_equation_to_ratio
      (scale num div root : Z) :
    UnOp.from div <> 0 ->
    root *F root *F div = scale *F num ->
    root *F root = scale *F BinOp.div num div.
  Proof.
    intros Hdiv Heq.
    assert (Hright :
      (scale *F BinOp.div num div) *F div = scale *F num).
    { rewrite field_mul_assoc.
      rewrite (div_mul (p := Primes.pallas_q) num div
                 pallas_q_gt_2 Hdiv).
      unfold BinOp.mul, UnOp.from.
      rewrite Zmult_mod_idemp_r.
      reflexivity. }
    pose proof
      (field_mul_cancel_r
         (p := Primes.pallas_q)
         (root *F root) (scale *F BinOp.div num div) div Hdiv)
      as Hcancel.
    specialize (Hcancel (eq_trans Heq (eq_sym Hright))).
    rewrite !from_mul_reduced in Hcancel.
    exact Hcancel.
  Qed.

  Lemma mul_square_congr (k a b : Z) :
    a *F a = b *F b ->
    (k *F a) *F (k *F a) = (k *F b) *F (k *F b).
  Proof.
    intros Hab.
    rewrite (field_mul_swap_inner k a k a).
    rewrite (field_mul_swap_inner k b k b).
    now rewrite Hab.
  Qed.

  (** A checked witness chooses the same branch as [sqrt_ratio], and its
      root differs from the canonical Tonelli--Shanks root by at most sign. *)
  Lemma sqrt_ratio_witness_roots
      (num div : Z) (was_square : bool) (root : Z) :
    UnOp.from num <> 0 ->
    UnOp.from div <> 0 ->
    SswuVesta.sqrt_ratio_witness_ok num div was_square root = true ->
    match SswuVesta.sqrt_ratio num div with
    | (canonical_square, canonical_root) =>
        was_square = canonical_square /\
        root *F root = canonical_root *F canonical_root
    end.
  Proof.
    intros Hnum Hdiv Hwit.
    unfold SswuVesta.sqrt_ratio.
    set (r := BinOp.div num div).
    assert (Hrred : UnOp.from r = r).
    { unfold r. apply from_div_reduced. }
    assert (Hrnon : UnOp.from r <> 0).
    { unfold r. now apply ratio_nonzero. }
    destruct (is_square (p := Primes.pallas_q) r) eqn:Hsquare;
      destruct was_square eqn:Hwas.
    - split; [reflexivity |].
      unfold SswuVesta.sqrt_ratio_witness_ok in Hwit.
      apply Z.eqb_eq in Hwit.
      pose proof (square_equation_to_ratio num div root Hdiv Hwit) as Hroot.
      fold r in Hroot.
      pose proof (field_sqrt_sound (p := Primes.pallas_q) r Hsquare) as Hcan.
      rewrite Hrred in Hcan.
      exact (eq_trans Hroot (eq_sym Hcan)).
    - exfalso.
      unfold SswuVesta.sqrt_ratio_witness_ok in Hwit.
      apply Z.eqb_eq in Hwit.
      pose proof
        (scaled_square_equation_to_ratio
           IsoVesta.lambda num div root Hdiv Hwit) as Hroot.
      fold r in Hroot.
      pose proof
        (is_square_mul_nonres_l
           (p := Primes.pallas_q) IsoVesta.lambda r
           pallas_q_gt_2 IsoVesta.lambda_nonsquare Hsquare Hrnon) as Hnon.
      pose proof (is_square_sq (p := Primes.pallas_q) root) as Hroot_square.
      rewrite Hroot in Hroot_square.
      rewrite Hnon in Hroot_square. discriminate.
    - exfalso.
      unfold SswuVesta.sqrt_ratio_witness_ok in Hwit.
      apply Z.eqb_eq in Hwit.
      pose proof (square_equation_to_ratio num div root Hdiv Hwit) as Hroot.
      fold r in Hroot.
      pose proof (is_square_sq (p := Primes.pallas_q) root) as Hroot_square.
      rewrite Hroot, Hsquare in Hroot_square. discriminate.
    - split; [reflexivity |].
      unfold SswuVesta.sqrt_ratio_witness_ok in Hwit.
      apply Z.eqb_eq in Hwit.
      pose proof
        (scaled_square_equation_to_ratio
           IsoVesta.lambda num div root Hdiv Hwit) as Hroot.
      fold r in Hroot.
      pose proof (is_square_sq (p := Primes.pallas_q) root) as Hscaled_square.
      rewrite Hroot in Hscaled_square.
      pose proof
        (field_sqrt_sound
           (p := Primes.pallas_q) (IsoVesta.lambda *F r) Hscaled_square)
        as Hcan.
      rewrite from_mul_reduced in Hcan.
      exact (eq_trans Hroot (eq_sym Hcan)).
  Qed.

  Definition swu_nonexceptional (u : Z) : Prop :=
    UnOp.from (SswuVesta.gx1_num u) <> 0 /\
    UnOp.from (SswuVesta.x_div3 u) <> 0.

  Definition field_nonzerob (value : Z) : bool :=
    negb (UnOp.from value =? 0).

  Definition swu_nonexceptionalb (u : Z) : bool :=
    field_nonzerob (SswuVesta.gx1_num u)
      && field_nonzerob (SswuVesta.x_div3 u).

  Lemma field_nonzerob_sound (value : Z) :
    field_nonzerob value = true -> UnOp.from value <> 0.
  Proof.
    unfold field_nonzerob. intros Hvalue.
    apply negb_true_iff in Hvalue.
    now apply Z.eqb_neq in Hvalue.
  Qed.

  Lemma swu_nonexceptionalb_sound (u : Z) :
    swu_nonexceptionalb u = true -> swu_nonexceptional u.
  Proof.
    unfold swu_nonexceptionalb, swu_nonexceptional.
    intros Hcheck. apply andb_prop in Hcheck as [Hnum Hdiv].
    split; now apply field_nonzerob_sound.
  Qed.

  (** The inexpensive witnessed map is extensionally the canonical SSWU map.
      The two nonzero hypotheses are exactly what makes the branch flag unique:
      division must be defined, and [gx1_num] must not be the common zero for
      both the residue and non-residue witness equations. *)
  Theorem map_to_curve_simple_swu_with_root_eq
      (u : Z) (was_square : bool) (root : Z) :
    swu_nonexceptional u ->
    SswuVesta.swu_witness_ok u was_square root = true ->
    SswuVesta.map_to_curve_simple_swu_with_root u was_square root =
    SswuVesta.map_to_curve_simple_swu u.
  Proof.
    intros [Hnum Hdiv] Hwit.
    unfold SswuVesta.swu_witness_ok in Hwit.
    pose proof
      (sqrt_ratio_witness_roots
        (SswuVesta.gx1_num u) (SswuVesta.x_div3 u)
        was_square root Hnum Hdiv Hwit) as Hroots.
    unfold SswuVesta.map_to_curve_simple_swu.
    destruct (SswuVesta.sqrt_ratio
      (SswuVesta.gx1_num u) (SswuVesta.x_div3 u))
      as [canonical_square canonical_root] eqn:Hratio.
    destruct Hroots as [Hflag Hsquare]. subst was_square.
    destruct canonical_square.
    - change (
        Weierstrass.Affine
          (BinOp.div (SswuVesta.x1_num u) (SswuVesta.x_div u))
          (normalize_sign (SswuVesta.sgn0 u) root) =
        Weierstrass.Affine
          (BinOp.div (SswuVesta.x1_num u) (SswuVesta.x_div u))
          (normalize_sign (SswuVesta.sgn0 u) canonical_root)).
      rewrite (normalize_sign_square_eq
        (SswuVesta.sgn0 u) root canonical_root Hsquare).
      reflexivity.
    - set (k := IsoVesta.theta *F SswuVesta.z_u2 u *F u).
      change (
        Weierstrass.Affine
          (BinOp.div (SswuVesta.x2_num u) (SswuVesta.x_div u))
          (normalize_sign (SswuVesta.sgn0 u) (k *F root)) =
        Weierstrass.Affine
          (BinOp.div (SswuVesta.x2_num u) (SswuVesta.x_div u))
          (normalize_sign (SswuVesta.sgn0 u) (k *F canonical_root))).
      rewrite (normalize_sign_square_eq
        (SswuVesta.sgn0 u) (k *F root) (k *F canonical_root)
        (mul_square_congr k root canonical_root Hsquare)).
      reflexivity.
  Qed.

  Definition hash_inputs_nonexceptional
      (domain_prefix msg : list Z) : Prop :=
    let '(u0, u1) := GroupHashVesta.hash_to_field_vesta domain_prefix msg in
    swu_nonexceptional u0 /\ swu_nonexceptional u1.

  (** One-pass boolean checker used by bulk SRS certificates.  The hash-to-
      field pair is shared by the witness equations and the nonzero tests. *)
  Definition canonical_witnesses_ok_for
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    (swu_nonexceptionalb u0
       && SswuVesta.swu_witness_ok u0 was_square0 root0)
      && (swu_nonexceptionalb u1
       && SswuVesta.swu_witness_ok u1 was_square1 root1).

  Definition group_hash_from_field_with_witness
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : Vesta.point :=
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu_with_root
          u0 was_square0 root0)
        (SswuVesta.map_to_curve_simple_swu_with_root
          u1 was_square1 root1)).

  Definition group_hash_from_field (u0 u1 : Z) : Vesta.point :=
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu u0)
        (SswuVesta.map_to_curve_simple_swu u1)).

  Lemma canonical_witnesses_ok_for_parts
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1 = true ->
    (swu_nonexceptional u0 /\
       SswuVesta.swu_witness_ok u0 was_square0 root0 = true) /\
    (swu_nonexceptional u1 /\
       SswuVesta.swu_witness_ok u1 was_square1 root1 = true).
  Proof.
    unfold canonical_witnesses_ok_for.
    intros Hcheck. apply andb_prop in Hcheck as [Hcheck0 Hcheck1].
    apply andb_prop in Hcheck0 as [Hnon0 Hwit0].
    apply andb_prop in Hcheck1 as [Hnon1 Hwit1].
    split; split; try assumption; now apply swu_nonexceptionalb_sound.
  Qed.

  Theorem canonical_witnesses_ok_for_group_hash
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1 = true ->
    group_hash_from_field_with_witness
      u0 u1 was_square0 root0 was_square1 root1 =
    group_hash_from_field u0 u1.
  Proof.
    intros Hcheck.
    destruct (canonical_witnesses_ok_for_parts
      u0 u1 was_square0 root0 was_square1 root1 Hcheck)
      as [[Hnon0 Hwit0] [Hnon1 Hwit1]].
    unfold group_hash_from_field_with_witness, group_hash_from_field.
    rewrite (map_to_curve_simple_swu_with_root_eq
      u0 was_square0 root0 Hnon0 Hwit0).
    rewrite (map_to_curve_simple_swu_with_root_eq
      u1 was_square1 root1 Hnon1 Hwit1).
    reflexivity.
  Qed.

  Corollary canonical_witnesses_ok_for_sound
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (expected : Vesta.point) :
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1 = true ->
    group_hash_from_field_with_witness
      u0 u1 was_square0 root0 was_square1 root1 = expected ->
    group_hash_from_field u0 u1 = expected.
  Proof.
    intros Hcheck Hpoint.
    pose proof (canonical_witnesses_ok_for_group_hash
      u0 u1 was_square0 root0 was_square1 root1 Hcheck) as Hcanonical.
    exact (eq_trans (eq_sym Hcanonical) Hpoint).
  Qed.

  Corollary canonical_witnesses_ok_for_sound_eqb
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (expected : Vesta.point) :
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1 = true ->
    GroupHashVesta.point_eqb
      (group_hash_from_field_with_witness
        u0 u1 was_square0 root0 was_square1 root1)
      expected = true ->
    group_hash_from_field u0 u1 = expected.
  Proof.
    intros Hcheck Hpoint.
    apply (canonical_witnesses_ok_for_sound
      u0 u1 was_square0 root0 was_square1 root1 expected Hcheck).
    now apply GroupHashVesta.point_eqb_eq.
  Qed.

  Definition canonical_point_eqb
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (expected : Vesta.point) : bool :=
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1
      && GroupHashVesta.point_eqb
        (group_hash_from_field_with_witness
          u0 u1 was_square0 root0 was_square1 root1)
        expected.

  Lemma canonical_point_eqb_witnesses_ok
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (expected : Vesta.point) :
    canonical_point_eqb
      u0 u1 was_square0 root0 was_square1 root1 expected = true ->
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1 = true.
  Proof.
    unfold canonical_point_eqb. intros Hcheck.
    now apply andb_prop in Hcheck as [Hok _].
  Qed.

  Theorem canonical_point_eqb_sound
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (expected : Vesta.point) :
    canonical_point_eqb
      u0 u1 was_square0 root0 was_square1 root1 expected = true ->
    group_hash_from_field u0 u1 = expected.
  Proof.
    unfold canonical_point_eqb. intros Hcheck.
    apply andb_prop in Hcheck as [Hok Hpoint].
    exact (canonical_witnesses_ok_for_sound_eqb
      u0 u1 was_square0 root0 was_square1 root1 expected Hok Hpoint).
  Qed.

  Definition canonical_witnesses_ok
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    let '(u0, u1) := GroupHashVesta.hash_to_field_vesta domain_prefix msg in
    canonical_witnesses_ok_for
      u0 u1 was_square0 root0 was_square1 root1.

  Lemma canonical_witnesses_ok_parts
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true ->
    hash_inputs_nonexceptional domain_prefix msg /\
    GroupHashVesta.witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true.
  Proof.
    unfold canonical_witnesses_ok, canonical_witnesses_ok_for,
      hash_inputs_nonexceptional,
      GroupHashVesta.witnesses_ok.
    destruct (GroupHashVesta.hash_to_field_vesta domain_prefix msg)
      as [u0 u1].
    intros Hcheck.
    apply andb_prop in Hcheck as [Hcheck0 Hcheck1].
    apply andb_prop in Hcheck0 as [Hnon0 Hwit0].
    apply andb_prop in Hcheck1 as [Hnon1 Hwit1].
    split.
    - split; now apply swu_nonexceptionalb_sound.
    - exact (andb_true_intro (conj Hwit0 Hwit1)).
  Qed.

  Lemma canonical_witnesses_ok_nonexceptional
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true ->
    hash_inputs_nonexceptional domain_prefix msg.
  Proof.
    intros Hcheck.
    exact (proj1 (canonical_witnesses_ok_parts
      domain_prefix msg was_square0 root0 was_square1 root1 Hcheck)).
  Qed.

  Lemma canonical_witnesses_ok_witnesses
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true ->
    GroupHashVesta.witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true.
  Proof.
    intros Hcheck.
    exact (proj2 (canonical_witnesses_ok_parts
      domain_prefix msg was_square0 root0 was_square1 root1 Hcheck)).
  Qed.

  (** Two checked SSWU witnesses therefore give exactly the canonical Vesta
      group hash.  Hashing, addition, and the isogeny remain the original
      definitions; only the square-root computation has been replaced. *)
  Theorem group_hash_with_witness_eq
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    hash_inputs_nonexceptional domain_prefix msg ->
    GroupHashVesta.witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true ->
    GroupHashVesta.group_hash_with_witness
      domain_prefix msg was_square0 root0 was_square1 root1 =
    GroupHashVesta.group_hash domain_prefix msg.
  Proof.
    intros Hnon Hwit.
    remember (GroupHashVesta.hash_to_field_vesta domain_prefix msg)
      as inputs eqn:Hinputs.
    destruct inputs as [u0 u1].
    unfold hash_inputs_nonexceptional in Hnon.
    unfold GroupHashVesta.witnesses_ok in Hwit.
    unfold GroupHashVesta.group_hash_with_witness,
      GroupHashVesta.group_hash.
    rewrite <- Hinputs in Hnon, Hwit |- *.
    destruct Hnon as [Hnon0 Hnon1].
    apply andb_true_iff in Hwit. destruct Hwit as [Hwit0 Hwit1].
    rewrite (map_to_curve_simple_swu_with_root_eq
      u0 was_square0 root0 Hnon0 Hwit0).
    rewrite (map_to_curve_simple_swu_with_root_eq
      u1 was_square1 root1 Hnon1 Hwit1).
    reflexivity.
  Qed.

  Theorem canonical_witnesses_ok_group_hash
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) :
    canonical_witnesses_ok
      domain_prefix msg was_square0 root0 was_square1 root1 = true ->
    GroupHashVesta.group_hash_with_witness
      domain_prefix msg was_square0 root0 was_square1 root1 =
    GroupHashVesta.group_hash domain_prefix msg.
  Proof.
    intros Hcheck.
    apply group_hash_with_witness_eq.
    - now apply (canonical_witnesses_ok_nonexceptional
        domain_prefix msg was_square0 root0 was_square1 root1).
    - now apply (canonical_witnesses_ok_witnesses
        domain_prefix msg was_square0 root0 was_square1 root1).
  Qed.

End SswuVestaWitness.
