(** * Annihilation by a prime generator order under the tight coset bound

    Extension of the generic order theorem [GroupOrder.mul_q_annihilates] to
    curves on the positive-trace side of a curve cycle, where the group
    order [q] is *smaller* than the base prime [p] and the two-coset bound
    [2*p + 1 < 2*q] fails.  Under the weaker bound [2*p + 1 < 3*q] the same
    counting argument runs with *three* cosets [<G>], [P + <G>],
    [2P + <G>], provided the curve carries no point of order two — supplied
    as the computable no-root hypothesis on [x^3 + a*x + b].  A point [P]
    escaping the subgroup [<G>] either yields three pairwise-disjoint
    cosets ([3*q] distinct reduced on-curve points, against the [2*p + 1]
    cap of [GroupOrderCounting.family_bound]), or doubles into [<G>], and
    then [mul q P] is a nonzero point annihilated by two — a point of order
    two, contradicting the no-root hypothesis.

    The file also proves the point-algebra lemmas the MSM checker layer
    consumes: distribution of scalar multiplication over point addition
    ([mul_point_add], by direct induction over the double-and-add ladder —
    no fiat-crypto transport), and reduction of scalars modulo an
    annihilating order ([mul_mod_order]).

    Everything is symbolic in [p] and [q]: nothing of scalar size is ever
    computed. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.GroupOrder.
Require Import Garden.EllipticCurve.GroupOrderCosets.
Require Import Garden.EllipticCurve.GroupOrderCounting.

Global Open Scope Z_scope.

Module GroupOrderTight.
Section Tight.
  (** The abstract base field [Z/pZ], as in [Weierstrass.Curve]. *)
  Context {p : Z} `{Prime p}.

  (** The short-Weierstrass coefficients [y^2 = x^3 + a*x + b]. *)
  Variables (a b : Z).

  (** The characteristic bound and nonsingularity required by the
      fiat-crypto transported group law. *)
  Hypothesis H11 : 11 < p.
  Hypothesis Hns : Weierstrass.nonsingular (p := p) a b.

  Local Notation point := Weierstrass.point.
  Local Notation Infinity := Weierstrass.Infinity.
  Local Notation Affine := Weierstrass.Affine.
  Local Notation on_curve := (Weierstrass.on_curve (p := p) a b).
  Local Notation reduced := (Weierstrass.reduced (p := p)).
  Local Notation add := (Weierstrass.add (p := p) a).
  Local Notation mul := (Weierstrass.mul (p := p) a).
  Local Notation mul_pos := (Weierstrass.mul_pos (p := p) a).

  Lemma three_lt_p : 3 < p.
  Proof. lia. Qed.

  (** ** Point algebra: the four-summand shuffle

      [(A + B) + (C + D) = (A + C) + (B + D)] on reduced on-curve points,
      by associativity and commutativity. *)
  Lemma add_swap4 (A B C D : point) :
    reduced A -> reduced B -> reduced C -> reduced D ->
    on_curve A -> on_curve B -> on_curve C -> on_curve D ->
    add (add A B) (add C D) = add (add A C) (add B D).
  Proof.
    intros HrA HrB HrC HrD HoA HoB HoC HoD.
    rewrite (Weierstrass.add_assoc a b A B (add C D) H11 Hns); try assumption;
      try (apply Weierstrass.add_reduced; assumption);
      try (apply Weierstrass.add_on_curve;
           [exact three_lt_p | assumption | assumption]).
    rewrite <- (Weierstrass.add_assoc a b B C D H11 Hns); try assumption.
    rewrite (Weierstrass.add_comm a b B C); try assumption.
    rewrite (Weierstrass.add_assoc a b C B D H11 Hns); try assumption.
    rewrite <- (Weierstrass.add_assoc a b A C (add B D) H11 Hns);
      try assumption;
      try (apply Weierstrass.add_reduced; assumption);
      try (apply Weierstrass.add_on_curve;
           [exact three_lt_p | assumption | assumption]).
    reflexivity.
  Qed.

  (** ** Distribution of the ladder over point addition *)
  Lemma mul_pos_point_add (n : positive) (X Y : point) :
    reduced X -> reduced Y -> on_curve X -> on_curve Y ->
    mul_pos n (add X Y) = add (mul_pos n X) (mul_pos n Y).
  Proof.
    intros HrX HrY HoX HoY.
    assert (HrQX : forall m : positive, reduced (mul_pos m X))
      by (intro m; apply Weierstrass.mul_pos_reduced; exact HrX).
    assert (HrQY : forall m : positive, reduced (mul_pos m Y))
      by (intro m; apply Weierstrass.mul_pos_reduced; exact HrY).
    assert (HoQX : forall m : positive, on_curve (mul_pos m X))
      by (intro m; apply (GroupOrderCosets.mul_pos_on_curve a b H11);
          exact HoX).
    assert (HoQY : forall m : positive, on_curve (mul_pos m Y))
      by (intro m; apply (GroupOrderCosets.mul_pos_on_curve a b H11);
          exact HoY).
    induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos].
    - (* xI: P + (Q + Q) with P := X + Y *)
      rewrite IH.
      rewrite (add_swap4 (mul_pos n X) (mul_pos n Y)
                 (mul_pos n X) (mul_pos n Y)); try auto.
      apply (add_swap4 X Y (add (mul_pos n X) (mul_pos n X))
               (add (mul_pos n Y) (mul_pos n Y))); try assumption;
        try (apply Weierstrass.add_reduced; auto);
        try (apply Weierstrass.add_on_curve;
             [exact three_lt_p | auto | auto]).
    - (* xO: Q + Q *)
      rewrite IH.
      apply (add_swap4 (mul_pos n X) (mul_pos n Y)
               (mul_pos n X) (mul_pos n Y)); auto.
    - reflexivity.
  Qed.

  (** [mul k (X + Y) = mul k X + mul k Y] for nonnegative [k]. *)
  Lemma mul_point_add (k : Z) (X Y : point) :
    0 <= k ->
    reduced X -> reduced Y -> on_curve X -> on_curve Y ->
    mul k (add X Y) = add (mul k X) (mul k Y).
  Proof.
    intros Hk HrX HrY HoX HoY.
    destruct k as [| n | n]; [reflexivity | | lia].
    cbn [Weierstrass.mul].
    apply mul_pos_point_add; assumption.
  Qed.

  (** [mul] fixes the identity. *)
  Lemma mul_Infinity_r (k : Z) : mul k Infinity = Infinity.
  Proof.
    assert (Hpos : forall n : positive, mul_pos n Infinity = Infinity).
    { intro n. induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos];
        rewrite ?IH; reflexivity. }
    destruct k as [| n | n]; cbn [Weierstrass.mul]; rewrite ?Hpos;
      reflexivity.
  Qed.

  (** ** Scalar reduction modulo an annihilating order *)
  Lemma mul_mod_order (Q : point) (r n : Z) :
    r <> 0 ->
    reduced Q -> on_curve Q ->
    mul r Q = Infinity ->
    mul (n mod r) Q = mul n Q.
  Proof.
    intros Hr HrQ HoQ Hann.
    rewrite (Z.div_mod n r Hr) at 2.
    rewrite (Weierstrass.mul_add a b (r * (n / r)) (n mod r) Q H11 Hns HrQ HoQ).
    replace (r * (n / r)) with ((n / r) * r) by lia.
    rewrite (Weierstrass.mul_mul a b (n / r) r Q H11 Hns HrQ HoQ).
    rewrite Hann, mul_Infinity_r.
    rewrite (Weierstrass.add_Infinity_l a b).
    reflexivity.
  Qed.

  (** ** No point of order two

      The computable hypothesis: [x^3 + a*x + b] has no root in the field.
      A same-[x] doubling reaching the identity forces [2*y = 0], hence
      [y = 0] ([p] is odd), hence a root — so doubling a proper point never
      reaches the identity. *)
  Hypothesis Hnoy :
    forall x : Z, UnOp.from (x *F x *F x +F a *F x +F b) <> 0.

  Lemma double_ne_infinity (T : point) :
    reduced T -> on_curve T -> T <> Infinity ->
    add T T <> Infinity.
  Proof.
    intros HrT HoT Hne.
    destruct T as [| x y]; [exact (fun _ => Hne eq_refl) |].
    cbn [Weierstrass.add].
    assert (Hx : (x -F x) = 0).
    { unfold BinOp.sub. rewrite Z.sub_diag. apply Zmod_0_l. }
    rewrite Hx. cbn [Z.eqb].
    destruct ((y +F y) =? 0) eqn:Hy; [| discriminate].
    exfalso.
    apply Z.eqb_eq in Hy.
    destruct HrT as [Hxr Hyr].
    pose proof (GroupOrderCounting.reduced_coord_range (p := p) y Hyr) as Hyb.
    assert (Hodd : p mod 2 = 1)
      by (apply GroupOrderCounting.p_odd; lia).
    assert (Hdiv : (y + y) mod p = 0).
    { unfold BinOp.add in Hy. exact Hy. }
    assert (Hy0 : y = 0).
    { assert (Hcases : y + y = 0 \/ y + y = p).
      { pose proof (Z.div_mod (y + y) p ltac:(lia)) as Hdm.
        rewrite Hdiv in Hdm.
        assert (Hq2 : 0 <= (y + y) / p < 2)
          by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        assert (Hqc : (y + y) / p = 0 \/ (y + y) / p = 1) by lia.
        destruct Hqc as [Hq0 | Hq1]; [left | right]; lia. }
      destruct Hcases as [Hc | Hc]; [lia |].
      exfalso. clear - Hodd Hc.
      pose proof (Z.div_mod p 2 ltac:(lia)) as Hdm2. lia. }
    subst y.
    cbn [Weierstrass.on_curve] in HoT.
    assert (Hzero : UnOp.from (0 *F 0) = 0).
    { unfold BinOp.mul, UnOp.from. rewrite Z.mul_0_l, !Zmod_0_l.
      reflexivity. }
    rewrite Hzero in HoT.
    exact (Hnoy x (eq_sym HoT)).
  Qed.

  (** ** The three-coset family

      The prime-order generator: reduced, on the curve, not the identity,
      with order certificate [mul q G = Infinity] for a prime [q]. *)
  Variables (G : point) (q : Z).
  Hypothesis HrG : reduced G.
  Hypothesis HoG : on_curve G.
  Hypothesis HGne : G <> Infinity.
  Hypothesis Hq : IsPrime q.
  Hypothesis Hord : mul q G = Infinity.

  Section WithP.
    (** A reduced on-curve point with both itself and its double outside
        the cyclic subgroup [<G>]. *)
    Variable P : point.
    Hypothesis HrP : reduced P.
    Hypothesis HoP : on_curve P.
    Hypothesis Hnm : forall n : Z, P <> mul n G.
    Hypothesis Hnm2 : forall n : Z, add P P <> mul n G.

    (** Indices [0 <= k < q] enumerate the subgroup [<G>]; indices
        [q <= k < 2q] the coset [P + <G>]; indices [2q <= k < 3q] the coset
        [2P + <G>]. *)
    Definition family3 (k : Z) : point :=
      if k <? q then mul k G
      else if k <? 2 * q then add P (mul (k - q) G)
      else add (add P P) (mul (k - 2 * q) G).

    Lemma addPP_reduced : reduced (add P P).
    Proof. apply Weierstrass.add_reduced; exact HrP. Qed.

    Lemma addPP_on_curve : on_curve (add P P).
    Proof.
      apply Weierstrass.add_on_curve; [exact three_lt_p | exact HoP | exact HoP].
    Qed.

    Lemma family3_reduced_on_curve (k : Z) :
      0 <= k < 3 * q ->
      reduced (family3 k) /\ on_curve (family3 k).
    Proof.
      intros _. unfold family3.
      destruct (k <? q); [| destruct (k <? 2 * q)].
      - split.
        + apply Weierstrass.mul_reduced. exact HrG.
        + apply (GroupOrderCosets.mul_on_curve a b H11). exact HoG.
      - split.
        + apply Weierstrass.add_reduced;
            [exact HrP | apply Weierstrass.mul_reduced; exact HrG].
        + apply Weierstrass.add_on_curve;
            [exact three_lt_p | exact HoP
             | apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG].
      - split.
        + apply Weierstrass.add_reduced;
            [exact addPP_reduced | apply Weierstrass.mul_reduced; exact HrG].
        + apply Weierstrass.add_on_curve;
            [exact three_lt_p | exact addPP_on_curve
             | apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG].
    Qed.

    (** Cross-coset disjointness of [P + <G>] and [2P + <G>]: a collision
        would cancel one [P] ([add_assoc] + [add_P_cancel]) and land in the
        [<G>]-vs-[P + <G>] case. *)
    Lemma cross_BC (i j : Z) :
      add P (mul i G) <> add (add P P) (mul j G).
    Proof.
      intros Heq.
      assert (HrmI : reduced (mul i G))
        by (apply Weierstrass.mul_reduced; exact HrG).
      assert (HomI : on_curve (mul i G))
        by (apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG).
      assert (HrmJ : reduced (mul j G))
        by (apply Weierstrass.mul_reduced; exact HrG).
      assert (HomJ : on_curve (mul j G))
        by (apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG).
      rewrite (Weierstrass.add_assoc a b P P (mul j G) H11 Hns HrP HrP HrmJ
                 HoP HoP HomJ) in Heq.
      assert (Hcancel : mul i G = add P (mul j G)).
      { apply (GroupOrderCosets.add_P_cancel a b H11 Hns P HoP
                 (mul i G) (add P (mul j G))); try assumption.
        - apply Weierstrass.add_reduced; assumption.
        - apply Weierstrass.add_on_curve;
            [exact three_lt_p | assumption | assumption]. }
      exact (GroupOrderCosets.coset_disjoint a b H11 Hns G HrG HoG P HrP
               HoP Hnm i j Hcancel).
    Qed.

    (** Injectivity of the three-coset family on [0, 3q). *)
    Lemma family3_inj (i j : Z) :
      0 <= i < 3 * q -> 0 <= j < 3 * q -> family3 i = family3 j -> i = j.
    Proof.
      intros Hi Hj. unfold family3.
      pose proof (GroupOrderCosets.mul_G_inj a b H11 Hns G q HrG HoG HGne Hq
                    Hord) as Hinj.
      destruct (Z.ltb_spec i q) as [Hiq | Hiq];
        destruct (Z.ltb_spec j q) as [Hjq | Hjq].
      - (* A-A *)
        intros Heq. apply Hinj; [lia | lia | exact Heq].
      - destruct (Z.ltb_spec j (2 * q)) as [Hj2 | Hj2]; intros Heq.
        + (* A-B *)
          exfalso.
          exact (GroupOrderCosets.coset_disjoint a b H11 Hns G HrG HoG P
                   HrP HoP Hnm i (j - q) Heq).
        + (* A-C *)
          exfalso.
          exact (GroupOrderCosets.coset_disjoint a b H11 Hns G HrG HoG
                   (add P P) addPP_reduced addPP_on_curve Hnm2
                   i (j - 2 * q) Heq).
      - destruct (Z.ltb_spec i (2 * q)) as [Hi2 | Hi2]; intros Heq.
        + (* B-A *)
          exfalso.
          exact (GroupOrderCosets.coset_disjoint a b H11 Hns G HrG HoG P
                   HrP HoP Hnm j (i - q) (eq_sym Heq)).
        + (* C-A *)
          exfalso.
          exact (GroupOrderCosets.coset_disjoint a b H11 Hns G HrG HoG
                   (add P P) addPP_reduced addPP_on_curve Hnm2
                   j (i - 2 * q) (eq_sym Heq)).
      - destruct (Z.ltb_spec i (2 * q)) as [Hi2 | Hi2];
          destruct (Z.ltb_spec j (2 * q)) as [Hj2 | Hj2]; intros Heq.
        + (* B-B *)
          assert (Hm : mul (i - q) G = mul (j - q) G).
          { apply (GroupOrderCosets.add_P_cancel a b H11 Hns P HoP);
              try (apply Weierstrass.mul_reduced; exact HrG);
              try (apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG).
            exact Heq. }
          assert (Hij : i - q = j - q) by (apply Hinj; [lia | lia | exact Hm]).
          lia.
        + (* B-C *)
          exfalso. exact (cross_BC (i - q) (j - 2 * q) Heq).
        + (* C-B *)
          exfalso. exact (cross_BC (j - q) (i - 2 * q) (eq_sym Heq)).
        + (* C-C *)
          assert (Hm : mul (i - 2 * q) G = mul (j - 2 * q) G).
          { apply (GroupOrderCosets.add_P_cancel a b H11 Hns (add P P)
                     addPP_on_curve);
              try (apply Weierstrass.mul_reduced; exact HrG);
              try (apply (GroupOrderCosets.mul_on_curve a b H11); exact HoG).
            exact Heq. }
          assert (Hij : i - 2 * q = j - 2 * q)
            by (apply Hinj; [lia | lia | exact Hm]).
          lia.
    Qed.

  End WithP.

  (** The tight smallness bound: the [2*p + 1] cap on reduced on-curve
      points is below the [3*q] members of a three-coset family. *)
  Hypothesis Hcard3 : 2 * p + 1 < 3 * q.

  (** ** The order theorem under the tight bound *)
  Theorem mul_q_annihilates_tight (P : point) :
    reduced P -> on_curve P -> mul q P = Infinity.
  Proof.
    intros HrP HoP.
    assert (H3 : 3 < p) by lia.
    destruct (GroupOrder.point_eq_dec (mul q P) Infinity) as [He | Hne];
      [exact He |].
    exfalso.
    (** [P] is outside [<G>]: a multiple would be annihilated by [q]. *)
    assert (Hnm : forall n : Z, P <> mul n G).
    { intros n HP. apply Hne. rewrite HP.
      rewrite <- (Weierstrass.mul_mul a b q n G H11 Hns HrG HoG).
      apply (proj2 (Weierstrass.mul_eq_Infinity_iff a b G q H11 Hns HrG HoG
                      HGne Hq Hord (q * n))).
      apply Z.divide_factor_l. }
    destruct (GroupOrder.point_eq_dec (mul (2 * q) P) Infinity)
      as [He2 | Hne2].
    - (* [2q]P = 0: the point [q]P is proper and doubles to the identity. *)
      assert (Hdbl : add (mul q P) (mul q P) = Infinity).
      { change (add (mul q P) (mul q P)) with (mul 2 (mul q P)).
        rewrite <- (Weierstrass.mul_mul a b 2 q P H11 Hns HrP HoP).
        exact He2. }
      refine (double_ne_infinity (mul q P) _ _ Hne Hdbl).
      + apply Weierstrass.mul_reduced. exact HrP.
      + apply (GroupOrderCosets.mul_on_curve a b H11). exact HoP.
    - (* [2q]P <> 0: the double also escapes <G>, three disjoint cosets. *)
      assert (Hnm2 : forall n : Z, add P P <> mul n G).
      { intros n HP2. apply Hne2.
        assert (Hpp : mul 2 P = add P P) by reflexivity.
        replace (2 * q) with (q * 2) by lia.
        rewrite (Weierstrass.mul_mul a b q 2 P H11 Hns HrP HoP).
        rewrite Hpp, HP2.
        rewrite <- (Weierstrass.mul_mul a b q n G H11 Hns HrG HoG).
        apply (proj2 (Weierstrass.mul_eq_Infinity_iff a b G q H11 Hns HrG
                        HoG HGne Hq Hord (q * n))).
        apply Z.divide_factor_l. }
      pose proof (GroupOrderCounting.family_bound a b (3 * q)
                    (family3 P)
                    H3
                    (fun k Hk =>
                       proj1 (family3_reduced_on_curve P HrP HoP k Hk))
                    (fun k Hk =>
                       proj2 (family3_reduced_on_curve P HrP HoP k Hk))
                    (family3_inj P HrP HoP Hnm Hnm2)) as Hbound.
      lia.
  Qed.

End Tight.
End GroupOrderTight.
