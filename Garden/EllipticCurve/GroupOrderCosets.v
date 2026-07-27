(** * Two-coset point families over a prime-order generator

    Counting kit for the generic short-Weierstrass group: given a generator
    [G] of prime order [q] and a point [P] that is not a multiple of [G],
    the family [k |-> if k <? q then [k]G else P + [k - q]G] over [0, 2q)
    consists of reduced on-curve points and is injective.  Together with an
    upper bound on the number of reduced on-curve points, an injective
    family of [2q] such points bounds [2q] by the curve size, which yields
    the group-order theorem ([mul q P = Infinity] for every reduced on-curve
    [P]) on curves with [2p + 1 < 2q].

    The same-coset and cross-coset cancellation steps are performed on the
    fiat-crypto side of the [Weierstrass.corresponds] bridge
    ([Group.cancel_left]/[cancel_right] and [scalarmult_add_l] over
    [Weierstrass.comm_group]), landing back on Garden points through
    [Weierstrass.corresponds_inj].  Every statement is symbolic in [q] and
    in the scalar indices: nothing in this file computes with scalar-sized
    values. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Spec.WeierstrassCurve.

Global Open Scope Z_scope.

Module GroupOrderCosets.
Section Cosets.
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
  Local Notation on_curve := (Weierstrass.on_curve (p := p) a b).
  Local Notation reduced := (Weierstrass.reduced (p := p)).
  Local Notation add := (Weierstrass.add (p := p) a).
  Local Notation neg := (Weierstrass.neg (p := p)).
  Local Notation mul := (Weierstrass.mul (p := p) a).

  Lemma three_lt_p : 3 < p.
  Proof. lia. Qed.

  Local Notation wpoint := (Weierstrass.wpoint (p := p) a b).
  Local Notation wadd := (Weierstrass.wadd (p := p) a b three_lt_p).
  Local Notation wzero := (Weierstrass.wzero (p := p) a b).
  Local Notation wopp := (Weierstrass.wopp (p := p) a b).
  Local Notation corresponds := (Weierstrass.corresponds (p := p) a b).
  Local Notation smul := (@scalarmult_ref wpoint wadd wzero wopp).

  (** The prime-order generator: reduced, on the curve, not the identity,
      with order certificate [mul q G = Infinity] for a prime [q]. *)
  Variables (G : point) (q : Z).
  Hypothesis HrG : reduced G.
  Hypothesis HoG : on_curve G.
  Hypothesis HGne : G <> Infinity.
  Hypothesis Hq : IsPrime q.
  Hypothesis Hord : mul q G = Infinity.

  (** A reduced on-curve point outside the cyclic subgroup [<G>]. *)
  Variable P : point.
  Hypothesis HrP : reduced P.
  Hypothesis HoP : on_curve P.
  Hypothesis Hnm : forall n : Z, P <> mul n G.

  (** ** The two-coset family

      Indices [0 <= k < q] enumerate the subgroup [<G>]; indices
      [q <= k < 2q] enumerate the coset [P + <G>]. *)
  Definition family (k : Z) : point :=
    if k <? q then mul k G else add P (mul (k - q) G).

  (** ** On-curve closure of [neg] and [mul]

      Direct inductions over the double-and-add structure; each step is the
      transported closure law [Weierstrass.add_on_curve]. *)
  Lemma neg_on_curve (Q : point) : on_curve Q -> on_curve (neg Q).
  Proof.
    intros HQ. destruct Q as [| x y].
    - exact I.
    - cbn [Weierstrass.neg Weierstrass.on_curve] in *.
      rewrite <- HQ.
      assert (Heq : (UnOp.opp (p := p) y) *F (UnOp.opp (p := p) y) = y *F y).
      { unfold UnOp.opp, BinOp.mul.
        rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_opp_opp.
        reflexivity. }
      rewrite Heq. reflexivity.
  Qed.

  Lemma mul_pos_on_curve (n : positive) (Q : point) :
    on_curve Q -> on_curve (Weierstrass.mul_pos (p := p) a n Q).
  Proof.
    intros HQ. induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos].
    - apply Weierstrass.add_on_curve; [exact three_lt_p | exact HQ |].
      apply Weierstrass.add_on_curve; [exact three_lt_p | exact IH | exact IH].
    - apply Weierstrass.add_on_curve; [exact three_lt_p | exact IH | exact IH].
    - exact HQ.
  Qed.

  Lemma mul_on_curve (k : Z) (Q : point) :
    on_curve Q -> on_curve (mul k Q).
  Proof.
    intros HQ. destruct k as [| n | n]; cbn [Weierstrass.mul].
    - exact I.
    - apply mul_pos_on_curve. exact HQ.
    - apply neg_on_curve. apply mul_pos_on_curve. exact HQ.
  Qed.

  (** ** Every family member is reduced and on the curve *)
  Lemma family_reduced_on_curve (k : Z) :
    0 <= k < 2 * q ->
    reduced (family k) /\ on_curve (family k).
  Proof.
    intros _. unfold family. destruct (k <? q).
    - split.
      + apply Weierstrass.mul_reduced. exact HrG.
      + apply mul_on_curve. exact HoG.
    - split.
      + apply Weierstrass.add_reduced; [exact HrP |].
        apply Weierstrass.mul_reduced. exact HrG.
      + apply Weierstrass.add_on_curve; [exact three_lt_p | exact HoP |].
        apply mul_on_curve. exact HoG.
  Qed.

  (** Two fiat images of one Garden point are [W.eq]-equal ([corresponds]
      pins the coordinates modulo [p]). *)
  Lemma corresponds_unique (A : point) (w1 w2 : wpoint) :
    corresponds A w1 -> corresponds A w2 -> W.eq w1 w2.
  Proof.
    destruct A as [| x y]; cbn [Weierstrass.corresponds]; intros H1 H2.
    - unfold W.eq. rewrite H1, H2. exact I.
    - destruct H1 as (x1 & y1 & Hc1 & Hx1 & Hy1).
      destruct H2 as (x2 & y2 & Hc2 & Hx2 & Hy2).
      unfold W.eq. rewrite Hc1, Hc2.
      change (eqm p x1 x2 /\ eqm p y1 y2).
      unfold eqm in *. split; congruence.
  Qed.

  (** ** Same-coset injectivity in [<G>] *)
  Lemma mul_G_inj (i j : Z) :
    0 <= i < q -> 0 <= j < q -> mul i G = mul j G -> i = j.
  Proof.
    intros Hi Hj Heq.
    pose proof (proj1 (Weierstrass.mul_injective_mod a b G q H11 Hns HrG HoG
                         HGne Hq Hord i j) Heq) as Hmod.
    rewrite (Z.mod_small i q Hi), (Z.mod_small j q Hj) in Hmod.
    exact Hmod.
  Qed.

  (** ** Same-coset cancellation in [P + <G>]

      [add P _] is cancelled on the fiat side: both sums correspond to fiat
      points, [Group.cancel_left] removes the shared summand, and
      [corresponds_inj] lands the [W.eq] back on the reduced Garden
      points. *)
  Lemma add_P_cancel (X Y : point) :
    reduced X -> reduced Y -> on_curve X -> on_curve Y ->
    add P X = add P Y -> X = Y.
  Proof.
    intros HrX HrY HoX HoY Heq.
    destruct (Weierstrass.repr_exists a b P HoP) as [wP HwP].
    destruct (Weierstrass.repr_exists a b X HoX) as [wX HwX].
    destruct (Weierstrass.repr_exists a b Y HoY) as [wY HwY].
    pose proof (Weierstrass.comm_group a b three_lt_p H11 Hns) as grp.
    pose proof (Weierstrass.add_corresponds a b three_lt_p P X wP wX HwP HwX)
      as HcX.
    pose proof (Weierstrass.add_corresponds a b three_lt_p P Y wP wY HwP HwY)
      as HcY.
    rewrite Heq in HcX.
    pose proof (corresponds_unique (add P Y) _ _ HcX HcY) as Hweq.
    apply (Weierstrass.corresponds_inj a b X Y wX wY HrX HrY HwX HwY).
    exact (proj1 (Group.cancel_left wP wX wY) Hweq).
  Qed.

  (** ** Cross-coset disjointness

      A multiple of [G] equal to [P + [m]G] would make [P] the multiple
      [[i - m]G]: split [[i]G] as [[i-m]G + [m]G] on the fiat side
      ([scalarmult_add_l]), cancel the shared [[m]G]
      ([Group.cancel_right]), and land back with [corresponds_inj] —
      contradicting [Hnm]. *)
  Lemma coset_disjoint (i m : Z) :
    mul i G <> add P (mul m G).
  Proof.
    intros Heq.
    destruct (Weierstrass.repr_exists a b G HoG) as [wG HwG].
    destruct (Weierstrass.repr_exists a b P HoP) as [wP HwP].
    pose proof (Weierstrass.comm_group a b three_lt_p H11 Hns) as grp.
    pose proof (Weierstrass.mul_corresponds a b three_lt_p H11 Hns G wG HwG)
      as Hmc.
    pose proof (Weierstrass.add_corresponds a b three_lt_p P (mul m G) wP
                  (smul m wG) HwP (Hmc m)) as HcR.
    pose proof (Hmc i) as HcL.
    rewrite Heq in HcL.
    pose proof (corresponds_unique (add P (mul m G)) _ _ HcL HcR) as Hweq.
    assert (Hsplit : W.eq (smul i wG) (wadd (smul (i - m) wG) (smul m wG))).
    { replace i with (i - m + m) at 1 by lia.
      apply scalarmult_add_l. }
    assert (HwPeq : W.eq (smul (i - m) wG) wP).
    { apply (proj1 (Group.cancel_right (smul m wG) (smul (i - m) wG) wP)).
      transitivity (smul i wG); [symmetry; exact Hsplit | exact Hweq]. }
    apply (Hnm (i - m)).
    symmetry.
    exact (Weierstrass.corresponds_inj a b (mul (i - m) G) P (smul (i - m) wG)
             wP (Weierstrass.mul_reduced a (i - m) G HrG) HrP (Hmc (i - m))
             HwP HwPeq).
  Qed.

  (** ** Injectivity of the family on [0, 2q) *)
  Lemma family_inj (i j : Z) :
    0 <= i < 2 * q -> 0 <= j < 2 * q -> family i = family j -> i = j.
  Proof.
    intros Hi Hj. unfold family.
    destruct (Z.ltb_spec i q) as [Hiq | Hiq];
      destruct (Z.ltb_spec j q) as [Hjq | Hjq]; intros Heq.
    - apply mul_G_inj; [lia | lia | exact Heq].
    - exfalso. exact (coset_disjoint i (j - q) Heq).
    - exfalso. exact (coset_disjoint j (i - q) (eq_sym Heq)).
    - assert (Hm : mul (i - q) G = mul (j - q) G).
      { apply add_P_cancel.
        - apply Weierstrass.mul_reduced. exact HrG.
        - apply Weierstrass.mul_reduced. exact HrG.
        - apply mul_on_curve. exact HoG.
        - apply mul_on_curve. exact HoG.
        - exact Heq. }
      assert (Hij : i - q = j - q) by (apply mul_G_inj; [lia | lia | exact Hm]).
      lia.
  Qed.

End Cosets.
End GroupOrderCosets.
