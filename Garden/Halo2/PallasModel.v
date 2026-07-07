(** * Bridge from the Pallas Weierstrass group to the chip model [EccSpec]

    Relates the Pallas instantiation of the generic short-Weierstrass group
    ([EllipticCurve/Pallas.v], itself built on [EllipticCurve/Weierstrass.v])
    to the relational chip model [EccSpec.point_add] / [EccSpec.scalar_mul],
    which uses the [(0, 0)]-sentinel convention.  This file is the Halo2-side
    counterpart to [EllipticCurve/Pallas.v]: it is the only place the group
    theory touches the Halo2 ECC chip spec, which is why it lives here rather
    than under [EllipticCurve/] (which stays independent of [Halo2/] and
    [Orchard/]).

    Every *definition* is given ([repr], its partial inverse [unrepr], and the
    Pallas-specialised wrappers [wadd], [wneg], [wmul], [on_curve], [reduced],
    [nonsingular]). The bridge theorems are proved here against the generic
    Weierstrass laws of [EllipticCurve/Weierstrass.v]; they are the group-law
    facts that [FixedBaseLadder.v] (and, through it, the Orchard determinism
    proof) wire onto: [repr] / [unrepr] and their two round-trip statements
    ([repr_unrepr] / [unrepr_repr]); [repr_add]
    ([repr (add P Q) = point_add (repr P) (repr Q)] on the documented
    on-curve domain — both inputs [reduced] and [on_curve], precisely where
    the [(0, 0)]-sentinel complete-add formula matches the textbook add,
    since affine on-curve points have nonzero [x] and so never collide with
    the identity sentinel, and field-equality of [x] coincides with
    integer-equality on reduced coordinates); [point_add_comm] /
    [point_add_assoc] / [point_add_identity_l] / [point_add_identity_r] /
    [point_add_neg] (the abelian-group laws lifted onto [EccSpec.point_add]
    over the image of [repr]); [scalar_mul_repr]
    ([scalar_mul k (repr G) = repr (mul k G)] for [0 <= k], giving the
    [Z.iter]-defined chip [scalar_mul] the group structure of
    [Weierstrass.mul]); and [mul_equiv_scalar_mul], the same fact restated
    over [EllipticCurve.Pallas]'s own [mul]/[reduced]/[on_curve] wrappers
    (the shape [FixedBaseLadder.v] actually consumes). *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Stdlib.Bool.Bool.

Global Open Scope Z_scope.

(** [EccSpec.point_add] is elaborated over [M.Primes.pallas_p] with the instance
    [M.Primes.PallasPIsPrime]; all Pallas-specialised Weierstrass wrappers below
    use that exact field so the bridge relates one and the same group. *)
#[local] Existing Instance M.Primes.PallasPIsPrime.

Module PallasModel.
  (** ** Pallas specialisation of the generic curve

      The ECC chips operate over the Pallas base field [M.Primes.pallas_p] and
      the curve [y^2 = x^3 + 5] ([a = 0], [b = constants.pallas_b]).  These
      wrappers pin those parameters so the bridge statements read cleanly and so
      downstream files share one Pallas vocabulary. *)

  (** Curve membership on the Pallas curve. *)
  Definition on_curve (P : Weierstrass.point) : Prop :=
    Weierstrass.on_curve (p := M.Primes.pallas_p) 0 constants.pallas_b P.

  (** Coordinates already reduced modulo [M.Primes.pallas_p]. *)
  Definition reduced (P : Weierstrass.point) : Prop :=
    Weierstrass.reduced (p := M.Primes.pallas_p) P.

  (** Nonsingularity of the Pallas curve ([4*0^3 + 27*5^2 <> 0]). *)
  Definition nonsingular : Prop :=
    Weierstrass.nonsingular (p := M.Primes.pallas_p) 0 constants.pallas_b.

  (** Group addition on the Pallas curve. *)
  Definition wadd (P Q : Weierstrass.point) : Weierstrass.point :=
    Weierstrass.add (p := M.Primes.pallas_p) 0 P Q.

  (** Group inverse on the Pallas curve. *)
  Definition wneg (P : Weierstrass.point) : Weierstrass.point :=
    Weierstrass.neg (p := M.Primes.pallas_p) P.

  (** Binary scalar multiplication on the Pallas curve. *)
  Definition wmul (k : Z) (P : Weierstrass.point) : Weierstrass.point :=
    Weierstrass.mul (p := M.Primes.pallas_p) 0 k P.

  (** ** Representation map and its partial inverse

      [repr] sends the point at infinity to the chips' [(0, 0)] sentinel
      ([EccSpec.identity]) and an affine point to the corresponding record.
      [unrepr] is the partial inverse: it reads [(0, 0)] back as infinity and
      every other record as the affine point with those coordinates. *)
  Definition repr (P : Weierstrass.point) : Point.t :=
    match P with
    | Weierstrass.Infinity => EccSpec.identity
    | Weierstrass.Affine x y => {| Point.x := x; Point.y := y |}
    end.

  Definition unrepr (P : Point.t) : Weierstrass.point :=
    if ((Point.x P =? 0) && (Point.y P =? 0))%bool then
      Weierstrass.Infinity
    else
      Weierstrass.Affine (Point.x P) (Point.y P).

  (** ** Helper facts feeding the bridge proofs *)

  (** The Pallas prime as a literal, so [lia] keeps the euclidean products
      linear (the same device as in [Halo2.lemmas.field_solve]). *)
  Notation pallas_p_lit :=
    28948022309329048855892746252171976963363056481941560715954676764349967630337.

  (** Curve membership recast in the [EccSpec] polynomial form. *)
  Lemma on_curve_affine_poly (x y : Z) :
    on_curve (Weierstrass.Affine x y) ->
    y *F y -F (x *F x *F x) -F constants.pallas_b = 0.
  Proof.
    unfold on_curve, Weierstrass.on_curve. intro H.
    rewrite FieldRewrite.mul_zero_left, FieldRewrite.add_zero_right,
      FieldRewrite.add_from_left in H.
    set (A := y *F y) in *.
    set (B := x *F x *F x) in *.
    clearbody A B.
    unfold BinOp.add, BinOp.sub, UnOp.from in *.
    change M.Primes.pallas_p with pallas_p_lit in *.
    lia.
  Qed.

  (** An affine on-curve point has nonzero [x] in the field ([b = 5] is a
      quadratic nonresidue). *)
  Lemma on_curve_x_nonzero (x y : Z) :
    on_curve (Weierstrass.Affine x y) ->
    UnOp.from x <> 0.
  Proof.
    intro H.
    apply (EccSpec.pallas_curve_x_nonzero x y).
    exact (on_curve_affine_poly x y H).
  Qed.

  (** Hence its integer [x] is not the literal [0] (so never the sentinel). *)
  Lemma on_curve_x_neq_0 (x y : Z) :
    on_curve (Weierstrass.Affine x y) ->
    x <> 0.
  Proof.
    intros H Hc.
    apply (on_curve_x_nonzero x y H).
    rewrite Hc. exact FieldRewrite.from_zero.
  Qed.

  (** On reduced coordinates the field-subtraction zero test coincides with the
      integer equality test of [x]-coordinates. *)
  Lemma reduced_sub_eqb (x1 x2 : Z) :
    UnOp.from x1 = x1 ->
    UnOp.from x2 = x2 ->
    ((x1 -F x2) =? 0) = (x1 =? x2).
  Proof.
    intros Hx1 Hx2.
    pose proof (prime_range (p := M.Primes.pallas_p)) as Hp.
    assert (B1 : 0 <= x1 < M.Primes.pallas_p).
    { pose proof (Z.mod_pos_bound x1 M.Primes.pallas_p ltac:(lia)) as Hb.
      unfold UnOp.from in Hx1. rewrite Hx1 in Hb. exact Hb. }
    assert (B2 : 0 <= x2 < M.Primes.pallas_p).
    { pose proof (Z.mod_pos_bound x2 M.Primes.pallas_p ltac:(lia)) as Hb.
      unfold UnOp.from in Hx2. rewrite Hx2 in Hb. exact Hb. }
    destruct (x1 =? x2) eqn:E.
    - apply Z.eqb_eq in E. subst x2.
      assert (Hzero : x1 -F x1 = 0).
      { unfold BinOp.sub. rewrite Z.sub_diag. apply Zmod_0_l. }
      rewrite Hzero. reflexivity.
    - apply Z.eqb_neq in E.
      apply Z.eqb_neq. intro Hc.
      unfold BinOp.sub in Hc.
      assert (Hd : x1 - x2 = 0).
      { apply (mod_0_range M.Primes.pallas_p (x1 - x2)); [lia | lia | exact Hc]. }
      apply E. lia.
  Qed.

  (** [repr] is a section of [unrepr] on every record (the only collision is the
      sentinel, which [unrepr] sends to infinity and [repr] sends back). *)
  Lemma repr_unrepr (Q : Point.t) :
    repr (unrepr Q) = Q.
  Proof.
    destruct Q as [qx qy].
    unfold unrepr, repr. cbn [Point.x Point.y].
    destruct ((qx =? 0) && (qy =? 0))%bool eqn:Hb.
    - apply Bool.andb_true_iff in Hb. destruct Hb as [Hx Hy].
      apply Z.eqb_eq in Hx, Hy. subst. reflexivity.
    - reflexivity.
  Qed.

  (** [unrepr] is a retraction of [repr] on the on-curve domain: an affine
      on-curve point has nonzero [x] (the curve constant [5] is a quadratic
      nonresidue), so it is never confused with the identity sentinel. *)
  Lemma unrepr_repr (P : Weierstrass.point) :
    on_curve P ->
    unrepr (repr P) = P.
  Proof.
    destruct P as [|x y].
    - intros _. reflexivity.
    - intros Hoc.
      pose proof (on_curve_x_neq_0 x y Hoc) as Hxn.
      unfold unrepr, repr. cbn [Point.x Point.y].
      rewrite (proj2 (Z.eqb_neq x 0) Hxn).
      cbn [andb]. reflexivity.
  Qed.

  (** ** Addition bridge on the on-curve domain

      On the documented domain — both inputs [reduced] and [on_curve] — the
      [(0, 0)]-sentinel complete-add formula [EccSpec.point_add] computes the
      [repr] of the textbook Weierstrass [add]. *)
  Lemma repr_add (P Q : Weierstrass.point) :
    reduced P ->
    reduced Q ->
    on_curve P ->
    on_curve Q ->
    repr (wadd P Q) = EccSpec.point_add (repr P) (repr Q).
  Proof.
    destruct P as [|x1 y1].
    - (* P = Infinity: [wadd Infinity Q = Q] and [point_add identity = id]. *)
      intros _ _ _ _.
      unfold wadd. cbn [Weierstrass.add].
      change (repr Weierstrass.Infinity) with EccSpec.identity.
      rewrite EccSpec.point_add_identity_left. reflexivity.
    - destruct Q as [|x2 y2].
      + (* Q = Infinity: [wadd P Infinity = P] and [point_add P identity = P]. *)
        intros HrP HrQ HoP HoQ.
        pose proof (on_curve_x_neq_0 x1 y1 HoP) as Hx1n.
        unfold wadd, EccSpec.point_add.
        cbn [Weierstrass.add repr Point.x Point.y EccSpec.identity].
        unfold CompleteAddition.output,
          Garden.Halo2.halo2_gadgets.utilities_proof.square.
        rewrite (proj2 (Z.eqb_neq x1 0) Hx1n).
        rewrite Z.eqb_refl.
        reflexivity.
      + (* Both affine: the heart of the addition bridge. *)
        intros HrP HrQ HoP HoQ.
        destruct HrP as [Hx1r Hy1r].
        destruct HrQ as [Hx2r Hy2r].
        pose proof (on_curve_x_neq_0 x1 y1 HoP) as Hx1n.
        pose proof (on_curve_x_neq_0 x2 y2 HoQ) as Hx2n.
        unfold wadd, EccSpec.point_add.
        cbn [Weierstrass.add repr Point.x Point.y EccSpec.identity].
        unfold CompleteAddition.output,
          Garden.Halo2.halo2_gadgets.utilities_proof.square.
        rewrite (proj2 (Z.eqb_neq x1 0) Hx1n).
        rewrite (proj2 (Z.eqb_neq x2 0) Hx2n).
        rewrite (reduced_sub_eqb x1 x2 Hx1r Hx2r).
        destruct (x1 =? x2) eqn:Exeq.
        * apply Z.eqb_eq in Exeq. subst x2.
          destruct ((y1 +F y2) =? 0) eqn:Eyy.
          -- (* inverse: both sides the identity / sentinel *)
             cbn [andb]. reflexivity.
          -- (* doubling: reconcile the two tangent-slope expressions *)
             cbn [andb].
             assert (Hnum :
                 UnOp.from 3 *F x1 *F x1 +F 0 = UnOp.from 3 *F (x1 *F x1)).
             { rewrite FieldRewrite.add_zero_right, FieldRewrite.from_mul.
               apply field_mul_assoc. }
             rewrite Hnum.
             set (lam := BinOp.div (UnOp.from 3 *F (x1 *F x1))
                                   (UnOp.from 2 *F y1)).
             clearbody lam.
             replace (lam *F lam -F UnOp.from 2 *F x1)
               with (lam *F lam -F x1 -F x1) by field_solve.
             reflexivity.
        * (* secant: identical formulas on both sides *)
          cbn [andb]. reflexivity.
  Qed.

  (** ** Pallas side conditions of the Weierstrass laws *)

  (** Characteristic bound [3 < p]. *)
  Lemma three_lt_p : 3 < M.Primes.pallas_p.
  Proof. change M.Primes.pallas_p with pallas_p_lit. lia. Qed.

  (** Sharper characteristic bound [11 < p], required by [add_assoc]'s
      fiat-crypto transport ([W.commutative_group] needs [char_ge 12]). *)
  Lemma eleven_lt_p : 11 < M.Primes.pallas_p.
  Proof. change M.Primes.pallas_p with pallas_p_lit. lia. Qed.

  (** Nonsingularity of [y^2 = x^3 + 5] over Pallas ([4*0 + 27*25 = 675 <> 0]). *)
  Lemma nonsingular_holds : nonsingular.
  Proof.
    unfold nonsingular, Weierstrass.nonsingular.
    intro Hc. vm_compute in Hc. discriminate.
  Qed.

  (** Outputs of [wadd] are reduced when the inputs are. *)
  Lemma reduced_wadd (P Q : Weierstrass.point) :
    reduced P ->
    reduced Q ->
    reduced (wadd P Q).
  Proof.
    intros HrP HrQ.
    destruct P as [|x1 y1]; destruct Q as [|x2 y2];
      unfold wadd; cbn [Weierstrass.add].
    - exact I.
    - exact HrQ.
    - exact HrP.
    - destruct ((x1 -F x2) =? 0).
      + destruct ((y1 +F y2) =? 0).
        * exact I.
        * split; apply from_sub_reduced.
      + split; apply from_sub_reduced.
  Qed.

  (** [wneg] preserves reducedness. *)
  Lemma reduced_wneg (P : Weierstrass.point) :
    reduced P ->
    reduced (wneg P).
  Proof.
    intros HrP. destruct P as [|x y].
    - exact I.
    - destruct HrP as [Hx Hy].
      unfold wneg. cbn [Weierstrass.neg].
      split.
      + exact Hx.
      + unfold UnOp.opp, UnOp.from. apply Zmod_mod.
  Qed.

  (** [wneg] preserves curve membership ([y -> -y] fixes [y^2]). *)
  Lemma on_curve_wneg (P : Weierstrass.point) :
    on_curve P ->
    on_curve (wneg P).
  Proof.
    destruct P as [|x y].
    - intros _. exact I.
    - intro H.
      unfold wneg. cbn [Weierstrass.neg].
      unfold on_curve, Weierstrass.on_curve in *.
      rewrite <- H.
      assert (Hsq : BinOp.mul (UnOp.opp y) (UnOp.opp y) = BinOp.mul y y).
      { unfold BinOp.mul, UnOp.opp.
        rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
        f_equal. ring. }
      rewrite Hsq. reflexivity.
  Qed.

  (** Reverse of [on_curve_affine_poly]: the [EccSpec] curve polynomial implies
      Weierstrass curve membership of the affine point. *)
  Lemma affine_on_curve_of_poly (x y : Z) :
    y *F y -F (x *F x *F x) -F constants.pallas_b = 0 ->
    on_curve (Weierstrass.Affine x y).
  Proof.
    intro H.
    unfold on_curve, Weierstrass.on_curve.
    rewrite FieldRewrite.mul_zero_left, FieldRewrite.add_zero_right,
      FieldRewrite.add_from_left.
    set (A := y *F y) in *.
    set (B := x *F x *F x) in *.
    assert (HAr : UnOp.from A = A) by (subst A; apply FieldRewrite.from_mul).
    assert (HBr : UnOp.from B = B)
      by (subst B; apply FieldRewrite.from_mul).
    clearbody A B.
    unfold BinOp.add, BinOp.sub, UnOp.from in *.
    change M.Primes.pallas_p with pallas_p_lit in *.
    lia.
  Qed.

  (** ** Closure of [EccSpec.point_add] on the curve

      Complete addition of two reduced on-curve points lands back on the curve
      or on the [(0, 0)] identity sentinel (the latter exactly when the inputs
      are mutual inverses).  Transported from the Weierstrass group's closure
      [Weierstrass.add_on_curve] through the [repr] bridge [repr_add]. *)
  Lemma point_add_curve_poly_or_identity (P Q : Point.t)
      (HrPx : UnOp.from (Point.x P) = Point.x P)
      (HrPy : UnOp.from (Point.y P) = Point.y P)
      (HrQx : UnOp.from (Point.x Q) = Point.x Q)
      (HrQy : UnOp.from (Point.y Q) = Point.y Q)
      (HPpoly :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F constants.pallas_b = 0)
      (HQpoly :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F constants.pallas_b = 0) :
    (Point.y (EccSpec.point_add P Q) *F Point.y (EccSpec.point_add P Q) -F
      (Point.x (EccSpec.point_add P Q) *F Point.x (EccSpec.point_add P Q) *F
        Point.x (EccSpec.point_add P Q)) -F constants.pallas_b = 0) \/
    EccSpec.point_add P Q = EccSpec.identity.
  Proof.
    destruct P as [px py]. destruct Q as [qx qy].
    cbn [Point.x Point.y] in *.
    assert (HoP : on_curve (Weierstrass.Affine px py))
      by (apply affine_on_curve_of_poly; exact HPpoly).
    assert (HoQ : on_curve (Weierstrass.Affine qx qy))
      by (apply affine_on_curve_of_poly; exact HQpoly).
    assert (HrP : reduced (Weierstrass.Affine px py))
      by (split; [exact HrPx | exact HrPy]).
    assert (HrQ : reduced (Weierstrass.Affine qx qy))
      by (split; [exact HrQx | exact HrQy]).
    change {| Point.x := px; Point.y := py |}
      with (repr (Weierstrass.Affine px py)).
    change {| Point.x := qx; Point.y := qy |}
      with (repr (Weierstrass.Affine qx qy)).
    rewrite <- (repr_add (Weierstrass.Affine px py)
      (Weierstrass.Affine qx qy) HrP HrQ HoP HoQ).
    assert (Hsum_oc :
        on_curve (wadd (Weierstrass.Affine px py)
          (Weierstrass.Affine qx qy))).
    { unfold on_curve, wadd.
      exact (Weierstrass.add_on_curve 0 constants.pallas_b
        (Weierstrass.Affine px py) (Weierstrass.Affine qx qy)
        three_lt_p HoP HoQ). }
    set (S := wadd (Weierstrass.Affine px py) (Weierstrass.Affine qx qy)) in *.
    clearbody S.
    destruct S as [| rx ry].
    - right. reflexivity.
    - left. cbn [repr Point.x Point.y].
      exact (on_curve_affine_poly rx ry Hsum_oc).
  Qed.

  (** ** The group laws lifted onto [EccSpec.point_add]

      Each lift is a corollary of [repr_add] together with the corresponding
      Weierstrass law; the Pallas-specific side conditions of those laws
      ([3 < p], [nonsingular]) are discharged internally, so they do not appear
      here. *)

  (** Commutativity. *)
  Lemma point_add_comm (P Q : Weierstrass.point) :
    reduced P ->
    reduced Q ->
    on_curve P ->
    on_curve Q ->
    EccSpec.point_add (repr P) (repr Q) = EccSpec.point_add (repr Q) (repr P).
  Proof.
    intros HrP HrQ HoP HoQ.
    rewrite <- (repr_add P Q HrP HrQ HoP HoQ).
    rewrite <- (repr_add Q P HrQ HrP HoQ HoP).
    unfold wadd.
    rewrite (Weierstrass.add_comm 0 constants.pallas_b P Q HoP HoQ).
    reflexivity.
  Qed.

  (** Associativity. *)
  Lemma point_add_assoc (P Q R : Weierstrass.point) :
    reduced P ->
    reduced Q ->
    reduced R ->
    on_curve P ->
    on_curve Q ->
    on_curve R ->
    EccSpec.point_add (EccSpec.point_add (repr P) (repr Q)) (repr R) =
    EccSpec.point_add (repr P) (EccSpec.point_add (repr Q) (repr R)).
  Proof.
    intros HrP HrQ HrR HoP HoQ HoR.
    pose proof three_lt_p as H3.
    pose proof eleven_lt_p as H11.
    pose proof nonsingular_holds as Hns.
    pose proof (Weierstrass.add_on_curve 0 constants.pallas_b
                  P Q H3 HoP HoQ) as HoPQ.
    pose proof (Weierstrass.add_on_curve 0 constants.pallas_b
                  Q R H3 HoQ HoR) as HoQR.
    pose proof (reduced_wadd P Q HrP HrQ) as HrPQ.
    pose proof (reduced_wadd Q R HrQ HrR) as HrQR.
    rewrite <- (repr_add P Q HrP HrQ HoP HoQ).
    rewrite <- (repr_add Q R HrQ HrR HoQ HoR).
    rewrite <- (repr_add (wadd P Q) R HrPQ HrR HoPQ HoR).
    rewrite <- (repr_add P (wadd Q R) HrP HrQR HoP HoQR).
    unfold wadd.
    rewrite (Weierstrass.add_assoc 0 constants.pallas_b
               P Q R H11 Hns HrP HrQ HrR HoP HoQ HoR).
    reflexivity.
  Qed.

  (** Left identity (the sentinel is the neutral element). *)
  Lemma point_add_identity_l (P : Weierstrass.point) :
    EccSpec.point_add EccSpec.identity (repr P) = repr P.
  Proof.
    apply EccSpec.point_add_identity_left.
  Qed.

  (** Right identity on the on-curve domain. *)
  Lemma point_add_identity_r (P : Weierstrass.point) :
    reduced P ->
    on_curve P ->
    EccSpec.point_add (repr P) EccSpec.identity = repr P.
  Proof.
    intros HrP HoP.
    change EccSpec.identity with (repr Weierstrass.Infinity).
    rewrite <- (repr_add P Weierstrass.Infinity HrP I HoP I).
    unfold wadd.
    rewrite (Weierstrass.add_Infinity_r 0 constants.pallas_b P).
    reflexivity.
  Qed.

  (** Inverse law: a point plus its negation is the identity. *)
  Lemma point_add_neg (P : Weierstrass.point) :
    reduced P ->
    on_curve P ->
    EccSpec.point_add (repr P) (repr (wneg P)) = EccSpec.identity.
  Proof.
    intros HrP HoP.
    rewrite <- (repr_add P (wneg P)
                  HrP (reduced_wneg P HrP) HoP (on_curve_wneg P HoP)).
    unfold wadd, wneg.
    rewrite (Weierstrass.add_neg 0 constants.pallas_b P).
    reflexivity.
  Qed.

  (** ** Helpers for the scalar-multiplication bridge: the
      multiple-as-running-sum recurrence *)

  (** One double-and-add step at the group level: [(m+1)G = mG + G]. *)
  Lemma wmul_succ (m : Z) (G : Weierstrass.point) :
    reduced G ->
    on_curve G ->
    wmul (m + 1) G = wadd (wmul m G) G.
  Proof.
    intros HrG HoG.
    unfold wmul, wadd.
    rewrite (Weierstrass.mul_add 0 constants.pallas_b m 1 G
               eleven_lt_p nonsingular_holds HrG HoG).
    change (Weierstrass.mul 0 1 G) with G.
    reflexivity.
  Qed.

  (** Each nonnegative multiple of an on-curve generator is reduced and
      on-curve. *)
  Lemma wmul_nat_props (n : nat) (G : Weierstrass.point) :
    reduced G ->
    on_curve G ->
    reduced (wmul (Z.of_nat n) G) /\ on_curve (wmul (Z.of_nat n) G).
  Proof.
    intros HrG HoG. induction n.
    - cbn [Z.of_nat]. unfold wmul.
      rewrite (Weierstrass.mul_0 0 constants.pallas_b G).
      split; exact I.
    - destruct IHn as [Hred Hoc].
      rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
      rewrite (wmul_succ (Z.of_nat n) G HrG HoG).
      split.
      + exact (reduced_wadd (wmul (Z.of_nat n) G) G Hred HrG).
      + exact (Weierstrass.add_on_curve 0 constants.pallas_b
                 (wmul (Z.of_nat n) G) G three_lt_p Hoc HoG).
  Qed.

  (** The chip's [Z.iter] scalar multiplication satisfies the same recurrence. *)
  Lemma scalar_mul_succ_nat (n : nat) (P : Point.t) :
    EccSpec.scalar_mul (Z.of_nat (S n)) P =
    EccSpec.point_add (EccSpec.scalar_mul (Z.of_nat n) P) P.
  Proof.
    unfold EccSpec.scalar_mul.
    rewrite (iter_nat_of_Z (Z.of_nat (S n)) _ _ _ (Zle_0_nat _)).
    rewrite (iter_nat_of_Z (Z.of_nat n) _ _ _ (Zle_0_nat _)).
    rewrite !Zabs2Nat.id.
    reflexivity.
  Qed.

  (** Bridge for nonnegative scalars given as a [nat]. *)
  Lemma scalar_mul_repr_nat (n : nat) (G : Weierstrass.point) :
    reduced G ->
    on_curve G ->
    EccSpec.scalar_mul (Z.of_nat n) (repr G) = repr (wmul (Z.of_nat n) G).
  Proof.
    intros HrG HoG. induction n.
    - cbn [Z.of_nat].
      rewrite EccSpec.scalar_mul_0.
      unfold wmul.
      rewrite (Weierstrass.mul_0 0 constants.pallas_b G).
      reflexivity.
    - rewrite scalar_mul_succ_nat.
      rewrite IHn.
      destruct (wmul_nat_props n G HrG HoG) as [Hred Hoc].
      rewrite <- (repr_add (wmul (Z.of_nat n) G) G Hred HrG Hoc HoG).
      rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
      rewrite (wmul_succ (Z.of_nat n) G HrG HoG).
      reflexivity.
  Qed.

  (** ** Scalar-multiplication bridge

      The chip's double-and-add [EccSpec.scalar_mul] (defined by [Z.iter], hence
      the identity for nonpositive scalars) equals [repr] of the Weierstrass
      multiple for every nonnegative scalar. *)
  Lemma scalar_mul_repr (k : Z) (G : Weierstrass.point) :
    0 <= k ->
    reduced G ->
    on_curve G ->
    EccSpec.scalar_mul k (repr G) = repr (wmul k G).
  Proof.
    intros Hk HrG HoG.
    rewrite <- (Z2Nat.id k Hk).
    apply scalar_mul_repr_nat; assumption.
  Qed.

  (** ** [mul] agrees with [EccSpec.scalar_mul], over [Pallas]'s own wrappers

      Through [repr], [Pallas]'s double-and-add [Pallas.mul] computes the same
      point as the chip model's iterated complete addition, for non-negative
      scalars on the curve. (Domain caveat: the [(0,0)]-sentinel [point_add]
      matches the textbook [add] only on the on-curve domain the ladder stays
      inside; [scalar_mul_repr] above establishes that the ladder does stay
      inside it, by induction on the scalar.) *)
  Lemma mul_equiv_scalar_mul (k : Z) (P : Pallas.point) :
    0 <= k ->
    Pallas.reduced P ->
    Pallas.on_curve P ->
    repr (Pallas.mul k P) = EccSpec.scalar_mul k (repr P).
  Proof.
  (* The [Pallas.reduced P] premise is mandatory: [EccSpec.point_add] (via
     [CompleteAddition.output]) decides the doubling/inverse branch with the
     *integer* tests [x1 =? x2] / [x1 =? 0] on the raw coordinates, whereas
     [Weierstrass.add] uses the *field* test [(x1 -F x2) =? 0]. For a
     non-reduced on-curve representative [P = Affine (x0 + p) y0] of a
     prime-order generator, at the step that adds the raw [P] to a reduced
     accumulator equal to [-P] (reached at [k = pallas_q - 1]), the field x's
     coincide but the integer x's differ, so [scalar_mul] takes the secant
     branch and divides by [(x0 + p) - x0 = p ≡ 0], producing garbage, while
     [repr (Pallas.mul pallas_q P) = Pallas.identity]. With [reduced P] the two
     coordinate conventions agree and the bridge is exactly [scalar_mul_repr]. *)
    intros Hk HrP HoP.
    symmetry.
    exact (scalar_mul_repr k P Hk HrP HoP).
  Qed.

End PallasModel.
