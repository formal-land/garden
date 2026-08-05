(** * Semantic refinement of the primitive Vesta Jacobian backend

    The executable Jacobian layer stores Montgomery field elements.  This
    file first decodes every coordinate to [Z / pallas_q], then transports
    the resulting projective point through fiat-crypto's proved Jacobian
    group law to Garden's abstract [Vesta.add].  The relation is the usual
    one: [(X,Y,Z)] represents infinity when [Z = 0], and otherwise represents
    [(X/Z^2,Y/Z^3)].

    The executable addition uses the standard [add-2007-bl] formula.  Its
    non-degenerate output is a projective rescaling by two of fiat-crypto's
    unequal-point formula; this is proved algebraically below.  Thus the
    proof validates the actual primitive implementation and does not replace
    it with a second executable group law. *)

From Stdlib Require Import ZArith Lia Ring Bool PeanoNat.
From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.EllipticCurve.FiatField.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module VkJacobianRefinement.
  Module J := VkJacobian.
  Module F := PallasQ.
  Module R := PallasQFacts.

  Local Notation q := Primes.pallas_q.

  Lemma q_pos : q <> 0.
  Proof. pose proof (@prime_range q Primes.PallasQIsPrime); lia. Qed.

  Lemma three_lt_q : 3 < q.
  Proof. change (3 < Vesta.vesta_p). exact Vesta.three_lt_p. Qed.

  (** ** Modular setoid infrastructure *)

  Local Instance eqm_equiv : Equivalence (eqm q).
  Proof. unfold eqm. constructor; congruence. Qed.

  Local Instance add_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.add :=
    Zplus_eqm q.
  Local Instance mul_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.mul :=
    Zmult_eqm q.
  Local Instance opp_eqm_mor : Proper (eqm q ==> eqm q) Z.opp :=
    Zopp_eqm q.
  Local Instance sub_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.sub :=
    Zminus_eqm q.

  Local Instance field_add_Proper :
      Proper (eqm q ==> eqm q ==> eqm q) BinOp.add.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.add.
    repeat setoid_rewrite (Zmod_eqm q).
    exact (Zplus_eqm q x x' Hx y y' Hy).
  Qed.

  Local Instance field_sub_Proper :
      Proper (eqm q ==> eqm q ==> eqm q) BinOp.sub.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.sub.
    repeat setoid_rewrite (Zmod_eqm q).
    exact (Zminus_eqm q x x' Hx y y' Hy).
  Qed.

  Local Instance field_mul_Proper :
      Proper (eqm q ==> eqm q ==> eqm q) BinOp.mul.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.mul.
    repeat setoid_rewrite (Zmod_eqm q).
    exact (Zmult_eqm q x x' Hx y y' Hy).
  Qed.

  Local Ltac eqm_ring :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    repeat setoid_rewrite (Zmod_eqm q);
    unfold eqm; f_equal; ring.

  Lemma eqm_from_zero (u : Z) : eqm q u 0 <-> UnOp.from u = 0.
  Proof.
    unfold eqm, UnOp.from. rewrite Z.mod_0_l by exact q_pos. reflexivity.
  Qed.

  Lemma from_bin_mul (u v : Z) :
    UnOp.from (BinOp.mul u v) = BinOp.mul u v.
  Proof. unfold UnOp.from, BinOp.mul. apply Zmod_mod. Qed.

  Lemma eqm_red_eq (u v : Z) :
    UnOp.from u = u -> UnOp.from v = v ->
    (eqm q u v <-> u = v).
  Proof. unfold eqm, UnOp.from. intros Hu Hv. split; congruence. Qed.

  Lemma nz_from (u : Z) : ~ eqm q u 0 -> UnOp.from u <> 0.
  Proof.
    intros Hu H. apply Hu. unfold eqm, UnOp.from in *.
    rewrite H, Z.mod_0_l by exact q_pos. reflexivity.
  Qed.

  Lemma nz_mul (u v : Z) :
    ~ eqm q u 0 -> ~ eqm q v 0 ->
    ~ eqm q (BinOp.mul u v) 0.
  Proof.
    intros Hu Hv H.
    apply (field_from_mul_nonzero u v (nz_from u Hu) (nz_from v Hv)).
    unfold eqm, UnOp.from in *.
    rewrite Z.mod_0_l in H by exact q_pos.
    unfold BinOp.mul in *.
    rewrite Z.mod_mod in H by exact q_pos.
    rewrite Z.mod_mod by exact q_pos. exact H.
  Qed.

  Lemma reduced_eqm_eq (u v : Z) :
    0 <= u < q -> 0 <= v < q -> eqm q u v -> u = v.
  Proof.
    unfold eqm. intros Hu Hv H.
    rewrite (Z.mod_small u q Hu), (Z.mod_small v q Hv) in H.
    exact H.
  Qed.

  (** ** Abstract projective representation *)

  Definition jpoint : Set := Z * Z * Z.
  Definition jzero : jpoint := (0, 1, 0).

  Definition jrepr (K : jpoint) (P : Vesta.point) : Prop :=
    let '(X, Y, Zc) := K in
    match P with
    | Weierstrass.Infinity => eqm q Zc 0
    | Weierstrass.Affine x y =>
        ~ eqm q Zc 0 /\
        eqm q X (BinOp.mul x (BinOp.mul Zc Zc)) /\
        eqm q Y (BinOp.mul y (BinOp.mul (BinOp.mul Zc Zc) Zc))
    end.

  Definition trip_eqm (K L : jpoint) : Prop :=
    let '(X, Y, Zc) := K in
    let '(X', Y', Zc') := L in
    eqm q X X' /\ eqm q Y Y' /\ eqm q Zc Zc'.

  Lemma jrepr_zero : jrepr jzero Vesta.identity.
  Proof. reflexivity. Qed.

  Lemma jrepr_trip_eqm (K L : jpoint) (P : Vesta.point) :
    trip_eqm K L -> jrepr L P -> jrepr K P.
  Proof.
    destruct K as [[X Y] Zc], L as [[X' Y'] Zc']; cbn.
    intros (HX & HY & HZ) H.
    destruct P as [|px py]; cbn in *.
    - now rewrite HZ.
    - destruct H as (Hnz & Hx & Hy).
      split; [now rewrite HZ | split].
      + now rewrite HX, HZ.
      + now rewrite HY, HZ.
  Qed.

  Lemma jrepr_inj (K : jpoint) (P Q : Vesta.point) :
    Vesta.reduced P -> Vesta.reduced Q ->
    jrepr K P -> jrepr K Q -> P = Q.
  Proof.
    destruct K as [[X Y] Zc].
    destruct P as [|x1 y1]; destruct Q as [|x2 y2];
      cbn [jrepr Vesta.reduced Weierstrass.reduced].
    - reflexivity.
    - intros _ _ HP (HQ & _ & _). exfalso. exact (HQ HP).
    - intros _ _ (HP & _ & _) HQ. exfalso. exact (HP HQ).
    - intros (Hx1 & Hy1) (Hx2 & Hy2)
        (Hnz & HX1 & HY1) (_ & HX2 & HY2).
      assert (Hzz : ~ eqm q (BinOp.mul Zc Zc) 0)
        by (apply nz_mul; exact Hnz).
      assert (Hzzz : ~ eqm q
        (BinOp.mul (BinOp.mul Zc Zc) Zc) 0)
        by (apply nz_mul; [exact Hzz | exact Hnz]).
      assert (Hxe :
        BinOp.mul x1 (BinOp.mul Zc Zc) =
        BinOp.mul x2 (BinOp.mul Zc Zc)).
      { apply (eqm_red_eq _ _ (from_bin_mul _ _) (from_bin_mul _ _)).
        transitivity X; [symmetry; exact HX1 | exact HX2]. }
      assert (Hye :
        BinOp.mul y1 (BinOp.mul (BinOp.mul Zc Zc) Zc) =
        BinOp.mul y2 (BinOp.mul (BinOp.mul Zc Zc) Zc)).
      { apply (eqm_red_eq _ _ (from_bin_mul _ _) (from_bin_mul _ _)).
        transitivity Y; [symmetry; exact HY1 | exact HY2]. }
      pose proof (field_mul_cancel_r x1 x2 _ (nz_from _ Hzz) Hxe) as Hx.
      pose proof (field_mul_cancel_r y1 y2 _ (nz_from _ Hzzz) Hye) as Hy.
      change (x1 mod q = x2 mod q) in Hx.
      change (y1 mod q = y2 mod q) in Hy.
      change (x1 mod q = x1) in Hx1.
      change (x2 mod q = x2) in Hx2.
      change (y1 mod q = y1) in Hy1.
      change (y2 mod q = y2) in Hy2.
      rewrite Hx1, Hx2 in Hx. rewrite Hy1, Hy2 in Hy. congruence.
  Qed.

  (** ** Transport through fiat-crypto's proved Jacobian group law *)

  Local Notation fpt :=
    (@Jacobian.point Z (eqm q) 0 BinOp.add BinOp.mul
      Vesta.a Vesta.b (@eqm_dec q)).
  Local Notation wpt :=
    (Weierstrass.wpoint (p := q) Vesta.a Vesta.b).

  Definition jto_affine (P : fpt) : wpt :=
    @Jacobian.to_affine Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub
      BinOp.mul Finv BinOp.div Vesta.a Vesta.b (@Field_eqm q _)
      (@eqm_dec q) P.

  Lemma jrepr_curve_obligation (X Y Zc : Z) (P : Vesta.point) :
    Vesta.on_curve P -> jrepr (X, Y, Zc) P ->
    (if dec (eqm q Zc 0) then True
     else eqm q (BinOp.mul Y Y)
       (BinOp.add
         (BinOp.add (BinOp.mul (BinOp.mul X X) X)
           (BinOp.mul (BinOp.mul Vesta.a X)
             (BinOp.mul (BinOp.mul Zc Zc) (BinOp.mul Zc Zc))))
         (BinOp.mul Vesta.b
           (BinOp.mul (BinOp.mul (BinOp.mul Zc Zc) Zc)
             (BinOp.mul (BinOp.mul Zc Zc) Zc))))).
  Proof.
    intros Hoc HK.
    destruct (dec (eqm q Zc 0)) as [Hz | Hz]; [exact I |].
    destruct P as [|px py]; cbn [jrepr] in HK.
    { contradiction. }
    destruct HK as (_ & HX & HY).
    cbn [Vesta.on_curve Weierstrass.on_curve] in Hoc.
    assert (Hoc' : eqm q (BinOp.mul py py)
      (BinOp.add
        (BinOp.add (BinOp.mul (BinOp.mul px px) px)
          (BinOp.mul Vesta.a px)) Vesta.b)).
    { unfold UnOp.from in Hoc. exact Hoc. }
    rewrite HX, HY.
    transitivity
      (BinOp.mul (BinOp.mul py py)
        (BinOp.mul (BinOp.mul (BinOp.mul Zc Zc) Zc)
          (BinOp.mul (BinOp.mul Zc Zc) Zc))).
    { eqm_ring. }
    rewrite Hoc'. eqm_ring.
  Qed.

  Definition fpt_of (X Y Zc : Z) (P : Vesta.point)
      (Hoc : Vesta.on_curve P) (HK : jrepr (X, Y, Zc) P) : fpt :=
    exist _ (X, Y, Zc) (jrepr_curve_obligation X Y Zc P Hoc HK).

  Lemma fpt_of_proj (X Y Zc : Z) P Hoc HK :
    proj1_sig (fpt_of X Y Zc P Hoc HK) = (X, Y, Zc).
  Proof. reflexivity. Qed.

  Lemma jto_affine_coords (JP : fpt) :
    W.coordinates (jto_affine JP) =
    (let '(X, Y, Zc) := proj1_sig JP in
     if dec (eqm q Zc 0) then inr tt
     else inl (BinOp.div X (BinOp.mul Zc Zc),
       BinOp.div Y (BinOp.mul (BinOp.mul Zc Zc) Zc))).
  Proof. destruct JP as [[[X Y] Zc] pf]. reflexivity. Qed.

  Lemma eqm_div_of_mul (u v d : Z) :
    ~ eqm q d 0 -> eqm q u (BinOp.mul v d) ->
    eqm q v (BinOp.div u d).
  Proof.
    intros Hd Hu.
    assert (Hd' : d mod q <> 0) by exact (nz_from d Hd).
    pose proof (div_mul (p := q) u d three_lt_q Hd') as Hdm.
    assert (Hstep :
      BinOp.mul (BinOp.div u d) d = BinOp.mul v d).
    { rewrite Hdm. unfold eqm in Hu. unfold BinOp.mul in *.
      rewrite Hu, Z.mod_mod by exact q_pos. reflexivity. }
    symmetry.
    exact (field_mul_cancel_r (BinOp.div u d) v d
      (nz_from d Hd) Hstep).
  Qed.

  Lemma eqm_mul_of_div (u v d : Z) :
    ~ eqm q d 0 -> eqm q v (BinOp.div u d) ->
    eqm q u (BinOp.mul v d).
  Proof.
    intros Hd Hv.
    assert (Hd' : d mod q <> 0) by exact (nz_from d Hd).
    pose proof (div_mul (p := q) u d three_lt_q Hd') as Hdm.
    rewrite Hv, Hdm. unfold eqm.
    rewrite Z.mod_mod by exact q_pos. reflexivity.
  Qed.

  Lemma jcorr (X Y Zc : Z) (P : Vesta.point) Hoc HK :
    Weierstrass.corresponds Vesta.a Vesta.b P
      (jto_affine (fpt_of X Y Zc P Hoc HK)).
  Proof.
    destruct P as [|px py].
    - cbn [Weierstrass.corresponds].
      rewrite jto_affine_coords, fpt_of_proj.
      cbn [jrepr] in HK.
      destruct (dec (eqm q Zc 0)); [reflexivity | contradiction].
    - cbn [Weierstrass.corresponds].
      rewrite jto_affine_coords, fpt_of_proj.
      cbn [jrepr] in HK. destruct HK as (Hnz & HX & HY).
      destruct (dec (eqm q Zc 0)); [contradiction |].
      eexists; eexists; split; [reflexivity | split].
      + apply eqm_div_of_mul; [|exact HX].
        apply nz_mul; exact Hnz.
      + apply eqm_div_of_mul; [|exact HY].
        apply nz_mul; [apply nz_mul |]; exact Hnz.
  Qed.

  Lemma jrepr_of_corresponds (JP : fpt) (P : Vesta.point) :
    Weierstrass.corresponds Vesta.a Vesta.b P (jto_affine JP) ->
    jrepr (proj1_sig JP) P.
  Proof.
    intros Hc.
    pose proof (jto_affine_coords JP) as Hco.
    destruct JP as [[[X Y] Zc] pf]. cbn [proj1_sig] in *.
    destruct P as [|px py]; cbn [Weierstrass.corresponds] in Hc;
      rewrite Hco in Hc; clear Hco; revert Hc;
      destruct (dec (eqm q Zc 0)) as [Hz | Hz]; intros Hc.
    - exact Hz.
    - discriminate.
    - destruct Hc as (x' & y' & Hbad & _ & _). discriminate.
    - destruct Hc as (x' & y' & Heq & Hx & Hy).
      injection Heq as <- <-.
      cbn [jrepr]. split; [exact Hz | split].
      + apply eqm_mul_of_div; [|exact Hx].
        apply nz_mul; exact Hz.
      + apply eqm_mul_of_div; [|exact Hy].
        apply nz_mul; [apply nz_mul |]; exact Hz.
  Qed.

  Definition jdouble_fiat (P : fpt) : fpt :=
    @Jacobian.double Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub
      BinOp.mul Finv BinOp.div Vesta.a Vesta.b (@Field_eqm q _)
      (@eqm_dec q) P.

  Definition jdouble_impl (K : jpoint) : jpoint :=
    @Jacobian.double_impl Z BinOp.add BinOp.sub BinOp.mul Vesta.a K.

  Lemma jdouble_fiat_proj (P : fpt) :
    proj1_sig (jdouble_fiat P) = jdouble_impl (proj1_sig P).
  Proof. reflexivity. Qed.

  Lemma jto_affine_double (P : fpt) :
    W.eq (jto_affine (jdouble_fiat P))
      (Weierstrass.wadd Vesta.a Vesta.b three_lt_q
        (jto_affine P) (jto_affine P)).
  Proof.
    exact
      (@Jacobian.to_affine_double Z (eqm q) 0 1 UnOp.opp BinOp.add
        BinOp.sub BinOp.mul Finv BinOp.div Vesta.a Vesta.b
        (@Field_eqm q _) (Weierstrass.c3 three_lt_q) (@eqm_dec q) P).
  Qed.

  Lemma jrepr_double_impl (K : jpoint) (P : Vesta.point) :
    Vesta.on_curve P -> jrepr K P ->
    jrepr (jdouble_impl K) (Vesta.add P P).
  Proof.
    destruct K as [[X Y] Zc]. intros Hoc HK.
    pose (JP := fpt_of X Y Zc P Hoc HK).
    pose proof (jcorr X Y Zc P Hoc HK) as Hcorr.
    pose proof
      (Weierstrass.add_corresponds Vesta.a Vesta.b three_lt_q
        P P (jto_affine JP) (jto_affine JP) Hcorr Hcorr) as Hadd.
    pose proof
      (Weierstrass.corresponds_W_eq Vesta.a Vesta.b (Vesta.add P P)
        (Weierstrass.wadd Vesta.a Vesta.b three_lt_q
          (jto_affine JP) (jto_affine JP))
        (jto_affine (jdouble_fiat JP)) Hadd
        (Weierstrass.W_eq_sym Vesta.a Vesta.b _ _
          (jto_affine_double JP))) as Hout.
    pose proof (jrepr_of_corresponds (jdouble_fiat JP)
      (Vesta.add P P) Hout) as Hr.
    rewrite jdouble_fiat_proj in Hr. unfold JP in Hr.
    rewrite fpt_of_proj in Hr.
    exact Hr.
  Qed.

  Definition jadd_neq_fiat (P Q : fpt) (H : ~ Jacobian.eq P Q) : fpt :=
    Jacobian.add_inequal_nz_nz P Q H.

  Lemma jto_affine_add_neq (P Q : fpt) (Hneq : ~ Jacobian.eq P Q)
      (HP : ~ Jacobian.iszero P) (HQ : ~ Jacobian.iszero Q) :
    W.eq (jto_affine (jadd_neq_fiat P Q Hneq))
      (Weierstrass.wadd Vesta.a Vesta.b three_lt_q
        (jto_affine P) (jto_affine Q)).
  Proof.
    exact (Jacobian.to_affine_add_inequal_nz_nz P Q Hneq HP HQ).
  Qed.

  Lemma jrepr_add_neq_fiat (JP JQ : fpt) (P Q : Vesta.point)
      (HcorrP : Weierstrass.corresponds Vesta.a Vesta.b P (jto_affine JP))
      (HcorrQ : Weierstrass.corresponds Vesta.a Vesta.b Q (jto_affine JQ))
      (Hneq : ~ Jacobian.eq JP JQ)
      (HP : ~ Jacobian.iszero JP) (HQ : ~ Jacobian.iszero JQ) :
    jrepr (proj1_sig (jadd_neq_fiat JP JQ Hneq)) (Vesta.add P Q).
  Proof.
    pose proof
      (Weierstrass.add_corresponds Vesta.a Vesta.b three_lt_q
        P Q (jto_affine JP) (jto_affine JQ) HcorrP HcorrQ) as Hadd.
    pose proof
      (Weierstrass.corresponds_W_eq Vesta.a Vesta.b (Vesta.add P Q)
        (Weierstrass.wadd Vesta.a Vesta.b three_lt_q
          (jto_affine JP) (jto_affine JQ))
        (jto_affine (jadd_neq_fiat JP JQ Hneq)) Hadd
        (Weierstrass.W_eq_sym Vesta.a Vesta.b _ _
          (jto_affine_add_neq JP JQ Hneq HP HQ))) as Hout.
    exact (jrepr_of_corresponds (jadd_neq_fiat JP JQ Hneq)
      (Vesta.add P Q) Hout).
  Qed.

  (** ** Refinement relation for the primitive Montgomery records *)

  Definition affine_canonical (p : J.affine) : Prop :=
    F.canonical p.(J.affine_x) /\ F.canonical p.(J.affine_y).

  Definition point_canonical (p : J.point) : Prop :=
    F.canonical p.(J.x) /\ F.canonical p.(J.y) /\ F.canonical p.(J.z).

  Definition coordinates (p : J.point) : jpoint :=
    (F.denote p.(J.x), F.denote p.(J.y), F.denote p.(J.z)).

  Definition affine_denote (p : J.affine) : Vesta.point :=
    Vesta.affine (F.denote p.(J.affine_x)) (F.denote p.(J.affine_y)).

  Definition represents (p : J.point) (P : Vesta.point) : Prop :=
    point_canonical p /\ Vesta.reduced P /\ Vesta.on_curve P /\
    jrepr (coordinates p) P.

  Lemma canonical_of_normalized (x : F.t) :
    x = F.from_Z (F.to_Z x) -> F.canonical x.
  Proof.
    intro Hx. rewrite Hx. apply R.from_Z_canonical.
  Qed.

  Lemma affine_canonical_of_normalized (p : J.affine) :
    p.(J.affine_x) = F.from_Z (F.to_Z p.(J.affine_x)) ->
    p.(J.affine_y) = F.from_Z (F.to_Z p.(J.affine_y)) ->
    affine_canonical p.
  Proof.
    intros Hx Hy. split; apply canonical_of_normalized; assumption.
  Qed.

  Lemma point_canonical_of_normalized (p : J.point) :
    p.(J.x) = F.from_Z (F.to_Z p.(J.x)) ->
    p.(J.y) = F.from_Z (F.to_Z p.(J.y)) ->
    p.(J.z) = F.from_Z (F.to_Z p.(J.z)) ->
    point_canonical p.
  Proof.
    intros Hx Hy Hz. split; [|split]; apply canonical_of_normalized; assumption.
  Qed.

  Lemma denote_range (a : F.t) : 0 <= F.denote a < q.
  Proof.
    unfold F.denote. apply Z.mod_pos_bound.
    pose proof three_lt_q; lia.
  Qed.

  Lemma denote_reduced (a : F.t) : UnOp.from (F.denote a) = F.denote a.
  Proof.
    unfold UnOp.from. apply Z.mod_small. exact (denote_range a).
  Qed.

  Lemma equal_denote_eqb (a b : F.t)
      (Ha : F.canonical a) (Hb : F.canonical b) :
    F.equal a b = Z.eqb (F.denote a) (F.denote b).
  Proof.
    destruct (F.equal a b) eqn:Hab;
      destruct (Z.eqb (F.denote a) (F.denote b)) eqn:Hden;
      try reflexivity.
    - exfalso. apply Z.eqb_neq in Hden. apply Hden.
      exact (proj1 (R.equal_denote_iff a b Ha Hb) Hab).
    - exfalso. apply Z.eqb_eq in Hden.
      apply (proj1 (R.equal_denote_false_iff a b Ha Hb)) in Hab.
      exact (Hab Hden).
  Qed.

  Lemma is_identity_denote (p : J.point) :
    F.canonical p.(J.z) ->
    J.is_identity p = Z.eqb (F.denote p.(J.z)) 0.
  Proof.
    intro Hz. unfold J.is_identity.
    rewrite (equal_denote_eqb p.(J.z) F.zero Hz R.zero_canonical).
    reflexivity.
  Qed.

  Lemma identity_canonical : point_canonical J.identity.
  Proof.
    split; [exact R.zero_canonical |].
    split; [exact R.one_canonical | exact R.zero_canonical].
  Qed.

  Lemma identity_coordinates : coordinates J.identity = jzero.
  Proof.
    reflexivity.
  Qed.

  Lemma identity_represents : represents J.identity Vesta.identity.
  Proof.
    split; [exact identity_canonical |].
    split; [exact I | split; [exact I |]].
    rewrite identity_coordinates. exact jrepr_zero.
  Qed.

  Lemma of_affine_canonical (p : J.affine) :
    affine_canonical p -> point_canonical (J.of_affine p).
  Proof.
    destruct p as [px py]. intros (Hx & Hy).
    cbn [affine_canonical point_canonical J.of_affine] in *.
    repeat split; assumption || exact R.one_canonical.
  Qed.

  Lemma of_affine_coordinates (p : J.affine) :
    coordinates (J.of_affine p) =
      (F.denote p.(J.affine_x), F.denote p.(J.affine_y), 1).
  Proof.
    destruct p; reflexivity.
  Qed.

  Lemma jrepr_affine_denote (p : J.affine) :
    jrepr
      (F.denote p.(J.affine_x), F.denote p.(J.affine_y), 1)
      (affine_denote p).
  Proof.
    destruct p as [px py].
    cbn [affine_denote Vesta.affine jrepr].
    split; [|split].
    - intro H. unfold eqm in H.
      rewrite Z.mod_small in H by (pose proof three_lt_q; lia).
      rewrite Z.mod_0_l in H by exact q_pos. discriminate.
    - eqm_ring.
    - eqm_ring.
  Qed.

  Lemma of_affine_represents (p : J.affine) :
    affine_canonical p -> Vesta.on_curve (affine_denote p) ->
    represents (J.of_affine p) (affine_denote p).
  Proof.
    intros Hcan Hon.
    split; [now apply of_affine_canonical |].
    split; [apply Vesta.affine_reduced | split; [exact Hon |]].
    rewrite of_affine_coordinates. apply jrepr_affine_denote.
  Qed.

  (** ** Executable doubling *)

  Definition ztwice (a : Z) : Z := BinOp.add a a.
  Definition zthrice (a : Z) : Z := BinOp.add a (ztwice a).
  Definition zeight_times (a : Z) : Z := ztwice (ztwice (ztwice a)).

  Definition zdouble_xx (K : jpoint) : Z :=
    let '(X, _, _) := K in BinOp.mul X X.
  Definition zdouble_yy (K : jpoint) : Z :=
    let '(_, Y, _) := K in BinOp.mul Y Y.
  Definition zdouble_yyyy (K : jpoint) : Z :=
    BinOp.mul (zdouble_yy K) (zdouble_yy K).
  Definition zdouble_s (K : jpoint) : Z :=
    let '(X, _, _) := K in
    ztwice (BinOp.sub
      (BinOp.sub (BinOp.mul (BinOp.add X (zdouble_yy K))
        (BinOp.add X (zdouble_yy K))) (zdouble_xx K))
      (zdouble_yyyy K)).
  Definition zdouble_m (K : jpoint) : Z := zthrice (zdouble_xx K).
  Definition zdouble_x3 (K : jpoint) : Z :=
    BinOp.sub (BinOp.mul (zdouble_m K) (zdouble_m K))
      (ztwice (zdouble_s K)).
  Definition zdouble_y3 (K : jpoint) : Z :=
    BinOp.sub (BinOp.mul (zdouble_m K)
      (BinOp.sub (zdouble_s K) (zdouble_x3 K)))
      (zeight_times (zdouble_yyyy K)).
  Definition zdouble_z3 (K : jpoint) : Z :=
    let '(_, Y, Zc) := K in ztwice (BinOp.mul Y Zc).

  Definition jdouble_exec (K : jpoint) : jpoint :=
    let '(X, Y, Zc) := K in
    if Z.eqb Zc 0 then jzero else
    (zdouble_x3 K, zdouble_y3 K, zdouble_z3 K).

  Definition double_xx (p : J.point) : F.t := F.square p.(J.x).
  Definition double_yy (p : J.point) : F.t := F.square p.(J.y).
  Definition double_yyyy (p : J.point) : F.t := F.square (double_yy p).
  Definition double_s (p : J.point) : F.t :=
    J.twice (F.sub
      (F.sub (F.square (F.add p.(J.x) (double_yy p))) (double_xx p))
      (double_yyyy p)).
  Definition double_m (p : J.point) : F.t := J.thrice (double_xx p).
  Definition double_x3 (p : J.point) : F.t :=
    F.sub (F.square (double_m p)) (J.twice (double_s p)).
  Definition double_y3 (p : J.point) : F.t :=
    F.sub (F.mul (double_m p) (F.sub (double_s p) (double_x3 p)))
      (J.eight_times (double_yyyy p)).
  Definition double_z3 (p : J.point) : F.t :=
    J.twice (F.mul p.(J.y) p.(J.z)).
  Definition double_core (p : J.point) : J.point := J.double_core p.

  Lemma double_as_core (p : J.point) :
    J.double p = if J.is_identity p then J.identity else double_core p.
  Proof.
    unfold J.double, double_core. destruct (J.is_identity p); reflexivity.
  Qed.

  Lemma twice_canonical (a : F.t) :
    F.canonical a -> F.canonical (J.twice a).
  Proof. intro Ha. apply R.add_canonical; exact Ha. Qed.

  Lemma thrice_canonical (a : F.t) :
    F.canonical a -> F.canonical (J.thrice a).
  Proof.
    intro Ha. unfold J.thrice.
    apply R.add_canonical; [exact Ha | now apply twice_canonical].
  Qed.

  Lemma eight_times_canonical (a : F.t) :
    F.canonical a -> F.canonical (J.eight_times a).
  Proof.
    intro Ha. unfold J.eight_times.
    do 3 apply twice_canonical. exact Ha.
  Qed.

  Local Ltac fcanonical :=
    lazymatch goal with
    | |- F.canonical F.zero => exact R.zero_canonical
    | |- F.canonical F.one => exact R.one_canonical
    | |- F.canonical (F.square ?a) =>
        apply R.square_canonical; fcanonical
    | |- F.canonical (J.twice ?a) =>
        apply twice_canonical; fcanonical
    | |- F.canonical (J.thrice ?a) =>
        apply thrice_canonical; fcanonical
    | |- F.canonical (J.eight_times ?a) =>
        apply eight_times_canonical; fcanonical
    | |- F.canonical (F.add ?a ?b) =>
        apply R.add_canonical; fcanonical
    | |- F.canonical (F.sub ?a ?b) =>
        apply R.sub_canonical; fcanonical
    | |- F.canonical (F.mul ?a ?b) =>
        apply R.mul_canonical; fcanonical
    | |- ?G => first [assumption | fail 1 "fcanonical cannot prove" G]
    end.

  Lemma point_canonical_build (x y z : F.t) :
    F.canonical x -> F.canonical y -> F.canonical z ->
    point_canonical {| J.x := x; J.y := y; J.z := z |}.
  Proof.
    intros Hx Hy Hz. unfold point_canonical.
    change (F.canonical x /\ F.canonical y /\ F.canonical z).
    tauto.
  Qed.

  Lemma double_xx_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_xx p).
  Proof.
    intros (Hx & _ & _). unfold double_xx.
    exact (R.square_canonical p.(J.x) Hx).
  Qed.

  Lemma double_yy_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_yy p).
  Proof.
    intros (_ & Hy & _). unfold double_yy.
    exact (R.square_canonical p.(J.y) Hy).
  Qed.

  Lemma double_yyyy_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_yyyy p).
  Proof.
    intro Hp. unfold double_yyyy.
    exact (R.square_canonical _ (double_yy_canonical p Hp)).
  Qed.

  Lemma double_s_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_s p).
  Proof.
    intro Hp. destruct Hp as (Hx & Hy & Hz).
    unfold double_s. apply twice_canonical, R.sub_canonical.
    - apply R.sub_canonical.
      + apply R.square_canonical, R.add_canonical.
        * exact Hx.
        * apply double_yy_canonical. repeat split; assumption.
      + apply double_xx_canonical. repeat split; assumption.
    - apply double_yyyy_canonical. repeat split; assumption.
  Qed.

  Lemma double_m_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_m p).
  Proof.
    intro Hp. unfold double_m.
    exact (thrice_canonical _ (double_xx_canonical p Hp)).
  Qed.

  Lemma double_x3_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_x3 p).
  Proof.
    intro Hp. unfold double_x3. apply R.sub_canonical.
    - exact (R.square_canonical _ (double_m_canonical p Hp)).
    - exact (twice_canonical _ (double_s_canonical p Hp)).
  Qed.

  Lemma double_y3_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_y3 p).
  Proof.
    intro Hp. unfold double_y3. apply R.sub_canonical.
    - apply R.mul_canonical, R.sub_canonical.
      + apply double_s_canonical, Hp.
      + apply double_x3_canonical, Hp.
    - exact (eight_times_canonical _ (double_yyyy_canonical p Hp)).
  Qed.

  Lemma double_z3_canonical (p : J.point) :
    point_canonical p -> F.canonical (double_z3 p).
  Proof.
    intros (_ & _ & Hz). unfold double_z3.
    apply twice_canonical, R.mul_canonical. exact Hz.
  Qed.

  Lemma double_core_canonical (p : J.point) :
    point_canonical p -> point_canonical (double_core p).
  Proof.
    destruct p as [px py pz]. intros (Hpx & Hpy & Hpz).
    unfold double_core, J.double_core, point_canonical.
    cbn [J.x J.y J.z].
    set (xx := F.square px).
    set (yy := F.square py).
    set (yyyy := F.square yy).
    set (s := J.twice
      (F.sub (F.sub (F.square (F.add px yy)) xx) yyyy)).
    set (m := J.thrice xx).
    set (x3 := F.sub (F.square m) (J.twice s)).
    set (y3 := F.sub (F.mul m (F.sub s x3))
      (J.eight_times yyyy)).
    set (z3 := J.twice (F.mul py pz)).
    assert (Hxx : F.canonical xx)
      by (unfold xx; exact (R.square_canonical px Hpx)).
    assert (Hyy : F.canonical yy)
      by (unfold yy; exact (R.square_canonical py Hpy)).
    assert (Hyyyy : F.canonical yyyy)
      by (unfold yyyy; exact (R.square_canonical yy Hyy)).
    assert (Hsum : F.canonical (F.add px yy))
      by exact (R.add_canonical px yy Hpx Hyy).
    assert (Hsqsum : F.canonical (F.square (F.add px yy)))
      by exact (R.square_canonical _ Hsum).
    assert (Hsubxx : F.canonical (F.sub (F.square (F.add px yy)) xx))
      by exact (R.sub_canonical _ _ Hsqsum Hxx).
    assert (Hsubyyyy : F.canonical
      (F.sub (F.sub (F.square (F.add px yy)) xx) yyyy))
      by exact (R.sub_canonical _ _ Hsubxx Hyyyy).
    assert (Hs : F.canonical s)
      by (unfold s; exact (twice_canonical _ Hsubyyyy)).
    assert (Hm : F.canonical m)
      by (unfold m; exact (thrice_canonical _ Hxx)).
    assert (Hx3 : F.canonical x3).
    { unfold x3. apply R.sub_canonical.
      - exact (R.square_canonical _ Hm).
      - exact (twice_canonical _ Hs). }
    assert (Hy3 : F.canonical y3).
    { unfold y3. apply R.sub_canonical.
      - apply R.mul_canonical. exact (R.sub_canonical _ _ Hs Hx3).
      - exact (eight_times_canonical _ Hyyyy). }
    assert (Hz3 : F.canonical z3).
    { unfold z3. exact (twice_canonical _ (R.mul_canonical _ _ Hpz)). }
    exact (conj Hx3 (conj Hy3 Hz3)).
  Qed.

  Lemma double_canonical (p : J.point) :
    point_canonical p -> point_canonical (J.double p).
  Proof.
    intro Hcan. rewrite double_as_core. destruct (J.is_identity p).
    - exact identity_canonical.
    - now apply double_core_canonical.
  Qed.

  Lemma twice_denote (a : F.t) :
    F.canonical a -> F.denote (J.twice a) = ztwice (F.denote a).
  Proof.
    intro Ha. unfold J.twice, ztwice.
    rewrite (R.add_denote a a Ha Ha). reflexivity.
  Qed.

  Lemma thrice_denote (a : F.t) :
    F.canonical a -> F.denote (J.thrice a) = zthrice (F.denote a).
  Proof.
    intro Ha. unfold J.thrice, zthrice.
    rewrite (R.add_denote a (J.twice a) Ha (twice_canonical a Ha)).
    rewrite (twice_denote a Ha). reflexivity.
  Qed.

  Lemma eight_times_denote (a : F.t) :
    F.canonical a -> F.denote (J.eight_times a) = zeight_times (F.denote a).
  Proof.
    intro Ha. unfold J.eight_times, zeight_times.
    rewrite (twice_denote _ (twice_canonical _ (twice_canonical a Ha))).
    rewrite (twice_denote _ (twice_canonical a Ha)).
    rewrite (twice_denote a Ha).
    reflexivity.
  Qed.

  Lemma double_xx_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_xx p) = zdouble_xx (coordinates p).
  Proof.
    intros (Hx & _ & _). unfold double_xx, zdouble_xx, coordinates.
    destruct p; cbn [J.x J.y J.z].
    rewrite R.square_denote by exact Hx. reflexivity.
  Qed.

  Lemma double_yy_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_yy p) = zdouble_yy (coordinates p).
  Proof.
    intros (_ & Hy & _). unfold double_yy, zdouble_yy, coordinates.
    destruct p; cbn [J.x J.y J.z].
    rewrite R.square_denote by exact Hy. reflexivity.
  Qed.

  Lemma double_yyyy_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_yyyy p) = zdouble_yyyy (coordinates p).
  Proof.
    intro Hp. unfold double_yyyy, zdouble_yyyy.
    rewrite R.square_denote by now apply double_yy_canonical.
    rewrite double_yy_denote by exact Hp. reflexivity.
  Qed.

  Strategy opaque [F.add F.sub F.mul F.square F.denote].

  (** Prove the nested field formula once over variables.  Instantiating this
      opaque lemma is substantially cheaper than replaying its rewrite chain
      over the concrete Montgomery expression in [double_s]. *)
  Local Lemma double_s_formula_denote (x yy xx yyyy : F.t) :
    F.canonical x -> F.canonical yy ->
    F.canonical xx -> F.canonical yyyy ->
    F.denote
      (J.twice
        (F.sub (F.sub (F.square (F.add x yy)) xx) yyyy)) =
      ztwice
        (BinOp.sub
          (BinOp.sub
            (BinOp.mul
              (BinOp.add (F.denote x) (F.denote yy))
              (BinOp.add (F.denote x) (F.denote yy)))
            (F.denote xx))
          (F.denote yyyy)).
  Proof.
    intros Hx Hyy Hxx Hyyyy.
    pose proof (R.add_canonical x yy Hx Hyy) as Hsum.
    pose proof (R.square_canonical _ Hsum) as Hsqsum.
    pose proof (R.sub_canonical _ _ Hsqsum Hxx) as Hsubxx.
    pose proof (R.sub_canonical _ _ Hsubxx Hyyyy) as Hsubyyyy.
    rewrite (twice_denote _ Hsubyyyy).
    rewrite (R.sub_denote _ _ Hsubxx Hyyyy).
    rewrite (R.sub_denote _ _ Hsqsum Hxx).
    rewrite (R.square_denote _ Hsum).
    rewrite (R.add_denote _ _ Hx Hyy).
    reflexivity.
  Qed.

  Lemma double_s_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_s p) = zdouble_s (coordinates p).
  Proof.
    intro Hp.
    pose proof Hp as (Hx & _ & _).
    pose proof (double_xx_canonical p Hp) as Hxx.
    pose proof (double_yy_canonical p Hp) as Hyy.
    pose proof (double_yyyy_canonical p Hp) as Hyyyy.
    unfold double_s.
    rewrite (double_s_formula_denote p.(J.x) (double_yy p)
      (double_xx p) (double_yyyy p) Hx Hyy Hxx Hyyyy).
    rewrite (double_xx_denote p Hp), (double_yy_denote p Hp),
      (double_yyyy_denote p Hp).
    unfold zdouble_s. destruct p; reflexivity.
  Qed.

  Lemma double_m_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_m p) = zdouble_m (coordinates p).
  Proof.
    intro Hp. unfold double_m, zdouble_m.
    rewrite (thrice_denote _ (double_xx_canonical p Hp)).
    now rewrite (double_xx_denote p Hp).
  Qed.

  Lemma double_x3_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_x3 p) = zdouble_x3 (coordinates p).
  Proof.
    intro Hp.
    pose proof (double_m_canonical p Hp) as Hm.
    pose proof (double_s_canonical p Hp) as Hs.
    pose proof (R.square_canonical _ Hm) as Hm2.
    pose proof (twice_canonical _ Hs) as Htwices.
    unfold double_x3, zdouble_x3.
    rewrite (R.sub_denote _ _ Hm2 Htwices).
    rewrite (R.square_denote _ Hm).
    rewrite (twice_denote _ Hs).
    now rewrite (double_m_denote p Hp), (double_s_denote p Hp).
  Qed.

  Local Lemma double_y3_formula_denote
      (m s x3 yyyy : F.t) (zm zs zx3 zyyyy : Z) :
    F.canonical s -> F.canonical x3 -> F.canonical yyyy ->
    F.denote m = zm -> F.denote s = zs ->
    F.denote x3 = zx3 -> F.denote yyyy = zyyyy ->
    F.denote
      (F.sub (F.mul m (F.sub s x3)) (J.eight_times yyyy)) =
      BinOp.sub (BinOp.mul zm (BinOp.sub zs zx3))
        (zeight_times zyyyy).
  Proof.
    intros Hsc Hx3c Hyyyyc Hm Hs Hx3 Hyyyy.
    pose proof (R.sub_canonical s x3 Hsc Hx3c) as Hsx.
    pose proof (R.mul_canonical m (F.sub s x3) Hsx) as Hmul.
    pose proof (eight_times_canonical yyyy Hyyyyc) as Height.
    rewrite (R.sub_denote _ _ Hmul Height).
    rewrite (R.mul_denote _ _ Hsx).
    rewrite (R.sub_denote _ _ Hsc Hx3c).
    rewrite (eight_times_denote _ Hyyyyc).
    now rewrite Hm, Hs, Hx3, Hyyyy.
  Qed.

  Lemma double_y3_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_y3 p) = zdouble_y3 (coordinates p).
  Proof.
    intro Hp.
    unfold double_y3, zdouble_y3.
    exact (double_y3_formula_denote
      (double_m p) (double_s p) (double_x3 p) (double_yyyy p)
      (zdouble_m (coordinates p)) (zdouble_s (coordinates p))
      (zdouble_x3 (coordinates p)) (zdouble_yyyy (coordinates p))
      (double_s_canonical p Hp) (double_x3_canonical p Hp)
      (double_yyyy_canonical p Hp) (double_m_denote p Hp)
      (double_s_denote p Hp) (double_x3_denote p Hp)
      (double_yyyy_denote p Hp)).
  Qed.

  Lemma double_z3_denote (p : J.point) :
    point_canonical p ->
    F.denote (double_z3 p) = zdouble_z3 (coordinates p).
  Proof.
    intros (_ & Hy & Hz). unfold double_z3, zdouble_z3, coordinates.
    destruct p; cbn [J.x J.y J.z].
    rewrite (twice_denote _ (R.mul_canonical _ _ Hz)).
    rewrite (R.mul_denote _ _ Hz). reflexivity.
  Qed.

  Lemma double_core_coordinates (p : J.point) :
    point_canonical p ->
    coordinates (double_core p) =
      (zdouble_x3 (coordinates p), zdouble_y3 (coordinates p),
       zdouble_z3 (coordinates p)).
  Proof.
    intro Hp. unfold coordinates, double_core, J.double_core.
    change
      ((F.denote (double_x3 p), F.denote (double_y3 p),
        F.denote (double_z3 p)) =
       (zdouble_x3 (coordinates p), zdouble_y3 (coordinates p),
        zdouble_z3 (coordinates p))).
    now rewrite double_x3_denote, double_y3_denote, double_z3_denote.
  Qed.

  Strategy transparent [F.add F.sub F.mul F.square F.denote].

  Local Ltac fdenote :=
    repeat first
      [ rewrite twice_denote by fcanonical
      | rewrite R.square_denote by fcanonical
      | rewrite R.add_denote by fcanonical
      | rewrite R.sub_denote by fcanonical
      | rewrite R.mul_denote by fcanonical ].

  Lemma double_coordinates (p : J.point) :
    point_canonical p ->
    coordinates (J.double p) = jdouble_exec (coordinates p).
  Proof.
    intro Hcan. rewrite double_as_core.
    rewrite (is_identity_denote p (proj2 (proj2 Hcan))).
    unfold jdouble_exec. destruct p as [px py pz].
    cbn [coordinates J.x J.y J.z] in *.
    destruct (Z.eqb (F.denote pz) 0).
    - exact identity_coordinates.
    - apply double_core_coordinates. exact Hcan.
  Qed.

  Lemma jdouble_exec_agrees (K : jpoint) :
    let '(_, _, Zc) := K in Z.eqb Zc 0 = false ->
    trip_eqm (jdouble_exec K) (jdouble_impl K).
  Proof.
    destruct K as [[X Y] Zc]. intro Hnz.
    cbv beta iota zeta delta
      [jdouble_exec jdouble_impl Jacobian.double_impl ztwice zthrice
       zeight_times zdouble_xx zdouble_yy zdouble_yyyy zdouble_s zdouble_m
       zdouble_x3 zdouble_y3 zdouble_z3 Vesta.a].
    cbn [fst snd].
    rewrite Hnz. repeat split; eqm_ring.
  Qed.

  Lemma jdouble_exec_sound (K : jpoint) (P : Vesta.point) :
    Vesta.on_curve P -> jrepr K P ->
    jrepr (jdouble_exec K) (Vesta.add P P).
  Proof.
    destruct K as [[X Y] Zc]. intros Hon Hrepr.
    destruct (Z.eqb Zc 0) eqn:Hz.
    - apply Z.eqb_eq in Hz.
      assert (HP : P = Vesta.identity).
      { destruct P as [|px py]; [reflexivity |].
        cbn [jrepr] in Hrepr. destruct Hrepr as (Hnz & _ & _).
        exfalso. apply Hnz. unfold eqm. rewrite Hz, Z.mod_0_l by exact q_pos.
        reflexivity. }
      subst P. cbn [Vesta.add Vesta.identity Weierstrass.add].
      cbn [jdouble_exec]. rewrite Hz. exact jrepr_zero.
    - eapply jrepr_trip_eqm.
      + exact (jdouble_exec_agrees (X, Y, Zc) Hz).
      + apply jrepr_double_impl; assumption.
  Qed.

  Lemma double_represents (p : J.point) (P : Vesta.point) :
    represents p P -> represents (J.double p) (Vesta.add P P).
  Proof.
    intros (Hcan & Hred & Hon & Hrepr).
    split; [now apply double_canonical |].
    split.
    - exact (Weierstrass.add_reduced Vesta.a P P Hred Hred).
    - split.
      + exact (Weierstrass.add_on_curve Vesta.a Vesta.b P P three_lt_q Hon Hon).
      + rewrite double_coordinates by exact Hcan.
        exact (jdouble_exec_sound (coordinates p) P Hon Hrepr).
  Qed.

  Lemma double_n_canonical (count : nat) (p : J.point) :
    point_canonical p -> point_canonical (J.double_n count p).
  Proof.
    revert p. induction count as [|count IH]; intros p Hp; cbn [J.double_n].
    - exact Hp.
    - apply IH, double_canonical, Hp.
  Qed.

  Lemma double_n_represents (count : nat) (p : J.point) (P : Vesta.point) :
    represents p P ->
    represents (J.double_n count p)
      (Nat.iter count (fun Q => Vesta.add Q Q) P).
  Proof.
    revert p P. induction count as [|count IH]; intros p P Hp.
    - cbn [J.double_n Nat.iter]. exact Hp.
    - cbn [J.double_n]. rewrite Nat.iter_succ_r.
      apply IH, double_represents, Hp.
  Qed.

  (** ** Executable complete addition *)

  Definition jadd_exec (K L : jpoint) : jpoint :=
    let '(X1, Y1, Z1) := K in
    let '(X2, Y2, Z2) := L in
    if Z.eqb Z1 0 then L else
    if Z.eqb Z2 0 then K else
    let Z1Z1 := BinOp.mul Z1 Z1 in
    let Z2Z2 := BinOp.mul Z2 Z2 in
    let U1 := BinOp.mul X1 Z2Z2 in
    let U2 := BinOp.mul X2 Z1Z1 in
    let S1 := BinOp.mul Y1 (BinOp.mul Z2 Z2Z2) in
    let S2 := BinOp.mul Y2 (BinOp.mul Z1 Z1Z1) in
    if Z.eqb U1 U2 then
      if Z.eqb S1 S2 then jdouble_exec K else jzero
    else
      let H := BinOp.sub U2 U1 in
      let I := BinOp.mul (ztwice H) (ztwice H) in
      let Jc := BinOp.mul H I in
      let Rr := ztwice (BinOp.sub S2 S1) in
      let V := BinOp.mul U1 I in
      let X3 := BinOp.sub (BinOp.sub (BinOp.mul Rr Rr) Jc) (ztwice V) in
      let Y3 := BinOp.sub (BinOp.mul Rr (BinOp.sub V X3))
        (ztwice (BinOp.mul S1 Jc)) in
      let Z3 := BinOp.mul
        (BinOp.sub (BinOp.sub
          (BinOp.mul (BinOp.add Z1 Z2) (BinOp.add Z1 Z2)) Z1Z1) Z2Z2) H in
      (X3, Y3, Z3).

  Definition add_core (p r : J.point) : J.point := J.add_core p r.

  Lemma add_as_core (p r : J.point) :
    J.add p r =
      if J.is_identity p then r
      else if J.is_identity r then p
      else add_core p r.
  Proof.
    unfold J.add, add_core. destruct (J.is_identity p); [reflexivity |].
    destruct (J.is_identity r); [reflexivity |].
    reflexivity.
  Qed.

  Lemma add_core_canonical (p r : J.point) :
    point_canonical p -> point_canonical r -> point_canonical (add_core p r).
  Proof.
    destruct p as [px py pz], r as [rx ry rz].
    intros (Hpx & Hpy & Hpz) (Hrx & Hry & Hrz).
    unfold add_core, J.add_core. cbn [J.x J.y J.z].
    set (Z1Z1 := F.square pz). set (Z2Z2 := F.square rz).
    set (U1 := F.mul px Z2Z2). set (U2 := F.mul rx Z1Z1).
    set (S1 := F.mul py (F.mul rz Z2Z2)).
    set (S2 := F.mul ry (F.mul pz Z1Z1)).
    assert (HZ1Z1 : F.canonical Z1Z1)
      by (unfold Z1Z1; exact (R.square_canonical pz Hpz)).
    assert (HZ2Z2 : F.canonical Z2Z2)
      by (unfold Z2Z2; exact (R.square_canonical rz Hrz)).
    assert (HU1 : F.canonical U1)
      by (unfold U1; exact (R.mul_canonical px Z2Z2 HZ2Z2)).
    assert (HU2 : F.canonical U2)
      by (unfold U2; exact (R.mul_canonical rx Z1Z1 HZ1Z1)).
    assert (HS1 : F.canonical S1).
    { unfold S1. apply R.mul_canonical, R.mul_canonical. exact HZ2Z2. }
    assert (HS2 : F.canonical S2).
    { unfold S2. apply R.mul_canonical, R.mul_canonical. exact HZ1Z1. }
    destruct (F.equal U1 U2).
    - destruct (F.equal S1 S2).
      + apply double_canonical. repeat split; assumption.
      + exact identity_canonical.
    - set (H := F.sub U2 U1).
      set (I := F.square (J.twice H)). set (Jc := F.mul H I).
      set (Rr := J.twice (F.sub S2 S1)). set (V := F.mul U1 I).
      set (X3 := F.sub (F.sub (F.square Rr) Jc) (J.twice V)).
      set (Y3 := F.sub (F.mul Rr (F.sub V X3))
        (J.twice (F.mul S1 Jc))).
      set (Z3 := F.mul
        (F.sub (F.sub (F.square (F.add pz rz)) Z1Z1) Z2Z2) H).
      assert (HH : F.canonical H)
        by (unfold H; exact (R.sub_canonical U2 U1 HU2 HU1)).
      assert (HI : F.canonical I)
        by (unfold I; exact (R.square_canonical _ (twice_canonical H HH))).
      assert (HJc : F.canonical Jc)
        by (unfold Jc; exact (R.mul_canonical H I HI)).
      assert (HRr : F.canonical Rr).
      { unfold Rr. apply twice_canonical, R.sub_canonical; assumption. }
      assert (HV : F.canonical V)
        by (unfold V; exact (R.mul_canonical U1 I HI)).
      assert (HX3 : F.canonical X3).
      { unfold X3. apply R.sub_canonical.
        - apply R.sub_canonical; [apply R.square_canonical |]; assumption.
        - now apply twice_canonical. }
      assert (HY3 : F.canonical Y3).
      { unfold Y3. apply R.sub_canonical.
        - apply R.mul_canonical, R.sub_canonical; assumption.
        - apply twice_canonical, R.mul_canonical. exact HJc. }
      assert (HZ3 : F.canonical Z3).
      { unfold Z3. apply R.mul_canonical. exact HH. }
      exact (point_canonical_build X3 Y3 Z3 HX3 HY3 HZ3).
  Qed.

  Lemma add_canonical (p r : J.point) :
    point_canonical p -> point_canonical r ->
    point_canonical (J.add p r).
  Proof.
    intros Hp Hr. rewrite add_as_core.
    destruct (J.is_identity p); [exact Hr |].
    destruct (J.is_identity r); [exact Hp |].
    now apply add_core_canonical.
  Qed.

  Local Ltac rewrite_equal_denote :=
    repeat match goal with
    | |- context [F.equal ?a ?b] =>
        rewrite (equal_denote_eqb a b) by fcanonical
    end.

  Strategy opaque [F.add F.sub F.mul F.square F.denote].

  Local Definition add_unequal_field_output
      (x1 y1 z1 x2 y2 z2 : F.t) : J.point :=
    let z1z1 := F.square z1 in
    let z2z2 := F.square z2 in
    let u1 := F.mul x1 z2z2 in
    let u2 := F.mul x2 z1z1 in
    let s1 := F.mul y1 (F.mul z2 z2z2) in
    let s2 := F.mul y2 (F.mul z1 z1z1) in
    let h := F.sub u2 u1 in
    let i := F.square (J.twice h) in
    let jc := F.mul h i in
    let rr := J.twice (F.sub s2 s1) in
    let v := F.mul u1 i in
    let x3 := F.sub (F.sub (F.square rr) jc) (J.twice v) in
    let y3 := F.sub (F.mul rr (F.sub v x3))
      (J.twice (F.mul s1 jc)) in
    let z3 := F.mul
      (F.sub (F.sub (F.square (F.add z1 z2)) z1z1) z2z2) h in
    {| J.x := x3; J.y := y3; J.z := z3 |}.

  Local Definition add_unequal_z_output
      (x1 y1 z1 x2 y2 z2 : Z) : jpoint :=
    let z1z1 := BinOp.mul z1 z1 in
    let z2z2 := BinOp.mul z2 z2 in
    let u1 := BinOp.mul x1 z2z2 in
    let u2 := BinOp.mul x2 z1z1 in
    let s1 := BinOp.mul y1 (BinOp.mul z2 z2z2) in
    let s2 := BinOp.mul y2 (BinOp.mul z1 z1z1) in
    let h := BinOp.sub u2 u1 in
    let i := BinOp.mul (ztwice h) (ztwice h) in
    let jc := BinOp.mul h i in
    let rr := ztwice (BinOp.sub s2 s1) in
    let v := BinOp.mul u1 i in
    let x3 := BinOp.sub (BinOp.sub (BinOp.mul rr rr) jc) (ztwice v) in
    let y3 := BinOp.sub (BinOp.mul rr (BinOp.sub v x3))
      (ztwice (BinOp.mul s1 jc)) in
    let z3 := BinOp.mul
      (BinOp.sub (BinOp.sub
        (BinOp.mul (BinOp.add z1 z2) (BinOp.add z1 z2)) z1z1) z2z2) h in
    (x3, y3, z3).

  Local Lemma add_denote_as_binop (a b : F.t) :
    F.canonical a -> F.canonical b ->
    F.denote (F.add a b) = BinOp.add (F.denote a) (F.denote b).
  Proof. exact (R.add_denote a b). Qed.

  Local Lemma sub_denote_as_binop (a b : F.t) :
    F.canonical a -> F.canonical b ->
    F.denote (F.sub a b) = BinOp.sub (F.denote a) (F.denote b).
  Proof. exact (R.sub_denote a b). Qed.

  Local Lemma mul_denote_as_binop (a b : F.t) :
    F.canonical b ->
    F.denote (F.mul a b) = BinOp.mul (F.denote a) (F.denote b).
  Proof. exact (R.mul_denote a b). Qed.

  Local Lemma square_denote_as_binop (a : F.t) :
    F.canonical a ->
    F.denote (F.square a) = BinOp.mul (F.denote a) (F.denote a).
  Proof. exact (R.square_denote a). Qed.

  Local Ltac fdenote_as_binop :=
    repeat first
      [ rewrite twice_denote by fcanonical
      | rewrite square_denote_as_binop by fcanonical
      | rewrite add_denote_as_binop by fcanonical
      | rewrite sub_denote_as_binop by fcanonical
      | rewrite mul_denote_as_binop by fcanonical ].

  Local Lemma add_unequal_output_denote
      (x1 y1 z1 x2 y2 z2 : F.t) (X1 Y1 Z1 X2 Y2 Z2 : Z) :
    F.canonical x1 -> F.canonical y1 -> F.canonical z1 ->
    F.canonical x2 -> F.canonical y2 -> F.canonical z2 ->
    F.denote x1 = X1 -> F.denote y1 = Y1 -> F.denote z1 = Z1 ->
    F.denote x2 = X2 -> F.denote y2 = Y2 -> F.denote z2 = Z2 ->
    coordinates (add_unequal_field_output x1 y1 z1 x2 y2 z2) =
      add_unequal_z_output X1 Y1 Z1 X2 Y2 Z2.
  Proof.
    intros Hx1 Hy1 Hz1 Hx2 Hy2 Hz2
      Hx1d Hy1d Hz1d Hx2d Hy2d Hz2d.
    unfold add_unequal_field_output, add_unequal_z_output, coordinates.
    cbn [J.x J.y J.z].
    fdenote_as_binop.
    now rewrite Hx1d, Hy1d, Hz1d, Hx2d, Hy2d, Hz2d.
  Qed.

  Lemma add_coordinates (p r : J.point) :
    point_canonical p -> point_canonical r ->
    coordinates (J.add p r) = jadd_exec (coordinates p) (coordinates r).
  Proof.
    destruct p as [px py pz], r as [rx ry rz].
    intros Hp Hr.
    destruct Hp as (Hpx & Hpy & Hpz), Hr as (Hrx & Hry & Hrz).
    unfold J.add, J.add_core, jadd_exec, coordinates.
    rewrite (is_identity_denote
      {| J.x := px; J.y := py; J.z := pz |} Hpz).
    rewrite (is_identity_denote
      {| J.x := rx; J.y := ry; J.z := rz |} Hrz).
    cbn [J.x J.y J.z].
    destruct (Z.eqb (F.denote pz) 0); [reflexivity |].
    destruct (Z.eqb (F.denote rz) 0); [reflexivity |].
    cbv beta iota zeta.
    rewrite_equal_denote. fdenote.
    fold (@BinOp.add q Primes.PallasQIsPrime).
    fold (@BinOp.sub q Primes.PallasQIsPrime).
    fold (@BinOp.mul q Primes.PallasQIsPrime).
    destruct (Z.eqb
      (BinOp.mul (F.denote px)
        (BinOp.mul (F.denote rz) (F.denote rz)))
      (BinOp.mul (F.denote rx)
        (BinOp.mul (F.denote pz) (F.denote pz)))) eqn:HU.
    - unfold BinOp.mul in HU. rewrite HU.
      destruct (Z.eqb
        (BinOp.mul (F.denote py)
          (BinOp.mul (F.denote rz)
            (BinOp.mul (F.denote rz) (F.denote rz))))
        (BinOp.mul (F.denote ry)
          (BinOp.mul (F.denote pz)
            (BinOp.mul (F.denote pz) (F.denote pz))))) eqn:HS.
      + unfold BinOp.mul in HS. rewrite HS.
        apply double_coordinates. repeat split; assumption.
      + unfold BinOp.mul in HS. rewrite HS.
        cbn [fst snd ztwice zthrice zeight_times]. reflexivity.
    - unfold BinOp.mul in HU. rewrite HU.
      change
        (coordinates (add_unequal_field_output px py pz rx ry rz) =
          add_unequal_z_output
            (F.denote px) (F.denote py) (F.denote pz)
            (F.denote rx) (F.denote ry) (F.denote rz)).
      apply add_unequal_output_denote;
        first [assumption | reflexivity].
  Qed.

  Strategy transparent [F.add F.sub F.mul F.square F.denote].

  (** The unequal-point formula used by fiat-crypto.  Keeping this small
      projection explicit makes the factor-of-two rescaling in [jadd_exec]
      visible to the final algebraic proof. *)
  Definition jadd_inequal_impl (K L : jpoint) : jpoint :=
    let '(X1, Y1, Z1) := K in
    let '(X2, Y2, Z2) := L in
    let Z1Z1 := BinOp.mul Z1 Z1 in
    let U2 := BinOp.mul X2 Z1Z1 in
    let Z2Z2 := BinOp.mul Z2 Z2 in
    let U1 := BinOp.mul X1 Z2Z2 in
    let H := BinOp.sub U2 U1 in
    let S2 := BinOp.mul (BinOp.mul Z1 Z1Z1) Y2 in
    let S1 := BinOp.mul (BinOp.mul Z2 Z2Z2) Y1 in
    let Rr := BinOp.sub S2 S1 in
    let HSqr := BinOp.mul H H in
    let HCub := BinOp.mul HSqr H in
    let U1HSqr := BinOp.mul U1 HSqr in
    let X3 := BinOp.sub
      (BinOp.sub (BinOp.sub (BinOp.mul Rr Rr) HCub) U1HSqr)
      U1HSqr in
    let Y3 := BinOp.sub (BinOp.mul (BinOp.sub U1HSqr X3) Rr)
      (BinOp.mul HCub S1) in
    let Z3 := BinOp.mul (BinOp.mul H Z1) Z2 in
    (X3, Y3, Z3).

  Lemma jadd_neq_fiat_proj (P Q : fpt) (Hneq : ~ Jacobian.eq P Q) :
    proj1_sig (jadd_neq_fiat P Q Hneq) =
      jadd_inequal_impl (proj1_sig P) (proj1_sig Q).
  Proof.
    destruct P as [[[X1 Y1] Z1] HP], Q as [[[X2 Y2] Z2] HQ].
    reflexivity.
  Qed.

  Lemma jrepr_inequal_impl (K L : jpoint) (P Q : Vesta.point) :
    Vesta.on_curve P -> Vesta.on_curve Q ->
    jrepr K P -> jrepr L Q ->
    (let '(_, _, Z1) := K in ~ eqm q Z1 0) ->
    (let '(_, _, Z2) := L in ~ eqm q Z2 0) ->
    (let '(X1, Y1, Z1) := K in
     let '(X2, Y2, Z2) := L in
     ~ (eqm q (BinOp.mul X1 (BinOp.mul Z2 Z2))
          (BinOp.mul X2 (BinOp.mul Z1 Z1)) /\
        eqm q (BinOp.mul Y1 (BinOp.mul Z2 (BinOp.mul Z2 Z2)))
          (BinOp.mul Y2 (BinOp.mul Z1 (BinOp.mul Z1 Z1))))) ->
    jrepr (jadd_inequal_impl K L) (Vesta.add P Q).
  Proof.
    destruct K as [[X1 Y1] Z1], L as [[X2 Y2] Z2].
    intros HonP HonQ HreprP HreprQ HZ1 HZ2 Hneqcross.
    pose (JP := fpt_of X1 Y1 Z1 P HonP HreprP).
    pose (JQ := fpt_of X2 Y2 Z2 Q HonQ HreprQ).
    assert (Hneq : ~ Jacobian.eq JP JQ).
    { intro Heq. unfold JP, JQ in Heq.
      unfold Jacobian.eq in Heq.
      rewrite !fpt_of_proj in Heq. cbn [fst snd] in Heq.
      destruct (dec (eqm q Z1 0)) as [Hbad | _]; [contradiction |].
      destruct Heq as [_ [HU HS]]. apply Hneqcross. split.
      - exact HU.
      - transitivity (Y1 *F (Z2 *F Z2 *F Z2)); [eqm_ring |].
        transitivity (Y2 *F (Z1 *F Z1 *F Z1)); [exact HS | eqm_ring]. }
    assert (HisoP : ~ Jacobian.iszero JP).
    { unfold JP, Jacobian.iszero. cbn [fpt_of]. exact HZ1. }
    assert (HisoQ : ~ Jacobian.iszero JQ).
    { unfold JQ, Jacobian.iszero. cbn [fpt_of]. exact HZ2. }
    pose proof (jrepr_add_neq_fiat JP JQ P Q
      (jcorr X1 Y1 Z1 P HonP HreprP)
      (jcorr X2 Y2 Z2 Q HonQ HreprQ)
      Hneq HisoP HisoQ) as Hout.
    rewrite jadd_neq_fiat_proj in Hout.
    unfold JP, JQ in Hout. rewrite !fpt_of_proj in Hout.
    exact Hout.
  Qed.

  Definition jcanonical (K : jpoint) : Prop :=
    let '(X, Y, Zc) := K in
    UnOp.from X = X /\ UnOp.from Y = Y /\ UnOp.from Zc = Zc.

  Lemma coordinates_jcanonical (p : J.point) : jcanonical (coordinates p).
  Proof.
    destruct p as [px py pz]. cbn [jcanonical coordinates].
    repeat split; apply denote_reduced.
  Qed.

  Lemma eqm_of_eq (u v : Z) : u = v -> eqm q u v.
  Proof. intros ->. reflexivity. Qed.

  Lemma not_eqm_of_reduced_neq (u v : Z) :
    UnOp.from u = u -> UnOp.from v = v -> u <> v -> ~ eqm q u v.
  Proof.
    intros Hu Hv Hneq Heqm. apply Hneq.
    exact (proj1 (eqm_red_eq u v Hu Hv) Heqm).
  Qed.

  Lemma zero_reduced : UnOp.from 0 = 0.
  Proof. unfold UnOp.from. apply Z.mod_0_l, q_pos. Qed.

  Lemma jrepr_exact_zero (K : jpoint) (P : Vesta.point) :
    jrepr K P ->
    (let '(_, _, Zc) := K in Zc = 0) -> P = Vesta.identity.
  Proof.
    destruct K as [[X Y] Zc]. intros Hrepr Hz. subst Zc.
    destruct P as [|px py]; [reflexivity |].
    cbn [jrepr] in Hrepr. destruct Hrepr as (Hnz & _ & _).
    exfalso. apply Hnz. reflexivity.
  Qed.

  Lemma jrepr_cross_equal (K L : jpoint) (P Q : Vesta.point) :
    Vesta.reduced P -> Vesta.reduced Q ->
    Vesta.on_curve P -> Vesta.on_curve Q ->
    jrepr K P -> jrepr L Q ->
    (let '(_, _, Z1) := K in ~ eqm q Z1 0) ->
    (let '(_, _, Z2) := L in ~ eqm q Z2 0) ->
    (let '(X1, Y1, Z1) := K in
     let '(X2, Y2, Z2) := L in
     eqm q (BinOp.mul X1 (BinOp.mul Z2 Z2))
       (BinOp.mul X2 (BinOp.mul Z1 Z1)) /\
     eqm q (BinOp.mul Y1 (BinOp.mul Z2 (BinOp.mul Z2 Z2)))
       (BinOp.mul Y2 (BinOp.mul Z1 (BinOp.mul Z1 Z1)))) ->
    P = Q.
  Proof.
    destruct K as [[X1 Y1] Z1], L as [[X2 Y2] Z2].
    intros HredP HredQ HonP HonQ HreprP HreprQ HZ1 HZ2 (HU & HS).
    pose (JP := fpt_of X1 Y1 Z1 P HonP HreprP).
    pose (JQ := fpt_of X2 Y2 Z2 Q HonQ HreprQ).
    assert (Heq : Jacobian.eq JP JQ).
    { unfold JP, JQ, Jacobian.eq. rewrite !fpt_of_proj.
      cbn [fst snd].
      destruct (dec (eqm q Z1 0)) as [Hbad | _]; [contradiction |].
      repeat split; try assumption.
      transitivity (Y1 *F (Z2 *F (Z2 *F Z2))); [eqm_ring |].
      transitivity (Y2 *F (Z1 *F (Z1 *F Z1))); [exact HS | eqm_ring]. }
    pose proof (proj1 (Jacobian.eq_iff JP JQ) Heq) as HW.
    exact (Weierstrass.corresponds_inj Vesta.a Vesta.b P Q
      (jto_affine JP) (jto_affine JQ) HredP HredQ
      (jcorr X1 Y1 Z1 P HonP HreprP)
      (jcorr X2 Y2 Z2 Q HonQ HreprQ) HW).
  Qed.

  (** Scaling every projective coordinate by [(2^2, 2^3, 2)] preserves
      the represented affine point.  This is the exact relationship between
      Garden's add-2007-bl output and fiat-crypto's unequal-point formula. *)
  Definition trip_eqm_scale2 (K L : jpoint) : Prop :=
    let '(X, Y, Zc) := K in
    let '(X', Y', Zc') := L in
    eqm q X (ztwice (ztwice X')) /\
    eqm q Y (zeight_times Y') /\
    eqm q Zc (ztwice Zc').

  Lemma ztwice_nz (u : Z) :
    ~ eqm q u 0 -> ~ eqm q (ztwice u) 0.
  Proof.
    intros Hu Htwice.
    assert (Htwo : ~ eqm q 2 0).
    { unfold eqm. rewrite Z.mod_small by (pose proof three_lt_q; lia).
      rewrite Z.mod_0_l by exact q_pos. discriminate. }
    apply (nz_mul 2 u Htwo Hu).
    transitivity (ztwice u); [unfold ztwice; eqm_ring | exact Htwice].
  Qed.

  Lemma jrepr_trip_eqm_scale2 (K L : jpoint) (P : Vesta.point) :
    trip_eqm_scale2 K L -> jrepr L P -> jrepr K P.
  Proof.
    destruct K as [[X Y] Zc], L as [[X' Y'] Zc'].
    cbn [trip_eqm_scale2 jrepr].
    intros (HX & HY & HZ) HL.
    destruct P as [|px py].
    - transitivity (ztwice Zc'); [exact HZ |].
      unfold ztwice. setoid_rewrite HL. eqm_ring.
    - destruct HL as (Hnz & HXL & HYL). split.
      + intro Hzero. apply (ztwice_nz Zc' Hnz).
        transitivity Zc; [symmetry; exact HZ | exact Hzero].
      + split.
        * transitivity (ztwice (ztwice X')); [exact HX |].
          unfold ztwice. setoid_rewrite HXL. setoid_rewrite HZ.
          eqm_ring.
        * transitivity (zeight_times Y'); [exact HY |].
          unfold zeight_times, ztwice.
          setoid_rewrite HYL. setoid_rewrite HZ. eqm_ring.
  Qed.

  Lemma jadd_exec_inequal_agrees (K L : jpoint) :
    let '(X1, Y1, Z1) := K in
    let '(X2, Y2, Z2) := L in
    Z.eqb Z1 0 = false -> Z.eqb Z2 0 = false ->
    Z.eqb (BinOp.mul X1 (BinOp.mul Z2 Z2))
      (BinOp.mul X2 (BinOp.mul Z1 Z1)) = false ->
    trip_eqm_scale2 (jadd_exec K L) (jadd_inequal_impl K L).
  Proof.
    destruct K as [[X1 Y1] Z1], L as [[X2 Y2] Z2].
    intros HZ1 HZ2 HU.
    cbv beta iota zeta delta
      [jadd_exec jadd_inequal_impl ztwice zeight_times].
    rewrite HZ1, HZ2, HU.
    unfold trip_eqm_scale2. cbn [fst snd].
    repeat split; eqm_ring.
  Qed.

  Lemma jadd_inequal_z_zero (K L : jpoint) :
    let '(X1, _, Z1) := K in
    let '(X2, _, Z2) := L in
    BinOp.mul X1 (BinOp.mul Z2 Z2) =
      BinOp.mul X2 (BinOp.mul Z1 Z1) ->
    eqm q (snd (jadd_inequal_impl K L)) 0.
  Proof.
    destruct K as [[X1 Y1] Z1], L as [[X2 Y2] Z2]. intro HU.
    cbv beta iota zeta delta [jadd_inequal_impl].
    rewrite HU. eqm_ring.
  Qed.

  Lemma jadd_exec_sound (K L : jpoint) (P Q : Vesta.point) :
    jcanonical K -> jcanonical L ->
    Vesta.reduced P -> Vesta.reduced Q ->
    Vesta.on_curve P -> Vesta.on_curve Q ->
    jrepr K P -> jrepr L Q ->
    jrepr (jadd_exec K L) (Vesta.add P Q).
  Proof.
    destruct K as [[X1 Y1] Z1], L as [[X2 Y2] Z2].
    intros (HX1 & HY1 & HZ1red) (HX2 & HY2 & HZ2red)
      HredP HredQ HonP HonQ HreprP HreprQ.
    destruct (Z.eqb Z1 0) eqn:HZ1.
    - apply Z.eqb_eq in HZ1.
      pose proof (jrepr_exact_zero (X1, Y1, Z1) P HreprP HZ1) as HP.
      subst P. cbn [Vesta.add Weierstrass.add jadd_exec].
      rewrite HZ1. exact HreprQ.
    - destruct (Z.eqb Z2 0) eqn:HZ2.
      + apply Z.eqb_eq in HZ2.
        pose proof (jrepr_exact_zero (X2, Y2, Z2) Q HreprQ HZ2) as HQ.
        subst Q.
        assert (Hadd : Vesta.add P Vesta.identity = P).
        { destruct P; reflexivity. }
        rewrite Hadd. cbn [jadd_exec].
        rewrite HZ1, HZ2. cbn. exact HreprP.
      + assert (HZ1neq : Z1 <> 0) by now apply Z.eqb_neq in HZ1.
        assert (HZ2neq : Z2 <> 0) by now apply Z.eqb_neq in HZ2.
        assert (HZ1eqm : ~ eqm q Z1 0).
        { apply not_eqm_of_reduced_neq;
            [exact HZ1red | exact zero_reduced | exact HZ1neq]. }
        assert (HZ2eqm : ~ eqm q Z2 0).
        { apply not_eqm_of_reduced_neq;
            [exact HZ2red | exact zero_reduced | exact HZ2neq]. }
        set (U1 := BinOp.mul X1 (BinOp.mul Z2 Z2)).
        set (U2 := BinOp.mul X2 (BinOp.mul Z1 Z1)).
        set (S1 := BinOp.mul Y1 (BinOp.mul Z2 (BinOp.mul Z2 Z2))).
        set (S2 := BinOp.mul Y2 (BinOp.mul Z1 (BinOp.mul Z1 Z1))).
        destruct (Z.eqb U1 U2) eqn:HU.
        * apply Z.eqb_eq in HU.
          destruct (Z.eqb S1 S2) eqn:HS.
          -- apply Z.eqb_eq in HS.
             assert (HPQ : P = Q).
             { eapply jrepr_cross_equal;
                 [exact HredP | exact HredQ | exact HonP | exact HonQ
                 | exact HreprP | exact HreprQ | exact HZ1eqm | exact HZ2eqm |].
               unfold U1, U2, S1, S2 in HU, HS.
               split; apply eqm_of_eq; assumption. }
             subst Q.
             cbn [jadd_exec]. rewrite HZ1, HZ2.
             fold U1 U2 S1 S2. rewrite (proj2 (Z.eqb_eq U1 U2) HU).
             rewrite (proj2 (Z.eqb_eq S1 S2) HS).
             apply jdouble_exec_sound; assumption.
          -- assert (HSneq : S1 <> S2) by now apply Z.eqb_neq in HS.
             assert (Hneqcross : ~ (eqm q U1 U2 /\ eqm q S1 S2)).
             { intros (_ & HSe). apply HSneq.
               apply (proj1 (eqm_red_eq S1 S2 (from_bin_mul _ _)
                 (from_bin_mul _ _))). exact HSe. }
             pose proof (jrepr_inequal_impl (X1, Y1, Z1) (X2, Y2, Z2)
               P Q HonP HonQ HreprP HreprQ HZ1eqm HZ2eqm Hneqcross) as Hgen.
             assert (Hzero :
               eqm q (snd (jadd_inequal_impl
                 (X1, Y1, Z1) (X2, Y2, Z2))) 0).
             { apply (jadd_inequal_z_zero
                 (X1, Y1, Z1) (X2, Y2, Z2)).
               unfold U1, U2 in HU. exact HU. }
             assert (Hsum : Vesta.add P Q = Vesta.identity).
             { destruct (Vesta.add P Q) as [|sx sy] eqn:Hadd;
                 [reflexivity |].
               cbn [jrepr] in Hgen.
               destruct Hgen as (Hnz & _ & _). contradiction. }
             rewrite Hsum.
             cbn [jadd_exec]. rewrite HZ1, HZ2.
             fold U1 U2 S1 S2. rewrite (proj2 (Z.eqb_eq U1 U2) HU), HS.
             exact jrepr_zero.
        * assert (HUneq : U1 <> U2) by now apply Z.eqb_neq in HU.
          assert (Hneqcross : ~ (eqm q U1 U2 /\ eqm q S1 S2)).
          { intros (HUe & _). apply HUneq.
            apply (proj1 (eqm_red_eq U1 U2 (from_bin_mul _ _)
              (from_bin_mul _ _))). exact HUe. }
          pose proof (jrepr_inequal_impl (X1, Y1, Z1) (X2, Y2, Z2)
            P Q HonP HonQ HreprP HreprQ HZ1eqm HZ2eqm Hneqcross) as Hgen.
          apply (jrepr_trip_eqm_scale2
            (jadd_exec (X1, Y1, Z1) (X2, Y2, Z2))
            (jadd_inequal_impl (X1, Y1, Z1) (X2, Y2, Z2))
            (Vesta.add P Q)).
          -- apply (jadd_exec_inequal_agrees
               (X1, Y1, Z1) (X2, Y2, Z2)).
             exact HZ1. exact HZ2.
             unfold U1, U2 in HU. exact HU.
          -- exact Hgen.
  Qed.

  Lemma add_represents (p r : J.point) (P Q : Vesta.point) :
    represents p P -> represents r Q ->
    represents (J.add p r) (Vesta.add P Q).
  Proof.
    intros (HcanP & HredP & HonP & HreprP)
      (HcanQ & HredQ & HonQ & HreprQ).
    split; [now apply add_canonical |].
    split.
    - exact (Weierstrass.add_reduced Vesta.a P Q HredP HredQ).
    - split.
      + exact (Weierstrass.add_on_curve Vesta.a Vesta.b P Q three_lt_q HonP HonQ).
      + rewrite add_coordinates by assumption.
        eapply jadd_exec_sound;
          try apply coordinates_jcanonical; assumption.
  Qed.

  (** ** Inversion-free equality checks *)

  Strategy opaque [F.add F.sub F.mul F.square F.denote].

  Lemma equal_affine_true (p : J.point) (r : J.affine) (P : Vesta.point) :
    represents p P -> affine_canonical r ->
    J.equal_affine p r = true -> P = affine_denote r.
  Proof.
    destruct p as [px py pz], r as [rx ry].
    intros (Hcan & Hred & Hon & Hrepr) (Hrx & Hry) Hcheck.
    destruct Hcan as (Hpx & Hpy & Hpz).
    unfold J.equal_affine in Hcheck.
    rewrite (is_identity_denote
      {| J.x := px; J.y := py; J.z := pz |} Hpz) in Hcheck.
    cbn [J.x J.y J.z] in Hcheck.
    destruct (Z.eqb (F.denote pz) 0) eqn:HZ; [discriminate |].
    apply andb_prop in Hcheck as [HX HY].
    apply (proj1 (R.equal_denote_iff
      px (F.mul rx (F.square pz)) Hpx ltac:(fcanonical))) in HX.
    apply (proj1 (R.equal_denote_iff
      py (F.mul ry (F.mul pz (F.square pz)))
      Hpy ltac:(fcanonical))) in HY.
    assert (HZeqm : ~ eqm q (F.denote pz) 0).
    { apply not_eqm_of_reduced_neq; [apply denote_reduced | exact zero_reduced |].
      now apply Z.eqb_neq in HZ. }
    assert (Hpin : jrepr (coordinates {| J.x := px; J.y := py; J.z := pz |})
      (affine_denote {| J.affine_x := rx; J.affine_y := ry |})).
    { cbn [coordinates affine_denote Vesta.affine jrepr
        J.x J.y J.z J.affine_x J.affine_y].
      split; [exact HZeqm | split].
      - rewrite HX.
        rewrite R.mul_denote by fcanonical.
        rewrite R.square_denote by fcanonical.
        eqm_ring.
      - rewrite HY.
        rewrite !R.mul_denote by fcanonical.
        rewrite R.square_denote by fcanonical.
        eqm_ring. }
    exact (jrepr_inj (coordinates {| J.x := px; J.y := py; J.z := pz |})
      P (affine_denote {| J.affine_x := rx; J.affine_y := ry |})
      Hred (Vesta.affine_reduced _ _) Hrepr Hpin).
  Qed.

  Lemma equal_true (p r : J.point) (P Q : Vesta.point) :
    represents p P -> represents r Q -> J.equal p r = true -> P = Q.
  Proof.
    destruct p as [px py pz], r as [rx ry rz].
    intros (HcanP & HredP & HonP & HreprP)
      (HcanQ & HredQ & HonQ & HreprQ) Hcheck.
    destruct HcanP as (Hpx & Hpy & Hpz), HcanQ as (Hrx & Hry & Hrz).
    unfold J.equal in Hcheck.
    rewrite (is_identity_denote
      {| J.x := px; J.y := py; J.z := pz |} Hpz) in Hcheck.
    rewrite (is_identity_denote
      {| J.x := rx; J.y := ry; J.z := rz |} Hrz) in Hcheck.
    cbn [J.x J.y J.z] in Hcheck.
    destruct (Z.eqb (F.denote pz) 0) eqn:HZP.
    - destruct (Z.eqb (F.denote rz) 0) eqn:HZQ; [|discriminate].
      apply Z.eqb_eq in HZP, HZQ.
      pose proof (jrepr_exact_zero (coordinates
        {| J.x := px; J.y := py; J.z := pz |}) P HreprP HZP) as HP.
      pose proof (jrepr_exact_zero (coordinates
        {| J.x := rx; J.y := ry; J.z := rz |}) Q HreprQ HZQ) as HQ.
      congruence.
    - destruct (Z.eqb (F.denote rz) 0) eqn:HZQ; [discriminate |].
      apply andb_prop in Hcheck as [HX HY].
      apply (proj1 (R.equal_denote_iff
        (F.mul px (F.square rz)) (F.mul rx (F.square pz))
        ltac:(fcanonical) ltac:(fcanonical))) in HX.
      apply (proj1 (R.equal_denote_iff
        (F.mul py (F.mul rz (F.square rz)))
        (F.mul ry (F.mul pz (F.square pz)))
        ltac:(fcanonical) ltac:(fcanonical))) in HY.
      rewrite !R.mul_denote in HX by fcanonical.
      rewrite !R.square_denote in HX by fcanonical.
      rewrite !R.mul_denote in HY by fcanonical.
      rewrite !R.square_denote in HY by fcanonical.
      assert (HZPeqm : ~ eqm q (F.denote pz) 0).
      { apply not_eqm_of_reduced_neq;
          [apply denote_reduced | exact zero_reduced | now apply Z.eqb_neq in HZP]. }
      assert (HZQeqm : ~ eqm q (F.denote rz) 0).
      { apply not_eqm_of_reduced_neq;
          [apply denote_reduced | exact zero_reduced | now apply Z.eqb_neq in HZQ]. }
      eapply jrepr_cross_equal;
        [exact HredP | exact HredQ | exact HonP | exact HonQ
        | exact HreprP | exact HreprQ | exact HZPeqm | exact HZQeqm |].
      cbn [coordinates J.x J.y J.z].
      split.
      + apply eqm_of_eq. exact HX.
      + apply eqm_of_eq. exact HY.
  Qed.

  Strategy transparent [F.add F.sub F.mul F.square F.denote].

End VkJacobianRefinement.
