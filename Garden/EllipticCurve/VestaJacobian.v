(** * Jacobian coordinates for Vesta

    An inversion-free addition layer for the Vesta curve [y^2 = x^3 + 5] over
    [F_{pallas_q}].  A Jacobian triple [(X, Y, Z)] with [Z <> 0] represents the
    affine point [(X/Z^2, Y/Z^3)]; [Z = 0] is the point at infinity.  The
    computed addition [jadd] is built from [BinOp.add] / [BinOp.sub] /
    [BinOp.mul] only: it contains no [BinOp.div] and no [mod_inverse], so a fold
    of [jadd] over a bucket accumulation never runs the extended-Euclid loop
    that the affine [Weierstrass.add] pays on every point addition.  Division by
    two in the standard formula is multiplication by the literal [two_inv].

    Correctness is transported from fiat-crypto's Jacobian group law: [jadd]
    agrees, modulo [pallas_q], with [Jacobian.add] at the instantiation
    [F := Z], [Feq := eqm pallas_q], and [Jacobian.to_affine_add] maps that sum
    onto the fiat affine sum, which [Weierstrass.add_corresponds] identifies
    with Garden's [Vesta.add].  The only characteristic hypothesis of the whole
    layer is [3 < pallas_q].

    Checking a Jacobian accumulator against a pinned affine point stays
    inversion-free as well: [jcheck] verifies [Z <> 0], [X = x * Z^2] and
    [Y = y * Z^3] with four multiplications instead of normalising.

    [jadd_fast] is [jadd] with each field operation evaluated by the Solinas
    reduction of [Field.PastaFast] instead of [Z.modulo].  It is proved equal
    to [jadd] on triples whose coordinates lie in [[0, pallas_q)], a condition
    [jadd] itself maintains, so it is an evaluation strategy and not a second
    addition: the group law above is stated and proved once, for [jadd]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Setoids.Setoid.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.PastaFast.
Require Import Garden.EllipticCurve.FiatField.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.VestaOrder.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module VestaJac.
  Local Notation q := Primes.pallas_q.

  Lemma q_pos : q <> 0.
  Proof. pose proof VestaOrder.eleven_lt_q. lia. Qed.

  Lemma three_lt_q : 3 < q.
  Proof. pose proof VestaOrder.eleven_lt_q. lia. Qed.

  (** ** Setoid infrastructure for [eqm pallas_q]

      [FiatField] declares these morphisms [Local], so the ring normalisation
      used below re-declares them.  [eqm_ring] needs the raw [Z.add] / [Z.mul] /
      [Z.opp] / [Z.sub] morphisms as well as the [BinOp] ones. *)

  Local Instance eqm_equiv : Equivalence (eqm q).
  Proof. unfold eqm. constructor; congruence. Qed.
  Local Instance add_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.add := Zplus_eqm q.
  Local Instance mul_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.mul := Zmult_eqm q.
  Local Instance opp_eqm_mor : Proper (eqm q ==> eqm q) Z.opp := Zopp_eqm q.
  Local Instance sub_eqm_mor : Proper (eqm q ==> eqm q ==> eqm q) Z.sub := Zminus_eqm q.

  Local Instance add_Proper : Proper (eqm q ==> eqm q ==> eqm q) BinOp.add.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.add.
    repeat setoid_rewrite (Zmod_eqm q). exact (Zplus_eqm q x x' Hx y y' Hy).
  Qed.
  Local Instance sub_Proper : Proper (eqm q ==> eqm q ==> eqm q) BinOp.sub.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.sub.
    repeat setoid_rewrite (Zmod_eqm q). exact (Zminus_eqm q x x' Hx y y' Hy).
  Qed.
  Local Instance mul_Proper : Proper (eqm q ==> eqm q ==> eqm q) BinOp.mul.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.mul.
    repeat setoid_rewrite (Zmod_eqm q). exact (Zmult_eqm q x x' Hx y y' Hy).
  Qed.
  Local Instance opp_Proper : Proper (eqm q ==> eqm q) UnOp.opp.
  Proof.
    intros x x' Hx. unfold UnOp.opp.
    repeat setoid_rewrite (Zmod_eqm q). exact (Zopp_eqm q x x' Hx).
  Qed.

  (* A pure ring identity between two field expressions is an [eqm q] equality:
     each [BinOp.div] is frozen as an atom, the internal [mod q] are normalised
     away, and [ring] discharges the polynomial. *)
  Local Ltac eqm_ring :=
    repeat match goal with
           | |- context[BinOp.div ?n ?d] => set (BinOp.div n d) in *
           end;
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    repeat setoid_rewrite (Zmod_eqm q);
    unfold eqm; f_equal; ring.

  (** ** Reduction and nonzeroness helpers *)

  Lemma from_eqm (u : Z) : eqm q (UnOp.from u) u.
  Proof. unfold eqm, UnOp.from. apply Z.mod_mod, q_pos. Qed.

  Lemma from_bin_add (u v : Z) : UnOp.from (BinOp.add u v) = BinOp.add u v.
  Proof. unfold UnOp.from, BinOp.add. apply Zmod_mod. Qed.
  Lemma from_bin_mul (u v : Z) : UnOp.from (BinOp.mul u v) = BinOp.mul u v.
  Proof. unfold UnOp.from, BinOp.mul. apply Zmod_mod. Qed.
  Lemma from_bin_sub (u v : Z) : UnOp.from (BinOp.sub u v) = BinOp.sub u v.
  Proof. unfold UnOp.from, BinOp.sub. apply Zmod_mod. Qed.

  Lemma eqm_red_eq (u v : Z) :
    UnOp.from u = u -> UnOp.from v = v -> (eqm q u v <-> u = v).
  Proof. unfold eqm, UnOp.from. intros Hu Hv. split; congruence. Qed.

  Lemma eqm_from_zero (u : Z) : eqm q u 0 <-> UnOp.from u = 0.
  Proof.
    unfold eqm, UnOp.from. rewrite Z.mod_0_l by apply q_pos. reflexivity.
  Qed.

  Lemma nz_from (d : Z) : ~ eqm q d 0 -> UnOp.from d <> 0.
  Proof.
    intros Hd Hc. apply Hd. unfold eqm, UnOp.from in *.
    rewrite Hc, Z.mod_0_l by apply q_pos. reflexivity.
  Qed.

  Lemma nz_mul (u v : Z) : ~ eqm q u 0 -> ~ eqm q v 0 -> ~ eqm q (BinOp.mul u v) 0.
  Proof.
    intros Hu Hv Hc.
    apply (field_from_mul_nonzero u v (nz_from u Hu) (nz_from v Hv)).
    unfold eqm, UnOp.from in *.
    rewrite Z.mod_0_l in Hc by apply q_pos.
    unfold BinOp.mul in *. rewrite Z.mod_mod in Hc by apply q_pos.
    rewrite Z.mod_mod by apply q_pos. exact Hc.
  Qed.

  Lemma eqm_div_of_mul (u v d : Z) :
    ~ eqm q d 0 -> eqm q u (BinOp.mul v d) -> eqm q v (BinOp.div u d).
  Proof.
    intros Hd Hu.
    assert (Hd' : d mod q <> 0) by exact (nz_from d Hd).
    pose proof (div_mul (p := q) u d ltac:(pose proof three_lt_q; lia) Hd') as Hdm.
    assert (Hstep : BinOp.mul (BinOp.div u d) d = BinOp.mul v d).
    { rewrite Hdm. unfold eqm in Hu. unfold BinOp.mul in *.
      rewrite Hu, Z.mod_mod by apply q_pos. reflexivity. }
    symmetry.
    exact (field_mul_cancel_r (BinOp.div u d) v d (nz_from d Hd) Hstep).
  Qed.

  Lemma eqm_mul_of_div (u v d : Z) :
    ~ eqm q d 0 -> eqm q v (BinOp.div u d) -> eqm q u (BinOp.mul v d).
  Proof.
    intros Hd Hv.
    assert (Hd' : d mod q <> 0) by exact (nz_from d Hd).
    pose proof (div_mul (p := q) u d ltac:(pose proof three_lt_q; lia) Hd') as Hdm.
    rewrite Hv, Hdm. unfold eqm. rewrite Z.mod_mod by apply q_pos. reflexivity.
  Qed.

  (** ** The pinned Vesta point predicate

      The same predicate the Vesta MSM layer carries on its accumulators. *)

  Definition good (P : Vesta.point) : Prop := Vesta.reduced P /\ Vesta.on_curve P.

  (** ** Jacobian triples *)

  Definition jpoint : Set := Z * Z * Z.

  (** The point at infinity: any triple with [Z = 0]. *)
  Definition jzero : jpoint := (0, 0, 0).

  (** An affine point sits at [Z = 1]. *)
  Definition jof (P : Vesta.point) : jpoint :=
    match P with
    | Weierstrass.Infinity => (0, 0, 0)
    | Weierstrass.Affine x y => (x, y, 1)
    end.

  (** [(X, Y, Z)] represents [P]: at infinity exactly when [Z = 0], and
      otherwise [X = x Z^2], [Y = y Z^3], all modulo [pallas_q]. *)
  Definition jrepr (J : jpoint) (P : Vesta.point) : Prop :=
    let '(X, Y, Zc) := J in
    match P with
    | Weierstrass.Infinity => eqm q Zc 0
    | Weierstrass.Affine x y =>
        ~ eqm q Zc 0 /\
        eqm q X (BinOp.mul x (BinOp.mul Zc Zc)) /\
        eqm q Y (BinOp.mul y (BinOp.mul (BinOp.mul Zc Zc) Zc))
    end.

  Lemma jrepr_zero : jrepr jzero Vesta.identity.
  Proof. reflexivity. Qed.

  Lemma jrepr_of (P : Vesta.point) : good P -> jrepr (jof P) P.
  Proof.
    intros _. destruct P as [| x y]; cbn [jof jrepr].
    - reflexivity.
    - split; [| split].
      + intro Hc. unfold eqm in Hc.
        rewrite Z.mod_0_l in Hc by apply q_pos.
        rewrite Z.mod_small in Hc by (pose proof three_lt_q; lia). discriminate.
      + eqm_ring.
      + eqm_ring.
  Qed.

  (** A triple represents at most one reduced Vesta point: [Z = 0] pins the
      point at infinity, and otherwise [Z^2] and [Z^3] are invertible, so the
      affine coordinates are determined modulo [pallas_q] — hence on the nose
      for reduced points.  This is what turns a checkpoint on the Jacobian
      accumulator into an equation between affine points. *)
  Lemma jrepr_inj (J : jpoint) (P Q : Vesta.point) :
    Vesta.reduced P -> Vesta.reduced Q -> jrepr J P -> jrepr J Q -> P = Q.
  Proof.
    destruct J as [[X Y] Zc].
    destruct P as [| x1 y1]; destruct Q as [| x2 y2];
      cbn [jrepr Vesta.reduced Weierstrass.reduced].
    - reflexivity.
    - intros _ _ HP (HQ & _ & _). exfalso. exact (HQ HP).
    - intros _ _ (HP & _ & _) HQ. exfalso. exact (HP HQ).
    - intros (Hx1 & Hy1) (Hx2 & Hy2) (Hnz & HX1 & HY1) (_ & HX2 & HY2).
      assert (Hzz : ~ eqm q (BinOp.mul Zc Zc) 0)
        by (apply nz_mul; exact Hnz).
      assert (Hzzz : ~ eqm q (BinOp.mul (BinOp.mul Zc Zc) Zc) 0)
        by (apply nz_mul; [exact Hzz | exact Hnz]).
      assert (Hxe : BinOp.mul x1 (BinOp.mul Zc Zc)
                    = BinOp.mul x2 (BinOp.mul Zc Zc)).
      { apply (eqm_red_eq _ _ (from_bin_mul _ _) (from_bin_mul _ _)).
        transitivity X; [symmetry; exact HX1 | exact HX2]. }
      assert (Hye : BinOp.mul y1 (BinOp.mul (BinOp.mul Zc Zc) Zc)
                    = BinOp.mul y2 (BinOp.mul (BinOp.mul Zc Zc) Zc)).
      { apply (eqm_red_eq _ _ (from_bin_mul _ _) (from_bin_mul _ _)).
        transitivity Y; [symmetry; exact HY1 | exact HY2]. }
      pose proof (field_mul_cancel_r x1 x2 _ (nz_from _ Hzz) Hxe) as Hx.
      pose proof (field_mul_cancel_r y1 y2 _ (nz_from _ Hzzz) Hye) as Hy.
      congruence.
  Qed.

  (** ** The instantiated fiat-crypto Jacobian layer *)

  Local Notation fpt :=
    (@Jacobian.point Z (eqm q) 0 BinOp.add BinOp.mul Vesta.a Vesta.b (@eqm_dec q)).

  Local Notation wpt := (Weierstrass.wpoint (p := q) Vesta.a Vesta.b).

  Definition jadd_fiat (P Q : fpt) : fpt :=
    @Jacobian.add Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
      Finv BinOp.div Vesta.a Vesta.b (@Field_eqm q _) (Weierstrass.c3 three_lt_q)
      (@eqm_dec q) P Q.

  Definition jto_affine (P : fpt) : wpt :=
    @Jacobian.to_affine Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
      Finv BinOp.div Vesta.a Vesta.b (@Field_eqm q _) (@eqm_dec q) P.

  (** fiat-crypto's group law at the Vesta instantiation.  The right-hand side
      is Garden's [Weierstrass.wadd] on the nose, which is what makes
      [Weierstrass.add_corresponds] composable with it. *)
  Definition to_affine_add_vesta :
    forall P Q : fpt,
      @W.eq Z (eqm q) BinOp.add BinOp.mul Vesta.a Vesta.b
        (jto_affine (jadd_fiat P Q))
        (Weierstrass.wadd Vesta.a Vesta.b three_lt_q (jto_affine P) (jto_affine Q))
    :=
    @Jacobian.to_affine_add Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
      Finv BinOp.div Vesta.a Vesta.b (@Field_eqm q _) (Weierstrass.c3 three_lt_q)
      (@eqm_dec q).

  (** A represented triple satisfies the Jacobian curve equation
      [Y^2 = X^3 + a X Z^4 + b Z^6], so it builds a fiat-crypto point.  At
      [Z = 0] the condition is vacuous. *)
  Lemma jrepr_curve_obligation (X Y Zc : Z) (P : Vesta.point) :
    Weierstrass.on_curve Vesta.a Vesta.b P ->
    jrepr (X, Y, Zc) P ->
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
    intros Hoc HJ.
    destruct (dec (eqm q Zc 0)) as [Hz | Hz]; [exact I |].
    destruct P as [| x y]; cbn [jrepr] in HJ.
    { exfalso. exact (Hz HJ). }
    destruct HJ as (_ & HX & HY).
    cbn [Weierstrass.on_curve] in Hoc.
    assert (Hoc' : eqm q (BinOp.mul y y)
                     (BinOp.add (BinOp.add (BinOp.mul (BinOp.mul x x) x)
                                   (BinOp.mul Vesta.a x)) Vesta.b)).
    { unfold UnOp.from in Hoc. exact Hoc. }
    rewrite HX, HY.
    transitivity (BinOp.mul (BinOp.mul y y)
                    (BinOp.mul (BinOp.mul (BinOp.mul Zc Zc) Zc)
                       (BinOp.mul (BinOp.mul Zc Zc) Zc))).
    { eqm_ring. }
    rewrite Hoc'. eqm_ring.
  Qed.

  Definition fpt_of (X Y Zc : Z) (P : Vesta.point)
    (Hoc : Weierstrass.on_curve Vesta.a Vesta.b P) (HJ : jrepr (X, Y, Zc) P)
    : fpt :=
    exist _ (X, Y, Zc) (jrepr_curve_obligation X Y Zc P Hoc HJ).

  Lemma fpt_of_proj (X Y Zc : Z) P Hoc HJ :
    proj1_sig (fpt_of X Y Zc P Hoc HJ) = (X, Y, Zc).
  Proof. reflexivity. Qed.

  (** ** The [corresponds] bridge

      [jto_affine JP] is used as the fiat representative of [P], which keeps the
      whole layer clear of [W.add]'s [Proper] instance (and hence of the
      [char_ge 12] and nonsingularity hypotheses it would require). *)

  Lemma jto_affine_coords (JP : fpt) :
    W.coordinates (jto_affine JP) =
    (let '(X, Y, Zc) := proj1_sig JP in
     if dec (eqm q Zc 0) then inr tt
     else inl (BinOp.div X (BinOp.mul Zc Zc),
               BinOp.div Y (BinOp.mul (BinOp.mul Zc Zc) Zc))).
  Proof. destruct JP as [[[X Y] Zc] pf]. reflexivity. Qed.

  Lemma jcorr (X Y Zc : Z) (P : Vesta.point) Hoc HJ :
    Weierstrass.corresponds Vesta.a Vesta.b P
      (jto_affine (fpt_of X Y Zc P Hoc HJ)).
  Proof.
    destruct P as [| x y].
    - cbn [Weierstrass.corresponds].
      rewrite jto_affine_coords, fpt_of_proj.
      cbn [jrepr] in HJ.
      destruct (dec (eqm q Zc 0)) as [_ | Hbad]; [reflexivity | contradiction].
    - cbn [Weierstrass.corresponds].
      rewrite jto_affine_coords, fpt_of_proj.
      cbn [jrepr] in HJ. destruct HJ as (Hnz & HX & HY).
      destruct (dec (eqm q Zc 0)) as [Hbad | _]; [contradiction |].
      eexists; eexists; split; [reflexivity | split].
      + apply eqm_div_of_mul; [apply nz_mul; assumption | exact HX].
      + apply eqm_div_of_mul;
          [apply nz_mul; [apply nz_mul |]; assumption | exact HY].
  Qed.

  Lemma jrepr_of_corresponds (JP : fpt) (P : Vesta.point) :
    Weierstrass.corresponds Vesta.a Vesta.b P (jto_affine JP) ->
    jrepr (proj1_sig JP) P.
  Proof.
    intros Hc.
    pose proof (jto_affine_coords JP) as Hco.
    destruct JP as [[[X Y] Zc] pf]. cbn [proj1_sig] in *.
    destruct P as [| x y]; cbn [Weierstrass.corresponds] in Hc;
      rewrite Hco in Hc; clear Hco; revert Hc;
      destruct (dec (eqm q Zc 0)) as [Hz | Hz]; intros Hc.
    - exact Hz.
    - discriminate.
    - destruct Hc as (x' & y' & Hbad & _ & _). discriminate.
    - destruct Hc as (x' & y' & Heq & Hx & Hy).
      injection Heq as <- <-.
      cbn [jrepr]. split; [exact Hz | split].
      + apply eqm_mul_of_div; [apply nz_mul; assumption | exact Hx].
      + apply eqm_mul_of_div;
          [apply nz_mul; [apply nz_mul |]; assumption | exact Hy].
  Qed.

  (** ** The computed addition

      Division by two is multiplication by [two_inv]; [div_two] is a syntactic
      equality, because [BinOp.div u (1 +F 1)] is [BinOp.mul u (mod_inverse
      (1 +F 1) pallas_q)] and the inverse of two reduces to the literal. *)

  Definition two_inv : Z :=
    14474011154664524427946373126085988481681528240970823689839871374196681474049.

  Lemma two_inv_spec : BinOp.mul two_inv (BinOp.add 1 1) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma div_two (u : Z) : BinOp.div u (BinOp.add 1 1) = BinOp.mul u two_inv.
  Proof. unfold BinOp.div. f_equal; vm_compute; reflexivity. Qed.

  (** The unified Jacobian addition, specialised to [a = 0] (the [a (Z^2)^2]
      term of the generic slope vanishes) and free of any division. *)
  Definition jadd (J1 J2 : jpoint) : jpoint :=
    let '(x1, y1, z1) := J1 in
    let '(x2, y2, z2) := J2 in
    if UnOp.from z1 =? 0 then J2
    else if UnOp.from z2 =? 0 then J1
    else
      let zz1 := z1 *F z1 in
      let zz2 := z2 *F z2 in
      let u1 := x1 *F zz2 in
      let u2 := x2 *F zz1 in
      let s1 := y1 *F (zz2 *F z2) in
      let s2 := y2 *F (zz1 *F z1) in
      let z := z1 *F z2 in
      let t := u1 +F u2 in
      let ss := s1 +F s2 in
      let e := ss =? 0 in
      let m := if e then u2 -F u1 else ss in
      let c := (-F t) *F (m *F m) in
      let r := if e then s2 -F s1 else (t *F t) -F (u1 *F u2) in
      let x3 := (r *F r) +F c in
      let y3 := (-F ((r *F (((1 +F 1) *F x3) +F c)) +F (m *F ((ss *F ss) *F ss))))
                  *F two_inv in
      let z3 := m *F z in
      if e then (if u1 =? u2 then (0, 0, 0) else (x3, y3, z3)) else (x3, y3, z3).

  (** ** Agreement with the fiat-crypto addition *)

  Definition trip_eqm (J J' : jpoint) : Prop :=
    let '(X, Y, Zc) := J in let '(X', Y', Zc') := J' in
    eqm q X X' /\ eqm q Y Y' /\ eqm q Zc Zc'.

  Lemma jrepr_eqm (J J' : jpoint) (P : Vesta.point) :
    trip_eqm J J' -> jrepr J' P -> jrepr J P.
  Proof.
    destruct J as [[X Y] Zc]; destruct J' as [[X' Y'] Zc'].
    intros (HX & HY & HZ) HJ.
    destruct P as [| x y]; cbn [jrepr] in *.
    - rewrite HZ. exact HJ.
    - destruct HJ as (Hnz & HXr & HYr).
      split; [rewrite HZ; exact Hnz | split].
      + rewrite HX, HZ. exact HXr.
      + rewrite HY, HZ. exact HYr.
  Qed.

  Local Notation jaimpl :=
    (@Jacobian.add_impl Z (eqm q) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
       BinOp.div Vesta.a (@eqm_dec q)).

  Lemma add_proj (P Q : fpt) :
    proj1_sig (jadd_fiat P Q) =
    (if dec (eqm q (snd (proj1_sig P)) 0) then proj1_sig Q
     else if dec (eqm q (snd (proj1_sig Q)) 0) then proj1_sig P
     else jaimpl (proj1_sig P) (proj1_sig Q) false).
  Proof.
    unfold jadd_fiat, Jacobian.add.
    destruct (dec (eqm q (snd (proj1_sig P)) 0)); [reflexivity |].
    destruct (dec (eqm q (snd (proj1_sig Q)) 0)); reflexivity.
  Qed.

  Lemma jadd_agrees_raw (J1 J2 : jpoint) :
    trip_eqm (jadd J1 J2)
      (if dec (eqm q (snd J1) 0) then J2
       else if dec (eqm q (snd J2) 0) then J1
       else jaimpl J1 J2 false).
  Proof.
    destruct J1 as [[x1 y1] z1]. destruct J2 as [[x2 y2] z2].
    cbn [snd fst jadd].
    destruct (Z.eqb_spec (UnOp.from z1) 0) as [E1 | E1];
      destruct (dec (eqm q z1 0)) as [D1 | D1];
      [ | exfalso; apply D1, eqm_from_zero, E1
        | exfalso; apply E1, eqm_from_zero, D1 | ].
    { split; [reflexivity | split; reflexivity]. }
    destruct (Z.eqb_spec (UnOp.from z2) 0) as [E2 | E2];
      destruct (dec (eqm q z2 0)) as [D2 | D2];
      [ | exfalso; apply D2, eqm_from_zero, E2
        | exfalso; apply E2, eqm_from_zero, D2 | ].
    { split; [reflexivity | split; reflexivity]. }
    unfold jaimpl. cbv beta zeta delta [Jacobian.add_impl]. cbn [fst snd].
    set (u1 := x1 *F (z2 *F z2)) in *.
    set (u2 := x2 *F (z1 *F z1)) in *.
    set (s1 := y1 *F (z2 *F z2 *F z2)) in *.
    set (s2 := y2 *F (z1 *F z1 *F z1)) in *.
    set (zz := z1 *F z2) in *.
    set (t := u1 +F u2) in *.
    set (ss := s1 +F s2) in *.
    assert (Hred : UnOp.from ss = ss) by (unfold ss; apply from_bin_add).
    destruct (Z.eqb_spec ss 0) as [Hss | Hss];
      destruct (dec (eqm q ss 0)) as [Dss | Dss];
      [ | exfalso; apply Dss, eqm_from_zero; rewrite Hred; exact Hss
        | exfalso; apply Hss; rewrite <- Hred; apply eqm_from_zero, Dss | ].
    - assert (Hu1 : UnOp.from u1 = u1) by (unfold u1; apply from_bin_mul).
      assert (Hu2 : UnOp.from u2 = u2) by (unfold u2; apply from_bin_mul).
      destruct (Z.eqb_spec u1 u2) as [Hu | Hu];
        destruct (dec (eqm q u1 u2)) as [Du | Du];
        [ | exfalso; apply Du, (eqm_red_eq u1 u2 Hu1 Hu2), Hu
          | exfalso; apply Hu, (eqm_red_eq u1 u2 Hu1 Hu2), Du | ].
      + split; [reflexivity | split; reflexivity].
      + rewrite div_two.
        split; [reflexivity | split; reflexivity].
    - rewrite div_two.
      set (r := t *F t -F u1 *F u2) in *.
      set (r' := r +F Vesta.a *F (zz *F zz *F (zz *F zz))) in *.
      assert (Hr : eqm q r' r) by (unfold r', Vesta.a; eqm_ring).
      split; [| split]; rewrite ?Hr; reflexivity.
  Qed.

  Lemma jadd_agrees (J1 J2 : jpoint) (pf1 : _) (pf2 : _) :
    trip_eqm (jadd J1 J2)
      (proj1_sig (jadd_fiat (exist _ J1 pf1) (exist _ J2 pf2))).
  Proof.
    rewrite add_proj. cbn [proj1_sig]. exact (jadd_agrees_raw J1 J2).
  Qed.

  (** ** The transported group law *)

  Theorem jrepr_add (J K : jpoint) (P Q : Vesta.point) :
    good P -> good Q -> jrepr J P -> jrepr K Q ->
    jrepr (jadd J K) (Vesta.add P Q).
  Proof.
    intros [_ Ho1] [_ Ho2] H1 H2.
    destruct J as [[X1 Y1] Z1]. destruct K as [[X2 Y2] Z2].
    pose (JP1 := fpt_of X1 Y1 Z1 P Ho1 H1).
    pose (JP2 := fpt_of X2 Y2 Z2 Q Ho2 H2).
    pose proof (jcorr X1 Y1 Z1 P Ho1 H1) as Hc1.
    pose proof (jcorr X2 Y2 Z2 Q Ho2 H2) as Hc2.
    pose proof (Weierstrass.add_corresponds Vesta.a Vesta.b three_lt_q P Q
                  (jto_affine JP1) (jto_affine JP2) Hc1 Hc2) as Hc3.
    pose proof (Weierstrass.corresponds_W_eq Vesta.a Vesta.b
                  (Weierstrass.add Vesta.a P Q)
                  (Weierstrass.wadd Vesta.a Vesta.b three_lt_q
                     (jto_affine JP1) (jto_affine JP2))
                  (jto_affine (jadd_fiat JP1 JP2))
                  Hc3
                  (Weierstrass.W_eq_sym Vesta.a Vesta.b _ _
                     (to_affine_add_vesta JP1 JP2))) as Hc4.
    pose proof (jrepr_of_corresponds (jadd_fiat JP1 JP2) _ Hc4) as Hr.
    eapply jrepr_eqm; [ | exact Hr ].
    exact (jadd_agrees (X1, Y1, Z1) (X2, Y2, Z2) _ _).
  Qed.

  (** ** Reduced triples and the Solinas-evaluated addition

      [PastaFast] replaces the [Z.modulo] of the field operations by the
      Solinas fold of [pallas_q], on the standing condition that the operands
      already lie in [[0, q)].  A triple whose three coordinates lie in that
      range is [jreduced]; [jadd] returns such a triple whenever its operands
      are ones, so a fold of the addition maintains the condition, and on
      [jreduced] triples [jadd_fast] is the very same function as [jadd].
      Nothing about the Jacobian layer is restated: every result proved for
      [jadd] transports along [jadd_fast_eq]. *)

  Definition jreduced (J : jpoint) : Prop :=
    let '(X, Y, Zc) := J in
    0 <= X < q /\ 0 <= Y < q /\ 0 <= Zc < q.

  Lemma range_zero : 0 <= 0 < q.
  Proof. pose proof three_lt_q. lia. Qed.

  Lemma range_one : 0 <= 1 < q.
  Proof. pose proof three_lt_q. lia. Qed.

  Lemma range_two_inv : 0 <= two_inv < q.
  Proof. vm_compute. split; [discriminate | reflexivity]. Qed.

  Lemma range_from (u : Z) : 0 <= UnOp.from u < q.
  Proof.
    unfold UnOp.from. apply Z.mod_pos_bound. pose proof three_lt_q. lia.
  Qed.

  Lemma from_range (u : Z) : 0 <= u < q -> UnOp.from u = u.
  Proof. intros Hu. unfold UnOp.from. apply Z.mod_small. exact Hu. Qed.

  Lemma range_of_from (u : Z) : UnOp.from u = u -> 0 <= u < q.
  Proof. intros Hu. rewrite <- Hu. apply range_from. Qed.

  Lemma range_bin_add (u v : Z) : 0 <= u +F v < q.
  Proof.
    unfold BinOp.add. apply Z.mod_pos_bound. pose proof three_lt_q. lia.
  Qed.

  Lemma range_bin_sub (u v : Z) : 0 <= u -F v < q.
  Proof.
    unfold BinOp.sub. apply Z.mod_pos_bound. pose proof three_lt_q. lia.
  Qed.

  Lemma range_bin_mul (u v : Z) : 0 <= u *F v < q.
  Proof.
    unfold BinOp.mul. apply Z.mod_pos_bound. pose proof three_lt_q. lia.
  Qed.

  Lemma range_un_opp (u : Z) : 0 <= -F u < q.
  Proof.
    unfold UnOp.opp. apply Z.mod_pos_bound. pose proof three_lt_q. lia.
  Qed.

  Lemma range_mulq (u v : Z) :
    0 <= u < q -> 0 <= v < q -> 0 <= mulq u v < q.
  Proof. intros Hu Hv. rewrite (mulq_spec u v Hu Hv). apply range_bin_mul. Qed.

  Lemma range_addq (u v : Z) :
    0 <= u < q -> 0 <= v < q -> 0 <= addq u v < q.
  Proof. intros Hu Hv. rewrite (addq_spec u v Hu Hv). apply range_bin_add. Qed.

  Lemma range_subq (u v : Z) :
    0 <= u < q -> 0 <= v < q -> 0 <= subq u v < q.
  Proof. intros Hu Hv. rewrite (subq_spec u v Hu Hv). apply range_bin_sub. Qed.

  Lemma range_oppq (u : Z) : 0 <= u < q -> 0 <= oppq u < q.
  Proof. intros Hu. rewrite (oppq_spec u Hu). apply range_un_opp. Qed.

  (* The slope and the numerator of the addition formula are selected by the
     doubling test, so a range argument passes through the conditional. *)
  Lemma range_if (b : bool) (u v : Z) :
    0 <= u < q -> 0 <= v < q -> 0 <= (if b then u else v) < q.
  Proof. intros Hu Hv. destruct b; assumption. Qed.

  (* Every operand of the addition formula is a coordinate, a literal, or the
     result of a field operation, so its range is read off structurally. *)
  Local Ltac jrange :=
    solve
      [ repeat first
          [ assumption
          | apply range_mulq | apply range_addq | apply range_subq
          | apply range_oppq
          | apply range_bin_mul | apply range_bin_add | apply range_bin_sub
          | apply range_un_opp | apply range_if
          | apply range_zero | apply range_one | apply range_two_inv ] ].

  (* Rewrite every [PastaFast] operation of the goal into its [Field]
     counterpart, outermost first, each range condition being discharged
     from the ones already established. *)
  Local Ltac jfastify :=
    repeat first
      [ rewrite mulq_spec by jrange
      | rewrite addq_spec by jrange
      | rewrite subq_spec by jrange
      | rewrite oppq_spec by jrange ].

  (** [jadd] with each field operation evaluated by the Solinas reduction, and
      with the zero tests on the [Z] coordinates taken directly, those
      coordinates being reduced already. *)
  Definition jadd_fast (J1 J2 : jpoint) : jpoint :=
    let '(x1, y1, z1) := J1 in
    let '(x2, y2, z2) := J2 in
    if z1 =? 0 then J2
    else if z2 =? 0 then J1
    else
      let zz1 := mulq z1 z1 in
      let zz2 := mulq z2 z2 in
      let u1 := mulq x1 zz2 in
      let u2 := mulq x2 zz1 in
      let s1 := mulq y1 (mulq zz2 z2) in
      let s2 := mulq y2 (mulq zz1 z1) in
      let z := mulq z1 z2 in
      let t := addq u1 u2 in
      let ss := addq s1 s2 in
      let e := ss =? 0 in
      let m := if e then subq u2 u1 else ss in
      let c := mulq (oppq t) (mulq m m) in
      let r := if e then subq s2 s1 else subq (mulq t t) (mulq u1 u2) in
      let x3 := addq (mulq r r) c in
      let y3 := mulq (oppq (addq (mulq r (addq (mulq (addq 1 1) x3) c))
                              (mulq m (mulq (mulq ss ss) ss)))) two_inv in
      let z3 := mulq m z in
      if e then (if u1 =? u2 then (0, 0, 0) else (x3, y3, z3)) else (x3, y3, z3).

  (** The addition maintains the range condition: the degenerate branches
      return an operand or the origin, and each coordinate of the general
      branch is the result of a field operation. *)
  Lemma jadd_reduced (J K : jpoint) :
    jreduced J -> jreduced K -> jreduced (jadd J K).
  Proof.
    destruct J as [[x1 y1] z1]. destruct K as [[x2 y2] z2].
    intros (Hx1 & Hy1 & Hz1) (Hx2 & Hy2 & Hz2).
    cbv beta iota zeta delta [jadd].
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           end;
      cbn [jreduced]; (split; [| split]); jrange.
  Qed.

  Lemma jreduced_zero : jreduced jzero.
  Proof. cbn [jreduced jzero]. repeat split; apply range_zero. Qed.

  Lemma jreduced_of (P : Vesta.point) : Vesta.reduced P -> jreduced (jof P).
  Proof.
    destruct P as [| x y]; cbn [jof Vesta.reduced Weierstrass.reduced jreduced].
    - intros _. repeat split; apply range_zero.
    - intros (Hx & Hy). split; [| split].
      + apply range_of_from, Hx.
      + apply range_of_from, Hy.
      + apply range_one.
  Qed.

  (** On reduced triples the Solinas evaluation is the field evaluation. *)
  Lemma jadd_fast_eq (J K : jpoint) :
    jreduced J -> jreduced K -> jadd_fast J K = jadd J K.
  Proof.
    destruct J as [[x1 y1] z1]. destruct K as [[x2 y2] z2].
    intros (Hx1 & Hy1 & Hz1) (Hx2 & Hy2 & Hz2).
    cbv beta iota zeta delta [jadd jadd_fast].
    rewrite (from_range z1 Hz1), (from_range z2 Hz2).
    destruct (z1 =? 0); [reflexivity |].
    destruct (z2 =? 0); [reflexivity |].
    jfastify. reflexivity.
  Qed.

  (** ** Inversion-free checkpoint against a pinned affine point

      Four multiplications, no normalisation: [Z <> 0], [X = x Z^2],
      [Y = y Z^3]. *)

  Definition jcheck (J : jpoint) (xy : Z * Z) : bool :=
    let '(X, Y, Zc) := J in
    let '(x, y) := xy in
    let zz := Zc *F Zc in
    negb (UnOp.from Zc =? 0) &&
    (UnOp.from X =? x *F zz) &&
    (UnOp.from Y =? y *F (zz *F Zc)).

  Lemma jcheck_sound (J : jpoint) (x y : Z) :
    jcheck J (x, y) = true -> jrepr J (Vesta.affine x y).
  Proof.
    destruct J as [[X Y] Zc]. cbn [jcheck].
    intros Hchk.
    apply andb_prop in Hchk as [Hchk HY].
    apply andb_prop in Hchk as [HZ HX].
    apply Bool.negb_true_iff, Z.eqb_neq in HZ.
    apply Z.eqb_eq in HX. apply Z.eqb_eq in HY.
    assert (Hnz : ~ eqm q Zc 0) by (intro Hc; apply HZ, eqm_from_zero, Hc).
    cbn [Vesta.affine jrepr]. split; [exact Hnz | split].
    - transitivity (BinOp.mul x (BinOp.mul Zc Zc)).
      + change (UnOp.from X = UnOp.from (BinOp.mul x (BinOp.mul Zc Zc))).
        rewrite from_bin_mul. exact HX.
      + apply mul_Proper; [symmetry; apply from_eqm | reflexivity].
    - transitivity (BinOp.mul y (BinOp.mul (BinOp.mul Zc Zc) Zc)).
      + change (UnOp.from Y = UnOp.from (BinOp.mul y (BinOp.mul (BinOp.mul Zc Zc) Zc))).
        rewrite from_bin_mul. exact HY.
      + apply mul_Proper; [symmetry; apply from_eqm | reflexivity].
  Qed.

  Lemma affine_reduced (x y : Z) : Vesta.reduced (Vesta.affine x y).
  Proof.
    unfold Vesta.reduced, Vesta.affine. cbn [Weierstrass.reduced].
    unfold UnOp.from. split; apply Z.mod_mod, q_pos.
  Qed.

  (** A passing checkpoint identifies the represented reduced point with the
      pinned coordinates: the inversion-free [jcheck] is enough to turn a
      Jacobian accumulator into an affine equation. *)
  Lemma jrepr_pin (J : jpoint) (P : Vesta.point) (x y : Z) :
    Vesta.reduced P -> jrepr J P -> jcheck J (x, y) = true ->
    P = Vesta.affine x y.
  Proof.
    intros HP HJ Hchk.
    exact (jrepr_inj J P (Vesta.affine x y) HP (affine_reduced x y) HJ
             (jcheck_sound J x y Hchk)).
  Qed.
End VestaJac.

(** ** Smoke test

    Two on-curve Vesta points added in Jacobian coordinates, checked against
    the affine sum computed by [Vesta.add]. *)

Module VestaJacSmokeTest.
  Definition pt1 : Vesta.point :=
    Weierstrass.Affine 1
      11426906929455361843568202299992114520848200991084027513389447476559454104162.

  Definition pt2 : Vesta.point :=
    Weierstrass.Affine 3
      28239913993140498068518932987371224554220162610247849969715027599554328000014.

  Lemma pt1_good : VestaJac.good pt1.
  Proof. split; vm_compute; repeat split; reflexivity. Qed.

  Lemma pt2_good : VestaJac.good pt2.
  Proof. split; vm_compute; repeat split; reflexivity. Qed.

  (* The Jacobian sum represents the affine sum: the pinned-point check passes
     on the coordinates [Vesta.add] returns. *)
  Example jadd_matches_affine :
    match Vesta.add pt1 pt2 with
    | Weierstrass.Affine x y =>
        VestaJac.jcheck (VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof pt2)) (x, y)
    | Weierstrass.Infinity => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.

  (* Doubling goes through the same unified formula. *)
  Example jadd_double_matches_affine :
    match Vesta.add pt1 pt1 with
    | Weierstrass.Affine x y =>
        VestaJac.jcheck (VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof pt1)) (x, y)
    | Weierstrass.Infinity => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.

  (* Adding a point to its negation lands on the point at infinity. *)
  Example jadd_neg_is_infinity :
    snd (VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof (Vesta.neg pt1))) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (* The Solinas evaluation returns the same triples as the field evaluation:
     on two affine operands, on a doubling, and on an accumulator whose [Z]
     coordinate is not [1]. *)
  Example jadd_fast_matches_generic :
    VestaJac.jadd_fast (VestaJac.jof pt1) (VestaJac.jof pt2)
    = VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof pt2).
  Proof. vm_compute. reflexivity. Qed.

  Example jadd_fast_matches_double :
    let s := VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof pt2) in
    VestaJac.jadd_fast s s = VestaJac.jadd s s.
  Proof. vm_compute. reflexivity. Qed.

  Example jadd_fast_matches_mixed :
    let s := VestaJac.jadd (VestaJac.jof pt1) (VestaJac.jof pt2) in
    VestaJac.jadd_fast s (VestaJac.jof pt1)
    = VestaJac.jadd s (VestaJac.jof pt1).
  Proof. vm_compute. reflexivity. Qed.

  (* The affine checkpoint passes on the Solinas-evaluated sum as well. *)
  Example jadd_fast_matches_affine :
    match Vesta.add pt1 pt2 with
    | Weierstrass.Affine x y =>
        VestaJac.jcheck
          (VestaJac.jadd_fast (VestaJac.jof pt1) (VestaJac.jof pt2)) (x, y)
    | Weierstrass.Infinity => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.
End VestaJacSmokeTest.
