(** * Generic short-Weierstrass curve over an abstract prime field

    The generic short-Weierstrass group over an *abstract* prime field
    [F = Z/pZ] (the repository's [Z]-mod-[p] field layer,
    [Garden.Field.Field]), with curve parameters [a b : Z] and the standing
    requirement that the characteristic differs from 2 and 3 (encoded as
    [3 < p] on the lemmas that divide by 2 or 3) and that the curve is
    nonsingular ([4 a^3 + 27 b^2 <> 0]).

    Every *definition* is given (point type with a proper point at infinity,
    [on_curve], [neg], the textbook complete addition [add] with its doubling /
    inverse / infinity branches, and the binary double-and-add [mul]), and the
    whole abelian-group cluster is proved ([Qed], axiom-free): closure
    [add_on_curve], commutativity / identity / inverse, associativity
    [add_assoc], the scalar-multiplication homomorphism [mul_add], the same-x
    dichotomy [same_x_eq_or_neg], and the prime-order theory
    [mul_eq_Infinity_iff] / [mul_injective_mod].  The associativity,
    homomorphism, and order facts are transported from fiat-crypto's affine
    [W.commutative_group] (and its [scalarmult_ref]), which is why they carry
    the [11 < p] characteristic bound and [reduced] inputs.
    [Pallas.v], [Halo2/PallasModel.v], and [FixedBaseLadder.v] wire onto these
    statements. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.EllipticCurve.FiatField.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Setoids.Setoid.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Global Open Scope Z_scope.

Module Weierstrass.
Section Curve.
  (** The abstract base field [Z/pZ]: any prime modulus. Pallas instantiates
      [p := pallas_p]. *)
  Context {p : Z} `{Prime p}.

  (** The short-Weierstrass coefficients [y^2 = x^3 + a*x + b]. *)
  Variables (a b : Z).

  (** ** Points, curve membership, negation *)

  (** A point is either the point at infinity (the group identity) or an affine
      pair of field coordinates. Coordinates are [Z]; field equality is taken
      modulo [p]. *)
  Inductive point : Set :=
  | Infinity : point
  | Affine (x y : Z) : point.

  (** The defining curve equation, compared modulo [p] so it is insensitive to
      the chosen integer representatives. *)
  Definition on_curve (P : point) : Prop :=
    match P with
    | Infinity => True
    | Affine x y =>
        UnOp.from (y *F y) = UnOp.from (x *F x *F x +F a *F x +F b)
    end.

  (** The group inverse: negate the [y] coordinate. *)
  Definition neg (P : point) : point :=
    match P with
    | Infinity => Infinity
    | Affine x y => Affine x (-F y)
    end.

  (** Nonsingularity of the curve: [4 a^3 + 27 b^2 <> 0] in the field. *)
  Definition nonsingular : Prop :=
    UnOp.from (UnOp.from 4 *F (a *F a *F a) +F UnOp.from 27 *F (b *F b)) <> 0.

  (** The [x]-coordinate as a partial projection ([None] at infinity), used to
      phrase the same-x dichotomy [same_x_eq_or_neg]. *)
  Definition x_coord (P : point) : option Z :=
    match P with
    | Infinity => None
    | Affine x _ => Some x
    end.

  (** A point is in canonical (reduced) form when its coordinates are already
      reduced modulo [p]. Outputs of [add] (hence of [mul] beyond the base
      multiple) are canonical; generators are supplied canonical. *)
  Definition reduced (P : point) : Prop :=
    match P with
    | Infinity => True
    | Affine x y => UnOp.from x = x /\ UnOp.from y = y
    end.

  (** ** Complete addition

      Textbook short-Weierstrass addition with the four exceptional branches:
      the two point-at-infinity identities, the inverse case ([x1 = x2] and
      [y1 + y2 = 0], giving infinity), the doubling case ([x1 = x2],
      [y1 + y2 <> 0], tangent slope [(3 x1^2 + a) / (2 y1)]), and the generic
      secant case ([x1 <> x2], slope [(y2 - y1) / (x2 - x1)]).  Field equality
      of [x] / [y + y'] is decided through [BinOp.sub] / [BinOp.add] reduced to
      [0]. *)
  Definition add (P Q : point) : point :=
    match P, Q with
    | Infinity, _ => Q
    | _, Infinity => P
    | Affine x1 y1, Affine x2 y2 =>
        if (x1 -F x2) =? 0 then
          if (y1 +F y2) =? 0 then
            Infinity
          else
            let lam :=
              BinOp.div (UnOp.from 3 *F x1 *F x1 +F a) (UnOp.from 2 *F y1) in
            let x3 := lam *F lam -F UnOp.from 2 *F x1 in
            let y3 := lam *F (x1 -F x3) -F y1 in
            Affine x3 y3
        else
          let lam := BinOp.div (y2 -F y1) (x2 -F x1) in
          let x3 := lam *F lam -F x1 -F x2 in
          let y3 := lam *F (x1 -F x3) -F y1 in
          Affine x3 y3
    end.

  (** ** Binary scalar multiplication (definition)

      Double-and-add over the positive binary representation, then signed by
      negating for negative scalars and returning [Infinity] at zero. *)
  Fixpoint mul_pos (n : positive) (P : point) : point :=
    match n with
    | xH => P
    | xO n' => let Q := mul_pos n' P in add Q Q
    | xI n' => let Q := mul_pos n' P in add P (add Q Q)
    end.

  Definition mul (k : Z) (P : point) : point :=
    match k with
    | Z0 => Infinity
    | Zpos n => mul_pos n P
    | Zneg n => neg (mul_pos n P)
    end.

  (** ** Reduction and congruence helpers used by the group-law proofs *)

  Lemma p_pos : p <> 0.
  Proof. pose proof (@prime_range p _). lia. Qed.

  (* Congruence modulo [p] as a setoid, to normalize field expressions to raw
     [Z] polynomials (removing all internal [mod p]) before discharging an
     identity. *)
  Local Instance eqm_equiv : Equivalence (eqm p).
  Proof. unfold eqm. constructor; congruence. Qed.
  Local Instance add_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.add := Zplus_eqm p.
  Local Instance mul_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.mul := Zmult_eqm p.
  Local Instance opp_eqm_mor : Proper (eqm p ==> eqm p) Z.opp := Zopp_eqm p.
  Local Instance sub_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.sub.
  Proof.
    intros u u' Hu v v' Hv. unfold eqm in *.
    rewrite Zminus_mod, Hu, Hv, <- Zminus_mod. reflexivity.
  Qed.

  Ltac to_raw :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    repeat setoid_rewrite (Zmod_eqm p);
    unfold eqm.

  Lemma reduced_eqp_eq (u v : Z) :
    UnOp.from u = u -> UnOp.from v = v -> eqm p u v -> u = v.
  Proof. unfold eqm, UnOp.from. intros Hu Hv He. rewrite <- Hu, <- Hv. exact He. Qed.

  Lemma from_add_reduced (u v : Z) : UnOp.from (BinOp.add u v) = BinOp.add u v.
  Proof. unfold UnOp.from, BinOp.add. apply Zmod_mod. Qed.

  Lemma add_fcong (u v c d : Z) :
    UnOp.from u = UnOp.from c -> UnOp.from v = UnOp.from d ->
    UnOp.from (BinOp.add u v) = UnOp.from (BinOp.add c d).
  Proof.
    intros Hu Hv. f_equal. unfold BinOp.add, UnOp.from in *.
    rewrite Zplus_mod, Hu, Hv, <- Zplus_mod. reflexivity.
  Qed.

  Lemma sub_fcong (u v c d : Z) :
    UnOp.from u = UnOp.from c -> UnOp.from v = UnOp.from d ->
    UnOp.from (BinOp.sub u v) = UnOp.from (BinOp.sub c d).
  Proof.
    intros Hu Hv. f_equal. unfold BinOp.sub, UnOp.from in *.
    rewrite Zminus_mod, Hu, Hv, <- Zminus_mod. reflexivity.
  Qed.

  Lemma mul_fcong (u v c d : Z) :
    UnOp.from u = UnOp.from c -> UnOp.from v = UnOp.from d ->
    UnOp.from (BinOp.mul u v) = UnOp.from (BinOp.mul c d).
  Proof. intros Hu Hv. f_equal. apply field_mul_cong; assumption. Qed.

  Lemma mod_inverse_cong (u v : Z) :
    u mod p = v mod p -> mod_inverse u p = mod_inverse v p.
  Proof.
    intros Huv.
    pose proof (@prime_range p _) as Hp1.
    unfold mod_inverse.
    destruct p as [|p'|p'] eqn:Hpe; try lia.
    rewrite !(fast_pow_correct (Z.pos p') ltac:(lia)).
    rewrite !Z.mul_1_l.
    rewrite (Zpower_mod u _ (Z.pos p')) by lia.
    rewrite (Zpower_mod v _ (Z.pos p')) by lia.
    rewrite Huv. reflexivity.
  Qed.

  Lemma div_cong (n1 d1 n2 d2 : Z) :
    UnOp.from n1 = UnOp.from n2 -> UnOp.from d1 = UnOp.from d2 ->
    BinOp.div n1 d1 = BinOp.div n2 d2.
  Proof.
    intros Hn Hd. unfold BinOp.div.
    apply field_mul_cong; [exact Hn|].
    f_equal. apply mod_inverse_cong. exact Hd.
  Qed.

  (* The modular inverse inverts any nonzero element, for every prime modulus
     (including [p = 2], handled by direct computation). *)
  Lemma mod_inverse_mul_gen (y : Z) :
    y mod p <> 0 -> BinOp.mul (mod_inverse y p) y = 1.
  Proof.
    intros Hy.
    pose proof (@is_prime p _) as Hpr.
    pose proof (@prime_range p _) as Hp1.
    destruct (Z.lt_total 2 p) as [Hgt | [Heq | Hlt]].
    - apply mod_inverse_mul; [lia | exact Hy].
    - assert (Hp2 : p = 2) by lia.
      unfold BinOp.mul, mod_inverse. rewrite Hp2 in *.
      cbn [Pos.pred Pos.pred_double fast_pow_modulo_positive].
      assert (Hm : y mod 2 = 1) by lia.
      rewrite Z.mul_1_l, Zmult_mod_idemp_l, Z.mul_mod by lia.
      rewrite Hm. reflexivity.
    - lia.
  Qed.

  Lemma div_mul_gen (x y : Z) :
    y mod p <> 0 -> BinOp.mul (BinOp.div x y) y = x mod p.
  Proof.
    intros Hy.
    pose proof (mod_inverse_mul_gen y Hy) as Hinv.
    unfold BinOp.mul in Hinv.
    unfold BinOp.div, BinOp.mul.
    rewrite Zmult_mod_idemp_l.
    replace (x * mod_inverse y p * y) with (x * (mod_inverse y p * y)) by ring.
    rewrite <- Zmult_mod_idemp_r, Hinv, Z.mul_1_r. reflexivity.
  Qed.

  Lemma sub_swap_mod_nz (u v : Z) :
    (u -F v) mod p <> 0 -> (v -F u) mod p <> 0.
  Proof.
    intros Hc Hbad. apply Hc. unfold BinOp.sub in *.
    rewrite Z.mod_mod in * by apply p_pos.
    apply (proj1 (Z.cong_iff_0 u v p)). symmetry.
    apply (proj2 (Z.cong_iff_0 v u p)). exact Hbad.
  Qed.

  (* The secant slope is invariant under swapping the two points: both the
     numerator and the denominator change sign. *)
  Lemma secant_slope_sym (x1 y1 x2 y2 : Z) :
    (x1 -F x2) mod p <> 0 ->
    BinOp.div (y2 -F y1) (x2 -F x1) = BinOp.div (y1 -F y2) (x1 -F x2).
  Proof.
    intros Hd1.
    assert (Hd2 : (x2 -F x1) mod p <> 0) by (apply sub_swap_mod_nz; exact Hd1).
    apply reduced_eqp_eq.
    - unfold BinOp.div. apply from_mul_reduced.
    - unfold BinOp.div. apply from_mul_reduced.
    - apply (field_mul_cancel_r _ _ (x2 -F x1)).
      + exact Hd2.
      + rewrite (div_mul_gen (y2 -F y1) (x2 -F x1) Hd2).
        set (D2 := BinOp.div (y1 -F y2) (x1 -F x2)).
        assert (Hr : BinOp.mul D2 (x1 -F x2) = (y1 -F y2) mod p)
          by (apply div_mul_gen; exact Hd1).
        unfold BinOp.mul, BinOp.sub in Hr |- *.
        rewrite !Zmult_mod_idemp_r in Hr |- *.
        rewrite !Z.mod_mod in Hr |- * by apply p_pos.
        apply (proj2 (Z.cong_iff_0 (y2 - y1) (D2 * (x2 - x1)) p)).
        replace (y2 - y1 - D2 * (x2 - x1))
          with (D2 * (x1 - x2) - (y1 - y2)) by ring.
        exact (proj1 (Z.cong_iff_0 (D2 * (x1 - x2)) (y1 - y2) p) Hr).
  Qed.

  (* The curve right-hand side respects field equality of the [x]-coordinate. *)
  Lemma rhs_cong (x1 x2 : Z) :
    UnOp.from x1 = UnOp.from x2 ->
    UnOp.from (x1 *F x1 *F x1 +F a *F x1 +F b) =
    UnOp.from (x2 *F x2 *F x2 +F a *F x2 +F b).
  Proof.
    intros Hx.
    apply add_fcong; [| reflexivity].
    apply add_fcong.
    - apply mul_fcong; [ apply mul_fcong; [exact Hx | exact Hx] | exact Hx].
    - apply mul_fcong; [reflexivity | exact Hx].
  Qed.

  (* Two on-curve points with equal [x] have either equal or opposite [y]. *)
  Lemma same_x_cases (x1 y1 x2 y2 : Z) :
    UnOp.from x1 = UnOp.from x2 ->
    on_curve (Affine x1 y1) -> on_curve (Affine x2 y2) ->
    UnOp.from (y1 -F y2) = 0 \/ UnOp.from (y1 +F y2) = 0.
  Proof.
    intros Hx HoP HoQ. cbn [on_curve] in HoP, HoQ.
    assert (Hsq : UnOp.from (y1 *F y1) = UnOp.from (y2 *F y2)).
    { rewrite HoP, HoQ. apply rhs_cong. exact Hx. }
    assert (Hsq' : (y1 * y1) mod p = (y2 * y2) mod p).
    { unfold UnOp.from, BinOp.mul in Hsq.
      rewrite !Z.mod_mod in Hsq by apply p_pos. exact Hsq. }
    assert (Hz : BinOp.mul (y1 -F y2) (y1 +F y2) = 0).
    { unfold BinOp.mul, BinOp.sub, BinOp.add.
      rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
      replace ((y1 - y2) * (y1 + y2)) with (y1 * y1 - y2 * y2) by ring.
      rewrite Zminus_mod, Hsq', Z.sub_diag. apply Zmod_0_l. }
    rewrite mul_zero_implies_zero in Hz. exact Hz.
  Qed.

  Lemma sub_eqb_sym (u v : Z) : ((u -F v) =? 0) = ((v -F u) =? 0).
  Proof.
    destruct (Z.eqb_spec (u -F v) 0) as [E1|E1];
    destruct (Z.eqb_spec (v -F u) 0) as [E2|E2]; try reflexivity.
    - apply sub_zero_equiv in E1. exfalso. apply E2.
      apply sub_zero_equiv. symmetry. exact E1.
    - apply sub_zero_equiv in E2. exfalso. apply E1.
      apply sub_zero_equiv. symmetry. exact E2.
  Qed.

  Lemma add_eqb_sym (u v : Z) : ((u +F v) =? 0) = ((v +F u) =? 0).
  Proof. rewrite (field_add_comm u v). reflexivity. Qed.

  (* Outputs of [add] are always reduced (their coordinates equal their own
     reduction modulo [p]). *)
  Lemma add_reduced (P Q : point) : reduced P -> reduced Q -> reduced (add P Q).
  Proof.
    intros HP HQ.
    destruct P as [|x1 y1]; [exact HQ|].
    destruct Q as [|x2 y2]; [exact HP|].
    cbn [add].
    destruct ((x1 -F x2) =? 0).
    - destruct ((y1 +F y2) =? 0).
      + exact I.
      + cbn [reduced]. split; apply from_sub_reduced.
    - cbn [reduced]. split; apply from_sub_reduced.
  Qed.

  Lemma mul_pos_reduced (n : positive) (P : point) :
    reduced P -> reduced (mul_pos n P).
  Proof.
    intros HP. induction n as [n' IH | n' IH | ]; cbn [mul_pos].
    - apply add_reduced; [exact HP | apply add_reduced; exact IH].
    - apply add_reduced; exact IH.
    - exact HP.
  Qed.

  Lemma neg_neg_reduced (P : point) : reduced P -> neg (neg P) = P.
  Proof.
    destruct P as [|x y]; [reflexivity|].
    intros [Hx Hy]. cbn [neg]. f_equal.
    unfold UnOp.opp.
    replace (- ((- y) mod p)) with ((-1) * ((- y) mod p)) by ring.
    rewrite Zmult_mod_idemp_r.
    replace ((-1) * (- y)) with y by ring.
    exact Hy.
  Qed.

  (** ** Bridge to fiat-crypto's affine short-Weierstrass group law

      The closure and associativity of [add] are obtained by transport along
      fiat-crypto's proved affine Weierstrass group law
      ([Crypto.Curves.Weierstrass.AffineProofs.W.commutative_group]), reusing the
      [field] instance over [(Z, eqm p)] built in [FiatField]. *)

  (* [Proper] instances for the field operations under [eqm p], so [setoid_rewrite]
     can normalize through them; the analogous [Z]-operation morphisms are above. *)
  Local Instance add_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.add.
  Proof.
    intros u u' Hu v v' Hv. unfold BinOp.add.
    repeat setoid_rewrite (Zmod_eqm p). exact (add_eqm_mor u u' Hu v v' Hv).
  Qed.
  Local Instance sub_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.sub.
  Proof.
    intros u u' Hu v v' Hv. unfold BinOp.sub.
    repeat setoid_rewrite (Zmod_eqm p). exact (sub_eqm_mor u u' Hu v v' Hv).
  Qed.
  Local Instance mul_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.mul.
  Proof.
    intros u u' Hu v v' Hv. unfold BinOp.mul.
    repeat setoid_rewrite (Zmod_eqm p). exact (mul_eqm_mor u u' Hu v v' Hv).
  Qed.
  Local Instance opp_Proper : Proper (eqm p ==> eqm p) UnOp.opp.
  Proof.
    intros u u' Hu. unfold UnOp.opp.
    repeat setoid_rewrite (Zmod_eqm p). exact (opp_eqm_mor u u' Hu).
  Qed.
  Local Instance from_Proper_eq : Proper (eqm p ==> @eq Z) UnOp.from.
  Proof. intros u u' Hu. exact Hu. Qed.

  (* [eqm p u v] is definitionally [UnOp.from u = UnOp.from v]. *)
  Lemma eqm_to_from (u v : Z) : eqm p u v -> UnOp.from u = UnOp.from v.
  Proof. exact (fun h => h). Qed.

  (* A pure ring identity between two field expressions in the same variables is
     an [eqm p] equality.  Each [BinOp.div] is first frozen as an opaque atom
     (the two sides share it once the slopes are identified), the internal [mod p]
     are normalized away, and [ring] discharges the remaining polynomial. *)
  Ltac eqm_ring :=
    repeat match goal with
           | |- context[BinOp.div ?n ?d] => set (BinOp.div n d) in *
           end;
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    repeat setoid_rewrite (Zmod_eqm p);
    unfold eqm; f_equal; ring.

  (** The image of [Z] under iterated [+1] is congruent to the integer. *)
  Lemma of_nat_eqm (n : nat) :
    eqm p (@Ring.of_nat Z 0 1 BinOp.add n) (Z.of_nat n).
  Proof.
    induction n as [|n IH]; cbn [Ring.of_nat].
    - reflexivity.
    - unfold BinOp.add.
      transitivity (@Ring.of_nat Z 0 1 BinOp.add n + 1).
      + apply (Zmod_eqm p).
      + rewrite Nat2Z.inj_succ, <- Z.add_1_r.
        apply (Zplus_eqm p); [exact IH | reflexivity].
  Qed.

  Lemma of_Z_eqm (z : Z) :
    eqm p (@Ring.of_Z Z 0 1 UnOp.opp BinOp.add z) z.
  Proof.
    unfold Ring.of_Z. destruct z as [|n|n].
    - reflexivity.
    - rewrite of_nat_eqm. unfold eqm. f_equal. lia.
    - unfold UnOp.opp.
      transitivity (- (@Ring.of_nat Z 0 1 BinOp.add (Pos.to_nat n))).
      + apply (Zmod_eqm p).
      + replace (Z.neg n) with (- Z.of_nat (Pos.to_nat n)) by lia.
        apply (Zopp_eqm p). apply of_nat_eqm.
  Qed.

  (** fiat-crypto's [Ring.char_ge C] holds whenever [C <= p]: every nonzero
      residue below [p] is nonzero. *)
  Lemma char_ge_aux (C : positive) :
    Z.pos C <= p ->
    @Ring.char_ge Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul C.
  Proof.
    intros HC n Hn Hbad.
    pose proof (of_Z_eqm (Z.pos n)) as Hn2.
    assert (Hz : eqm p (Z.pos n) 0) by (rewrite <- Hn2; exact Hbad).
    unfold eqm in Hz. rewrite Z.mod_0_l in Hz by apply p_pos.
    assert (0 < Z.pos n < p) by (split; [lia | apply Pos2Z.pos_lt_pos in Hn; lia]).
    rewrite Z.mod_small in Hz by lia. lia.
  Qed.

  (** The characteristic certificate [char_ge 3], used to instantiate [W.add]. *)
  Definition c3 (H3 : 3 < p) :
    @Ring.char_ge Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
      (BinNat.N.succ_pos BinNat.N.two).
  Proof. apply (char_ge_aux 3). lia. Defined.

  (** fiat-crypto's affine point type over our field, and the instantiated
      addition (needs [char_ge 3]). *)
  Definition wpoint := @W.point Z (eqm p) BinOp.add BinOp.mul a b.

  Definition wadd (H3 : 3 < p) : wpoint -> wpoint -> wpoint :=
    @W.add Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul Finv BinOp.div
      Field_eqm eqm_dec (c3 H3) a b.

  (** fiat-crypto's identity (point at infinity) and inverse (negate [y]) over
      our field; these are the group's [id] / [inv], hence the [zero] / [opp]
      that [scalarmult_ref] folds over. *)
  Definition wzero : wpoint := @W.zero Z (eqm p) BinOp.add BinOp.mul a b.

  Definition wopp (wp : wpoint) : wpoint :=
    @W.opp Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul Finv BinOp.div
      a b Field_eqm eqm_dec wp.

  (** A Garden point [P] corresponds to a fiat point [wp] when their coordinates
      agree modulo [p] (with infinity matched to infinity). *)
  Definition corresponds (P : point) (wp : wpoint) : Prop :=
    match P with
    | Infinity => W.coordinates wp = inr tt
    | Affine x y =>
        exists x' y', W.coordinates wp = inl (x', y') /\ eqm p x x' /\ eqm p y y'
    end.

  (** Every on-curve Garden point has a corresponding fiat point. *)
  Lemma repr_exists (P : point) : on_curve P -> exists wp : wpoint, corresponds P wp.
  Proof.
    destruct P as [|x y]; intros Hoc.
    - exists (exist _ (inr tt) I). reflexivity.
    - assert (Hpf : eqm p (BinOp.mul y y)
                      (BinOp.add (BinOp.add (BinOp.mul x (BinOp.mul x x)) (BinOp.mul a x)) b)).
      { cbn [on_curve] in Hoc. unfold UnOp.from in Hoc.
        change (eqm p (BinOp.mul y y)
                  (BinOp.add (BinOp.add (BinOp.mul (BinOp.mul x x) x) (BinOp.mul a x)) b)) in Hoc.
        rewrite Hoc. eqm_ring. }
      exists (exist _ (inl (x, y)) Hpf). exists x, y.
      split; [reflexivity | split; reflexivity].
  Qed.

  (* Correlation of the [x1 = x2] branch test: Garden decides [(x1 -F x2) =? 0],
     fiat decides [eqm p x1' x2']; they agree under the coordinate congruences. *)
  Lemma xcorr_iff (u v u' v' : Z) :
    eqm p u u' -> eqm p v v' -> (BinOp.sub u v = 0 <-> eqm p u' v').
  Proof.
    intros Hu Hv. rewrite sub_zero_equiv. split; intro Hc.
    - change (eqm p u v) in Hc. rewrite <- Hu, <- Hv. exact Hc.
    - change (eqm p u v). rewrite Hu, Hv. exact Hc.
  Qed.

  (* Correlation of the inverse-point branch test: Garden decides
     [(y1 +F y2) =? 0], fiat decides [eqm p y2' (-y1')]. *)
  Lemma ycorr (u v u' v' : Z) :
    eqm p u u' -> eqm p v v' -> (BinOp.add u v = 0 <-> eqm p v' (UnOp.opp u')).
  Proof.
    intros Hu Hv. unfold eqm in Hu, Hv.
    unfold BinOp.add, UnOp.opp, eqm.
    rewrite (Z.mod_mod (- u') p p_pos).
    split; intro Hc.
    - apply (proj2 (Z.cong_iff_0 v' (- u') p)).
      replace (v' - - u') with (u' + v') by ring.
      rewrite Zplus_mod, <- Hu, <- Hv, <- Zplus_mod. exact Hc.
    - apply (proj1 (Z.cong_iff_0 v' (- u') p)) in Hc.
      replace (v' - - u') with (u' + v') in Hc by ring.
      rewrite Zplus_mod, <- Hu, <- Hv, <- Zplus_mod in Hc. exact Hc.
  Qed.

  (** Single-addition agreement: [add P Q] corresponds to fiat's [W.add] of the
      corresponding points.  This is the only coordinate-algebra step; closure
      and associativity are then transported from it. *)
  Lemma add_corresponds (H3 : 3 < p) (P Q : point) (wP wQ : wpoint) :
    corresponds P wP -> corresponds Q wQ ->
    corresponds (add P Q) (wadd H3 wP wQ).
  Proof.
    intros HP HQ.
    destruct P as [|x1 y1]; destruct Q as [|x2 y2].
    - (* Infinity, Infinity *)
      cbn [add corresponds] in HP, HQ |- *.
      unfold wadd, W.add. cbn [W.coordinates]. rewrite HP, HQ. reflexivity.
    - (* Infinity, Affine *)
      cbn [add corresponds] in HP, HQ |- *.
      destruct HQ as (xq & yq & HcQ & Hx2 & Hy2).
      exists xq, yq. unfold wadd, W.add. cbn [W.coordinates].
      rewrite HP, HcQ. split; [reflexivity | split; assumption].
    - (* Affine, Infinity *)
      cbn [add corresponds] in HP, HQ |- *.
      destruct HP as (xp & yp & HcP & Hx1 & Hy1).
      exists xp, yp. unfold wadd, W.add. cbn [W.coordinates].
      rewrite HcP, HQ. split; [reflexivity | split; assumption].
    - (* Affine, Affine *)
      cbn [corresponds] in HP, HQ.
      destruct HP as (xp & yp & HcP & Hx1 & Hy1).
      destruct HQ as (xq & yq & HcQ & Hx2 & Hy2).
      cbn [add].
      destruct (Z.eqb_spec (x1 -F x2) 0) as [Hxe | Hxne].
      + (* Garden detects x1 = x2 *)
        assert (Hx12 : eqm p x1 x2) by (apply sub_zero_equiv; exact Hxe).
        assert (Hxx : eqm p xp xq).
        { transitivity x1; [symmetry; exact Hx1|].
          transitivity x2; [exact Hx12 | exact Hx2]. }
        destruct (Z.eqb_spec (y1 +F y2) 0) as [Hye | Hyne].
        * (* inverse point: both yield infinity *)
          assert (Hyy : eqm p yq (UnOp.opp yp))
            by (apply (proj1 (ycorr y1 y2 yp yq Hy1 Hy2)); exact Hye).
          cbn [corresponds].
          unfold wadd, W.add. cbn [W.coordinates]. rewrite HcP, HcQ.
          destruct (dec (eqm p xp xq)) as [_ | Hbad]; [| exfalso; apply Hbad; exact Hxx].
          destruct (dec (eqm p yq (UnOp.opp yp))) as [_ | Hbad];
            [| exfalso; apply Hbad; exact Hyy].
          reflexivity.
        * (* doubling *)
          assert (Hyy : ~ eqm p yq (UnOp.opp yp))
            by (intro Hc; apply Hyne; apply (proj2 (ycorr y1 y2 yp yq Hy1 Hy2)); exact Hc).
          assert (Hqp : eqm p xq xp) by (symmetry; exact Hxx).
          cbn [corresponds].
          unfold wadd, W.add. cbn [W.coordinates]. rewrite HcP, HcQ.
          destruct (dec (eqm p xp xq)) as [_ | Hbad]; [| exfalso; apply Hbad; exact Hxx].
          destruct (dec (eqm p yq (UnOp.opp yp))) as [Hbad | _];
            [exfalso; apply Hyy; exact Hbad |].
          assert (Hlam :
            BinOp.div (UnOp.from 3 *F x1 *F x1 +F a) (UnOp.from 2 *F y1) =
            BinOp.div ((1 +F (1 +F 1)) *F (xp *F xp) +F a) ((1 +F 1) *F yp)).
          { apply div_cong; apply eqm_to_from;
            [ rewrite Hx1; eqm_ring | rewrite Hy1; eqm_ring ]. }
          rewrite Hlam.
          eexists; eexists; split; [reflexivity | split].
          -- rewrite Hx1, Hqp. eqm_ring.
          -- rewrite Hx1, Hy1, Hqp. eqm_ring.
      + (* secant *)
        assert (Hxx : ~ eqm p xp xq)
          by (intro Hc; apply Hxne;
              apply (proj2 (xcorr_iff x1 x2 xp xq Hx1 Hx2)); exact Hc).
        cbn [corresponds].
        unfold wadd, W.add. cbn [W.coordinates]. rewrite HcP, HcQ.
        destruct (dec (eqm p xp xq)) as [Hbad | _]; [exfalso; apply Hxx; exact Hbad |].
        assert (Hlam :
          BinOp.div (y2 -F y1) (x2 -F x1) = BinOp.div (yq -F yp) (xq -F xp)).
        { apply div_cong; apply eqm_to_from;
          [ rewrite Hy1, Hy2; eqm_ring | rewrite Hx1, Hx2; eqm_ring ]. }
        rewrite Hlam.
        eexists; eexists; split; [reflexivity | split].
        -- rewrite Hx1, Hx2. eqm_ring.
        -- rewrite Hx1, Hx2, Hy1. eqm_ring.
  Qed.

  (** ** Closure of addition on the curve

      Transported from fiat-crypto: [W.add] of two on-curve fiat points is again
      an on-curve fiat point by construction, and [add P Q] corresponds to it. *)
  Lemma add_on_curve (P Q : point) :
    3 < p ->
    on_curve P ->
    on_curve Q ->
    on_curve (add P Q).
  Proof.
    intros H3 HP HQ.
    destruct (repr_exists P HP) as [wP HwP].
    destruct (repr_exists Q HQ) as [wQ HwQ].
    pose proof (add_corresponds H3 P Q wP wQ HwP HwQ) as Hc.
    destruct (add P Q) as [|x3 y3].
    - exact I.
    - cbn [corresponds] in Hc. destruct Hc as (x' & y' & Hcoord & Hx3 & Hy3).
      destruct (wadd H3 wP wQ) as [c Hpf].
      cbn [W.coordinates] in Hcoord. subst c. cbn in Hpf.
      cbn [on_curve]. apply eqm_to_from.
      rewrite Hx3, Hy3, Hpf. eqm_ring.
  Qed.

  (** ** Commutativity *)
  Lemma add_comm (P Q : point) :
    on_curve P ->
    on_curve Q ->
    add P Q = add Q P.
  Proof using a b.
    intros HP HQ.
    destruct P as [|x1 y1]; destruct Q as [|x2 y2].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn [add].
      destruct ((x1 -F x2) =? 0) eqn:E1.
      + (* x1 and x2 agree modulo p *)
        rewrite (sub_eqb_sym x2 x1), E1.
        assert (Hxeq : UnOp.from x1 = UnOp.from x2)
          by (apply sub_zero_equiv; apply Z.eqb_eq; exact E1).
        destruct ((y1 +F y2) =? 0) eqn:E2.
        * rewrite (add_eqb_sym y2 y1), E2. reflexivity.
        * rewrite (add_eqb_sym y2 y1), E2.
          assert (Hyeq : UnOp.from y1 = UnOp.from y2).
          { destruct (same_x_cases x1 y1 x2 y2 Hxeq HP HQ) as [Hd|Hd].
            - rewrite from_sub_reduced in Hd. apply sub_zero_equiv. exact Hd.
            - exfalso. rewrite from_add_reduced in Hd.
              apply Z.eqb_neq in E2. contradiction. }
          assert (Hlf : UnOp.from
                          (BinOp.div (UnOp.from 3 *F x1 *F x1 +F a) (UnOp.from 2 *F y1)) =
                        UnOp.from
                          (BinOp.div (UnOp.from 3 *F x2 *F x2 +F a) (UnOp.from 2 *F y2))).
          { f_equal. apply div_cong.
            - apply add_fcong; [| reflexivity].
              apply mul_fcong; [ apply mul_fcong; [reflexivity | exact Hxeq] | exact Hxeq].
            - apply mul_fcong; [reflexivity | exact Hyeq]. }
          assert (Hx3 : UnOp.from
                          (BinOp.div (UnOp.from 3 *F x1 *F x1 +F a) (UnOp.from 2 *F y1) *F
                           BinOp.div (UnOp.from 3 *F x1 *F x1 +F a) (UnOp.from 2 *F y1)
                           -F UnOp.from 2 *F x1) =
                        UnOp.from
                          (BinOp.div (UnOp.from 3 *F x2 *F x2 +F a) (UnOp.from 2 *F y2) *F
                           BinOp.div (UnOp.from 3 *F x2 *F x2 +F a) (UnOp.from 2 *F y2)
                           -F UnOp.from 2 *F x2)).
          { apply sub_fcong.
            - apply mul_fcong; [exact Hlf | exact Hlf].
            - apply mul_fcong; [reflexivity | exact Hxeq]. }
          f_equal.
          -- apply reduced_eqp_eq; [apply from_sub_reduced | apply from_sub_reduced | exact Hx3].
          -- apply reduced_eqp_eq; [apply from_sub_reduced | apply from_sub_reduced | ].
             apply sub_fcong; [| exact Hyeq].
             apply mul_fcong; [exact Hlf |].
             apply sub_fcong; [exact Hxeq | exact Hx3].
      + (* secant case: distinct x-coordinates *)
        rewrite (sub_eqb_sym x2 x1), E1.
        assert (Hne : (x1 -F x2) mod p <> 0).
        { apply Z.eqb_neq in E1. unfold BinOp.sub.
          rewrite Z.mod_mod by apply p_pos. exact E1. }
        assert (Hslope :
          BinOp.div (y2 -F y1) (x2 -F x1) = BinOp.div (y1 -F y2) (x1 -F x2))
          by (apply secant_slope_sym; exact Hne).
        assert (Hd2 : (x2 -F x1) mod p <> 0) by (apply sub_swap_mod_nz; exact Hne).
        set (L := BinOp.div (y2 -F y1) (x2 -F x1)) in *.
        rewrite <- Hslope.
        assert (Hslrel : (L * (x2 - x1)) mod p = (y2 - y1) mod p).
        { pose proof (div_mul_gen (y2 -F y1) (x2 -F x1) Hd2) as Hr.
          fold L in Hr. unfold BinOp.mul, BinOp.sub in Hr.
          rewrite Zmult_mod_idemp_r, !Z.mod_mod in Hr by apply p_pos. exact Hr. }
        f_equal.
        -- apply reduced_eqp_eq; [apply from_sub_reduced | apply from_sub_reduced | ].
           to_raw. f_equal. ring.
        -- apply reduced_eqp_eq; [apply from_sub_reduced | apply from_sub_reduced | ].
           to_raw.
           apply (proj2 (Z.cong_iff_0 _ _ p)).
           match goal with
           | |- (?A - ?B) mod p = 0 =>
               replace (A - B) with (- (L * (x2 - x1) - (y2 - y1))) by ring
           end.
           replace (- (L * (x2 - x1) - (y2 - y1)))
             with ((-1) * (L * (x2 - x1) - (y2 - y1))) by ring.
           rewrite Z.mul_mod by apply p_pos.
           rewrite (proj1 (Z.cong_iff_0 (L * (x2 - x1)) (y2 - y1) p) Hslrel).
           rewrite Z.mul_0_r. apply Zmod_0_l.
  Qed.

  (** ** Identity laws *)
  Lemma add_Infinity_l (P : point) :
    add Infinity P = P.
  Proof using a b. reflexivity. Qed.

  Lemma add_Infinity_r (P : point) :
    add P Infinity = P.
  Proof using a b. destruct P; reflexivity. Qed.

  (** ** Inverse law *)
  Lemma add_neg (P : point) :
    add P (neg P) = Infinity.
  Proof using a b.
    destruct P as [|x y]; [reflexivity|].
    cbn [neg add].
    assert (Hx : (x -F x) = 0).
    { unfold BinOp.sub. rewrite Z.sub_diag. apply Zmod_0_l. }
    assert (Hy : (y +F -F y) = 0).
    { unfold BinOp.add, UnOp.opp.
      rewrite Z.add_mod_idemp_r by apply p_pos.
      rewrite Z.add_opp_diag_r. apply Zmod_0_l. }
    rewrite Hx, Hy. reflexivity.
  Qed.

  (** Symmetry of fiat's point equality [W.eq]. *)
  Lemma W_eq_sym (u v : wpoint) : W.eq u v -> W.eq v u.
  Proof.
    unfold W.eq.
    destruct (W.coordinates u) as [[xu yu]|[]];
      destruct (W.coordinates v) as [[xv yv]|[]];
      intros He; try exact He.
    destruct He as [Hx Hy]. split; symmetry; assumption.
  Qed.

  (** [corresponds] is injective on the reduced domain: two reduced Garden points
      whose fiat images are [W.eq] are syntactically equal.  ([corresponds] only
      pins coordinates modulo [p], so reducedness is what upgrades the modular
      agreement to integer equality of the representatives.) *)
  Lemma corresponds_inj (A B : point) (wA wB : wpoint) :
    reduced A -> reduced B ->
    corresponds A wA -> corresponds B wB -> W.eq wA wB -> A = B.
  Proof.
    intros HrA HrB HcA HcB Heq.
    destruct A as [|xa ya]; destruct B as [|xb yb].
    - reflexivity.
    - cbn [corresponds] in HcA, HcB.
      destruct HcB as (xb2 & yb2 & HcoordB & _ & _).
      unfold W.eq in Heq. rewrite HcA, HcoordB in Heq. cbn in Heq. contradiction.
    - cbn [corresponds] in HcA, HcB.
      destruct HcA as (xa2 & ya2 & HcoordA & _ & _).
      unfold W.eq in Heq. rewrite HcoordA, HcB in Heq. cbn in Heq. contradiction.
    - cbn [corresponds reduced] in HcA, HcB, HrA, HrB.
      destruct HcA as (xa2 & ya2 & HcoordA & Hxa & Hya).
      destruct HcB as (xb2 & yb2 & HcoordB & Hxb & Hyb).
      destruct HrA as [HrAx HrAy]. destruct HrB as [HrBx HrBy].
      unfold W.eq in Heq. rewrite HcoordA, HcoordB in Heq.
      change (eqm p xa2 xb2 /\ eqm p ya2 yb2) in Heq.
      destruct Heq as [Hxe Hye].
      f_equal.
      + apply (reduced_eqp_eq xa xb HrAx HrBx).
        transitivity xa2; [exact Hxa | transitivity xb2; [exact Hxe | symmetry; exact Hxb]].
      + apply (reduced_eqp_eq ya yb HrAy HrBy).
        transitivity ya2; [exact Hya | transitivity yb2; [exact Hye | symmetry; exact Hyb]].
  Qed.

  (** ** Associativity (the long pole)

      Transported from fiat-crypto's proved affine Weierstrass commutative group
      law ([W.commutative_group]).  That theorem needs [char_ge 12] (i.e.
      [11 < p]) and the nonzero-discriminant (= [nonsingular]) hypothesis; its
      conclusion is modular ([W.eq]), so [corresponds_inj] upgrades it to Garden's
      syntactic point equality, which is why the inputs must be [reduced]
      (outputs of [add] then are too).  Associativity is false at the level of
      integer representatives for non-reduced inputs: [add]'s
      infinity-passthrough returns its argument verbatim, so e.g. at [p = 17],
      [a = 0], [b = 1], [add (add P (neg P)) R] keeps [R]'s representative while
      [add P (add (neg P) R)] reduces it. *)
  Lemma add_assoc (P Q R : point) :
    11 < p ->
    nonsingular ->
    reduced P ->
    reduced Q ->
    reduced R ->
    on_curve P ->
    on_curve Q ->
    on_curve R ->
    add (add P Q) R = add P (add Q R).
  Proof.
    intros H11 Hns HrP HrQ HrR HoP HoQ HoR.
    assert (H3 : 3 < p) by lia.
    destruct (repr_exists P HoP) as [wP HwP].
    destruct (repr_exists Q HoQ) as [wQ HwQ].
    destruct (repr_exists R HoR) as [wR HwR].
    pose proof (add_corresponds H3 P Q wP wQ HwP HwQ) as HcPQ.
    pose proof (add_corresponds H3 Q R wQ wR HwQ HwR) as HcQR.
    pose proof (add_corresponds H3 (add P Q) R (wadd H3 wP wQ) wR HcPQ HwR) as HcL.
    pose proof (add_corresponds H3 P (add Q R) wP (wadd H3 wQ wR) HwP HcQR) as HcR.
    (* The nonzero-discriminant precondition of [W.commutative_group], obtained
       from [nonsingular] by identifying fiat's literal [4]/[27] with ours. *)
    assert (Hdisc : ~ eqm p
      (BinOp.add
         (BinOp.mul (BinOp.mul (BinOp.mul
            (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1) a) a) a)
         (BinOp.mul (BinOp.mul
            (BinOp.add (BinOp.add (BinOp.add (BinOp.add (BinOp.add
               (BinOp.mul (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)
                  (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
               (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
               (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)) 1) 1) 1)
            b) b)) 0).
    { intros Hbad. apply Hns.
      assert (Heq0 : eqm p
        (UnOp.from 4 *F (a *F a *F a) +F UnOp.from 27 *F (b *F b)) 0).
      { transitivity
          (BinOp.add
             (BinOp.mul (BinOp.mul (BinOp.mul
                (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1) a) a) a)
             (BinOp.mul (BinOp.mul
                (BinOp.add (BinOp.add (BinOp.add (BinOp.add (BinOp.add
                   (BinOp.mul (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)
                      (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
                   (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
                   (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)) 1) 1) 1)
                b) b)).
        - eqm_ring.
        - exact Hbad. }
      unfold eqm in Heq0. rewrite Z.mod_0_l in Heq0 by apply p_pos. exact Heq0. }
    pose proof (@W.commutative_group Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub
                  BinOp.mul Finv BinOp.div a b Field_eqm eqm_dec (c3 H3)
                  (char_ge_aux 12 ltac:(lia)) Hdisc) as Hcg.
    pose proof (@associative wpoint (@W.eq Z (eqm p) BinOp.add BinOp.mul a b)
                  (@W.add Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
                     Finv BinOp.div Field_eqm eqm_dec (c3 H3) a b)
                  _ wP wQ wR) as Hassoc.
    apply (corresponds_inj (add (add P Q) R) (add P (add Q R))
             (wadd H3 (wadd H3 wP wQ) wR) (wadd H3 wP (wadd H3 wQ wR))).
    - apply add_reduced; [apply add_reduced; assumption | assumption].
    - apply add_reduced; [assumption | apply add_reduced; assumption].
    - exact HcL.
    - exact HcR.
    - apply W_eq_sym. exact Hassoc.
  Qed.

  (** ** Scalar-multiplication bridge to fiat-crypto

      [Weierstrass.mul] is transported onto fiat-crypto's [scalarmult_ref] over
      the proved affine commutative group: the binary double-and-add [mul_pos]
      matches the peano [scalarmult_ref] through [scalarmult_add_l] / [_1_l], so
      the homomorphism is [scalarmult_add_l] and the order theory is
      [scalarmult_times_order] plus a Bezout argument.  Because [scalarmult_ref]
      only proves equalities modulo [p] ([W.eq]), [corresponds_inj] upgrades them
      to Garden's structural point equality, which is why the consumers carry the
      [reduced] / [11 < p] preconditions [add_assoc] already needs. *)

  (* [corresponds] only constrains coordinates up to [W.eq], so it is stable
     under replacing the fiat point by a [W.eq]-equal one. *)
  Lemma corresponds_W_eq (P : point) (w w' : wpoint) :
    corresponds P w -> W.eq w w' -> corresponds P w'.
  Proof.
    destruct P as [|x y]; cbn [corresponds]; intros Hc Heq; unfold W.eq in Heq.
    - rewrite Hc in Heq.
      destruct (W.coordinates w') as [[xx yy]|u] eqn:E; [contradiction|].
      destruct u. reflexivity.
    - destruct Hc as (x' & y' & Hcw & Hx & Hy).
      rewrite Hcw in Heq.
      destruct (W.coordinates w') as [[xx yy]|u] eqn:E; [|contradiction].
      destruct Heq as [Hxe Hye].
      exists xx, yy. split; [reflexivity | split].
      + transitivity x'; assumption.
      + transitivity y'; assumption.
  Qed.

  (* [W.zero] is the point at infinity, so it corresponds to [Infinity]. *)
  Lemma corresponds_Infinity_wzero : corresponds Infinity wzero.
  Proof. reflexivity. Qed.

  (* The fiat inverse only negates the [y]-coordinate. *)
  Lemma wopp_coordinates (wQ : wpoint) :
    W.coordinates (wopp wQ) =
    match W.coordinates wQ with
    | inl (x1, y1) => inl (x1, UnOp.opp y1)
    | inr tt => inr tt
    end.
  Proof. destruct wQ as [[[x1 y1]|[]] pf]; reflexivity. Qed.

  (* The fiat inverse matches Garden's [neg]. *)
  Lemma neg_corresponds (Q : point) (wQ : wpoint) :
    corresponds Q wQ -> corresponds (neg Q) (wopp wQ).
  Proof.
    destruct Q as [|x y]; cbn [neg corresponds]; intros Hc.
    - rewrite wopp_coordinates, Hc. reflexivity.
    - destruct Hc as (x' & y' & Hcw & Hx & Hy).
      exists x', (UnOp.opp y').
      rewrite wopp_coordinates, Hcw. split; [reflexivity | split].
      + exact Hx.
      + apply opp_Proper. exact Hy.
  Qed.

  (* Outputs of [neg] / [mul] are reduced when the input is. *)
  Lemma neg_reduced (Q : point) : reduced Q -> reduced (neg Q).
  Proof.
    destruct Q as [|x y]; [cbn; tauto|].
    intros [Hx _]. cbn [neg reduced]. split; [exact Hx|].
    unfold UnOp.from, UnOp.opp. apply Zmod_mod.
  Qed.

  Lemma mul_reduced (k : Z) (P : point) : reduced P -> reduced (mul k P).
  Proof.
    intros HP. destruct k as [|n|n]; cbn [mul].
    - exact I.
    - apply mul_pos_reduced. exact HP.
    - apply neg_reduced. apply mul_pos_reduced. exact HP.
  Qed.

  (* The nonsingular curve's discriminant in fiat's literal-[4]/[27] form
     (the precondition of [W.commutative_group]). *)
  Lemma disc_of_nonsingular :
    nonsingular ->
    ~ eqm p
      (BinOp.add
         (BinOp.mul (BinOp.mul (BinOp.mul
            (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1) a) a) a)
         (BinOp.mul (BinOp.mul
            (BinOp.add (BinOp.add (BinOp.add (BinOp.add (BinOp.add
               (BinOp.mul (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)
                  (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
               (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
               (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)) 1) 1) 1)
            b) b)) 0.
  Proof.
    intros Hns Hbad. apply Hns.
    assert (Heq0 : eqm p
      (UnOp.from 4 *F (a *F a *F a) +F UnOp.from 27 *F (b *F b)) 0).
    { transitivity
        (BinOp.add
           (BinOp.mul (BinOp.mul (BinOp.mul
              (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1) a) a) a)
           (BinOp.mul (BinOp.mul
              (BinOp.add (BinOp.add (BinOp.add (BinOp.add (BinOp.add
                 (BinOp.mul (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)
                    (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
                 (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1))
                 (BinOp.add (BinOp.add (BinOp.add 1 1) 1) 1)) 1) 1) 1)
              b) b)).
      - eqm_ring.
      - exact Hbad. }
    unfold eqm in Heq0. rewrite Z.mod_0_l in Heq0 by apply p_pos. exact Heq0.
  Qed.

  (* fiat-crypto's affine commutative group instantiated over our field, from
     the [11 < p] characteristic bound and the nonsingular discriminant. *)
  Definition comm_group (H3 : 3 < p) (H11 : 11 < p) (Hns : nonsingular) :
    @commutative_group wpoint W.eq (wadd H3) wzero wopp :=
    @W.commutative_group Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul
      Finv BinOp.div a b Field_eqm eqm_dec (c3 H3)
      (char_ge_aux 12 ltac:(lia)) (disc_of_nonsingular Hns).

  (* [mul k P] corresponds to the fiat scalar multiple [k . wP].  [mul_pos]'s
     binary double-and-add matches the peano [scalarmult_ref] via
     [scalarmult_add_l] (doubling) / [scalarmult_1_l]; the zero and sign cases
     use [scalarmult_0_l] / [scalarmult_opp_l]. *)
  Lemma mul_corresponds (H3 : 3 < p) (H11 : 11 < p) (Hns : nonsingular)
    (P : point) (wP : wpoint) (Hc : corresponds P wP) :
    forall k : Z,
      corresponds (mul k P)
        (@scalarmult_ref wpoint (wadd H3) wzero wopp k wP).
  Proof.
    pose proof (comm_group H3 H11 Hns) as grp.
    assert (Hpos : forall n : positive,
              corresponds (mul_pos n P)
                (@scalarmult_ref wpoint (wadd H3) wzero wopp (Z.pos n) wP)).
    { induction n as [n IH | n IH | ]; cbn [mul_pos].
      - (* xI n *)
        eapply corresponds_W_eq.
        + apply add_corresponds; [exact Hc|].
          apply add_corresponds; [exact IH | exact IH].
        + symmetry.
          replace (Z.pos (xI n)) with (1 + (Z.pos n + Z.pos n)) by lia.
          rewrite (scalarmult_add_l 1 (Z.pos n + Z.pos n) wP).
          rewrite (scalarmult_add_l (Z.pos n) (Z.pos n) wP).
          rewrite (scalarmult_1_l wP).
          reflexivity.
      - (* xO n *)
        eapply corresponds_W_eq.
        + apply add_corresponds; [exact IH | exact IH].
        + symmetry.
          replace (Z.pos (xO n)) with (Z.pos n + Z.pos n) by lia.
          rewrite (scalarmult_add_l (Z.pos n) (Z.pos n) wP).
          reflexivity.
      - (* xH *)
        eapply corresponds_W_eq; [exact Hc|].
        symmetry. apply scalarmult_1_l. }
    intros k. destruct k as [|n|n]; cbn [mul].
    - apply (corresponds_W_eq Infinity wzero
               (@scalarmult_ref wpoint (wadd H3) wzero wopp 0 wP)).
      + apply corresponds_Infinity_wzero.
      + symmetry. apply scalarmult_0_l.
    - exact (Hpos n).
    - apply (corresponds_W_eq (neg (mul_pos n P))
               (wopp (@scalarmult_ref wpoint (wadd H3) wzero wopp (Z.pos n) wP))
               (@scalarmult_ref wpoint (wadd H3) wzero wopp (Z.neg n) wP)).
      + apply neg_corresponds. exact (Hpos n).
      + symmetry. replace (Z.neg n) with (- Z.pos n) by lia.
        apply scalarmult_opp_l.
  Qed.

  (* [mul n G = Infinity] iff the fiat multiple [n . wG] is the identity. *)
  Lemma mul_Infinity_iff_smul_zero (H3 : 3 < p) (H11 : 11 < p) (Hns : nonsingular)
    (G : point) (wG : wpoint) (HrG : reduced G) (Hc : corresponds G wG) (n : Z) :
    mul n G = Infinity <->
    W.eq (@scalarmult_ref wpoint (wadd H3) wzero wopp n wG) wzero.
  Proof.
    pose proof (mul_corresponds H3 H11 Hns G wG Hc n) as Hmc.
    split.
    - intros Hn. rewrite Hn in Hmc. cbn [corresponds] in Hmc.
      unfold W.eq. rewrite Hmc. exact I.
    - intros Hn.
      apply (corresponds_inj (mul n G) Infinity
               (@scalarmult_ref wpoint (wadd H3) wzero wopp n wG) wzero).
      + apply mul_reduced. exact HrG.
      + exact I.
      + exact Hmc.
      + apply corresponds_Infinity_wzero.
      + exact Hn.
  Qed.

  (* Order theory: for [G] of prime order [q] (the certificate [q . wG = 0]),
     the multiples annihilated by [scalarmult] are exactly the [q]-multiples.
     The converse is a Bezout argument: were [q] coprime to [n], [1 = u*q + v*n]
     would make [wG = 1 . wG] the identity, contradicting [wG <> 0]. *)
  Lemma smul_zero_iff_divide (H3 : 3 < p) (H11 : 11 < p) (Hns : nonsingular)
    (G : point) (wG : wpoint) (Hc : corresponds G wG)
    (HGne : ~ W.eq wG wzero)
    (q : Z) (Hq : IsPrime q)
    (Hqz : W.eq (@scalarmult_ref wpoint (wadd H3) wzero wopp q wG) wzero)
    (n : Z) :
    W.eq (@scalarmult_ref wpoint (wadd H3) wzero wopp n wG) wzero <->
    Z.divide q n.
  Proof.
    pose proof (comm_group H3 H11 Hns) as grp.
    split.
    - intros Hnz.
      destruct (Zdivide_dec q n) as [Hd | Hnd]; [exact Hd | exfalso].
      apply HGne.
      pose proof (prime_rel_prime q Hq n Hnd) as Hrp.
      destruct (rel_prime_bezout q n Hrp) as [u v Huv].
      assert (HG1 : W.eq
        (@scalarmult_ref wpoint (wadd H3) wzero wopp (u * q + v * n) wG) wzero).
      { rewrite (scalarmult_add_l (u * q) (v * n) wG).
        rewrite (Z.mul_comm u q).
        rewrite (scalarmult_times_order q wG Hqz u).
        rewrite (Z.mul_comm v n).
        rewrite (scalarmult_times_order n wG Hnz v).
        apply left_identity. }
      rewrite Huv in HG1.
      rewrite (scalarmult_1_l wG) in HG1.
      exact HG1.
    - intros [m Hm]. rewrite Hm, (Z.mul_comm m q).
      apply (scalarmult_times_order q wG Hqz m).
  Qed.

  (** ** Scalar-multiplication homomorphism *)
  Lemma mul_add (i j : Z) (P : point) :
    11 < p ->
    nonsingular ->
    reduced P ->
    on_curve P ->
    mul (i + j) P = add (mul i P) (mul j P).
  Proof.
    intros H11 Hns HrP HoP.
    assert (H3 : 3 < p) by lia.
    destruct (repr_exists P HoP) as [wP HwP].
    pose proof (comm_group H3 H11 Hns) as grp.
    pose proof (mul_corresponds H3 H11 Hns P wP HwP) as Hmc.
    apply (corresponds_inj (mul (i + j) P) (add (mul i P) (mul j P))
             (@scalarmult_ref wpoint (wadd H3) wzero wopp (i + j) wP)
             (wadd H3 (@scalarmult_ref wpoint (wadd H3) wzero wopp i wP)
                      (@scalarmult_ref wpoint (wadd H3) wzero wopp j wP))).
    - apply mul_reduced. exact HrP.
    - apply add_reduced; apply mul_reduced; exact HrP.
    - exact (Hmc (i + j)).
    - apply add_corresponds; [exact (Hmc i) | exact (Hmc j)].
    - apply scalarmult_add_l.
  Qed.

  Lemma mul_0 (P : point) :
    mul 0 P = Infinity.
  Proof using a b. reflexivity. Qed.

  Lemma mul_neg (i : Z) (P : point) :
    reduced P ->
    mul (- i) P = neg (mul i P).
  Proof using a b.
    intros HP. destruct i as [|n|n]; cbn [mul Z.opp].
    - reflexivity.
    - reflexivity.
    - symmetry. apply neg_neg_reduced. apply mul_pos_reduced. exact HP.
  Qed.

  (** ** Scalar-multiplication composition law

      [mul (i*j) P = mul i (mul j P)].  Transported, exactly like the
      homomorphism [mul_add], from fiat-crypto's [scalarmult_assoc] over the
      commutative group: both sides correspond to fiat scalar multiples
      ([scalarmult_ref (i*j) wP] and [scalarmult_ref i (scalarmult_ref j wP)]),
      and [scalarmult_assoc] identifies them modulo [W.eq]; [corresponds_inj]
      upgrades the modular equality to Garden's structural point equality on
      the reduced domain.  Carries [11 < p] and [reduced]/[on_curve P], like
      [add_assoc] and [mul_add]. *)
  Lemma mul_mul (i j : Z) (P : point) :
    11 < p ->
    nonsingular ->
    reduced P ->
    on_curve P ->
    mul (i * j) P = mul i (mul j P).
  Proof.
    intros H11 Hns HrP HoP.
    assert (H3 : 3 < p) by lia.
    destruct (repr_exists P HoP) as [wP HwP].
    pose proof (comm_group H3 H11 Hns) as grp.
    pose proof (mul_corresponds H3 H11 Hns P wP HwP) as Hmc.
    apply (corresponds_inj (mul (i * j) P) (mul i (mul j P))
             (@scalarmult_ref wpoint (wadd H3) wzero wopp (i * j) wP)
             (@scalarmult_ref wpoint (wadd H3) wzero wopp i
                (@scalarmult_ref wpoint (wadd H3) wzero wopp j wP))).
    - apply mul_reduced. exact HrP.
    - apply mul_reduced. apply mul_reduced. exact HrP.
    - exact (Hmc (i * j)).
    - exact (mul_corresponds H3 H11 Hns (mul j P)
               (@scalarmult_ref wpoint (wadd H3) wzero wopp j wP) (Hmc j) i).
    - apply W_eq_sym.
      replace (i * j) with (j * i) by lia.
      exact (scalarmult_assoc i j wP).
  Qed.

  (** ** Two on-curve points with equal [x] are equal or opposite *)
  Lemma same_x_eq_or_neg (P Q : point) :
    reduced P ->
    reduced Q ->
    on_curve P ->
    on_curve Q ->
    x_coord P = x_coord Q ->
    P = Q \/ P = neg Q.
  Proof using a b.
    destruct P as [|x1 y1]; destruct Q as [|x2 y2].
    - intros. left. reflexivity.
    - intros _ _ _ _ Hxc. cbn in Hxc. discriminate.
    - intros _ _ _ _ Hxc. cbn in Hxc. discriminate.
    - intros [Hx1 Hy1] [Hx2 Hy2] HoP HoQ Hxc.
      cbn in Hxc. injection Hxc as Hx12. subst x2.
      assert (Hxeq : UnOp.from x1 = UnOp.from x1) by reflexivity.
      destruct (same_x_cases x1 y1 x1 y2 Hxeq HoP HoQ) as [Hd | Hd].
      + rewrite from_sub_reduced in Hd. apply sub_zero_equiv in Hd.
        rewrite Hy1, Hy2 in Hd. left. congruence.
      + right.
        assert (Hd' : (y1 + y2) mod p = 0).
        { unfold UnOp.from, BinOp.add in Hd.
          rewrite Z.mod_mod in Hd by apply p_pos. exact Hd. }
        cbn [neg]. f_equal.
        replace (UnOp.opp y2) with (UnOp.from (- y2)) by reflexivity.
        rewrite <- Hy1, <- sub_zero_equiv.
        unfold BinOp.sub. replace (y1 - - y2) with (y1 + y2) by ring.
        exact Hd'.
  Qed.

  (** ** Order theory and injectivity for a prime-order generator

      For [G] on the curve, distinct from the identity, with prime-order
      certificate [mul q G = Infinity] and [q] prime: the multiples of [G]
      annihilated by [mul] are exactly the [q]-multiples, and [mul] is
      injective on residues modulo [q]. *)
  Lemma mul_eq_Infinity_iff (G : point) (q : Z) :
    11 < p ->
    nonsingular ->
    reduced G ->
    on_curve G ->
    G <> Infinity ->
    IsPrime q ->
    mul q G = Infinity ->
    forall n : Z, mul n G = Infinity <-> Z.divide q n.
  Proof.
    intros H11 Hns HrG HoG Hne Hq Hord n.
    assert (H3 : 3 < p) by lia.
    destruct (repr_exists G HoG) as [wG HwG].
    assert (HGne : ~ W.eq wG wzero).
    { destruct G as [|x y]; [exfalso; apply Hne; reflexivity|].
      destruct HwG as (x' & y' & Hcw & _ & _).
      unfold W.eq. rewrite Hcw. cbn. intros Hf. exact Hf. }
    pose proof (proj1 (mul_Infinity_iff_smul_zero H3 H11 Hns G wG HrG HwG q) Hord)
      as Hqz.
    rewrite (mul_Infinity_iff_smul_zero H3 H11 Hns G wG HrG HwG n).
    apply (smul_zero_iff_divide H3 H11 Hns G wG HwG HGne q Hq Hqz n).
  Qed.

  Lemma mul_injective_mod (G : point) (q : Z) :
    11 < p ->
    nonsingular ->
    reduced G ->
    on_curve G ->
    G <> Infinity ->
    IsPrime q ->
    mul q G = Infinity ->
    forall i j : Z, mul i G = mul j G <-> i mod q = j mod q.
  Proof.
    intros H11 Hns HrG HoG Hne Hq Hord i j.
    assert (Hqne : q <> 0) by (pose proof (prime_ge_2 q Hq); lia).
    split.
    - intros Heq.
      assert (Hd : mul (i - j) G = Infinity).
      { replace (i - j) with (i + (- j)) by lia.
        rewrite (mul_add i (- j) G H11 Hns HrG HoG).
        rewrite (mul_neg j G HrG).
        rewrite Heq.
        apply add_neg. }
      apply (proj1 (mul_eq_Infinity_iff G q H11 Hns HrG HoG Hne Hq Hord (i - j)))
        in Hd.
      apply (proj2 (Z.cong_iff_0 i j q)).
      apply (proj2 (Z.mod_divide (i - j) q Hqne)).
      exact Hd.
    - intros Hmod.
      assert (Hd : Z.divide q (i - j)).
      { apply (proj1 (Z.mod_divide (i - j) q Hqne)).
        apply (proj1 (Z.cong_iff_0 i j q)). exact Hmod. }
      apply (proj2 (mul_eq_Infinity_iff G q H11 Hns HrG HoG Hne Hq Hord (i - j)))
        in Hd.
      replace i with (j + (i - j)) by lia.
      rewrite (mul_add j (i - j) G H11 Hns HrG HoG).
      rewrite Hd.
      apply add_Infinity_r.
  Qed.

End Curve.
End Weierstrass.
