(** * A fiat-crypto [field] instance over [Z/pZ]

    This file builds the fiat-crypto field structure
    ([Crypto.Algebra.Hierarchy.field]) directly over Garden's scalar-field
    layer: the carrier is [Z], the equality is congruence modulo [p]
    ([Stdlib.ZArith.Zdiv.eqm p]), and the operations are Garden's
    [UnOp]/[BinOp] reductions modulo [p] together with the extended-Euclid
    [mod_inverse]. It also provides the decidability of [eqm p].

    The instance is the bridge that lets [Garden.EllipticCurve.Weierstrass]
    reuse fiat-crypto's proved affine short-Weierstrass commutative group law.
    To avoid an import cycle this file depends only on [Garden.Field] and
    fiat-crypto; [Weierstrass.v] requires THIS file, never the converse.

    No characteristic or discriminant hypotheses are discharged here: those
    ([char_ge_3], [char_ge_12], [discriminant_nonzero]) are NOT part of the
    [field] record and are supplied at the curve-specific instantiation. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Setoids.Setoid.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Open Scope Z_scope.

Section FiatField.
  Context {p : Z} `{Prime p}.

  (** The multiplicative inverse, written as a one-argument function so it
      matches fiat-crypto's [Finv : F -> F]. *)
  Definition Finv (y : Z) : Z := mod_inverse y p.

  (** ** Congruence modulo [p] as a setoid, with the [Z]-operation morphisms *)

  Local Instance eqm_equiv : Equivalence (eqm p).
  Proof. unfold eqm. constructor; congruence. Qed.

  Local Instance add_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.add := Zplus_eqm p.
  Local Instance sub_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.sub := Zminus_eqm p.
  Local Instance mul_eqm_mor : Proper (eqm p ==> eqm p ==> eqm p) Z.mul := Zmult_eqm p.
  Local Instance opp_eqm_mor : Proper (eqm p ==> eqm p) Z.opp := Zopp_eqm p.

  Lemma p_pos : p <> 0.
  Proof. pose proof (@prime_range p _). lia. Qed.

  (** ** Inverse congruence and the inverse law, re-derived from [Field.Div]

      These mirror the helpers proved inside [Weierstrass.v]; they are reproved
      here so that this file stays independent of [Weierstrass.v]. *)

  Lemma mod_inverse_cong (u v : Z) :
    u mod p = v mod p -> mod_inverse u p = mod_inverse v p.
  Proof.
    intros Huv.
    unfold mod_inverse.
    now rewrite Huv.
  Qed.

  (** The modular inverse inverts any nonzero element, for every prime modulus
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
      unfold BinOp.mul. rewrite Hp2 in *.
      assert (Hm : y mod 2 = 1) by lia.
      assert (Hinv : mod_inverse y 2 = 1).
      { unfold mod_inverse. rewrite Hm. reflexivity. }
      rewrite Hinv, Z.mul_1_l. exact Hm.
    - lia.
  Qed.

  (** ** [Proper] instances for the field operations under [eqm p] *)

  Local Instance add_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.add.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.add.
    repeat setoid_rewrite (Zmod_eqm p).
    exact (add_eqm_mor x x' Hx y y' Hy).
  Qed.

  Local Instance sub_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.sub.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.sub.
    repeat setoid_rewrite (Zmod_eqm p).
    exact (sub_eqm_mor x x' Hx y y' Hy).
  Qed.

  Local Instance mul_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.mul.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.mul.
    repeat setoid_rewrite (Zmod_eqm p).
    exact (mul_eqm_mor x x' Hx y y' Hy).
  Qed.

  Local Instance opp_Proper : Proper (eqm p ==> eqm p) UnOp.opp.
  Proof.
    intros x x' Hx. unfold UnOp.opp.
    repeat setoid_rewrite (Zmod_eqm p).
    exact (opp_eqm_mor x x' Hx).
  Qed.

  Local Instance inv_Proper : Proper (eqm p ==> eqm p) Finv.
  Proof.
    intros x x' Hx. unfold Finv.
    rewrite (mod_inverse_cong x x' Hx). reflexivity.
  Qed.

  Local Instance div_Proper : Proper (eqm p ==> eqm p ==> eqm p) BinOp.div.
  Proof.
    intros x x' Hx y y' Hy. unfold BinOp.div, BinOp.mul.
    repeat setoid_rewrite (Zmod_eqm p).
    rewrite (mod_inverse_cong y y' Hy).
    apply mul_eqm_mor; [exact Hx | reflexivity].
  Qed.

  (** ** A normalizer for the ring-shaped [eqm p] obligations

      It strips every internal [mod p] (via the [Zmod_eqm]/operation morphisms)
      to expose a raw [Z] polynomial identity, then closes it with [ring]. *)
  Ltac fring :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    repeat setoid_rewrite (Zmod_eqm p);
    unfold eqm; f_equal; ring.

  (** ** The additive and multiplicative monoids, group, and (commutative) ring

      The records are assembled in proof mode (not via the [{| ... |}]
      term-mode syntax), because [ring] inside a record-field [ltac:()]
      misresolves the equation relation once the [eqm p] operation morphisms
      are in scope; the same [fring] closes every goal cleanly in proof mode. *)

  Definition monoid_add : @monoid Z (eqm p) BinOp.add 0.
  Proof.
    constructor.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - exact add_Proper.
    - exact eqm_equiv.
  Qed.

  Definition group_add : @group Z (eqm p) BinOp.add 0 UnOp.opp.
  Proof.
    constructor.
    - exact monoid_add.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - exact opp_Proper.
  Qed.

  Definition cgroup_add : @commutative_group Z (eqm p) BinOp.add 0 UnOp.opp.
  Proof.
    constructor.
    - exact group_add.
    - constructor; intros; fring.
  Qed.

  Definition monoid_mul : @monoid Z (eqm p) BinOp.mul 1.
  Proof.
    constructor.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - exact mul_Proper.
    - exact eqm_equiv.
  Qed.

  Definition ring_i :
    @ring Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul.
  Proof.
    constructor.
    - exact cgroup_add.
    - exact monoid_mul.
    - constructor; intros; fring.
    - constructor; intros; fring.
    - intros x y; fring.
    - exact mul_Proper.
    - exact sub_Proper.
  Qed.

  Definition cring_i :
    @commutative_ring Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul.
  Proof.
    constructor.
    - exact ring_i.
    - constructor; intros; fring.
  Qed.

  (** ** The integral-domain "no zero divisors" fact, from Euclid's lemma *)
  Definition zero_product_zero_factor_i :
    @is_zero_product_zero_factor Z (eqm p) 0 BinOp.mul.
  Proof.
    constructor. intros x y Hxy.
    unfold eqm in Hxy. rewrite Z.mod_0_l in Hxy by apply p_pos.
    assert (Hm0 : BinOp.mul x y = 0).
    { unfold BinOp.mul in *. rewrite Z.mod_mod in Hxy by apply p_pos. exact Hxy. }
    apply mul_zero_implies_zero in Hm0.
    unfold eqm. rewrite (Z.mod_0_l p p_pos).
    unfold UnOp.from in Hm0. exact Hm0.
  Qed.

  (** ** The field instance *)

  Global Instance Field_eqm :
    @field Z (eqm p) 0 1 UnOp.opp BinOp.add BinOp.sub BinOp.mul Finv BinOp.div.
  Proof.
    constructor.
    - exact cring_i.
    - constructor. intros x Hx.
      assert (Hx' : x mod p <> 0)
        by (intro Hc; apply Hx; unfold eqm;
            rewrite Hc, Z.mod_0_l by apply p_pos; reflexivity).
      unfold Finv. rewrite (mod_inverse_mul_gen x Hx'). reflexivity.
    - constructor. intro Hc. unfold eqm in Hc.
      rewrite Z.mod_0_l in Hc by apply p_pos.
      rewrite Z.mod_1_l in Hc by (pose proof (@prime_range p _); lia).
      discriminate.
    - intros x y; unfold BinOp.div, Finv; reflexivity.
    - exact inv_Proper.
    - exact div_Proper.
  Qed.

  (** ** Decidability of [eqm p] (fiat-crypto's [Feq_dec]) *)

  Global Instance eqm_dec : DecidableRel (eqm p).
  Proof. intros x y. unfold Decidable, eqm. apply Z.eq_dec. Defined.

End FiatField.
