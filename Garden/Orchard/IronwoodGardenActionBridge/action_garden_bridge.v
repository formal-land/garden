(** * Arithmetic bridge for the translated Garden-shaped Action

    This file contains only representation and elliptic-curve facts used by
    the public Action comparison.  It deliberately has no duplicate Action
    records, input relation, or output function. *)

From Stdlib Require Import List ZArith Lia.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Field.Div.
Require Import Garden.Field.Fermat.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.IronwoodGardenActionBridge.action_garden_generated.
Require Import Garden.Plonky3.M.

Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module ActionGardenBridge.

  (** Garden-side predicates used only to state representation invariants. *)
  Definition baseCanonical (value : Z) : Prop :=
    0 <= value < Primes.pallas_p.

  Definition scalarCanonical (value : Z) : Prop :=
    0 <= value < Primes.pallas_q.

  Definition pointCanonical (point : Point.t) : Prop :=
    baseCanonical point.(Point.x) /\
    baseCanonical point.(Point.y).

  Definition pointIdentity (point : Point.t) : Prop :=
    point.(Point.x) = 0 /\ point.(Point.y) = 0.

  Definition pointOnCurve (point : Point.t) : Prop :=
    point.(Point.y) *F point.(Point.y) =
      point.(Point.x) *F point.(Point.x) *F point.(Point.x) +F
        UnOp.from 5.

  Definition pointValid (point : Point.t) : Prop :=
    pointIdentity point \/ pointOnCurve point.

  Definition from_garden_point (point : Point.t) : ActionGardenZ_Point :=
    {| actionGardenPointX := point.(Point.x); actionGardenPointY := point.(Point.y) |}.

  Definition to_garden_point (point : ActionGardenZ_Point) : Point.t :=
    {| Point.x := point.(actionGardenPointX); Point.y := point.(actionGardenPointY) |}.

  Definition z_poseidon_parameters : ActionGardenZ_PoseidonParameters := {|
    ActionGardenZ_roundConstant := fun round => {|
      ActionGardenZ_x0 := p128pow5t3.round_constant (Z.to_nat round) 0;
      ActionGardenZ_x1 := p128pow5t3.round_constant (Z.to_nat round) 1;
      ActionGardenZ_x2 := p128pow5t3.round_constant (Z.to_nat round) 2
    |};
    ActionGardenZ_mds := {|
      ActionGardenZ_m00 := p128pow5t3.mds_coeff 0 0;
      ActionGardenZ_m01 := p128pow5t3.mds_coeff 0 1;
      ActionGardenZ_m02 := p128pow5t3.mds_coeff 0 2;
      ActionGardenZ_m10 := p128pow5t3.mds_coeff 1 0;
      ActionGardenZ_m11 := p128pow5t3.mds_coeff 1 1;
      ActionGardenZ_m12 := p128pow5t3.mds_coeff 1 2;
      ActionGardenZ_m20 := p128pow5t3.mds_coeff 2 0;
      ActionGardenZ_m21 := p128pow5t3.mds_coeff 2 1;
      ActionGardenZ_m22 := p128pow5t3.mds_coeff 2 2
    |}
  |}.

  Lemma to_from_garden_point (point : Point.t) :
    to_garden_point (from_garden_point point) = point.
  Proof. destruct point; reflexivity. Qed.

  Lemma from_to_garden_point (point : ActionGardenZ_Point) :
    from_garden_point (to_garden_point point) = point.
  Proof. destruct point; reflexivity. Qed.

  Lemma to_garden_point_eq_iff (left right : ActionGardenZ_Point) :
    to_garden_point left = to_garden_point right <-> left = right.
  Proof.
    split.
    - intro H.
      apply (f_equal from_garden_point) in H.
      now rewrite !from_to_garden_point in H.
    - intro H. now subst right.
  Qed.

  (** ** Integer and field representation *)

  Lemma pallas_base_modulus_eq :
    ActionGardenZ_pallasBaseModulus = Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pallas_scalar_modulus_eq :
    ActionGardenZ_pallasScalarModulus = Primes.pallas_q.
  Proof. vm_compute. reflexivity. Qed.

  (** Lean's [Int.ediv]/[Int.emod] use a nonnegative Euclidean remainder
      even when the divisor is negative.  These examples pin the signed and
      zero-divisor cases that differ from applying Rocq's [Z.div]/[Z.modulo]
      directly to a negative divisor. *)
  Example z_div_mod_positive_negative :
    (ActionGardenZ_zDiv 5 (-2), ActionGardenZ_zMod 5 (-2)) = (-2, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example z_div_mod_negative_negative :
    (ActionGardenZ_zDiv (-5) (-2), ActionGardenZ_zMod (-5) (-2)) = (3, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example z_div_mod_negative_positive :
    (ActionGardenZ_zDiv (-5) 2, ActionGardenZ_zMod (-5) 2) = (-3, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example z_div_mod_exact_negative :
    (ActionGardenZ_zDiv 4 (-2), ActionGardenZ_zMod 4 (-2)) = (-2, 0).
  Proof. vm_compute. reflexivity. Qed.

  Example z_div_mod_positive_zero :
    (ActionGardenZ_zDiv 5 0, ActionGardenZ_zMod 5 0) = (0, 5).
  Proof. vm_compute. reflexivity. Qed.

  Example z_div_mod_negative_zero :
    (ActionGardenZ_zDiv (-5) 0, ActionGardenZ_zMod (-5) 0) = (0, -5).
  Proof. vm_compute. reflexivity. Qed.

  Lemma base_normalize_eq (value : Z) :
    ActionGardenZ_baseNormalize value = UnOp.from value.
  Proof.
    unfold ActionGardenZ_baseNormalize, ActionGardenZ_normalize, ActionGardenZ_zMod, UnOp.from.
    rewrite pallas_base_modulus_eq.
    reflexivity.
  Qed.

  Lemma scalar_normalize_eq (value : Z) :
    ActionGardenZ_scalarNormalize value = value mod Primes.pallas_q.
  Proof.
    unfold ActionGardenZ_scalarNormalize, ActionGardenZ_normalize, ActionGardenZ_zMod.
    rewrite pallas_scalar_modulus_eq.
    reflexivity.
  Qed.

  Lemma base_add_eq (left right : Z) :
    ActionGardenZ_baseAdd left right = left +F right.
  Proof.
    unfold ActionGardenZ_baseAdd, ActionGardenZ_addModulo, ActionGardenZ_normalize,
      ActionGardenZ_zMod, ActionGardenZ_zAdd, BinOp.add.
    rewrite pallas_base_modulus_eq.
    reflexivity.
  Qed.

  Lemma base_sub_eq (left right : Z) :
    ActionGardenZ_baseSub left right = left -F right.
  Proof.
    unfold ActionGardenZ_baseSub, ActionGardenZ_subModulo, ActionGardenZ_normalize,
      ActionGardenZ_zMod, ActionGardenZ_zSub, BinOp.sub.
    rewrite pallas_base_modulus_eq.
    reflexivity.
  Qed.

  Lemma base_mul_eq (left right : Z) :
    ActionGardenZ_baseMul left right = left *F right.
  Proof.
    unfold ActionGardenZ_baseMul, ActionGardenZ_mulModulo, ActionGardenZ_normalize,
      ActionGardenZ_zMod, ActionGardenZ_zMul, BinOp.mul.
    rewrite pallas_base_modulus_eq.
    reflexivity.
  Qed.

  Lemma base_neg_eq (value : Z) :
    ActionGardenZ_baseNeg value = -F value.
  Proof.
    unfold ActionGardenZ_baseNeg, ActionGardenZ_negModulo, ActionGardenZ_normalize,
      ActionGardenZ_zMod, ActionGardenZ_zNeg, UnOp.opp.
    rewrite pallas_base_modulus_eq.
    reflexivity.
  Qed.

  Lemma base_equal_eq (left right : Z) :
    ActionGardenZ_baseEqual left right =
      Z.eqb (UnOp.from left) (UnOp.from right).
  Proof.
    unfold ActionGardenZ_baseEqual, ActionGardenZ_zEq.
    rewrite !base_normalize_eq.
    reflexivity.
  Qed.

  Lemma base_canonical_iff (value : Z) :
    ActionGardenZ_baseCanonical value <-> baseCanonical value.
  Proof.
    unfold ActionGardenZ_baseCanonical, baseCanonical.
    rewrite base_normalize_eq.
    unfold UnOp.from.
    pose proof (prime_range (p := Primes.pallas_p)) as Hp.
    split.
    - intro Hcanonical.
      pose proof (Z.mod_pos_bound value Primes.pallas_p ltac:(lia)) as Hrange.
      rewrite Hcanonical in Hrange.
      exact Hrange.
    - intro Hrange.
      apply Z.mod_small.
      exact Hrange.
  Qed.

  Lemma scalar_canonical_iff (value : Z) :
    ActionGardenZ_scalarCanonical value <-> scalarCanonical value.
  Proof.
    unfold ActionGardenZ_scalarCanonical, scalarCanonical.
    rewrite scalar_normalize_eq.
    pose proof (prime_range (p := Primes.pallas_q)) as Hq.
    split.
    - intro Hcanonical.
      pose proof (Z.mod_pos_bound value Primes.pallas_q ltac:(lia)) as Hrange.
      rewrite Hcanonical in Hrange.
      exact Hrange.
    - intro Hrange.
      apply Z.mod_small.
      exact Hrange.
  Qed.

  (** ** Point representation *)

  Lemma point_canonical_iff (point : Point.t) :
    ActionGardenZ_pointCanonical (from_garden_point point) <->
    pointCanonical point.
  Proof.
    destruct point as [px py].
    change
      (ActionGardenZ_baseCanonical px /\ ActionGardenZ_baseCanonical py <->
       baseCanonical px /\ baseCanonical py).
    rewrite !base_canonical_iff.
    reflexivity.
  Qed.

  Lemma point_on_curve_iff (point : Point.t) :
    ActionGardenZ_pointOnCurve (from_garden_point point) <->
    pointOnCurve point.
  Proof.
    destruct point as [px py].
    unfold ActionGardenZ_pointOnCurve, pointOnCurve.
    cbn [from_garden_point].
    rewrite !base_mul_eq, base_add_eq.
    cbn.
    reflexivity.
  Qed.

  Lemma point_normalize_from_canonical
      (point : Point.t) (Hcanonical : pointCanonical point) :
    ActionGardenZ_pointNormalize (from_garden_point point) =
      from_garden_point point.
  Proof.
    destruct point as [px py].
    change (baseCanonical px /\ baseCanonical py) in Hcanonical.
    destruct Hcanonical as [Hx Hy].
    apply base_canonical_iff in Hx.
    apply base_canonical_iff in Hy.
    unfold ActionGardenZ_baseCanonical in Hx, Hy.
    change
      ({| actionGardenPointX := ActionGardenZ_baseNormalize px;
          actionGardenPointY := ActionGardenZ_baseNormalize py |} =
       {| actionGardenPointX := px; actionGardenPointY := py |}).
    now rewrite Hx, Hy.
  Qed.

  Lemma point_identity_iff
      (point : Point.t) (Hcanonical : pointCanonical point) :
    ActionGardenZ_pointNormalize (from_garden_point point) =
      ActionGardenZ_pointIdentity <->
    pointIdentity point.
  Proof.
    rewrite (point_normalize_from_canonical point Hcanonical).
    destruct point as [px py].
    unfold from_garden_point, ActionGardenZ_pointIdentity, pointIdentity.
    cbn.
    split.
    - intro H. inversion H. now split.
    - intros [Hx Hy]. subst px. subst py. reflexivity.
  Qed.

  Lemma point_valid_iff
      (point : Point.t) (Hcanonical : pointCanonical point) :
    ActionGardenZ_pointValid (from_garden_point point) <->
    pointValid point.
  Proof.
    unfold ActionGardenZ_pointValid, pointValid.
    rewrite (point_identity_iff point Hcanonical).
    rewrite point_on_curve_iff.
    reflexivity.
  Qed.

  Lemma zpoint_canonical_iff (point : ActionGardenZ_Point) :
    ActionGardenZ_pointCanonical point <->
    pointCanonical (to_garden_point point).
  Proof.
    rewrite <- (from_to_garden_point point) at 1.
    apply point_canonical_iff.
  Qed.

  Lemma zpoint_on_curve_iff (point : ActionGardenZ_Point) :
    ActionGardenZ_pointOnCurve point <->
    pointOnCurve (to_garden_point point).
  Proof.
    rewrite <- (from_to_garden_point point) at 1.
    apply point_on_curve_iff.
  Qed.

  Lemma zpoint_valid_iff
      (point : ActionGardenZ_Point)
      (Hcanonical : pointCanonical (to_garden_point point)) :
    ActionGardenZ_pointValid point <->
    pointValid (to_garden_point point).
  Proof.
    rewrite <- (from_to_garden_point point) at 1.
    apply point_valid_iff.
    exact Hcanonical.
  Qed.

  Lemma mod_inverse_reduced
      (value modulus : Z) (Hmodulus : 0 < modulus) :
    mod_inverse value modulus mod modulus =
      mod_inverse value modulus.
  Proof.
    unfold mod_inverse.
    destruct modulus; try lia.
    cbn.
    destruct (value mod Z.pos p =? 0);
      [apply Zmod_0_l | apply Zmod_mod];
      lia.
  Qed.

  Lemma garden_mod_inverse_reduced (value : Z) :
    UnOp.from (mod_inverse value Primes.pallas_p) =
      mod_inverse value Primes.pallas_p.
  Proof.
    unfold UnOp.from.
    apply mod_inverse_reduced.
    unfold Primes.pallas_p, Primes.t_p.
    lia.
  Qed.

  Lemma base_inverse_eq (value : Z) :
    ActionGardenZ_baseInverse value =
      mod_inverse value Primes.pallas_p.
  Proof.
    unfold ActionGardenZ_baseInverse, ActionGardenZ_modInverse.
    unfold ActionGardenZ_normalize, ActionGardenZ_zMod.
    rewrite pallas_base_modulus_eq.
    destruct (ActionGardenZ_zEq (value mod Primes.pallas_p) ActionGardenZ_zZero)
      eqn:Hzero.
    - unfold ActionGardenZ_zEq, ActionGardenZ_zZero in Hzero.
      apply Z.eqb_eq in Hzero.
      unfold mod_inverse.
      cbn [Primes.pallas_p Primes.t_p].
      now rewrite Hzero, Zmod_0_l, Z.eqb_refl.
    - unfold ActionGardenZ_zEq, ActionGardenZ_zZero in Hzero.
      apply Z.eqb_neq in Hzero.
      assert (Hp : Znumtheory.prime Primes.pallas_p).
      { exact (@is_prime Primes.pallas_p Primes.PallasPIsPrime). }
      assert (Hstandalone :
          BinOp.mul
            ((value mod Primes.pallas_p) ^
              (Primes.pallas_p - 2) mod Primes.pallas_p)
            value = 1).
      {
        unfold BinOp.mul.
        rewrite Z.mul_comm.
        rewrite <- Zmult_mod_idemp_l.
        apply inv_correct_gen.
        - exact Hp.
        - rewrite Z.mod_mod by
            (unfold Primes.pallas_p, Primes.t_p; lia).
          exact Hzero.
      }
      assert (Hgarden :
          BinOp.mul (mod_inverse value Primes.pallas_p) value = 1).
      {
        apply mod_inverse_mul.
        - unfold Primes.pallas_p, Primes.t_p. lia.
        - exact Hzero.
      }
      assert (Heq :
          UnOp.from
            ((value mod Primes.pallas_p) ^
              (Primes.pallas_p - 2) mod Primes.pallas_p) =
          UnOp.from (mod_inverse value Primes.pallas_p)).
      {
        apply (field_mul_cancel_r _ _ value).
        - exact Hzero.
        - now rewrite Hstandalone, Hgarden.
      }
      unfold ActionGardenZ_zPowNat, ActionGardenZ_zSub, ActionGardenZ_zTwo.
      rewrite Z2Nat.id by
        (unfold Primes.pallas_p, Primes.t_p; lia).
      unfold UnOp.from in Heq.
      rewrite Z.mod_mod in Heq by
        (unfold Primes.pallas_p, Primes.t_p; lia).
      rewrite mod_inverse_reduced in Heq by
        (unfold Primes.pallas_p, Primes.t_p; lia).
      exact Heq.
  Qed.

  Lemma base_div_eq (numerator denominator : Z) :
    ActionGardenZ_baseDiv numerator denominator =
      BinOp.div numerator denominator.
  Proof.
    unfold ActionGardenZ_baseDiv, BinOp.div.
    rewrite base_mul_eq, base_inverse_eq.
    reflexivity.
  Qed.

  Lemma base_equal_canonical_eq
      (left right : Z)
      (Hleft : baseCanonical left)
      (Hright : baseCanonical right) :
    ActionGardenZ_baseEqual left right = Z.eqb left right.
  Proof.
    rewrite base_equal_eq.
    apply base_canonical_iff in Hleft.
    apply base_canonical_iff in Hright.
    unfold ActionGardenZ_baseCanonical in Hleft, Hright.
    rewrite base_normalize_eq in Hleft, Hright.
    now rewrite Hleft, Hright.
  Qed.

  Lemma full_point_on_curve_x_nonzero
      (point : Point.t)
      (Hcurve : pointOnCurve point) :
    UnOp.from point.(Point.x) <> 0.
  Proof.
    destruct point as [px py].
    cbn [Point.x Point.y] in *.
    apply (EccSpec.pallas_curve_x_nonzero px py).
    unfold pointOnCurve in Hcurve.
    cbn [Point.x Point.y] in Hcurve.
    unfold
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b.
    apply sub_zero_equiv.
    rewrite from_sub_reduced.
    rewrite Hcurve.
    field_solve.
  Qed.

  Lemma point_is_identity_x_eq
      (point : Point.t)
      (Hcanonical : pointCanonical point)
      (Hvalid : pointValid point) :
    ActionGardenZ_pointIsIdentity (from_garden_point point) =
      Z.eqb point.(Point.x) 0.
  Proof.
    destruct point as [px py].
    change
      (baseCanonical px /\ baseCanonical py) in Hcanonical.
    destruct Hcanonical as [Hxcanonical Hycanonical].
    unfold pointValid in Hvalid.
    destruct Hvalid as [Hidentity | Hcurve].
    - unfold pointIdentity in Hidentity.
      cbn [Point.x Point.y] in Hidentity.
      destruct Hidentity as [Hx Hy].
      subst px. subst py.
      vm_compute.
      reflexivity.
    - assert (Hxnonzero : px <> 0).
      {
        intro Hzero.
        pose proof
          (full_point_on_curve_x_nonzero
            {| Point.x := px; Point.y := py |} Hcurve) as Hnonzero.
        cbn in Hnonzero.
        apply Hnonzero.
        rewrite Hzero.
        apply FieldRewrite.from_zero.
      }
      unfold ActionGardenZ_pointIsIdentity, from_garden_point.
      cbn.
      rewrite
        (base_equal_canonical_eq px 0 Hxcanonical
          ltac:(unfold baseCanonical; split;
            [lia | unfold Primes.pallas_p, Primes.t_p; lia])).
      rewrite (proj2 (Z.eqb_neq px 0) Hxnonzero).
      reflexivity.
  Qed.

  Lemma point_add_eq
      (left right : Point.t)
      (HleftCanonical : pointCanonical left)
      (HrightCanonical : pointCanonical right)
      (HleftValid : pointValid left)
      (HrightValid : pointValid right) :
    to_garden_point
      (ActionGardenZ_pointAdd
        (from_garden_point left) (from_garden_point right)) =
    EccSpec.point_add left right.
  Proof.
    Strategy transparent [EccSpec.point_add].
    destruct left as [leftX leftY].
    destruct right as [rightX rightY].
    change
      (baseCanonical leftX /\ baseCanonical leftY)
      in HleftCanonical.
    change
      (baseCanonical rightX /\ baseCanonical rightY)
      in HrightCanonical.
    destruct HleftCanonical as [HleftX HleftY].
    destruct HrightCanonical as [HrightX HrightY].
    assert (HleftCanonical' :
        pointCanonical {| Point.x := leftX; Point.y := leftY |})
      by now split.
    assert (HrightCanonical' :
        pointCanonical {| Point.x := rightX; Point.y := rightY |})
      by now split.
    pose proof
      (point_is_identity_x_eq
        {| Point.x := leftX; Point.y := leftY |}
        HleftCanonical' HleftValid) as HleftIdentity.
    pose proof
      (point_is_identity_x_eq
        {| Point.x := rightX; Point.y := rightY |}
        HrightCanonical' HrightValid) as HrightIdentity.
    cbn [Point.x Point.y] in HleftIdentity, HrightIdentity.
    unfold ActionGardenZ_pointAdd, EccSpec.point_add,
      add_proof.CompleteAddition.output.
    rewrite HleftIdentity, HrightIdentity.
    cbn [Point.x Point.y].
    destruct (leftX =? 0) eqn:HleftZero.
    - rewrite
        (point_normalize_from_canonical
          {| Point.x := rightX; Point.y := rightY |}
          HrightCanonical').
      unfold from_garden_point, to_garden_point.
      reflexivity.
    - destruct (rightX =? 0) eqn:HrightZero.
      + rewrite
          (point_normalize_from_canonical
            {| Point.x := leftX; Point.y := leftY |}
            HleftCanonical').
        unfold from_garden_point, to_garden_point.
        reflexivity.
      + unfold from_garden_point, to_garden_point.
        cbn [Point.x Point.y actionGardenPointX actionGardenPointY].
        rewrite
          (base_equal_canonical_eq leftX rightX HleftX HrightX).
        destruct (leftX =? rightX) eqn:HxEqual.
        * assert (Hsum :
              ActionGardenZ_baseEqual
                (ActionGardenZ_baseAdd leftY rightY) ActionGardenZ_zZero =
              Z.eqb (leftY +F rightY) 0).
          {
            rewrite base_equal_eq, base_add_eq.
            unfold ActionGardenZ_zZero.
            autorewrite with field_rewrite.
            reflexivity.
          }
          rewrite Hsum.
          destruct (leftY +F rightY =? 0) eqn:HyInverse.
          -- reflexivity.
          -- assert (Hslope :
                ActionGardenZ_baseDiv
                  (ActionGardenZ_baseAdd
                    (ActionGardenZ_baseMul (Z.of_nat 3)
                      (ActionGardenZ_baseMul leftX leftX))
                    ActionGardenZ_zZero)
                  (ActionGardenZ_baseMul ActionGardenZ_zTwo leftY) =
                BinOp.div
                  (UnOp.from 3 *F
                    Garden.Halo2.halo2_gadgets.utilities_proof.square leftX)
                  (UnOp.from 2 *F leftY)).
             {
               rewrite base_div_eq, base_add_eq.
               rewrite
                 (base_mul_eq (Z.of_nat 3)
                   (ActionGardenZ_baseMul leftX leftX)).
               rewrite (base_mul_eq leftX leftX).
               rewrite (base_mul_eq ActionGardenZ_zTwo leftY).
               unfold ActionGardenZ_zZero, ActionGardenZ_zTwo.
               unfold
                 Garden.Halo2.halo2_gadgets.utilities_proof.square.
               rewrite FieldRewrite.add_zero_right.
               rewrite from_mul_reduced.
               rewrite (mul_left_reduce 3 (leftX *F leftX)).
               rewrite (mul_left_reduce 2 leftY).
               reflexivity.
             }
             rewrite !Hslope, !base_mul_eq, !base_sub_eq.
             unfold
               Garden.Halo2.halo2_gadgets.utilities_proof.square.
             reflexivity.
        * assert (Hslope :
              ActionGardenZ_baseDiv
                (ActionGardenZ_baseSub rightY leftY)
                (ActionGardenZ_baseSub rightX leftX) =
              BinOp.div
                (rightY -F leftY) (rightX -F leftX)).
          {
            now rewrite base_div_eq, !base_sub_eq.
          }
          rewrite !Hslope, !base_mul_eq, !base_sub_eq.
          unfold
            Garden.Halo2.halo2_gadgets.utilities_proof.square.
          reflexivity.
  Qed.

  Lemma point_add_from_eq
      (left right : Point.t)
      (HleftCanonical : pointCanonical left)
      (HrightCanonical : pointCanonical right)
      (HleftValid : pointValid left)
      (HrightValid : pointValid right) :
    ActionGardenZ_pointAdd
      (from_garden_point left) (from_garden_point right) =
      from_garden_point (EccSpec.point_add left right).
  Proof.
    pose proof
      (point_add_eq left right
        HleftCanonical HrightCanonical HleftValid HrightValid) as H.
    apply (f_equal from_garden_point) in H.
    now rewrite from_to_garden_point in H.
  Qed.

  Lemma full_base_canonical_of_reduced
      (value : Z) (Hreduced : UnOp.from value = value) :
    baseCanonical value.
  Proof.
    apply (proj1 (base_canonical_iff value)).
    unfold ActionGardenZ_baseCanonical.
    now rewrite base_normalize_eq.
  Qed.

  Lemma full_base_canonical_reduced
      (value : Z) (Hcanonical : baseCanonical value) :
    UnOp.from value = value.
  Proof.
    apply base_canonical_iff in Hcanonical.
    unfold ActionGardenZ_baseCanonical in Hcanonical.
    now rewrite base_normalize_eq in Hcanonical.
  Qed.

  Lemma full_point_curve_poly
      (point : Point.t) (Hcurve : pointOnCurve point) :
    point.(Point.y) *F point.(Point.y) -F
      (point.(Point.x) *F point.(Point.x) *F point.(Point.x)) -F
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0.
  Proof.
    destruct point as [px py].
    cbn [Point.x Point.y] in *.
    unfold pointOnCurve in Hcurve.
    cbn [Point.x Point.y] in Hcurve.
    unfold
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b.
    apply sub_zero_equiv.
    rewrite from_sub_reduced.
    rewrite Hcurve.
    field_solve.
  Qed.

  Lemma full_point_curve_of_poly
      (point : Point.t)
      (Hpoly :
        point.(Point.y) *F point.(Point.y) -F
          (point.(Point.x) *F point.(Point.x) *F point.(Point.x)) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0) :
    pointOnCurve point.
  Proof.
    destruct point as [px py].
    cbn [Point.x Point.y] in *.
    unfold pointOnCurve.
    cbn [Point.x Point.y].
    unfold
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b in Hpoly.
    apply sub_zero_equiv in Hpoly.
    rewrite from_sub_reduced in Hpoly.
    field_solve.
  Qed.

  Lemma garden_point_add_canonical
      (left right : Point.t)
      (Hleft : pointCanonical left)
      (Hright : pointCanonical right) :
    pointCanonical (EccSpec.point_add left right).
  Proof.
    Strategy transparent [EccSpec.point_add].
    destruct left as [leftX leftY].
    destruct right as [rightX rightY].
    change
      (baseCanonical leftX /\ baseCanonical leftY) in Hleft.
    change
      (baseCanonical rightX /\ baseCanonical rightY) in Hright.
    destruct Hleft as [HleftX HleftY].
    destruct Hright as [HrightX HrightY].
    unfold EccSpec.point_add, add_proof.CompleteAddition.output.
    cbn [Point.x Point.y].
    destruct (leftX =? 0).
    - now split.
    - destruct (rightX =? 0).
      + now split.
      + destruct ((leftX =? rightX) && (leftY +F rightY =? 0))%bool.
        * split;
            apply full_base_canonical_of_reduced;
            apply FieldRewrite.from_zero.
        * destruct (leftX =? rightX);
            split;
            apply full_base_canonical_of_reduced;
            apply from_sub_reduced.
  Qed.

  Lemma garden_point_add_valid
      (left right : Point.t)
      (HleftCanonical : pointCanonical left)
      (HrightCanonical : pointCanonical right)
      (HleftValid : pointValid left)
      (HrightValid : pointValid right) :
    pointValid (EccSpec.point_add left right).
  Proof.
    unfold pointValid in HleftValid, HrightValid |- *.
    destruct HleftValid as [HleftIdentity | HleftCurve].
    - destruct left as [leftX leftY].
      unfold pointIdentity in HleftIdentity.
      cbn [Point.x Point.y] in HleftIdentity.
      destruct HleftIdentity as [HleftX HleftY].
      subst leftX. subst leftY.
      Strategy transparent [EccSpec.point_add].
      unfold EccSpec.point_add, add_proof.CompleteAddition.output.
      cbn [Point.x Point.y].
      exact HrightValid.
    - destruct HrightValid as [HrightIdentity | HrightCurve].
      + destruct right as [rightX rightY].
        unfold pointIdentity in HrightIdentity.
        cbn [Point.x Point.y] in HrightIdentity.
        destruct HrightIdentity as [HrightX HrightY].
        subst rightX. subst rightY.
        pose proof (full_point_on_curve_x_nonzero left HleftCurve)
          as HleftXNonzero.
        assert (HleftXRaw : left.(Point.x) <> 0).
        {
          intro Hzero.
          apply HleftXNonzero.
          now rewrite Hzero, FieldRewrite.from_zero.
        }
        Strategy transparent [EccSpec.point_add].
        unfold EccSpec.point_add, add_proof.CompleteAddition.output.
        rewrite (proj2 (Z.eqb_neq _ _) HleftXRaw).
        cbn [Point.x Point.y].
        now right.
      + destruct HleftCanonical as [HleftXReduced HleftYReduced].
        destruct HrightCanonical as [HrightXReduced HrightYReduced].
        pose proof
          (PallasModel.point_add_curve_poly_or_identity left right
            (full_base_canonical_reduced _ HleftXReduced)
            (full_base_canonical_reduced _ HleftYReduced)
            (full_base_canonical_reduced _ HrightXReduced)
            (full_base_canonical_reduced _ HrightYReduced)
            (full_point_curve_poly left HleftCurve)
            (full_point_curve_poly right HrightCurve)) as Hresult.
        destruct Hresult as [Hcurve | Hidentity].
        * right. now apply full_point_curve_of_poly.
        * left.
          rewrite Hidentity.
          unfold pointIdentity, EccSpec.identity.
          split; reflexivity.
  Qed.

  Lemma point_nat_mul_properties
      (scalar : nat) (point : Point.t)
      (Hcanonical : pointCanonical point)
      (Hvalid : pointValid point) :
    to_garden_point
      (ActionGardenZ_pointNatMul scalar (from_garden_point point)) =
        EccSpec.scalar_mul (Z.of_nat scalar) point /\
    pointCanonical
      (EccSpec.scalar_mul (Z.of_nat scalar) point) /\
    pointValid
      (EccSpec.scalar_mul (Z.of_nat scalar) point).
  Proof.
    induction scalar as [| scalar IH].
    - cbn [ActionGardenZ_pointNatMul EccSpec.scalar_mul].
      split.
      + reflexivity.
      + split.
        * unfold pointCanonical, EccSpec.identity.
          split; apply full_base_canonical_of_reduced;
            apply FieldRewrite.from_zero.
        * unfold pointValid, pointIdentity, EccSpec.identity.
          left. split; reflexivity.
    - destruct IH as (Heq & HpreviousCanonical & HpreviousValid).
      assert (HzCanonical :
          pointCanonical
            (to_garden_point
              (ActionGardenZ_pointNatMul scalar (from_garden_point point)))).
      { now rewrite Heq. }
      assert (HzValid :
          pointValid
            (to_garden_point
              (ActionGardenZ_pointNatMul scalar (from_garden_point point)))).
      { now rewrite Heq. }
      rewrite PallasModel.scalar_mul_succ_nat.
      cbn [ActionGardenZ_pointNatMul].
      split.
      + rewrite <-
          (from_to_garden_point
            (ActionGardenZ_pointNatMul scalar (from_garden_point point))).
        rewrite
          (point_add_eq
            (to_garden_point
              (ActionGardenZ_pointNatMul scalar (from_garden_point point)))
            point HzCanonical Hcanonical HzValid Hvalid).
        now rewrite Heq.
      + split.
        * apply garden_point_add_canonical; assumption.
        * apply garden_point_add_valid; assumption.
  Qed.

  Lemma scalar_mul_eq
      (scalar : Z) (point : Point.t)
      (Hscalar : scalarCanonical scalar)
      (HpointCanonical : pointCanonical point)
      (HpointValid : pointValid point) :
    to_garden_point
      (ActionGardenZ_scalarMul scalar (from_garden_point point)) =
      EccSpec.scalar_mul scalar point.
  Proof.
    pose proof (proj2 (scalar_canonical_iff scalar) Hscalar)
      as HscalarStandalone.
    unfold ActionGardenZ_scalarCanonical in HscalarStandalone.
    unfold ActionGardenZ_scalarMul.
    rewrite HscalarStandalone.
    assert (Hnonnegative : 0 <= scalar) by
      (unfold scalarCanonical in Hscalar; lia).
    rewrite <- (Z2Nat.id scalar Hnonnegative) at 2.
    exact
      (proj1
        (point_nat_mul_properties
          (Z.to_nat scalar) point HpointCanonical HpointValid)).
  Qed.


  Lemma words_le_in_range
      (count : nat) (value word : Z)
      (Hword : In word (SinsemillaSpec.words_le count value)) :
    0 <= word < 1024.
  Proof.
    revert value word Hword.
    induction count as [| count IH]; intros value word Hword.
    - contradiction.
    - cbn [SinsemillaSpec.words_le] in Hword.
      destruct Hword as [Hhead | Htail].
      + subst word.
        apply Z.mod_pos_bound.
        lia.
      + exact (IH _ _ Htail).
  Qed.

End ActionGardenBridge.
