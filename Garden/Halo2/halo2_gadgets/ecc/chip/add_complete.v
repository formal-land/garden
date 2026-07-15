(** * Completeness of the complete-addition chip

    Dual of [add_proof]: for any two reduced points that are on the Pallas
    curve or are the [(0, 0)] identity sentinel — the same input reading as
    the soundness side ([witness_point_proof.sound] and
    [EccSpec.pallas_curve_x_nonzero] use exactly this curve-or-sentinel
    disjunction) — there is an assignment satisfying [circuit_holds] for the
    [add] chip whose advice plane carries the inputs at the gate's input
    cells (A0-A3 at row 0) and [CompleteAddition.output] at the result cells
    (A2/A3 at row 1).

    The assignment is built explicitly: honest selector/fixed/lookup planes
    via [Complete.circuit_holds_intro] (the generic gluing introduction
    lemma), and an advice plane from the complete-addition witness formulas
    — the case-split gradient [lambda_w] via [mod_inverse], the witnessed
    inverses [alpha_w]/[beta_w]/[gamma_w]/[delta_w], and the output
    coordinates of [CompleteAddition.output].  The single enabled point
    leaves the twelve gate polynomials, discharged by field algebra over
    the case split [x_p = 0] / [x_q = 0] / [x_p = x_q] / [y_p + y_q = 0].

    Two concrete Pallas facts feed the exceptional cases: [b = 5] is not a
    square ([EccSpec.pallas_b_quadratic_nonresidue], so [x = 0] never lies
    on the curve and the sentinel is unambiguous), and [-b = -5] is not a
    cube ([pallas_neg_b_cubic_nonresidue] below, so [y = 0] never lies on
    the curve and the tangent gradient of the doubling branch is always
    defined). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Import Garden.Field.Fermat.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.Bool.Bool.

#[local] Existing Instance Primes.PallasPIsPrime.

(* [Field.Fermat] (via [ecc.chip.spec]) loads ssreflect, which turns bullet
   discipline off; the proofs below rely on bullets focusing subgoals. *)
#[local] Set Bullet Behavior "Strict Subproofs".

Global Open Scope Z_scope.

Module CompleteAdditionCompleteness.
  (** The input reading of the soundness side: a witnessed point is on the
      curve ([curve_eqn] evaluates to zero) or is the [(0, 0)] identity
      sentinel — the disjunction established by [WitnessPoint.sound]. *)
  Definition on_curve_or_identity (x y : Z) : Prop :=
    y *F y -F (x *F x *F x) -F
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0 \/
    (x = 0 /\ y = 0).

  Definition add_region : RegionId.t :=
    RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd.

  Definition add_facts : list (Fact.t columns RegionId.t) :=
    layouter_facts Garden.Halo2.halo2_gadgets.ecc.chip.add.synthesize.

  (** ** The advice-plane witness formulas

      Mirrors the prover's [Assigned] values in the Rust chip: the gradient
      [lambda_w] (secant, or tangent on the doubling branch), and the
      witnessed inverses that select the exceptional cases ([inv0]
      semantics: the inverse of a nonzero element, [0] otherwise). *)

  Definition lambda_w (x_p y_p x_q y_q : Z) : Z :=
    if x_p =? x_q then
      if y_p =? 0 then 0
      else BinOp.div (UnOp.from 3 *F square x_p) (UnOp.from 2 *F y_p)
    else BinOp.div (y_q -F y_p) (x_q -F x_p).

  Definition alpha_w (x_p x_q : Z) : Z :=
    if x_p =? x_q then 0 else mod_inverse (x_q -F x_p) Primes.pallas_p.

  Definition beta_w (x_p : Z) : Z :=
    if x_p =? 0 then 0 else mod_inverse x_p Primes.pallas_p.

  Definition gamma_w (x_q : Z) : Z :=
    if x_q =? 0 then 0 else mod_inverse x_q Primes.pallas_p.

  Definition delta_w (x_p y_p x_q y_q : Z) : Z :=
    if x_p =? x_q then
      if (y_p +F y_q) =? 0 then 0
      else mod_inverse (y_q +F y_p) Primes.pallas_p
    else 0.

  Definition advice_w (x_p y_p x_q y_q : Z)
      (column : Advice.t) (_region : RegionId.t) (row : Z) : Z :=
    if row =? 0 then
      match column with
      | Advice.A0 => x_p
      | Advice.A1 => y_p
      | Advice.A2 => x_q
      | Advice.A3 => y_q
      | Advice.A4 => lambda_w x_p y_p x_q y_q
      | Advice.A5 => alpha_w x_p x_q
      | Advice.A6 => beta_w x_p
      | Advice.A7 => gamma_w x_q
      | Advice.A8 => delta_w x_p y_p x_q y_q
      | Advice.A9 => 0
      end
    else if row =? 1 then
      match column with
      | Advice.A2 => (CompleteAddition.output x_p y_p x_q y_q).(Point.x)
      | Advice.A3 => (CompleteAddition.output x_p y_p x_q y_q).(Point.y)
      | _ => 0
      end
    else 0.

  (** The honest assignment: indicator selector plane on the synthesis-
      enabled points, all-zero fixed/instance/lookup planes (the [add]
      program writes no fixed cell and loads no table), and the witness
      advice plane. *)
  Definition witness_assignment (x_p y_p x_q y_q : Z)
      : Assignment.t columns RegionId.t := {|
    Assignment.selector selector region offset :=
      if Complete.enabled_memb
           OrchardDecidableEq.selector_eqb OrchardDecidableEq.region_id_eqb
           add_facts selector region offset
      then 1 else 0;
    Assignment.fixed _ _ _ := 0;
    Assignment.advice := advice_w x_p y_p x_q y_q;
    Assignment.instance_ _ _ := 0;
    Assignment.lookup _ _ := 0;
  |}.

  (** ** Field-algebra helpers *)

  Lemma from_reduced (x : Z) (Hx : 0 <= x < Primes.pallas_p) :
    UnOp.from x = x.
  Proof.
    unfold UnOp.from.
    apply Z.mod_small.
    exact Hx.
  Qed.

  Lemma sub_self (x : Z) : x -F x = 0.
  Proof.
    unfold BinOp.sub.
    rewrite Z.sub_diag.
    apply Zmod_0_l.
  Qed.

  Lemma sub_nonzero_from (a b : Z)
      (Ha : UnOp.from a = a) (Hb : UnOp.from b = b) (Hne : a <> b) :
    UnOp.from (a -F b) <> 0.
  Proof.
    rewrite FieldRewrite.from_sub.
    intros Hz.
    apply sub_zero_equiv in Hz.
    rewrite Ha, Hb in Hz.
    exact (Hne Hz).
  Qed.

  Lemma mul_inverse_r (y : Z) (Hy : UnOp.from y <> 0) :
    y *F mod_inverse y Primes.pallas_p = 1.
  Proof.
    rewrite field_mul_comm.
    apply mod_inverse_mul_prime.
    exact Hy.
  Qed.

  Lemma mul_div_r (a d : Z) (Hd : UnOp.from d <> 0) :
    d *F BinOp.div a d = UnOp.from a.
  Proof.
    rewrite field_mul_comm.
    apply div_mul.
    - unfold Primes.pallas_p, Primes.t_p; lia.
    - exact Hd.
  Qed.

  Lemma from_two_nonzero : UnOp.from (UnOp.from 2) <> 0.
  Proof.
    rewrite FieldRewrite.from_from.
    rewrite (from_reduced 2)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    lia.
  Qed.

  (** ** Concrete Pallas fact: [-b = -5] is not a cube

      Companion of [EccSpec.pallas_b_quadratic_nonresidue]: it records the
      cubic-residue status of one field element, via the computed value of
      [(p - 5) ^ ((p - 1) / 3) mod p] (which is [<> 1], while a cube's
      [(p-1)/3]-th power is [x ^ (p-1) = 1] by Fermat).  Consequence: no
      Pallas point has [y = 0] (such a point would satisfy [x³ = -5]). *)
  Lemma pallas_neg_b_cubic_nonresidue :
    forall x : Z,
      UnOp.from (- (x *F x *F x)) <>
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b.
  Proof.
    intros x Hx.
    set (p := Primes.pallas_p) in *.
    set (e := (p - 1) / 3) in *.
    assert (Hpprime : Znumtheory.prime p).
    { subst p.
      pose proof (@is_prime Primes.pallas_p Primes.PallasPIsPrime) as Hp.
      exact Hp. }
    assert (Hpgt5 : 5 < p)
      by (subst p; unfold Primes.pallas_p, Primes.t_p; lia).
    assert (Htriple : 3 * e = p - 1)
      by (subst e; subst p; unfold Primes.pallas_p, Primes.t_p; cbn; lia).
    (* The hypothesis says the reduced cube is [p - 5], i.e. [x³ ≡ -5]. *)
    assert (Hcube : (x * x * x) mod p = p - 5).
    { unfold Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b in Hx.
      unfold UnOp.from, BinOp.mul in Hx.
      rewrite Zmult_mod_idemp_l in Hx.
      rewrite (Z.mod_small 5 p) in Hx by lia.
      pose proof (Z.mod_pos_bound (x * x * x) p ltac:(lia)) as Hcb.
      set (c := (x * x * x) mod p) in *.
      destruct (Z.eqb_spec c 0) as [Hc0 | Hc0].
      - exfalso.
        rewrite Hc0 in Hx.
        replace (- 0) with 0 in Hx by lia.
        rewrite Zmod_0_l in Hx.
        lia.
      - assert (Hneg : (- c) mod p = p - c).
        { rewrite Z.mod_opp_l_nz;
            [| lia | rewrite Z.mod_small by lia; exact Hc0].
          rewrite Z.mod_small by lia.
          reflexivity. }
        rewrite Hneg in Hx.
        lia. }
    assert (Hxnz : x mod p <> 0).
    { intros H0.
      apply Z.mod_divide in H0; [| lia].
      assert (Hdiv : (x * x * x) mod p = 0).
      { apply Z.mod_divide; [lia |].
        apply Z.divide_mul_r.
        exact H0. }
      rewrite Hdiv in Hcube.
      lia. }
    assert (He_pos : 0 < e) by lia.
    assert (Hfermat : (x ^ (p - 1)) mod p = 1).
    { pose proof (Z.mod_pos_bound x p ltac:(lia)) as Hxb.
      pose proof (flt_pow_pred (x mod p) p Hpprime ltac:(lia)) as Hflt.
      rewrite Zpower_mod by lia.
      exact Hflt. }
    assert (Hpow_one : ((p - 5) ^ e) mod p = 1).
    { rewrite <- Hcube.
      rewrite <- Zpower_mod by lia.
      replace (x * x * x) with (x ^ 3) by ring.
      rewrite <- Z.pow_mul_r by lia.
      rewrite Htriple.
      exact Hfermat. }
    assert (Hcompute :
        fast_pow_modulo_positive 1 (p - 5) p (Z.to_pos e) =
        20444556541222657078399132219657928148671392403212669005631716460534733845831).
    { subst e; subst p.
      vm_compute.
      reflexivity. }
    pose proof (fast_pow_correct p ltac:(lia) (Z.to_pos e) 1 (p - 5)) as Hfast.
    rewrite Hcompute in Hfast.
    rewrite Z2Pos.id in Hfast by lia.
    rewrite Z.mul_1_l in Hfast.
    rewrite Hpow_one in Hfast.
    lia.
  Qed.

  (** No on-curve point has [y = 0]. *)
  Lemma pallas_curve_y_nonzero (x y : Z)
      (Hcurve : y *F y -F (x *F x *F x) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (Hy : UnOp.from y = 0) : False.
  Proof.
    apply (pallas_neg_b_cubic_nonresidue x).
    apply sub_zero_equiv in Hcurve.
    rewrite FieldRewrite.from_sub in Hcurve.
    assert (Hyy : y *F y = 0).
    { unfold BinOp.mul.
      unfold UnOp.from in Hy.
      rewrite <- Zmult_mod_idemp_l, Hy, Z.mul_0_l.
      apply Zmod_0_l. }
    rewrite Hyy in Hcurve.
    rewrite FieldRewrite.sub_zero_left in Hcurve.
    exact Hcurve.
  Qed.

  (** The [x = 0] leg of the sentinel encoding: [x = 0] is not on the curve
      ([EccSpec.pallas_b_quadratic_nonresidue]), so an
      [on_curve_or_identity] point with [x = 0] is the sentinel. *)
  Lemma x_zero_forces_y_zero (x y : Z)
      (Hpoint : on_curve_or_identity x y) (Hx0 : x = 0) : y = 0.
  Proof.
    destruct Hpoint as [Hcurve | [_ Hy0] ]; [| exact Hy0].
    exfalso.
    apply (EccSpec.pallas_curve_x_nonzero x y Hcurve).
    rewrite Hx0.
    reflexivity.
  Qed.

  (** Two reduced on-curve points with the same [x] whose [y]-sum is
      nonzero have equal [y] (their squares agree, and [y2 <> -y1]). *)
  Lemma same_x_equal_y (x y1 y2 : Z)
      (Hy1 : 0 <= y1 < Primes.pallas_p)
      (Hy2 : 0 <= y2 < Primes.pallas_p)
      (H1 : y1 *F y1 -F (x *F x *F x) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (H2 : y2 *F y2 -F (x *F x *F x) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (Hs : y1 +F y2 <> 0) : y2 = y1.
  Proof.
    apply sub_zero_equiv in H1, H2.
    rewrite FieldRewrite.from_sub in H1, H2.
    assert (Heq : y1 *F y1 -F (x *F x *F x) = y2 *F y2 -F (x *F x *F x))
      by (rewrite H1, H2; reflexivity).
    assert (Hcancel : (y1 *F y1) -F (y2 *F y2) =
        (y1 *F y1 -F (x *F x *F x)) -F (y2 *F y2 -F (x *F x *F x)))
      by mod_ring_solve.
    rewrite Heq in Hcancel.
    rewrite sub_self in Hcancel.
    assert (Hfac : (y1 -F y2) *F (y1 +F y2) = (y1 *F y1) -F (y2 *F y2))
      by mod_ring_solve.
    rewrite Hcancel in Hfac.
    apply mul_zero_implies_zero in Hfac.
    destruct Hfac as [Hz | Hz].
    - rewrite FieldRewrite.from_sub in Hz.
      apply sub_zero_equiv in Hz.
      rewrite (from_reduced y1 Hy1), (from_reduced y2 Hy2) in Hz.
      symmetry; exact Hz.
    - exfalso.
      rewrite FieldRewrite.from_add in Hz.
      exact (Hs Hz).
  Qed.

  (** ** The twelve gate polynomials hold on the witness values

      One conjunct per named constraint of [complete_addition_gate], in the
      exact shape the gate evaluates to on [witness_assignment] (after
      stripping the reduced-operand [UnOp.from] wrappers). *)
  Lemma witness_polys (x_p y_p x_q y_q : Z)
      (Hx_p : 0 <= x_p < Primes.pallas_p)
      (Hy_p : 0 <= y_p < Primes.pallas_p)
      (Hx_q : 0 <= x_q < Primes.pallas_p)
      (Hy_q : 0 <= y_q < Primes.pallas_p)
      (HP : on_curve_or_identity x_p y_p)
      (HQ : on_curve_or_identity x_q y_q) :
    let lam := lambda_w x_p y_p x_q y_q in
    let al := alpha_w x_p x_q in
    let be := beta_w x_p in
    let ga := gamma_w x_q in
    let de := delta_w x_p y_p x_q y_q in
    let x_r := (CompleteAddition.output x_p y_p x_q y_q).(Point.x) in
    let y_r := (CompleteAddition.output x_p y_p x_q y_q).(Point.y) in
    ((x_q -F x_p) *F ((x_q -F x_p) *F lam -F (y_q -F y_p)) = 0) /\
    ((1 -F (x_q -F x_p) *F al) *F
      (2 *F y_p *F lam -F 3 *F (x_p *F x_p)) = 0) /\
    (x_p *F x_q *F (x_q -F x_p) *F
      (lam *F lam -F x_p -F x_q -F x_r) = 0) /\
    (x_p *F x_q *F (x_q -F x_p) *F
      (lam *F (x_p -F x_r) -F y_p -F y_r) = 0) /\
    (x_p *F x_q *F (y_q +F y_p) *F
      (lam *F lam -F x_p -F x_q -F x_r) = 0) /\
    (x_p *F x_q *F (y_q +F y_p) *F
      (lam *F (x_p -F x_r) -F y_p -F y_r) = 0) /\
    ((1 -F x_p *F be) *F (x_r -F x_q) = 0) /\
    ((1 -F x_p *F be) *F (y_r -F y_q) = 0) /\
    ((1 -F x_q *F ga) *F (x_r -F x_p) = 0) /\
    ((1 -F x_q *F ga) *F (y_r -F y_p) = 0) /\
    ((1 -F (x_q -F x_p) *F al -F (y_q +F y_p) *F de) *F x_r = 0) /\
    ((1 -F (x_q -F x_p) *F al -F (y_q +F y_p) *F de) *F y_r = 0).
  Proof.
    cbv zeta.
    pose proof (from_reduced x_p Hx_p) as Fxp.
    pose proof (from_reduced y_p Hy_p) as Fyp.
    pose proof (from_reduced x_q Hx_q) as Fxq.
    pose proof (from_reduced y_q Hy_q) as Fyq.
    unfold lambda_w, alpha_w, beta_w, gamma_w, delta_w,
      CompleteAddition.output, square.
    destruct (Z.eqb_spec x_p 0) as [Hxp0 | Hxp0].
    { (* P is the sentinel. *)
      assert (Hyp0 : y_p = 0) by exact (x_zero_forces_y_zero x_p y_p HP Hxp0).
      subst x_p; subst y_p.
      destruct (Z.eqb_spec x_q 0) as [Hxq0 | Hxq0].
      { (* Q is the sentinel too: everything is concrete. *)
        assert (Hyq0 : y_q = 0)
          by exact (x_zero_forces_y_zero x_q y_q HQ Hxq0).
        subst x_q; subst y_q.
        repeat apply conj; vm_compute; reflexivity. }
      { (* R = Q: the [beta] case. *)
        destruct HQ as [HQc | [Hq0 _] ]; [| easy].
        assert (Hpq : (0 =? x_q) = false)
          by (apply Z.eqb_neq; congruence).
        rewrite Hpq.
        cbn [andb Z.eqb].
        assert (Hqz : UnOp.from x_q <> 0) by (rewrite Fxq; exact Hxq0).
        assert (Hd : UnOp.from (x_q -F 0) <> 0)
          by (apply sub_nonzero_from;
              [exact Fxq | reflexivity | congruence]).
        repeat apply conj.
        - rewrite (mul_div_r (y_q -F 0) (x_q -F 0) Hd).
          rewrite FieldRewrite.from_sub.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite (mul_inverse_r (x_q -F 0) Hd).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite FieldRewrite.mul_zero_left.
          rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite FieldRewrite.mul_zero_left.
          rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite (mul_inverse_r x_q Hqz).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite (mul_inverse_r x_q Hqz).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite (mul_inverse_r (x_q -F 0) Hd).
          rewrite FieldRewrite.mul_zero_right.
          rewrite !sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite (mul_inverse_r (x_q -F 0) Hd).
          rewrite FieldRewrite.mul_zero_right.
          rewrite !sub_self.
          apply FieldRewrite.mul_zero_left. } }
    { (* P is on the curve. *)
      destruct HP as [HPc | [Hp0 _] ]; [| easy].
      assert (Hpz : UnOp.from x_p <> 0) by (rewrite Fxp; exact Hxp0).
      destruct (Z.eqb_spec x_q 0) as [Hxq0 | Hxq0].
      { (* R = P: the [gamma] case. *)
        assert (Hyq0 : y_q = 0)
          by exact (x_zero_forces_y_zero x_q y_q HQ Hxq0).
        subst x_q; subst y_q.
        assert (Hpq : (x_p =? 0) = false) by (apply Z.eqb_neq; exact Hxp0).
        rewrite Hpq.
        cbn [andb Z.eqb].
        assert (Hd : UnOp.from (0 -F x_p) <> 0)
          by (apply sub_nonzero_from;
              [reflexivity | exact Fxp | congruence]).
        repeat apply conj.
        - rewrite (mul_div_r (0 -F y_p) (0 -F x_p) Hd).
          rewrite FieldRewrite.from_sub.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite (mul_inverse_r (0 -F x_p) Hd).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite FieldRewrite.mul_zero_right,
            !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite FieldRewrite.mul_zero_right,
            !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite FieldRewrite.mul_zero_right,
            !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite FieldRewrite.mul_zero_right,
            !FieldRewrite.mul_zero_left; reflexivity.
        - rewrite (mul_inverse_r x_p Hpz).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite (mul_inverse_r x_p Hpz).
          rewrite sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite FieldRewrite.mul_zero_left.
          rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite FieldRewrite.mul_zero_left.
          rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
          rewrite sub_self.
          apply FieldRewrite.mul_zero_right.
        - rewrite (mul_inverse_r (0 -F x_p) Hd).
          rewrite FieldRewrite.mul_zero_right.
          rewrite !sub_self.
          apply FieldRewrite.mul_zero_left.
        - rewrite (mul_inverse_r (0 -F x_p) Hd).
          rewrite FieldRewrite.mul_zero_right.
          rewrite !sub_self.
          apply FieldRewrite.mul_zero_left. }
      { (* Both x-coordinates nonzero. *)
        destruct HQ as [HQc | [Hq0 _] ]; [| easy].
        assert (Hqz : UnOp.from x_q <> 0) by (rewrite Fxq; exact Hxq0).
        destruct (Z.eqb_spec x_p x_q) as [Hpq | Hpq].
        { (* Equal x-coordinates. *)
          subst x_q.
          destruct (Z.eqb_spec y_p 0) as [Hyp0 | Hyp0].
          { (* [y_p = 0] on the curve: impossible ([-5] is not a cube). *)
            exfalso.
            apply (pallas_curve_y_nonzero x_p y_p HPc).
            rewrite Hyp0; reflexivity. }
          assert (Hden : UnOp.from (UnOp.from 2 *F y_p) <> 0).
          { apply field_from_mul_nonzero.
            - exact from_two_nonzero.
            - rewrite Fyp; exact Hyp0. }
          destruct (Z.eqb_spec (y_p +F y_q) 0) as [Hs0 | Hs0].
          { (* P = -Q: the [delta]-free identity output. *)
            cbn [andb].
            assert (Hsq : y_q +F y_p = 0)
              by (rewrite field_add_comm; exact Hs0).
            repeat apply conj.
            - rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite FieldRewrite.mul_zero_right.
              rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
              rewrite FieldRewrite.mul_one_left.
              rewrite FieldRewrite.from_sub.
              rewrite <- (FieldRewrite.mul_from_left 2 y_p).
              rewrite (mul_div_r (UnOp.from 3 *F (x_p *F x_p))
                (UnOp.from 2 *F y_p) Hden).
              rewrite FieldRewrite.from_mul, FieldRewrite.mul_from_left.
              apply sub_self.
            - rewrite sub_self, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite sub_self, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite Hsq, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite Hsq, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hpz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hpz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hqz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hqz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - apply FieldRewrite.mul_zero_right.
            - apply FieldRewrite.mul_zero_right. }
          { (* Doubling: the tangent case. *)
            assert (Hyq : y_q = y_p)
              by exact (same_x_equal_y x_p y_p y_q Hy_p Hy_q HPc HQc Hs0).
            subst y_q.
            cbn [andb].
            assert (Hsz : UnOp.from (y_p +F y_p) <> 0)
              by (rewrite FieldRewrite.from_add; exact Hs0).
            repeat apply conj.
            - rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite FieldRewrite.mul_zero_right.
              rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
              rewrite FieldRewrite.mul_one_left.
              rewrite FieldRewrite.from_sub.
              rewrite <- (FieldRewrite.mul_from_left 2 y_p).
              rewrite (mul_div_r (UnOp.from 3 *F (x_p *F x_p))
                (UnOp.from 2 *F y_p) Hden).
              rewrite FieldRewrite.from_mul, FieldRewrite.mul_from_left.
              apply sub_self.
            - rewrite sub_self, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite sub_self, FieldRewrite.mul_zero_right.
              apply FieldRewrite.mul_zero_left.
            - rewrite sub_self.
              apply FieldRewrite.mul_zero_right.
            - rewrite sub_self.
              apply FieldRewrite.mul_zero_right.
            - rewrite (mul_inverse_r x_p Hpz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hpz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hqz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite (mul_inverse_r x_p Hqz).
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite FieldRewrite.mul_zero_right.
              rewrite (mul_inverse_r (y_p +F y_p) Hsz).
              rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left.
            - rewrite FieldRewrite.mul_zero_right.
              rewrite (mul_inverse_r (y_p +F y_p) Hsz).
              rewrite FieldRewrite.sub_zero_right, FieldRewrite.from_one.
              rewrite sub_self.
              apply FieldRewrite.mul_zero_left. } }
        { (* Distinct nonzero x-coordinates: the generic secant case. *)
          assert (Hd : UnOp.from (x_q -F x_p) <> 0)
            by (apply sub_nonzero_from; [exact Fxq | exact Fxp | congruence]).
          cbn [andb].
          repeat apply conj.
          - rewrite (mul_div_r (y_q -F y_p) (x_q -F x_p) Hd).
            rewrite FieldRewrite.from_sub.
            rewrite sub_self.
            apply FieldRewrite.mul_zero_right.
          - rewrite (mul_inverse_r (x_q -F x_p) Hd).
            rewrite sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite sub_self.
            apply FieldRewrite.mul_zero_right.
          - rewrite sub_self.
            apply FieldRewrite.mul_zero_right.
          - rewrite sub_self.
            apply FieldRewrite.mul_zero_right.
          - rewrite sub_self.
            apply FieldRewrite.mul_zero_right.
          - rewrite (mul_inverse_r x_p Hpz).
            rewrite sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite (mul_inverse_r x_p Hpz).
            rewrite sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite (mul_inverse_r x_q Hqz).
            rewrite sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite (mul_inverse_r x_q Hqz).
            rewrite sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite (mul_inverse_r (x_q -F x_p) Hd).
            rewrite FieldRewrite.mul_zero_right.
            rewrite !sub_self.
            apply FieldRewrite.mul_zero_left.
          - rewrite (mul_inverse_r (x_q -F x_p) Hd).
            rewrite FieldRewrite.mul_zero_right.
            rewrite !sub_self.
            apply FieldRewrite.mul_zero_left. } } }
  Qed.

  (** ** Completeness of the [add] chip

      For any reduced curve-or-identity input pair there is an assignment
      accepted by the whole chip ([circuit_holds] over the synthesis
      program and the configured system) whose advice plane carries the
      inputs at the gate's input cells and [CompleteAddition.output] at the
      result cells.  Together with [CompleteAddition.synthesize_correct]
      (soundness), the [add] chip computes exactly [output] on this
      domain. *)
  Theorem completeness (x_p y_p x_q y_q : Z)
      (Hx_p : 0 <= x_p < Primes.pallas_p)
      (Hy_p : 0 <= y_p < Primes.pallas_p)
      (Hx_q : 0 <= x_q < Primes.pallas_p)
      (Hy_q : 0 <= y_q < Primes.pallas_p)
      (HP : on_curve_or_identity x_p y_p)
      (HQ : on_curve_or_identity x_q y_q) :
    exists Γ : Assignment.t columns RegionId.t,
      circuit_holds Γ
        Garden.Halo2.halo2_gadgets.ecc.chip.add.synthesize
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.add.configure
          ConstraintSystem.empty) /\
      Γ.(Assignment.advice) Advice.A0 add_region 0 = x_p /\
      Γ.(Assignment.advice) Advice.A1 add_region 0 = y_p /\
      Γ.(Assignment.advice) Advice.A2 add_region 0 = x_q /\
      Γ.(Assignment.advice) Advice.A3 add_region 0 = y_q /\
      Γ.(Assignment.advice) Advice.A2 add_region 1 =
        (CompleteAddition.output x_p y_p x_q y_q).(Point.x) /\
      Γ.(Assignment.advice) Advice.A3 add_region 1 =
        (CompleteAddition.output x_p y_p x_q y_q).(Point.y).
  Proof.
    exists (witness_assignment x_p y_p x_q y_q).
    split; [| repeat apply conj; reflexivity].
    pose proof (witness_polys x_p y_p x_q y_q Hx_p Hy_p Hx_q Hy_q HP HQ)
      as HW.
    cbv zeta in HW.
    destruct HW as (HG1 & HG2 & HG3a & HG3b & HG3c & HG3d &
      HG4a & HG4b & HG5a & HG5b & HG6a & HG6b).
    apply (Complete.circuit_holds_intro
      OrchardDecidableEq.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardDecidableEq.fixed_eqb OrchardDecidableEq.lookup_eqb
      OrchardDecidableEq.region_id_eqb OrchardDecidableEq.region_id_eqb_eq).
    - (* Every gate constraint is selector-guarded. *)
      vm_compute; reflexivity.
    - (* No conflicting fixed writes or table loads (there are none). *)
      vm_compute; reflexivity.
    - (* Lookup padding (the system has no lookup argument). *)
      vm_compute; reflexivity.
    - (* The honest planes are definitional for [witness_assignment]. *)
      split; [| split].
      + intros selector region offset; reflexivity.
      + intros column region offset; reflexivity.
      + intros column row Hrow; reflexivity.
    - (* No witness facts: the program only enables the selector. *)
      exact I.
    - (* One enabled point, one gate, twelve guarded constraints. *)
      intros selector region row Hin gate Hgate name body Hbody.
      cbn in Hin.
      destruct Hin as [Heq | Habs]; [| destruct Habs].
      injection Heq as Hsel Hreg Hrow.
      subst.
      cbn in Hgate.
      destruct Hgate as [Hgate | Habs]; [| destruct Habs].
      subst gate.
      cbn in Hbody.
      destruct Hbody as
        [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | Habs
        ] ] ] ] ] ] ] ] ] ] ] ];
        [ | | | | | | | | | | | | destruct Habs ].
      all: inversion H; subst; clear H.
      all: with_strategy opaque
        [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
         lambda_w alpha_w beta_w gamma_w delta_w CompleteAddition.output]
        cbn.
      all: autorewrite with field_rewrite.
      { exact HG1. }
      { exact HG2. }
      { exact HG3a. }
      { exact HG3b. }
      { exact HG3c. }
      { exact HG3d. }
      { exact HG4a. }
      { exact HG4b. }
      { exact HG5a. }
      { exact HG5b. }
      { exact HG6a. }
      { exact HG6b. }
    - (* The system has no lookup argument. *)
      intros selector region row Hin arg Harg Hmention.
      cbn in Harg.
      destruct Harg.
  Qed.
End CompleteAdditionCompleteness.
