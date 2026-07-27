(** * Variable-base scalar multiplication: the incomplete double-and-add halves

    The generic round-induction core for the two incomplete halves of the
    address-integrity variable-base [mul] chip
    ([ecc/chip/mul/incomplete.v], instantiated twice by [ecc/chip/mul.v]:
    "hi" on [z=A9, x_a=A3, x_p=A0, y_p=A1, λ₁=A4, λ₂=A5] and "lo" on
    [z=A6, x_a=A7, x_p=A0, y_p=A1, λ₁=A8, λ₂=A2]), and the two
    instantiations [hi_half_correct] / [lo_half_correct], whose statements
    are identical to the phase cuts of
    [circuit_proof/ownership/var_base_mul.v].

    Layering:
    - [chord_add]: the raw chord equations (slope, secant [x], line [y])
      compute the Weierstrass [add] of two affine reduced points with
      distinct integer x-coordinates — the field-side core both incomplete
      additions of a step reduce to.
    - [incomplete_step_group]: one double-and-add step.  The chip carries
      the accumulator y-coordinate not as a cell but as the gate expression
      [y_a = (λ₁+λ₂)(x_a−x_r)·2⁻¹]; from the raw [gradient_1], [secant_line]
      and [gradient_2] constraints of [incomplete.for_loop] and the
      row's nondegeneracy ([x_a ≠ 0], [x_a ≠ x_p], [x_r ≠ x_a]) the step
      lands the accumulator on [repr ([2c + 2k − 1] B)]: [gradient_1] pins
      [λ₁] as the chord slope from the accumulator to [[2k−1] B] (whence
      [(x_r, y_r) = acc + [2k−1]B] by [chord_add]), the [y_a] shape itself
      pins [λ₂] as the chord slope of the second addition
      ([half_double_add]), and [secant_line]/[gradient_2] read off its
      result.
    - [q_mul_2_row_facts] / [q_mul_3_row_facts]: the per-row gate
      constraints at a symbolic row, in evaluated form ([q_mul_2] rows also
      propagate the base point to the next row; [q_mul_3]'s outgoing
      accumulator y is the witnessed [λ₁] on the next row).
    - [enable_selector_rows_on]: the per-row [SelectorOn] facts of an
      [enable_selector_rows] block, by induction on the block length.
    - [running_sum_exact] / [running_sum_bits_exact]: the boolean-bit
      running sum [z_{i+1} = 2 z_i + k] is exact over ℤ (no mod-[p] wrap)
      as long as [2^n (z_0 + 1) <= 2^254], giving the range and division
      links of the half conclusions.
    - [incomplete_half_generic]: the [n]-step round induction, threading
      the [repr ([2^m + 2z + 1] B)] invariant with
      [VarBaseDefs.double_add_step_multiple] / [step_scalar_shape].
    - [hi_half_correct] ([n = 125]) and [lo_half_correct] ([n = 126]):
      the facts navigation ([variable_base_region_facts] indices 5–21) and
      the boundary splices ([q_mul_1]'s "init y_a" via
      [QMul1Checks.deterministic], the accumulator/z copies), then one
      application of the generic core each. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
(* [Garden.Plonky3.M] is deliberately Require'd but NOT Imported: its
   notations break nested or-intropatterns.  [Primes] and the
   [PallasPIsPrime] instance are the [Field.Field] originals that
   [M.Primes] aliases. *)
Require Garden.Plonky3.M.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module VarBaseIncomplete.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Local Notation two_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv.

  (** The raw advice reader of the variable-base region ([VarBaseDefs.av]
      with the rotation already resolved — [av_adv] below aligns the
      two). *)
  Local Notation adv Γ c row :=
    (UnOp.from (Γ.(Assignment.advice) c VarBaseDefs.mul_region row)).

  Lemma av_adv
      (Γ : Assignment.t columns RegionId.t) (c : Advice.t) (row : Z) :
    VarBaseDefs.av Γ c row = adv Γ c row.
  Proof.
    unfold VarBaseDefs.av, OrchardActionInputs.read_advice.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
    unfold rotated_row.
    cbn [Rotation.cur Rotation.offset].
    rewrite Z.add_0_r.
    reflexivity.
  Qed.

  (** ** Field-side core *)

  (** The chord equations compute the Weierstrass [add] on the secant
      branch: for reduced affine points with distinct (integer, hence
      field) x-coordinates and [lam] the chord slope, the secant/line
      formulas are the addition result. *)
  Lemma chord_add
      (xa ya xb yb lam : Z)
      (Hxa : UnOp.from xa = xa) (Hya : UnOp.from ya = ya)
      (Hxb : UnOp.from xb = xb) (Hyb : UnOp.from yb = yb)
      (Hlam : UnOp.from lam = lam)
      (Hne : xa <> xb)
      (Hslope : lam *F (xa -F xb) = ya -F yb) :
    Pallas.add (Weierstrass.Affine xa ya) (Weierstrass.Affine xb yb) =
    Weierstrass.Affine
      (lam *F lam -F xa -F xb)
      (lam *F (xa -F (lam *F lam -F xa -F xb)) -F ya).
  Proof.
    unfold Pallas.add.
    cbn [Weierstrass.add].
    rewrite (PallasModel.reduced_sub_eqb xa xb Hxa Hxb).
    rewrite (proj2 (Z.eqb_neq xa xb) Hne).
    set (L := BinOp.div (yb -F ya) (xb -F xa)).
    assert (Hd : UnOp.from (xb -F xa) <> 0).
    { rewrite from_sub_reduced. intro Hc.
      apply sub_zero_equiv in Hc.
      rewrite Hxa, Hxb in Hc.
      exact (Hne (eq_sym Hc)). }
    assert (HLd : L *F (xb -F xa) = yb -F ya).
    { subst L. rewrite div_mul.
      - apply from_sub_reduced.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd. }
    assert (Hlamd : lam *F (xb -F xa) = yb -F ya).
    { transitivity (0 -F (lam *F (xa -F xb))).
      - mod_ring_solve.
      - rewrite Hslope. mod_ring_solve. }
    assert (HL : L = lam).
    { pose proof (field_mul_cancel_r L lam (xb -F xa) Hd) as Hc.
      rewrite HLd, Hlamd in Hc.
      specialize (Hc eq_refl).
      rewrite Hlam in Hc.
      rewrite <- Hc.
      subst L.
      unfold UnOp.from, BinOp.div.
      symmetry.
      apply from_mul_reduced. }
    rewrite HL.
    reflexivity.
  Qed.

  (** Halving is inverted by doubling: [A·2⁻¹ + A·2⁻¹ = A] in the field.
      This is what turns the [y_a] expression shape into the second chord
      slope. *)
  Lemma half_double_add (A : Z) :
    (A *F UnOp.from two_inv) +F (A *F UnOp.from two_inv) = UnOp.from A.
  Proof.
    unfold BinOp.add, BinOp.mul, UnOp.from.
    change (Zdiv.eqm Primes.pallas_p
      ((A * (two_inv mod Primes.pallas_p)) mod Primes.pallas_p +
       (A * (two_inv mod Primes.pallas_p)) mod Primes.pallas_p) A).
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    replace (A * two_inv + A * two_inv) with (A * (2 * two_inv)) by ring.
    rewrite Zmult_mod.
    assert (Ht : (2 * two_inv) mod Primes.pallas_p = 1)
      by (vm_compute; reflexivity).
    rewrite Ht, Z.mul_1_r.
    apply Z.mod_mod.
    unfold Primes.pallas_p, Primes.t_p; lia.
  Qed.

  (** One incomplete double-and-add step at the group level: from the raw
      [for_loop] constraint values at a row (with the accumulator's y
      carried as the [y_a] expression value) and the row's nondegeneracy,
      the outgoing accumulator represents [[2c + 2k − 1] B]. *)
  Lemma incomplete_step_group
      (B : Pallas.point) (bx byv : Z)
      (HB : B = Weierstrass.Affine bx byv)
      (HBred : Pallas.reduced B) (HBoc : Pallas.on_curve B)
      (c k xa l1 l2 xan yan : Z)
      (Hl1 : UnOp.from l1 = l1) (Hl2 : UnOp.from l2 = l2)
      (Hyan : UnOp.from yan = yan)
      (Hk : k = 0 \/ k = 1)
      (Hacc : {| Point.x := xa; Point.y := y_a xa bx l1 l2 |} =
              PallasModel.repr (Pallas.mul c B))
      (Hxa0 : xa <> 0)
      (Hxab : xa <> bx)
      (Hxr : x_r xa bx l1 <> xa)
      (Hg1 : l1 *F (xa -F bx) -F y_a xa bx l1 l2
               +F ((k *F UnOp.from 2 -F UnOp.from 1) *F byv) = 0)
      (Hxan_e : xan = next_x_a xa bx l1 l2)
      (Hg2 : l2 *F (xa -F xan) -F y_a xa bx l1 l2 -F yan = 0) :
    {| Point.x := xan; Point.y := yan |} =
    PallasModel.repr (Pallas.mul (2 * c + 2 * k - 1) B).
  Proof.
    assert (Hbx : UnOp.from bx = bx) by (rewrite HB in HBred; apply HBred).
    assert (Hbyv : UnOp.from byv = byv) by (rewrite HB in HBred; apply HBred).
    set (Ya := y_a xa bx l1 l2) in *.
    assert (HYa : UnOp.from Ya = Ya)
      by (subst Ya; unfold y_a; apply from_mul_reduced).
    pose proof (VarBaseDefs.pallas_mul_reduced c B HBred) as HAred.
    pose proof (VarBaseDefs.pallas_mul_on_curve c B HBoc) as HAoc.
    destruct (Pallas.mul c B) as [| ax ay] eqn:HAeq.
    { exfalso. apply Hxa0.
      cbn [PallasModel.repr] in Hacc.
      injection Hacc. intros _ Hx. exact Hx. }
    cbn [PallasModel.repr] in Hacc.
    injection Hacc. intros Hay Hax.
    subst ax ay.
    assert (Hxa : UnOp.from xa = xa) by apply HAred.
    (* The signed base point [[2k−1] B] the step adds, per bit branch. *)
    assert (Hsigned : exists yb : Z,
        UnOp.from yb = yb /\
        VarBaseDefs.signed_base B k = Weierstrass.Affine bx yb /\
        Pallas.on_curve (Weierstrass.Affine bx yb) /\
        l1 *F (xa -F bx) = Ya -F yb).
    { destruct Hk as [-> | ->].
      - exists (UnOp.opp byv).
        split; [| split; [| split]].
        + unfold UnOp.opp, UnOp.from. apply Z.mod_mod.
          unfold Primes.pallas_p, Primes.t_p; lia.
        + unfold VarBaseDefs.signed_base. cbn [Z.eqb].
          rewrite HB. reflexivity.
        + pose proof (VarBaseDefs.pallas_neg_on_curve B HBoc) as Hoc.
          rewrite HB in Hoc. exact Hoc.
        + assert (Hs : (0 *F UnOp.from 2 -F UnOp.from 1) *F byv = UnOp.opp byv).
          { unfold UnOp.opp. mod_ring_solve. }
          rewrite Hs in Hg1.
          assert (Hmv : l1 *F (xa -F bx) -F (Ya -F UnOp.opp byv) =
              l1 *F (xa -F bx) -F Ya +F UnOp.opp byv) by mod_ring_solve.
          rewrite Hg1 in Hmv.
          apply sub_zero_equiv in Hmv.
          rewrite from_mul_reduced, from_sub_reduced in Hmv.
          exact Hmv.
      - exists byv.
        split; [| split; [| split]].
        + exact Hbyv.
        + unfold VarBaseDefs.signed_base. cbn [Z.eqb].
          exact HB.
        + rewrite HB in HBoc. exact HBoc.
        + assert (Hs : (1 *F UnOp.from 2 -F UnOp.from 1) *F byv = UnOp.from byv).
          { mod_ring_solve. }
          rewrite Hbyv in Hs.
          rewrite Hs in Hg1.
          assert (Hmv : l1 *F (xa -F bx) -F (Ya -F byv) =
              l1 *F (xa -F bx) -F Ya +F byv) by mod_ring_solve.
          rewrite Hg1 in Hmv.
          apply sub_zero_equiv in Hmv.
          rewrite from_mul_reduced, from_sub_reduced in Hmv.
          exact Hmv. }
    destruct Hsigned as (yb & Hyb & Hsb & Hocb & Hslope1).
    (* First incomplete addition: [acc + [2k−1]B]. *)
    pose proof (chord_add xa Ya bx yb l1 Hxa HYa Hbx Hyb Hl1 Hxab Hslope1)
      as Hchord1.
    set (XR := l1 *F l1 -F xa -F bx) in *.
    set (YR := l1 *F (xa -F XR) -F Ya) in *.
    assert (HXRxr : x_r xa bx l1 = XR) by reflexivity.
    assert (HXRred : UnOp.from XR = XR) by apply from_sub_reduced.
    assert (HYRred : UnOp.from YR = YR) by apply from_sub_reduced.
    assert (HRoc : Pallas.on_curve (Weierstrass.Affine XR YR)).
    { rewrite <- Hchord1.
      apply (Weierstrass.add_on_curve Pallas.a Pallas.b).
      - exact Pallas.three_lt_p.
      - exact HAoc.
      - exact Hocb. }
    (* The [y_a] shape pins [λ₂] as the second chord slope. *)
    assert (HYa_eq : Ya = ((l1 +F l2) *F (xa -F XR)) *F UnOp.from two_inv)
      by reflexivity.
    assert (HYR_eq : YR = l1 *F (xa -F XR) -F Ya) by reflexivity.
    assert (Hslope2 : l2 *F (xa -F XR) = Ya -F YR).
    { transitivity ((Ya +F Ya) -F (l1 *F (xa -F XR))).
      - rewrite HYa_eq at 1 2.
        rewrite half_double_add.
        mod_ring_solve.
      - rewrite HYR_eq. mod_ring_solve. }
    assert (Hne2 : xa <> XR).
    { rewrite HXRxr in Hxr. exact (fun Hc => Hxr (eq_sym Hc)). }
    pose proof (chord_add xa Ya XR YR l2 Hxa HYa HXRred HYRred Hl2 Hne2 Hslope2)
      as Hchord2.
    (* [secant_line] / [gradient_2] read off the second addition. *)
    assert (Hx3 : xan = l2 *F l2 -F xa -F XR).
    { rewrite Hxan_e. unfold next_x_a, square. rewrite HXRxr. mod_ring_solve. }
    apply sub_zero_equiv in Hg2.
    rewrite from_sub_reduced, Hyan in Hg2.
    rewrite <- (VarBaseDefs.double_add_step_multiple B c k HBred HBoc Hk).
    rewrite HAeq, Hsb, Hchord1.
    assert (Hcomm :
        Pallas.add (Weierstrass.Affine XR YR) (Weierstrass.Affine xa Ya) =
        Pallas.add (Weierstrass.Affine xa Ya) (Weierstrass.Affine XR YR)).
    { unfold Pallas.add.
      apply (Weierstrass.add_comm Pallas.a Pallas.b _ _ HRoc HAoc). }
    rewrite Hcomm, Hchord2.
    cbn [PallasModel.repr].
    rewrite <- Hx3.
    f_equal.
    symmetry.
    exact Hg2.
  Qed.

  (** ** Per-row gate facts (symbolic row) *)

  (** The six [q_mul_2] constraints at row [r], evaluated: base-point
      propagation to the next row, the boolean bit, and the raw
      [gradient_1]/[secant_line]/[gradient_2] with the [y_a]/[x_r]
      expression values folded to [incomplete_proof.y_a]/[x_r]/[next_x_a]
      (the next-row [y_a] is the expression at [r + 1]). *)
  Lemma q_mul_2_row_facts
      (Γ : Assignment.t columns RegionId.t)
      (q2 : Selector.t) (Zc Xa Xp Yp L1 L2 : Advice.t) (r : Z)
      (Hsel : Γ.(Assignment.selector) q2 VarBaseDefs.mul_region r = 1)
      (Hgate : eval_gate Γ (VarBaseDefs.mul_region, r)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          q2 Zc Xa Xp Yp L1 L2)) :
    adv Γ Xp (r + 1) = adv Γ Xp r /\
    adv Γ Yp (r + 1) = adv Γ Yp r /\
    (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) =
      Z.b2z (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2)) /\
    adv Γ L1 r *F (adv Γ Xa r -F adv Γ Xp r)
      -F y_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r)
      +F (((adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) *F UnOp.from 2
           -F UnOp.from 1) *F adv Γ Yp r) = 0 /\
    adv Γ Xa (r + 1) =
      next_x_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r) /\
    adv Γ L2 r *F (adv Γ Xa r -F adv Γ Xa (r + 1))
      -F y_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r)
      -F y_a (adv Γ Xa (r + 1)) (adv Γ Xp (r + 1)) (adv Γ L1 (r + 1))
           (adv Γ L2 (r + 1)) = 0.
  Proof.
    pose proof (enabled_nonzero Γ q2 VarBaseDefs.mul_region r Hsel) as Hnz.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from Primes.pallas_p]
      cbn in Hgate.
    assert (Hrc : rotated_row r Rotation.cur = r)
      by (unfold rotated_row; cbn; lia).
    assert (Hrn : rotated_row r Rotation.next = r + 1)
      by (unfold rotated_row; cbn; lia).
    assert (Hrp : rotated_row r Rotation.prev = r - 1)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrc, Hrn, Hrp in Hgate.
    destruct Hgate as (hxp & hyp & hbool & hg1 & hsec & hg2).
    specialize (hxp Hnz).
    specialize (hyp Hnz).
    specialize (hbool Hnz).
    specialize (hg1 Hnz).
    specialize (hsec Hnz).
    specialize (hg2 Hnz).
    split; [| split; [| split; [| split; [| split]]]].
    - symmetry. exact hxp.
    - symmetry. exact hyp.
    - exact hbool.
    - unfold y_a, x_r, square. exact hg1.
    - clear - hsec. unfold next_x_a, x_r, square. field_solve.
    - unfold y_a, x_r, square. exact hg2.
  Qed.

  (** The four [q_mul_3] constraints at row [r]: as above, but the
      outgoing accumulator y is the witnessed [λ₁] cell on the next row. *)
  Lemma q_mul_3_row_facts
      (Γ : Assignment.t columns RegionId.t)
      (q3 : Selector.t) (Zc Xa Xp Yp L1 L2 : Advice.t) (r : Z)
      (Hsel : Γ.(Assignment.selector) q3 VarBaseDefs.mul_region r = 1)
      (Hgate : eval_gate Γ (VarBaseDefs.mul_region, r)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          q3 Zc Xa Xp Yp L1 L2)) :
    (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) =
      Z.b2z (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2)) /\
    adv Γ L1 r *F (adv Γ Xa r -F adv Γ Xp r)
      -F y_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r)
      +F (((adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) *F UnOp.from 2
           -F UnOp.from 1) *F adv Γ Yp r) = 0 /\
    adv Γ Xa (r + 1) =
      next_x_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r) /\
    adv Γ L2 r *F (adv Γ Xa r -F adv Γ Xa (r + 1))
      -F y_a (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) (adv Γ L2 r)
      -F adv Γ L1 (r + 1) = 0.
  Proof.
    pose proof (enabled_nonzero Γ q3 VarBaseDefs.mul_region r Hsel) as Hnz.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from Primes.pallas_p]
      cbn in Hgate.
    assert (Hrc : rotated_row r Rotation.cur = r)
      by (unfold rotated_row; cbn; lia).
    assert (Hrn : rotated_row r Rotation.next = r + 1)
      by (unfold rotated_row; cbn; lia).
    assert (Hrp : rotated_row r Rotation.prev = r - 1)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrc, Hrn, Hrp in Hgate.
    destruct Hgate as (hbool & hg1 & hsec & hg2).
    specialize (hbool Hnz).
    specialize (hg1 Hnz).
    specialize (hsec Hnz).
    specialize (hg2 Hnz).
    split; [| split; [| split]].
    - exact hbool.
    - unfold y_a, x_r, square. exact hg1.
    - clear - hsec. unfold next_x_a, x_r, square. field_solve.
    - unfold y_a, x_r, square. exact hg2.
  Qed.

  (** ** Selector-block facts *)

  (** Every row of an [enable_selector_rows] block carries its
      [SelectorOn] fact. *)
  Lemma enable_selector_rows_on
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (sel : Selector.t)
      (count : nat) (offset : Z)
      (Hfacts : interpret_facts Γ (region_facts region
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_selector_rows
          sel offset count))) :
    forall r, offset <= r < offset + Z.of_nat count ->
    Γ.(Assignment.selector) sel region r = 1.
  Proof.
    revert offset Hfacts.
    induction count as [| count IH]; intros offset Hfacts r Hr.
    - cbn in Hr. lia.
    - cbn [Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_selector_rows]
        in Hfacts.
      pose proof Hfacts as Hhead.
      apply interpret_region_facts_bind_left in Hhead.
      pose proof Hfacts as Htail.
      apply interpret_region_facts_bind_right in Htail.
      cbn [region_facts interpret_facts interpret_fact] in Hhead.
      destruct Hhead as [Hhead _].
      destruct (Z.eq_dec r offset) as [-> | Hne].
      + exact Hhead.
      + apply (IH (offset + 1) Htail). lia.
  Qed.

  (** ** The exact running sum *)

  Lemma pallas_p_shape : Primes.pallas_p = 2 ^ 254 + Primes.t_p.
  Proof. reflexivity. Qed.

  (** The boolean-bit running sum is exact over ℤ: as long as
      [2^n (z_0 + 1) <= 2^254 < p], no step wraps mod [p], so after [j]
      steps the value is [2^j z_0] plus a [j]-bit remainder. *)
  Lemma running_sum_exact
      (f : Z -> Z) (r0 n : Z)
      (Hn : 0 <= n)
      (Hred : forall j, 0 <= j <= n -> 0 <= f (r0 + j) < Primes.pallas_p)
      (Hcap : 2 ^ n * (f r0 + 1) <= 2 ^ 254)
      (Hbits : forall j, 0 <= j < n ->
          exists k, (k = 0 \/ k = 1) /\
          f (r0 + j + 1) = (2 * f (r0 + j) + k) mod Primes.pallas_p) :
      forall j, 0 <= j <= n ->
      0 <= f (r0 + j) - 2 ^ j * f r0 < 2 ^ j.
  Proof.
    assert (Hf0 : 0 <= f r0).
    { specialize (Hred 0 ltac:(lia)). rewrite Z.add_0_r in Hred. lia. }
    intros j Hj.
    destruct Hj as [Hj0 Hjn].
    revert Hjn.
    pattern j.
    apply natlike_ind; [| | exact Hj0].
    - intros _.
      rewrite Z.add_0_r, Z.pow_0_r.
      lia.
    - intros x Hx IH Hxn.
      assert (Hxn' : x <= n) by lia.
      specialize (IH Hxn').
      destruct (Hbits x ltac:(lia)) as (k & Hk & Hstep).
      assert (Hpow_pos : 0 < 2 ^ x) by (apply Z.pow_pos_nonneg; lia).
      assert (Hpow_succ : 2 ^ Z.succ x = 2 * 2 ^ x)
        by (rewrite Z.pow_succ_r; lia).
      assert (Hmono : 2 ^ Z.succ x <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
      assert (Hlow : 0 <= 2 ^ x * f r0)
        by (apply Z.mul_nonneg_nonneg; lia).
      assert (Hbound : 0 <= 2 * f (r0 + x) + k < Primes.pallas_p).
      { rewrite pallas_p_shape.
        assert (Htp : 0 < Primes.t_p) by (unfold Primes.t_p; lia).
        assert (Hup : 2 * f (r0 + x) + k <= 2 ^ Z.succ x * (f r0 + 1) - 1)
          by (clear - IH Hk Hpow_succ Hf0 Hpow_pos; nia).
        assert (Hcap' : 2 ^ Z.succ x * (f r0 + 1) <= 2 ^ 254)
          by (clear - Hcap Hmono Hf0; nia).
        clear - IH Hk Hup Hcap' Htp Hpow_pos Hlow.
        lia. }
      replace (r0 + Z.succ x) with (r0 + x + 1) by lia.
      rewrite Hstep.
      rewrite Z.mod_small by exact Hbound.
      rewrite Hpow_succ.
      clear - IH Hk Hpow_pos Hlow.
      lia.
  Qed.

  (** Per-step corollary: each field-level bit congruence is in fact an
      exact ℤ equation [z_{j+1} = 2 z_j + k]. *)
  Lemma running_sum_bits_exact
      (f : Z -> Z) (r0 n : Z)
      (Hn : 0 <= n)
      (Hred : forall j, 0 <= j <= n -> 0 <= f (r0 + j) < Primes.pallas_p)
      (Hcap : 2 ^ n * (f r0 + 1) <= 2 ^ 254)
      (Hbits : forall j, 0 <= j < n ->
          exists k, (k = 0 \/ k = 1) /\
          f (r0 + j + 1) = (2 * f (r0 + j) + k) mod Primes.pallas_p) :
      forall j, 0 <= j < n ->
      exists k, (k = 0 \/ k = 1) /\ f (r0 + j + 1) = 2 * f (r0 + j) + k.
  Proof.
    intros j Hj.
    pose proof (running_sum_exact f r0 n Hn Hred Hcap Hbits j ltac:(lia))
      as Hbnd.
    destruct (Hbits j ltac:(lia)) as (k & Hk & Hstep).
    exists k.
    split; [exact Hk |].
    assert (Hf0 : 0 <= f r0).
    { specialize (Hred 0 ltac:(lia)). rewrite Z.add_0_r in Hred. lia. }
    assert (Hpow_pos : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    assert (Hlow : 0 <= 2 ^ j * f r0) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hpow_succ : 2 ^ (j + 1) = 2 * 2 ^ j)
      by (rewrite Z.pow_add_r by lia; lia).
    assert (Hmono : 2 ^ (j + 1) <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
    assert (Hbound : 0 <= 2 * f (r0 + j) + k < Primes.pallas_p).
    { rewrite pallas_p_shape.
      assert (Htp : 0 < Primes.t_p) by (unfold Primes.t_p; lia).
      assert (Hup : 2 * f (r0 + j) + k <= 2 ^ (j + 1) * (f r0 + 1) - 1)
        by (clear - Hbnd Hk Hpow_succ Hf0 Hpow_pos; nia).
      assert (Hcap' : 2 ^ (j + 1) * (f r0 + 1) <= 2 ^ 254)
        by (clear - Hcap Hmono Hf0; nia).
      clear - Hbnd Hk Hup Hcap' Htp Hpow_pos Hlow.
      lia. }
    rewrite Hstep.
    apply Z.mod_small.
    exact Hbound.
  Qed.

  (** ** The generic round induction

      The [n]-step incomplete half on an arbitrary column tuple, from the
      entry state at rows 1–2 to the exit accumulator at row [n + 2]:
      [q_mul_2] rows 2..n, [q_mul_3] row [n + 1], running sum from row 1
      to row [n + 1] with the [repr ([2^m + 2z + 1] B)] invariant.  The
      two subtraction bounds are the range and division links the halves'
      conclusions decompose into. *)
  Lemma incomplete_half_generic
      (Γ : Assignment.t columns RegionId.t)
      (q2 q3 : Selector.t) (Zc Xa Xp Yp L1 L2 : Advice.t)
      (B : Pallas.point) (bx byv : Z)
      (n m0 : Z)
      (Hn : 1 <= n)
      (Hm0 : 0 <= m0)
      (HB : B = Weierstrass.Affine bx byv)
      (HBred : Pallas.reduced B)
      (HBoc : Pallas.on_curve B)
      (Hbx2 : adv Γ Xp 2 = bx)
      (Hby2 : adv Γ Yp 2 = byv)
      (Hnondeg : forall r, 2 <= r <= n + 1 ->
          adv Γ Xa r <> 0 /\
          adv Γ Xa r <> adv Γ Xp r /\
          x_r (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) <> adv Γ Xa r)
      (Hcap : 2 ^ n * (adv Γ Zc 1 + 1) <= 2 ^ 254)
      (Hacc0 : {| Point.x := adv Γ Xa 2; Point.y := adv Γ L1 1 |} =
          PallasModel.repr (Pallas.mul (2 ^ m0 + 2 * adv Γ Zc 1 + 1) B))
      (Hya2 : adv Γ L1 1 =
          y_a (adv Γ Xa 2) (adv Γ Xp 2) (adv Γ L1 2) (adv Γ L2 2))
      (Hsel2 : forall r, 2 <= r <= n ->
          Γ.(Assignment.selector) q2 VarBaseDefs.mul_region r = 1)
      (Hsel3 : Γ.(Assignment.selector) q3 VarBaseDefs.mul_region (n + 1) = 1)
      (Hgate2 : forall row : Z, eval_gate Γ (VarBaseDefs.mul_region, row)
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
            q2 Zc Xa Xp Yp L1 L2))
      (Hgate3 : forall row : Z, eval_gate Γ (VarBaseDefs.mul_region, row)
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
            q3 Zc Xa Xp Yp L1 L2)) :
    0 <= adv Γ Zc (n + 1) - 2 ^ n * adv Γ Zc 1 < 2 ^ n /\
    0 <= adv Γ Zc (n + 1) - 2 ^ (n - 1) * adv Γ Zc 2 < 2 ^ (n - 1) /\
    {| Point.x := adv Γ Xa (n + 2); Point.y := adv Γ L1 (n + 2) |} =
    PallasModel.repr
      (Pallas.mul (2 ^ (m0 + n) + 2 * adv Γ Zc (n + 1) + 1) B).
  Proof.
    assert (Hplit : 0 < Primes.pallas_p)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    assert (Hadv_bound : forall (c : Advice.t) (row : Z),
        0 <= adv Γ c row < Primes.pallas_p)
      by (intros; unfold UnOp.from; apply Z.mod_pos_bound; exact Hplit).
    assert (Hadv_red : forall (c : Advice.t) (row : Z),
        UnOp.from (adv Γ c row) = adv Γ c row)
      by (intros; apply from_idem).
    (* The per-row boolean bit, as a field congruence on the running sum. *)
    assert (Hbitfacts : forall r, 2 <= r <= n + 1 ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc r = (2 * adv Γ Zc (r - 1) + k) mod Primes.pallas_p).
    { intros r Hr.
      assert (Hkb : (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) =
          Z.b2z (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2))).
      { destruct (Z.eq_dec r (n + 1)) as [-> | Hne].
        - pose proof (q_mul_3_row_facts Γ q3 Zc Xa Xp Yp L1 L2 (n + 1)
            Hsel3 (Hgate3 (n + 1))) as H3.
          cbv zeta beta in H3.
          exact (proj1 H3).
        - pose proof (q_mul_2_row_facts Γ q2 Zc Xa Xp Yp L1 L2 r
            (Hsel2 r ltac:(lia)) (Hgate2 r)) as H2f.
          cbv zeta beta in H2f.
          exact (proj1 (proj2 (proj2 H2f))). }
      assert (Hkv01 : (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) = 0 \/
          (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) = 1).
      { destruct (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2));
          cbn in Hkb; [right | left]; exact Hkb. }
      exists (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2).
      split; [exact Hkv01 |].
      assert (Hfe : UnOp.from
          (2 * adv Γ Zc (r - 1) +
           (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2)) =
          UnOp.from (adv Γ Zc r)) by mod_ring_solve.
      rewrite Hadv_red in Hfe.
      exact (eq_sym Hfe). }
    assert (Hbits1 : forall j, 0 <= j < n ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc (1 + j + 1) = (2 * adv Γ Zc (1 + j) + k) mod Primes.pallas_p).
    { intros j Hj.
      destruct (Hbitfacts (1 + j + 1) ltac:(lia)) as (k & Hk & He).
      exists k.
      split; [exact Hk |].
      replace (1 + j + 1 - 1) with (1 + j) in He by lia.
      exact He. }
    assert (Hz1 : forall j, 0 <= j <= n ->
        0 <= adv Γ Zc (1 + j) - 2 ^ j * adv Γ Zc 1 < 2 ^ j).
    { apply (running_sum_exact (fun row => adv Γ Zc row) 1 n).
      - lia.
      - intros j _. apply Hadv_bound.
      - exact Hcap.
      - exact Hbits1. }
    assert (Hzstep : forall j, 0 <= j < n ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc (1 + j + 1) = 2 * adv Γ Zc (1 + j) + k).
    { apply (running_sum_bits_exact (fun row => adv Γ Zc row) 1 n).
      - lia.
      - intros j _. apply Hadv_bound.
      - exact Hcap.
      - exact Hbits1. }
    assert (Hcap2 : 2 ^ (n - 1) * (adv Γ Zc 2 + 1) <= 2 ^ 254).
    { destruct (Hzstep 0 ltac:(lia)) as (k & Hk & He).
      replace (1 + 0 + 1) with 2 in He by lia.
      replace (1 + 0) with 1 in He by lia.
      assert (Hpow : 2 ^ n = 2 * 2 ^ (n - 1)).
      { replace n with (Z.succ (n - 1)) at 1 by lia.
        rewrite Z.pow_succ_r by lia.
        lia. }
      assert (Hz1nn : 0 <= adv Γ Zc 1) by (apply Hadv_bound).
      clear - He Hk Hpow Hcap Hz1nn.
      nia. }
    assert (Hz2 : forall j, 0 <= j <= n - 1 ->
        0 <= adv Γ Zc (2 + j) - 2 ^ j * adv Γ Zc 2 < 2 ^ j).
    { apply (running_sum_exact (fun row => adv Γ Zc row) 2 (n - 1)).
      - lia.
      - intros j _. apply Hadv_bound.
      - exact Hcap2.
      - intros j Hj.
        destruct (Hbitfacts (2 + j + 1) ltac:(lia)) as (k & Hk & He).
        exists k.
        split; [exact Hk |].
        replace (2 + j + 1 - 1) with (2 + j) in He by lia.
        exact He. }
    assert (Hyared : forall xa xp l1 l2 : Z,
        UnOp.from (y_a xa xp l1 l2) = y_a xa xp l1 l2)
      by (intros; unfold y_a; apply from_mul_reduced).
    (* The accumulator invariant, one [q_mul_2] step at a time. *)
    assert (Hinv : forall j, 0 <= j -> j <= n - 1 ->
        (adv Γ Xp (2 + j) = bx /\ adv Γ Yp (2 + j) = byv) /\
        {| Point.x := adv Γ Xa (2 + j);
           Point.y := y_a (adv Γ Xa (2 + j)) (adv Γ Xp (2 + j))
                        (adv Γ L1 (2 + j)) (adv Γ L2 (2 + j)) |} =
        PallasModel.repr
          (Pallas.mul (2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1) B)).
    { intros j Hj0.
      pattern j.
      revert Hj0.
      apply natlike_ind.
      - intros _.
        replace (2 + 0) with 2 by lia.
        replace (1 + 0) with 1 by lia.
        replace (m0 + 0) with m0 by lia.
        split.
        + split; [exact Hbx2 | exact Hby2].
        + rewrite <- Hya2. exact Hacc0.
      - intros x Hx IH Hsx.
        specialize (IH ltac:(lia)).
        destruct IH as [[Hxpr Hypr] Hacc].
        pose proof (q_mul_2_row_facts Γ q2 Zc Xa Xp Yp L1 L2 (2 + x)
          (Hsel2 (2 + x) ltac:(lia)) (Hgate2 (2 + x))) as HF.
        cbv zeta beta in HF.
        destruct HF as (Hxp' & Hyp' & _ & Hg1 & Hxan & Hg2).
        replace (2 + x + 1) with (2 + Z.succ x) in Hxp', Hyp', Hxan, Hg2 by lia.
        replace (2 + x - 1) with (1 + x) in Hg1 by lia.
        destruct (Hzstep x ltac:(lia)) as (k & Hk & Hstep).
        replace (1 + x + 1) with (2 + x) in Hstep by lia.
        assert (Hkv : (adv Γ Zc (2 + x) -F adv Γ Zc (1 + x) *F UnOp.from 2) = k).
        { rewrite Hstep.
          destruct Hk as [-> | ->].
          - transitivity (UnOp.from 0).
            + mod_ring_solve.
            + unfold UnOp.from. apply Zmod_0_l.
          - transitivity (UnOp.from 1).
            + mod_ring_solve.
            + unfold UnOp.from. apply Z.mod_small.
              unfold Primes.pallas_p, Primes.t_p; lia. }
        rewrite Hkv in Hg1.
        rewrite Hxpr in Hg1, Hxan, Hg2, Hacc.
        rewrite Hypr in Hg1.
        destruct (Hnondeg (2 + x) ltac:(lia)) as (Hnd1 & Hnd2 & Hnd3).
        rewrite Hxpr in Hnd2, Hnd3.
        pose proof (incomplete_step_group B bx byv HB HBred HBoc
          (2 ^ (m0 + x) + 2 * adv Γ Zc (1 + x) + 1) k
          (adv Γ Xa (2 + x)) (adv Γ L1 (2 + x)) (adv Γ L2 (2 + x))
          (adv Γ Xa (2 + Z.succ x))
          (y_a (adv Γ Xa (2 + Z.succ x)) (adv Γ Xp (2 + Z.succ x))
               (adv Γ L1 (2 + Z.succ x)) (adv Γ L2 (2 + Z.succ x)))
          (Hadv_red _ _) (Hadv_red _ _)
          (Hyared _ _ _ _)
          Hk Hacc Hnd1 Hnd2 Hnd3 Hg1 Hxan Hg2) as Hnext.
        rewrite (VarBaseDefs.step_scalar_shape (m0 + x) (adv Γ Zc (1 + x)) k
          ltac:(lia)) in Hnext.
        rewrite <- Hstep in Hnext.
        replace (m0 + x + 1) with (m0 + Z.succ x) in Hnext by lia.
        split.
        + split; [rewrite Hxp'; exact Hxpr | rewrite Hyp'; exact Hypr].
        + replace (1 + Z.succ x) with (2 + x) by lia.
          exact Hnext. }
    split.
    { pose proof (Hz1 n ltac:(lia)) as Hc.
      replace (1 + n) with (n + 1) in Hc by lia.
      exact Hc. }
    split.
    { pose proof (Hz2 (n - 1) ltac:(lia)) as Hc.
      replace (2 + (n - 1)) with (n + 1) in Hc by lia.
      exact Hc. }
    (* The final [q_mul_3] step. *)
    pose proof (Hinv (n - 1) ltac:(lia) ltac:(lia)) as [[Hxpr Hypr] Hacc].
    replace (2 + (n - 1)) with (n + 1) in Hxpr, Hypr, Hacc by lia.
    replace (1 + (n - 1)) with n in Hacc by lia.
    pose proof (q_mul_3_row_facts Γ q3 Zc Xa Xp Yp L1 L2 (n + 1)
      Hsel3 (Hgate3 (n + 1))) as HF.
    cbv zeta beta in HF.
    destruct HF as (_ & Hg1 & Hxan & Hg2).
    replace (n + 1 - 1) with n in Hg1 by lia.
    replace (n + 1 + 1) with (n + 2) in Hxan, Hg2 by lia.
    destruct (Hzstep (n - 1) ltac:(lia)) as (k & Hk & Hstep).
    replace (1 + (n - 1) + 1) with (n + 1) in Hstep by lia.
    replace (1 + (n - 1)) with n in Hstep by lia.
    assert (Hkv : (adv Γ Zc (n + 1) -F adv Γ Zc n *F UnOp.from 2) = k).
    { rewrite Hstep.
      destruct Hk as [-> | ->].
      - transitivity (UnOp.from 0).
        + mod_ring_solve.
        + unfold UnOp.from. apply Zmod_0_l.
      - transitivity (UnOp.from 1).
        + mod_ring_solve.
        + unfold UnOp.from. apply Z.mod_small.
          unfold Primes.pallas_p, Primes.t_p; lia. }
    rewrite Hkv in Hg1.
    rewrite Hxpr in Hg1, Hxan, Hg2, Hacc.
    rewrite Hypr in Hg1.
    destruct (Hnondeg (n + 1) ltac:(lia)) as (Hnd1 & Hnd2 & Hnd3).
    rewrite Hxpr in Hnd2, Hnd3.
    pose proof (incomplete_step_group B bx byv HB HBred HBoc
      (2 ^ (m0 + (n - 1)) + 2 * adv Γ Zc n + 1) k
      (adv Γ Xa (n + 1)) (adv Γ L1 (n + 1)) (adv Γ L2 (n + 1))
      (adv Γ Xa (n + 2)) (adv Γ L1 (n + 2))
      (Hadv_red _ _) (Hadv_red _ _) (Hadv_red _ _)
      Hk Hacc Hnd1 Hnd2 Hnd3 Hg1 Hxan Hg2) as Hnext.
    rewrite (VarBaseDefs.step_scalar_shape (m0 + (n - 1)) (adv Γ Zc n) k
      ltac:(lia)) in Hnext.
    rewrite <- Hstep in Hnext.
    replace (m0 + (n - 1) + 1) with (m0 + n) in Hnext by lia.
    exact Hnext.
  Qed.

  (** ** The hi incomplete half (125 steps)

      Statement identical to [VarBaseMul.hi_half_correct]
      ([circuit_proof/ownership/var_base_mul.v]). *)
  Lemma hi_half_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (VarBaseDefs.base_wpoint Γ))
      (HBoc : Pallas.on_curve (VarBaseDefs.base_wpoint Γ))
      (HBne : VarBaseDefs.base_wpoint Γ <> Pallas.identity)
      (Hnondeg : forall r, 2 <= r <= 126 ->
        VarBaseDefs.hi_step_nondegenerate Γ r)
      (Hinit :
        {| Point.x := VarBaseDefs.av Γ Advice.A2 1;
           Point.y := VarBaseDefs.av Γ Advice.A3 1 |} =
        PallasModel.repr (Pallas.mul 2 (VarBaseDefs.base_wpoint Γ))) :
    0 <= VarBaseDefs.av Γ Advice.A9 126 < 2 ^ 125 /\
    VarBaseDefs.av Γ Advice.A9 126 / 2 ^ 124 = VarBaseDefs.av Γ Advice.A9 2 /\
    {| Point.x := VarBaseDefs.av Γ Advice.A3 127;
       Point.y := VarBaseDefs.av Γ Advice.A4 127 |} =
    PallasModel.repr
      (Pallas.mul (2 ^ 125 + 2 * VarBaseDefs.av Γ Advice.A9 126 + 1)
        (VarBaseDefs.base_wpoint Γ)).
  Proof.
    (* Facts 5–13 of the region program: the [z] constant, the three hi
       selector nodes and the boundary copies. *)
    pose proof (VarBaseDefs.variable_base_region_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hz1c.
    do 5 apply interpret_region_facts_bind_right in Hz1c.
    apply interpret_region_facts_bind_left in Hz1c.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hz1c.
    destruct Hz1c as [Hz1c _].
    pose proof Hfacts as Hsel1.
    do 6 apply interpret_region_facts_bind_right in Hsel1.
    apply interpret_region_facts_bind_left in Hsel1.
    cbn [region_facts interpret_facts interpret_fact] in Hsel1.
    destruct Hsel1 as [Hsel1 _].
    pose proof Hfacts as Hblock.
    do 7 apply interpret_region_facts_bind_right in Hblock.
    apply interpret_region_facts_bind_left in Hblock.
    pose proof Hfacts as Hsel3.
    do 8 apply interpret_region_facts_bind_right in Hsel3.
    apply interpret_region_facts_bind_left in Hsel3.
    cbn [region_facts interpret_facts interpret_fact] in Hsel3.
    destruct Hsel3 as [Hsel3 _].
    pose proof Hfacts as Hcopy_x.
    do 10 apply interpret_region_facts_bind_right in Hcopy_x.
    apply interpret_region_facts_bind_left in Hcopy_x.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_x.
    destruct Hcopy_x as [Hcopy_x _].
    pose proof Hfacts as Hcopy_y.
    do 11 apply interpret_region_facts_bind_right in Hcopy_y.
    apply interpret_region_facts_bind_left in Hcopy_y.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_y.
    destruct Hcopy_y as [Hcopy_y _].
    pose proof Hfacts as Hcopy_bx.
    do 12 apply interpret_region_facts_bind_right in Hcopy_bx.
    apply interpret_region_facts_bind_left in Hcopy_bx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_bx.
    destruct Hcopy_bx as [Hcopy_bx _].
    pose proof Hfacts as Hcopy_by.
    do 13 apply interpret_region_facts_bind_right in Hcopy_by.
    apply interpret_region_facts_bind_left in Hcopy_by.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_by.
    destruct Hcopy_by as [Hcopy_by _].
    cbn in Hz1c, Hcopy_x, Hcopy_y, Hcopy_bx, Hcopy_by.
    assert (Hz1adv : adv Γ Advice.A9 1 = 0)
      by (rewrite Hz1c; apply Zmod_0_l).
    assert (Hcx : adv Γ Advice.A3 2 = adv Γ Advice.A2 1)
      by (f_equal; exact Hcopy_x).
    assert (Hcy : adv Γ Advice.A4 1 = adv Γ Advice.A3 1)
      by (f_equal; exact Hcopy_y).
    set (bx :=
      UnOp.from (Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0)).
    set (byv :=
      UnOp.from (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0)).
    assert (Hcbx : adv Γ Advice.A0 2 = bx)
      by (subst bx; f_equal; exact Hcopy_bx).
    assert (Hcby : adv Γ Advice.A1 2 = byv)
      by (subst byv; f_equal; exact Hcopy_by).
    (* The witnessed base is a genuine affine point. *)
    assert (Hbp : VarBaseDefs.base_point Γ =
        {| Point.x := Γ.(Assignment.advice) Advice.A0
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p;
           Point.y := Γ.(Assignment.advice) Advice.A1
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p |}).
    { unfold VarBaseDefs.base_point, OrchardActionInputs.read_point,
        OrchardActionInputs.read, OrchardActionInputs.read1,
        OrchardActionInputs.read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : VarBaseDefs.base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold VarBaseDefs.base_wpoint.
      rewrite Hbp.
      unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0) &&
        (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0))%bool eqn:Hid.
      - exfalso. apply HBne.
        unfold VarBaseDefs.base_wpoint.
        rewrite Hbp.
        unfold PallasModel.unrepr.
        cbn [Point.x Point.y].
        rewrite Hid.
        reflexivity.
      - reflexivity. }
    (* The three hi gates of the configured system. *)
    pose proof (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteHi1 Advice.A3 Advice.A0 Advice.A4 Advice.A5)
        VarBaseDefs.mul_region 1
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate1.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteHi2 Advice.A9 Advice.A3 Advice.A0 Advice.A1
          Advice.A4 Advice.A5)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate2.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteHi3 Advice.A9 Advice.A3 Advice.A0 Advice.A1
          Advice.A4 Advice.A5)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate3.
    (* [q_mul_1]'s "init y_a": the entry accumulator's y expression. *)
    pose proof (QMul1Checks.deterministic Γ VarBaseDefs.mul_region 1
        Selector.QMulIncompleteHi1 Advice.A3 Advice.A0 Advice.A4 Advice.A5
        (enabled_nonzero Γ Selector.QMulIncompleteHi1 VarBaseDefs.mul_region 1
          Hsel1)
        Hgate1) as Hq1.
    unfold QMul1Checks.output in Hq1.
    injection Hq1.
    intro Hya2raw.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hya2raw.
    change (rotated_row 1 Rotation.next) with 2 in Hya2raw.
    change (rotated_row 1 Rotation.cur) with 1 in Hya2raw.
    (* The generic core at [n = 125], [m0 = 0]. *)
    assert (Hnd' : forall r, 2 <= r <= 125 + 1 ->
        adv Γ Advice.A3 r <> 0 /\
        adv Γ Advice.A3 r <> adv Γ Advice.A0 r /\
        x_r (adv Γ Advice.A3 r) (adv Γ Advice.A0 r) (adv Γ Advice.A4 r) <>
          adv Γ Advice.A3 r).
    { intros r Hr.
      specialize (Hnondeg r ltac:(lia)).
      unfold VarBaseDefs.hi_step_nondegenerate, VarBaseDefs.step_nondegenerate
        in Hnondeg.
      rewrite !av_adv in Hnondeg.
      exact Hnondeg. }
    assert (Hcap' : 2 ^ 125 * (adv Γ Advice.A9 1 + 1) <= 2 ^ 254).
    { rewrite Hz1adv.
      replace (0 + 1) with 1 by lia.
      rewrite Z.mul_1_r.
      apply Z.pow_le_mono_r; lia. }
    assert (Hacc0' :
        {| Point.x := adv Γ Advice.A3 2; Point.y := adv Γ Advice.A4 1 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 0 + 2 * adv Γ Advice.A9 1 + 1)
            (VarBaseDefs.base_wpoint Γ))).
    { rewrite Hcx, Hcy, Hz1adv.
      replace (2 ^ 0 + 2 * 0 + 1) with 2 by lia.
      rewrite !av_adv in Hinit.
      exact Hinit. }
    assert (Hsel2' : forall r, 2 <= r <= 125 ->
        Γ.(Assignment.selector) Selector.QMulIncompleteHi2
          VarBaseDefs.mul_region r = 1).
    { intros r Hr.
      apply (enable_selector_rows_on Γ VarBaseDefs.mul_region
        Selector.QMulIncompleteHi2 124 2 Hblock).
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
      lia. }
    pose proof (incomplete_half_generic Γ
      Selector.QMulIncompleteHi2 Selector.QMulIncompleteHi3
      Advice.A9 Advice.A3 Advice.A0 Advice.A1 Advice.A4 Advice.A5
      (VarBaseDefs.base_wpoint Γ) bx byv 125 0
      ltac:(lia) ltac:(lia) HB HBred HBoc Hcbx Hcby
      Hnd' Hcap' Hacc0' Hya2raw Hsel2' Hsel3 Hgate2 Hgate3) as Hmain.
    destruct Hmain as (Hr1 & Hr2 & Hr3).
    replace (125 + 1) with 126 in Hr1, Hr2 by lia.
    replace (125 + 2) with 127 in Hr3 by lia.
    replace (125 - 1) with 124 in Hr2 by lia.
    replace (0 + 125) with 125 in Hr3 by lia.
    rewrite !av_adv.
    split.
    { rewrite Hz1adv in Hr1. lia. }
    split.
    { assert (H124pos : 0 < 2 ^ 124) by (apply Z.pow_pos_nonneg; lia).
      replace (adv Γ Advice.A9 126)
        with (adv Γ Advice.A9 2 * 2 ^ 124 +
              (adv Γ Advice.A9 126 - 2 ^ 124 * adv Γ Advice.A9 2)) by lia.
      rewrite Z.div_add_l by lia.
      rewrite (Z.div_small
        (adv Γ Advice.A9 126 - 2 ^ 124 * adv Γ Advice.A9 2)) by lia.
      lia. }
    { replace (125 + 1) with 126 in Hr3 by lia.
      exact Hr3. }
  Qed.

  (** ** The lo incomplete half (126 steps)

      Statement identical to [VarBaseMul.lo_half_correct]
      ([circuit_proof/ownership/var_base_mul.v]). *)
  Lemma lo_half_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (VarBaseDefs.base_wpoint Γ))
      (HBoc : Pallas.on_curve (VarBaseDefs.base_wpoint Γ))
      (HBne : VarBaseDefs.base_wpoint Γ <> Pallas.identity)
      (Hnondeg : forall r, 2 <= r <= 127 ->
        VarBaseDefs.lo_step_nondegenerate Γ r)
      (Hz_hi : 0 <= VarBaseDefs.av Γ Advice.A9 126 < 2 ^ 125)
      (Hinit :
        {| Point.x := VarBaseDefs.av Γ Advice.A3 127;
           Point.y := VarBaseDefs.av Γ Advice.A4 127 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 125 + 2 * VarBaseDefs.av Γ Advice.A9 126 + 1)
            (VarBaseDefs.base_wpoint Γ))) :
    0 <= VarBaseDefs.av Γ Advice.A6 127 < 2 ^ 251 /\
    VarBaseDefs.av Γ Advice.A6 127 / 2 ^ 126 = VarBaseDefs.av Γ Advice.A9 126 /\
    {| Point.x := VarBaseDefs.av Γ Advice.A7 128;
       Point.y := VarBaseDefs.av Γ Advice.A8 128 |} =
    PallasModel.repr
      (Pallas.mul (2 ^ 251 + 2 * VarBaseDefs.av Γ Advice.A6 127 + 1)
        (VarBaseDefs.base_wpoint Γ)).
  Proof.
    (* Facts 14–21 of the region program: the three lo selector nodes and
       the boundary copies (the hi output spliced in as [z]/x/y, and the
       base re-copied at row 2). *)
    pose proof (VarBaseDefs.variable_base_region_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hsel1.
    do 14 apply interpret_region_facts_bind_right in Hsel1.
    apply interpret_region_facts_bind_left in Hsel1.
    cbn [region_facts interpret_facts interpret_fact] in Hsel1.
    destruct Hsel1 as [Hsel1 _].
    pose proof Hfacts as Hblock.
    do 15 apply interpret_region_facts_bind_right in Hblock.
    apply interpret_region_facts_bind_left in Hblock.
    pose proof Hfacts as Hsel3.
    do 16 apply interpret_region_facts_bind_right in Hsel3.
    apply interpret_region_facts_bind_left in Hsel3.
    cbn [region_facts interpret_facts interpret_fact] in Hsel3.
    destruct Hsel3 as [Hsel3 _].
    pose proof Hfacts as Hcopy_z.
    do 17 apply interpret_region_facts_bind_right in Hcopy_z.
    apply interpret_region_facts_bind_left in Hcopy_z.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_z.
    destruct Hcopy_z as [Hcopy_z _].
    pose proof Hfacts as Hcopy_x.
    do 18 apply interpret_region_facts_bind_right in Hcopy_x.
    apply interpret_region_facts_bind_left in Hcopy_x.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_x.
    destruct Hcopy_x as [Hcopy_x _].
    pose proof Hfacts as Hcopy_y.
    do 19 apply interpret_region_facts_bind_right in Hcopy_y.
    apply interpret_region_facts_bind_left in Hcopy_y.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_y.
    destruct Hcopy_y as [Hcopy_y _].
    pose proof Hfacts as Hcopy_bx.
    do 20 apply interpret_region_facts_bind_right in Hcopy_bx.
    apply interpret_region_facts_bind_left in Hcopy_bx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_bx.
    destruct Hcopy_bx as [Hcopy_bx _].
    pose proof Hfacts as Hcopy_by.
    do 21 apply interpret_region_facts_bind_right in Hcopy_by.
    apply interpret_region_facts_bind_left in Hcopy_by.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_by.
    destruct Hcopy_by as [Hcopy_by _].
    cbn in Hcopy_z, Hcopy_x, Hcopy_y, Hcopy_bx, Hcopy_by.
    assert (Hz1lo : adv Γ Advice.A6 1 = adv Γ Advice.A9 126)
      by (f_equal; exact Hcopy_z).
    assert (Hcx : adv Γ Advice.A7 2 = adv Γ Advice.A3 127)
      by (f_equal; exact Hcopy_x).
    assert (Hcy : adv Γ Advice.A8 1 = adv Γ Advice.A4 127)
      by (f_equal; exact Hcopy_y).
    set (bx :=
      UnOp.from (Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0)).
    set (byv :=
      UnOp.from (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0)).
    assert (Hcbx : adv Γ Advice.A0 2 = bx)
      by (subst bx; f_equal; exact Hcopy_bx).
    assert (Hcby : adv Γ Advice.A1 2 = byv)
      by (subst byv; f_equal; exact Hcopy_by).
    assert (Hbp : VarBaseDefs.base_point Γ =
        {| Point.x := Γ.(Assignment.advice) Advice.A0
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p;
           Point.y := Γ.(Assignment.advice) Advice.A1
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p |}).
    { unfold VarBaseDefs.base_point, OrchardActionInputs.read_point,
        OrchardActionInputs.read, OrchardActionInputs.read1,
        OrchardActionInputs.read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : VarBaseDefs.base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold VarBaseDefs.base_wpoint.
      rewrite Hbp.
      unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0) &&
        (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0))%bool eqn:Hid.
      - exfalso. apply HBne.
        unfold VarBaseDefs.base_wpoint.
        rewrite Hbp.
        unfold PallasModel.unrepr.
        cbn [Point.x Point.y].
        rewrite Hid.
        reflexivity.
      - reflexivity. }
    pose proof (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteLo1 Advice.A7 Advice.A0 Advice.A8 Advice.A2)
        VarBaseDefs.mul_region 1
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate1.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteLo2 Advice.A6 Advice.A7 Advice.A0 Advice.A1
          Advice.A8 Advice.A2)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate2.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteLo3 Advice.A6 Advice.A7 Advice.A0 Advice.A1
          Advice.A8 Advice.A2)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate3.
    pose proof (QMul1Checks.deterministic Γ VarBaseDefs.mul_region 1
        Selector.QMulIncompleteLo1 Advice.A7 Advice.A0 Advice.A8 Advice.A2
        (enabled_nonzero Γ Selector.QMulIncompleteLo1 VarBaseDefs.mul_region 1
          Hsel1)
        Hgate1) as Hq1.
    unfold QMul1Checks.output in Hq1.
    injection Hq1.
    intro Hya2raw.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hya2raw.
    change (rotated_row 1 Rotation.next) with 2 in Hya2raw.
    change (rotated_row 1 Rotation.cur) with 1 in Hya2raw.
    rewrite !av_adv in Hz_hi, Hinit.
    (* The generic core at [n = 126], [m0 = 125]. *)
    assert (Hnd' : forall r, 2 <= r <= 126 + 1 ->
        adv Γ Advice.A7 r <> 0 /\
        adv Γ Advice.A7 r <> adv Γ Advice.A0 r /\
        x_r (adv Γ Advice.A7 r) (adv Γ Advice.A0 r) (adv Γ Advice.A8 r) <>
          adv Γ Advice.A7 r).
    { intros r Hr.
      specialize (Hnondeg r ltac:(lia)).
      unfold VarBaseDefs.lo_step_nondegenerate, VarBaseDefs.step_nondegenerate
        in Hnondeg.
      rewrite !av_adv in Hnondeg.
      exact Hnondeg. }
    assert (Hpow251 : (2:Z) ^ 126 * 2 ^ 125 = 2 ^ 251)
      by (rewrite <- Z.pow_add_r by lia; reflexivity).
    assert (Hcap' : 2 ^ 126 * (adv Γ Advice.A6 1 + 1) <= 2 ^ 254).
    { rewrite Hz1lo.
      assert (Hle : adv Γ Advice.A9 126 + 1 <= 2 ^ 125) by lia.
      assert (Hmul : 2 ^ 126 * (adv Γ Advice.A9 126 + 1) <= 2 ^ 126 * 2 ^ 125)
        by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hp3 : (2:Z) ^ 251 <= 2 ^ 254) by (apply Z.pow_le_mono_r; lia).
      lia. }
    assert (Hacc0' :
        {| Point.x := adv Γ Advice.A7 2; Point.y := adv Γ Advice.A8 1 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 125 + 2 * adv Γ Advice.A6 1 + 1)
            (VarBaseDefs.base_wpoint Γ))).
    { rewrite Hcx, Hcy, Hz1lo.
      exact Hinit. }
    assert (Hsel2' : forall r, 2 <= r <= 126 ->
        Γ.(Assignment.selector) Selector.QMulIncompleteLo2
          VarBaseDefs.mul_region r = 1).
    { intros r Hr.
      apply (enable_selector_rows_on Γ VarBaseDefs.mul_region
        Selector.QMulIncompleteLo2 125 2 Hblock).
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
      lia. }
    pose proof (incomplete_half_generic Γ
      Selector.QMulIncompleteLo2 Selector.QMulIncompleteLo3
      Advice.A6 Advice.A7 Advice.A0 Advice.A1 Advice.A8 Advice.A2
      (VarBaseDefs.base_wpoint Γ) bx byv 126 125
      ltac:(lia) ltac:(lia) HB HBred HBoc Hcbx Hcby
      Hnd' Hcap' Hacc0' Hya2raw Hsel2' Hsel3 Hgate2 Hgate3) as Hmain.
    destruct Hmain as (Hr1 & _ & Hr3).
    replace (126 + 1) with 127 in Hr1, Hr3 by lia.
    replace (126 + 2) with 128 in Hr3 by lia.
    replace (125 + 126) with 251 in Hr3 by lia.
    rewrite Hz1lo in Hr1.
    rewrite !av_adv.
    split.
    { assert (Hle : adv Γ Advice.A9 126 <= 2 ^ 125 - 1) by lia.
      assert (Hmul_hi :
          2 ^ 126 * adv Γ Advice.A9 126 <= 2 ^ 126 * (2 ^ 125 - 1))
        by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hmul_lo : 0 <= 2 ^ 126 * adv Γ Advice.A9 126)
        by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    split.
    { assert (H126pos : 0 < 2 ^ 126) by (apply Z.pow_pos_nonneg; lia).
      replace (adv Γ Advice.A6 127)
        with (adv Γ Advice.A9 126 * 2 ^ 126 +
              (adv Γ Advice.A6 127 - 2 ^ 126 * adv Γ Advice.A9 126)) by lia.
      rewrite Z.div_add_l by lia.
      rewrite (Z.div_small
        (adv Γ Advice.A6 127 - 2 ^ 126 * adv Γ Advice.A9 126)) by lia.
      lia. }
    { exact Hr3. }
  Qed.

End VarBaseIncomplete.
