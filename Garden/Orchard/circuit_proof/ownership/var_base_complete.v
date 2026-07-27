(** * Variable-base scalar multiplication: the three complete rounds

    The complete-bits phase of the address-integrity variable-base [mul]
    composition ([circuit_proof/ownership/var_base_mul.v]): bits
    [k_3, k_2, k_1] are processed at rows 128–135 of the variable-base
    region by three identical rounds, each a [QMulDecomposeVar] running-sum
    step plus two [QEccAdd] complete additions.  [complete_bits_correct]
    below is the phase's cut obligation, stated exactly as
    [VarBaseMul.complete_bits_correct]: from the lo-half output (running sum
    [z_4 = A6@127], accumulator [(A7@128, A8@128)]), the phase ends at
    [z_1 = A9@135 < 2^254] with the [/ 2^3] division link and the
    accumulator [(A2@135, A3@135)] on the [repr ([2^254 + 2 z_1 + 1] B)]
    multiple.

    Round layout (decompose row [d = 130, 132, 134]; [r = d - 1]):
    - [z]: [A9@(d-1)] (previous running sum; [A9@129] is the [A6@127] copy)
      and [A9@(d+1)] (next), constrained by the [QMulDecomposeVar] gate at
      [d] to differ by a boolean bit [k = z_next - 2 z_prev];
    - the gate's [y_switch] ternary pins the witnessed [A1@r] to [±base_y]
      ([base_y] itself re-witnessed at [A9@d] by a [Copy] from the [GDOld]
      cell), so [(A0@r, A1@r)] is [repr (signed_base B k)] ([A0@r] is a
      [Copy] of [base_x]);
    - [QEccAdd@r] adds it to the accumulator [(A2@r, A3@r)], and
      [QEccAdd@d] adds the accumulator to that intermediate (the round's
      copies re-feed the accumulator at [(A0@d, A1@d)]), landing the
      multiple on [2c + 2k − 1] ([double_add_step_multiple]'s shape, glued
      through [PallasModel.repr_add] on the multiples-of-[B] subgroup).

    The generic round is [round_correct]; the phase lemma peels the three
    rounds explicitly (facts 22–58 of the region program, the indices
    validated by [VarBaseMul.lsb_correct]'s 59–62). *)

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
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete_proof.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
(* [Garden.Plonky3.M] is deliberately Require'd but NOT Imported: its
   notations break nested or-intropatterns ([destruct H as [A | [B | C]]]
   fails to parse under it).  [Primes] and the [PallasPIsPrime] instance are
   the [Field.Field] originals that [M.Primes] aliases; the few [M]-qualified
   rewrite lemmas below are referenced by full path. *)
Require Garden.Plonky3.M.
Require Import Garden.Field.Field.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module VarBaseComplete.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The shared surface of [var_base_defs.v], under the same abbreviations
      as [VarBaseMul]. *)
  Notation mul_region := VarBaseDefs.mul_region.
  Notation gd_old_region := VarBaseDefs.gd_old_region.
  Notation av := VarBaseDefs.av.
  Notation base_point := VarBaseDefs.base_point.
  Notation base_wpoint := VarBaseDefs.base_wpoint.
  Notation signed_base := VarBaseDefs.signed_base.
  Notation signed_base_mul := VarBaseDefs.signed_base_mul.
  Notation pallas_mul_add := VarBaseDefs.pallas_mul_add.
  Notation pallas_mul_neg := VarBaseDefs.pallas_mul_neg.
  Notation pallas_mul_one := VarBaseDefs.pallas_mul_one.
  Notation pallas_mul_on_curve := VarBaseDefs.pallas_mul_on_curve.
  Notation pallas_mul_reduced := VarBaseDefs.pallas_mul_reduced.
  Notation pallas_neg_on_curve := VarBaseDefs.pallas_neg_on_curve.
  Notation pallas_neg_reduced := VarBaseDefs.pallas_neg_reduced.
  Notation variable_base_region_facts := VarBaseDefs.variable_base_region_facts.

  (** ** Small evaluation helpers *)

  (** Every field evaluation is reduced. *)
  Lemma from_bound (w : Z) : 0 <= UnOp.from w < Primes.pallas_p.
  Proof.
    unfold UnOp.from. apply Z.mod_pos_bound.
    change Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337.
    lia.
  Qed.

  (** The region reader, in raw-cell form (the shape the [Copy] facts and
      the [cbn]-normalized gate evaluations expose). *)
  Lemma av_eq
      (Γ : Assignment.t columns RegionId.t) (column : Advice.t) (row : Z) :
    av Γ column row =
    UnOp.from (Γ.(Assignment.advice) column mul_region row).
  Proof.
    unfold VarBaseDefs.av, read_advice.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
    unfold rotated_row. cbn [Rotation.cur Rotation.offset].
    now rewrite Z.add_0_r.
  Qed.

  (** The two forced evaluations of the [ternary] gate combinator. *)
  Lemma ternary_one (t f : Z) : 1 *F t +F (1 -F 1) *F f = UnOp.from t.
  Proof.
    unfold BinOp.add, BinOp.mul, BinOp.sub, UnOp.from.
    change Garden.Plonky3.M.Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337.
    change Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337.
    replace (1 - 1) with 0 by ring.
    rewrite Zmod_0_l.
    rewrite Z.add_0_r.
    rewrite Z.mod_mod by lia.
    rewrite Z.mul_1_l.
    reflexivity.
  Qed.

  Lemma ternary_zero (t f : Z) : 0 *F t +F (1 -F 0) *F f = UnOp.from f.
  Proof.
    unfold BinOp.add, BinOp.mul, BinOp.sub, UnOp.from.
    change Garden.Plonky3.M.Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337.
    change Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337.
    rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_l.
    replace (1 - 0) with 1 by ring.
    rewrite (Z.mod_small 1) by lia.
    rewrite Z.mul_1_l.
    rewrite Z.mod_mod by lia.
    reflexivity.
  Qed.

  (** ** One complete round

      Rows [r] and [r + 1] ([r = 129, 131, 133]): the [QMulDecomposeVar]
      gate at [r + 1] and the two [QEccAdd] complete additions, from the
      round's [Copy] facts (the base [x] at [A0@r], the re-witnessed base
      [y] at [A9@(r+1)], and the accumulator re-fed at [(A0, A1)@(r+1)]).
      Concludes the boolean running-sum step and the multiple update
      [c ↦ 2c + 2k − 1]. *)
  Lemma round_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (r c : Z)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (Hsel_dec :
        Γ.(Assignment.selector) Selector.QMulDecomposeVar mul_region (r + 1) =
        1)
      (Hsel_add1 : Γ.(Assignment.selector) Selector.QEccAdd mul_region r = 1)
      (Hsel_add2 :
        Γ.(Assignment.selector) Selector.QEccAdd mul_region (r + 1) = 1)
      (Hcopy_bx :
        Γ.(Assignment.advice) Advice.A0 mul_region r =
        Γ.(Assignment.advice) Advice.A0 gd_old_region 0)
      (Hcopy_by :
        Γ.(Assignment.advice) Advice.A9 mul_region (r + 1) =
        Γ.(Assignment.advice) Advice.A1 gd_old_region 0)
      (Hcopy_ax :
        Γ.(Assignment.advice) Advice.A0 mul_region (r + 1) =
        Γ.(Assignment.advice) Advice.A2 mul_region r)
      (Hcopy_ay :
        Γ.(Assignment.advice) Advice.A1 mul_region (r + 1) =
        Γ.(Assignment.advice) Advice.A3 mul_region r)
      (Hz : 0 <= av Γ Advice.A9 r < 2 ^ 253)
      (Hacc :
        {| Point.x := av Γ Advice.A2 r; Point.y := av Γ Advice.A3 r |} =
        PallasModel.repr (Pallas.mul c (base_wpoint Γ))) :
    (av Γ Advice.A9 (r + 2) - 2 * av Γ Advice.A9 r = 0 \/
     av Γ Advice.A9 (r + 2) - 2 * av Γ Advice.A9 r = 1) /\
    {| Point.x := av Γ Advice.A2 (r + 2); Point.y := av Γ Advice.A3 (r + 2) |} =
    PallasModel.repr
      (Pallas.mul
        (2 * c + 2 * (av Γ Advice.A9 (r + 2) - 2 * av Γ Advice.A9 r) - 1)
        (base_wpoint Γ)).
  Proof.
    (* The three gate instances at the round's rows. *)
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
          .decompose_scalar_complete_gate
        mul_region (r + 1)
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (holds_gates Γ Hcircuit)) as Hdec.
    cbn in Hdec.
    destruct Hdec as [Hbool Hswitch].
    specialize (Hbool
      (enabled_nonzero Γ Selector.QMulDecomposeVar mul_region (r + 1) Hsel_dec)).
    specialize (Hswitch
      (enabled_nonzero Γ Selector.QMulDecomposeVar mul_region (r + 1) Hsel_dec)).
    unfold rotated_row in Hbool, Hswitch.
    cbn [Rotation.next Rotation.prev Rotation.cur Rotation.offset]
      in Hbool, Hswitch.
    replace (r + 1 + 1) with (r + 2) in Hbool, Hswitch by lia.
    replace (r + 1 + -1) with r in Hbool, Hswitch by lia.
    replace (r + 1 + 0) with (r + 1) in Hswitch by lia.
    (* The boolean running-sum step, over the integers. *)
    rewrite !av_eq in Hz, Hacc |- *.
    set (zP := UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region r)) in *.
    set (zN := UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region (r + 2)))
      in *.
    set (L := zN -F 2 *F zP) in *.
    assert (HL : L = 0 \/ L = 1)
      by (rewrite Hbool; destruct (Z.odd L); [right | left]; reflexivity).
    assert (HLmod : L = (zN - 2 * zP) mod Primes.pallas_p)
      by apply Zminus_mod_idemp_r.
    assert (HzN : 0 <= zN < Primes.pallas_p) by apply from_bound.
    assert (Hpw : 2 * 2 ^ 253 <
      28948022309329048855892746252171976963363056481941560715954676764349967630337)
      by (vm_compute; reflexivity).
    repeat rewrite av_eq in Hacc.
    repeat rewrite av_eq.
    fold zP zN.
    assert (HK : zN - 2 * zP = 0 \/ zN - 2 * zP = 1).
    { change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        in HLmod, HzN.
      destruct HL as [H0 | H1].
      - left.
        rewrite H0 in HLmod.
        symmetry in HLmod.
        apply Z.mod_divide in HLmod; [| lia].
        destruct HLmod as [m Hm].
        clear - Hm Hz HzN Hpw. nia.
      - right.
        rewrite H1 in HLmod.
        assert (Hd : (zN - 2 * zP - 1) mod
          28948022309329048855892746252171976963363056481941560715954676764349967630337
          = 0).
        { rewrite Zminus_mod, <- HLmod, Z.sub_diag. apply Zmod_0_l. }
        apply Z.mod_divide in Hd; [| lia].
        destruct Hd as [m Hm].
        clear - Hm Hz HzN Hpw. nia. }
    split; [exact HK |].
    (* The two complete additions. *)
    pose proof
      (CompleteAddition.deterministic Γ mul_region r
        (enabled_nonzero Γ Selector.QEccAdd mul_region r Hsel_add1)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate
          mul_region r
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          (holds_gates Γ Hcircuit))) as Hdet1.
    pose proof
      (CompleteAddition.deterministic Γ mul_region (r + 1)
        (enabled_nonzero Γ Selector.QEccAdd mul_region (r + 1) Hsel_add2)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate
          mul_region (r + 1)
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          (holds_gates Γ Hcircuit))) as Hdet2.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hdet1, Hdet2.
    unfold rotated_row in Hdet1, Hdet2.
    cbn [Rotation.next Rotation.cur Rotation.offset] in Hdet1, Hdet2.
    replace (r + 0) with r in Hdet1 by lia.
    replace (r + 1 + 0) with (r + 1) in Hdet2 by lia.
    replace (r + 1 + 1) with (r + 2) in Hdet2 by lia.
    (* The witnessed base coordinates. *)
    set (yw := UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region r)) in *.
    set (byc := UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region (r + 1)))
      in *.
    set (bx := UnOp.from (Γ.(Assignment.advice) Advice.A0 gd_old_region 0))
      in *.
    set (byv := UnOp.from (Γ.(Assignment.advice) Advice.A1 gd_old_region 0))
      in *.
    assert (Hbyc : byc = byv)
      by (unfold byc, byv; rewrite Hcopy_by; reflexivity).
    assert (Hbp : base_point Γ = {| Point.x := bx; Point.y := byv |}).
    { unfold VarBaseDefs.base_point, read_point, read, read1, read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold VarBaseDefs.base_wpoint. rewrite Hbp. unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((bx =? 0) && (byv =? 0))%bool eqn:Hid.
      - exfalso. apply HBne. unfold VarBaseDefs.base_wpoint. rewrite Hbp.
        unfold PallasModel.unrepr. cbn [Point.x Point.y]. rewrite Hid.
        reflexivity.
      - reflexivity. }
    assert (HLK : L = zN - 2 * zP).
    { rewrite HLmod. apply Z.mod_small.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      destruct HK as [Hk | Hk]; lia. }
    (* The [y_switch] ternary pins the witnessed point to [[2k−1] B]. *)
    assert (Hwit :
      {| Point.x := UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region r);
         Point.y := yw |} =
      PallasModel.repr
        (Pallas.mul (2 * (zN - 2 * zP) - 1) (base_wpoint Γ))).
    { assert (Hxw : UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region r) = bx)
        by (unfold bx; rewrite Hcopy_bx; reflexivity).
      assert (Hyw_b : 0 <= yw <
        28948022309329048855892746252171976963363056481941560715954676764349967630337)
        by apply from_bound.
      assert (Hby_b : 0 <= byv <
        28948022309329048855892746252171976963363056481941560715954676764349967630337)
        by apply from_bound.
      assert (Hbyc_b : 0 <= byc <
        28948022309329048855892746252171976963363056481941560715954676764349967630337)
        by apply from_bound.
      destruct HK as [Hk | Hk].
      - (* k = 0: the witnessed point is −B. *)
        assert (HL0 : L = 0) by (rewrite HLK, Hk; reflexivity).
        rewrite HL0 in Hswitch.
        rewrite ternary_zero in Hswitch.
        change (byc +F yw) with (UnOp.from (byc + yw)) in Hswitch.
        rewrite Garden.Plonky3.M.FieldRewrite.from_from in Hswitch.
        unfold UnOp.from in Hswitch.
        change Garden.Plonky3.M.Primes.pallas_p with
          28948022309329048855892746252171976963363056481941560715954676764349967630337
          in Hswitch.
        change Primes.pallas_p with
          28948022309329048855892746252171976963363056481941560715954676764349967630337
          in Hswitch.
        apply Z.mod_divide in Hswitch; [| lia].
        destruct Hswitch as [m Hm].
        rewrite Hbyc in Hm.
        assert (Hyp : yw + byv = 0 \/
          yw + byv =
          28948022309329048855892746252171976963363056481941560715954676764349967630337)
          by (clear - Hm Hyw_b Hby_b; nia).
        rewrite Hk.
        replace (2 * 0 - 1) with (- (1)) by lia.
        rewrite (pallas_mul_neg 1 _ HBred), pallas_mul_one.
        rewrite HB.
        cbn [Pallas.neg Weierstrass.neg PallasModel.repr].
        f_equal.
        + exact Hxw.
        + unfold UnOp.opp.
          change Garden.Plonky3.M.Primes.pallas_p with
            28948022309329048855892746252171976963363056481941560715954676764349967630337.
          destruct Hyp as [Hyp0 | Hypp].
          * assert (Hy0 : yw = 0) by lia.
            assert (Hb0 : byv = 0) by lia.
            rewrite Hy0, Hb0. reflexivity.
          * assert (Hbnz : byv <> 0) by lia.
            rewrite Z.mod_opp_l_nz.
            -- rewrite (Z.mod_small byv) by lia. lia.
            -- lia.
            -- rewrite (Z.mod_small byv) by lia. exact Hbnz.
      - (* k = 1: the witnessed point is B itself. *)
        assert (HL1 : L = 1) by (rewrite HLK, Hk; reflexivity).
        rewrite HL1 in Hswitch.
        rewrite ternary_one in Hswitch.
        change (byc -F yw) with (UnOp.from (byc - yw)) in Hswitch.
        rewrite Garden.Plonky3.M.FieldRewrite.from_from in Hswitch.
        unfold UnOp.from in Hswitch.
        change Garden.Plonky3.M.Primes.pallas_p with
          28948022309329048855892746252171976963363056481941560715954676764349967630337
          in Hswitch.
        change Primes.pallas_p with
          28948022309329048855892746252171976963363056481941560715954676764349967630337
          in Hswitch.
        apply Z.mod_divide in Hswitch; [| lia].
        destruct Hswitch as [m Hm].
        assert (Hyweq : yw = byv)
          by (rewrite <- Hbyc; clear - Hm Hyw_b Hbyc_b; nia).
        rewrite Hk.
        replace (2 * 1 - 1) with 1 by lia.
        rewrite pallas_mul_one.
        rewrite HB.
        cbn [PallasModel.repr].
        f_equal; [exact Hxw | exact Hyweq]. }
    (* First addition: [(±B) + acc], glued through [repr]. *)
    change (CompleteAddition.output
        (UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region r)) yw
        (UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region r))
        (UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region r)))
      with (EccSpec.point_add
        {| Point.x := UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region r);
           Point.y := yw |}
        {| Point.x := UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region r);
           Point.y := UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region r) |})
      in Hdet1.
    rewrite Hwit, Hacc in Hdet1.
    assert (Hred1 :
      Pallas.reduced (Pallas.mul (2 * (zN - 2 * zP) - 1) (base_wpoint Γ)))
      by (apply pallas_mul_reduced; exact HBred).
    assert (Hoc1 :
      Pallas.on_curve (Pallas.mul (2 * (zN - 2 * zP) - 1) (base_wpoint Γ)))
      by (apply pallas_mul_on_curve; exact HBoc).
    assert (Hredc : Pallas.reduced (Pallas.mul c (base_wpoint Γ)))
      by (apply pallas_mul_reduced; exact HBred).
    assert (Hocc : Pallas.on_curve (Pallas.mul c (base_wpoint Γ)))
      by (apply pallas_mul_on_curve; exact HBoc).
    rewrite <- (PallasModel.repr_add _ _ Hred1 Hredc Hoc1 Hocc) in Hdet1.
    change PallasModel.wadd with Pallas.add in Hdet1.
    rewrite <- (pallas_mul_add (2 * (zN - 2 * zP) - 1) c _ HBred HBoc) in Hdet1.
    (* Second addition: [acc + intermediate]. *)
    rewrite Hcopy_ax, Hcopy_ay in Hdet2.
    change (CompleteAddition.output
        (UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region r))
        (UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region r))
        (UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region (r + 1)))
        (UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region (r + 1))))
      with (EccSpec.point_add
        {| Point.x := UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region r);
           Point.y := UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region r) |}
        {| Point.x :=
             UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region (r + 1));
           Point.y :=
             UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region (r + 1)) |})
      in Hdet2.
    rewrite Hacc, Hdet1 in Hdet2.
    assert (Hred2 :
      Pallas.reduced (Pallas.mul (2 * (zN - 2 * zP) - 1 + c) (base_wpoint Γ)))
      by (apply pallas_mul_reduced; exact HBred).
    assert (Hoc2 :
      Pallas.on_curve (Pallas.mul (2 * (zN - 2 * zP) - 1 + c) (base_wpoint Γ)))
      by (apply pallas_mul_on_curve; exact HBoc).
    rewrite <- (PallasModel.repr_add _ _ Hredc Hred2 Hocc Hoc2) in Hdet2.
    change PallasModel.wadd with Pallas.add in Hdet2.
    rewrite <- (pallas_mul_add c (2 * (zN - 2 * zP) - 1 + c) _ HBred HBoc)
      in Hdet2.
    rewrite Hdet2.
    f_equal.
    f_equal.
    lia.
  Qed.

  (** ** Walking the region program

      [pull_fact] extracts the head fact of the remaining region program into
      [Hout] and advances [Hrest] past it; [skip_fact] only advances.  The
      same peeling as [VarBaseMul.lsb_correct]'s [do N …; bind_left] blocks,
      but walking the [Bind] chain once. *)
  Ltac pull_fact Hrest Hout :=
    pose proof Hrest as Hout;
    apply interpret_region_facts_bind_left in Hout;
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hout;
    destruct Hout as [Hout _];
    cbn in Hout;
    apply interpret_region_facts_bind_right in Hrest.

  Ltac skip_fact Hrest :=
    apply interpret_region_facts_bind_right in Hrest.

  (** ** The phase lemma

      Statement identical to [VarBaseMul.complete_bits_correct]
      ([circuit_proof/ownership/var_base_mul.v]). *)
  Lemma complete_bits_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (Hz_lo : 0 <= av Γ Advice.A6 127 < 2 ^ 251)
      (Hinit :
        {| Point.x := av Γ Advice.A7 128; Point.y := av Γ Advice.A8 128 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 251 + 2 * av Γ Advice.A6 127 + 1) (base_wpoint Γ))) :
    0 <= av Γ Advice.A9 135 < 2 ^ 254 /\
    av Γ Advice.A9 135 / 2 ^ 3 = av Γ Advice.A6 127 /\
    {| Point.x := av Γ Advice.A2 135; Point.y := av Γ Advice.A3 135 |} =
    PallasModel.repr
      (Pallas.mul (2 ^ 254 + 2 * av Γ Advice.A9 135 + 1) (base_wpoint Γ)).
  Proof.
    (* Facts 22–56 of the region program: the three [QMulDecomposeVar]
       selectors, the [z]/base/accumulator [Copy] splices and the six
       [QEccAdd] selectors of the three rounds. *)
    pose proof (variable_base_region_facts Γ Hcircuit) as Hrest.
    do 22 apply interpret_region_facts_bind_right in Hrest.
    pull_fact Hrest Hsd1.   (* 22: QMulDecomposeVar@130 *)
    pull_fact Hrest Hsd2.   (* 23: QMulDecomposeVar@132 *)
    pull_fact Hrest Hsd3.   (* 24: QMulDecomposeVar@134 *)
    pull_fact Hrest Hzs.    (* 25: A9@129 ← A6@127 *)
    pull_fact Hrest Hby1.   (* 26: A9@130 ← base_y *)
    pull_fact Hrest Hsa1.   (* 27: QEccAdd@129 *)
    pull_fact Hrest Hbx1.   (* 28: A0@129 ← base_x *)
    skip_fact Hrest.        (* 29: A1@129 self *)
    pull_fact Hrest Hqx1.   (* 30: A2@129 ← A7@128 *)
    pull_fact Hrest Hqy1.   (* 31: A3@129 ← A8@128 *)
    pull_fact Hrest Hsa2.   (* 32: QEccAdd@130 *)
    pull_fact Hrest Hax1.   (* 33: A0@130 ← A7@128 *)
    pull_fact Hrest Hay1.   (* 34: A1@130 ← A8@128 *)
    skip_fact Hrest.        (* 35–36: A2/A3@130 self *)
    skip_fact Hrest.
    pull_fact Hrest Hby2.   (* 37: A9@132 ← base_y *)
    pull_fact Hrest Hsa3.   (* 38: QEccAdd@131 *)
    pull_fact Hrest Hbx2.   (* 39: A0@131 ← base_x *)
    skip_fact Hrest.        (* 40–42: A1/A2/A3@131 self *)
    skip_fact Hrest.
    skip_fact Hrest.
    pull_fact Hrest Hsa4.   (* 43: QEccAdd@132 *)
    pull_fact Hrest Hax2.   (* 44: A0@132 ← A2@131 *)
    pull_fact Hrest Hay2.   (* 45: A1@132 ← A3@131 *)
    skip_fact Hrest.        (* 46–47: A2/A3@132 self *)
    skip_fact Hrest.
    pull_fact Hrest Hby3.   (* 48: A9@134 ← base_y *)
    pull_fact Hrest Hsa5.   (* 49: QEccAdd@133 *)
    pull_fact Hrest Hbx3.   (* 50: A0@133 ← base_x *)
    skip_fact Hrest.        (* 51–53: A1/A2/A3@133 self *)
    skip_fact Hrest.
    skip_fact Hrest.
    pull_fact Hrest Hsa6.   (* 54: QEccAdd@134 *)
    pull_fact Hrest Hax3.   (* 55: A0@134 ← A2@133 *)
    pull_fact Hrest Hay3.   (* 56: A1@134 ← A3@133 *)
    clear Hrest.
    assert (Hp252 : 2 ^ 252 = 2 * 2 ^ 251) by (rewrite <- Z.pow_succ_r; lia).
    assert (Hp253 : 2 ^ 253 = 2 * 2 ^ 252) by (rewrite <- Z.pow_succ_r; lia).
    assert (Hp254 : 2 ^ 254 = 2 * 2 ^ 253) by (rewrite <- Z.pow_succ_r; lia).
    (* Round 1 (bit k_3, rows 129–130).  The lo-half output is spliced in by
       the [A6@127 → A9@129] (z) and [A7/A8@128 → A2/A3@129] (accumulator)
       copies; the accumulator is re-fed at [(A0, A1)@130] through the same
       [A7/A8@128] cells. *)
    assert (Hz9 : av Γ Advice.A9 129 = av Γ Advice.A6 127)
      by (repeat rewrite av_eq; rewrite Hzs; reflexivity).
    assert (Hax1' :
      Γ.(Assignment.advice) Advice.A0 mul_region 130 =
      Γ.(Assignment.advice) Advice.A2 mul_region 129)
      by (rewrite Hax1, Hqx1; reflexivity).
    assert (Hay1' :
      Γ.(Assignment.advice) Advice.A1 mul_region 130 =
      Γ.(Assignment.advice) Advice.A3 mul_region 129)
      by (rewrite Hay1, Hqy1; reflexivity).
    assert (Hacc1 :
      {| Point.x := av Γ Advice.A2 129; Point.y := av Γ Advice.A3 129 |} =
      PallasModel.repr
        (Pallas.mul (2 ^ 251 + 2 * av Γ Advice.A6 127 + 1) (base_wpoint Γ))).
    { repeat rewrite av_eq.
      rewrite Hqx1, Hqy1.
      repeat rewrite av_eq in Hinit.
      exact Hinit. }
    assert (Hzr1 : 0 <= av Γ Advice.A9 129 < 2 ^ 253)
      by (rewrite Hz9; lia).
    pose proof
      (round_correct Γ Hcircuit 129 (2 ^ 251 + 2 * av Γ Advice.A6 127 + 1)
        HBred HBoc HBne Hsd1 Hsa1 Hsa2 Hbx1 Hby1 Hax1' Hay1' Hzr1 Hacc1)
      as [HK1 HP1].
    change (129 + 2) with 131 in HK1, HP1.
    (* Round 2 (bit k_2, rows 131–132). *)
    assert (Hacc2 :
      {| Point.x := av Γ Advice.A2 131; Point.y := av Γ Advice.A3 131 |} =
      PallasModel.repr
        (Pallas.mul (2 ^ 252 + 2 * av Γ Advice.A9 131 + 1) (base_wpoint Γ))).
    { etransitivity; [exact HP1 |].
      f_equal. f_equal.
      clear - Hz9 Hp252. lia. }
    assert (Hzr2 : 0 <= av Γ Advice.A9 131 < 2 ^ 253)
      by (clear - HK1 Hzr1 Hz9 Hz_lo Hp252 Hp253; lia).
    pose proof
      (round_correct Γ Hcircuit 131 (2 ^ 252 + 2 * av Γ Advice.A9 131 + 1)
        HBred HBoc HBne Hsd2 Hsa3 Hsa4 Hbx2 Hby2 Hax2 Hay2 Hzr2 Hacc2)
      as [HK2 HP2].
    change (131 + 2) with 133 in HK2, HP2.
    (* Round 3 (bit k_1, rows 133–134). *)
    assert (Hacc3 :
      {| Point.x := av Γ Advice.A2 133; Point.y := av Γ Advice.A3 133 |} =
      PallasModel.repr
        (Pallas.mul (2 ^ 253 + 2 * av Γ Advice.A9 133 + 1) (base_wpoint Γ))).
    { etransitivity; [exact HP2 |].
      f_equal. f_equal.
      clear - Hp253. lia. }
    assert (Hzr3 : 0 <= av Γ Advice.A9 133 < 2 ^ 253)
      by (clear - HK2 Hzr2 HK1 Hzr1 Hz9 Hz_lo Hp252 Hp253; lia).
    pose proof
      (round_correct Γ Hcircuit 133 (2 ^ 253 + 2 * av Γ Advice.A9 133 + 1)
        HBred HBoc HBne Hsd3 Hsa5 Hsa6 Hbx3 Hby3 Hax3 Hay3 Hzr3 Hacc3)
      as [HK3 HP3].
    change (133 + 2) with 135 in HK3, HP3.
    (* The three conjuncts: the [z_1] range, the [/ 2^3] division link and
       the accumulator multiple. *)
    split; [| split].
    - clear - HK1 HK2 HK3 Hz9 Hz_lo Hp252 Hp253 Hp254. lia.
    - change (2 ^ 3) with 8.
      replace (av Γ Advice.A9 135)
        with (av Γ Advice.A6 127 * 8 +
          (av Γ Advice.A9 135 - av Γ Advice.A6 127 * 8))
        by lia.
      rewrite Z.div_add_l by lia.
      rewrite (Z.div_small (av Γ Advice.A9 135 - av Γ Advice.A6 127 * 8) 8)
        by (clear - HK1 HK2 HK3 Hz9 Hz_lo; lia).
      lia.
    - etransitivity; [exact HP3 |].
      f_equal. f_equal.
      clear - Hp254. lia.
  Qed.
End VarBaseComplete.
