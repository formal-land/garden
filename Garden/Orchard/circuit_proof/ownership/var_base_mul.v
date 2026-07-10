(** * Variable-base scalar multiplication: the address-integrity composition

    The composition target for the [[ivk] g_d_old] block of
    [synthesize_address_integrity] ([Garden/Orchard/circuit.v]): from
    [Holds Γ], the output point of the variable-base [mul] chip
    ([ecc/chip/mul.v], synthesized at the
    [RegionId.AddressIntegrity.Mul.VariableBase] region over 137 rows) equals
    [PallasModel.repr (Pallas.mul α B)] for the scalar cell [α] (the [ivk]
    x-coordinate, [CommitIvk.CompletePointAdd] [A2@1]) and the witnessed base
    [B] (the [GDOld] witness point).

    The per-row gate facts are proved in
    [ecc/chip/mul/incomplete_proof.v] / [overflow_proof.v] /
    [complete_proof.v] / [mul_proof.v]; this file states the whole-region
    composition, phase by phase, mirroring the circuit's layout:

    - rows 0–1: the initial complete doubling [acc := [2]B]
      ([init_acc_correct]);
    - rows 1–127 ("hi" incomplete half, columns [z=A9, x_a=A3, λ₁=A4,
      λ₂=A5]): 125 double-and-add steps, one per bit [k_254..k_130]
      ([hi_half_correct]);
    - rows 1–128 ("lo" incomplete half, columns [z=A6, x_a=A7, λ₁=A8,
      λ₂=A2]): 126 steps for bits [k_129..k_4] ([lo_half_correct]);
    - rows 128–135: three complete double-and-add rounds for bits
      [k_3, k_2, k_1] ([complete_bits_correct]);
    - rows 135–136: the LSB round ([lsb_correct]);
    - the overflow block ([Mul.OverflowS] / [OverflowLookup] /
      [OverflowCheck]): the recovered 255-bit running sum equals
      [α + t_q] over the integers ([overflow_scalar_exact], via the pure
      arithmetic core [overflow_no_wrap]).

    The maintained invariant is that after processing bits down to protocol
    index [i], the accumulator is [repr ([2^(255-i) + 2·z_i + 1] B)], where
    [z_i] is the running sum of the processed bits — [z_i] is a circuit cell
    at every phase boundary, so the per-phase statements compose without any
    side bookkeeping.  After the LSB round the multiple is
    [2^254 + recovered_scalar Γ] (the true integer bit sum — the final [z]
    step is the only one that can wrap mod [p], so the [z_0] cell itself is
    only its reduction); with [recovered_scalar Γ = α + t_q] and
    [q = 2^254 + t_q] this is [α + q ≡ α (mod q)], which the
    [Pallas.mul q B = identity] hypothesis collapses to the target
    ([address_integrity_mul_correct]).

    Side conditions, surfaced as hypotheses rather than assumed:
    - [Pallas.reduced B / Pallas.on_curve B / B <> identity]: the base is a
      genuine affine curve point.  For the witnessed [g_d_old] these are
      discharged by the [QWitnessPointNonId] gate
      ([witness_non_identity_point_value] / [_on_curve],
      [circuit_proof/fixed_base/main.v]).
    - [Pallas.mul pallas_q B = identity]: the base lies in the (whole-curve)
      order-[q] group.  Every reduced on-curve Pallas point satisfies this
      ([PallasOrder.pallas_mul_q_on_curve], [EllipticCurve/PallasOrder.v]);
      the consumer derives it from the [QWitnessPointNonId] facts
      ([DiversifiedAddress.base_point_order]) and supplies it at the call
      site.
    - [mul_nondegenerate]: the incomplete-addition halves never meet a
      degenerate case (equal x-coordinates, or an identity accumulator).
      The gates force nothing in those cases, so this is genuine witness
      honesty — the variable-base analogue of [SinsemillaHash.nondegenerate],
      a conjunct of [OrchardValidActionInputs.commit_ivk_witness_ok].
    - Scalar canonicity is NOT needed as a hypothesis: cell values are field
      evaluations, hence already reduced mod [pallas_p], and the conclusion
      is exact ([Pallas.mul α B] for the reduced [α]), leaving any mod-[q]
      reasoning to the consumer.

    Proof status: everything is Qed.  The two incomplete-half lemmas
    ([hi_half_correct], [lo_half_correct]) delegate to
    [circuit_proof/ownership/var_base_incomplete.v], the complete-rounds
    lemma ([complete_bits_correct]) to
    [circuit_proof/ownership/var_base_complete.v], and the circuit side of
    the overflow argument ([overflow_scalar_exact]) to
    [circuit_proof/ownership/var_base_overflow.v] — each a self-contained
    obligation from [Holds Γ] with its interface cells pinned down here.
    The spec layer, the facts extractors, the initial doubling
    ([init_acc_correct]), the LSB round ([lsb_correct]), the pure overflow
    arithmetic ([overflow_no_wrap]) and the final composition
    ([address_integrity_mul_correct]) are proved in this file and
    [var_base_defs.v]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_incomplete.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_complete.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_overflow.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
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

Module VarBaseMul.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Shared surface

      The concrete regions and cells, the readers, the nondegeneracy side
      conditions, the Pallas spec-layer step laws, the whole-region facts
      extractor and the pure overflow arithmetic core
      ([overflow_no_wrap]) live in
      [circuit_proof/ownership/var_base_defs.v]; the abbreviations below
      keep every [VarBaseMul.*] path denoting those constants. *)

  Notation mul_region := VarBaseDefs.mul_region.
  Notation overflow_s_region := VarBaseDefs.overflow_s_region.
  Notation overflow_lookup_region := VarBaseDefs.overflow_lookup_region.
  Notation overflow_check_region := VarBaseDefs.overflow_check_region.
  Notation gd_old_region := VarBaseDefs.gd_old_region.
  Notation ivk_add_region := VarBaseDefs.ivk_add_region.
  Notation alpha_cell := VarBaseDefs.alpha_cell.
  Notation gd_x_cell := VarBaseDefs.gd_x_cell.
  Notation gd_y_cell := VarBaseDefs.gd_y_cell.
  Notation av := VarBaseDefs.av.
  Notation alpha_value := VarBaseDefs.alpha_value.
  Notation base_point := VarBaseDefs.base_point.
  Notation base_wpoint := VarBaseDefs.base_wpoint.
  Notation result_point := VarBaseDefs.result_point.
  Notation lsb_bit := VarBaseDefs.lsb_bit.
  Notation recovered_scalar := VarBaseDefs.recovered_scalar.
  Notation step_nondegenerate := VarBaseDefs.step_nondegenerate.
  Notation hi_step_nondegenerate := VarBaseDefs.hi_step_nondegenerate.
  Notation lo_step_nondegenerate := VarBaseDefs.lo_step_nondegenerate.
  Notation mul_nondegenerate := VarBaseDefs.mul_nondegenerate.
  Notation pallas_11_lt := VarBaseDefs.pallas_11_lt.
  Notation pallas_mul_one := VarBaseDefs.pallas_mul_one.
  Notation pallas_mul_add := VarBaseDefs.pallas_mul_add.
  Notation pallas_mul_neg := VarBaseDefs.pallas_mul_neg.
  Notation pallas_mul_2 := VarBaseDefs.pallas_mul_2.
  Notation pallas_3_lt := VarBaseDefs.pallas_3_lt.
  Notation w_neg_on_curve := VarBaseDefs.w_neg_on_curve.
  Notation w_mul_pos_on_curve := VarBaseDefs.w_mul_pos_on_curve.
  Notation w_mul_on_curve := VarBaseDefs.w_mul_on_curve.
  Notation pallas_mul_on_curve := VarBaseDefs.pallas_mul_on_curve.
  Notation pallas_mul_reduced := VarBaseDefs.pallas_mul_reduced.
  Notation pallas_neg_on_curve := VarBaseDefs.pallas_neg_on_curve.
  Notation pallas_neg_reduced := VarBaseDefs.pallas_neg_reduced.
  Notation signed_base := VarBaseDefs.signed_base.
  Notation signed_base_mul := VarBaseDefs.signed_base_mul.
  Notation double_add_step_multiple := VarBaseDefs.double_add_step_multiple.
  Notation step_scalar_shape := VarBaseDefs.step_scalar_shape.
  Notation variable_base_region_facts := VarBaseDefs.variable_base_region_facts.
  Notation overflow_no_wrap := VarBaseDefs.overflow_no_wrap.

  (** ** The initial doubling (rows 0–1): [acc = [2] B]

      Row 0 is a [QEccAdd] complete addition of the base with itself (all
      four input cells are [Copy]-pinned to the [GDOld] witness cells), so
      the output cells [(A2@1, A3@1)] hold [repr ([2] B)]. *)
  Lemma init_acc_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ)) :
    {| Point.x := av Γ Advice.A2 1; Point.y := av Γ Advice.A3 1 |} =
    PallasModel.repr (Pallas.mul 2 (base_wpoint Γ)).
  Proof.
    pose proof (variable_base_region_facts Γ Hcircuit) as Hfacts.
    (* The [QEccAdd] selector at offset 0. *)
    pose proof Hfacts as Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    cbn [region_facts interpret_facts interpret_fact] in Hsel.
    destruct Hsel as [Hsel _].
    (* The four base [Copy] facts at row 0. *)
    pose proof Hfacts as Hcopy0.
    apply interpret_region_facts_bind_right in Hcopy0.
    apply interpret_region_facts_bind_left in Hcopy0.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy0.
    destruct Hcopy0 as [Hcopy0 _].
    pose proof Hfacts as Hcopy1.
    do 2 apply interpret_region_facts_bind_right in Hcopy1.
    apply interpret_region_facts_bind_left in Hcopy1.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy1.
    destruct Hcopy1 as [Hcopy1 _].
    pose proof Hfacts as Hcopy2.
    do 3 apply interpret_region_facts_bind_right in Hcopy2.
    apply interpret_region_facts_bind_left in Hcopy2.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy2.
    destruct Hcopy2 as [Hcopy2 _].
    pose proof Hfacts as Hcopy3.
    do 4 apply interpret_region_facts_bind_right in Hcopy3.
    apply interpret_region_facts_bind_left in Hcopy3.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy3.
    destruct Hcopy3 as [Hcopy3 _].
    (* The complete-addition gate at row 0 determines [(A2@1, A3@1)]. *)
    pose proof
      (CompleteAddition.deterministic Γ mul_region 0
        (enabled_nonzero Γ Selector.QEccAdd mul_region 0 Hsel)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate
          mul_region 0
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          (holds_gates Γ Hcircuit))) as Hdet.
    (* Align the readers with the gate lemma's rotated cells. *)
    unfold av, read_advice.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hdet |- *.
    cbn in Hcopy0, Hcopy1, Hcopy2, Hcopy3.
    change (rotated_row 0 Rotation.next) with 1 in Hdet.
    change (rotated_row 0 Rotation.cur) with 0 in Hdet.
    change (rotated_row 1 Rotation.cur) with 1.
    rewrite Hdet.
    rewrite Hcopy0, Hcopy1, Hcopy2, Hcopy3.
    (* [output bx by bx by = point_add (base) (base) = repr ([2] B)]. *)
    change (CompleteAddition.output
        (UnOp.from (Γ.(Assignment.advice) Advice.A0 gd_old_region 0))
        (UnOp.from (Γ.(Assignment.advice) Advice.A1 gd_old_region 0))
        (UnOp.from (Γ.(Assignment.advice) Advice.A0 gd_old_region 0))
        (UnOp.from (Γ.(Assignment.advice) Advice.A1 gd_old_region 0)))
      with (EccSpec.point_add (base_point Γ) (base_point Γ)).
    rewrite <- (PallasModel.repr_unrepr (base_point Γ)).
    change (PallasModel.unrepr (base_point Γ)) with (base_wpoint Γ).
    rewrite <- (PallasModel.repr_add _ _ HBred HBred HBoc HBoc).
    rewrite (pallas_mul_2 _ HBred HBoc).
    reflexivity.
  Qed.

  (** ** Phase cuts: the ladder segments and the overflow

      Each lemma below is a self-contained obligation from [Holds Γ],
      proved in its own leaf file ([var_base_incomplete.v],
      [var_base_complete.v], [var_base_overflow.v]) and delegated to here:
      the proof extracts the segment's selector/copy facts from the region
      program (and, for [overflow_scalar_exact], the overflow block's facts
      and the running-sum lookup), applies the per-row gate lemmas and
      threads the [repr ([2^m + 2 z + 1] B)] invariant with
      [double_add_step_multiple] / [step_scalar_shape].  The interface cells
      and multiples are fixed by the region layout
      ([synthesize_variable_base_scalar_mul_region]); [lsb_correct] below is
      proved end-to-end on that layout in this file, validating the fact
      indices and the gate/reader alignment the delegated segments share. *)

  (** Hi incomplete half.  Inputs: the initial accumulator [(A2@1, A3@1)]
      (spliced into the half by the [A2@1 → A3@2] / [A3@1 → A4@1] copies and
      the [q_mul_1] "init y_a" gate) and [z] pinned to [0] at [A9@1]
      ([ConstrainConstant]).  Steps at rows 2..126 ([QMulIncompleteHi2] at
      2..125, [QMulIncompleteHi3] at 126) process 125 boolean bits into the
      running sum [z@r = 2·z@(r−1) + k_r], ending at
      [z_130 = A9@126 < 2^125], accumulator [(A3@127, A4@127)]
      (the [q_mul_3] final [x_a]/witnessed [y_a]).  The [A9@126 / 2^124]
      conjunct recovers the top bit [k_254 = A9@2] for the overflow
      argument. *)
  Lemma hi_half_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (Hnondeg : forall r, 2 <= r <= 126 -> hi_step_nondegenerate Γ r)
      (Hinit :
        {| Point.x := av Γ Advice.A2 1; Point.y := av Γ Advice.A3 1 |} =
        PallasModel.repr (Pallas.mul 2 (base_wpoint Γ))) :
    0 <= av Γ Advice.A9 126 < 2 ^ 125 /\
    av Γ Advice.A9 126 / 2 ^ 124 = av Γ Advice.A9 2 /\
    {| Point.x := av Γ Advice.A3 127; Point.y := av Γ Advice.A4 127 |} =
    PallasModel.repr
      (Pallas.mul (2 ^ 125 + 2 * av Γ Advice.A9 126 + 1) (base_wpoint Γ)).
  Proof.
    exact (VarBaseIncomplete.hi_half_correct
      Γ Hcircuit HBred HBoc HBne Hnondeg Hinit).
  Qed.

  (** Lo incomplete half.  The hi output is spliced in by the
      [A9@126 → A6@1] (z), [A3@127 → A7@2] (x_a) and [A4@127 → A8@1] (y_a)
      copies; steps at rows 2..127 ([QMulIncompleteLo2] at 2..126,
      [QMulIncompleteLo3] at 127) process 126 more bits, ending at
      [z_4 = A6@127], accumulator [(A7@128, A8@128)].  The multiple keeps the
      [2^m + 2z + 1] shape because the incoming [2^125 + 2·z_130 + 1]
      composes with the 126 absorbed bits exactly as
      [z_4 = 2^126·z_130 + (low bits)] — whence also the
      [A6@127 / 2^126 = A9@126] division link. *)
  Lemma lo_half_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (Hnondeg : forall r, 2 <= r <= 127 -> lo_step_nondegenerate Γ r)
      (Hz_hi : 0 <= av Γ Advice.A9 126 < 2 ^ 125)
      (Hinit :
        {| Point.x := av Γ Advice.A3 127; Point.y := av Γ Advice.A4 127 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 125 + 2 * av Γ Advice.A9 126 + 1) (base_wpoint Γ))) :
    0 <= av Γ Advice.A6 127 < 2 ^ 251 /\
    av Γ Advice.A6 127 / 2 ^ 126 = av Γ Advice.A9 126 /\
    {| Point.x := av Γ Advice.A7 128; Point.y := av Γ Advice.A8 128 |} =
    PallasModel.repr
      (Pallas.mul (2 ^ 251 + 2 * av Γ Advice.A6 127 + 1) (base_wpoint Γ)).
  Proof.
    exact (VarBaseIncomplete.lo_half_correct
      Γ Hcircuit HBred HBoc HBne Hnondeg Hz_hi Hinit).
  Qed.

  (** The three complete rounds (bits [k_3, k_2, k_1], rows 128–135).  The lo
      output is copied to [(A2@129, A3@129)] (and re-fed as [(A0, A1)] on the
      even rows); [z] continues at [A9@129 = A6@127] (copy) through
      [A9@131, A9@133, A9@135] ([QMulDecomposeVar] at 130/132/134, with the
      sign-corrected [±y_p] witnessed on [A9@130/132/134] and checked by the
      [y_switch] ternary); each round is two [QEccAdd] complete additions.
      Ends at [z_1 = A9@135], accumulator [(A2@135, A3@135)]. *)
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
    exact (VarBaseComplete.complete_bits_correct
      Γ Hcircuit HBred HBoc HBne Hz_lo Hinit).
  Qed.

  (** The LSB round (rows 135–136).  [QMulLsb@135] forces the witnessed point
      [(A0@135, A1@135)] to the identity sentinel [(0, 0)] when
      [k_0 = z_0 − 2·z_1 = 1] and to [−B] ([base_x], [−base_y], with the base
      re-copied at [(A0@136, A1@136)]) when [k_0 = 0]; the [QEccAdd@135]
      complete addition then lands the multiple on
      [2^254 + recovered_scalar Γ] in both branches ([2^254 + 2·z_1 + 1] and
      [2^254 + 2·z_1 + 1 − 1]).  The [z_0] cell itself is only the mod-[p]
      reduction of the recovered scalar (the one [z] step that can wrap). *)
  Lemma lsb_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (Hz_1 : 0 <= av Γ Advice.A9 135 < 2 ^ 254)
      (Hacc :
        {| Point.x := av Γ Advice.A2 135; Point.y := av Γ Advice.A3 135 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 254 + 2 * av Γ Advice.A9 135 + 1) (base_wpoint Γ))) :
    (lsb_bit Γ = 0 \/ lsb_bit Γ = 1) /\
    av Γ Advice.A9 136 = recovered_scalar Γ mod Primes.pallas_p /\
    result_point Γ =
    PallasModel.repr
      (Pallas.mul (2 ^ 254 + recovered_scalar Γ) (base_wpoint Γ)).
  Proof.
    (* Facts: the [QMulLsb]/[QEccAdd] selectors at row 135 and the base
       copies at row 136 (facts 59–62 of the region program). *)
    pose proof (variable_base_region_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hlsb_sel.
    do 59 apply interpret_region_facts_bind_right in Hlsb_sel.
    apply interpret_region_facts_bind_left in Hlsb_sel.
    cbn [region_facts interpret_facts interpret_fact] in Hlsb_sel.
    destruct Hlsb_sel as [Hlsb_sel _].
    pose proof Hfacts as Hcopy_bx.
    do 60 apply interpret_region_facts_bind_right in Hcopy_bx.
    apply interpret_region_facts_bind_left in Hcopy_bx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_bx.
    destruct Hcopy_bx as [Hcopy_bx _].
    pose proof Hfacts as Hcopy_by.
    do 61 apply interpret_region_facts_bind_right in Hcopy_by.
    apply interpret_region_facts_bind_left in Hcopy_by.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_by.
    destruct Hcopy_by as [Hcopy_by _].
    pose proof Hfacts as Hadd_sel.
    do 62 apply interpret_region_facts_bind_right in Hadd_sel.
    apply interpret_region_facts_bind_left in Hadd_sel.
    cbn [region_facts interpret_facts interpret_fact] in Hadd_sel.
    destruct Hadd_sel as [Hadd_sel _].
    (* The two gates at row 135. *)
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.lsb_check_gate
        mul_region 135
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (holds_gates Γ Hcircuit)) as Hlsb_gate.
    pose proof
      (CompleteAddition.deterministic Γ mul_region 135
        (enabled_nonzero Γ Selector.QEccAdd mul_region 135 Hadd_sel)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate
          mul_region 135
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          (holds_gates Γ Hcircuit))) as Hdet.
    cbn [eval_gate Garden.Halo2.halo2_gadgets.ecc.chip.mul.lsb_check_gate
      Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur Rotation.next] in Hlsb_gate.
    cbn in Hlsb_gate.
    destruct Hlsb_gate as (Hbool & Hx & Hy).
    specialize (Hbool (enabled_nonzero Γ Selector.QMulLsb mul_region 135 Hlsb_sel)).
    specialize (Hx (enabled_nonzero Γ Selector.QMulLsb mul_region 135 Hlsb_sel)).
    specialize (Hy (enabled_nonzero Γ Selector.QMulLsb mul_region 135 Hlsb_sel)).
    (* The witnessed bit is [lsb_bit]. *)
    set (z0r := Γ.(Assignment.advice) Advice.A9 mul_region 136) in *.
    set (z1r := Γ.(Assignment.advice) Advice.A9 mul_region 135) in *.
    set (L := UnOp.from z0r -F UnOp.from z1r *F 2) in Hbool, Hx, Hy.
    assert (HLbit : L = lsb_bit Γ).
    { unfold lsb_bit, av, read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 136 Rotation.cur) with 136.
      change (rotated_row 135 Rotation.cur) with 135.
      unfold L, BinOp.sub, BinOp.mul, UnOp.from.
      fold z0r z1r.
      change Garden.Plonky3.M.Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      rewrite Zminus_mod_idemp_r.
      f_equal.
      ring. }
    assert (Hbit : lsb_bit Γ = 0 \/ lsb_bit Γ = 1).
    { rewrite <- HLbit. rewrite Hbool.
      destruct (Z.odd L); [right | left]; reflexivity. }
    assert (Hcell : av Γ Advice.A9 136 = recovered_scalar Γ mod Primes.pallas_p).
    { unfold recovered_scalar, lsb_bit, av, read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 136 Rotation.cur) with 136.
      change (rotated_row 135 Rotation.cur) with 135.
      fold z0r z1r.
      unfold UnOp.from.
      change Garden.Plonky3.M.Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      rewrite Zplus_mod_idemp_r.
      replace
        (2 *
         (z1r mod
          28948022309329048855892746252171976963363056481941560715954676764349967630337) +
         (z0r mod
          28948022309329048855892746252171976963363056481941560715954676764349967630337 -
          2 *
          (z1r mod
           28948022309329048855892746252171976963363056481941560715954676764349967630337)))
        with
        (z0r mod
         28948022309329048855892746252171976963363056481941560715954676764349967630337)
        by ring.
      rewrite Z.mod_mod by lia.
      reflexivity. }
    refine (conj Hbit (conj Hcell _)).
    (* Align the readers with the gate cells. *)
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hdet.
    change (rotated_row 135 Rotation.next) with 136 in Hdet.
    change (rotated_row 135 Rotation.cur) with 135 in Hdet.
    unfold result_point, av, read_advice in Hacc |- *.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hacc |- *.
    change (rotated_row 136 Rotation.cur) with 136 in Hacc |- *.
    change (rotated_row 135 Rotation.cur) with 135 in Hacc |- *.
    rewrite Hdet.
    cbn in Hcopy_bx, Hcopy_by.
    (* The two forced ternary evaluations. *)
    assert (Hsimpl1 : forall t f : Z, 1 *F t +F (1 -F 1) *F f = UnOp.from t).
    { intros t f.
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
      reflexivity. }
    assert (Hsimpl0 : forall t f : Z, 0 *F t +F (1 -F 0) *F f = UnOp.from f).
    { intros t f.
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
      reflexivity. }
    unfold recovered_scalar.
    rewrite <- HLbit.
    unfold av, read_advice.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
    change (rotated_row 135 Rotation.cur) with 135.
    destruct Hbit as [Hb | Hb].
    (* Bit 1: the gate pins the witnessed point to the identity sentinel and
       the complete addition is the identity on the accumulator. *)
    2:{ assert (HL1 : L = 1) by (rewrite HLbit; exact Hb).
        rewrite HL1 in Hx, Hy |- *.
        rewrite Hsimpl1 in Hx, Hy.
        rewrite Garden.Plonky3.M.FieldRewrite.from_from in Hx, Hy.
        rewrite Hx, Hy.
        cbn [CompleteAddition.output Z.eqb].
        rewrite Hacc.
        f_equal.
        f_equal.
        lia. }
    (* Bit 0: the gate pins the witnessed point to [−B] and the complete
       addition subtracts one multiple of the base. *)
    assert (HL0 : L = 0) by (rewrite HLbit; exact Hb).
    rewrite HL0 in Hx, Hy |- *.
    rewrite Hsimpl0 in Hx, Hy.
    change (BinOp.sub (UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region 135))
                      (UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region 136)))
      with (UnOp.from (UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region 135)
                       - UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region 136))) in Hx.
    change (BinOp.add (UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region 135))
                      (UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region 136)))
      with (UnOp.from (UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region 135)
                       + UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region 136))) in Hy.
    rewrite Garden.Plonky3.M.FieldRewrite.from_from in Hx, Hy.
    rewrite Hcopy_bx in Hx.
    rewrite Hcopy_by in Hy.
    set (xp := UnOp.from (Γ.(Assignment.advice) Advice.A0 mul_region 135)) in *.
    set (yp := UnOp.from (Γ.(Assignment.advice) Advice.A1 mul_region 135)) in *.
    set (xq := UnOp.from (Γ.(Assignment.advice) Advice.A2 mul_region 135)) in *.
    set (yq := UnOp.from (Γ.(Assignment.advice) Advice.A3 mul_region 135)) in *.
    set (bx := UnOp.from (Γ.(Assignment.advice) Advice.A0 gd_old_region 0)) in *.
    set (byv := UnOp.from (Γ.(Assignment.advice) Advice.A1 gd_old_region 0)) in *.
    assert (Hbound : forall w : Z, 0 <= UnOp.from w < Primes.pallas_p).
    { intro w. unfold UnOp.from. apply Z.mod_pos_bound.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      lia. }
    pose proof (Hbound (Γ.(Assignment.advice) Advice.A0 mul_region 135)) as Hxp_b;
      fold xp in Hxp_b.
    pose proof (Hbound (Γ.(Assignment.advice) Advice.A1 mul_region 135)) as Hyp_b;
      fold yp in Hyp_b.
    pose proof (Hbound (Γ.(Assignment.advice) Advice.A0 gd_old_region 0)) as Hbx_b;
      fold bx in Hbx_b.
    pose proof (Hbound (Γ.(Assignment.advice) Advice.A1 gd_old_region 0)) as Hby_b;
      fold byv in Hby_b.
    unfold UnOp.from in Hx, Hy.
    change Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337
      in Hx, Hy, Hxp_b, Hyp_b, Hbx_b, Hby_b.
    change Garden.Plonky3.M.Primes.pallas_p with
      28948022309329048855892746252171976963363056481941560715954676764349967630337
      in Hx, Hy.
    assert (Hxpb : xp = bx).
    { apply Z.mod_divide in Hx; [| lia].
      destruct Hx as [k Hk].
      clear - Hk Hxp_b Hbx_b. nia. }
    assert (Hyp : yp + byv = 0 \/
      yp + byv =
      28948022309329048855892746252171976963363056481941560715954676764349967630337).
    { apply Z.mod_divide in Hy; [| lia].
      destruct Hy as [k Hk].
      clear - Hk Hyp_b Hby_b. nia. }
    (* The witnessed base is a genuine affine point. *)
    assert (Hbp : base_point Γ = {| Point.x := bx; Point.y := byv |}).
    { unfold base_point, read_point, read, read1, read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold base_wpoint. rewrite Hbp. unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((bx =? 0) && (byv =? 0))%bool eqn:Hid.
      - exfalso. apply HBne. unfold base_wpoint. rewrite Hbp.
        unfold PallasModel.unrepr. cbn [Point.x Point.y]. rewrite Hid.
        reflexivity.
      - reflexivity. }
    (* The witnessed point is the representation of [−B]. *)
    assert (Hnegpt :
      {| Point.x := xp; Point.y := yp |} =
      PallasModel.repr (Pallas.neg (base_wpoint Γ))).
    { rewrite HB.
      cbn [Pallas.neg Weierstrass.neg PallasModel.repr].
      f_equal.
      - exact Hxpb.
      - unfold UnOp.opp.
        change Garden.Plonky3.M.Primes.pallas_p with
          28948022309329048855892746252171976963363056481941560715954676764349967630337.
        destruct Hyp as [Hyp0 | Hypp].
        + assert (Hy0 : yp = 0) by lia.
          assert (Hb0 : byv = 0) by lia.
          rewrite Hy0, Hb0. reflexivity.
        + assert (Hbnz : byv <> 0) by lia.
          rewrite Z.mod_opp_l_nz.
          * rewrite (Z.mod_small byv) by lia. lia.
          * lia.
          * rewrite (Z.mod_small byv) by lia. exact Hbnz. }
    change (CompleteAddition.output xp yp xq yq)
      with (EccSpec.point_add {| Point.x := xp; Point.y := yp |}
                              {| Point.x := xq; Point.y := yq |}).
    rewrite Hnegpt, Hacc.
    assert (Hneg_red : Pallas.reduced (Pallas.neg (base_wpoint Γ)))
      by (apply pallas_neg_reduced; exact HBred).
    assert (Hneg_oc : Pallas.on_curve (Pallas.neg (base_wpoint Γ)))
      by (apply pallas_neg_on_curve; exact HBoc).
    assert (Hmul_red : Pallas.reduced
        (Pallas.mul
          (2 ^ 254 + 2 * UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region 135) + 1)
          (base_wpoint Γ)))
      by (apply pallas_mul_reduced; exact HBred).
    assert (Hmul_oc : Pallas.on_curve
        (Pallas.mul
          (2 ^ 254 + 2 * UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region 135) + 1)
          (base_wpoint Γ)))
      by (apply pallas_mul_on_curve; exact HBoc).
    rewrite <- (PallasModel.repr_add _ _ Hneg_red Hmul_red Hneg_oc Hmul_oc).
    replace (Pallas.neg (base_wpoint Γ)) with (Pallas.mul (- (1)) (base_wpoint Γ))
      by (rewrite (pallas_mul_neg 1 _ HBred), pallas_mul_one; reflexivity).
    rewrite <- (pallas_mul_add (- (1)) _ _ HBred HBoc).
    f_equal.
    f_equal.
    lia.
  Qed.

  (** Circuit side of the overflow argument: the [OverflowCheck] gate at the
      copied cells ([z_136 = A9@136], [z_126 = A9@126], [z_2 = A9@2],
      [α = alpha_cell], [z_13] from the 13-row running-sum lookup, [s] the
      [OverflowS] witness) plus the lookup's 130-bit decomposition of [s]
      discharge the hypotheses of [overflow_no_wrap] at
      [z0 := recovered_scalar Γ]: the [Hcell] congruence turns the gate's
      [recovery] constraint on the [z_0] cell into the mod-[p] congruence on
      the true scalar, and the division links identify the gate's
      [k_254]/[z_130] cells with [recovered_scalar Γ / 2^254] and
      [/ 2^130]. *)
  Lemma overflow_scalar_exact
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hz_1 : 0 <= av Γ Advice.A9 135 < 2 ^ 254)
      (Hbit : lsb_bit Γ = 0 \/ lsb_bit Γ = 1)
      (Hcell : av Γ Advice.A9 136 = recovered_scalar Γ mod Primes.pallas_p)
      (Hz130 : recovered_scalar Γ / 2 ^ 130 = av Γ Advice.A9 126)
      (Hk254 : recovered_scalar Γ / 2 ^ 254 = av Γ Advice.A9 2) :
    recovered_scalar Γ = alpha_value Γ + Primes.t_q.
  Proof.
    exact (VarBaseOverflow.overflow_scalar_exact
      Γ Hcircuit Hz_1 Hbit Hcell Hz130 Hk254).
  Qed.

  (** ** The composition target

      From [Holds Γ] and the surfaced side conditions: the mul chip's output
      point is [repr ([α] B)] for the (reduced) scalar cell value [α] and the
      witnessed base [B]. *)
  Theorem address_integrity_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (base_wpoint Γ))
      (HBoc : Pallas.on_curve (base_wpoint Γ))
      (HBne : base_wpoint Γ <> Pallas.identity)
      (HBorder : Pallas.mul Pallas.pallas_q (base_wpoint Γ) = Pallas.identity)
      (Hnondeg : mul_nondegenerate Γ) :
    result_point Γ =
    PallasModel.repr (Pallas.mul (alpha_value Γ) (base_wpoint Γ)).
  Proof.
    destruct Hnondeg as [Hhi_nd Hlo_nd].
    pose proof (init_acc_correct Γ Hcircuit HBred HBoc) as Hinit.
    pose proof (hi_half_correct Γ Hcircuit HBred HBoc HBne Hhi_nd Hinit)
      as (Hzh_range & Hk254_link & Hhi_acc).
    pose proof
      (lo_half_correct Γ Hcircuit HBred HBoc HBne Hlo_nd Hzh_range Hhi_acc)
      as (Hzl_range & Hzl_link & Hlo_acc).
    pose proof
      (complete_bits_correct Γ Hcircuit HBred HBoc HBne Hzl_range Hlo_acc)
      as (Hz1_range & Hz1_link & Hc_acc).
    pose proof (lsb_correct Γ Hcircuit HBred HBoc HBne Hz1_range Hc_acc)
      as (Hbit & Hcell & Hres).
    (* The division links compose into the [z_130]/[k_254] recoveries the
       overflow lemma consumes. *)
    assert (H2pos : (0 : Z) < 2) by lia.
    assert (H3pos : 0 < 2 ^ 3) by (apply Z.pow_pos_nonneg; lia).
    assert (H126pos : 0 < 2 ^ 126) by (apply Z.pow_pos_nonneg; lia).
    assert (H124pos : 0 < 2 ^ 124) by (apply Z.pow_pos_nonneg; lia).
    assert (H130pos : 0 < 2 ^ 130) by (apply Z.pow_pos_nonneg; lia).
    assert (Hdiv2 : recovered_scalar Γ / 2 = av Γ Advice.A9 135).
    { unfold recovered_scalar.
      destruct Hbit as [Hb | Hb]; rewrite Hb.
      - rewrite Z.add_0_r, Z.mul_comm, Z.div_mul by lia. reflexivity.
      - rewrite Z.mul_comm, Z.div_add_l by lia.
        rewrite (Z.div_small 1 2) by lia.
        apply Z.add_0_r. }
    assert (Hz130 : recovered_scalar Γ / 2 ^ 130 = av Γ Advice.A9 126).
    { rewrite <- Hzl_link, <- Hz1_link, <- Hdiv2.
      rewrite Z.div_div by lia.
      rewrite Z.div_div by lia.
      f_equal; vm_compute; reflexivity. }
    assert (Hk254 : recovered_scalar Γ / 2 ^ 254 = av Γ Advice.A9 2).
    { rewrite <- Hk254_link, <- Hz130.
      rewrite Z.div_div by lia.
      f_equal; vm_compute; reflexivity. }
    pose proof
      (overflow_scalar_exact Γ Hcircuit Hz1_range Hbit Hcell Hz130 Hk254)
      as Halpha.
    rewrite Hres, Halpha.
    (* [2^254 + (α + t_q) = α + q], and the order hypothesis kills the [q]. *)
    replace (2 ^ 254 + (alpha_value Γ + Primes.t_q))
      with (alpha_value Γ + Pallas.pallas_q)
      by (unfold Pallas.pallas_q, Primes.pallas_q; lia).
    rewrite (pallas_mul_add (alpha_value Γ) Pallas.pallas_q _ HBred HBoc).
    rewrite HBorder.
    unfold Pallas.add, Pallas.identity.
    rewrite (Weierstrass.add_Infinity_r (p := Primes.pallas_p)
      Pallas.a Pallas.b).
    reflexivity.
  Qed.
End VarBaseMul.
