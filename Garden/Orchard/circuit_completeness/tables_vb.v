(** * Hoisted variable-base-ladder tables for the honest-witness generator

    The cell values of the address-integrity variable-base multiplication
    block ([[ivk] g_d_old], §4.18.4 'Diversified address integrity'): the
    137-row double-and-add region and its three overflow-check regions.  The
    per-row values are the forward image of the soundness bridge
    ([circuit_proof/ownership/var_base_{defs,incomplete,complete,mul,
    overflow}.v] over the gates of [ecc/chip/mul.v] and [ecc/chip/mul/
    {incomplete,complete,overflow}.v]):

    - row 0 hosts a complete addition doubling the base ([QEccAdd]), its
      output [[2] B] on [A2]/[A3] of row 1;
    - rows 2..126 host the hi-half incomplete double-and-add steps (bits
      254..130 of the scalar [ivk + t_q]) on columns
      [z = A9, x_a = A3, λ₁ = A4, λ₂ = A5], and rows 2..127 the lo-half
      steps (bits 129..4) on [z = A6, x_a = A7, λ₁ = A8, λ₂ = A2], both
      halves reading the base on [A0]/[A1]; the boundary cells [A4@1]/[A8@1]
      carry the witnessed initial [y_a] and [A3@127]/[A4@127] ([A7@128]/
      [A8@128]) the final hi (lo) accumulator;
    - rows 129..134 host the three complete rounds (bits 3..1), one bit per
      [QEccAdd] pair with the [QMulDecomposeVar] running sums and the
      base-[y] pins on [A9];
    - row 135 hosts the LSB round ([QMulLsb] plus a final [QEccAdd] of the
      [(0, 0)]-or-[−B] point), its output — the multiple [[ivk] g_d_old] —
      on [A2]/[A3] of row 136;
    - the overflow block ([s = α + k_254·2^130], the 13-word running-sum
      decomposition of [s], and the [QMulOverflow] gate row) carries the
      reduced [s] and the running-sum probes [z_0]/[z_130]/[k_254] copied
      from the ladder's [A9] cells, with the [η] inverse witness.

    Each incomplete step from accumulator [acc] and bit [k] computes
    [mid = acc ⊞ (2k−1)B] and [acc' = acc ⊞ mid] with the exact
    [IncompleteAddition.output] chord formulas, so every table entry equals
    the corresponding [OrchardWitnessInput] value ([mul_acc] /
    [mul_step_point] / [bit_running_sum]) on the nondegenerate domain.  The
    whole ladder is built by one linear fold ([ladder_go]) — two field
    inversions per bit, paid once per [vm_compute] run — never a per-cell
    [Pallas.mul] (the per-read recomputation pitfall of
    [docs/compile-performance.md]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Orchard.circuit_completeness.advice_ecc_muls.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardVarBaseTables.
  Import OrchardWitnessInput.

  Local Notation A0 := Advice.A0.
  Local Notation A1 := Advice.A1.
  Local Notation A2 := Advice.A2.
  Local Notation A3 := Advice.A3.
  Local Notation A4 := Advice.A4.
  Local Notation A5 := Advice.A5.
  Local Notation A6 := Advice.A6.
  Local Notation A7 := Advice.A7.
  Local Notation A8 := Advice.A8.
  Local Notation A9 := Advice.A9.

  (** ** One incomplete double-and-add step

      Per step row the region stores the accumulator's [x] and the two chord
      gradients; the accumulator's [y] threads through the fold (the gates
      recover it as [((λ₁ + λ₂)(x_a − x_r)) / 2]). *)
  Record step_row : Set := {
    sr_xa : Z;
    sr_l1 : Z;
    sr_l2 : Z;
  }.

  Definition sr0 : step_row := {| sr_xa := 0; sr_l1 := 0; sr_l2 := 0 |}.

  (** The signed base point of a bit [k]: [[2k−1] B]. *)
  Definition signed_pt (B : Point.t) (bit : Z) : Point.t :=
    if bit =? 1 then B else point_neg B.

  (** The LSB round's point: the [(0, 0)] identity sentinel on bit [1],
      [−B] on bit [0] ([lsb_check_gate]). *)
  Definition lsb_pt (B : Point.t) (bit : Z) : Point.t :=
    if bit =? 1 then {| Point.x := 0; Point.y := 0 |} else point_neg B.

  (** From accumulator [acc] and bit [k]: [mid = acc ⊞ (2k−1)B] and
      [acc' = acc ⊞ mid], with the [IncompleteAddition.output] chord
      formulas spelled out so the two gradients are also returned.  On the
      nondegenerate domain [acc' = [2c + 2k − 1] B] for [acc = [c] B]
      ([VarBaseDefs.double_add_step_multiple]). *)
  Definition ladder_step (B : Point.t) (bit : Z) (acc : Point.t)
      : step_row * Point.t :=
    let xa := Point.x acc in
    let ya := Point.y acc in
    let xp := Point.x B in
    let yp := if bit =? 1 then Point.y B else 0 -F Point.y B in
    let l1 := BinOp.div (ya -F yp) (xa -F xp) in
    let xr := l1 *F l1 -F xa -F xp in
    let yr := l1 *F (xa -F xr) -F ya in
    let l2 := BinOp.div (ya -F yr) (xa -F xr) in
    let xa' := l2 *F l2 -F xa -F xr in
    let ya' := l2 *F (xa -F xa') -F ya in
    ({| sr_xa := xa; sr_l1 := l1; sr_l2 := l2 |},
     {| Point.x := xa'; Point.y := ya' |}).

  (** [count] steps absorbing bits [i], [i−1], …, low-index-last, from the
      given accumulator; returns the per-step rows and the final
      accumulator. *)
  Fixpoint ladder_go (B : Point.t) (k : Z) (acc : Point.t)
      (i count : nat) : list step_row * Point.t :=
    match count with
    | O => ([], acc)
    | S count' =>
        let '(row, acc') := ladder_step B (scalar_bit k i) acc in
        let '(rows, out) := ladder_go B k acc' (Nat.pred i) count' in
        (row :: rows, out)
    end.

  (** ** The hoisted ladder record

      Everything the region readers consume, computed once per assignment:
      the two incomplete halves, the boundary accumulators, the
      complete-round and LSB points, and the overflow-block scalars. *)
  Record t : Set := {
    (* The 255-bit running-sum value [z_0 = α + t_q]. *)
    vb_scalar : Z;
    (* Hi-half step rows (region rows 2..126, bits 254..130). *)
    vb_hi : list step_row;
    (* Lo-half step rows (region rows 2..127, bits 129..4). *)
    vb_lo : list step_row;
    (* The initial doubling [[2] B] and the two half boundaries. *)
    vb_d : Point.t;
    vb_acc130 : Point.t;
    vb_acc4 : Point.t;
    (* Complete rounds: per bit the signed base, the first sum and the
       round output. *)
    vb_p3 : Point.t; vb_mid3 : Point.t; vb_acc3 : Point.t;
    vb_p2 : Point.t; vb_mid2 : Point.t; vb_acc2 : Point.t;
    vb_p1 : Point.t; vb_mid1 : Point.t; vb_acc1 : Point.t;
    (* The LSB round's point and the ladder output [[ivk] g_d_old]. *)
    vb_p0 : Point.t;
    vb_out : Point.t;
    (* Overflow block: the top bit, the reduced [s = α + k_254·2^130] and
       the [η] inverse witness for the canonicity constraint. *)
    vb_k254 : Z;
    vb_s : Z;
    vb_eta : Z;
  }.

  Definition vb_columns (alpha : Z) (B : Point.t) : t :=
    let k := alpha + Primes.t_q in
    let d := EccSpec.point_add B B in
    let '(hi, acc130) := ladder_go B k d 254%nat 125%nat in
    let '(lo, acc4) := ladder_go B k acc130 129%nat 126%nat in
    let p3 := signed_pt B (scalar_bit k 3%nat) in
    let mid3 := EccSpec.point_add p3 acc4 in
    let acc3 := EccSpec.point_add acc4 mid3 in
    let p2 := signed_pt B (scalar_bit k 2%nat) in
    let mid2 := EccSpec.point_add p2 acc3 in
    let acc2 := EccSpec.point_add acc3 mid2 in
    let p1 := signed_pt B (scalar_bit k 1%nat) in
    let mid1 := EccSpec.point_add p1 acc2 in
    let acc1 := EccSpec.point_add acc2 mid1 in
    let p0 := lsb_pt B (scalar_bit k 0%nat) in
    let out := EccSpec.point_add p0 acc1 in
    let k254 := k / 2 ^ 254 in
    let z130 := k / 2 ^ 130 in
    {|
      vb_scalar := k;
      vb_hi := hi;
      vb_lo := lo;
      vb_d := d;
      vb_acc130 := acc130;
      vb_acc4 := acc4;
      vb_p3 := p3; vb_mid3 := mid3; vb_acc3 := acc3;
      vb_p2 := p2; vb_mid2 := mid2; vb_acc2 := acc2;
      vb_p1 := p1; vb_mid1 := mid1; vb_acc1 := acc1;
      vb_p0 := p0;
      vb_out := out;
      vb_k254 := k254;
      vb_s := (alpha + k254 * 2 ^ 130) mod Primes.pallas_p;
      vb_eta := if z130 =? 0 then 0 else mod_inverse z130 Primes.pallas_p;
    |}.

  (** The spec-anchored instantiation at an honest input. *)
  Definition vb_tables_of (w : HonestInput) : t :=
    vb_columns (ivk w) (hi_g_d_old w).

  (** ** The variable-base region reader *)

  Definition hi_at (tb : t) (offset : Z) : step_row :=
    List.nth (Z.to_nat (offset - 2)) (vb_hi tb) sr0.
  Definition lo_at (tb : t) (offset : Z) : step_row :=
    List.nth (Z.to_nat (offset - 2)) (vb_lo tb) sr0.

  (** The complete-addition operand pair [(p, q)] of a [QEccAdd] row: the
      doubling at row 0, and per complete round the [signed-base + acc]
      then [acc + mid] pairs; the LSB addition at row 135. *)
  Definition cadd_ops (B : Point.t) (tb : t) (offset : Z)
      : Point.t * Point.t :=
    if offset =? 129 then (vb_p3 tb, vb_acc4 tb)
    else if offset =? 130 then (vb_acc4 tb, vb_mid3 tb)
    else if offset =? 131 then (vb_p2 tb, vb_acc3 tb)
    else if offset =? 132 then (vb_acc3 tb, vb_mid2 tb)
    else if offset =? 133 then (vb_p1 tb, vb_acc2 tb)
    else if offset =? 134 then (vb_acc2 tb, vb_mid1 tb)
    else if offset =? 135 then (vb_p0 tb, vb_acc1 tb)
    else (B, B).

  (** The full 137-row region: hi/lo ladder columns, the complete-round
      block, and the [assign_complete_add] witness formulas
      ([OrchardAdviceEccMuls.lambda_w]/[alpha_w]/[beta_w]/[gamma_w]/
      [delta_w]) on the [QEccAdd] rows. *)
  Definition vb_region_advice (B : Point.t) (tb : t)
      (column : Advice.t) (offset : Z) : Z :=
    let k := vb_scalar tb in
    match column with
    | A0 =>
        if (offset =? 0) || ((2 <=? offset) && (offset <=? 127))
           || (offset =? 129) || (offset =? 131) || (offset =? 133)
           || (offset =? 136)
        then Point.x B
        else if offset =? 130 then Point.x (vb_acc4 tb)
        else if offset =? 132 then Point.x (vb_acc3 tb)
        else if offset =? 134 then Point.x (vb_acc2 tb)
        else if offset =? 135 then Point.x (vb_p0 tb)
        else 0
    | A1 =>
        if (offset =? 0) || ((2 <=? offset) && (offset <=? 127))
           || (offset =? 136)
        then Point.y B
        else if offset =? 129 then Point.y (vb_p3 tb)
        else if offset =? 131 then Point.y (vb_p2 tb)
        else if offset =? 133 then Point.y (vb_p1 tb)
        else if offset =? 130 then Point.y (vb_acc4 tb)
        else if offset =? 132 then Point.y (vb_acc3 tb)
        else if offset =? 134 then Point.y (vb_acc2 tb)
        else if offset =? 135 then Point.y (vb_p0 tb)
        else 0
    | A2 =>
        if offset =? 0 then Point.x B
        else if offset =? 1 then Point.x (vb_d tb)
        else if (2 <=? offset) && (offset <=? 127) then sr_l2 (lo_at tb offset)
        else if offset =? 129 then Point.x (vb_acc4 tb)
        else if offset =? 130 then Point.x (vb_mid3 tb)
        else if offset =? 131 then Point.x (vb_acc3 tb)
        else if offset =? 132 then Point.x (vb_mid2 tb)
        else if offset =? 133 then Point.x (vb_acc2 tb)
        else if offset =? 134 then Point.x (vb_mid1 tb)
        else if offset =? 135 then Point.x (vb_acc1 tb)
        else if offset =? 136 then Point.x (vb_out tb)
        else 0
    | A3 =>
        if offset =? 0 then Point.y B
        else if offset =? 1 then Point.y (vb_d tb)
        else if (2 <=? offset) && (offset <=? 126) then sr_xa (hi_at tb offset)
        else if offset =? 127 then Point.x (vb_acc130 tb)
        else if offset =? 129 then Point.y (vb_acc4 tb)
        else if offset =? 130 then Point.y (vb_mid3 tb)
        else if offset =? 131 then Point.y (vb_acc3 tb)
        else if offset =? 132 then Point.y (vb_mid2 tb)
        else if offset =? 133 then Point.y (vb_acc2 tb)
        else if offset =? 134 then Point.y (vb_mid1 tb)
        else if offset =? 135 then Point.y (vb_acc1 tb)
        else if offset =? 136 then Point.y (vb_out tb)
        else 0
    | A4 =>
        if offset =? 1 then Point.y (vb_d tb)
        else if (2 <=? offset) && (offset <=? 126) then sr_l1 (hi_at tb offset)
        else if offset =? 127 then Point.y (vb_acc130 tb)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := cadd_ops B tb offset in
          OrchardAdviceEccMuls.lambda_w
            (Point.x pp) (Point.y pp) (Point.x qq) (Point.y qq)
        else 0
    | A5 =>
        if (2 <=? offset) && (offset <=? 126) then sr_l2 (hi_at tb offset)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := cadd_ops B tb offset in
          OrchardAdviceEccMuls.alpha_w (Point.x pp) (Point.x qq)
        else 0
    | A6 =>
        if (1 <=? offset) && (offset <=? 127) then k / 2 ^ (131 - offset)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, _) := cadd_ops B tb offset in
          OrchardAdviceEccMuls.beta_w (Point.x pp)
        else 0
    | A7 =>
        if (2 <=? offset) && (offset <=? 127) then sr_xa (lo_at tb offset)
        else if offset =? 128 then Point.x (vb_acc4 tb)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(_, qq) := cadd_ops B tb offset in
          OrchardAdviceEccMuls.gamma_w (Point.x qq)
        else 0
    | A8 =>
        if offset =? 1 then Point.y (vb_acc130 tb)
        else if (2 <=? offset) && (offset <=? 127) then sr_l1 (lo_at tb offset)
        else if offset =? 128 then Point.y (vb_acc4 tb)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := cadd_ops B tb offset in
          OrchardAdviceEccMuls.delta_w
            (Point.x pp) (Point.y pp) (Point.x qq) (Point.y qq)
        else 0
    | A9 =>
        if (1 <=? offset) && (offset <=? 126) then k / 2 ^ (256 - offset)
        else if offset =? 129 then k / 2 ^ 4
        else if offset =? 131 then k / 2 ^ 3
        else if offset =? 133 then k / 2 ^ 2
        else if offset =? 135 then k / 2 ^ 1
        else if offset =? 136 then k
        else if (offset =? 130) || (offset =? 132) || (offset =? 134)
        then Point.y B
        else 0
    end.

  (** ** The overflow-block readers

      [s = α + k_254·2^130] reduced to its field representative (the
      running-sum lookup decomposes the reduced value, so on [k_254 = 1] —
      where [α + 2^130 ≥ p] — the tail [z_13 = s / 2^130] is [0], as the
      [s_minus_lo_130_check] constraint requires). *)

  Definition overflow_s_advice_of (tb : t)
      (column : Advice.t) (offset : Z) : Z :=
    if offset =? 0 then
      match column with A6 => vb_s tb | _ => 0 end
    else 0.

  Definition overflow_lookup_advice_of (tb : t)
      (column : Advice.t) (offset : Z) : Z :=
    match column with
    | A9 =>
        if (0 <=? offset) && (offset <=? 13)
        then vb_s tb / 2 ^ (10 * offset)
        else 0
    | _ => 0
    end.

  (** The [QMulOverflow] gate row and its copies: [z_0]/[z_130]/[k_254]
      mirror the ladder's [A9] running sums at rows 136/126/2, [α] the
      [ivk] cell, [s]/[z_13] the decomposition region; [η] is the free
      inverse witness of the canonicity constraint. *)
  Definition overflow_check_advice_of (alpha : Z) (tb : t)
      (column : Advice.t) (offset : Z) : Z :=
    match column with
    | A6 =>
        if offset =? 0 then vb_scalar tb
        else if offset =? 1 then vb_scalar tb / 2 ^ 130
        else if offset =? 2 then vb_eta tb
        else 0
    | A7 =>
        if offset =? 0 then vb_scalar tb / 2 ^ 254
        else if offset =? 1 then alpha
        else if offset =? 2 then vb_s tb / 2 ^ 130
        else 0
    | A8 =>
        if offset =? 1 then vb_s tb else 0
    | _ => 0
    end.

  (** The whole [AddressIntegrity.Mul] block over the tables. *)
  Definition mul_advice_of (alpha : Z) (B : Point.t) (tb : t)
      (sub : RegionId.AddressIntegrity.Mul.t)
      (column : Advice.t) (offset : Z) : Z :=
    match sub with
    | RegionId.AddressIntegrity.Mul.VariableBase =>
        vb_region_advice B tb column offset
    | RegionId.AddressIntegrity.Mul.OverflowS =>
        overflow_s_advice_of tb column offset
    | RegionId.AddressIntegrity.Mul.OverflowLookup =>
        overflow_lookup_advice_of tb column offset
    | RegionId.AddressIntegrity.Mul.OverflowCheck =>
        overflow_check_advice_of alpha tb column offset
    end.

End OrchardVarBaseTables.
