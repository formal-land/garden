Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Advice sub-generator: the ECC scalar-multiplication regions

    The forward image of the soundness readers and region synthesis programs
    for the elliptic-curve multiplication block of [circuit.synthesize]: the
    two full-width fixed-base multiplications ([SpendAuthG] on the spend
    randomizer, [ValueCommitR] on the value-commitment trapdoor), the short
    fixed-base multiplication ([ValueCommitV] on the net-value magnitude), the
    variable-base ladder of the diversified-address integrity check, the
    value-commitment and spend-authority complete-addition legs, and the
    gadget-local witness-point / add / incomplete-add smoke regions.

    The function [advice] maps a cell [(column, region, offset)] to the value
    the honest prover writes, reusing the derived values of
    [OrchardWitnessInput].  It covers exactly the regions listed above and
    returns [0] on every other region and on every cell of those regions that
    no gate, copy, or lookup reads.

    Layout provenance (each cell's intended value is the read-back of a
    soundness bridge):

    - full-width fixed base ([circuit.synth_full_mul_incomplete_with_rows],
      bridged by [OrchardActionFixedBase.full_width_incomplete_window_correct]):
      window [i] carries the fixed window point on [A0]/[A1], its base-8 digit
      on [A4], and its square-root witness on [A5]; the incomplete-addition
      accumulator threads through [A2]/[A3];
    - short fixed base ([circuit.synth_short_mul_incomplete]): as above, but
      [A4] holds the running sum [magnitude / 8^i] (the [decompose_running_sum]
      column), with the strict tail [A4@22 = 0];
    - complete additions ([circuit.assign_complete_add]): operands on
      [A0]-[A3] at row 0, the case-split gradient on [A4], the [inv0]
      exceptional-case witnesses on [A5]-[A8], and [point_add] output on
      [A2]/[A3] at row 1 — the witness formulas of the [add] chip's
      completeness proof;
    - variable-base ladder ([mul.synthesize_variable_base_scalar_mul_region],
      bridged by [circuit_proof/ownership/var_base_mul.v]): row 0 doubles the
      base by complete addition; rows 2..126 and 2..127 carry the hi and lo
      incomplete double-and-add halves (bits 254..130 and 129..4 of
      [ivk + t_q]) on the [z]/[x_a]/[λ₁]/[λ₂] column quadruples
      [A9]/[A3]/[A4]/[A5] and [A6]/[A7]/[A8]/[A2]; rows 129..134 the three
      complete rounds (bits 3..1, one [QEccAdd] pair per bit with the
      [QMulDecomposeVar] running sums); row 135 the LSB round, its output
      [[ivk] g_d_old] on [A2]/[A3] of row 136; the overflow block carries
      the reduced [s = ivk + k_254·2^130], its 13-word running-sum
      decomposition, and the [z_0]/[z_130]/[k_254] copies of the ladder's
      [A9] running sums. *)

Module OrchardAdviceEccMuls.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.

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

  (** ** The fixed-base window tables

      The circuit-internal Lagrange tables of the three fixed bases this file
      multiplies by (from [orchard_internal_params]). *)
  Definition tbl_spend_auth : EccSpec.fixed_table :=
    OrchardCircuitSpec.spend_auth_g orchard_internal_params.
  Definition tbl_value_commit_r : EccSpec.fixed_table :=
    OrchardCircuitSpec.value_commit_r orchard_internal_params.
  Definition tbl_value_commit_v : EccSpec.fixed_table :=
    OrchardCircuitSpec.value_commit_v orchard_internal_params.
  Definition tbl_note_commit_r : EccSpec.fixed_table :=
    OrchardCircuitSpec.note_commit_r orchard_internal_params.

  Definition dummy_window : EccSpec.fixed_window := {|
    EccSpec.fw_coeffs := [];
    EccSpec.fw_z := 0;
  |}.

  (** ** Fixed-base incomplete-region cells

      The window point of window [i]: interpolation on the table row, [y]
      recovered from the square-root witness ([EccSpec.fixed_window_point]). *)
  Definition fb_window_point
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : list Z) (i : nat)
      : Point.t :=
    EccSpec.fixed_window_point (List.nth i tbl dummy_window)
      (EccSpec.window_digit scalar i) (List.nth i us 0).

  (** The running incomplete-addition accumulator: [acc_0] is window [0], and
      each further window is incomplete-added onto it low-window-first, so
      [fb_acc k] is the accumulator threaded into the [A2]/[A3] cells at
      offset [k + 1]. *)
  Fixpoint fb_acc
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : list Z) (k : nat)
      : Point.t :=
    match k with
    | O => fb_window_point tbl scalar us O
    | S k' =>
        EccSpec.point_add_incomplete
          (fb_window_point tbl scalar us (S k'))
          (fb_acc tbl scalar us k')
    end.

  (** The full-width incomplete region ([count] windows, one per offset).
      [A4] holds the base-8 digit directly (the full-width gate reads it
      without a running-sum difference).  The square-root list is passed as
      a thunk so that reads of the digit column — the
      [read_scalar_from_windows] reader — never force it. *)
  Definition fb_full_advice
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : unit -> list Z)
      (count : Z) (column : Advice.t) (offset : Z) : Z :=
    if (0 <=? offset) && (offset <? count) then
      let i := Z.to_nat offset in
      match column with
      | A0 => Point.x (fb_window_point tbl scalar (us tt) i)
      | A1 => Point.y (fb_window_point tbl scalar (us tt) i)
      | A4 => EccSpec.window_digit scalar i
      | A5 => List.nth i (us tt) 0
      | A2 =>
          if 1 <=? offset then Point.x (fb_acc tbl scalar (us tt) (i - 1))
          else 0
      | A3 =>
          if 1 <=? offset then Point.y (fb_acc tbl scalar (us tt) (i - 1))
          else 0
      | _ => 0
      end
    else 0.

  (** The short incomplete region ([count] windows).  [A4] holds the running
      sum [scalar / 8^offset] over the whole column [0 .. count] (the strict
      tail [A4@count = 0] falls out for a [count]-window in-range scalar);
      the square-root list is a thunk, as in [fb_full_advice]. *)
  Definition fb_short_advice
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : unit -> list Z)
      (count : Z) (column : Advice.t) (offset : Z) : Z :=
    match column with
    | A4 =>
        if (0 <=? offset) && (offset <=? count) then scalar / 8 ^ offset else 0
    | _ =>
        if (0 <=? offset) && (offset <? count) then
          let i := Z.to_nat offset in
          match column with
          | A0 => Point.x (fb_window_point tbl scalar (us tt) i)
          | A1 => Point.y (fb_window_point tbl scalar (us tt) i)
          | A5 => List.nth i (us tt) 0
          | A2 =>
              if 1 <=? offset then Point.x (fb_acc tbl scalar (us tt) (i - 1))
              else 0
          | A3 =>
              if 1 <=? offset then Point.y (fb_acc tbl scalar (us tt) (i - 1))
              else 0
          | _ => 0
          end
        else 0
    end.

  (** ** Complete-addition cells

      The [inv0] witness formulas of [circuit.assign_complete_add]: the secant
      or (equal-x) tangent gradient, and the exceptional-case inverse
      witnesses selecting the [x_p = 0] / [x_q = 0] / [x_p = x_q] /
      [y_p + y_q = 0] branches. *)
  Definition lambda_w (x_p y_p x_q y_q : Z) : Z :=
    if x_p =? x_q then
      if y_p =? 0 then 0
      else BinOp.div (UnOp.from 3 *F (x_p *F x_p)) (UnOp.from 2 *F y_p)
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

  (** A complete addition of operands [p], [q]: inputs on [A0]-[A3] at row 0,
      the witnesses on [A4]-[A8], and [EccSpec.point_add] output on [A2]/[A3]
      at row 1. *)
  Definition cadd_advice (p q : Point.t) (column : Advice.t) (offset : Z) : Z :=
    let x_p := Point.x p in let y_p := Point.y p in
    let x_q := Point.x q in let y_q := Point.y q in
    if offset =? 0 then
      match column with
      | A0 => x_p
      | A1 => y_p
      | A2 => x_q
      | A3 => y_q
      | A4 => lambda_w x_p y_p x_q y_q
      | A5 => alpha_w x_p x_q
      | A6 => beta_w x_p
      | A7 => gamma_w x_q
      | A8 => delta_w x_p y_p x_q y_q
      | A9 => 0
      end
    else if offset =? 1 then
      match column with
      | A2 => Point.x (EccSpec.point_add p q)
      | A3 => Point.y (EccSpec.point_add p q)
      | _ => 0
      end
    else 0.

  (** ** The scalar-multiplication leg points

      The two full-width legs (85 windows) and the short leg (22 windows), the
      final windows and accumulators feeding their complete-addition regions,
      and the derived leg points. *)
  Definition sa_scalar (w : HonestInput) : Z := hi_alpha w.
  Definition sa_us (w : HonestInput) : list Z := us_alpha w.
  Definition sa_window_last (w : HonestInput) : Point.t :=
    fb_window_point tbl_spend_auth (sa_scalar w) (sa_us w) 84.
  Definition sa_acc_last (w : HonestInput) : Point.t :=
    fb_acc tbl_spend_auth (sa_scalar w) (sa_us w) 83.
  (** [[alpha] SpendAuthG]. *)
  Definition sa_commitment (w : HonestInput) : Point.t :=
    EccSpec.point_add (sa_window_last w) (sa_acc_last w).

  Definition vcr_scalar (w : HonestInput) : Z := hi_rcv w.
  Definition vcr_us (w : HonestInput) : list Z := us_rcv w.
  Definition vcr_window_last (w : HonestInput) : Point.t :=
    fb_window_point tbl_value_commit_r (vcr_scalar w) (vcr_us w) 84.
  Definition vcr_acc_last (w : HonestInput) : Point.t :=
    fb_acc tbl_value_commit_r (vcr_scalar w) (vcr_us w) 83.
  (** [[rcv] ValueCommitR]. *)
  Definition vcr_point (w : HonestInput) : Point.t :=
    EccSpec.point_add (vcr_window_last w) (vcr_acc_last w).

  Definition vcv_scalar (w : HonestInput) : Z := magnitude w.
  Definition vcv_us (w : HonestInput) : list Z := us_magnitude w.
  Definition vcv_window_last (w : HonestInput) : Point.t :=
    fb_window_point tbl_value_commit_v (vcv_scalar w) (vcv_us w) 21.
  Definition vcv_acc_last (w : HonestInput) : Point.t :=
    fb_acc tbl_value_commit_v (vcv_scalar w) (vcv_us w) 20.
  (** The unsigned magnitude multiple [[magnitude] ValueCommitV]. *)
  Definition vcv_magnitude_mul (w : HonestInput) : Point.t :=
    EccSpec.point_add (vcv_window_last w) (vcv_acc_last w).
  (** The sign-adjusted [y] of the most-significant-word region: [y] on a
      positive net value, [-y] on a negative one. *)
  Definition vcv_y_var (w : HonestInput) : Z :=
    if sign w =? 1
    then Point.y (vcv_magnitude_mul w)
    else 0 -F Point.y (vcv_magnitude_mul w).
  (** [[v_net] ValueCommitV], sign applied. *)
  Definition vcv_point (w : HonestInput) : Point.t := {|
    Point.x := Point.x (vcv_magnitude_mul w);
    Point.y := vcv_y_var w;
  |}.

  (** ** The variable-base ladder

      The base point [g_d_old] and the ladder result
      [pk_d_old = [ivk] g_d_old]. *)
  Definition vb_base (w : HonestInput) : Point.t := hi_g_d_old w.
  Definition vb_result (w : HonestInput) : Point.t :=
    PallasModel.repr (Pallas.mul (ivk w) (mul_base w)).

  (** The incomplete double-and-add step at bit [i] (accumulator boundary
      [i + 1]): the intermediate sum [mid = acc ⊞ (2k_i − 1)B] and the two
      chord gradients the [q_mul_{1,2,3}] gates read
      ([ecc/chip/mul/incomplete.v]; soundness bridge
      [circuit_proof/ownership/var_base_incomplete.v]).  The accumulator's
      [y] is not stored per row — the gates recover it as
      [((λ₁ + λ₂)(x_a − x_r)) / 2]. *)
  Definition vb_step_mid (w : HonestInput) (i : nat) : Point.t :=
    EccSpec.point_add_incomplete (mul_acc w (S i)) (mul_step_point w i).

  Definition vb_step_l1 (w : HonestInput) (i : nat) : Z :=
    let acc := mul_acc w (S i) in
    let q := mul_step_point w i in
    BinOp.div (Point.y acc -F Point.y q) (Point.x acc -F Point.x q).

  Definition vb_step_l2 (w : HonestInput) (i : nat) : Z :=
    let acc := mul_acc w (S i) in
    let m := vb_step_mid w i in
    BinOp.div (Point.y acc -F Point.y m) (Point.x acc -F Point.x m).

  (** The complete-round chain (bits 3..1, [ecc/chip/mul/complete.v];
      soundness bridge [circuit_proof/ownership/var_base_complete.v]): per
      bit the signed base is complete-added into the accumulator and the
      accumulator complete-added onto the sum.  On the nondegenerate domain
      each [vb_acc_bit i] equals [mul_acc w i]. *)
  Definition vb_cacc4 (w : HonestInput) : Point.t := mul_acc w 4.
  Definition vb_mid_bit3 (w : HonestInput) : Point.t :=
    EccSpec.point_add (mul_step_point w 3) (vb_cacc4 w).
  Definition vb_acc_bit3 (w : HonestInput) : Point.t :=
    EccSpec.point_add (vb_cacc4 w) (vb_mid_bit3 w).
  Definition vb_mid_bit2 (w : HonestInput) : Point.t :=
    EccSpec.point_add (mul_step_point w 2) (vb_acc_bit3 w).
  Definition vb_acc_bit2 (w : HonestInput) : Point.t :=
    EccSpec.point_add (vb_acc_bit3 w) (vb_mid_bit2 w).
  Definition vb_mid_bit1 (w : HonestInput) : Point.t :=
    EccSpec.point_add (mul_step_point w 1) (vb_acc_bit2 w).
  Definition vb_acc_bit1 (w : HonestInput) : Point.t :=
    EccSpec.point_add (vb_acc_bit2 w) (vb_mid_bit1 w).

  (** The LSB round's point ([lsb_check_gate]): the [(0, 0)] identity
      sentinel on bit [1], [−B] on bit [0]. *)
  Definition vb_lsb_point (w : HonestInput) : Point.t :=
    if scalar_bit (mul_scalar w) 0 =? 1
    then {| Point.x := 0; Point.y := 0 |}
    else point_neg (vb_base w).

  (** The complete-addition operand pair [(p, q)] of a [QEccAdd] row of the
      region: the base doubling at row 0, per complete round the
      [signed-base + acc] then [acc + mid] pairs, and the LSB addition at
      row 135. *)
  Definition vb_cadd_ops (w : HonestInput) (offset : Z)
      : Point.t * Point.t :=
    if offset =? 129 then (mul_step_point w 3, vb_cacc4 w)
    else if offset =? 130 then (vb_cacc4 w, vb_mid_bit3 w)
    else if offset =? 131 then (mul_step_point w 2, vb_acc_bit3 w)
    else if offset =? 132 then (vb_acc_bit3 w, vb_mid_bit2 w)
    else if offset =? 133 then (mul_step_point w 1, vb_acc_bit2 w)
    else if offset =? 134 then (vb_acc_bit2 w, vb_mid_bit1 w)
    else if offset =? 135 then (vb_lsb_point w, vb_acc_bit1 w)
    else (vb_base w, vb_base w).

  (** The full 137-row variable-base region.  Row [r] of the hi half
      (rows 2..126) processes bit [256 − r] of [ivk + t_q] from accumulator
      boundary [257 − r] on columns [A9]/[A3]/[A4]/[A5]
      ([z]/[x_a]/[λ₁]/[λ₂]); row [r] of the lo half (rows 2..127) processes
      bit [131 − r] from boundary [132 − r] on [A6]/[A7]/[A8]/[A2]; both
      halves read the base on [A0]/[A1].  The boundary cells carry the
      witnessed [y_a] values ([A4@1], [A4@127], [A8@1], [A8@128]) and the
      final accumulator coordinates ([A2]/[A3]@1, [A3]/[A7]@127/128).  Rows
      129..135 host the complete rounds and the LSB round: the [QEccAdd]
      operand/output chain on [A0]..[A3] with the [assign_complete_add]
      witnesses on [A4]..[A8], and on [A9] the resumed running sums
      interleaved with the base-[y] pins the [QMulDecomposeVar] gate reads.
      Every cell equals the corresponding hoisted-table value
      ([tables_vb.v]) on the nondegenerate domain. *)
  Definition vb_advice (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    let k := mul_scalar w in
    match column with
    | A0 =>
        if (offset =? 0) || ((2 <=? offset) && (offset <=? 127))
           || (offset =? 129) || (offset =? 131) || (offset =? 133)
           || (offset =? 136)
        then Point.x (vb_base w)
        else if offset =? 130 then Point.x (vb_cacc4 w)
        else if offset =? 132 then Point.x (vb_acc_bit3 w)
        else if offset =? 134 then Point.x (vb_acc_bit2 w)
        else if offset =? 135 then Point.x (vb_lsb_point w)
        else 0
    | A1 =>
        if (offset =? 0) || ((2 <=? offset) && (offset <=? 127))
           || (offset =? 136)
        then Point.y (vb_base w)
        else if offset =? 129 then Point.y (mul_step_point w 3)
        else if offset =? 131 then Point.y (mul_step_point w 2)
        else if offset =? 133 then Point.y (mul_step_point w 1)
        else if offset =? 130 then Point.y (vb_cacc4 w)
        else if offset =? 132 then Point.y (vb_acc_bit3 w)
        else if offset =? 134 then Point.y (vb_acc_bit2 w)
        else if offset =? 135 then Point.y (vb_lsb_point w)
        else 0
    | A2 =>
        if offset =? 0 then Point.x (vb_base w)
        else if offset =? 1 then Point.x (mul_acc w 255)
        else if (2 <=? offset) && (offset <=? 127)
        then vb_step_l2 w (Z.to_nat (131 - offset))
        else if offset =? 129 then Point.x (vb_cacc4 w)
        else if offset =? 130 then Point.x (vb_mid_bit3 w)
        else if offset =? 131 then Point.x (vb_acc_bit3 w)
        else if offset =? 132 then Point.x (vb_mid_bit2 w)
        else if offset =? 133 then Point.x (vb_acc_bit2 w)
        else if offset =? 134 then Point.x (vb_mid_bit1 w)
        else if offset =? 135 then Point.x (vb_acc_bit1 w)
        else if offset =? 136 then Point.x (vb_result w)
        else 0
    | A3 =>
        if offset =? 0 then Point.y (vb_base w)
        else if offset =? 1 then Point.y (mul_acc w 255)
        else if (2 <=? offset) && (offset <=? 126)
        then Point.x (mul_acc w (Z.to_nat (257 - offset)))
        else if offset =? 127 then Point.x (mul_acc w 130)
        else if offset =? 129 then Point.y (vb_cacc4 w)
        else if offset =? 130 then Point.y (vb_mid_bit3 w)
        else if offset =? 131 then Point.y (vb_acc_bit3 w)
        else if offset =? 132 then Point.y (vb_mid_bit2 w)
        else if offset =? 133 then Point.y (vb_acc_bit2 w)
        else if offset =? 134 then Point.y (vb_mid_bit1 w)
        else if offset =? 135 then Point.y (vb_acc_bit1 w)
        else if offset =? 136 then Point.y (vb_result w)
        else 0
    | A4 =>
        if offset =? 1 then Point.y (mul_acc w 255)
        else if (2 <=? offset) && (offset <=? 126)
        then vb_step_l1 w (Z.to_nat (256 - offset))
        else if offset =? 127 then Point.y (mul_acc w 130)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := vb_cadd_ops w offset in
          lambda_w (Point.x pp) (Point.y pp) (Point.x qq) (Point.y qq)
        else 0
    | A5 =>
        if (2 <=? offset) && (offset <=? 126)
        then vb_step_l2 w (Z.to_nat (256 - offset))
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := vb_cadd_ops w offset in
          alpha_w (Point.x pp) (Point.x qq)
        else 0
    | A6 =>
        if (1 <=? offset) && (offset <=? 127)
        then bit_running_sum k (Z.to_nat (131 - offset))
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, _) := vb_cadd_ops w offset in
          beta_w (Point.x pp)
        else 0
    | A7 =>
        if (2 <=? offset) && (offset <=? 127)
        then Point.x (mul_acc w (Z.to_nat (132 - offset)))
        else if offset =? 128 then Point.x (vb_cacc4 w)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(_, qq) := vb_cadd_ops w offset in
          gamma_w (Point.x qq)
        else 0
    | A8 =>
        if offset =? 1 then Point.y (mul_acc w 130)
        else if (2 <=? offset) && (offset <=? 127)
        then vb_step_l1 w (Z.to_nat (131 - offset))
        else if offset =? 128 then Point.y (vb_cacc4 w)
        else if (offset =? 0) || ((129 <=? offset) && (offset <=? 135)) then
          let '(pp, qq) := vb_cadd_ops w offset in
          delta_w (Point.x pp) (Point.y pp) (Point.x qq) (Point.y qq)
        else 0
    | A9 =>
        if (1 <=? offset) && (offset <=? 126)
        then bit_running_sum k (Z.to_nat (256 - offset))
        else if offset =? 129 then bit_running_sum k 4
        else if offset =? 131 then bit_running_sum k 3
        else if offset =? 133 then bit_running_sum k 2
        else if offset =? 135 then bit_running_sum k 1
        else if offset =? 136 then k
        else if (offset =? 130) || (offset =? 132) || (offset =? 134)
        then Point.y (vb_base w)
        else 0
    end.

  (** ** The overflow check

      [s = alpha + k_254 . 2^130] recovers the top scalar bit
      ([ecc/chip/mul/overflow.v]; soundness bridge
      [circuit_proof/ownership/var_base_overflow.v]).  [s] is reduced to its
      field representative: the lookup region decomposes the reduced value
      into thirteen 10-bit running sums, so on [k_254 = 1] — where
      [alpha + 2^130 ≥ p] — the tail [z_13 = s / 2^130] is [0], as the
      [s_minus_lo_130_check] constraint requires.  The check region copies
      the three var-base [A9] running sums ([z_136 = ivk + t_q],
      [z_126 = z_130], [z_2 = k_254]) and [alpha]/[s]/[z_13], and witnesses
      the [η] inverse of [z_130] for the canonicity constraint. *)
  Definition vb_k254 (w : HonestInput) : Z := mul_scalar w / 2 ^ 254.
  Definition vb_s (w : HonestInput) : Z :=
    (ivk w + vb_k254 w * 2 ^ 130) mod Primes.pallas_p.
  Definition vb_z130 (w : HonestInput) : Z := mul_scalar w / 2 ^ 130.
  Definition vb_eta (w : HonestInput) : Z :=
    if vb_z130 w =? 0 then 0
    else mod_inverse (vb_z130 w) Primes.pallas_p.

  Definition overflow_s_advice (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    if (offset =? 0) then match column with A6 => vb_s w | _ => 0 end else 0.

  Definition overflow_lookup_advice
      (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    match column with
    | A9 => if (0 <=? offset) && (offset <=? 13) then vb_s w / 2 ^ (10 * offset) else 0
    | _ => 0
    end.

  Definition overflow_check_advice
      (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    if offset =? 0 then
      match column with
      | A6 => mul_scalar w    (* z_136 copy: the full 255-bit running sum *)
      | A7 => vb_k254 w       (* z_2 copy: the top scalar bit *)
      | _ => 0
      end
    else if offset =? 1 then
      match column with
      | A6 => vb_z130 w       (* z_126 copy *)
      | A7 => ivk w           (* alpha copy *)
      | A8 => vb_s w          (* s copy *)
      | _ => 0
      end
    else if offset =? 2 then
      match column with
      | A6 => vb_eta w           (* eta: the inverse witness of z_130 *)
      | A7 => vb_s w / 2 ^ 130   (* z_13 copy: low-130-bit running-sum tail *)
      | _ => 0
      end
    else 0.

  (** ** The witness-point / range-check cells *)

  (** The witnessed diversified public key [pk_d_old = [ivk] g_d_old]. *)
  Definition witness_pk_d_advice
      (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    if offset =? 0 then
      match column with
      | A0 => Point.x (vb_result w)
      | A1 => Point.y (vb_result w)
      | _ => 0
      end
    else 0.

  (** ** The whole ECC-mul advice plane

      Dispatch over the region families this generator owns; every other
      region and every unread cell default to [0]. *)
  Definition is_A9 (column : Advice.t) : bool :=
    match column with A9 => true | _ => false end.

  Definition advice
      (w : HonestInput) (column : Advice.t) (region : RegionId.t) (offset : Z)
      : Z :=
    match region with
    (* Spend authority: the full-width [alpha] SpendAuthG leg and [rk]. *)
    | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete =>
        fb_full_advice tbl_spend_auth (sa_scalar w) (fun _ => sa_us w) 85
          column offset
    | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast =>
        cadd_advice (sa_window_last w) (sa_acc_last w) column offset
    | RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd =>
        cadd_advice (sa_commitment w) (hi_ak w) column offset
    (* Value commitment: the magnitude/sign witnesses, the V short leg, the R
       full-width leg, and [cv_net]. *)
    | RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck =>
        if (is_A9 column) && (offset =? 0) then magnitude w else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck =>
        if (is_A9 column) && (offset =? 0) then sign w else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete =>
        fb_short_advice tbl_value_commit_v (vcv_scalar w) (fun _ => vcv_us w)
          22 column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb =>
        if offset =? 0 then
          cadd_advice (vcv_window_last w) (vcv_acc_last w) column 0
        else if offset =? 1 then
          match column with
          | A1 => vcv_y_var w
          | A2 => Point.x (vcv_magnitude_mul w)
          | A3 => Point.y (vcv_magnitude_mul w)
          | A4 => sign w
          | A5 => vcv_scalar w / 8 ^ 21
          | _ => 0
          end
        else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete =>
        fb_full_advice tbl_value_commit_r (vcr_scalar w) (fun _ => vcr_us w)
          85 column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast =>
        cadd_advice (vcr_window_last w) (vcr_acc_last w) column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd =>
        cadd_advice (vcv_point w) (vcr_point w) column offset
    (* Address integrity: the variable-base ladder, its overflow check, the
       witnessed pk_d_old, and the (copy-only) equality region. *)
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase) =>
        vb_advice w column offset
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowS) =>
        overflow_s_advice w column offset
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowLookup) =>
        overflow_lookup_advice w column offset
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck) =>
        overflow_check_advice w column offset
    | RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD =>
        witness_pk_d_advice w column offset
    | RegionId.AddressIntegrity RegionId.AddressIntegrity.Equality => 0
    (* Note commitments: the [rcm] full-width NoteCommitR blinding legs of
       the old and new notes ([read_scalar_from_windows] reads the new
       leg's digit column back as [in_rcm_new]). *)
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.FixedBaseIncomplete =>
        fb_full_advice tbl_note_commit_r (hi_rcm_old w) (fun _ => us_rcm_old w)
          85 column offset
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete =>
        fb_full_advice tbl_note_commit_r (hi_rcm_new w) (fun _ => us_rcm_new w)
          85 column offset
    (* Every region outside the ECC-mul block, and the gadget-local ECC smoke
       regions (which enable a selector but write no advice). *)
    | _ => 0
    end.

End OrchardAdviceEccMuls.
