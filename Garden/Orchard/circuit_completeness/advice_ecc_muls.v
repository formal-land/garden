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
Require Import Garden.Orchard.circuit_completeness.witness_input.
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
    - variable-base ladder ([mul.synthesize_variable_base_scalar_mul_region]):
      the base-point copies and the [[ivk] g_d_old] result cell; the deep
      double-and-add interior rows are the per-gate C2 obligation and default
      to [0]. *)

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
  (** [rk = ak + [alpha] SpendAuthG]. *)
  Definition rk_point (w : HonestInput) : Point.t :=
    EccSpec.point_add (sa_commitment w) (hi_ak w).

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
  (** [cv_net = [v_net] ValueCommitV + [rcv] ValueCommitR]. *)
  Definition cv_point (w : HonestInput) : Point.t :=
    EccSpec.point_add (vcv_point w) (vcr_point w).

  (** ** The variable-base ladder

      The base point [g_d_old] and the ladder result
      [pk_d_old = [ivk] g_d_old]. *)
  Definition vb_base (w : HonestInput) : Point.t := hi_g_d_old w.
  Definition vb_result (w : HonestInput) : Point.t :=
    PallasModel.repr (Pallas.mul (ivk w) (mul_base w)).

  (** The variable-base region's cleanly-determined cells: the base-point
      copies at the first double-and-add row, the zero-initialised running
      sum, and the [[ivk] g_d_old] result at [A2]/[A3] of the final row.  The
      interior double-and-add rows (the incomplete hi/lo ladders, the complete
      final rounds, and the [A9] scalar running sums) are the per-gate C2
      obligation and default to [0]. *)
  Definition vb_advice (w : HonestInput) (column : Advice.t) (offset : Z) : Z :=
    if offset =? 0 then
      match column with
      | A0 => Point.x (vb_base w)
      | A1 => Point.y (vb_base w)
      | A2 => Point.x (vb_base w)
      | A3 => Point.y (vb_base w)
      | _ => 0
      end
    else if offset =? 1 then
      match column with A9 => 0 | _ => 0 end
    else if offset =? 136 then
      match column with
      | A0 => Point.x (vb_base w)
      | A1 => Point.y (vb_base w)
      | A2 => Point.x (vb_result w)
      | A3 => Point.y (vb_result w)
      | _ => 0
      end
    else 0.

  (** ** The overflow check

      [s = alpha + k_254 . 2^130] recovers the top scalar bit; the lookup
      region decomposes its low 130 bits into thirteen 10-bit running sums;
      the check region copies the three var-base running sums and [alpha]/[s].
      The cross-region [z] copies ([z_2], [z_126], [z_136]) mirror the
      variable-base [A9] running sums (defaulted above) and so default to [0]
      here for copy consistency; the [alpha]/[s]/[z_13] cells carry their
      determined values. *)
  Definition vb_k254 (w : HonestInput) : Z := mul_scalar w / 2 ^ 254.
  Definition vb_s (w : HonestInput) : Z := ivk w + vb_k254 w * 2 ^ 130.

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
      | A6 => 0            (* z_136 copy: mirrors the defaulted var-base A9 *)
      | A7 => 0            (* z_2 copy *)
      | _ => 0
      end
    else if offset =? 1 then
      match column with
      | A6 => 0            (* z_126 copy *)
      | A7 => ivk w        (* alpha copy *)
      | A8 => vb_s w       (* s copy *)
      | _ => 0
      end
    else if offset =? 2 then
      match column with
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

  (** ** Small agreement lemmas

      The running-sum column of the short leg telescopes by a factor of 8, and
      the full-width digit column reads back the leg's base-8 digits — the two
      identities the running-sum coordinate gate and the reader
      [read_scalar_from_windows] pin. *)
  Lemma fb_short_A4_step
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : unit -> list Z)
      (count offset : Z)
      (Hlo : 0 <= offset)
      (Hhi : offset < count) :
    fb_short_advice tbl scalar us count A4 offset =
      EccSpec.window_digit scalar (Z.to_nat offset) +
        8 * fb_short_advice tbl scalar us count A4 (offset + 1).
  Proof.
    unfold fb_short_advice.
    assert (H0 : (0 <=? offset) = true) by (apply Z.leb_le; lia).
    assert (H1 : (offset <=? count) = true) by (apply Z.leb_le; lia).
    assert (H2 : (0 <=? offset + 1) = true) by (apply Z.leb_le; lia).
    assert (H3 : (offset + 1 <=? count) = true) by (apply Z.leb_le; lia).
    rewrite H0, H1, H2, H3. cbn [andb].
    (* [scalar / 8^offset = digit + 8 * (scalar / 8^(offset+1))]. *)
    unfold EccSpec.window_digit.
    rewrite (Z2Nat.id offset) by lia.
    replace (8 ^ (offset + 1)) with (8 ^ offset * 8).
    2:{ rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
    rewrite <- Z.div_div by lia.
    pose proof (Z.div_mod (scalar / 8 ^ offset) 8 ltac:(lia)) as Hdm.
    clear -Hdm. lia.
  Qed.

  Lemma fb_full_digit_read
      (tbl : EccSpec.fixed_table) (scalar : Z) (us : unit -> list Z)
      (count offset : Z)
      (Hlo : 0 <= offset)
      (Hhi : offset < count) :
    fb_full_advice tbl scalar us count A4 offset =
      EccSpec.window_digit scalar (Z.to_nat offset).
  Proof.
    unfold fb_full_advice.
    assert (H0 : (0 <=? offset) = true) by (apply Z.leb_le; lia).
    assert (H1 : (offset <? count) = true) by (apply Z.ltb_lt; lia).
    rewrite H0, H1. cbn [andb]. reflexivity.
  Qed.

End OrchardAdviceEccMuls.
