Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

(** * The witness-input advice sub-generator

    The forward image, on the advice plane, of the [circuit_proof] readers for
    the regions the whole-action witness inputs live in: the eight
    [WitnessInput] regions (the free advice / witnessed points of
    [synthesize_witness_inputs]), the [OrchardCircuitChecks] copy row (the
    [QOrchard] gate's eight read cells), and the public [Instance_.Primary]
    rows the gate's copies and the [ConstrainInstance] sites pin.

    This file supplies *values* only; it does not build a full
    [Assignment.t] and proves no gate-satisfaction facts (that is the
    assembly / C2 step).  Each in-scope cell carries the value the region's
    synthesize program and its reader
    ([Garden.Orchard.circuit_proof.inputs.read_action_inputs]) fix; every
    other cell defaults to [0].  The definitions read off
    [OrchardWitnessInput]'s derived values, so the read-back equalities
    ([read_action_inputs (…) = inputs_of w]) reduce to reflexivity on this
    plane. *)

Module OrchardAdviceWitnessIo.
  Import OrchardWitnessInput.

  (** ** The [WitnessInput] regions

      [synthesize_witness_inputs] (circuit.v) lays each auxiliary input at
      row 0 of its own region:

      - the scalar witnesses [PsiOld] / [RhoOld] / [Nk] / [VOld] / [VNew] on
        [A0] (via [assign_free_advice … Advice.A0]);
      - the points [CmOld] ([witness_point], [QWitnessPoint]) and
        [GDOld] / [AkP] ([witness_non_identity_point],
        [QWitnessPointNonId]) on [A0] (x) and [A1] (y).

      The witness-point gates read [A0]/[A1] at [Rotation.cur] only
      ([witness_point.v]); the readers ([read], [read_point]) read the same
      cells.  [CmOld]'s [A0] is both the commitment's x-coordinate and the
      Merkle leaf ([in_leaf := read … CmOld]; [leaf w = extract_x (cm_old w)
      = Point.x (cm_old w)]), so one value serves both reads. *)
  Definition witness_input_advice (w : HonestInput)
      (column : Advice.t) (region : RegionId.WitnessInput.t) (row : Z) : Z :=
    if row =? 0 then
      match region, column with
      | RegionId.WitnessInput.PsiOld, Advice.A0 => hi_psi_old w
      | RegionId.WitnessInput.RhoOld, Advice.A0 => hi_rho_old w
      | RegionId.WitnessInput.CmOld, Advice.A0 => Point.x (cm_old w)
      | RegionId.WitnessInput.CmOld, Advice.A1 => Point.y (cm_old w)
      | RegionId.WitnessInput.GDOld, Advice.A0 => Point.x (hi_g_d_old w)
      | RegionId.WitnessInput.GDOld, Advice.A1 => Point.y (hi_g_d_old w)
      | RegionId.WitnessInput.AkP, Advice.A0 => Point.x (hi_ak w)
      | RegionId.WitnessInput.AkP, Advice.A1 => Point.y (hi_ak w)
      | RegionId.WitnessInput.Nk, Advice.A0 => hi_nk w
      | RegionId.WitnessInput.VOld, Advice.A0 => hi_v_old w
      | RegionId.WitnessInput.VNew, Advice.A0 => hi_v_new w
      | _, _ => 0
      end
    else 0.

  (** ** The [OrchardCircuitChecks] copy row

      [synthesize_orchard_gate] copies eight cells into row 0 of the
      [OrchardCircuitChecks] region — the [QOrchard] gate's reads
      ([orchard_circuit_checks_gate]):

      - [A0] ← [v_old], [A1] ← [v_new] (from [VOld] / [VNew]);
      - [A2] ← [magnitude], [A3] ← [sign] (from the value-commitment range
        checks);
      - [A4] ← [root] (the Merkle-path output cell);
      - [A5] ← [anchor], [A6] ← [enable_spends], [A7] ← [enable_outputs]
        (from the [Instance_.Primary] rows [ANCHOR] / [ENABLE_SPEND] /
        [ENABLE_OUTPUT]).

      Each value equals its copy source: the [VOld] / [VNew] cells above, the
      value-commitment [magnitude] / [sign] cells, the Merkle root
      ([anchor_root w]), and the public rows below.  On [v_old ≠ 0] the
      [root = anchor] conjunct forces [A4 = A5]; both are [anchor_root w]
      there ([anchor_public_row_root]). *)
  Definition orchard_checks_advice (w : HonestInput)
      (column : Advice.t) (row : Z) : Z :=
    if row =? 0 then
      match column with
      | Advice.A0 => hi_v_old w
      | Advice.A1 => hi_v_new w
      | Advice.A2 => magnitude w
      | Advice.A3 => sign w
      | Advice.A4 => anchor_root w
      | Advice.A5 => anchor_public_row w
      | Advice.A6 => hi_enable_spends w
      | Advice.A7 => hi_enable_outputs w
      | _ => 0
      end
    else 0.

  (** ** The new-note witness marker regions

      [synthesize_note_commit_new] (circuit.v) witnesses the new note's
      diversified base and transmission key with [witness_non_identity_point]
      ([QWitnessPointNonId]; [A0] = x, [A1] = y at row 0) in the
      [NoteCommitNewWitnessGD] / [NoteCommitNewWitnessPkD] regions, and [ψ]
      with [assign_free_advice] on [A0] of [NoteCommitNewWitnessPsi] — the
      cells [read_action_inputs] reads back as [in_g_d_new] / [in_pk_d_new] /
      [in_psi_new].  [NoteCommitOldEquality] holds no own cells (its region
      program only copies cells of other regions). *)
  Definition note_commit_new_witness_advice (w : HonestInput)
      (point : Point.t) (column : Advice.t) (row : Z) : Z :=
    if row =? 0 then
      match column with
      | Advice.A0 => Point.x point
      | Advice.A1 => Point.y point
      | _ => 0
      end
    else 0.

  (** ** The advice plane

      The generator on the full [RegionId.t]: the region families above,
      [0] everywhere else.  Composed with the other per-gadget advice
      sub-generators (Merkle, value commitment, nullifier, …) it forms the
      [Assignment.advice] field of [honest_assignment]. *)
  Definition advice_witness_io (w : HonestInput)
      (column : Advice.t) (region : RegionId.t) (row : Z) : Z :=
    match region with
    | RegionId.WitnessInput r => witness_input_advice w column r row
    | RegionId.OrchardCircuitChecks => orchard_checks_advice w column row
    | RegionId.NoteCommitNewWitnessGD =>
        note_commit_new_witness_advice w (hi_g_d_new w) column row
    | RegionId.NoteCommitNewWitnessPkD =>
        note_commit_new_witness_advice w (hi_pk_d_new w) column row
    | RegionId.NoteCommitNewWitnessPsi =>
        if (row =? 0) then
          match column with
          | Advice.A0 => hi_psi_new w
          | _ => 0
          end
        else 0
    | _ => 0
    end.

  (** ** The public [Instance_.Primary] rows

      The primary-input column, indexed by the row constants of [circuit.v].
      Rows [ANCHOR] / [ENABLE_SPEND] / [ENABLE_OUTPUT] are copied into the
      [OrchardCircuitChecks] row; [CV_NET_*] / [NF_OLD] / [RK_*] / [CMX] are
      the [ConstrainInstance] targets of the value-commitment, nullifier,
      spend-authority and new-note-commitment gadgets.  This is the [x] side
      of the §4.1.13 statement — the public instance the honest proof
      satisfies — and the [Assignment.instance_] field of
      [honest_assignment]. *)
  Definition public_instance_row (w : HonestInput) (row : Z) : Z :=
    match row with
    | 0 => anchor_public_row w      (* ANCHOR *)
    | 1 => Point.x (cv_net w)       (* CV_NET_X *)
    | 2 => Point.y (cv_net w)       (* CV_NET_Y *)
    | 3 => nf_old w                 (* NF_OLD (= rho_new) *)
    | 4 => Point.x (rk w)           (* RK_X *)
    | 5 => Point.y (rk w)           (* RK_Y *)
    | 6 => cmx w                    (* CMX *)
    | 7 => hi_enable_spends w       (* ENABLE_SPEND *)
    | 8 => hi_enable_outputs w      (* ENABLE_OUTPUT *)
    | _ => 0
    end.

  (** ** Layout-agreement lemmas

      Small equalities documenting the copy / instance invariants the gate
      satisfaction and read-back proofs rely on.  They fix the intended
      values against [circuit.v]'s named constants and the copy sources;
      the per-gate constraint proofs are the follow-up (C2) step. *)

  (** The public rows land at their named constants (the [ConstrainInstance]
      row indices of [circuit.v]). *)
  Lemma public_instance_row_anchor (w : HonestInput) :
    public_instance_row w Garden.Orchard.circuit.ANCHOR = anchor_public_row w.
  Proof. reflexivity. Qed.

  Lemma public_instance_row_nf_old (w : HonestInput) :
    public_instance_row w Garden.Orchard.circuit.NF_OLD = nf_old w.
  Proof. reflexivity. Qed.

  Lemma public_instance_row_cmx (w : HonestInput) :
    public_instance_row w Garden.Orchard.circuit.CMX = cmx w.
  Proof. reflexivity. Qed.

  Lemma public_instance_row_enable_spends (w : HonestInput) :
    public_instance_row w Garden.Orchard.circuit.ENABLE_SPEND =
      hi_enable_spends w.
  Proof. reflexivity. Qed.

  Lemma public_instance_row_enable_outputs (w : HonestInput) :
    public_instance_row w Garden.Orchard.circuit.ENABLE_OUTPUT =
      hi_enable_outputs w.
  Proof. reflexivity. Qed.

  (** The [OrchardCircuitChecks] value copies agree with their sources in the
      [WitnessInput] regions (the [Copy v_old_target v_old] /
      [Copy v_new_target v_new] obligations). *)
  Lemma orchard_checks_copies_v_old (w : HonestInput) :
    advice_witness_io w Advice.A0 RegionId.OrchardCircuitChecks 0 =
      advice_witness_io w Advice.A0
        (RegionId.WitnessInput RegionId.WitnessInput.VOld) 0.
  Proof. reflexivity. Qed.

  Lemma orchard_checks_copies_v_new (w : HonestInput) :
    advice_witness_io w Advice.A1 RegionId.OrchardCircuitChecks 0 =
      advice_witness_io w Advice.A0
        (RegionId.WitnessInput RegionId.WitnessInput.VNew) 0.
  Proof. reflexivity. Qed.

  (** The instance copies agree with the public rows they read
      ([Copy anchor_target anchor_instance] and the two enable-flag copies). *)
  Lemma orchard_checks_copies_anchor (w : HonestInput) :
    advice_witness_io w Advice.A5 RegionId.OrchardCircuitChecks 0 =
      public_instance_row w Garden.Orchard.circuit.ANCHOR.
  Proof. reflexivity. Qed.

  Lemma orchard_checks_copies_enable_spends (w : HonestInput) :
    advice_witness_io w Advice.A6 RegionId.OrchardCircuitChecks 0 =
      public_instance_row w Garden.Orchard.circuit.ENABLE_SPEND.
  Proof. reflexivity. Qed.

  Lemma orchard_checks_copies_enable_outputs (w : HonestInput) :
    advice_witness_io w Advice.A7 RegionId.OrchardCircuitChecks 0 =
      public_instance_row w Garden.Orchard.circuit.ENABLE_OUTPUT.
  Proof. reflexivity. Qed.

  (** On a real spend ([v_old ≠ 0]) the root ([A4]) and anchor ([A5]) cells
      coincide, discharging the [QOrchard] "root = anchor" conjunct's value
      obligation; on a dummy spend the conjunct is waived by the [v_old = 0]
      branch. *)
  Lemma orchard_checks_root_anchor (w : HonestInput) :
    hi_v_old w <> 0 ->
    advice_witness_io w Advice.A4 RegionId.OrchardCircuitChecks 0 =
      advice_witness_io w Advice.A5 RegionId.OrchardCircuitChecks 0.
  Proof.
    intro Hv.
    apply Z.eqb_neq in Hv.
    unfold advice_witness_io, orchard_checks_advice, anchor_public_row.
    rewrite Z.eqb_refl, Hv.
    reflexivity.
  Qed.

  (** The [CmOld] [A0] cell serves both the commitment x-coordinate
      ([in_cm_old]) and the Merkle leaf ([in_leaf]): [leaf w = Point.x
      (cm_old w)]. *)
  Lemma witness_input_cm_old_leaf (w : HonestInput) :
    advice_witness_io w Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 = leaf w.
  Proof.
    unfold advice_witness_io, witness_input_advice, leaf, EccSpec.extract_x.
    (* Both sides project the [x] lane of [cm_old w]; abstracting the point
       keeps the projection stuck, so [reflexivity] never forces the whnf of
       the [NoteCommit] Sinsemilla fold hidden in [cm_old]. *)
    generalize (cm_old w); intro P.
    reflexivity.
  Qed.

End OrchardAdviceWitnessIo.
