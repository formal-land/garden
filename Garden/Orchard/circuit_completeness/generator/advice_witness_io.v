Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.

Global Open Scope Z_scope.

(** * The witness-input advice sub-generator

    The forward image, on the advice plane, of the [circuit_proof] readers for
    the regions the whole-action witness inputs live in: the eight
    [WitnessInput] regions (the free advice / witnessed points of
    [synthesize_witness_inputs]), the [OrchardCircuitChecks] copy row (the
    [QOrchard] gate's eight read cells), the four post-NU6.3 cross-address
    rows, and the public [Instance_.Primary] rows their copies and the
    [ConstrainInstance] sites pin.

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

  (** ** Post-NU6.3 cross-address rows

      Rows 0..3 compare [g_d.x], [g_d.y], [pk_d.x], and [pk_d.y].
      [A0]/[A2]/[A8]/[A9] carry the public disable flag,
      [A1]/[A3]/[A6]/[A7] carry the neutralizing constants, and [A4]/[A5]
      carry the corresponding old/new coordinates. *)
  Definition cross_address_checks_advice (w : HonestInput)
      (column : Advice.t) (row : Z) : Z :=
    let old_coordinate :=
      match row with
      | 0 => Point.x (hi_g_d_old w)
      | 1 => Point.y (hi_g_d_old w)
      | 2 => Point.x (hi_pk_d_old w)
      | 3 => Point.y (hi_pk_d_old w)
      | _ => 0
      end in
    let new_coordinate :=
      match row with
      | 0 => Point.x (hi_g_d_new w)
      | 1 => Point.y (hi_g_d_new w)
      | 2 => Point.x (hi_pk_d_new w)
      | 3 => Point.y (hi_pk_d_new w)
      | _ => 0
      end in
    if (0 <=? row) && (row <? 4) then
      match column with
      | Advice.A0
      | Advice.A2
      | Advice.A8
      | Advice.A9 => hi_disable_cross_address w
      | Advice.A1 => 0
      | Advice.A3
      | Advice.A6
      | Advice.A7 => 1
      | Advice.A4 => old_coordinate
      | Advice.A5 => new_coordinate
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
    | RegionId.PostNu63CrossAddressChecks =>
        cross_address_checks_advice w column row
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
      [OrchardCircuitChecks] row, and [DISABLE_CROSS_ADDRESS] is copied into
      every post-NU6.3 coordinate-check row.  [CV_NET_*] / [NF_OLD] / [RK_*]
      / [CMX] are the [ConstrainInstance] targets of the value-commitment,
      nullifier, spend-authority and new-note-commitment gadgets.  This is the
      [x] side of the §4.1.13 statement — the public instance the honest proof
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
    | 9 => hi_disable_cross_address w (* DISABLE_CROSS_ADDRESS *)
    | _ => 0
    end.

End OrchardAdviceWitnessIo.
