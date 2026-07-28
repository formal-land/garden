(** * Hoisted per-family tables for the honest-witness generator

    The [vm_compute] cost discipline for the whole-circuit completeness
    certificates: the virtual machine shares no work between two applications
    of the same function, so an advice plane that recomputes a region-level
    derivation (a Sinsemilla accumulator prefix, a fixed-base ladder fold, a
    scalar multiple) at every cell read makes the per-family certificates
    infeasible (the per-read cost profile is recorded in
    [docs/compile-performance.md]).  Global constants, by contrast, are
    evaluated once per [vm_compute] run and closure environments are built
    strictly, so every region-level derivation is hoisted here into a
    [tables] record computed once per honest assignment.  [honest_assignment]
    binds [tables_of w] in a [let] outside the per-cell lambdas: one
    [vm_compute] run forces the record once, and every cell read is a list
    lookup.

    The cell values are numerically identical to the per-read sub-generators
    of the [advice_*] files (whose per-region readers this file's dispatcher
    [advice_t] mirrors), with one exception: the square-root witnesses of the
    fixed-base window points are read from the window-sign certificates'
    pasted root tables ([circuit_proof/<base>/sign_cert.v], one root per
    (window, digit) with [root² = fw_z + y]) instead of the per-window
    [field_sqrt] of [canonical_us_for] — the recovered [y = u² − z] is the
    same for either root, and the [u]-cells only ever face the [u² = y + z]
    coordinate checks.

    The builders reuse the specification functions step by step
    (incomplete-addition chords, window interpolation, Poseidon round
    schedule), so every table entry equals the corresponding specification
    value; the certificates verify that equality numerically. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_witness_io.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardCompletenessTables.
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

  Definition point0 : Point.t := {| Point.x := 0; Point.y := 0 |}.
  Definition state0 : State.t :=
    {| State.x0 := 0; State.x1 := 0; State.x2 := 0 |}.
  Definition row0 : Z * Z * Z * Z := (0, 0, 0, 0).

  (** ** Sinsemilla hash-to-point region data

      One record per hash region: per round [j], the accumulator's
      x-coordinate [x_a(j)], the generator's x-coordinate [x_p(j)] and the two
      chord gradients [λ₁(j)]/[λ₂(j)]; plus the output point, the [bits]
      running-sum column and the message words.  The fold mirrors
      [IncompleteAddition.output] literally (the same reduced chord formulas),
      so every entry equals the corresponding
      [round_acc]/[round_gen]/[round_lambda1]/[round_lambda2] value while the
      whole region costs two field inversions per round, once. *)
  Record hash_data : Set := {
    hd_rows : list (Z * Z * Z * Z);
    hd_out : Point.t;
    hd_bits : list Z;
    hd_words : list Z;
  }.

  Fixpoint hash_go (acc : Point.t) (ws : list Z)
      : list (Z * Z * Z * Z) * Point.t :=
    match ws with
    | [] => ([], acc)
    | wd :: ws' =>
        let g := SinsemillaSpec.generator wd in
        let xa := Point.x acc in
        let ya := Point.y acc in
        let xg := Point.x g in
        let yg := Point.y g in
        let l1 := BinOp.div (ya -F yg) (xa -F xg) in
        let xm := l1 *F l1 -F xa -F xg in
        let ym := l1 *F (xa -F xm) -F ya in
        let l2 := BinOp.div (ym -F ya) (xm -F xa) in
        let xn := l2 *F l2 -F xm -F xa in
        let yn := l2 *F (xm -F xn) -F ym in
        let '(rows, out) := hash_go {| Point.x := xn; Point.y := yn |} ws' in
        ((xa, xg, l1, l2) :: rows, out)
    end.

  Definition hash_data_of (Q : Point.t) (pieces : list (list Z)) : hash_data :=
    let words := Stdlib.Lists.List.concat pieces in
    let '(rows, out) := hash_go Q words in
    {|
      hd_rows := rows;
      hd_out := out;
      hd_bits := OrchardAdviceMerkleSinsemilla.bits_column pieces;
      hd_words := words;
    |}.

  (** The hash-region reader: [OrchardAdviceMerkleSinsemilla
      .hash_region_advice] with every prefix fold replaced by a row lookup. *)
  Definition hash_region_advice_t (h : hash_data) (second : bool)
      (col : Advice.t) (row : Z) : Z :=
    let nn := Z.of_nat (List.length (hd_words h)) in
    let j := Z.to_nat row in
    match OrchardAdviceMerkleSinsemilla.logical_col second col with
    | Some 0%nat =>
        if (0 <=? row) && (row <? nn)
        then let '(xa, _, _, _) := List.nth j (hd_rows h) row0 in xa
        else if row =? nn then Point.x (hd_out h) else 0
    | Some 1%nat =>
        if (0 <=? row) && (row <? nn)
        then let '(_, xg, _, _) := List.nth j (hd_rows h) row0 in xg
        else 0
    | Some 2%nat =>
        if 0 <=? row then List.nth j (hd_bits h) 0 else 0
    | Some 3%nat =>
        if (0 <=? row) && (row <? nn)
        then let '(_, _, l1, _) := List.nth j (hd_rows h) row0 in l1
        else if row =? nn then Point.y (hd_out h) else 0
    | Some 4%nat =>
        if (0 <=? row) && (row <? nn)
        then let '(_, _, _, l2) := List.nth j (hd_rows h) row0 in l2
        else 0
    | _ => 0
    end.

  (** ** Merkle layer data

      Per layer: the running node before the layer and the layer's hash-region
      data; the sibling, the position bit and the [b]-piece halves are cheap
      reads off the input and the stored words. *)
  Record layer_data : Set := {
    lyd_node : Z;
    lyd_hash : hash_data;
  }.

  Definition layer0 : layer_data := {|
    lyd_node := 0;
    lyd_hash := {| hd_rows := []; hd_out := point0; hd_bits := [];
                   hd_words := [] |};
  |}.

  Definition merkle_words_at (w : HonestInput) (node : Z) (i : nat)
      : list Z :=
    let sibling := List.nth i (hi_path w) 0 in
    if path_bit w i
    then SinsemillaSpec.merkle_message (Z.of_nat i) sibling node
    else SinsemillaSpec.merkle_message (Z.of_nat i) node sibling.

  Fixpoint layers_go (w : HonestInput) (node : Z) (i count : nat)
      : list layer_data :=
    match count with
    | O => []
    | S count' =>
        let h := hash_data_of merkle_Q
          (OrchardAdviceMerkleSinsemilla.split_pieces
            OrchardAdviceMerkleSinsemilla.merkle_lens
            (merkle_words_at w node i)) in
        {| lyd_node := node; lyd_hash := h |}
          :: layers_go w (Point.x (hd_out h)) (S i) count'
    end.

  Definition layers_of (w : HonestInput) (leaf : Z) : list layer_data :=
    layers_go w leaf 0%nat 32%nat.

  Definition anchor_of (layers : list layer_data) (leaf : Z) : Z :=
    match List.rev layers with
    | [] => leaf
    | l :: _ => Point.x (hd_out (lyd_hash l))
    end.

  (** ** Fixed-base leg data

      Per window: the window point (x from Lagrange interpolation, y recovered
      from the pasted square root), and the incomplete-addition accumulator
      threaded low-window-first — the [fb_window_point]/[fb_acc] values of
      [OrchardAdviceEccMuls] with the accumulator fold paid once. *)
  Record leg_data : Set := {
    lg_px : list Z;
    lg_py : list Z;
    lg_ax : list Z;
    lg_ay : list Z;
    lg_us : list Z;
  }.

  (** The square-root witness of window [i] at scalar digit [d]: the pasted
      root of [fw_z + y] from the window-sign certificate's [root_table]. *)
  Definition roots_us (roots : list (list Z)) (scalar : Z) (count : nat)
      : list Z :=
    List.map
      (fun i =>
        List.nth (Z.to_nat (EccSpec.window_digit scalar i))
          (List.nth i roots []) 0)
      (List.seq 0%nat count).

  Fixpoint accs_go (prev : Point.t) (pts : list Point.t) : list Point.t :=
    match pts with
    | [] => []
    | p :: ps =>
        let nxt := EccSpec.point_add_incomplete p prev in
        nxt :: accs_go nxt ps
    end.

  Definition leg_of (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (scalar : Z) : leg_data :=
    let count := List.length tbl in
    let us := roots_us roots scalar count in
    let pts :=
      List.map
        (fun i =>
          EccSpec.fixed_window_point
            (List.nth i tbl OrchardAdviceEccMuls.dummy_window)
            (EccSpec.window_digit scalar i)
            (List.nth i us 0))
        (List.seq 0%nat count) in
    let accs :=
      match pts with
      | [] => []
      | p0 :: ps => p0 :: accs_go p0 ps
      end in
    {|
      lg_px := List.map Point.x pts;
      lg_py := List.map Point.y pts;
      lg_ax := List.map Point.x accs;
      lg_ay := List.map Point.y accs;
      lg_us := us;
    |}.

  Definition leg_pt (l : leg_data) (i : nat) : Point.t := {|
    Point.x := List.nth i (lg_px l) 0;
    Point.y := List.nth i (lg_py l) 0;
  |}.

  Definition leg_acc (l : leg_data) (i : nat) : Point.t := {|
    Point.x := List.nth i (lg_ax l) 0;
    Point.y := List.nth i (lg_ay l) 0;
  |}.

  (** The full-width incomplete-region reader ([fb_full_advice] semantics). *)
  Definition fb_full_advice_t (l : leg_data) (scalar : Z) (count : Z)
      (column : Advice.t) (offset : Z) : Z :=
    if (0 <=? offset) && (offset <? count) then
      let i := Z.to_nat offset in
      match column with
      | A0 => List.nth i (lg_px l) 0
      | A1 => List.nth i (lg_py l) 0
      | A4 => EccSpec.window_digit scalar i
      | A5 => List.nth i (lg_us l) 0
      | A2 => if 1 <=? offset then List.nth (i - 1) (lg_ax l) 0 else 0
      | A3 => if 1 <=? offset then List.nth (i - 1) (lg_ay l) 0 else 0
      | _ => 0
      end
    else 0.

  (** The short incomplete-region reader ([fb_short_advice] semantics: [A4]
      is the base-8 running sum over rows [0 .. count]). *)
  Definition fb_short_advice_t (l : leg_data) (scalar : Z) (count : Z)
      (column : Advice.t) (offset : Z) : Z :=
    match column with
    | A4 =>
        if (0 <=? offset) && (offset <=? count) then scalar / 8 ^ offset else 0
    | _ =>
        if (0 <=? offset) && (offset <? count) then
          let i := Z.to_nat offset in
          match column with
          | A0 => List.nth i (lg_px l) 0
          | A1 => List.nth i (lg_py l) 0
          | A5 => List.nth i (lg_us l) 0
          | A2 => if 1 <=? offset then List.nth (i - 1) (lg_ax l) 0 else 0
          | A3 => if 1 <=? offset then List.nth (i - 1) (lg_ay l) 0 else 0
          | _ => 0
          end
        else 0
    end.

  (** ** Poseidon round states *)
  Fixpoint states_go (s : State.t) (row count : nat) : list State.t :=
    match count with
    | O => [s]
    | S count' => s :: states_go (poseidon_round row s) (S row) count'
    end.

  (** The 37 row states of the permutation region ([poseidon_round_state w n]
      for [n = 0 .. 36]). *)
  Definition pose_states_of (w : HonestInput) : list State.t :=
    states_go (poseidon_input_state w) 0%nat 36%nat.

  (** ** The hoisted table record

      Everything the advice and instance readers consume, computed once per
      [vm_compute] run: the note-commitment/[Commit^ivk] hash regions, the
      old-note commitment and the anchor chain, the six fixed-base legs and
      their derived sums, the Poseidon schedule, the nullifier chain and the
      variable-base ladder record, plus the public-instance values. *)
  Record t : Set := {
    (* Old note commitment and the Merkle chain. *)
    t_nc_old_hash : hash_data;
    t_cm_old : Point.t;
    t_layers : list layer_data;
    t_anchor : Z;
    (* Poseidon and the nullifier chain. *)
    t_pose : list State.t;
    t_hash2 : Z;
    t_nullifier_scalar : Z;
    t_nk_leg : leg_data;
    t_nk_prod : Point.t;
    t_nf_pt : Point.t;
    t_nf_spec : Z;
    (* New note commitment. *)
    t_nc_new_hash : hash_data;
    t_cmx_spec : Z;
    (* Commit^ivk and the variable-base scalar. *)
    t_civk_hash : hash_data;
    t_civkr_leg : leg_data;
    t_civkr_pt : Point.t;
    t_ivk : Z;
    t_vb_result : Point.t;
    t_vb : OrchardVarBaseTables.t;
    (* Fixed-base legs and their derived points. *)
    t_sa_leg : leg_data;
    t_sa_comm : Point.t;
    t_rk_pt : Point.t;
    t_vcr_leg : leg_data;
    t_vcr_pt : Point.t;
    t_vcv_leg : leg_data;
    t_vcv_mul : Point.t;
    t_nco_leg : leg_data;
    t_nco_pt : Point.t;
    t_ncn_leg : leg_data;
    t_ncn_pt : Point.t;
    (* Public-instance values. *)
    t_anchor_row : Z;
    t_cv_spec : Point.t;
    t_rk_spec : Point.t;
  }.

  Definition tables_of (w : HonestInput) : t :=
    (* Old note commitment: the hash region and the blinded commitment. *)
    let nc_old_hash :=
      hash_data_of (OrchardAdviceMerkleSinsemilla.note_commit_Q)
        (OrchardAdviceMerkleSinsemilla.split_pieces
          OrchardAdviceMerkleSinsemilla.note_commit_lens
          (note_commit_old_words w)) in
    let cm_old_pt :=
      EccSpec.point_add (hd_out nc_old_hash)
        (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)) in
    (* The 32 Merkle layers from the leaf. *)
    let layers := layers_of w (Point.x cm_old_pt) in
    let anchor := anchor_of layers (Point.x cm_old_pt) in
    (* Poseidon schedule and the nullifier scalar. *)
    let pose := pose_states_of w in
    let hash2 := State.x0 (List.nth 36 pose state0) in
    let nscalar := hash2 +F hi_psi_old w in
    (* The NullifierK base-field leg and the nullifier point. *)
    let nk_leg :=
      leg_of OrchardAdvicePoseidonNullifier.nk_table
        NullifierKWindowSignCert.root_table nscalar in
    let nk_prod :=
      EccSpec.point_add (leg_pt nk_leg 84%nat) (leg_acc nk_leg 83%nat) in
    let nf_pt := EccSpec.point_add cm_old_pt nk_prod in
    let nf_spec :=
      EccSpec.extract_x
        (EccSpec.point_add
          (OrchardProtocolSpec.mul_nullifier_k nscalar) cm_old_pt) in
    (* New note commitment ([ρ_new] = the nullifier). *)
    let nc_new_hash :=
      hash_data_of (OrchardAdviceMerkleSinsemilla.note_commit_Q)
        (OrchardAdviceMerkleSinsemilla.split_pieces
          OrchardAdviceMerkleSinsemilla.note_commit_lens
          (OrchardSpec.note_commit_message (hi_g_d_new w) (hi_pk_d_new w)
            (hi_v_new w) nf_spec (hi_psi_new w))) in
    let cmx :=
      EccSpec.extract_x
        (EccSpec.point_add (hd_out nc_new_hash)
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_new w))) in
    (* Commit^ivk and the variable-base multiplication result. *)
    let civk_hash :=
      hash_data_of (OrchardAdviceMerkleSinsemilla.commit_ivk_Q)
        (OrchardAdviceMerkleSinsemilla.split_pieces
          OrchardAdviceMerkleSinsemilla.commit_ivk_lens
          (commit_ivk_words w)) in
    let civkr_leg :=
      leg_of (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        CommitIvkRWindowSignCert.root_table (hi_rivk w) in
    let civkr_pt :=
      EccSpec.point_add (leg_pt civkr_leg 84%nat) (leg_acc civkr_leg 83%nat) in
    let ivk_v :=
      EccSpec.extract_x
        (EccSpec.point_add (hd_out civk_hash)
          (OrchardProtocolSpec.mul_commit_ivk_r (hi_rivk w))) in
    let vb_res :=
      PallasModel.repr
        (Pallas.mul ivk_v (PallasModel.unrepr (hi_g_d_old w))) in
    let vb := OrchardVarBaseTables.vb_columns ivk_v (hi_g_d_old w) in
    (* The five remaining fixed-base legs and the derived leg sums. *)
    let sa_leg :=
      leg_of OrchardAdviceEccMuls.tbl_spend_auth
        SpendAuthGWindowSignCert.root_table (hi_alpha w) in
    let sa_comm :=
      EccSpec.point_add (leg_pt sa_leg 84%nat) (leg_acc sa_leg 83%nat) in
    let rk_pt := EccSpec.point_add sa_comm (hi_ak w) in
    let vcr_leg :=
      leg_of OrchardAdviceEccMuls.tbl_value_commit_r
        ValueCommitRWindowSignCert.root_table (hi_rcv w) in
    let vcr_pt :=
      EccSpec.point_add (leg_pt vcr_leg 84%nat) (leg_acc vcr_leg 83%nat) in
    let vcv_leg :=
      leg_of OrchardAdviceEccMuls.tbl_value_commit_v
        ValueCommitVWindowSignCert.root_table (magnitude w) in
    let vcv_mul :=
      EccSpec.point_add (leg_pt vcv_leg 21%nat) (leg_acc vcv_leg 20%nat) in
    let nco_leg :=
      leg_of OrchardAdviceEccMuls.tbl_note_commit_r
        NoteCommitRWindowSignCert.root_table (hi_rcm_old w) in
    let nco_pt :=
      EccSpec.point_add (leg_pt nco_leg 84%nat) (leg_acc nco_leg 83%nat) in
    let ncn_leg :=
      leg_of OrchardAdviceEccMuls.tbl_note_commit_r
        NoteCommitRWindowSignCert.root_table (hi_rcm_new w) in
    let ncn_pt :=
      EccSpec.point_add (leg_pt ncn_leg 84%nat) (leg_acc ncn_leg 83%nat) in
    (* The public-instance values. *)
    let anchor_row :=
      if hi_v_old w =? 0 then hi_anchor_public w else anchor in
    let cv :=
      OrchardProtocolSpec.value_commit
        (OrchardProtocolSpec.signed_net_value (magnitude w) (sign w))
        (hi_rcv w) in
    let rk_spec :=
      OrchardProtocolSpec.spend_auth_randomize (hi_ak w) (hi_alpha w) in
    {|
      t_nc_old_hash := nc_old_hash;
      t_cm_old := cm_old_pt;
      t_layers := layers;
      t_anchor := anchor;
      t_pose := pose;
      t_hash2 := hash2;
      t_nullifier_scalar := nscalar;
      t_nk_leg := nk_leg;
      t_nk_prod := nk_prod;
      t_nf_pt := nf_pt;
      t_nf_spec := nf_spec;
      t_nc_new_hash := nc_new_hash;
      t_cmx_spec := cmx;
      t_civk_hash := civk_hash;
      t_civkr_leg := civkr_leg;
      t_civkr_pt := civkr_pt;
      t_ivk := ivk_v;
      t_vb_result := vb_res;
      t_vb := vb;
      t_sa_leg := sa_leg;
      t_sa_comm := sa_comm;
      t_rk_pt := rk_pt;
      t_vcr_leg := vcr_leg;
      t_vcr_pt := vcr_pt;
      t_vcv_leg := vcv_leg;
      t_vcv_mul := vcv_mul;
      t_nco_leg := nco_leg;
      t_nco_pt := nco_pt;
      t_ncn_leg := ncn_leg;
      t_ncn_pt := ncn_pt;
      t_anchor_row := anchor_row;
      t_cv_spec := cv;
      t_rk_spec := rk_spec;
    |}.

  (** ** Region readers over the tables

      Each reader mirrors the corresponding [advice_*] sub-generator with the
      heavy derivations replaced by table lookups. *)

  (** The [WitnessInput] regions ([witness_input_advice] semantics). *)
  Definition witness_input_advice_t (w : HonestInput) (tb : t)
      (column : Advice.t) (region : RegionId.WitnessInput.t) (row : Z) : Z :=
    if row =? 0 then
      match region, column with
      | RegionId.WitnessInput.PsiOld, A0 => hi_psi_old w
      | RegionId.WitnessInput.RhoOld, A0 => hi_rho_old w
      | RegionId.WitnessInput.CmOld, A0 => Point.x (t_cm_old tb)
      | RegionId.WitnessInput.CmOld, A1 => Point.y (t_cm_old tb)
      | RegionId.WitnessInput.GDOld, A0 => Point.x (hi_g_d_old w)
      | RegionId.WitnessInput.GDOld, A1 => Point.y (hi_g_d_old w)
      | RegionId.WitnessInput.AkP, A0 => Point.x (hi_ak w)
      | RegionId.WitnessInput.AkP, A1 => Point.y (hi_ak w)
      | RegionId.WitnessInput.Nk, A0 => hi_nk w
      | RegionId.WitnessInput.VOld, A0 => hi_v_old w
      | RegionId.WitnessInput.VNew, A0 => hi_v_new w
      | _, _ => 0
      end
    else 0.

  (** The [OrchardCircuitChecks] copy row ([orchard_checks_advice]
      semantics; the root/anchor cells read the hoisted anchor chain). *)
  Definition orchard_checks_advice_t (w : HonestInput) (tb : t)
      (column : Advice.t) (row : Z) : Z :=
    if row =? 0 then
      match column with
      | A0 => hi_v_old w
      | A1 => hi_v_new w
      | A2 => magnitude w
      | A3 => sign w
      | A4 => t_anchor tb
      | A5 => t_anchor_row tb
      | A6 => hi_enable_spends w
      | A7 => hi_enable_outputs w
      | _ => 0
      end
    else 0.

  (** The Merkle regions (the per-layer readers of
      [OrchardAdviceMerkleSinsemilla] over [layer_data]). *)
  Definition merkle_advice_t (w : HonestInput) (tb : t)
      (col : Advice.t) (layer : RegionId.Merkle.Layer.t)
      (mregion : RegionId.Merkle.Region.t) (row : Z) : Z :=
    let i := Z.to_nat (RegionId.Merkle.Layer.to_index layer) in
    let second := negb (RegionId.Merkle.Layer.to_index layer <? 16) in
    let ld := List.nth i (t_layers tb) layer0 in
    let node := lyd_node ld in
    let sibling := List.nth i (hi_path w) 0 in
    let bit := path_bit w i in
    let left := if bit then sibling else node in
    let right := if bit then node else sibling in
    let bits := hd_bits (lyd_hash ld) in
    let b_word := List.nth 26 (hd_words (lyd_hash ld)) 0 in
    let b1 := b_word mod 2 ^ 5 in
    let b2 := b_word / 2 ^ 5 in
    match mregion with
    | RegionId.Merkle.Region.NodePosition =>
        if row =? 0 then
          match second, col with
          | false, A0 => node
          | false, A1 => sibling
          | false, A2 => left
          | false, A3 => right
          | false, A4 => if bit then 1 else 0
          | true, A5 => node
          | true, A6 => sibling
          | true, A7 => left
          | true, A8 => right
          | true, A9 => if bit then 1 else 0
          | _, _ => 0
          end
        else 0
    | RegionId.Merkle.Region.HashToPoint =>
        hash_region_advice_t (lyd_hash ld) second col row
    | RegionId.Merkle.Region.Decomposition =>
        match OrchardAdviceMerkleSinsemilla.logical_col second col, row with
        | Some 0%nat, 0 => List.nth 0 bits 0
        | Some 0%nat, 1 => List.nth 1 bits 0
        | Some 1%nat, 0 => List.nth 25 bits 0
        | Some 1%nat, 1 => List.nth 26 bits 0
        | Some 2%nat, 0 => List.nth 27 bits 0
        | Some 2%nat, 1 => b1
        | Some 3%nat, 0 => left
        | Some 3%nat, 1 => b2
        | Some 4%nat, 0 => right
        | Some 4%nat, 1 => Z.of_nat i
        | _, _ => 0
        end
    | RegionId.Merkle.Region.WitnessA =>
        if OrchardAdviceMerkleSinsemilla.advice_eqb col
             (OrchardAdviceMerkleSinsemilla.merkle_witness_col second)
           && (row =? 0)
        then List.nth 0 bits 0 else 0
    | RegionId.Merkle.Region.WitnessB =>
        if OrchardAdviceMerkleSinsemilla.advice_eqb col
             (OrchardAdviceMerkleSinsemilla.merkle_witness_col second)
           && (row =? 0)
        then List.nth 25 bits 0 else 0
    | RegionId.Merkle.Region.WitnessC =>
        if OrchardAdviceMerkleSinsemilla.advice_eqb col
             (OrchardAdviceMerkleSinsemilla.merkle_witness_col second)
           && (row =? 0)
        then List.nth 27 bits 0 else 0
    (* Short 5-bit range checks ([synthesize_short]): the checked value at
       row 0, the bitshifted word [value · 2^5] at row 1, and the pinned
       constant [inv_two_pow_5] at row 2 (the [q_bitshift] gate reads
       [word · 2^10 · inv_two_pow_5 = shifted]). *)
    | RegionId.Merkle.Region.RangeB1 =>
        match col, row with
        | A9, 0 => b1
        | A9, 1 => b1 * 2 ^ 5
        | A9, 2 => Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5
        | _, _ => 0
        end
    | RegionId.Merkle.Region.RangeB2 =>
        match col, row with
        | A9, 0 => b2
        | A9, 1 => b2 * 2 ^ 5
        | A9, 2 => Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5
        | _, _ => 0
        end
    end.

  (** The Poseidon regions ([advice_poseidon] semantics over the hoisted
      round-state list). *)
  Definition pose_state_t (tb : t) (n : nat) : State.t :=
    List.nth n (t_pose tb) state0.

  Definition poseidon_mid_t (tb : t) (row : nat) : Z :=
    OrchardAdvicePoseidonNullifier.pow5_field
      (State.x0 (pose_state_t tb row)
        +F Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant
             (2 * row - 4)%nat 0%nat).

  Definition advice_poseidon_t (w : HonestInput) (tb : t)
      (col : Advice.t) (region : RegionId.Poseidon.t) (off : Z) : Z :=
    match region with
    | RegionId.Poseidon.InitialState =>
        if off =? 0 then
          match col with
          | A6 => 0
          | A7 => 0
          | A8 => 2 ^ 65
          | _ => 0
          end
        else 0
    | RegionId.Poseidon.AddInput =>
        if off =? 0 then
          match col with
          | A6 => 0
          | A7 => 0
          | A8 => 2 ^ 65
          | _ => 0
          end
        else if off =? 1 then
          match col with
          | A6 => hi_nk w
          | A7 => hi_rho_old w
          | _ => 0
          end
        else if off =? 2 then
          match col with
          | A6 => hi_nk w
          | A7 => hi_rho_old w
          | A8 => 2 ^ 65
          | _ => 0
          end
        else 0
    | RegionId.Poseidon.PermuteState =>
        if (0 <=? off) && (off <=? 36) then
          let n := Z.to_nat off in
          match col with
          | A6 => State.x0 (pose_state_t tb n)
          | A7 => State.x1 (pose_state_t tb n)
          | A8 => State.x2 (pose_state_t tb n)
          | A5 =>
              if (4 <=? off) && (off <=? 31) then poseidon_mid_t tb n else 0
          | _ => 0
          end
        else 0
    | _ => 0
    end.

  (** The nullifier chain ([advice_nullifier] semantics; the complete
      addition of the commitment carries the full [cadd_advice] witness
      row, the [inv0] formulas included). *)
  Definition advice_nullifier_t (w : HonestInput) (tb : t)
      (col : Advice.t) (region : RegionId.Nullifier.t) (off : Z) : Z :=
    let nscalar := t_nullifier_scalar tb in
    let z84 := running_sum_at nscalar 84%nat in
    let alpha_0 := nscalar - z84 * 2 ^ 252 in
    let alpha_0_prime := (alpha_0 + 2 ^ 130 - Primes.t_p) mod Primes.pallas_p in
    match region with
    | RegionId.Nullifier.ScalarAdd =>
        if off =? 0 then
          match col with
          | A6 => nscalar
          | A7 => t_hash2 tb
          | A8 => hi_psi_old w
          | _ => 0
          end
        else 0
    | RegionId.Nullifier.BaseFieldIncomplete =>
        match col with
        | A0 =>
            if (0 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off) (lg_px (t_nk_leg tb)) 0 else 0
        | A1 =>
            if (0 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off) (lg_py (t_nk_leg tb)) 0 else 0
        | A2 =>
            if (1 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off - 1) (lg_ax (t_nk_leg tb)) 0 else 0
        | A3 =>
            if (1 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off - 1) (lg_ay (t_nk_leg tb)) 0 else 0
        | A4 =>
            if (0 <=? off) && (off <=? 85)
            then running_sum_at nscalar (Z.to_nat off) else 0
        | A5 =>
            if (0 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off) (lg_us (t_nk_leg tb)) 0 else 0
        | _ => 0
        end
    | RegionId.Nullifier.BaseFieldComplete =>
        (* [synth_base_field_mul_complete]: a complete addition of the top
           window into the incomplete fold, with the full [assign_complete_add]
           witness row ([QEccAdd]). *)
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_nk_leg tb) 84%nat) (leg_acc (t_nk_leg tb) 83%nat)
          col off
    | RegionId.Nullifier.AlphaLookup =>
        match col with
        | A9 =>
            if (0 <=? off) && (off <=? 13)
            then alpha_0_prime / 2 ^ (10 * off) else 0
        | _ => 0
        end
    | RegionId.Nullifier.CanonicityChecks =>
        match col with
        | A6 =>
            if off =? 0 then nscalar
            else if off =? 1 then alpha_0_prime
            else if off =? 2 then alpha_0_prime / 2 ^ 130
            else 0
        | A7 =>
            if off =? 1 then z84 mod 4
            else if off =? 2 then running_sum_at nscalar 44%nat
            else 0
        | A8 =>
            if off =? 0 then z84
            else if off =? 1 then z84 / 4
            else if off =? 2 then running_sum_at nscalar 43%nat
            else 0
        | _ => 0
        end
    | RegionId.Nullifier.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice (t_cm_old tb) (t_nk_prod tb) col off
    end.

  (** The ECC scalar-multiplication regions ([OrchardAdviceEccMuls.advice]
      semantics over the hoisted legs and points). *)
  Definition vcv_y_var_t (w : HonestInput) (tb : t) : Z :=
    if sign w =? 1
    then Point.y (t_vcv_mul tb)
    else 0 -F Point.y (t_vcv_mul tb).

  Definition vcv_point_t (w : HonestInput) (tb : t) : Point.t := {|
    Point.x := Point.x (t_vcv_mul tb);
    Point.y := vcv_y_var_t w tb;
  |}.

  Definition advice_ecc_t (w : HonestInput) (tb : t)
      (column : Advice.t) (region : RegionId.t) (offset : Z) : Z :=
    match region with
    | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete =>
        fb_full_advice_t (t_sa_leg tb) (hi_alpha w) 85 column offset
    | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast =>
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_sa_leg tb) 84%nat) (leg_acc (t_sa_leg tb) 83%nat)
          column offset
    | RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice (t_sa_comm tb) (hi_ak w)
          column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck =>
        if OrchardAdviceEccMuls.is_A9 column && (offset =? 0)
        then magnitude w else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck =>
        if OrchardAdviceEccMuls.is_A9 column && (offset =? 0)
        then sign w else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete =>
        fb_short_advice_t (t_vcv_leg tb) (magnitude w) 22 column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb =>
        if offset =? 0 then
          OrchardAdviceEccMuls.cadd_advice
            (leg_pt (t_vcv_leg tb) 21%nat) (leg_acc (t_vcv_leg tb) 20%nat)
            column 0
        else if offset =? 1 then
          match column with
          | A1 => vcv_y_var_t w tb
          | A2 => Point.x (t_vcv_mul tb)
          | A3 => Point.y (t_vcv_mul tb)
          | A4 => sign w
          | A5 => magnitude w / 8 ^ 21
          | _ => 0
          end
        else 0
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete =>
        fb_full_advice_t (t_vcr_leg tb) (hi_rcv w) 85 column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast =>
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_vcr_leg tb) 84%nat) (leg_acc (t_vcr_leg tb) 83%nat)
          column offset
    | RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice (vcv_point_t w tb) (t_vcr_pt tb)
          column offset
    (* The variable-base multiplication block ([[ivk] g_d_old]): the 137-row
       double-and-add ladder and the three overflow-check regions, read off
       the hoisted ladder record ([OrchardVarBaseTables]). *)
    | RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul sub) =>
        OrchardVarBaseTables.mul_advice_of (t_ivk tb) (hi_g_d_old w)
          (t_vb tb) sub column offset
    | RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD =>
        if offset =? 0 then
          match column with
          | A0 => Point.x (t_vb_result tb)
          | A1 => Point.y (t_vb_result tb)
          | _ => 0
          end
        else 0
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.FixedBaseIncomplete =>
        fb_full_advice_t (t_nco_leg tb) (hi_rcm_old w) 85 column offset
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete =>
        fb_full_advice_t (t_ncn_leg tb) (hi_rcm_new w) 85 column offset
    | _ => 0
    end.

  (** ** The advice plane over the tables

      The total dispatcher: the same region routing as
      [OrchardHonestAssignment.advice_plane], every family reading its
      hoisted data.  The [NoteCommit]/[Commit^ivk] decomposition,
      canonicity, range-check and lookup subregions read the [tables_nc.v]
      bit-slice layer directly (per-read cost a few integer divisions); the
      variable-base multiplication block reads the hoisted ladder record of
      [tables_vb.v]. *)
  Definition advice_t (w : HonestInput) (tb : t)
      (column : Advice.t) (region : RegionId.t) (row : Z) : Z :=
    match region with
    | RegionId.WitnessInput r => witness_input_advice_t w tb column r row
    | RegionId.OrchardCircuitChecks =>
        orchard_checks_advice_t w tb column row
    | RegionId.Merkle layer mregion =>
        merkle_advice_t w tb column layer mregion row
    | RegionId.Poseidon r => advice_poseidon_t w tb column r row
    | RegionId.Nullifier r => advice_nullifier_t w tb column r row
    | RegionId.SpendAuthority _ => advice_ecc_t w tb column region row
    | RegionId.ValueCommitment _ => advice_ecc_t w tb column region row
    | RegionId.AddressIntegrity _ => advice_ecc_t w tb column region row
    | RegionId.CommitIvk RegionId.CommitIvk.HashToPoint =>
        hash_region_advice_t (t_civk_hash tb) false column row
    | RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete =>
        fb_full_advice_t (t_civkr_leg tb) (hi_rivk w) 85 column row
    | RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast =>
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_civkr_leg tb) 84%nat) (leg_acc (t_civkr_leg tb) 83%nat)
          column row
    | RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice
          (hd_out (t_civk_hash tb)) (t_civkr_pt tb) column row
    (* The witnessed message pieces, the sub-piece range checks, the
       canonicity lookup running sums and the canonicity-gate rows: the
       [tables_nc.v] bit-slice cell layer over the packed [Commit^ivk]
       message [ak_x + nk·2^255] (every read costs a few integer
       divisions, so no hoisting is needed). *)
    | RegionId.CommitIvk cregion =>
        OrchardNoteCommitCells.civk_advice
          (EccSpec.extract_x (hi_ak w)) (hi_nk w) cregion column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint =>
        hash_region_advice_t (t_nc_old_hash tb) false column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint =>
        hash_region_advice_t (t_nc_new_hash tb) true column row
    | RegionId.NoteCommit _ RegionId.NoteCommit.FixedBaseIncomplete =>
        advice_ecc_t w tb column region row
    (* The fixed-base blinding legs' final complete additions and the
       commitment sums (the [assign_complete_add] witness rows over the
       hoisted leg boundaries and hash outputs). *)
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.FixedBaseLast =>
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_nco_leg tb) 84%nat) (leg_acc (t_nco_leg tb) 83%nat)
          column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseLast =>
        OrchardAdviceEccMuls.cadd_advice
          (leg_pt (t_ncn_leg tb) 84%nat) (leg_acc (t_ncn_leg tb) 83%nat)
          column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice
          (hd_out (t_nc_old_hash tb)) (t_nco_pt tb) column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd =>
        OrchardAdviceEccMuls.cadd_advice
          (hd_out (t_nc_new_hash tb)) (t_ncn_pt tb) column row
    (* The message-piece, input-decomposition, y-canonicity, range-check
       and canonicity-lookup subregions: the [tables_nc.v] bit-slice cell
       layer over the packed §5.4.8.4 note message ([ρ_new] is the old
       note's nullifier, read from the hoisted chain). *)
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old nregion =>
        OrchardNoteCommitCells.nc_advice
          (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w)
          (hi_rho_old w) (hi_psi_old w) false nregion column row
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New nregion =>
        OrchardNoteCommitCells.nc_advice
          (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (t_nf_spec tb) (hi_psi_new w) true nregion column row
    | RegionId.NoteCommitOldEquality => 0
    | RegionId.NoteCommitNewWitnessGD =>
        if row =? 0 then
          match column with
          | A0 => Point.x (hi_g_d_new w)
          | A1 => Point.y (hi_g_d_new w)
          | _ => 0
          end
        else 0
    | RegionId.NoteCommitNewWitnessPkD =>
        if row =? 0 then
          match column with
          | A0 => Point.x (hi_pk_d_new w)
          | A1 => Point.y (hi_pk_d_new w)
          | _ => 0
          end
        else 0
    | RegionId.NoteCommitNewWitnessPsi =>
        if row =? 0 then
          match column with
          | A0 => hi_psi_new w
          | _ => 0
          end
        else 0
    | RegionId.GadgetLocal _ => 0
    end.

  (** ** The public-instance rows over the tables

      [public_instance_row] semantics: the nine §4.18.4 public rows, each a
      hoisted value. *)
  Definition instance_t (w : HonestInput) (tb : t) (row : Z) : Z :=
    match row with
    | 0 => t_anchor_row tb
    | 1 => Point.x (t_cv_spec tb)
    | 2 => Point.y (t_cv_spec tb)
    | 3 => t_nf_spec tb
    | 4 => Point.x (t_rk_spec tb)
    | 5 => Point.y (t_rk_spec tb)
    | 6 => t_cmx_spec tb
    | 7 => hi_enable_spends w
    | 8 => hi_enable_outputs w
    | _ => 0
    end.

End OrchardCompletenessTables.
