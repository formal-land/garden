(** * Forward lemma: the free-witness read-back

    The [read_back_ok] obligation of [forward/api.v] — the second conjunct of
    [OrchardWitnessInput.completeness_statement]: on every valid, nondegenerate
    honest input the free-witness readers of [circuit_proof/inputs.v]
    reproduce the input record,

    [read_action_inputs (honest_assignment w) = inputs_of w].

    This is the universal form of the concrete instance certificate
    [OrchardCompletenessInstanceRead.read_action_inputs_ok], which closes the
    same equation at one input by a single [vm_compute].  Here every reader is
    resolved symbolically instead:

    - the plane readers ([read_advice] / [read_public_instance]) project the
      generator's advice and instance planes, so each field is the hoisted
      cell value reduced modulo the Pallas prime;
    - the reduction is the identity because every honest cell is already a
      field element: the [valid] type envelope bounds the witnessed scalars
      and path entries, [point_ok] bounds the witnessed point coordinates, and
      the derived values ([cm_old], the Merkle root) end in the field
      reductions of the chord formulas;
    - the two windowed scalars and the note-commitment blinding scalar are
      reconstructed from their base-8 window cells ([sfw_digits]: the 85-window
      reconstruction inverts the window decomposition below [8^85]);
    - the Merkle path reader collects the cond-swap regions' sibling and
      position cells layer by layer;
    - the public anchor row reads the hoisted anchor chain, identified with
      the specification root [anchor_root] through the layer-chain bridge of
      [forward/sinsemilla.v].

    The derived-value identifications ([t_cm_old_of], [t_layers_nth]) and the
    coordinate-range lemmas ([padd_coords], [mul_gen_coords]) are the ones the
    sibling gate lanes already establish; this file adds the anchor read-off
    and the reader-level algebra. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Garden.Orchard.circuit_completeness.forward.canonicity.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardReadBack.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.

  Module OCT := OrchardCompletenessTables.
  Module OHA := OrchardHonestAssignment.
  Module OFS := OrchardForwardSinsemilla.
  Module OCF := OrchardCanonicityForward.

  (** ** Modulus bounds

      The three numeric facts the range side conditions consume; each is a
      constant comparison over the Pallas prime and the group order. *)

  Lemma one_lt_p : 1 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma two_64_lt_p : 2 ^ 64 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma q_lt_pow8_85 : Primes.pallas_q < 8 ^ 85.
  Proof. unfold Primes.pallas_q, Primes.t_q. lia. Qed.

  (** ** The plane readers over the generator

      [read_advice] / [read_public_instance] at the honest assignment are the
      hoisted advice and instance readers, reduced modulo the prime.  The
      current-rotation row offset is discharged by [Z.add_0_r] rather than by
      conversion, so nothing forces the hoisted record. *)

  Lemma read_advice_cell (w : HonestInput) (col : Advice.t)
      (region : RegionId.t) (row : Z) :
    read_advice (OHA.honest_assignment w) col region row =
    UnOp.from (OCT.advice_t w (OCT.tables_of w) col region row).
  Proof.
    change (read_advice (OHA.honest_assignment w) col region row)
      with (UnOp.from (OCT.advice_t w (OCT.tables_of w) col region (row + 0))).
    rewrite Z.add_0_r.
    reflexivity.
  Qed.

  Lemma read_instance_cell (w : HonestInput) (row : Z) :
    read_public_instance (OHA.honest_assignment w) row =
    UnOp.from (OCT.instance_t w (OCT.tables_of w) row).
  Proof.
    change (read_public_instance (OHA.honest_assignment w) row)
      with (UnOp.from (OCT.instance_t w (OCT.tables_of w) (row + 0))).
    rewrite Z.add_0_r.
    reflexivity.
  Qed.

  (** ** Generic reader shapes

      A cell equation plus the value's field range gives the reader's value:
      the plane read is the cell modulo the prime, and a reduced cell is its
      own residue. *)

  Lemma point_eta (P : Point.t) :
    {| Point.x := Point.x P; Point.y := Point.y P |} = P.
  Proof. reflexivity. Qed.

  Lemma read_of (w : HonestInput) (region : RegionId.t) (v : Z)
      (Hcell : OCT.advice_t w (OCT.tables_of w) Advice.A0 region 0 = v)
      (Hrange : 0 <= v < Primes.pallas_p) :
    read (OHA.honest_assignment w) region = v.
  Proof.
    unfold read. rewrite read_advice_cell, Hcell.
    unfold UnOp.from. exact (Z.mod_small _ _ Hrange).
  Qed.

  Lemma read9_of (w : HonestInput) (region : RegionId.t) (v : Z)
      (Hcell : OCT.advice_t w (OCT.tables_of w) Advice.A9 region 0 = v)
      (Hrange : 0 <= v < Primes.pallas_p) :
    read9 (OHA.honest_assignment w) region = v.
  Proof.
    unfold read9. rewrite read_advice_cell, Hcell.
    unfold UnOp.from. exact (Z.mod_small _ _ Hrange).
  Qed.

  Lemma read_point_of (w : HonestInput) (region : RegionId.t) (P : Point.t)
      (Hx : OCT.advice_t w (OCT.tables_of w) Advice.A0 region 0 = Point.x P)
      (Hy : OCT.advice_t w (OCT.tables_of w) Advice.A1 region 0 = Point.y P)
      (Hxr : 0 <= Point.x P < Primes.pallas_p)
      (Hyr : 0 <= Point.y P < Primes.pallas_p) :
    read_point (OHA.honest_assignment w) region = P.
  Proof.
    unfold read_point, read, read1.
    rewrite !read_advice_cell, Hx, Hy.
    unfold UnOp.from.
    rewrite (Z.mod_small _ _ Hxr), (Z.mod_small _ _ Hyr).
    exact (point_eta P).
  Qed.

  (** ** Coordinate ranges of the derived points

      Both chord formulas end in a field reduction, so every incomplete
      addition — and therefore every Sinsemilla accumulator past the domain
      point — has reduced coordinates. *)

  Lemma padd_inc_coords (P Q : Point.t) :
    0 <= Point.x (EccSpec.point_add_incomplete P Q) < Primes.pallas_p /\
    0 <= Point.y (EccSpec.point_add_incomplete P Q) < Primes.pallas_p.
  Proof.
    split; [rewrite OFS.padd_x | rewrite OFS.padd_y];
      apply OFS.binop_sub_reduced.
  Qed.

  Lemma round_coords (Q : Point.t) (wd : Z) :
    0 <= Point.x (SinsemillaSpec.round Q wd) < Primes.pallas_p /\
    0 <= Point.y (SinsemillaSpec.round Q wd) < Primes.pallas_p.
  Proof. unfold SinsemillaSpec.round. apply padd_inc_coords. Qed.

  Lemma s2p_cons (Q : Point.t) (wd : Z) (ws : list Z) :
    SinsemillaSpec.sinsemilla_hash_to_point Q (wd :: ws) =
    SinsemillaSpec.sinsemilla_hash_to_point (SinsemillaSpec.round Q wd) ws.
  Proof. reflexivity. Qed.

  (** The fold is peeled word by word through [s2p_cons]; unfolding the fold
      and letting the induction hypothesis be matched up to conversion instead
      costs a minute at [Qed] ([docs/compile-performance.md]). *)
  Lemma s2p_coords (ws : list Z) :
    forall Q : Point.t,
      0 <= Point.x Q < Primes.pallas_p ->
      0 <= Point.y Q < Primes.pallas_p ->
      0 <= Point.x (SinsemillaSpec.sinsemilla_hash_to_point Q ws)
        < Primes.pallas_p /\
      0 <= Point.y (SinsemillaSpec.sinsemilla_hash_to_point Q ws)
        < Primes.pallas_p.
  Proof.
    induction ws as [| wd ws IH]; intros Q Hx Hy.
    - split; assumption.
    - rewrite s2p_cons.
      destruct (round_coords Q wd) as [H1 H2].
      exact (IH _ H1 H2).
  Qed.

  Lemma red_of_bool (P : Point.t) :
    (0 <=? Point.x P) && (Point.x P <? Primes.pallas_p) &&
    (0 <=? Point.y P) && (Point.y P <? Primes.pallas_p) = true ->
    0 <= Point.x P < Primes.pallas_p /\ 0 <= Point.y P < Primes.pallas_p.
  Proof.
    intros H.
    rewrite !andb_true_iff in H.
    destruct H as (((H1 & H2) & H3) & H4).
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    auto.
  Qed.

  Lemma cm_old_coords (w : HonestInput) :
    0 <= Point.x (cm_old w) < Primes.pallas_p /\
    0 <= Point.y (cm_old w) < Primes.pallas_p.
  Proof.
    unfold cm_old, OrchardProtocolSpec.note_commit,
      OrchardProtocolSpec.mul_note_commit_r.
    destruct (red_of_bool _ OFS.nc_Q_reduced) as [HQx HQy].
    destruct (s2p_coords
      (OrchardSpec.note_commit_message (hi_g_d_old w) (hi_pk_d_old w)
        (hi_v_old w) (hi_rho_old w) (hi_psi_old w)) _ HQx HQy) as [H1 H2].
    destruct (OCF.mul_gen_coords (hi_rcm_old w)
      PallasGenerators.note_commit_r_G PallasGenerators.note_commit_r_reduced)
      as [H3 H4].
    exact (OCF.padd_coords _ _ H1 H2 H3 H4).
  Qed.

  (** ** The anchor chain

      The hoisted layer list is the specification Merkle fold, so the record's
      anchor field is the root [anchor_root] and lies below the prime. *)

  Lemma t_anchor_def (w : HonestInput) :
    OCT.t_anchor (OCT.tables_of w) =
    OCT.anchor_of (OCT.t_layers (OCT.tables_of w))
      (Point.x (OCT.t_cm_old (OCT.tables_of w))).
  Proof.
    cbn [OCT.tables_of OCT.t_anchor OCT.t_layers OCT.t_cm_old]. reflexivity.
  Qed.

  Lemma t_anchor_row_def (w : HonestInput) :
    OCT.t_anchor_row (OCT.tables_of w) =
    (if hi_v_old w =? 0 then hi_anchor_public w
     else OCT.t_anchor (OCT.tables_of w)).
  Proof.
    cbn [OCT.tables_of OCT.t_anchor_row OCT.t_anchor]. reflexivity.
  Qed.

  Lemma layers_go_length (w : HonestInput) :
    forall (count : nat) (node : Z) (i : nat),
      List.length (OCT.layers_go w node i count) = count.
  Proof.
    induction count as [| count IH]; intros node i;
      cbn [OCT.layers_go List.length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma t_layers_length (w : HonestInput) :
    List.length (OCT.t_layers (OCT.tables_of w)) = 32%nat.
  Proof.
    cbn [OCT.tables_of OCT.t_layers].
    unfold OCT.layers_of.
    apply layers_go_length.
  Qed.

  Lemma anchor_of_last (layers : list OCT.layer_data) (lf : Z) (n : nat) :
    List.length layers = S n ->
    OCT.anchor_of layers lf =
    Point.x (OCT.hd_out (OCT.lyd_hash (List.nth n layers OCT.layer0))).
  Proof.
    intros Hlen.
    assert (Hne : layers <> []).
    { intros Hnil. rewrite Hnil in Hlen. cbn in Hlen. lia. }
    destruct (List.exists_last Hne) as (l' & a & Heq).
    subst layers.
    rewrite List.length_app in Hlen. cbn [List.length] in Hlen.
    assert (Hn : List.length l' = n) by lia.
    unfold OCT.anchor_of.
    rewrite List.rev_app_distr. cbn [List.rev List.app].
    rewrite <- Hn, List.nth_middle.
    reflexivity.
  Qed.

  Lemma path_of_length (w : HonestInput) :
    List.length (path_of w) = 32%nat.
  Proof.
    unfold path_of. rewrite List.length_map, List.length_seq. reflexivity.
  Qed.

  Lemma merkle_node_32 (w : HonestInput) :
    merkle_node w 32%nat = anchor_root w.
  Proof.
    unfold merkle_node, anchor_root, anchor_of_leaf, OrchardSpec.anchor.
    rewrite List.firstn_all2 by (rewrite path_of_length; lia).
    reflexivity.
  Qed.

  Lemma anchor_root_eq (w : HonestInput) :
    anchor_root w =
    Point.x (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
      (merkle_layer_words w 31%nat)).
  Proof.
    rewrite <- merkle_node_32.
    rewrite (merkle_node_succ w 31%nat ltac:(lia)).
    rewrite merkle_layer_words_spec.
    reflexivity.
  Qed.

  Lemma anchor_root_range (w : HonestInput) :
    0 <= anchor_root w < Primes.pallas_p.
  Proof.
    rewrite anchor_root_eq.
    destruct (red_of_bool merkle_Q OFS.merkle_Q_reduced) as [HQx HQy].
    exact (proj1 (s2p_coords _ merkle_Q HQx HQy)).
  Qed.

  Lemma t_anchor_root (w : HonestInput) :
    OCT.t_anchor (OCT.tables_of w) = anchor_root w.
  Proof.
    rewrite t_anchor_def.
    rewrite (anchor_of_last _ _ 31%nat (t_layers_length w)).
    rewrite (OFS.t_layers_nth w 31%nat ltac:(lia)).
    cbn [OFS.merkle_layer_data OCT.lyd_hash].
    rewrite OFS.hd_out_of, OFS.merkle_words_concat.
    exact (eq_sym (anchor_root_eq w)).
  Qed.

  (** ** The base-8 window reconstruction

      Each full-width fixed-base region witnesses its scalar as 85 base-8
      window digits on [A4]; the reader's [scalar_from_windows] inverts that
      decomposition for every scalar below [8^85]. *)

  Lemma window_digit_range (k : Z) (i : nat) :
    0 <= EccSpec.window_digit k i < 8.
  Proof. unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia. Qed.

  Lemma sfw_digits (count : nat) :
    forall k : Z,
      0 <= k < 8 ^ Z.of_nat count ->
      scalar_from_windows
        (List.map (fun i => EccSpec.window_digit k i)
          (List.seq 0%nat count)) = k.
  Proof.
    induction count as [| count IH]; intros k Hk.
    - cbn [List.seq List.map]. unfold scalar_from_windows.
      cbn [scalar_from_windows_aux]. cbn [Z.of_nat] in Hk. lia.
    - cbn [List.seq List.map].
      rewrite scalar_from_windows_cons.
      replace (List.map (fun i => EccSpec.window_digit k i) (List.seq 1 count))
        with (List.map (fun i => EccSpec.window_digit (k / 8) i)
                (List.seq 0 count)).
      2:{ rewrite <- List.seq_shift, List.map_map.
          apply List.map_ext. intros i.
          unfold EccSpec.window_digit.
          rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
          assert (Hp : 0 < 8 ^ Z.of_nat i) by (apply Z.pow_pos_nonneg; lia).
          rewrite !Z.div_div by lia.
          rewrite (Z.mul_comm 8 (8 ^ Z.of_nat i)).
          reflexivity. }
      rewrite IH.
      2:{ rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia.
          split; [apply Z.div_pos; lia |].
          apply Z.div_lt_upper_bound; lia. }
      unfold EccSpec.window_digit.
      change (8 ^ Z.of_nat 0) with 1. rewrite Z.div_1_r.
      pose proof (Z.div_mod k 8 ltac:(lia)). lia.
  Qed.

  Lemma windows_read (w : HonestInput) (region : RegionId.t) (k : Z) :
    (forall i : nat, (i < 85)%nat ->
      OCT.advice_t w (OCT.tables_of w) Advice.A4 region (Z.of_nat i) =
        EccSpec.window_digit k i) ->
    0 <= k < 8 ^ 85 ->
    read_scalar_from_windows (OHA.honest_assignment w) region 85%nat = k.
  Proof.
    intros Hcell Hk.
    unfold read_scalar_from_windows, read_windows.
    replace (List.map
        (fun i : nat =>
          read_advice (OHA.honest_assignment w) Advice.A4 region (Z.of_nat i))
        (List.seq 0 85))
      with (List.map (fun i : nat => EccSpec.window_digit k i)
              (List.seq 0 85)).
    - rewrite (sfw_digits 85%nat k); [reflexivity |].
      change (8 ^ Z.of_nat 85) with (8 ^ 85). exact Hk.
    - apply List.map_ext_in. intros i Hi. apply List.in_seq in Hi.
      rewrite read_advice_cell. rewrite Hcell by lia.
      unfold UnOp.from. rewrite Z.mod_small; [reflexivity |].
      pose proof (window_digit_range k i).
      pose proof two_64_lt_p.
      lia.
  Qed.

  (** ** The Merkle layer index round trip

      The path reader names each layer by [Layer.of_index]; the generator's
      cell dispatch reads it back with [Layer.to_index]. *)

  Lemma layer_index_roundtrip (i : nat) :
    (i < 32)%nat ->
    RegionId.Merkle.Layer.to_index
      (RegionId.Merkle.Layer.of_index (Z.of_nat i)) = Z.of_nat i.
  Proof.
    intros Hi. do 32 (destruct i as [| i]; [reflexivity |]). lia.
  Qed.

  Lemma merkle_path_ok (w : HonestInput)
      (Hred : List.Forall (fun s => 0 <= s < Primes.pallas_p) (hi_path w))
      (Hlen : List.length (hi_path w) = 32%nat) :
    merkle_path_of (OHA.honest_assignment w) = path_of w.
  Proof.
    unfold merkle_path_of, path_of.
    apply List.map_ext_in. intros i Hi. apply List.in_seq in Hi.
    destruct Hi as [_ Hi]. cbn [Nat.add] in Hi.
    cbv zeta.
    unfold read1, read4, read6, read9. rewrite !read_advice_cell.
    cbn [OCT.advice_t].
    unfold OCT.merkle_advice_t.
    rewrite !(layer_index_roundtrip i ltac:(lia)).
    rewrite Nat2Z.id.
    assert (Hsib : UnOp.from (List.nth i (hi_path w) 0) =
        List.nth i (hi_path w) 0).
    { unfold UnOp.from. apply Z.mod_small.
      rewrite List.Forall_forall in Hred. apply Hred.
      apply List.nth_In. lia. }
    assert (Hbit : UnOp.from (if path_bit w i then 1 else 0) =? 1 =
        path_bit w i).
    { destruct (path_bit w i); unfold UnOp.from.
      - rewrite Z.mod_small by (pose proof one_lt_p; lia). reflexivity.
      - rewrite Zmod_0_l. reflexivity. }
    cbn [Z.eqb].
    destruct (Z.of_nat i <? 16); cbn [negb];
      rewrite Hsib, Hbit; reflexivity.
  Qed.

  (** ** The witnessed cells, family by family

      Each equation reduces the generator's region dispatch at a fixed column
      and row; no hoisted derivation is forced. *)

  Lemma cell_ak_x (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.AkP) 0 =
    Point.x (hi_ak w).
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_ak_y (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A1
      (RegionId.WitnessInput RegionId.WitnessInput.AkP) 0 =
    Point.y (hi_ak w).
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_gd_x (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.GDOld) 0 =
    Point.x (hi_g_d_old w).
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_gd_y (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A1
      (RegionId.WitnessInput RegionId.WitnessInput.GDOld) 0 =
    Point.y (hi_g_d_old w).
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_cm_x (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 =
    Point.x (cm_old w).
  Proof.
    cbn [OCT.advice_t]. unfold OCT.witness_input_advice_t. cbn [Z.eqb].
    rewrite OFS.t_cm_old_of. reflexivity.
  Qed.

  Lemma cell_cm_y (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A1
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 =
    Point.y (cm_old w).
  Proof.
    cbn [OCT.advice_t]. unfold OCT.witness_input_advice_t. cbn [Z.eqb].
    rewrite OFS.t_cm_old_of. reflexivity.
  Qed.

  Lemma cell_nk (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.Nk) 0 = hi_nk w.
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_rho_old (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.RhoOld) 0 = hi_rho_old w.
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_psi_old (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.PsiOld) 0 = hi_psi_old w.
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_v_old (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.VOld) 0 = hi_v_old w.
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_v_new (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.VNew) 0 = hi_v_new w.
  Proof. cbn [OCT.advice_t OCT.witness_input_advice_t]. reflexivity. Qed.

  Lemma cell_gd_new_x (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      RegionId.NoteCommitNewWitnessGD 0 = Point.x (hi_g_d_new w).
  Proof. cbn [OCT.advice_t]. reflexivity. Qed.

  Lemma cell_gd_new_y (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A1
      RegionId.NoteCommitNewWitnessGD 0 = Point.y (hi_g_d_new w).
  Proof. cbn [OCT.advice_t]. reflexivity. Qed.

  Lemma cell_pkd_new_x (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      RegionId.NoteCommitNewWitnessPkD 0 = Point.x (hi_pk_d_new w).
  Proof. cbn [OCT.advice_t]. reflexivity. Qed.

  Lemma cell_pkd_new_y (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A1
      RegionId.NoteCommitNewWitnessPkD 0 = Point.y (hi_pk_d_new w).
  Proof. cbn [OCT.advice_t]. reflexivity. Qed.

  Lemma cell_psi_new (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A0
      RegionId.NoteCommitNewWitnessPsi 0 = hi_psi_new w.
  Proof. cbn [OCT.advice_t]. reflexivity. Qed.

  Lemma cell_magnitude (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A9
      (RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck)
      0 = magnitude w.
  Proof.
    cbn [OCT.advice_t OCT.advice_ecc_t OrchardAdviceEccMuls.is_A9].
    reflexivity.
  Qed.

  Lemma cell_sign (w : HonestInput) :
    OCT.advice_t w (OCT.tables_of w) Advice.A9
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck)
      0 = sign w.
  Proof.
    cbn [OCT.advice_t OCT.advice_ecc_t OrchardAdviceEccMuls.is_A9].
    reflexivity.
  Qed.

  Lemma cell_alpha_window (w : HonestInput) (i : nat) :
    (i < 85)%nat ->
    OCT.advice_t w (OCT.tables_of w) Advice.A4
      (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
      (Z.of_nat i) = EccSpec.window_digit (hi_alpha w) i.
  Proof.
    intros Hi.
    cbn [OCT.advice_t OCT.advice_ecc_t].
    unfold OCT.fb_full_advice_t.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat i))) by lia.
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) 85)) by lia.
    cbn [andb]. rewrite Nat2Z.id. reflexivity.
  Qed.

  Lemma cell_rcv_window (w : HonestInput) (i : nat) :
    (i < 85)%nat ->
    OCT.advice_t w (OCT.tables_of w) Advice.A4
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete)
      (Z.of_nat i) = EccSpec.window_digit (hi_rcv w) i.
  Proof.
    intros Hi.
    cbn [OCT.advice_t OCT.advice_ecc_t].
    unfold OCT.fb_full_advice_t.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat i))) by lia.
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) 85)) by lia.
    cbn [andb]. rewrite Nat2Z.id. reflexivity.
  Qed.

  Lemma cell_rcm_new_window (w : HonestInput) (i : nat) :
    (i < 85)%nat ->
    OCT.advice_t w (OCT.tables_of w) Advice.A4
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete)
      (Z.of_nat i) = EccSpec.window_digit (hi_rcm_new w) i.
  Proof.
    intros Hi.
    cbn [OCT.advice_t OCT.advice_ecc_t].
    unfold OCT.fb_full_advice_t.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat i))) by lia.
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) 85)) by lia.
    cbn [andb]. rewrite Nat2Z.id. reflexivity.
  Qed.

  (** ** The public anchor row *)

  Lemma anchor_row_ok (w : HonestInput)
      (Hanchor : 0 <= hi_anchor_public w < Primes.pallas_p) :
    read_public_instance (OHA.honest_assignment w)
      Garden.Orchard.circuit.ANCHOR = anchor_public_row w.
  Proof.
    rewrite read_instance_cell.
    change (OCT.instance_t w (OCT.tables_of w) Garden.Orchard.circuit.ANCHOR)
      with (OCT.t_anchor_row (OCT.tables_of w)).
    rewrite t_anchor_row_def, t_anchor_root.
    unfold anchor_public_row, anchor_public_row_of_leaf, UnOp.from.
    destruct (hi_v_old w =? 0).
    - exact (Z.mod_small _ _ Hanchor).
    - exact (Z.mod_small _ _ (anchor_root_range w)).
  Qed.

  (** ** Value ranges of the derived witness fields *)

  Lemma magnitude_range (w : HonestInput)
      (Hold : 0 <= hi_v_old w < 2 ^ 64)
      (Hnew : 0 <= hi_v_new w < 2 ^ 64) :
    0 <= magnitude w < Primes.pallas_p.
  Proof.
    pose proof two_64_lt_p as Hp.
    unfold magnitude.
    clear -Hold Hnew Hp. lia.
  Qed.

  Lemma sign_range (w : HonestInput) : 0 <= sign w < Primes.pallas_p.
  Proof.
    pose proof one_lt_p as Hp.
    unfold sign.
    destruct (hi_v_new w <=? hi_v_old w); lia.
  Qed.

  (** ** The read-back obligation

      Every field of the read record is its honest value; the two constant
      pins ([pk_d_old], [rivk]) agree on both sides by construction. *)

  Theorem read_back_forward : OrchardCompletenessForward.read_back_ok.
  Proof.
    intros w Hvalid Hnondeg.
    destruct Hvalid as (Hty & _ & _ & _).
    destruct Hty as (Hvold & Hvnew & Halpha & Hrcv & Hrcmold & Hrcmnew
      & Hrivk & Hnk & Hrho & Hpsio & Hpsin & Hanch & Hak & Hgdo & Hpkdo
      & Hgdn & Hpkdn & Hplen & Hpred & Hpos & _ & _).
    pose proof two_64_lt_p as Hp64.
    pose proof q_lt_pow8_85 as Hq85.
    destruct (OCF.point_ok_coords _ Hak) as [Hakx Haky].
    destruct (OCF.point_ok_coords _ Hgdo) as [Hgdox Hgdoy].
    destruct (OCF.point_ok_coords _ Hgdn) as [Hgdnx Hgdny].
    destruct (OCF.point_ok_coords _ Hpkdn) as [Hpkdnx Hpkdny].
    destruct (cm_old_coords w) as [Hcmx Hcmy].
    unfold read_action_inputs, read_action_inputs_with_anchor, inputs_of.
    cbv zeta.
    rewrite (read_point_of w _ (hi_ak w) (cell_ak_x w) (cell_ak_y w)
      Hakx Haky).
    rewrite (read_point_of w _ (hi_g_d_old w) (cell_gd_x w) (cell_gd_y w)
      Hgdox Hgdoy).
    rewrite (read_point_of w _ (hi_g_d_new w)
      (cell_gd_new_x w) (cell_gd_new_y w) Hgdnx Hgdny).
    rewrite (read_point_of w _ (hi_pk_d_new w)
      (cell_pkd_new_x w) (cell_pkd_new_y w) Hpkdnx Hpkdny).
    rewrite (read_point_of w _ (cm_old w) (cell_cm_x w) (cell_cm_y w)
      Hcmx Hcmy).
    rewrite (read_of w _ (hi_nk w) (cell_nk w) Hnk).
    rewrite (read_of w _ (hi_rho_old w) (cell_rho_old w) Hrho).
    rewrite (read_of w _ (hi_psi_old w) (cell_psi_old w) Hpsio).
    rewrite (read_of w _ (hi_psi_new w) (cell_psi_new w) Hpsin).
    rewrite (read_of w _ (hi_v_old w) (cell_v_old w) ltac:(lia)).
    rewrite (read_of w _ (hi_v_new w) (cell_v_new w) ltac:(lia)).
    rewrite (read_of w _ (Point.x (cm_old w)) (cell_cm_x w) Hcmx).
    rewrite (read9_of w _ (magnitude w) (cell_magnitude w)
      (magnitude_range w Hvold Hvnew)).
    rewrite (read9_of w _ (sign w) (cell_sign w) (sign_range w)).
    rewrite (windows_read w _ (hi_alpha w) (cell_alpha_window w)
      ltac:(lia)).
    rewrite (windows_read w _ (hi_rcv w) (cell_rcv_window w) ltac:(lia)).
    rewrite (windows_read w _ (hi_rcm_new w) (cell_rcm_new_window w)
      ltac:(lia)).
    rewrite (merkle_path_ok w Hpred Hplen).
    rewrite (anchor_row_ok w Hanch).
    reflexivity.
  Qed.

End OrchardForwardReadBack.
