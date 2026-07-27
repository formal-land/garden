(** * Forward witness facts: a hoisted fold's final row

    The "chain-outputs" group of the open witness-fact residue: the eight
    facts of the synthesis program whose two cell addresses are the last row
    of a hoisted derivation fold and the first row of the region that
    consumes it.

    - the three Sinsemilla hash regions ([Commit^ivk] at row 51, the old and
      new [NoteCommit] hashes at row 109) carry their output point on the
      accumulator/ordinate columns of the region's variant, and the
      commitment region's complete addition reads the same point as its
      first summand;
    - the last Merkle layer's hash output at row 52 is the anchor cell of
      the whole-circuit checks region;
    - the 36th Poseidon permutation state's first word is the nullifier
      chain's [hash2] input.

    None of them is a reduction: one side is a projection of the hoisted
    record [tables_of w], the other goes through a region reader's guarded
    index arithmetic over the [hash_go] / [layers_go] / [pose_states_of]
    folds.  Each is bridged by two cell-reading lemmas and one endpoint
    identity ([hash_endpoint_x] / [hash_endpoint_y] for the hash regions,
    [t_anchor_last] for the anchor, [t_hash2_state] for Poseidon).

    Export: [orchardwitnesschainoutputs_facts] (the fact literals) and
    [orchardwitnesschainoutputs_ok] (they hold at [honest_assignment w] for
    every valid, nondegenerate input). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Garden.Orchard.circuit.
Require Garden.Orchard.protocol_spec.
Require Import Garden.Field.Div.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardWitnessChainOutputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.
  Import OrchardCompletenessTables.
  Import OrchardAdviceMerkleSinsemilla.
  Import OrchardForwardSinsemilla.

  Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** The hoisted derivation record stays a stuck atom: a reduction that
      unfolds [tables_of] on symbolic input normalizes the Sinsemilla,
      ladder and Poseidon folds it carries (docs/compile-performance.md). *)
  #[local] Strategy opaque
    [OrchardCompletenessTables.tables_of
     BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** The heavy folds the cell readings mention.  [layers_of] is left
      transparent: [t_layers_length] unfolds it to reach [layers_go]. *)
  #[local] Opaque OrchardCompletenessTables.hash_data_of
    OrchardCompletenessTables.hash_go
    OrchardCompletenessTables.pose_states_of
    OrchardWitnessInput.poseidon_state
    OrchardAdviceMerkleSinsemilla.split_pieces
    OrchardVarBaseTables.vb_columns
    SinsemillaSpec.sinsemilla_hash_to_point
    Poseidon.poseidon_hash2.

  (** ** The hash regions' endpoint row

      At row [n = |ws|] the accumulator column carries the abscissa and the
      first-gradient column the ordinate of the region's output point.  Both
      the column and the row are taken as parameters constrained by an
      equation, so every instance below matches syntactically. *)

  Lemma hash_endpoint_x (Q : Point.t) (pieces : list (list Z))
      (second : bool) (col : Advice.t) (n : nat) (r : Z)
      (Hcol : col = xa_col second)
      (Hn : List.length (Stdlib.Lists.List.concat pieces) = n)
      (Hr : r = Z.of_nat n) :
    hash_region_advice_t (hash_data_of Q pieces) second col r =
      Point.x (hd_out (hash_data_of Q pieces)).
  Proof.
    subst col. subst r. subst n.
    rewrite (hash_cell_xa Q pieces second
      (List.length (Stdlib.Lists.List.concat pieces)) ltac:(lia)).
    rewrite hd_out_of.
    rewrite sinsemilla_acc_full.
    reflexivity.
  Qed.

  Lemma hash_endpoint_y (Q : Point.t) (pieces : list (list Z))
      (second : bool) (col : Advice.t) (n : nat) (r : Z)
      (Hcol : col = l1_col second)
      (Hn : List.length (Stdlib.Lists.List.concat pieces) = n)
      (Hr : r = Z.of_nat n) :
    hash_region_advice_t (hash_data_of Q pieces) second col r =
      Point.y (hd_out (hash_data_of Q pieces)).
  Proof.
    subst col. subst r. subst n.
    rewrite (hash_cell_yout Q pieces second).
    rewrite hd_out_of.
    rewrite sinsemilla_acc_full.
    reflexivity.
  Qed.

  (** ** The cell readings

      Each address of each fact, read off the generator's advice dispatch.
      The commitment and copy rows are definitional; the hash regions go
      through the dispatch lemmas of [forward/sinsemilla.v], restated at the
      literal region of the fact so the rewrites are syntactic. *)

  Lemma civk_cadd_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 0 =
    Point.x (hd_out (t_civk_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma civk_cadd_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 0 =
    Point.y (hd_out (t_civk_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma nc_old_cadd_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 0 =
    Point.x (hd_out (t_nc_old_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma nc_old_cadd_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 0 =
    Point.y (hd_out (t_nc_old_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma nc_new_cadd_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 0 =
    Point.x (hd_out (t_nc_new_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma nc_new_cadd_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 0 =
    Point.y (hd_out (t_nc_new_hash (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma anchor_read (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A4 RegionId.OrchardCircuitChecks 0 =
    t_anchor (tables_of w).
  Proof. reflexivity. Qed.

  Lemma scalar_add_hash2_read (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.Nullifier RegionId.Nullifier.ScalarAdd) 0 =
    t_hash2 (tables_of w).
  Proof. reflexivity. Qed.

  Lemma permute_state_36_read (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.Poseidon RegionId.Poseidon.PermuteState) 36 =
    State.x0 (pose_state_t (tables_of w) 36%nat).
  Proof. reflexivity. Qed.

  Lemma civk_hash_read (w : HonestInput) (col : Advice.t) (r : Z) :
    (Γw w).(Assignment.advice) col
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) r =
    hash_region_advice_t
      (hash_data_of commit_ivk_Q
        (split_pieces commit_ivk_lens (commit_ivk_words w))) false col r.
  Proof. exact (civk_hash_adv w col r). Qed.

  Lemma nc_old_hash_read (w : HonestInput) (col : Advice.t) (r : Z) :
    (Γw w).(Assignment.advice) col
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) r =
    hash_region_advice_t
      (hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_old_words w))) false
      col r.
  Proof. exact (nc_old_hash_adv w col r). Qed.

  Lemma nc_new_hash_read (w : HonestInput) (col : Advice.t) (r : Z) :
    (Γw w).(Assignment.advice) col
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint) r =
    hash_region_advice_t
      (hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_new_words w))) true
      col r.
  Proof. exact (nc_new_hash_adv w col r). Qed.

  Lemma merkle31_hash_read (w : HonestInput) (col : Advice.t) (r : Z) :
    (Γw w).(Assignment.advice) col
      (RegionId.Merkle RegionId.Merkle.Layer.L31
        RegionId.Merkle.Region.HashToPoint) r =
    hash_region_advice_t
      (hash_data_of merkle_Q
        (split_pieces merkle_lens (merkle_layer_words w 31%nat))) true col r.
  Proof. exact (merkle_hash_adv w RegionId.Merkle.Layer.L31 col r). Qed.

  (** ** The anchor is the last Merkle layer's hash output

      [t_anchor] is [anchor_of] over the hoisted layer chain, i.e. the
      output of the chain's last entry; [t_layers_nth] identifies that entry
      with layer 31's data. *)

  Lemma layers_go_length (w : HonestInput) :
    forall (count : nat) (node : Z) (i : nat),
      List.length (layers_go w node i count) = count.
  Proof.
    induction count as [| count IH]; intros node i;
      cbn [layers_go List.length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma t_layers_length (w : HonestInput) :
    List.length (t_layers (tables_of w)) = 32%nat.
  Proof.
    cbn [tables_of t_layers].
    unfold layers_of.
    apply layers_go_length.
  Qed.

  Lemma anchor_of_last (layers : list layer_data) (lf : Z) (n : nat) :
    List.length layers = S n ->
    anchor_of layers lf =
    Point.x (hd_out (lyd_hash (List.nth n layers layer0))).
  Proof.
    intros Hlen.
    assert (Hne : layers <> []).
    { intros Hnil. rewrite Hnil in Hlen. cbn in Hlen. lia. }
    destruct (List.exists_last Hne) as (l' & a & Heq).
    subst layers.
    rewrite List.length_app in Hlen. cbn [List.length] in Hlen.
    assert (Hn : List.length l' = n) by lia.
    unfold anchor_of.
    rewrite List.rev_app_distr. cbn [List.rev List.app].
    rewrite <- Hn, List.nth_middle.
    reflexivity.
  Qed.

  Lemma t_anchor_def (w : HonestInput) :
    t_anchor (tables_of w) =
    anchor_of (t_layers (tables_of w)) (Point.x (t_cm_old (tables_of w))).
  Proof.
    cbn [tables_of t_anchor t_layers t_cm_old]. reflexivity.
  Qed.

  Lemma t_anchor_last (w : HonestInput) :
    t_anchor (tables_of w) =
    Point.x (hd_out (hash_data_of merkle_Q
      (split_pieces merkle_lens (merkle_layer_words w 31%nat)))).
  Proof.
    rewrite t_anchor_def.
    rewrite (anchor_of_last _ _ 31%nat (t_layers_length w)).
    rewrite (t_layers_nth w 31%nat ltac:(lia)).
    cbn [merkle_layer_data lyd_hash].
    reflexivity.
  Qed.

  (** ** The nullifier chain's Poseidon input

      The record's [t_hash2] field is the first word of the 36th
      permutation state, which is what the [PermuteState] region's [A6]
      column reads at row 36. *)

  Lemma t_hash2_state (w : HonestInput) :
    t_hash2 (tables_of w) = State.x0 (pose_state_t (tables_of w) 36%nat).
  Proof.
    unfold pose_state_t.
    cbn [tables_of t_hash2 t_pose].
    reflexivity.
  Qed.

  (** ** The group's facts

      The literals are copied verbatim from the residue list [nt_open] of
      [forward/lookups_witness.v], in increasing index order (indices 4, 18,
      19, 45, 46, 78, 79, 96). *)

  Definition orchardwitnesschainoutputs_facts
      : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Nullifier RegionId.Nullifier.ScalarAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.PermuteState; Cell.row_offset := 36 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 51 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 51 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 109 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 109 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 109 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 109 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |}].

  (** The head of a witness-fact goal: the two cell addresses, with the
      advice dispatch left folded. *)
  Ltac co_head :=
    cbn [interpret_fact eval_cell Cell.column Cell.region Cell.row_offset].

  Lemma fact_hash2 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.Nullifier RegionId.Nullifier.ScalarAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.Poseidon RegionId.Poseidon.PermuteState) 36.
  Proof.
    rewrite scalar_add_hash2_read, permute_state_36_read.
    exact (t_hash2_state w).
  Qed.

  Lemma fact_civk_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) 51.
  Proof.
    rewrite civk_cadd_x, civk_hash_read.
    rewrite (hash_endpoint_x commit_ivk_Q _ false Advice.A0 51%nat 51
      eq_refl (civk_hash_len w) eq_refl).
    rewrite t_civk_hash_of.
    reflexivity.
  Qed.

  Lemma fact_civk_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) 51.
  Proof.
    rewrite civk_cadd_y, civk_hash_read.
    rewrite (hash_endpoint_y commit_ivk_Q _ false Advice.A3 51%nat 51
      eq_refl (civk_hash_len w) eq_refl).
    rewrite t_civk_hash_of.
    reflexivity.
  Qed.

  Lemma fact_nc_old_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) 109.
  Proof.
    rewrite nc_old_cadd_x, nc_old_hash_read.
    rewrite (hash_endpoint_x note_commit_Q _ false Advice.A0 109%nat 109
      eq_refl (nc_old_hash_len w) eq_refl).
    rewrite t_nc_old_hash_of.
    reflexivity.
  Qed.

  Lemma fact_nc_old_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) 109.
  Proof.
    rewrite nc_old_cadd_y, nc_old_hash_read.
    rewrite (hash_endpoint_y note_commit_Q _ false Advice.A3 109%nat 109
      eq_refl (nc_old_hash_len w) eq_refl).
    rewrite t_nc_old_hash_of.
    reflexivity.
  Qed.

  Lemma fact_nc_new_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A5
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint) 109.
  Proof.
    rewrite nc_new_cadd_x, nc_new_hash_read.
    rewrite (hash_endpoint_x note_commit_Q _ true Advice.A5 109%nat 109
      eq_refl (nc_new_hash_len w) eq_refl).
    rewrite t_nc_new_hash_of.
    reflexivity.
  Qed.

  Lemma fact_nc_new_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 0 =
    (Γw w).(Assignment.advice) Advice.A8
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint) 109.
  Proof.
    rewrite nc_new_cadd_y, nc_new_hash_read.
    rewrite (hash_endpoint_y note_commit_Q _ true Advice.A8 109%nat 109
      eq_refl (nc_new_hash_len w) eq_refl).
    rewrite t_nc_new_hash_of.
    reflexivity.
  Qed.

  Lemma fact_anchor (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A4 RegionId.OrchardCircuitChecks 0 =
    (Γw w).(Assignment.advice) Advice.A5
      (RegionId.Merkle RegionId.Merkle.Layer.L31
        RegionId.Merkle.Region.HashToPoint) 52.
  Proof.
    rewrite anchor_read, merkle31_hash_read.
    rewrite (hash_endpoint_x merkle_Q _ true Advice.A5 52%nat 52
      eq_refl (merkle_hash_len w 31%nat) eq_refl).
    exact (t_anchor_last w).
  Qed.

  Lemma orchardwitnesschainoutputs_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w)
    : interpret_facts (OrchardHonestAssignment.honest_assignment w)
        orchardwitnesschainoutputs_facts.
  Proof.
    unfold orchardwitnesschainoutputs_facts.
    cbn [interpret_facts].
    repeat apply conj.
    - co_head. exact (fact_hash2 w).
    - co_head. exact (fact_civk_x w).
    - co_head. exact (fact_civk_y w).
    - co_head. exact (fact_nc_old_x w).
    - co_head. exact (fact_nc_old_y w).
    - co_head. exact (fact_nc_new_x w).
    - co_head. exact (fact_nc_new_y w).
    - co_head. exact (fact_anchor w).
    - exact I.
  Qed.
End OrchardWitnessChainOutputs.
