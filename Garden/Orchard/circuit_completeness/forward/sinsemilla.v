(** * Forward lemmas: the Sinsemilla hash round gates

    The symbolic per-gate forward lemmas of the C2 completeness campaign for
    the Sinsemilla hash-to-point regions — the 32 Merkle path layers and the
    three note/commitment hash regions (old/new [NoteCommit], [Commit^ivk]).
    The obligation is the [Hgates] premise of [Complete.circuit_holds_intro]
    at [honest_assignment w], restricted to the enabled points whose selector
    is one of the four Sinsemilla selectors ([QSinsemilla1_1], [QSinsemilla1_2],
    [QSinsemilla4_1], [QSinsemilla4_2]); these selectors are enabled exactly
    on the hash-region rows, so this restriction is the hash-round slice of
    the per-family gate obligations ([forward/api.v]) for the Merkle families
    [1..32] and the [CommitIvk]/[NoteCommit] families [38..40].

    Structure:

    - the gate inventory: the constraints guarded by each Sinsemilla selector
      are exactly the chip's "Secant line" / "y check" ([sinsemilla_gate]) and
      "Initial y_Q" ([initial_y_q_gate]) bodies, by one [vm_compute]
      certificate per selector over the configured system;
    - the point inventory: a [vm_compute] certificate pinning the region/row
      shape of every enabled point carrying a Sinsemilla selector;
    - the fixed-plane certificates: the [q_sinsemilla2] piece schedule
      (interior rows [0]/[1], final row [2]) and the [fixed_y_q] domain
      ordinate of every hash region;
    - the [hash_go] fold bridge: the hoisted table rows of
      [OrchardCompletenessTables.hash_data_of] are the per-round
      accumulator/generator/gradient values of the specification fold;
    - the derived-table identifications: the Merkle layer chain, the old-note
      commitment and the new note's [ρ] (the nullifier) as the spec values;
    - the field-algebra cores: the three gate identities over the fold values,
      under the incomplete-addition nondegeneracy of [nondegenerate w];
    - the assembly [sinsemilla_gates_forward].

    The soundness-side counterparts are
    [sinsemilla/hash_to_point_round_proof.v] ([round_pins]) and
    [circuit_proof/merkle.v]; the forward direction proves the generator's
    cells satisfy the gates, so the algebra runs on the same identities with
    the division-exactness laws supplying the chord equations. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Orchard.circuit_completeness.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.tables.
Require Import Garden.Orchard.circuit_completeness.certificates.
Require Import Garden.Orchard.circuit_completeness.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Classes.Morphisms.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module SChip := Garden.Halo2.halo2_gadgets.sinsemilla.chip.

Module OrchardForwardSinsemilla.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.
  Import OrchardCompletenessInstanceDefs.

  (** ** The selector class and the obligation

      The four Sinsemilla selectors; the forward obligation below is the
      [Hgates] premise of [circuit_holds_intro] restricted to the enabled
      points guarded by one of them.  Together with the sibling per-selector
      forward lemmas this covers the per-family gate obligations of
      [forward/api.v]. *)
  Definition sins_selector (sel : Selector.t) : bool :=
    match sel with
    | Selector.QSinsemilla1_1 | Selector.QSinsemilla1_2
    | Selector.QSinsemilla4_1 | Selector.QSinsemilla4_2 => true
    | _ => false
    end.

  (** ** The gate inventory

      [sel_bodies sel gates]: every constraint body guarded by [sel] across
      the system's gates.  [sel_bodies_complete] turns a membership in the
      intro obligation into a membership of this list; one [vm_compute]
      certificate per Sinsemilla selector pins the list to the chip's
      bodies. *)
  Definition sel_bodies (sel : Selector.t) (gates : list (Gate.t columns))
      : list (Constraint.t columns) :=
    Stdlib.Lists.List.flat_map
      (fun gate =>
        Stdlib.Lists.List.flat_map
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select sel' body =>
                if OrchardDecidableEq.selector_eqb sel' sel then [body] else []
            | _ => []
            end)
          gate.(Gate.constraints))
      gates.

  Lemma sel_bodies_complete
      (sel : Selector.t) (gates : list (Gate.t columns))
      (gate : Gate.t columns) (name : option string)
      (body : Constraint.t columns) :
    List.In gate gates ->
    List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
    List.In body (sel_bodies sel gates).
  Proof.
    intros Hgate Hbody.
    unfold sel_bodies.
    apply (proj2 (List.in_flat_map _ _ _)).
    exists gate.
    split; [exact Hgate |].
    apply (proj2 (List.in_flat_map _ _ _)).
    exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    cbn.
    rewrite OrchardDecidableEq.selector_eqb_refl.
    left; reflexivity.
  Qed.

  (** The gate bodies, extracted from the chip's gate definitions (so no
      transcription of the constraint trees appears here). *)
  Definition body_at (gate : Gate.t columns) (k : nat) : Constraint.t columns :=
    match List.nth_error gate.(Gate.constraints) k with
    | Some (_, Constraint.Select _ body) => body
    | _ => Constraint.Boolean (Expression.Constant 0)
    end.

  (** The "Secant line" and "y check" bodies of [sinsemilla_gate] and the
      "Initial y_Q" body of [initial_y_q_gate], over the given columns.  The
      guarding selector does not occur in the bodies, so it is fixed
      arbitrarily. *)
  Definition secant_body (q2 : Fixed.t) (x_a x_p lambda_1 lambda_2 : Advice.t)
      : Constraint.t columns :=
    body_at
      (SChip.sinsemilla_gate Selector.QSinsemilla1_1 q2 x_a x_p
        lambda_1 lambda_2) 0.

  Definition ycheck_body (q2 : Fixed.t) (x_a x_p lambda_1 lambda_2 : Advice.t)
      : Constraint.t columns :=
    body_at
      (SChip.sinsemilla_gate Selector.QSinsemilla1_1 q2 x_a x_p
        lambda_1 lambda_2) 1.

  Definition init_body (y_q : Fixed.t) (x_a x_p lambda_1 lambda_2 : Advice.t)
      : Constraint.t columns :=
    body_at
      (SChip.initial_y_q_gate Selector.QSinsemilla4_1 y_q x_a x_p
        lambda_1 lambda_2) 0.

  (** The per-selector body inventories over the configured system. *)
  Lemma bodies_qs1_1 :
    sel_bodies Selector.QSinsemilla1_1 system.(ConstraintSystem.gates) =
      [secant_body Fixed.QSinsemilla2_1 Advice.A0 Advice.A1 Advice.A3 Advice.A4;
       ycheck_body Fixed.QSinsemilla2_1 Advice.A0 Advice.A1 Advice.A3 Advice.A4].
  Proof. vm_compute. reflexivity. Qed.

  Lemma bodies_qs1_2 :
    sel_bodies Selector.QSinsemilla1_2 system.(ConstraintSystem.gates) =
      [secant_body Fixed.QSinsemilla2_2 Advice.A5 Advice.A6 Advice.A8 Advice.A9;
       ycheck_body Fixed.QSinsemilla2_2 Advice.A5 Advice.A6 Advice.A8 Advice.A9].
  Proof. vm_compute. reflexivity. Qed.

  Lemma bodies_qs4_1 :
    sel_bodies Selector.QSinsemilla4_1 system.(ConstraintSystem.gates) =
      [init_body Fixed.LagrangeCoeffs0 Advice.A0 Advice.A1 Advice.A3 Advice.A4].
  Proof. vm_compute. reflexivity. Qed.

  Lemma bodies_qs4_2 :
    sel_bodies Selector.QSinsemilla4_2 system.(ConstraintSystem.gates) =
      [init_body Fixed.LagrangeCoeffs1 Advice.A5 Advice.A6 Advice.A8 Advice.A9].
  Proof. vm_compute. reflexivity. Qed.

  (** ** The point inventory

      The region/row shape of every enabled point carrying a Sinsemilla
      selector: variant-1 selectors on the first sixteen Merkle layers, the
      old-note hash and the [Commit^ivk] hash; variant-2 selectors on the
      last sixteen Merkle layers and the new-note hash; [QSinsemilla1_*] on
      the round rows, [QSinsemilla4_*] on row [0]. *)
  Definition sins_point_shape (pt : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, row) := pt in
    match sel with
    | Selector.QSinsemilla1_1 =>
        match region with
        | RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint =>
            (RegionId.Merkle.Layer.to_index layer <? 16) &&
            (0 <=? row) && (row <? 52)
        | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
            RegionId.NoteCommit.HashToPoint =>
            (0 <=? row) && (row <? 109)
        | RegionId.CommitIvk RegionId.CommitIvk.HashToPoint =>
            (0 <=? row) && (row <? 51)
        | _ => false
        end
    | Selector.QSinsemilla1_2 =>
        match region with
        | RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint =>
            negb (RegionId.Merkle.Layer.to_index layer <? 16) &&
            (0 <=? row) && (row <? 52)
        | RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.HashToPoint =>
            (0 <=? row) && (row <? 109)
        | _ => false
        end
    | Selector.QSinsemilla4_1 =>
        match region with
        | RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint =>
            (RegionId.Merkle.Layer.to_index layer <? 16) && (row =? 0)
        | RegionId.NoteCommit RegionId.NoteCommit.Which.Old
            RegionId.NoteCommit.HashToPoint =>
            row =? 0
        | RegionId.CommitIvk RegionId.CommitIvk.HashToPoint =>
            row =? 0
        | _ => false
        end
    | Selector.QSinsemilla4_2 =>
        match region with
        | RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint =>
            negb (RegionId.Merkle.Layer.to_index layer <? 16) && (row =? 0)
        | RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.HashToPoint =>
            row =? 0
        | _ => false
        end
    | _ => true
    end.

  Lemma sins_points_shape_cert :
    List.forallb sins_point_shape enabled = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma sins_point_shape_of_In
      (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    sins_point_shape (sel, region, row) = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall sins_point_shape enabled)
      sins_points_shape_cert _ Hin).
  Qed.

  (** ** The fixed-plane reads

      The honest fixed plane is [Complete.fixed_write_or_zero] over the
      synthesis facts; [fixed_at] names that reader, and per-hash-region
      [vm_compute] certificates pin the [q_sinsemilla2] piece schedule and
      the [fixed_y_q] domain ordinate. *)
  Definition fixed_at (column : Fixed.t) (region : RegionId.t) (row : Z) : Z :=
    Complete.fixed_write_or_zero
      OrchardHonestAssignment.fixed_eqb OrchardHonestAssignment.region_eqb
      OrchardHonestAssignment.facts column region row.

  Lemma fixed_at_read (w : HonestInput) (column : Fixed.t)
      (region : RegionId.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      column region row = fixed_at column region row.
  Proof. reflexivity. Qed.

  (** The variant-indexed columns of a hash region. *)
  Definition q2_col (second : bool) : Fixed.t :=
    if second then Fixed.QSinsemilla2_2 else Fixed.QSinsemilla2_1.
  Definition yq_col (second : bool) : Fixed.t :=
    if second then Fixed.LagrangeCoeffs1 else Fixed.LagrangeCoeffs0.
  Definition xa_col (second : bool) : Advice.t :=
    if second then Advice.A5 else Advice.A0.
  Definition xp_col (second : bool) : Advice.t :=
    if second then Advice.A6 else Advice.A1.
  Definition l1_col (second : bool) : Advice.t :=
    if second then Advice.A8 else Advice.A3.
  Definition l2_col (second : bool) : Advice.t :=
    if second then Advice.A9 else Advice.A4.

  (** The [q_sinsemilla2] schedule property at one row: [2] on the final
      round row, [0] or [1] elsewhere ([q_s3 = q_s2 (q_s2 - 1)] is then [2]
      exactly on the final row and [0] on every other round row). *)
  Definition q2_row_ok (second : bool) (region : RegionId.t) (n : Z) (j : nat)
      : bool :=
    let v := fixed_at (q2_col second) region (Z.of_nat j) in
    if Z.of_nat j =? n - 1 then v =? 2 else (v =? 0) || (v =? 1).

  (** All 32 Merkle layers, with the case-complete enumeration. *)
  Definition all_layers : list RegionId.Merkle.Layer.t :=
    [RegionId.Merkle.Layer.L0; RegionId.Merkle.Layer.L1;
     RegionId.Merkle.Layer.L2; RegionId.Merkle.Layer.L3;
     RegionId.Merkle.Layer.L4; RegionId.Merkle.Layer.L5;
     RegionId.Merkle.Layer.L6; RegionId.Merkle.Layer.L7;
     RegionId.Merkle.Layer.L8; RegionId.Merkle.Layer.L9;
     RegionId.Merkle.Layer.L10; RegionId.Merkle.Layer.L11;
     RegionId.Merkle.Layer.L12; RegionId.Merkle.Layer.L13;
     RegionId.Merkle.Layer.L14; RegionId.Merkle.Layer.L15;
     RegionId.Merkle.Layer.L16; RegionId.Merkle.Layer.L17;
     RegionId.Merkle.Layer.L18; RegionId.Merkle.Layer.L19;
     RegionId.Merkle.Layer.L20; RegionId.Merkle.Layer.L21;
     RegionId.Merkle.Layer.L22; RegionId.Merkle.Layer.L23;
     RegionId.Merkle.Layer.L24; RegionId.Merkle.Layer.L25;
     RegionId.Merkle.Layer.L26; RegionId.Merkle.Layer.L27;
     RegionId.Merkle.Layer.L28; RegionId.Merkle.Layer.L29;
     RegionId.Merkle.Layer.L30; RegionId.Merkle.Layer.L31].

  Lemma all_layers_complete (layer : RegionId.Merkle.Layer.t) :
    List.In layer all_layers.
  Proof. destruct layer; cbn; tauto. Qed.

  (** The per-layer variant flag. *)
  Definition layer_second (layer : RegionId.Merkle.Layer.t) : bool :=
    negb (RegionId.Merkle.Layer.to_index layer <? 16).

  Definition merkle_h2p (layer : RegionId.Merkle.Layer.t) : RegionId.t :=
    RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint.

  Definition nc_h2p (which : RegionId.NoteCommit.Which.t) : RegionId.t :=
    RegionId.NoteCommit which RegionId.NoteCommit.HashToPoint.

  Definition civk_h2p : RegionId.t :=
    RegionId.CommitIvk RegionId.CommitIvk.HashToPoint.

  Lemma q2_sched_merkle_cert :
    List.forallb
      (fun layer =>
        List.forallb (q2_row_ok (layer_second layer) (merkle_h2p layer) 52)
          (List.seq 0%nat 52%nat))
      all_layers = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma q2_sched_nc_old_cert :
    List.forallb
      (q2_row_ok false (nc_h2p RegionId.NoteCommit.Which.Old) 109)
      (List.seq 0%nat 109%nat) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma q2_sched_nc_new_cert :
    List.forallb
      (q2_row_ok true (nc_h2p RegionId.NoteCommit.Which.New) 109)
      (List.seq 0%nat 109%nat) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma q2_sched_civk_cert :
    List.forallb (q2_row_ok false civk_h2p 51) (List.seq 0%nat 51%nat) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The [fixed_y_q] ordinate of each hash region is the domain point's
      y-coordinate. *)
  Lemma yq_merkle_cert :
    List.forallb
      (fun layer =>
        fixed_at (yq_col (layer_second layer)) (merkle_h2p layer) 0 =?
          Point.y merkle_Q)
      all_layers = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma yq_nc_old_cert :
    fixed_at (yq_col false) (nc_h2p RegionId.NoteCommit.Which.Old) 0 =
      Point.y (OrchardSpec.note_commit_q orchard_circuit_params).
  Proof. vm_cast_no_check (@eq_refl Z (Point.y
    (OrchardSpec.note_commit_q orchard_circuit_params))). Qed.

  Lemma yq_nc_new_cert :
    fixed_at (yq_col true) (nc_h2p RegionId.NoteCommit.Which.New) 0 =
      Point.y (OrchardSpec.note_commit_q orchard_circuit_params).
  Proof. vm_cast_no_check (@eq_refl Z (Point.y
    (OrchardSpec.note_commit_q orchard_circuit_params))). Qed.

  Lemma yq_civk_cert :
    fixed_at (yq_col false) civk_h2p 0 =
      Point.y (OrchardSpec.commit_ivk_q orchard_circuit_params).
  Proof. vm_cast_no_check (@eq_refl Z (Point.y
    (OrchardSpec.commit_ivk_q orchard_circuit_params))). Qed.

  (** The domain points have reduced coordinates. *)
  Lemma merkle_Q_reduced :
    (0 <=? Point.x merkle_Q) && (Point.x merkle_Q <? Primes.pallas_p) &&
    (0 <=? Point.y merkle_Q) && (Point.y merkle_Q <? Primes.pallas_p) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nc_Q_reduced :
    (0 <=? Point.x (OrchardSpec.note_commit_q orchard_circuit_params)) &&
    (Point.x (OrchardSpec.note_commit_q orchard_circuit_params)
      <? Primes.pallas_p) &&
    (0 <=? Point.y (OrchardSpec.note_commit_q orchard_circuit_params)) &&
    (Point.y (OrchardSpec.note_commit_q orchard_circuit_params)
      <? Primes.pallas_p) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma civk_Q_reduced :
    (0 <=? Point.x (OrchardSpec.commit_ivk_q orchard_circuit_params)) &&
    (Point.x (OrchardSpec.commit_ivk_q orchard_circuit_params)
      <? Primes.pallas_p) &&
    (0 <=? Point.y (OrchardSpec.commit_ivk_q orchard_circuit_params)) &&
    (Point.y (OrchardSpec.commit_ivk_q orchard_circuit_params)
      <? Primes.pallas_p) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** The [hash_go] fold bridge

      The hoisted hash-region record rows are the per-round values of the
      specification fold: at round [j] the accumulator's abscissa, the
      generator's abscissa, and the two chord gradients [rr_l1]/[rr_l2]
      (the same reduced formulas as [IncompleteAddition.output]). *)

  Definition rr_l1 (acc g : Point.t) : Z :=
    BinOp.div (Point.y acc -F Point.y g) (Point.x acc -F Point.x g).

  Definition rr_mid (acc g : Point.t) : Point.t :=
    EccSpec.point_add_incomplete acc g.

  Definition rr_l2 (acc g : Point.t) : Z :=
    BinOp.div (Point.y (rr_mid acc g) -F Point.y acc)
      (Point.x (rr_mid acc g) -F Point.x acc).

  Import OrchardCompletenessTables.
  Import OrchardAdviceMerkleSinsemilla.

  Lemma hash_go_cons (acc : Point.t) (w : Z) (ws : list Z) :
    hash_go acc (w :: ws) =
      ((Point.x acc, Point.x (SinsemillaSpec.generator w),
        rr_l1 acc (SinsemillaSpec.generator w),
        rr_l2 acc (SinsemillaSpec.generator w))
        :: fst (hash_go (SinsemillaSpec.round acc w) ws),
       snd (hash_go (SinsemillaSpec.round acc w) ws)).
  Proof.
    cbn [hash_go].
    match goal with
    | |- context [hash_go ?P ws] =>
        replace P with (SinsemillaSpec.round acc w)
    end.
    - destruct (hash_go (SinsemillaSpec.round acc w) ws) as [rows out].
      reflexivity.
    - unfold SinsemillaSpec.round, rr_l1, rr_l2, rr_mid,
        EccSpec.point_add_incomplete, IncompleteAddition.output, square.
      reflexivity.
  Qed.

  Lemma hash_go_out (ws : list Z) :
    forall acc : Point.t,
      snd (hash_go acc ws) =
        SinsemillaSpec.sinsemilla_hash_to_point acc ws.
  Proof.
    induction ws as [| w ws IH]; intros acc.
    - reflexivity.
    - rewrite hash_go_cons.
      cbn [snd].
      rewrite (IH (SinsemillaSpec.round acc w)).
      reflexivity.
  Qed.

  Lemma hash_go_nth (ws : list Z) :
    forall (acc : Point.t) (j : nat),
      (j < List.length ws)%nat ->
      List.nth j (fst (hash_go acc ws)) row0 =
        (Point.x (sinsemilla_acc acc ws j),
         Point.x (SinsemillaSpec.generator (List.nth j ws 0)),
         rr_l1 (sinsemilla_acc acc ws j)
           (SinsemillaSpec.generator (List.nth j ws 0)),
         rr_l2 (sinsemilla_acc acc ws j)
           (SinsemillaSpec.generator (List.nth j ws 0))).
  Proof.
    induction ws as [| w ws IH]; intros acc j Hj.
    - cbn [List.length] in Hj. lia.
    - rewrite hash_go_cons.
      destruct j as [| j'].
      + reflexivity.
      + cbn [List.length] in Hj.
        cbn [fst List.nth].
        rewrite (IH (SinsemillaSpec.round acc w) j' ltac:(lia)).
        reflexivity.
  Qed.

  (** Projections of [hash_data_of]. *)
  Lemma hd_words_of (Q : Point.t) (pieces : list (list Z)) :
    hd_words (hash_data_of Q pieces) = Stdlib.Lists.List.concat pieces.
  Proof.
    unfold hash_data_of.
    destruct (hash_go Q (Stdlib.Lists.List.concat pieces)) as [rows out].
    reflexivity.
  Qed.

  Lemma hd_rows_of (Q : Point.t) (pieces : list (list Z)) :
    hd_rows (hash_data_of Q pieces) =
      fst (hash_go Q (Stdlib.Lists.List.concat pieces)).
  Proof.
    unfold hash_data_of.
    destruct (hash_go Q (Stdlib.Lists.List.concat pieces)) as [rows out].
    reflexivity.
  Qed.

  Lemma hd_out_of (Q : Point.t) (pieces : list (list Z)) :
    hd_out (hash_data_of Q pieces) =
      SinsemillaSpec.sinsemilla_hash_to_point Q
        (Stdlib.Lists.List.concat pieces).
  Proof.
    unfold hash_data_of.
    pose proof (hash_go_out (Stdlib.Lists.List.concat pieces) Q) as Hout.
    destruct (hash_go Q (Stdlib.Lists.List.concat pieces)) as [rows out].
    exact Hout.
  Qed.

  (** ** Word-list bookkeeping: lengths and the piece split *)

  Lemma words_le_length (c : nat) :
    forall n : Z, List.length (SinsemillaSpec.words_le c n) = c.
  Proof.
    induction c as [| c IH]; intros n; cbn [SinsemillaSpec.words_le
      List.length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Fixpoint lens_sum (lens : list nat) : nat :=
    match lens with
    | [] => 0%nat
    | a :: lens' => (a + lens_sum lens')%nat
    end.

  Lemma concat_split_pieces (lens : list nat) :
    forall l : list Z,
      lens_sum lens = List.length l ->
      Stdlib.Lists.List.concat (split_pieces lens l) = l.
  Proof.
    induction lens as [| a lens IH]; intros l Hlen; cbn [lens_sum] in Hlen.
    - symmetry in Hlen.
      apply List.length_zero_iff_nil in Hlen.
      subst l.
      reflexivity.
    - cbn [split_pieces Stdlib.Lists.List.concat].
      rewrite IH
        by (rewrite List.length_skipn; lia).
      apply List.firstn_skipn.
  Qed.

  Lemma merkle_words_length (w : HonestInput) (i : nat) :
    List.length (merkle_layer_words w i) = 52%nat.
  Proof.
    unfold merkle_layer_words, SinsemillaSpec.merkle_message.
    destruct (path_bit w i); apply words_le_length.
  Qed.

  Lemma merkle_words_concat (w : HonestInput) (i : nat) :
    Stdlib.Lists.List.concat
      (split_pieces merkle_lens (merkle_layer_words w i)) =
    merkle_layer_words w i.
  Proof.
    apply concat_split_pieces.
    rewrite merkle_words_length.
    reflexivity.
  Qed.

  Lemma note_commit_message_length (g_d pk_d : Point.t) (v rho psi : Z) :
    List.length (OrchardSpec.note_commit_message g_d pk_d v rho psi) = 109%nat.
  Proof. apply words_le_length. Qed.

  Lemma note_commit_message_concat (g_d pk_d : Point.t) (v rho psi : Z) :
    Stdlib.Lists.List.concat
      (split_pieces note_commit_lens
        (OrchardSpec.note_commit_message g_d pk_d v rho psi)) =
    OrchardSpec.note_commit_message g_d pk_d v rho psi.
  Proof.
    apply concat_split_pieces.
    rewrite note_commit_message_length.
    reflexivity.
  Qed.

  Lemma commit_ivk_words_length (w : HonestInput) :
    List.length (commit_ivk_words w) = 51%nat.
  Proof. apply words_le_length. Qed.

  Lemma commit_ivk_words_concat (w : HonestInput) :
    Stdlib.Lists.List.concat
      (split_pieces commit_ivk_lens (commit_ivk_words w)) =
    commit_ivk_words w.
  Proof.
    apply concat_split_pieces.
    rewrite commit_ivk_words_length.
    reflexivity.
  Qed.

  (** ** The hash-region cell reads

      [hash_region_advice_t] at the five ladder columns, at a round row
      [j < n] and at the output row [n], as the specification fold values. *)

  Lemma logical_xa (second : bool) :
    logical_col second (xa_col second) = Some 0%nat.
  Proof. destruct second; reflexivity. Qed.

  Lemma logical_xp (second : bool) :
    logical_col second (xp_col second) = Some 1%nat.
  Proof. destruct second; reflexivity. Qed.

  Lemma logical_l1 (second : bool) :
    logical_col second (l1_col second) = Some 3%nat.
  Proof. destruct second; reflexivity. Qed.

  Lemma logical_l2 (second : bool) :
    logical_col second (l2_col second) = Some 4%nat.
  Proof. destruct second; reflexivity. Qed.

  Section HashCells.
    Variable Q : Point.t.
    Variable pieces : list (list Z).

    Local Notation ws := (Stdlib.Lists.List.concat pieces).
    Local Notation n := (List.length ws).
    Local Notation h := (hash_data_of Q pieces).

    Lemma hash_cell_xa (second : bool) (j : nat) :
      (j <= n)%nat ->
      hash_region_advice_t h second (xa_col second) (Z.of_nat j) =
        Point.x (sinsemilla_acc Q ws j).
    Proof.
      intros Hj.
      unfold hash_region_advice_t.
      rewrite logical_xa, hd_words_of, hd_rows_of.
      rewrite Nat2Z.id.
      destruct (Nat.eq_dec j n) as [-> | Hne].
      - rewrite (proj2 (Z.ltb_ge (Z.of_nat n) (Z.of_nat n)) ltac:(lia)).
        rewrite Bool.andb_false_r.
        rewrite (proj2 (Z.eqb_eq (Z.of_nat n) (Z.of_nat n)) eq_refl).
        rewrite hd_out_of.
        rewrite <- (sinsemilla_acc_full Q ws).
        reflexivity.
      - rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt (Z.of_nat j) (Z.of_nat n)) ltac:(lia)).
        cbn [andb].
        rewrite (hash_go_nth ws Q j ltac:(lia)).
        reflexivity.
    Qed.

    Lemma hash_cell_xp (second : bool) (j : nat) :
      (j < n)%nat ->
      hash_region_advice_t h second (xp_col second) (Z.of_nat j) =
        Point.x (SinsemillaSpec.generator (List.nth j ws 0)).
    Proof.
      intros Hj.
      unfold hash_region_advice_t.
      rewrite logical_xp, hd_words_of, hd_rows_of.
      rewrite Nat2Z.id.
      rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (Z.of_nat j) (Z.of_nat n)) ltac:(lia)).
      cbn [andb].
      rewrite (hash_go_nth ws Q j ltac:(lia)).
      reflexivity.
    Qed.

    Lemma hash_cell_l1 (second : bool) (j : nat) :
      (j < n)%nat ->
      hash_region_advice_t h second (l1_col second) (Z.of_nat j) =
        rr_l1 (sinsemilla_acc Q ws j)
          (SinsemillaSpec.generator (List.nth j ws 0)).
    Proof.
      intros Hj.
      unfold hash_region_advice_t.
      rewrite logical_l1, hd_words_of, hd_rows_of.
      rewrite Nat2Z.id.
      rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (Z.of_nat j) (Z.of_nat n)) ltac:(lia)).
      cbn [andb].
      rewrite (hash_go_nth ws Q j ltac:(lia)).
      reflexivity.
    Qed.

    Lemma hash_cell_l2 (second : bool) (j : nat) :
      (j < n)%nat ->
      hash_region_advice_t h second (l2_col second) (Z.of_nat j) =
        rr_l2 (sinsemilla_acc Q ws j)
          (SinsemillaSpec.generator (List.nth j ws 0)).
    Proof.
      intros Hj.
      unfold hash_region_advice_t.
      rewrite logical_l2, hd_words_of, hd_rows_of.
      rewrite Nat2Z.id.
      rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (Z.of_nat j) (Z.of_nat n)) ltac:(lia)).
      cbn [andb].
      rewrite (hash_go_nth ws Q j ltac:(lia)).
      reflexivity.
    Qed.

    Lemma hash_cell_yout (second : bool) :
      hash_region_advice_t h second (l1_col second) (Z.of_nat n) =
        Point.y (sinsemilla_acc Q ws n).
    Proof.
      unfold hash_region_advice_t.
      rewrite logical_l1, hd_words_of.
      rewrite (proj2 (Z.ltb_ge (Z.of_nat n) (Z.of_nat n)) ltac:(lia)).
      rewrite Bool.andb_false_r.
      rewrite (proj2 (Z.eqb_eq (Z.of_nat n) (Z.of_nat n)) eq_refl).
      rewrite hd_out_of.
      rewrite <- (sinsemilla_acc_full Q ws).
      reflexivity.
    Qed.

    Lemma hash_cell_xp_out (second : bool) :
      hash_region_advice_t h second (xp_col second) (Z.of_nat n) = 0.
    Proof.
      unfold hash_region_advice_t.
      rewrite logical_xp, hd_words_of.
      rewrite (proj2 (Z.ltb_ge (Z.of_nat n) (Z.of_nat n)) ltac:(lia)).
      rewrite Bool.andb_false_r.
      reflexivity.
    Qed.

    Lemma hash_cell_l2_out (second : bool) :
      hash_region_advice_t h second (l2_col second) (Z.of_nat n) = 0.
    Proof.
      unfold hash_region_advice_t.
      rewrite logical_l2, hd_words_of.
      rewrite (proj2 (Z.ltb_ge (Z.of_nat n) (Z.of_nat n)) ltac:(lia)).
      rewrite Bool.andb_false_r.
      reflexivity.
    Qed.
  End HashCells.

  (** ** The generated advice at the hash regions

      The dispatch of [honest_assignment]'s advice plane at each hash region
      is the [hash_region_advice_t] reader of the region's hoisted
      [hash_data], and the hoisted data is [hash_data_of] at the region's
      domain point and honest message. *)

  Lemma advice_merkle_h2p (w : HonestInput) (col : Advice.t)
      (layer : RegionId.Merkle.Layer.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col (merkle_h2p layer) row =
    hash_region_advice_t
      (lyd_hash
        (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
          (t_layers (tables_of w)) layer0))
      (layer_second layer) col row.
  Proof. reflexivity. Qed.

  Lemma advice_nc_old_h2p (w : HonestInput) (col : Advice.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col (nc_h2p RegionId.NoteCommit.Which.Old) row =
    hash_region_advice_t (t_nc_old_hash (tables_of w)) false col row.
  Proof. reflexivity. Qed.

  Lemma advice_nc_new_h2p (w : HonestInput) (col : Advice.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col (nc_h2p RegionId.NoteCommit.Which.New) row =
    hash_region_advice_t (t_nc_new_hash (tables_of w)) true col row.
  Proof. reflexivity. Qed.

  Lemma advice_civk_h2p (w : HonestInput) (col : Advice.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col civk_h2p row =
    hash_region_advice_t (t_civk_hash (tables_of w)) false col row.
  Proof. reflexivity. Qed.

  (** The old-note commitment of the hoisted record is the specification
      commitment. *)
  Lemma nc_old_words_concat (w : HonestInput) :
    Stdlib.Lists.List.concat
      (split_pieces note_commit_lens (note_commit_old_words w)) =
    note_commit_old_words w.
  Proof.
    apply concat_split_pieces.
    unfold note_commit_old_words.
    rewrite note_commit_message_length.
    reflexivity.
  Qed.

  Lemma t_nc_old_hash_of (w : HonestInput) :
    t_nc_old_hash (tables_of w) =
      hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_old_words w)).
  Proof. reflexivity. Qed.

  (** The zeta expansion of the record's [cm_old] field is the specification
      commitment ([hd_out_of] folds the hash, [nc_old_words_concat] restores
      the message).  Every consumer rewrites with this equation instead of
      converting through a nested [tables_of] projection — conversion between
      two spellings of a projection argument forces the symbolic hash fold. *)
  Lemma cm_old_expand (w : HonestInput) :
    EccSpec.point_add
      (hd_out (hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_old_words w))))
      (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)) = cm_old w.
  Proof.
    rewrite hd_out_of, nc_old_words_concat.
    unfold cm_old, OrchardProtocolSpec.note_commit.
    reflexivity.
  Qed.

  Lemma t_cm_old_of (w : HonestInput) :
    t_cm_old (tables_of w) = cm_old w.
  Proof.
    change (t_cm_old (tables_of w)) with
      (EccSpec.point_add
        (hd_out (hash_data_of note_commit_Q
          (split_pieces note_commit_lens (note_commit_old_words w))))
        (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w))).
    exact (cm_old_expand w).
  Qed.

  (** The Merkle layer chain of the hoisted record: layer [i] carries the
      running node [merkle_node w i] and the hash data of the layer's
      message. *)
  Definition merkle_layer_data (w : HonestInput) (i : nat) : layer_data := {|
    lyd_node := merkle_node w i;
    lyd_hash :=
      hash_data_of merkle_Q
        (split_pieces merkle_lens (merkle_layer_words w i));
  |}.

  Lemma merkle_words_at_node (w : HonestInput) (i : nat) :
    merkle_words_at w (merkle_node w i) i = merkle_layer_words w i.
  Proof. reflexivity. Qed.

  Lemma layers_go_nth (w : HonestInput) :
    forall (count start k : nat),
      (start + count <= 32)%nat ->
      (k < count)%nat ->
      List.nth k (layers_go w (merkle_node w start) start count) layer0 =
        merkle_layer_data w (start + k).
  Proof.
    induction count as [| count IH]; intros start k Hbound Hk; [lia |].
    cbn [layers_go].
    rewrite merkle_words_at_node.
    destruct k as [| k'].
    - cbn [List.nth].
      rewrite Nat.add_0_r.
      reflexivity.
    - cbn [List.nth].
      replace (Point.x (hd_out (hash_data_of merkle_Q
          (split_pieces merkle_lens (merkle_layer_words w start)))))
        with (merkle_node w (S start)).
      + rewrite (IH (S start) k' ltac:(lia) ltac:(lia)).
        replace (start + S k')%nat with (S start + k')%nat by lia.
        reflexivity.
      + rewrite hd_out_of, merkle_words_concat.
        rewrite (merkle_node_succ w start ltac:(lia)).
        rewrite merkle_layer_words_spec.
        reflexivity.
  Qed.

  (** Tactic-level opacity for the heavy folds: every remaining proof in
      this module rewrites across [tables_of] projections whose arguments
      carry the Sinsemilla hash folds, the Merkle layer chain and the
      Poseidon schedule.  A [rewrite]/[change]/[exact] whose unification
      unfolds one of these folds on symbolic input diverges (the
      fold-normalization pitfalls of [docs/compile-performance.md]), so the
      constants are opaque from here on; the few proofs that genuinely
      unfold one re-enable it locally via [with_strategy transparent]. *)
  #[local] Opaque hash_data_of hash_go layers_of split_pieces pose_states_of
    cm_old nf_old OrchardProtocolSpec.mul_nullifier_k
    OrchardProtocolSpec.mul_note_commit_r OrchardProtocolSpec.mul_commit_ivk_r
    OrchardProtocolSpec.note_commit OrchardProtocolSpec.nullifier
    Poseidon.poseidon_hash2 SinsemillaSpec.sinsemilla_hash_to_point.

  Lemma t_layers_nth (w : HonestInput) (i : nat) :
    (i < 32)%nat ->
    List.nth i (t_layers (tables_of w)) layer0 = merkle_layer_data w i.
  Proof.
    intros Hi.
    change (t_layers (tables_of w)) with
      (layers_of w
        (Point.x (EccSpec.point_add
          (hd_out (hash_data_of note_commit_Q
            (split_pieces note_commit_lens (note_commit_old_words w))))
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w))))).
    rewrite cm_old_expand.
    change (Point.x (cm_old w)) with (leaf w).
    with_strategy transparent [layers_of] (unfold layers_of).
    change (leaf w) with (merkle_node w 0).
    exact (layers_go_nth w 32%nat 0%nat i ltac:(lia) Hi).
  Qed.

  (** The Poseidon schedule end state and the nullifier of the hoisted
      record. *)
  Fixpoint pose_iter (s : State.t) (row count : nat) : State.t :=
    match count with
    | O => s
    | S count' => pose_iter (poseidon_round row s) (S row) count'
    end.

  Lemma states_go_last :
    forall (count : nat) (s : State.t) (row : nat),
      List.nth count (states_go s row count) state0 = pose_iter s row count.
  Proof.
    induction count as [| count IH]; intros s row.
    - reflexivity.
    - cbn [states_go List.nth pose_iter].
      apply IH.
  Qed.

  Lemma pose_iter_fold :
    forall (count : nat) (s : State.t) (row : nat),
      pose_iter s row count =
        Stdlib.Lists.List.fold_left (fun t r => poseidon_round r t)
          (List.seq row count) s.
  Proof.
    induction count as [| count IH]; intros s row.
    - reflexivity.
    - cbn [pose_iter List.seq Stdlib.Lists.List.fold_left].
      apply IH.
  Qed.

  (** The fold spelling of the iterate is [witness_input.v]'s
      [poseidon_state], so the squeeze lemma applies syntactically (never
      hand conversion two spellings of the 36-round chain). *)
  Lemma pose_iter_state (s : State.t) (n : nat) :
    pose_iter s 0%nat n = poseidon_state s n.
  Proof.
    rewrite pose_iter_fold.
    unfold poseidon_state.
    reflexivity.
  Qed.

  (** The zeta expansion of the record's Poseidon squeeze is the PRF value. *)
  Lemma pose_hash2_expand (w : HonestInput) :
    State.x0 (List.nth 36 (pose_states_of w) state0) =
      Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w).
  Proof.
    with_strategy transparent [pose_states_of] (unfold pose_states_of).
    rewrite (states_go_last 36%nat (poseidon_input_state w) 0%nat).
    rewrite (pose_iter_state (poseidon_input_state w) 36%nat).
    pose proof (poseidon_round_state_hash2 w) as Hh.
    unfold poseidon_round_state in Hh.
    exact Hh.
  Qed.

  Lemma t_hash2_of (w : HonestInput) :
    t_hash2 (tables_of w) =
      Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w).
  Proof.
    change (t_hash2 (tables_of w)) with
      (State.x0 (List.nth 36 (pose_states_of w) state0)).
    exact (pose_hash2_expand w).
  Qed.

  (** The zeta expansion of the record's nullifier field is the
      specification nullifier. *)
  Lemma nf_expand_eq (w : HonestInput) :
    EccSpec.extract_x
      (EccSpec.point_add
        (OrchardProtocolSpec.mul_nullifier_k
          (State.x0 (List.nth 36 (pose_states_of w) state0) +F hi_psi_old w))
        (EccSpec.point_add
          (hd_out (hash_data_of note_commit_Q
            (split_pieces note_commit_lens (note_commit_old_words w))))
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)))) =
    nf_old w.
  Proof.
    rewrite pose_hash2_expand.
    rewrite cm_old_expand.
    with_strategy transparent [nf_old OrchardProtocolSpec.nullifier]
      (unfold nf_old, OrchardProtocolSpec.nullifier).
    reflexivity.
  Qed.

  Lemma t_nf_spec_of (w : HonestInput) :
    t_nf_spec (tables_of w) = nf_old w.
  Proof.
    change (t_nf_spec (tables_of w)) with
      (EccSpec.extract_x
        (EccSpec.point_add
          (OrchardProtocolSpec.mul_nullifier_k
            (State.x0 (List.nth 36 (pose_states_of w) state0)
              +F hi_psi_old w))
          (EccSpec.point_add
            (hd_out (hash_data_of note_commit_Q
              (split_pieces note_commit_lens (note_commit_old_words w))))
            (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w))))).
    exact (nf_expand_eq w).
  Qed.

  Lemma t_nc_new_hash_of (w : HonestInput) :
    t_nc_new_hash (tables_of w) =
      hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_new_words w)).
  Proof.
    change (t_nc_new_hash (tables_of w)) with
      (hash_data_of note_commit_Q
        (split_pieces note_commit_lens
          (OrchardSpec.note_commit_message (hi_g_d_new w) (hi_pk_d_new w)
            (hi_v_new w)
            (EccSpec.extract_x
              (EccSpec.point_add
                (OrchardProtocolSpec.mul_nullifier_k
                  (State.x0 (List.nth 36 (pose_states_of w) state0)
                    +F hi_psi_old w))
                (EccSpec.point_add
                  (hd_out (hash_data_of note_commit_Q
                    (split_pieces note_commit_lens
                      (note_commit_old_words w))))
                  (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)))))
            (hi_psi_new w)))).
    rewrite nf_expand_eq.
    unfold note_commit_new_words, rho_new.
    reflexivity.
  Qed.

  Lemma t_civk_hash_of (w : HonestInput) :
    t_civk_hash (tables_of w) =
      hash_data_of commit_ivk_Q
        (split_pieces commit_ivk_lens (commit_ivk_words w)).
  Proof. reflexivity. Qed.

  (** ** Nondegeneracy: the chord divisors are nonzero

      [nondegenerate w]'s per-hash clauses give distinct x-coordinates; with
      the reduced accumulator abscissa this makes the second chord's divisor
      a nonzero field element (the first chord's divisor is not consumed by
      the gate identities). *)

  Definition rr_next (A G : Point.t) : Point.t :=
    EccSpec.point_add_incomplete (rr_mid A G) A.

  Lemma binop_sub_reduced (a b : Z) :
    0 <= BinOp.sub a b < Primes.pallas_p.
  Proof.
    unfold BinOp.sub.
    apply Z.mod_pos_bound.
    unfold Primes.pallas_p, Primes.t_p.
    lia.
  Qed.

  Lemma mid_x_reduced (A G : Point.t) :
    0 <= Point.x (rr_mid A G) < Primes.pallas_p.
  Proof.
    unfold rr_mid, EccSpec.point_add_incomplete, IncompleteAddition.output,
      square.
    cbn [Point.x].
    apply binop_sub_reduced.
  Qed.

  Lemma acc_x_reduced (Q : Point.t) (ws : list Z) (j : nat) :
    0 <= Point.x Q < Primes.pallas_p ->
    0 <= Point.x (sinsemilla_acc Q ws j) < Primes.pallas_p.
  Proof.
    intros HQ.
    with_strategy transparent [SinsemillaSpec.sinsemilla_hash_to_point]
      (unfold sinsemilla_acc, SinsemillaSpec.sinsemilla_hash_to_point).
    generalize (List.firstn j ws); intros l.
    revert Q HQ.
    induction l as [| word l IH]; intros Q HQ; cbn
      [Stdlib.Lists.List.fold_left].
    - exact HQ.
    - apply IH.
      unfold SinsemillaSpec.round, EccSpec.point_add_incomplete,
        IncompleteAddition.output, square.
      cbn [Point.x].
      apply binop_sub_reduced.
  Qed.

  Lemma chord2_nonzero (Q : Point.t) (ws : list Z) (j : nat)
      (HQ : 0 <= Point.x Q < Primes.pallas_p)
      (Hj : (j < List.length ws)%nat)
      (Hnd : SinsemillaHash.nondegenerate Q ws) :
    BinOp.sub
      (Point.x (rr_mid (sinsemilla_acc Q ws j)
        (SinsemillaSpec.generator (List.nth j ws 0))))
      (Point.x (sinsemilla_acc Q ws j)) <> 0.
  Proof.
    destruct (Hnd j Hj) as [_ Hneq].
    intros Hzero.
    apply sub_zero_equiv in Hzero.
    unfold UnOp.from in Hzero.
    rewrite (Z.mod_small _ _ (mid_x_reduced _ _)) in Hzero.
    rewrite (Z.mod_small _ _ (acc_x_reduced Q ws j HQ)) in Hzero.
    exact (Hneq (eq_sym Hzero)).
  Qed.

  (** ** The congruence toolkit

      Everything below runs modulo the Pallas prime through [Zdiv.eqm]:
      the goal and the chord/definition facts are stripped of inner [mod]s
      through the [eqm] morphisms, and the gate identities close by a linear
      combination of the facts plus [ring]. *)

  #[local] Instance eqm_iff_proper (q : Z) :
    Proper (Zdiv.eqm q ==> Zdiv.eqm q ==> iff) (Zdiv.eqm q).
  Proof.
    intros a b Hab c d Hcd.
    unfold Zdiv.eqm in *.
    split; congruence.
  Qed.

  Lemma eqm_diff_zero (q A B : Z) :
    Zdiv.eqm q A B -> (A - B) mod q = 0.
  Proof.
    unfold Zdiv.eqm.
    intros HAB.
    rewrite Zdiv.Zminus_mod, HAB, Z.sub_diag.
    apply Zdiv.Zmod_0_l.
  Qed.

  Lemma eqm_lin1 (q X Y A1 B1 c1 : Z) :
    Zdiv.eqm q A1 B1 ->
    X - Y = c1 * (A1 - B1) ->
    Zdiv.eqm q X Y.
  Proof.
    intros H1 Hpoly.
    unfold Zdiv.eqm.
    replace X with (Y + c1 * (A1 - B1)) by lia.
    rewrite Zdiv.Zplus_mod, Zdiv.Zmult_mod, (eqm_diff_zero q A1 B1 H1),
      Z.mul_0_r, Zdiv.Zmod_0_l, Z.add_0_r, Zdiv.Zmod_mod.
    reflexivity.
  Qed.

  Lemma eqm_lin2 (q X Y A1 B1 A2 B2 c1 c2 : Z) :
    Zdiv.eqm q A1 B1 ->
    Zdiv.eqm q A2 B2 ->
    X - Y = c1 * (A1 - B1) + c2 * (A2 - B2) ->
    Zdiv.eqm q X Y.
  Proof.
    intros H1 H2 Hpoly.
    unfold Zdiv.eqm.
    replace X with (Y + c1 * (A1 - B1) + c2 * (A2 - B2)) by lia.
    rewrite Zdiv.Zplus_mod, (Zdiv.Zmult_mod c2), (eqm_diff_zero q A2 B2 H2),
      Z.mul_0_r, Zdiv.Zmod_0_l, Z.add_0_r, Zdiv.Zmod_mod.
    rewrite Zdiv.Zplus_mod, (Zdiv.Zmult_mod c1), (eqm_diff_zero q A1 B1 H1),
      Z.mul_0_r, Zdiv.Zmod_0_l, Z.add_0_r, Zdiv.Zmod_mod.
    reflexivity.
  Qed.

  Lemma eqm_of_ring (q X Y : Z) : X - Y = 0 -> Zdiv.eqm q X Y.
  Proof.
    intros Hpoly.
    unfold Zdiv.eqm.
    replace X with Y by lia.
    reflexivity.
  Qed.

  (** The definitional congruences of one round's derived points, over the
      folded atoms [rr_l1]/[rr_l2]/[rr_mid]/[rr_next]. *)

  Lemma mid_x_eqm (A G : Point.t) :
    Zdiv.eqm Primes.pallas_p
      (Point.x (rr_mid A G))
      (rr_l1 A G * rr_l1 A G - Point.x A - Point.x G).
  Proof.
    change (Point.x (rr_mid A G)) with
      (BinOp.sub (BinOp.sub (BinOp.mul (rr_l1 A G) (rr_l1 A G)) (Point.x A))
        (Point.x G)).
    unfold Zdiv.eqm, BinOp.sub, BinOp.mul.
    change (Zdiv.eqm Primes.pallas_p
      ((rr_l1 A G * rr_l1 A G) mod Primes.pallas_p - Point.x A -
        Point.x G)
      (rr_l1 A G * rr_l1 A G - Point.x A - Point.x G)).
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    reflexivity.
  Qed.

  Lemma mid_y_eqm (A G : Point.t) :
    Zdiv.eqm Primes.pallas_p
      (Point.y (rr_mid A G))
      (rr_l1 A G * (Point.x A - Point.x (rr_mid A G)) - Point.y A).
  Proof.
    change (Point.y (rr_mid A G)) with
      (BinOp.sub
        (BinOp.mul (rr_l1 A G) (BinOp.sub (Point.x A) (Point.x (rr_mid A G))))
        (Point.y A)).
    unfold Zdiv.eqm, BinOp.sub, BinOp.mul.
    change (Zdiv.eqm Primes.pallas_p
      ((rr_l1 A G *
        ((Point.x A - Point.x (rr_mid A G)) mod Primes.pallas_p))
        mod Primes.pallas_p - Point.y A)
      (rr_l1 A G * (Point.x A - Point.x (rr_mid A G)) - Point.y A)).
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    reflexivity.
  Qed.

  Lemma nxt_x_eqm (A G : Point.t) :
    Zdiv.eqm Primes.pallas_p
      (Point.x (rr_next A G))
      (rr_l2 A G * rr_l2 A G - Point.x (rr_mid A G) - Point.x A).
  Proof.
    change (Point.x (rr_next A G)) with
      (BinOp.sub
        (BinOp.sub (BinOp.mul (rr_l2 A G) (rr_l2 A G))
          (Point.x (rr_mid A G)))
        (Point.x A)).
    unfold Zdiv.eqm, BinOp.sub, BinOp.mul.
    change (Zdiv.eqm Primes.pallas_p
      ((rr_l2 A G * rr_l2 A G) mod Primes.pallas_p -
        Point.x (rr_mid A G) - Point.x A)
      (rr_l2 A G * rr_l2 A G - Point.x (rr_mid A G) - Point.x A)).
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    reflexivity.
  Qed.

  Lemma nxt_y_eqm (A G : Point.t) :
    Zdiv.eqm Primes.pallas_p
      (Point.y (rr_next A G))
      (rr_l2 A G * (Point.x (rr_mid A G) - Point.x (rr_next A G)) -
        Point.y (rr_mid A G)).
  Proof.
    change (Point.y (rr_next A G)) with
      (BinOp.sub
        (BinOp.mul (rr_l2 A G)
          (BinOp.sub (Point.x (rr_mid A G)) (Point.x (rr_next A G))))
        (Point.y (rr_mid A G))).
    unfold Zdiv.eqm, BinOp.sub, BinOp.mul.
    change (Zdiv.eqm Primes.pallas_p
      ((rr_l2 A G *
        ((Point.x (rr_mid A G) - Point.x (rr_next A G)) mod Primes.pallas_p))
        mod Primes.pallas_p - Point.y (rr_mid A G))
      (rr_l2 A G * (Point.x (rr_mid A G) - Point.x (rr_next A G)) -
        Point.y (rr_mid A G))).
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    reflexivity.
  Qed.

  (** The second chord's exactness: with a nonzero divisor, the witnessed
      gradient times the chord run is the chord rise. *)
  Lemma chord2_mul (A G : Point.t)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
    Zdiv.eqm Primes.pallas_p
      (rr_l2 A G * (Point.x (rr_mid A G) - Point.x A))
      (Point.y (rr_mid A G) - Point.y A).
  Proof.
    assert (Hp2 : 2 < Primes.pallas_p)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    assert (Hden :
        BinOp.sub (Point.x (rr_mid A G)) (Point.x A) mod Primes.pallas_p
          <> 0).
    { unfold BinOp.sub.
      rewrite Zdiv.Zmod_mod.
      exact Hnd. }
    pose proof (div_mul
      (BinOp.sub (Point.y (rr_mid A G)) (Point.y A))
      (BinOp.sub (Point.x (rr_mid A G)) (Point.x A))
      Hp2 Hden) as Hmul.
    change (BinOp.div (BinOp.sub (Point.y (rr_mid A G)) (Point.y A))
        (BinOp.sub (Point.x (rr_mid A G)) (Point.x A)))
      with (rr_l2 A G) in Hmul.
    unfold Zdiv.eqm.
    unfold BinOp.mul, BinOp.sub in Hmul.
    rewrite Zdiv.Zmult_mod_idemp_r in Hmul.
    rewrite Zdiv.Zmod_mod in Hmul.
    exact Hmul.
  Qed.

End OrchardForwardSinsemilla.
