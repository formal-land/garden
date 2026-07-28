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
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
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

  (** The Poseidon schedule iterate is opaque to the kernel from here on: a
      conversion between [poseidon_round_state w 36] and
      [poseidon_state (poseidon_input_state w) 36] (both spellings of the
      36-round chain at the concrete count) would normalize the round chain on
      the lazy machine (the [3^36] trap of [docs/compile-performance.md]); with
      the constant opaque the kernel matches the two through the single
      [poseidon_round_state] delta instead of reducing either side. *)
  #[local] Opaque poseidon_state.

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

  #[local] Instance eqm_equiv (q : Z) : Equivalence (Zdiv.eqm q).
  Proof.
    unfold Zdiv.eqm; split;
      [intro | intros ? ? | intros ? ? ?]; congruence.
  Qed.

  #[local] Instance eqm_iff_proper (q : Z) :
    Proper (Zdiv.eqm q ==> Zdiv.eqm q ==> iff) (Zdiv.eqm q).
  Proof.
    intros a b Hab c d Hcd.
    unfold Zdiv.eqm in *.
    split; congruence.
  Qed.

  (** The [Zdiv.eqm] ring morphisms as instances, so [setoid_rewrite] with
      the [BinOp]-to-[eqm] lemmas below descends through the products and
      differences of the point-addition formula and strips the guarding [mod]s
      (keeping [eqm] folded and never normalizing the chord folds). *)
  #[local] Existing Instances Zdiv.Zplus_eqm Zdiv.Zmult_eqm Zdiv.Zopp_eqm
    Zdiv.Zminus_eqm.

  (** Each field product/difference is [eqm]-congruent to its integer
      counterpart.  Rewriting the syntactic [BinOp.sub]/[BinOp.mul] of the
      point-addition formula with these strips the outer [mod]s while leaving a
      folded gradient ([rr_l1]/[rr_l2], itself a [BinOp.div]) untouched, so the
      two sides never desynchronize on the hidden inverse. *)
  Lemma binop_sub_eqm (x y : Z) :
    Zdiv.eqm Primes.pallas_p (BinOp.sub x y) (x - y).
  Proof. unfold BinOp.sub. apply Zdiv.Zmod_eqm. Qed.

  Lemma binop_mul_eqm (x y : Z) :
    Zdiv.eqm Primes.pallas_p (BinOp.mul x y) (x * y).
  Proof. unfold BinOp.mul. apply Zdiv.Zmod_eqm. Qed.

  (** The incomplete-addition output coordinates as [BinOp] terms over the
      chord gradient, stated over variable summands.  Proved by [reflexivity]
      on the abstract points, so the gradient's field inverse is never forced;
      [rewrite]ing with these at a concrete (possibly compound) summand only
      instantiates the lemma, so the [rr_mid]/[rr_next] chord folds stay
      folded (a direct [change] at [rr_next A G] converts through the doubly
      nested gradient and is quadratically expensive). *)
  Lemma padd_x (P Q : Point.t) :
    Point.x (EccSpec.point_add_incomplete P Q) =
      BinOp.sub (BinOp.sub (BinOp.mul (rr_l1 P Q) (rr_l1 P Q)) (Point.x P))
        (Point.x Q).
  Proof. reflexivity. Qed.

  Lemma padd_y (P Q : Point.t) :
    Point.y (EccSpec.point_add_incomplete P Q) =
      BinOp.sub
        (BinOp.mul (rr_l1 P Q)
          (BinOp.sub (Point.x P)
            (Point.x (EccSpec.point_add_incomplete P Q))))
        (Point.y P).
  Proof. reflexivity. Qed.

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
    generalize (rr_l1 A G); intro l1.
    repeat (setoid_rewrite binop_mul_eqm || setoid_rewrite binop_sub_eqm).
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
    generalize (rr_l1 A G); intro l1.
    generalize (Point.x (rr_mid A G)); intro xm.
    repeat (setoid_rewrite binop_mul_eqm || setoid_rewrite binop_sub_eqm).
    reflexivity.
  Qed.

  (** From here the middle chord point [rr_mid] and the field inverse are
      opaque to the kernel: the [rr_next] chord identities relate a doubly
      nested gradient ([rr_l1 (rr_mid A G) A]) to [rr_l2 A G], and converting
      those spellings by unfolding [rr_mid] normalizes the point-addition
      coordinates through the inverse — quadratically expensive.  With the two
      constants opaque the equal spellings match as stuck atoms. *)
  #[local] Opaque rr_mid mod_inverse.

  Lemma nxt_y_eqm (A G : Point.t) :
    Zdiv.eqm Primes.pallas_p
      (Point.y (rr_next A G))
      (rr_l2 A G * (Point.x (rr_mid A G) - Point.x (rr_next A G)) -
        Point.y (rr_mid A G)).
  Proof.
    unfold rr_next.
    rewrite (padd_y (rr_mid A G) A).
    change (rr_l1 (rr_mid A G) A) with (rr_l2 A G).
    generalize (rr_l2 A G); intro l2.
    generalize (Point.x (EccSpec.point_add_incomplete (rr_mid A G) A)); intro xn.
    generalize (Point.x (rr_mid A G)); intro xm.
    generalize (Point.y (rr_mid A G)); intro ym.
    repeat (setoid_rewrite binop_mul_eqm || setoid_rewrite binop_sub_eqm).
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

  (** ** The round points as [BinOp] terms

      The coordinates of the two derived points of a round, spelled with the
      field operations of the gate bodies.  Stated as explicit-right-hand-side
      lemmas so a consumer [rewrite]s instead of converting through
      [rr_mid]'s hidden inverse. *)

  Lemma mid_x_def (A G : Point.t) :
    Point.x (rr_mid A G) =
      BinOp.sub (BinOp.sub (BinOp.mul (rr_l1 A G) (rr_l1 A G)) (Point.x A))
        (Point.x G).
  Proof. with_strategy transparent [rr_mid] (unfold rr_mid). apply padd_x. Qed.

  Lemma nxt_x_def (A G : Point.t) :
    Point.x (rr_next A G) =
      BinOp.sub (BinOp.sub (BinOp.mul (rr_l2 A G) (rr_l2 A G))
        (Point.x (rr_mid A G))) (Point.x A).
  Proof. unfold rr_next. apply (padd_x (rr_mid A G) A). Qed.

  (** The two gradients and the field division are opaque to the kernel from
      here on: the mod-stripping [setoid_rewrite] of [mod_ring_solve] matches
      its pattern up to conversion, so a transparent gradient would be
      unfolded on one side of a goal and left folded on the other, and the two
      spellings would then have to be reconciled through the inverse. *)
  #[local] Opaque rr_l1 rr_l2 BinOp.div.

  (** ** The gate bodies at one round

      Each body is discharged over an abstract assignment from the round's
      cell values; the region dispatch below supplies those from the
      generator.  The chord identities enter through [chord2_mul], so the
      only side condition is the round's non-vertical second chord. *)

  (** The "Secant line" body: [λ₂² = x_a(next) + x_r + x_a], where [x_r] is the
      middle point's abscissa. *)
  Lemma secant_eval (Gamma : Assignment.t columns RegionId.t)
      (q2 : Fixed.t) (xa xp l1 l2 : Advice.t)
      (region : RegionId.t) (row : Z) (A G : Point.t)
      (Hxa : Gamma.(Assignment.advice) xa region row = Point.x A)
      (Hxp : Gamma.(Assignment.advice) xp region row = Point.x G)
      (Hl1 : Gamma.(Assignment.advice) l1 region row = rr_l1 A G)
      (Hl2 : Gamma.(Assignment.advice) l2 region row = rr_l2 A G)
      (Hxa' : Gamma.(Assignment.advice) xa region (row + 1) =
        Point.x (rr_next A G)) :
    eval_constraint Gamma (region, row) (secant_body q2 xa xp l1 l2).
  Proof.
    unfold secant_body, body_at.
    cbn [SChip.sinsemilla_gate Gate.constraints Constraints.with_selector
      List.map List.nth_error].
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p] cbn.
    cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    rewrite ?Z.add_0_r.
    rewrite ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hxa'.
    rewrite nxt_x_def, mid_x_def.
    mod_ring_solve.
  Qed.

  (** One step of a linear combination of congruences: shifting the left side
      by a multiple of a known congruence keeps the goal. *)
  Lemma eqm_cons (q X Y A B c : Z) (H : Zdiv.eqm q A B)
      (Hrest : Zdiv.eqm q (X - c * (A - B)) Y) : Zdiv.eqm q X Y.
  Proof.
    transitivity (X - c * (A - B)).
    - exact (eqm_lin1 q X (X - c * (A - B)) A B c H ltac:(ring)).
    - exact Hrest.
  Qed.

  (** The chip's doubled ordinate [y_a] at a round row is twice the
      accumulator's ordinate: [λ₁] contributes [y_mid + y_a] by the
      middle point's definition, [λ₂] contributes [y_a − y_mid] by the second
      chord's exactness. *)
  Lemma ya_row_eqm (A G : Point.t)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
    Zdiv.eqm Primes.pallas_p
      ((rr_l1 A G + rr_l2 A G) *
        (Point.x A - (rr_l1 A G * rr_l1 A G - Point.x A - Point.x G)))
      (2 * Point.y A).
  Proof.
    apply (eqm_cons _ _ _ _ _ (rr_l1 A G + rr_l2 A G) (mid_x_eqm A G)).
    apply (eqm_cons _ _ _ _ _ (-1) (mid_y_eqm A G)).
    apply (eqm_cons _ _ _ _ _ (-1) (chord2_mul A G Hnd)).
    apply eqm_of_ring. ring.
  Qed.

  (** The second chord over the whole round: its gradient times the run from
      the accumulator to the round's output is the sum of the two ordinates. *)
  Lemma chord_next_eqm (A G : Point.t)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
    Zdiv.eqm Primes.pallas_p
      (rr_l2 A G * (Point.x A - Point.x (rr_next A G)))
      (Point.y A + Point.y (rr_next A G)).
  Proof.
    apply (eqm_cons _ _ _ _ _ (-1) (nxt_y_eqm A G)).
    apply (eqm_cons _ _ _ _ _ (-1) (chord2_mul A G Hnd)).
    apply eqm_of_ring. ring.
  Qed.

  (** Turn a reduced-form equality goal into the congruence it abbreviates and
      strip every inner [mod]. *)
  Ltac to_eqm :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from;
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end;
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).

  (** Replace the round's cell values by opaque variables before stripping the
      [mod]s: the stripping rewrite matches up to conversion, and a folded
      gradient or accumulator coordinate left in place would be unfolded
      through the point-addition formula. *)
  Ltac sins_abstract A G G' :=
    remember (rr_l1 A G) as L1 in *;
    remember (rr_l2 A G) as L2 in *;
    remember (rr_l1 (rr_next A G) G') as L1' in *;
    remember (rr_l2 (rr_next A G) G') as L2' in *;
    remember (Point.x (rr_next A G)) as xN in *;
    remember (Point.y (rr_next A G)) as yN in *;
    remember (Point.x A) as xA in *;
    remember (Point.y A) as yA in *;
    remember (Point.x G) as xG in *;
    remember (Point.x G') as xG' in *.

  Ltac sins_abstract_fin A G :=
    remember (rr_l1 A G) as L1 in *;
    remember (rr_l2 A G) as L2 in *;
    remember (Point.x (rr_next A G)) as xN in *;
    remember (Point.y (rr_next A G)) as yN in *;
    remember (Point.x A) as xA in *;
    remember (Point.y A) as yA in *;
    remember (Point.x G) as xG in *.

  (** The "y check" body at an interior round row, where the next row carries
      the following round and [q_sinsemilla2] is [0] or [1] (so [q_s3] is
      [0]): four times the chord run equals twice each row's doubled
      ordinate. *)
  Lemma ycheck_interior_eval (Gamma : Assignment.t columns RegionId.t)
      (q2 : Fixed.t) (xa xp l1 l2 : Advice.t)
      (region : RegionId.t) (row : Z) (A G G' : Point.t)
      (Hxa : Gamma.(Assignment.advice) xa region row = Point.x A)
      (Hxp : Gamma.(Assignment.advice) xp region row = Point.x G)
      (Hl1 : Gamma.(Assignment.advice) l1 region row = rr_l1 A G)
      (Hl2 : Gamma.(Assignment.advice) l2 region row = rr_l2 A G)
      (Hxa' : Gamma.(Assignment.advice) xa region (row + 1) =
        Point.x (rr_next A G))
      (Hxp' : Gamma.(Assignment.advice) xp region (row + 1) = Point.x G')
      (Hl1' : Gamma.(Assignment.advice) l1 region (row + 1) =
        rr_l1 (rr_next A G) G')
      (Hl2' : Gamma.(Assignment.advice) l2 region (row + 1) =
        rr_l2 (rr_next A G) G')
      (Hq2 : Gamma.(Assignment.fixed) q2 region row = 0 \/
        Gamma.(Assignment.fixed) q2 region row = 1)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0)
      (Hnd' : BinOp.sub (Point.x (rr_mid (rr_next A G) G'))
        (Point.x (rr_next A G)) <> 0) :
    eval_constraint Gamma (region, row) (ycheck_body q2 xa xp l1 l2).
  Proof.
    pose proof (ya_row_eqm A G Hnd) as F1.
    pose proof (ya_row_eqm (rr_next A G) G' Hnd') as F2.
    pose proof (chord_next_eqm A G Hnd) as F3.
    clear Hnd Hnd'.
    unfold ycheck_body, body_at.
    cbn [SChip.sinsemilla_gate Gate.constraints Constraints.with_selector
      List.map List.nth_error].
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p] cbn.
    cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    rewrite ?Z.add_0_r.
    rewrite ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hxa', ?Hxp', ?Hl1', ?Hl2'.
    clear Hxa Hxp Hl1 Hl2 Hxa' Hxp' Hl1' Hl2'.
    destruct Hq2 as [Hq2 | Hq2]; rewrite Hq2; clear Hq2;
      sins_abstract A G G'; to_eqm.
    all: apply (eqm_cons _ _ _ _ _ (-2) F1);
         apply (eqm_cons _ _ _ _ _ (-2) F2);
         apply (eqm_cons _ _ _ _ _ 4 F3);
         apply eqm_of_ring; ring.
  Qed.

  (** The "y check" body at the final round row, where [q_sinsemilla2] is [2]
      (so [q_s3] is [2]): the next-row [y_a] term drops out and the output
      point's ordinate enters through the [λ₁] cell of the output row. *)
  Lemma ycheck_final_eval (Gamma : Assignment.t columns RegionId.t)
      (q2 : Fixed.t) (xa xp l1 l2 : Advice.t)
      (region : RegionId.t) (row : Z) (A G : Point.t)
      (Hxa : Gamma.(Assignment.advice) xa region row = Point.x A)
      (Hxp : Gamma.(Assignment.advice) xp region row = Point.x G)
      (Hl1 : Gamma.(Assignment.advice) l1 region row = rr_l1 A G)
      (Hl2 : Gamma.(Assignment.advice) l2 region row = rr_l2 A G)
      (Hxa' : Gamma.(Assignment.advice) xa region (row + 1) =
        Point.x (rr_next A G))
      (Hxp' : Gamma.(Assignment.advice) xp region (row + 1) = 0)
      (Hl1' : Gamma.(Assignment.advice) l1 region (row + 1) =
        Point.y (rr_next A G))
      (Hl2' : Gamma.(Assignment.advice) l2 region (row + 1) = 0)
      (Hq2 : Gamma.(Assignment.fixed) q2 region row = 2)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
    eval_constraint Gamma (region, row) (ycheck_body q2 xa xp l1 l2).
  Proof.
    pose proof (ya_row_eqm A G Hnd) as F1.
    pose proof (chord_next_eqm A G Hnd) as F3.
    clear Hnd.
    unfold ycheck_body, body_at.
    cbn [SChip.sinsemilla_gate Gate.constraints Constraints.with_selector
      List.map List.nth_error].
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p] cbn.
    cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    rewrite ?Z.add_0_r.
    rewrite ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hxa', ?Hxp', ?Hl1', ?Hl2', ?Hq2.
    clear Hxa Hxp Hl1 Hl2 Hxa' Hxp' Hl1' Hl2' Hq2.
    sins_abstract_fin A G; to_eqm.
    apply (eqm_cons _ _ _ _ _ (-2) F1).
    apply (eqm_cons _ _ _ _ _ 4 F3).
    apply eqm_of_ring. ring.
  Qed.

  (** The "Initial y_Q" body: the fixed domain ordinate doubled is the row's
      doubled [y_a]. *)
  Lemma init_eval (Gamma : Assignment.t columns RegionId.t)
      (yq : Fixed.t) (xa xp l1 l2 : Advice.t)
      (region : RegionId.t) (row : Z) (A G : Point.t)
      (Hxa : Gamma.(Assignment.advice) xa region row = Point.x A)
      (Hxp : Gamma.(Assignment.advice) xp region row = Point.x G)
      (Hl1 : Gamma.(Assignment.advice) l1 region row = rr_l1 A G)
      (Hl2 : Gamma.(Assignment.advice) l2 region row = rr_l2 A G)
      (Hyq : Gamma.(Assignment.fixed) yq region row = Point.y A)
      (Hnd : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
    eval_constraint Gamma (region, row) (init_body yq xa xp l1 l2).
  Proof.
    pose proof (ya_row_eqm A G Hnd) as F1.
    clear Hnd.
    unfold init_body, body_at.
    cbn [SChip.initial_y_q_gate Gate.constraints Constraints.with_selector
      List.map List.nth_error].
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p] cbn.
    cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    rewrite ?Z.add_0_r.
    rewrite ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hyq.
    clear Hxa Hxp Hl1 Hl2 Hyq.
    sins_abstract_fin A G; to_eqm.
    apply (eqm_cons _ _ _ _ _ (-1) F1).
    apply eqm_of_ring. ring.
  Qed.

  (** The accumulator after one more round is the round's chord output. *)
  Lemma round_rr_next (A : Point.t) (word : Z) :
    SinsemillaSpec.round A word = rr_next A (SinsemillaSpec.generator word).
  Proof.
    unfold rr_next, SinsemillaSpec.round.
    with_strategy transparent [rr_mid] (unfold rr_mid).
    reflexivity.
  Qed.

  Lemma acc_succ_next (Q : Point.t) (ws : list Z) (j : nat)
      (Hj : (j < List.length ws)%nat) :
    sinsemilla_acc Q ws (S j) =
      rr_next (sinsemilla_acc Q ws j)
        (SinsemillaSpec.generator (List.nth j ws 0)).
  Proof. rewrite (sinsemilla_acc_succ Q ws j Hj). apply round_rr_next. Qed.

  (** ** The gate obligations of one hash region

      At a round row of a hash region whose advice plane is the region's
      [hash_region_advice_t] reader, both [sinsemilla_gate] bodies hold: the
      cell values are the fold's accumulator, generator and gradients, the
      row's [q_sinsemilla2] value selects the interior or the final shape, and
      [SinsemillaHash.nondegenerate] supplies each round's non-vertical second
      chord. *)
  Lemma hash_region_gates
      (Gamma : Assignment.t columns RegionId.t)
      (Q : Point.t) (pieces : list (list Z)) (second : bool)
      (region : RegionId.t) (j : nat)
      (HQ : 0 <= Point.x Q < Primes.pallas_p)
      (Hnd : SinsemillaHash.nondegenerate Q (Stdlib.Lists.List.concat pieces))
      (Hadv : forall (col : Advice.t) (r : Z),
        Gamma.(Assignment.advice) col region r =
          hash_region_advice_t (hash_data_of Q pieces) second col r)
      (Hj : (j < List.length (Stdlib.Lists.List.concat pieces))%nat)
      (Hq2 : if (j =? List.length (Stdlib.Lists.List.concat pieces) - 1)%nat
        then Gamma.(Assignment.fixed) (q2_col second) region (Z.of_nat j) = 2
        else Gamma.(Assignment.fixed) (q2_col second) region (Z.of_nat j) = 0 \/
             Gamma.(Assignment.fixed) (q2_col second) region (Z.of_nat j) = 1)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [secant_body (q2_col second) (xa_col second) (xp_col second)
          (l1_col second) (l2_col second);
         ycheck_body (q2_col second) (xa_col second) (xp_col second)
          (l1_col second) (l2_col second)]) :
    eval_constraint Gamma (region, Z.of_nat j) body.
  Proof.
    set (A := sinsemilla_acc Q (Stdlib.Lists.List.concat pieces) j).
    set (G := SinsemillaSpec.generator
      (List.nth j (Stdlib.Lists.List.concat pieces) 0)).
    assert (Hxa : Gamma.(Assignment.advice) (xa_col second) region
      (Z.of_nat j) = Point.x A).
    { rewrite Hadv. exact (hash_cell_xa Q pieces second j ltac:(lia)). }
    assert (Hxp : Gamma.(Assignment.advice) (xp_col second) region
      (Z.of_nat j) = Point.x G).
    { rewrite Hadv. exact (hash_cell_xp Q pieces second j Hj). }
    assert (Hl1 : Gamma.(Assignment.advice) (l1_col second) region
      (Z.of_nat j) = rr_l1 A G).
    { rewrite Hadv. exact (hash_cell_l1 Q pieces second j Hj). }
    assert (Hl2 : Gamma.(Assignment.advice) (l2_col second) region
      (Z.of_nat j) = rr_l2 A G).
    { rewrite Hadv. exact (hash_cell_l2 Q pieces second j Hj). }
    assert (Hsucc : sinsemilla_acc Q (Stdlib.Lists.List.concat pieces) (S j) =
      rr_next A G) by exact (acc_succ_next Q _ j Hj).
    assert (Hxa' : Gamma.(Assignment.advice) (xa_col second) region
      (Z.of_nat j + 1) = Point.x (rr_next A G)).
    { rewrite Hadv.
      replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
      rewrite (hash_cell_xa Q pieces second (S j) ltac:(lia)).
      rewrite Hsucc. reflexivity. }
    assert (Hndj : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0)
      by exact (chord2_nonzero Q _ j HQ Hj Hnd).
    destruct Hbody as [<- | [<- | Habs] ]; [ | | destruct Habs].
    { exact (secant_eval Gamma _ _ _ _ _ region (Z.of_nat j) A G
        Hxa Hxp Hl1 Hl2 Hxa'). }
    destruct (Nat.eq_dec (S j) (List.length (Stdlib.Lists.List.concat pieces)))
      as [Hfin | Hint].
    - assert (Hq2f : Gamma.(Assignment.fixed) (q2_col second) region
        (Z.of_nat j) = 2).
      { rewrite (proj2 (Nat.eqb_eq j
          (List.length (Stdlib.Lists.List.concat pieces) - 1)) ltac:(lia))
          in Hq2. exact Hq2. }
      assert (Hxp' : Gamma.(Assignment.advice) (xp_col second) region
        (Z.of_nat j + 1) = 0).
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with
          (Z.of_nat (List.length (Stdlib.Lists.List.concat pieces))) by lia.
        exact (hash_cell_xp_out Q pieces second). }
      assert (Hl2' : Gamma.(Assignment.advice) (l2_col second) region
        (Z.of_nat j + 1) = 0).
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with
          (Z.of_nat (List.length (Stdlib.Lists.List.concat pieces))) by lia.
        exact (hash_cell_l2_out Q pieces second). }
      assert (Hl1' : Gamma.(Assignment.advice) (l1_col second) region
        (Z.of_nat j + 1) = Point.y (rr_next A G)).
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with
          (Z.of_nat (List.length (Stdlib.Lists.List.concat pieces))) by lia.
        rewrite (hash_cell_yout Q pieces second).
        rewrite <- Hfin, Hsucc. reflexivity. }
      exact (ycheck_final_eval Gamma _ _ _ _ _ region (Z.of_nat j) A G
        Hxa Hxp Hl1 Hl2 Hxa' Hxp' Hl1' Hl2' Hq2f Hndj).
    - assert (HjS : (S j < List.length (Stdlib.Lists.List.concat pieces))%nat)
        by lia.
      assert (Hq2i : Gamma.(Assignment.fixed) (q2_col second) region
          (Z.of_nat j) = 0 \/
        Gamma.(Assignment.fixed) (q2_col second) region (Z.of_nat j) = 1).
      { rewrite (proj2 (Nat.eqb_neq j
          (List.length (Stdlib.Lists.List.concat pieces) - 1)) ltac:(lia))
          in Hq2. exact Hq2. }
      set (G' := SinsemillaSpec.generator
        (List.nth (S j) (Stdlib.Lists.List.concat pieces) 0)).
      assert (Hxp' : Gamma.(Assignment.advice) (xp_col second) region
        (Z.of_nat j + 1) = Point.x G').
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        exact (hash_cell_xp Q pieces second (S j) HjS). }
      assert (Hl1' : Gamma.(Assignment.advice) (l1_col second) region
        (Z.of_nat j + 1) = rr_l1 (rr_next A G) G').
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        rewrite (hash_cell_l1 Q pieces second (S j) HjS), Hsucc. reflexivity. }
      assert (Hl2' : Gamma.(Assignment.advice) (l2_col second) region
        (Z.of_nat j + 1) = rr_l2 (rr_next A G) G').
      { rewrite Hadv.
        replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        rewrite (hash_cell_l2 Q pieces second (S j) HjS), Hsucc. reflexivity. }
      assert (Hnd' : BinOp.sub (Point.x (rr_mid (rr_next A G) G'))
        (Point.x (rr_next A G)) <> 0).
      { rewrite <- Hsucc. exact (chord2_nonzero Q _ (S j) HQ HjS Hnd). }
      exact (ycheck_interior_eval Gamma _ _ _ _ _ region (Z.of_nat j) A G G'
        Hxa Hxp Hl1 Hl2 Hxa' Hxp' Hl1' Hl2' Hq2i Hndj Hnd').
  Qed.

  (** The "Initial y_Q" body at row [0] of a hash region: the domain point is
      the accumulator there. *)
  Lemma hash_region_init
      (Gamma : Assignment.t columns RegionId.t)
      (Q : Point.t) (pieces : list (list Z)) (second : bool)
      (region : RegionId.t)
      (HQ : 0 <= Point.x Q < Primes.pallas_p)
      (Hnd : SinsemillaHash.nondegenerate Q (Stdlib.Lists.List.concat pieces))
      (Hadv : forall (col : Advice.t) (r : Z),
        Gamma.(Assignment.advice) col region r =
          hash_region_advice_t (hash_data_of Q pieces) second col r)
      (Hpos : (0 < List.length (Stdlib.Lists.List.concat pieces))%nat)
      (Hyq : Gamma.(Assignment.fixed) (yq_col second) region 0 = Point.y Q)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [init_body (yq_col second) (xa_col second) (xp_col second)
          (l1_col second) (l2_col second)]) :
    eval_constraint Gamma (region, 0) body.
  Proof.
    set (G := SinsemillaSpec.generator
      (List.nth 0%nat (Stdlib.Lists.List.concat pieces) 0)).
    assert (Hxa : Gamma.(Assignment.advice) (xa_col second) region 0 =
      Point.x Q).
    { rewrite Hadv.
      change 0 with (Z.of_nat 0%nat) at 1.
      rewrite (hash_cell_xa Q pieces second 0%nat ltac:(lia)).
      rewrite sinsemilla_acc_zero. reflexivity. }
    assert (Hxp : Gamma.(Assignment.advice) (xp_col second) region 0 =
      Point.x G).
    { rewrite Hadv.
      change 0 with (Z.of_nat 0%nat) at 1.
      exact (hash_cell_xp Q pieces second 0%nat Hpos). }
    assert (Hl1 : Gamma.(Assignment.advice) (l1_col second) region 0 =
      rr_l1 Q G).
    { rewrite Hadv.
      change 0 with (Z.of_nat 0%nat) at 1.
      rewrite (hash_cell_l1 Q pieces second 0%nat Hpos).
      rewrite sinsemilla_acc_zero. reflexivity. }
    assert (Hl2 : Gamma.(Assignment.advice) (l2_col second) region 0 =
      rr_l2 Q G).
    { rewrite Hadv.
      change 0 with (Z.of_nat 0%nat) at 1.
      rewrite (hash_cell_l2 Q pieces second 0%nat Hpos).
      rewrite sinsemilla_acc_zero. reflexivity. }
    assert (Hndj : BinOp.sub (Point.x (rr_mid Q G)) (Point.x Q) <> 0).
    { pose proof (chord2_nonzero Q _ 0%nat HQ Hpos Hnd) as Hc.
      rewrite sinsemilla_acc_zero in Hc. exact Hc. }
    destruct Hbody as [<- | Habs]; [ | destruct Habs].
    exact (init_eval Gamma _ _ _ _ _ region 0 Q G Hxa Hxp Hl1 Hl2 Hyq Hndj).
  Qed.

  (** ** The hash regions of the circuit

      The four hash families instantiate the region lemmas at their domain
      point and honest message: the [Merkle] layers, the two [NoteCommit]
      hashes and the [Commit^ivk] hash. *)

  Lemma layer_index_lt (layer : RegionId.Merkle.Layer.t) :
    (Z.to_nat (RegionId.Merkle.Layer.to_index layer) < 32)%nat.
  Proof. destruct layer; cbn; lia. Qed.

  Lemma merkle_hash_len (w : HonestInput) (i : nat) :
    List.length (Stdlib.Lists.List.concat
      (split_pieces merkle_lens (merkle_layer_words w i))) = 52%nat.
  Proof. rewrite merkle_words_concat. apply merkle_words_length. Qed.

  Lemma merkle_hash_adv (w : HonestInput) (layer : RegionId.Merkle.Layer.t)
      (col : Advice.t) (r : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) col
      (merkle_h2p layer) r =
    hash_region_advice_t
      (hash_data_of merkle_Q
        (split_pieces merkle_lens
          (merkle_layer_words w (Z.to_nat
            (RegionId.Merkle.Layer.to_index layer)))))
      (layer_second layer) col r.
  Proof.
    rewrite advice_merkle_h2p.
    rewrite (t_layers_nth w _ (layer_index_lt layer)).
    reflexivity.
  Qed.

  (** The [q_sinsemilla2] hypothesis of [hash_region_gates] at one row, read
      off a region's schedule certificate. *)
  Lemma q2_from_cert (w : HonestInput) (second : bool) (region : RegionId.t)
      (n j : nat)
      (Hj : (j < n)%nat)
      (Hcert : List.forallb (q2_row_ok second region (Z.of_nat n))
        (List.seq 0%nat n) = true) :
    if (j =? n - 1)%nat
    then (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      (q2_col second) region (Z.of_nat j) = 2
    else (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      (q2_col second) region (Z.of_nat j) = 0 \/
     (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      (q2_col second) region (Z.of_nat j) = 1.
  Proof.
    pose proof (proj1 (List.forallb_forall _ _) Hcert j
      ltac:(apply List.in_seq; lia)) as Hrow.
    unfold q2_row_ok in Hrow.
    cbn zeta in Hrow.
    rewrite fixed_at_read.
    destruct (Nat.eq_dec j (n - 1)%nat) as [Heq | Hne].
    - rewrite (proj2 (Nat.eqb_eq j (n - 1)%nat) Heq).
      rewrite (proj2 (Z.eqb_eq (Z.of_nat j) (Z.of_nat n - 1)) ltac:(lia))
        in Hrow.
      exact (proj1 (Z.eqb_eq _ _) Hrow).
    - rewrite (proj2 (Nat.eqb_neq j (n - 1)%nat) Hne).
      rewrite (proj2 (Z.eqb_neq (Z.of_nat j) (Z.of_nat n - 1)) ltac:(lia))
        in Hrow.
      destruct (proj1 (Bool.orb_true_iff _ _) Hrow) as [H0 | H1].
      + left. exact (proj1 (Z.eqb_eq _ _) H0).
      + right. exact (proj1 (Z.eqb_eq _ _) H1).
  Qed.

  Lemma reduced_of_cert (P : Point.t) :
    (0 <=? Point.x P) && (Point.x P <? Primes.pallas_p) &&
    (0 <=? Point.y P) && (Point.y P <? Primes.pallas_p) = true ->
    0 <= Point.x P < Primes.pallas_p.
  Proof.
    intros H.
    apply Bool.andb_true_iff in H; destruct H as [H _].
    apply Bool.andb_true_iff in H; destruct H as [H _].
    apply Bool.andb_true_iff in H; destruct H as [H1 H2].
    split; [ exact (proj1 (Z.leb_le _ _) H1) | exact (proj1 (Z.ltb_lt _ _) H2) ].
  Qed.

  Lemma merkle_gates (w : HonestInput) (Hnd : nondegenerate w)
      (layer : RegionId.Merkle.Layer.t) (row : Z) (Hrow : 0 <= row < 52)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [secant_body (q2_col (layer_second layer))
           (xa_col (layer_second layer)) (xp_col (layer_second layer))
           (l1_col (layer_second layer)) (l2_col (layer_second layer));
         ycheck_body (q2_col (layer_second layer))
           (xa_col (layer_second layer)) (xp_col (layer_second layer))
           (l1_col (layer_second layer)) (l2_col (layer_second layer))]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (merkle_h2p layer, row) body.
  Proof.
    pose proof (proj1 (List.forallb_forall _ _) q2_sched_merkle_cert layer
      (all_layers_complete layer)) as Hq2c.
    cbn beta in Hq2c.
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    apply (hash_region_gates _ merkle_Q
      (split_pieces merkle_lens (merkle_layer_words w
        (Z.to_nat (RegionId.Merkle.Layer.to_index layer))))
      (layer_second layer) (merkle_h2p layer) (Z.to_nat row)).
    - exact (reduced_of_cert merkle_Q merkle_Q_reduced).
    - rewrite merkle_words_concat.
      exact (proj1 Hnd _ (layer_index_lt layer)).
    - intros col r. apply merkle_hash_adv.
    - rewrite merkle_hash_len. lia.
    - rewrite merkle_hash_len.
      exact (q2_from_cert w (layer_second layer) (merkle_h2p layer) 52%nat
        (Z.to_nat row) ltac:(lia) Hq2c).
    - exact Hbody.
  Qed.

  Lemma merkle_init_gate (w : HonestInput) (Hnd : nondegenerate w)
      (layer : RegionId.Merkle.Layer.t) (body : Constraint.t columns)
      (Hbody : List.In body
        [init_body (yq_col (layer_second layer))
           (xa_col (layer_second layer)) (xp_col (layer_second layer))
           (l1_col (layer_second layer)) (l2_col (layer_second layer))]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (merkle_h2p layer, 0) body.
  Proof.
    pose proof (proj1 (List.forallb_forall _ _) yq_merkle_cert layer
      (all_layers_complete layer)) as Hyqc.
    cbn beta in Hyqc.
    apply (hash_region_init _ merkle_Q
      (split_pieces merkle_lens (merkle_layer_words w
        (Z.to_nat (RegionId.Merkle.Layer.to_index layer))))
      (layer_second layer) (merkle_h2p layer)).
    - exact (reduced_of_cert merkle_Q merkle_Q_reduced).
    - rewrite merkle_words_concat.
      exact (proj1 Hnd _ (layer_index_lt layer)).
    - intros col r. apply merkle_hash_adv.
    - rewrite merkle_hash_len. lia.
    - rewrite fixed_at_read. exact (proj1 (Z.eqb_eq _ _) Hyqc).
    - exact Hbody.
  Qed.

  Lemma nc_new_words_concat (w : HonestInput) :
    Stdlib.Lists.List.concat
      (split_pieces note_commit_lens (note_commit_new_words w)) =
    note_commit_new_words w.
  Proof.
    apply concat_split_pieces.
    unfold note_commit_new_words.
    rewrite note_commit_message_length.
    reflexivity.
  Qed.

  Lemma nc_old_hash_len (w : HonestInput) :
    List.length (Stdlib.Lists.List.concat
      (split_pieces note_commit_lens (note_commit_old_words w))) = 109%nat.
  Proof.
    rewrite nc_old_words_concat.
    unfold note_commit_old_words. apply note_commit_message_length.
  Qed.

  Lemma nc_new_hash_len (w : HonestInput) :
    List.length (Stdlib.Lists.List.concat
      (split_pieces note_commit_lens (note_commit_new_words w))) = 109%nat.
  Proof.
    rewrite nc_new_words_concat.
    unfold note_commit_new_words. apply note_commit_message_length.
  Qed.

  Lemma civk_hash_len (w : HonestInput) :
    List.length (Stdlib.Lists.List.concat
      (split_pieces commit_ivk_lens (commit_ivk_words w))) = 51%nat.
  Proof.
    rewrite commit_ivk_words_concat. apply commit_ivk_words_length.
  Qed.

  Lemma nc_old_hash_adv (w : HonestInput) (col : Advice.t) (r : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) col
      (nc_h2p RegionId.NoteCommit.Which.Old) r =
    hash_region_advice_t
      (hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_old_words w))) false col r.
  Proof. rewrite advice_nc_old_h2p, t_nc_old_hash_of. reflexivity. Qed.

  Lemma nc_new_hash_adv (w : HonestInput) (col : Advice.t) (r : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) col
      (nc_h2p RegionId.NoteCommit.Which.New) r =
    hash_region_advice_t
      (hash_data_of note_commit_Q
        (split_pieces note_commit_lens (note_commit_new_words w))) true col r.
  Proof. rewrite advice_nc_new_h2p, t_nc_new_hash_of. reflexivity. Qed.

  Lemma civk_hash_adv (w : HonestInput) (col : Advice.t) (r : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) col
      civk_h2p r =
    hash_region_advice_t
      (hash_data_of commit_ivk_Q
        (split_pieces commit_ivk_lens (commit_ivk_words w))) false col r.
  Proof. rewrite advice_civk_h2p, t_civk_hash_of. reflexivity. Qed.

  Lemma nc_old_gates (w : HonestInput) (Hnd : nondegenerate w)
      (row : Z) (Hrow : 0 <= row < 109) (body : Constraint.t columns)
      (Hbody : List.In body
        [secant_body (q2_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false);
         ycheck_body (q2_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (nc_h2p RegionId.NoteCommit.Which.Old, row) body.
  Proof.
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    apply (hash_region_gates _ note_commit_Q
      (split_pieces note_commit_lens (note_commit_old_words w)) false
      (nc_h2p RegionId.NoteCommit.Which.Old) (Z.to_nat row)).
    - exact (reduced_of_cert note_commit_Q nc_Q_reduced).
    - rewrite nc_old_words_concat. exact (proj1 (proj2 Hnd)).
    - intros col r. apply nc_old_hash_adv.
    - rewrite nc_old_hash_len. lia.
    - rewrite nc_old_hash_len.
      exact (q2_from_cert w false (nc_h2p RegionId.NoteCommit.Which.Old)
        109%nat (Z.to_nat row) ltac:(lia) q2_sched_nc_old_cert).
    - exact Hbody.
  Qed.

  Lemma nc_old_init_gate (w : HonestInput) (Hnd : nondegenerate w)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [init_body (yq_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (nc_h2p RegionId.NoteCommit.Which.Old, 0) body.
  Proof.
    apply (hash_region_init _ note_commit_Q
      (split_pieces note_commit_lens (note_commit_old_words w)) false
      (nc_h2p RegionId.NoteCommit.Which.Old)).
    - exact (reduced_of_cert note_commit_Q nc_Q_reduced).
    - rewrite nc_old_words_concat. exact (proj1 (proj2 Hnd)).
    - intros col r. apply nc_old_hash_adv.
    - rewrite nc_old_hash_len. lia.
    - rewrite fixed_at_read. exact yq_nc_old_cert.
    - exact Hbody.
  Qed.

  Lemma nc_new_gates (w : HonestInput) (Hnd : nondegenerate w)
      (row : Z) (Hrow : 0 <= row < 109) (body : Constraint.t columns)
      (Hbody : List.In body
        [secant_body (q2_col true) (xa_col true) (xp_col true)
           (l1_col true) (l2_col true);
         ycheck_body (q2_col true) (xa_col true) (xp_col true)
           (l1_col true) (l2_col true)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (nc_h2p RegionId.NoteCommit.Which.New, row) body.
  Proof.
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    apply (hash_region_gates _ note_commit_Q
      (split_pieces note_commit_lens (note_commit_new_words w)) true
      (nc_h2p RegionId.NoteCommit.Which.New) (Z.to_nat row)).
    - exact (reduced_of_cert note_commit_Q nc_Q_reduced).
    - rewrite nc_new_words_concat. exact (proj1 (proj2 (proj2 Hnd))).
    - intros col r. apply nc_new_hash_adv.
    - rewrite nc_new_hash_len. lia.
    - rewrite nc_new_hash_len.
      exact (q2_from_cert w true (nc_h2p RegionId.NoteCommit.Which.New)
        109%nat (Z.to_nat row) ltac:(lia) q2_sched_nc_new_cert).
    - exact Hbody.
  Qed.

  Lemma nc_new_init_gate (w : HonestInput) (Hnd : nondegenerate w)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [init_body (yq_col true) (xa_col true) (xp_col true)
           (l1_col true) (l2_col true)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (nc_h2p RegionId.NoteCommit.Which.New, 0) body.
  Proof.
    apply (hash_region_init _ note_commit_Q
      (split_pieces note_commit_lens (note_commit_new_words w)) true
      (nc_h2p RegionId.NoteCommit.Which.New)).
    - exact (reduced_of_cert note_commit_Q nc_Q_reduced).
    - rewrite nc_new_words_concat. exact (proj1 (proj2 (proj2 Hnd))).
    - intros col r. apply nc_new_hash_adv.
    - rewrite nc_new_hash_len. lia.
    - rewrite fixed_at_read. exact yq_nc_new_cert.
    - exact Hbody.
  Qed.

  Lemma civk_gates (w : HonestInput) (Hnd : nondegenerate w)
      (row : Z) (Hrow : 0 <= row < 51) (body : Constraint.t columns)
      (Hbody : List.In body
        [secant_body (q2_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false);
         ycheck_body (q2_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (civk_h2p, row) body.
  Proof.
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    apply (hash_region_gates _ commit_ivk_Q
      (split_pieces commit_ivk_lens (commit_ivk_words w)) false
      civk_h2p (Z.to_nat row)).
    - exact (reduced_of_cert commit_ivk_Q civk_Q_reduced).
    - rewrite commit_ivk_words_concat.
      exact (proj1 (proj2 (proj2 (proj2 Hnd)))).
    - intros col r. apply civk_hash_adv.
    - rewrite civk_hash_len. lia.
    - rewrite civk_hash_len.
      exact (q2_from_cert w false civk_h2p 51%nat (Z.to_nat row)
        ltac:(lia) q2_sched_civk_cert).
    - exact Hbody.
  Qed.

  Lemma civk_init_gate (w : HonestInput) (Hnd : nondegenerate w)
      (body : Constraint.t columns)
      (Hbody : List.In body
        [init_body (yq_col false) (xa_col false) (xp_col false)
           (l1_col false) (l2_col false)]) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (civk_h2p, 0) body.
  Proof.
    apply (hash_region_init _ commit_ivk_Q
      (split_pieces commit_ivk_lens (commit_ivk_words w)) false civk_h2p).
    - exact (reduced_of_cert commit_ivk_Q civk_Q_reduced).
    - rewrite commit_ivk_words_concat.
      exact (proj1 (proj2 (proj2 (proj2 Hnd)))).
    - intros col r. apply civk_hash_adv.
    - rewrite civk_hash_len. lia.
    - rewrite fixed_at_read. exact yq_civk_cert.
    - exact Hbody.
  Qed.

  (** ** The forward obligation

      The [Hgates] premise of [Complete.circuit_holds_intro] at
      [honest_assignment w], restricted to the enabled points guarded by a
      Sinsemilla selector — the selector-keyed refinement of
      [OrchardCompletenessForward.family_gates_ok] ([forward/api.v]), the
      same shape the sibling per-selector forward files export.  These four
      selectors are enabled exactly on the hash-region rows of the Merkle
      families and of the [Commit^ivk] / [NoteCommit] families, so this is
      the hash-round slice of those families' gate obligations; the family
      obligations follow from the selector obligations of the selectors
      enabled inside the family. *)
  Definition sins_selector_gates_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        sins_selector sel = true ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.

  Theorem sinsemilla_gates_forward : sins_selector_gates_ok.
  Proof.
    intros w Hvalid Hnd sel region row Hin Hsel gate Hgate name body Hbody.
    pose proof (sel_bodies_complete sel _ gate name body Hgate Hbody) as Hb.
    pose proof (sins_point_shape_of_In sel region row Hin) as Hshape.
    clear Hgate Hbody Hin.
    destruct sel; try discriminate Hsel.
    (* [QSinsemilla1_1]: the first sixteen Merkle layers, the old-note hash
       and the [Commit^ivk] hash. *)
    - rewrite bodies_qs1_1 in Hb.
      cbn [sins_point_shape] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | | glr]; try discriminate Hshape.
      { destruct mr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hshape Hlt].
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hidx Hge].
        assert (Hsec : layer_second ml = false)
          by (unfold layer_second; rewrite Hidx; reflexivity).
        apply (merkle_gates w Hnd ml row).
        - split; [ exact (proj1 (Z.leb_le _ _) Hge)
                 | exact (proj1 (Z.ltb_lt _ _) Hlt) ].
        - rewrite Hsec. exact Hb. }
      { destruct cr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hge Hlt].
        apply (civk_gates w Hnd row).
        - split; [ exact (proj1 (Z.leb_le _ _) Hge)
                 | exact (proj1 (Z.ltb_lt _ _) Hlt) ].
        - exact Hb. }
      { destruct ncw; [ | discriminate Hshape ].
        destruct ncr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hge Hlt].
        apply (nc_old_gates w Hnd row).
        - split; [ exact (proj1 (Z.leb_le _ _) Hge)
                 | exact (proj1 (Z.ltb_lt _ _) Hlt) ].
        - exact Hb. }
    (* [QSinsemilla4_1]: row [0] of the same regions. *)
    - rewrite bodies_qs4_1 in Hb.
      cbn [sins_point_shape] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | | glr]; try discriminate Hshape.
      + destruct mr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hidx Hrow0].
        assert (Hsec : layer_second ml = false)
          by (unfold layer_second; rewrite Hidx; reflexivity).
        rewrite (proj1 (Z.eqb_eq _ _) Hrow0).
        apply (merkle_init_gate w Hnd ml).
        rewrite Hsec. exact Hb.
      + destruct cr; try discriminate Hshape.
        rewrite (proj1 (Z.eqb_eq _ _) Hshape).
        apply (civk_init_gate w Hnd). exact Hb.
      + destruct ncw; [ | discriminate Hshape ].
        destruct ncr; try discriminate Hshape.
        rewrite (proj1 (Z.eqb_eq _ _) Hshape).
        apply (nc_old_init_gate w Hnd). exact Hb.
    (* [QSinsemilla1_2]: the last sixteen Merkle layers and the new-note
       hash. *)
    - rewrite bodies_qs1_2 in Hb.
      cbn [sins_point_shape] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | | glr]; try discriminate Hshape.
      + destruct mr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hshape Hlt].
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hidx Hge].
        assert (Hsec : layer_second ml = true)
          by (unfold layer_second; exact Hidx).
        apply (merkle_gates w Hnd ml row).
        * split; [ exact (proj1 (Z.leb_le _ _) Hge)
                 | exact (proj1 (Z.ltb_lt _ _) Hlt) ].
        * rewrite Hsec. exact Hb.
      + destruct ncw; [ discriminate Hshape | ].
        destruct ncr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hge Hlt].
        apply (nc_new_gates w Hnd row).
        * split; [ exact (proj1 (Z.leb_le _ _) Hge)
                 | exact (proj1 (Z.ltb_lt _ _) Hlt) ].
        * exact Hb.
    (* [QSinsemilla4_2]: row [0] of the same regions. *)
    - rewrite bodies_qs4_2 in Hb.
      cbn [sins_point_shape] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | | glr]; try discriminate Hshape.
      + destruct mr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hidx Hrow0].
        assert (Hsec : layer_second ml = true)
          by (unfold layer_second; exact Hidx).
        rewrite (proj1 (Z.eqb_eq _ _) Hrow0).
        apply (merkle_init_gate w Hnd ml).
        rewrite Hsec. exact Hb.
      + destruct ncw; [ discriminate Hshape | ].
        destruct ncr; try discriminate Hshape.
        rewrite (proj1 (Z.eqb_eq _ _) Hshape).
        apply (nc_new_init_gate w Hnd). exact Hb.
  Qed.

End OrchardForwardSinsemilla.
