(** * Forward completeness: the residual gate families

    The gate families of the Orchard circuit that no other [forward/] file
    covers, stated as the selector-keyed refinement of [forward/api.v]'s
    [family_gates_ok]:

    - [QOrchard] — the whole-circuit checks gate ([circuit.v]
      [orchard_circuit_checks_gate]): the magnitude/sign split of the net
      value, the anchor equality on an active spend, and the two enable-flag
      clauses;
    - [QAdd] — the nullifier scalar sum ([gadget/add_chip.v]
      [addition_gate]);
    - [QCondSwap1] / [QCondSwap2] — the Merkle cond-swap gate
      ([utilities/cond_swap.v] [cond_swap_gate]): the two children in
      position order and the boolean position bit;
    - [QMerkleDecompose1] / [QMerkleDecompose2] — the Merkle node
      decomposition gate ([sinsemilla/merkle/chip.v]
      [decomposition_check_gate]): the layer prefix, the two 5-bit halves of
      the word straddling the two children, and the children recombined from
      the running sums of the layer message.

    The constraint bodies guarded by each selector are pinned by [vm_compute]
    certificates against the configured system, and the enabled points of the
    six selectors are pinned by one input-independent shape certificate over
    the reified synthesis facts.  The decomposition identities are exact
    integer facts about the 52-word packing
    [l + left · 2¹⁰ + right · 2²⁶⁵] of §5.4.1.3, so they need only the
    field-element ranges of the two children.

    The obligation [residual_selector_gates_ok] is delivered by
    [residual_gates_forward]: the shape certificate resolves each enabled
    point to its region and row, and the per-region point lemmas discharge
    every guarded body there. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Field.Pow2.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Garden.Orchard.circuit_completeness.forward.ecc_add.
Require Import Garden.Orchard.circuit_completeness.forward.canonicity.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardResidual.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.

  Module OCT := OrchardCompletenessTables.
  Module AMS := OrchardAdviceMerkleSinsemilla.
  Module FS := OrchardForwardSinsemilla.
  Module FC := OrchardCanonicityForward.
  Module FE := OrchardCompletenessForwardEccAdd.

  (** The Poseidon schedule and its hash output stay stuck atoms for the
      conversion oracle: a comparison of two spellings of the nullifier
      scalar would otherwise normalize the 36-round chain
      ([docs/compile-performance.md]). *)
  #[local] Opaque OCT.pose_states_of OCT.states_go Poseidon.poseidon_hash2.

  (** ** The selector group and its obligation Prop *)

  Definition is_residual_sel (sel : Selector.t) : bool :=
    match sel with
    | Selector.QOrchard | Selector.QAdd
    | Selector.QCondSwap1 | Selector.QCondSwap2
    | Selector.QMerkleDecompose1 | Selector.QMerkleDecompose2 => true
    | _ => false
    end.

  (** The gate obligation of [Complete.circuit_holds_intro] restricted to the
      enabled points whose guarding selector is one of this file's — the
      selector-sliced analog of [OrchardCompletenessForward.family_gates_ok]
      (a family obligation follows by case analysis on the selector). *)
  Definition residual_selector_gates_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        is_residual_sel sel = true ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.

  (** ** The constraint bodies guarded by each selector *)

  Definition guarded (sel : Selector.t) : list (Constraint.t columns) :=
    List.flat_map (fun gate =>
      List.flat_map (fun '(_, c) =>
        match c with
        | Constraint.Select s body =>
            if OrchardDecidableEq.selector_eqb s sel then [body] else []
        | _ => []
        end) gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma guarded_complete (sel : Selector.t) (gate : Gate.t columns)
      (name : option string) (body : Constraint.t columns)
      (Hgate : List.In gate system.(ConstraintSystem.gates))
      (Hbody : List.In (name, Constraint.Select sel body)
        gate.(Gate.constraints)) :
    List.In body (guarded sel).
  Proof.
    unfold guarded.
    apply List.in_flat_map. exists gate. split; [exact Hgate |].
    apply List.in_flat_map. exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    cbn. rewrite OrchardDecidableEq.selector_eqb_refl. now left.
  Qed.

  (** Cell expressions at the current and next row. *)
  Definition ac (c : Advice.t) : Expression.t columns :=
    Expression.Advice c Rotation.cur.
  Definition an (c : Advice.t) : Expression.t columns :=
    Expression.Advice c Rotation.next.

  Lemma rot0c : rotated_row 0 Rotation.cur = 0.
  Proof. reflexivity. Qed.
  Lemma rot0n : rotated_row 0 Rotation.next = 1.
  Proof. reflexivity. Qed.

  (** The [QOrchard] and [QAdd] bodies. *)
  Definition orchard_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum (ac Advice.A0)
        (Expression.Negated (ac Advice.A1)))
      (Expression.Product (ac Advice.A2) (ac Advice.A3));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A0))
      (Constraint.Equal (ac Advice.A4) (ac Advice.A5));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A0))
      (Constraint.Equal (Expression.Constant 1) (ac Advice.A6));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A1))
      (Constraint.Equal (Expression.Constant 1) (ac Advice.A7))
  ].

  Definition add_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum (ac Advice.A7) (ac Advice.A8))
      (ac Advice.A6)
  ].

  (** The cond-swap bodies at an arbitrary column layout. *)
  Definition cs_bodies (a b a' b' sw : Advice.t)
      : list (Constraint.t columns) := [
    Constraint.Equal (ac a')
      (Expression.Sum
        (Expression.Product (ac sw) (ac b))
        (Expression.Product
          (Expression.Sum (Expression.Constant 1)
            (Expression.Negated (ac sw)))
          (ac a)));
    Constraint.Equal (ac b')
      (Expression.Sum
        (Expression.Product (ac sw) (ac a))
        (Expression.Product
          (Expression.Sum (Expression.Constant 1)
            (Expression.Negated (ac sw)))
          (ac b)));
    Constraint.Boolean (ac sw)
  ].

  (** The node-decomposition bodies at an arbitrary column layout. *)
  Definition md_bodies (a b c l r : Advice.t)
      : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum (ac a)
        (Expression.Negated (Expression.Scaled (an a) 1024)))
      (an r);
    Constraint.EqualZeroToPrecise
      (Expression.Sum
        (Expression.Sum (an a)
          (Expression.Scaled
            (Expression.Sum
              (Expression.Sum (ac b)
                (Expression.Negated (Expression.Scaled (an b) 1024)))
              (Expression.Scaled (an c) 1024))
            (2 ^ 240)))
        (Expression.Negated (ac l)));
    Constraint.Equal
      (Expression.Sum (an l) (Expression.Scaled (ac c) 32))
      (ac r);
    Constraint.Equal (an b)
      (Expression.Sum (an c) (Expression.Scaled (an l) 32))
  ].

  Lemma guarded_orchard_eq : guarded Selector.QOrchard = orchard_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QOrchard)).
  Qed.

  Lemma guarded_add_eq : guarded Selector.QAdd = add_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QAdd)).
  Qed.

  Lemma guarded_cs1_eq :
    guarded Selector.QCondSwap1 =
    cs_bodies Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QCondSwap1)).
  Qed.

  Lemma guarded_cs2_eq :
    guarded Selector.QCondSwap2 =
    cs_bodies Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QCondSwap2)).
  Qed.

  Lemma guarded_md1_eq :
    guarded Selector.QMerkleDecompose1 =
    md_bodies Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QMerkleDecompose1)).
  Qed.

  Lemma guarded_md2_eq :
    guarded Selector.QMerkleDecompose2 =
    md_bodies Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QMerkleDecompose2)).
  Qed.

  (** ** The enabled points of the six selectors *)

  Definition residual_shape (sel : Selector.t) (region : RegionId.t) (row : Z)
      : bool :=
    match sel, region with
    | Selector.QOrchard, RegionId.OrchardCircuitChecks => row =? 0
    | Selector.QAdd, RegionId.Nullifier RegionId.Nullifier.ScalarAdd =>
        row =? 0
    | Selector.QCondSwap1,
      RegionId.Merkle layer RegionId.Merkle.Region.NodePosition =>
        (row =? 0) && negb (FS.layer_second layer)
    | Selector.QCondSwap2,
      RegionId.Merkle layer RegionId.Merkle.Region.NodePosition =>
        (row =? 0) && FS.layer_second layer
    | Selector.QMerkleDecompose1,
      RegionId.Merkle layer RegionId.Merkle.Region.Decomposition =>
        (row =? 0) && negb (FS.layer_second layer)
    | Selector.QMerkleDecompose2,
      RegionId.Merkle layer RegionId.Merkle.Region.Decomposition =>
        (row =? 0) && FS.layer_second layer
    | _, _ => false
    end.

  Lemma residual_shape_cert :
    List.forallb (fun pt =>
      let '(sel, region, row) := pt in
      implb (is_residual_sel sel) (residual_shape sel region row))
      enabled = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** ** Field-level evaluation helpers *)

  Ltac ev_cells :=
    cbn [eval_constraint eval_expression ac an];
    rewrite ?rot0c, ?rot0n.

  Lemma zeromod (x : Z) :
    Zdiv.eqm Primes.pallas_p x 0 -> x mod Primes.pallas_p = 0.
  Proof. unfold Zdiv.eqm. intros ->. reflexivity. Qed.

  (** Strip the field reductions from a reduced-form equality: after
      unfolding the operations both sides are outermost [mod p]; congruence
      modulo [p] removes the inner reductions and [f_equal] leaves the
      underlying integer identity, exact for these cells. *)
  Ltac field_int :=
    cbv [BinOp.add BinOp.sub BinOp.mul UnOp.from UnOp.opp];
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end;
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p);
    unfold Zdiv.eqm;
    f_equal.

  Ltac field_int0 :=
    cbv [BinOp.add BinOp.sub BinOp.mul UnOp.from UnOp.opp];
    apply zeromod;
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p);
    unfold Zdiv.eqm;
    f_equal.

  Lemma from_eq_zero (x : Z) : x = 0 -> UnOp.from x = 0.
  Proof. intros ->. reflexivity. Qed.

  Lemma isbool_from (v : Z) :
    v = 0 \/ v = 1 -> IsBool.t (UnOp.from v).
  Proof. intros [-> | ->]; vm_compute; reflexivity. Qed.

  (** ** The generic assignment dispatch *)

  (** ** The nullifier scalar sum ([QAdd])

      The [ScalarAdd] row carries the Poseidon output on [A7], [ψ_old] on
      [A8] and their field sum on [A6] — the sum is the hoisted record's
      nullifier scalar by construction. *)

  Lemma cell_add_a6 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A6 (RegionId.Nullifier RegionId.Nullifier.ScalarAdd) 0 =
    OCT.t_nullifier_scalar (OCT.tables_of w).
  Proof. reflexivity. Qed.

  Lemma cell_add_a7 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A7 (RegionId.Nullifier RegionId.Nullifier.ScalarAdd) 0 =
    OCT.t_hash2 (OCT.tables_of w).
  Proof. reflexivity. Qed.

  Lemma cell_add_a8 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A8 (RegionId.Nullifier RegionId.Nullifier.ScalarAdd) 0 =
    hi_psi_old w.
  Proof. reflexivity. Qed.

  Lemma t_nscalar_shape (w : HonestInput) :
    OCT.t_nullifier_scalar (OCT.tables_of w) =
    BinOp.add (OCT.t_hash2 (OCT.tables_of w)) (hi_psi_old w).
  Proof.
    rewrite FE.t_nullifier_scalar_eq, FE.t_hash2_eq.
    unfold nullifier_scalar.
    reflexivity.
  Qed.

  (** The sum identity over abstract row values: the generator's cells are
      substituted by [rewrite], so no reduction engine ever traverses the
      hoisted Poseidon output ([docs/compile-performance.md]). *)
  Lemma add_gate_core (h psi : Z) :
    BinOp.add (UnOp.from h) (UnOp.from psi) = UnOp.from (BinOp.add h psi).
  Proof. mod_ring_solve. Qed.

  Lemma add_point (w : HonestInput) (body : Constraint.t columns)
      (Hb : List.In body add_bodies) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (RegionId.Nullifier RegionId.Nullifier.ScalarAdd, 0) body.
  Proof.
    cbv [add_bodies] in Hb.
    destruct Hb as [<- | [] ].
    ev_cells.
    rewrite cell_add_a6, cell_add_a7, cell_add_a8, t_nscalar_shape.
    exact (add_gate_core _ _).
  Qed.

  (** ** The whole-circuit checks gate ([QOrchard])

      The [OrchardCircuitChecks] row carries [v_old], [v_new], the
      magnitude/sign split, the computed Merkle root, the public anchor row
      and the two enable flags. *)

  Lemma cell_chk_a0 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A0 RegionId.OrchardCircuitChecks 0 = hi_v_old w.
  Proof. reflexivity. Qed.

  Lemma cell_chk_a1 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A1 RegionId.OrchardCircuitChecks 0 = hi_v_new w.
  Proof. reflexivity. Qed.

  Lemma cell_chk_a2 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A2 RegionId.OrchardCircuitChecks 0 = magnitude w.
  Proof. reflexivity. Qed.

  Lemma cell_chk_a3 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A3 RegionId.OrchardCircuitChecks 0 = sign w.
  Proof. reflexivity. Qed.

  Lemma cell_chk_a4 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 RegionId.OrchardCircuitChecks 0 = OCT.t_anchor (OCT.tables_of w).
  Proof. reflexivity. Qed.

  Lemma cell_chk_a5 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A5 RegionId.OrchardCircuitChecks 0 =
    OCT.t_anchor_row (OCT.tables_of w).
  Proof. reflexivity. Qed.

  Lemma cell_chk_a6 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A6 RegionId.OrchardCircuitChecks 0 = hi_enable_spends w.
  Proof. reflexivity. Qed.

  Lemma cell_chk_a7 (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A7 RegionId.OrchardCircuitChecks 0 = hi_enable_outputs w.
  Proof. reflexivity. Qed.

  (** The public anchor row is the computed root off a dummy spend. *)
  Lemma t_anchor_row_shape (w : HonestInput) :
    OCT.t_anchor_row (OCT.tables_of w) =
    (if hi_v_old w =? 0 then hi_anchor_public w
     else OCT.t_anchor (OCT.tables_of w)).
  Proof. reflexivity. Qed.

  (** The magnitude/sign split of the net value. *)
  Lemma magnitude_sign_split (w : HonestInput) :
    BinOp.sub (UnOp.from (hi_v_old w)) (UnOp.from (hi_v_new w)) =
    BinOp.mul (UnOp.from (magnitude w)) (UnOp.from (sign w)).
  Proof.
    rewrite FieldRewrite.sub_from_left, FieldRewrite.sub_from_right,
      FieldRewrite.mul_from_left, FieldRewrite.mul_from_right.
    unfold magnitude, sign.
    destruct (hi_v_new w <=? hi_v_old w) eqn:Hcmp.
    - apply Z.leb_le in Hcmp.
      rewrite Z.abs_eq by lia.
      unfold BinOp.sub, BinOp.mul.
      f_equal. ring.
    - apply Z.leb_gt in Hcmp.
      rewrite Z.abs_neq by lia.
      unfold BinOp.sub, BinOp.mul.
      replace (- (hi_v_old w - hi_v_new w) * (Primes.pallas_p - 1))
        with ((hi_v_old w - hi_v_new w)
              + (hi_v_new w - hi_v_old w) * Primes.pallas_p) by ring.
      rewrite Z_mod_plus_full.
      reflexivity.
  Qed.

  (** The whole-circuit checks gate at its single enabled point. *)
  Lemma orchard_point (w : HonestInput) (Hvalid : valid w)
      (body : Constraint.t columns) (Hb : List.In body orchard_bodies) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (RegionId.OrchardCircuitChecks, 0) body.
  Proof.
    destruct Hvalid as (_ & Hspends & Houtputs & _).
    cbv [orchard_bodies] in Hb.
    destruct Hb as [<- | [<- | [<- | [<- | [] ] ] ] ]; ev_cells.
    - rewrite cell_chk_a0, cell_chk_a1, cell_chk_a2, cell_chk_a3.
      exact (magnitude_sign_split w).
    - destruct (hi_v_old w =? 0) eqn:Hzero.
      + left. rewrite cell_chk_a0. apply from_eq_zero.
        exact (proj1 (Z.eqb_eq _ _) Hzero).
      + right. rewrite cell_chk_a4, cell_chk_a5, t_anchor_row_shape,
          Hzero. reflexivity.
    - destruct Hspends as [Hzero | Hflag].
      + left. rewrite cell_chk_a0. exact (from_eq_zero _ Hzero).
      + right. rewrite cell_chk_a6, Hflag. reflexivity.
    - destruct Houtputs as [Hzero | Hflag].
      + left. rewrite cell_chk_a1. exact (from_eq_zero _ Hzero).
      + right. rewrite cell_chk_a7, Hflag. reflexivity.
  Qed.

  (** ** Merkle layer data: the cells of the two Merkle gate regions *)

  Lemma cell_merkle (w : HonestInput) (layer : RegionId.Merkle.Layer.t)
      (mr : RegionId.Merkle.Region.t) (col : Advice.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col (RegionId.Merkle layer mr) row =
    OCT.merkle_advice_t w (OCT.tables_of w) col layer mr row.
  Proof. reflexivity. Qed.

  Lemma hd_bits_of (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_bits (OCT.hash_data_of Q pieces) = AMS.bits_column pieces.
  Proof.
    unfold OCT.hash_data_of.
    destruct (OCT.hash_go Q (Stdlib.Lists.List.concat pieces)).
    reflexivity.
  Qed.

  Lemma hd_words_of (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_words (OCT.hash_data_of Q pieces) =
    Stdlib.Lists.List.concat pieces.
  Proof.
    unfold OCT.hash_data_of.
    destruct (OCT.hash_go Q (Stdlib.Lists.List.concat pieces)).
    reflexivity.
  Qed.

  (** ** Ranges of the two children of a layer *)

  Lemma leaf_range (w : HonestInput) : 0 <= leaf w < Primes.pallas_p.
  Proof.
    unfold leaf, EccSpec.extract_x.
    rewrite <- FS.cm_old_expand.
    destruct FC.note_commit_Q_coords as [HQx HQy].
    destruct
      (FC.hash_go_coords
        (Stdlib.Lists.List.concat
          (AMS.split_pieces AMS.note_commit_lens (note_commit_old_words w)))
        AMS.note_commit_Q HQx HQy) as [Hhx Hhy].
    rewrite <- FC.hd_out_hash_data_of in Hhx, Hhy.
    destruct
      (FC.mul_gen_coords (hi_rcm_old w) PallasGenerators.note_commit_r_G
        PallasGenerators.note_commit_r_reduced) as [Hmx Hmy].
    unfold OrchardProtocolSpec.mul_note_commit_r.
    exact (proj1 (FC.padd_coords _ _ Hhx Hhy Hmx Hmy)).
  Qed.

  Lemma merkle_node_range (w : HonestInput) (i : nat) (Hi : (i <= 32)%nat) :
    0 <= merkle_node w i < Primes.pallas_p.
  Proof.
    destruct i as [| j].
    - exact (leaf_range w).
    - rewrite (merkle_node_succ w j ltac:(lia)).
      rewrite merkle_layer_words_spec.
      unfold SinsemillaSpec.sinsemilla_hash, EccSpec.extract_x.
      rewrite <- (sinsemilla_acc_full merkle_Q (merkle_layer_words w j)).
      apply FS.acc_x_reduced.
      exact (FS.reduced_of_cert merkle_Q FS.merkle_Q_reduced).
  Qed.

  Lemma sibling_range (w : HonestInput) (Hvalid : valid w) (i : nat)
      (Hi : (i < 32)%nat) :
    0 <= List.nth i (hi_path w) 0 < Primes.pallas_p.
  Proof.
    destruct Hvalid as (Hty & _).
    destruct Hty as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & Hlen & Hall & _).
    apply (proj1 (List.Forall_forall _ _) Hall).
    apply List.nth_In.
    rewrite Hlen. exact Hi.
  Qed.

  (** ** The packed 52-word layer message

      §5.4.1.3 packs the layer prefix and the two children into
      [n = l + left · 2^10 + right · 2^265]; every cell the decomposition
      gate reads is a running sum of the 10-bit words of [n]. *)

  Definition mnum (L left right : Z) : Z :=
    L + left * 2 ^ 10 + right * 2 ^ 265.

  Definition layer_left (w : HonestInput) (i : nat) : Z :=
    if path_bit w i then List.nth i (hi_path w) 0 else merkle_node w i.
  Definition layer_right (w : HonestInput) (i : nat) : Z :=
    if path_bit w i then merkle_node w i else List.nth i (hi_path w) 0.

  Lemma merkle_words_msg (w : HonestInput) (i : nat) :
    merkle_layer_words w i =
    SinsemillaSpec.words_le 52 (mnum (Z.of_nat i)
      (layer_left w i) (layer_right w i)).
  Proof.
    unfold merkle_layer_words, layer_left, layer_right,
      SinsemillaSpec.merkle_message, mnum.
    destruct (path_bit w i); reflexivity.
  Qed.

  (** ** Integer facts about the packing *)

  Lemma pow2_nz (k : Z) (Hk : 0 <= k) : 2 ^ k <> 0.
  Proof. pose proof (pow2_pos k Hk). lia. Qed.

  Ltac pow_side := first [apply pow2_nz | apply pow2_pos]; lia.

  Lemma div_mod_split (x k : Z) (Hk : 0 <= k) :
    x = x mod 2 ^ k + x / 2 ^ k * 2 ^ k.
  Proof.
    pose proof (pow2_pos k Hk) as Hp.
    pose proof (Z.div_mod x (2 ^ k) ltac:(lia)) as H.
    clear -H. lia.
  Qed.

  Lemma mod_low (u v k : Z) (Hk : 0 <= k) (Hu : 0 <= u < 2 ^ k) :
    (u + v * 2 ^ k) mod 2 ^ k = u.
  Proof.
    rewrite Z_mod_plus_full.
    apply Z.mod_small. exact Hu.
  Qed.

  Lemma div_low (u v k : Z) (Hk : 0 <= k) (Hu : 0 <= u < 2 ^ k) :
    (u + v * 2 ^ k) / 2 ^ k = v.
  Proof.
    pose proof (pow2_pos k Hk) as Hp.
    rewrite Z.div_add by lia.
    rewrite (Z.div_small u (2 ^ k)) by exact Hu.
    lia.
  Qed.

  Lemma split_low (u v k m : Z) (Hk : 0 <= k) (Hm : 0 <= m)
      (Hu : 0 <= u < 2 ^ k) :
    (u + v * 2 ^ k) mod (2 ^ k * 2 ^ m) = u + v mod 2 ^ m * 2 ^ k.
  Proof.
    pose proof (pow2_pos k Hk) as Hpk.
    pose proof (pow2_pos m Hm) as Hpm.
    rewrite Z.rem_mul_r by lia.
    rewrite (mod_low u v k Hk Hu).
    rewrite (div_low u v k Hk Hu).
    lia.
  Qed.

  Lemma div_split2 (x k m : Z) (Hk : 0 <= k) (Hm : 0 <= m) :
    x / (2 ^ k * 2 ^ m) = x / 2 ^ k / 2 ^ m.
  Proof.
    pose proof (pow2_pos k Hk) as Hpk.
    pose proof (pow2_pos m Hm) as Hpm.
    rewrite Z.div_div by lia.
    reflexivity.
  Qed.

  (** The five running sums of the packing the decomposition gate reads.
      Stated as free lemmas rather than inside a [Section]: a [lia] call
      under a section hypothesis does not terminate in this development
      ([docs/compile-performance.md]). *)

  Lemma mnum_mod10 (L left right : Z) (HL : 0 <= L < 2 ^ 10) :
    mnum L left right mod 2 ^ 10 = L.
  Proof.
    unfold mnum.
    replace (L + left * 2 ^ 10 + right * 2 ^ 265)
      with (L + (left + right * 2 ^ 255) * 2 ^ 10) by ring.
    apply mod_low; [lia | exact HL].
  Qed.

  Lemma mnum_div10 (L left right : Z) (HL : 0 <= L < 2 ^ 10) :
    mnum L left right / 2 ^ 10 = left + right * 2 ^ 255.
  Proof.
    unfold mnum.
    replace (L + left * 2 ^ 10 + right * 2 ^ 265)
      with (L + (left + right * 2 ^ 255) * 2 ^ 10) by ring.
    apply div_low; [lia | exact HL].
  Qed.

  Lemma u_range (left : Z) (Hlf : 0 <= left < 2 ^ 255) :
    0 <= left / 2 ^ 250 < 2 ^ 5.
  Proof.
    pose proof (pow2_pos 250 ltac:(lia)) as Hp.
    split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    replace (2 ^ 250 * 2 ^ 5) with (2 ^ 255) by reflexivity.
    lia.
  Qed.

  Lemma v_range (left : Z) (Hlf : 0 <= left < 2 ^ 255) :
    0 <= left / 2 ^ 240 < 2 ^ 15.
  Proof.
    pose proof (pow2_pos 240 ltac:(lia)) as Hp.
    split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    replace (2 ^ 240 * 2 ^ 15) with (2 ^ 255) by reflexivity.
    lia.
  Qed.

  Lemma q_range (right : Z) (Hrt : 0 <= right < 2 ^ 255) :
    0 <= right / 2 ^ 5 < 2 ^ 250.
  Proof.
    pose proof (pow2_pos 5 ltac:(lia)) as Hp.
    split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    replace (2 ^ 5 * 2 ^ 250) with (2 ^ 255) by reflexivity.
    lia.
  Qed.

  Lemma mb1_val (L left right : Z) (HL : 0 <= L < 2 ^ 10) :
    mnum L left right / 2 ^ 10 mod 2 ^ 240 = left mod 2 ^ 240.
  Proof.
    rewrite (mnum_div10 L left right HL).
    replace (left + right * 2 ^ 255)
      with (left + right * 2 ^ 15 * 2 ^ 240) by ring.
    rewrite Z_mod_plus_full.
    reflexivity.
  Qed.

  Lemma mb0_val (L left right : Z) (HL : 0 <= L < 2 ^ 10) :
    mnum L left right mod 2 ^ 250 = L + 2 ^ 10 * (left mod 2 ^ 240).
  Proof.
    pose proof (pow2_pos 10 ltac:(lia)) as Hp10.
    pose proof (pow2_pos 240 ltac:(lia)) as Hp240.
    replace (2 ^ 250) with (2 ^ 10 * 2 ^ 240) by reflexivity.
    rewrite Z.rem_mul_r by lia.
    rewrite (mnum_mod10 L left right HL), (mb1_val L left right HL).
    reflexivity.
  Qed.

  Lemma mb25_val (L left right : Z) (HL : 0 <= L < 2 ^ 10)
      (Hlf : 0 <= left < 2 ^ 255) :
    mnum L left right / 2 ^ 250 mod 2 ^ 20 =
    left / 2 ^ 240 + right mod 2 ^ 5 * 2 ^ 15.
  Proof.
    replace (2 ^ 250) with (2 ^ 10 * 2 ^ 240) by reflexivity.
    rewrite (div_split2 _ 10 240 ltac:(lia) ltac:(lia)).
    rewrite (mnum_div10 L left right HL).
    replace (left + right * 2 ^ 255)
      with (left + right * 2 ^ 15 * 2 ^ 240) by ring.
    pose proof (pow2_pos 240 ltac:(lia)) as Hp240.
    rewrite Z.div_add by lia.
    replace (2 ^ 20) with (2 ^ 15 * 2 ^ 5) by reflexivity.
    apply split_low; [lia | lia | exact (v_range left Hlf)].
  Qed.

  Lemma mb26_val (L left right : Z) (HL : 0 <= L < 2 ^ 10)
      (Hlf : 0 <= left < 2 ^ 255) :
    mnum L left right / 2 ^ 260 mod 2 ^ 10 =
    left / 2 ^ 250 + right mod 2 ^ 5 * 2 ^ 5.
  Proof.
    replace (2 ^ 260) with (2 ^ 10 * 2 ^ 250) by reflexivity.
    rewrite (div_split2 _ 10 250 ltac:(lia) ltac:(lia)).
    rewrite (mnum_div10 L left right HL).
    replace (left + right * 2 ^ 255)
      with (left + right * 2 ^ 5 * 2 ^ 250) by ring.
    pose proof (pow2_pos 250 ltac:(lia)) as Hp250.
    rewrite Z.div_add by lia.
    replace (2 ^ 10) with (2 ^ 5 * 2 ^ 5) by reflexivity.
    apply split_low; [lia | lia | exact (u_range left Hlf)].
  Qed.

  Lemma mb27_val (L left right : Z) (HL : 0 <= L < 2 ^ 10)
      (Hlf : 0 <= left < 2 ^ 255) (Hrt : 0 <= right < 2 ^ 255) :
    mnum L left right / 2 ^ 270 mod 2 ^ 250 = right / 2 ^ 5.
  Proof.
    replace (2 ^ 270) with (2 ^ 10 * 2 ^ 260) by reflexivity.
    rewrite (div_split2 _ 10 260 ltac:(lia) ltac:(lia)).
    rewrite (mnum_div10 L left right HL).
    replace (2 ^ 260) with (2 ^ 255 * 2 ^ 5) by reflexivity.
    rewrite (div_split2 _ 255 5 ltac:(lia) ltac:(lia)).
    rewrite (div_low left right 255 ltac:(lia) Hlf).
    apply Z.mod_small.
    exact (q_range right Hrt).
  Qed.

  (** ** The running sums of the packing *)

  Lemma sds_nth (l : list Z) : forall k : nat,
    List.nth k (AMS.suffix_digit_sums l) 0 =
    SinsemillaHash.digit_sum (List.skipn k l).
  Proof.
    induction l as [| x xs IH]; intros k.
    - destruct k; reflexivity.
    - destruct k as [| k].
      + cbn [AMS.suffix_digit_sums List.nth List.skipn
             SinsemillaHash.digit_sum].
        rewrite AMS.suffix_digit_sums_head. reflexivity.
      + cbn [AMS.suffix_digit_sums List.nth List.skipn].
        apply IH.
  Qed.

  Lemma words_le_cons (c : nat) (n : Z) :
    SinsemillaSpec.words_le (S c) n =
    n mod 2 ^ 10 :: SinsemillaSpec.words_le c (n / 2 ^ 10).
  Proof. reflexivity. Qed.

  Lemma firstn_words_le (k : nat) : forall (d : nat) (n : Z),
    List.firstn k (SinsemillaSpec.words_le (k + d) n) =
    SinsemillaSpec.words_le k n.
  Proof.
    induction k as [| k IH]; intros d n; [reflexivity |].
    cbn [Nat.add].
    rewrite (words_le_cons (k + d) n), (words_le_cons k n).
    cbn [List.firstn].
    rewrite IH. reflexivity.
  Qed.

  Lemma skipn_words_le (k : nat) : forall (d : nat) (n : Z),
    List.skipn k (SinsemillaSpec.words_le (k + d) n) =
    SinsemillaSpec.words_le d (n / 2 ^ (10 * Z.of_nat k)).
  Proof.
    induction k as [| k IH]; intros d n.
    - cbn [Nat.add List.skipn].
      replace (10 * Z.of_nat 0) with 0 by lia.
      rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
    - cbn [Nat.add].
      rewrite (words_le_cons (k + d) n).
      cbn [List.skipn].
      rewrite IH.
      replace (10 * Z.of_nat (S k)) with (10 + 10 * Z.of_nat k) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite <- Z.div_div by pow_side.
      reflexivity.
  Qed.

  Lemma firstn_words_le' (k d c : nat) (n : Z) (Hc : c = (k + d)%nat) :
    List.firstn k (SinsemillaSpec.words_le c n) =
    SinsemillaSpec.words_le k n.
  Proof. subst c. apply firstn_words_le. Qed.

  Lemma skipn_words_le' (k d c : nat) (n : Z) (Hc : c = (k + d)%nat) :
    List.skipn k (SinsemillaSpec.words_le c n) =
    SinsemillaSpec.words_le d (n / 2 ^ (10 * Z.of_nat k)).
  Proof. subst c. apply skipn_words_le. Qed.

  Lemma nth_words_le (k : nat) : forall (c : nat) (n : Z),
    (k < c)%nat ->
    List.nth k (SinsemillaSpec.words_le c n) 0 =
    n / 2 ^ (10 * Z.of_nat k) mod 2 ^ 10.
  Proof.
    induction k as [| k IH]; intros c n Hk.
    - destruct c as [| c]; [lia |].
      rewrite words_le_cons. cbn [List.nth].
      replace (10 * Z.of_nat 0) with 0 by lia.
      rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
    - destruct c as [| c]; [lia |].
      rewrite words_le_cons. cbn [List.nth].
      rewrite (IH c (n / 2 ^ 10) ltac:(lia)).
      replace (10 * Z.of_nat (S k)) with (10 + 10 * Z.of_nat k) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite <- Z.div_div by pow_side.
      reflexivity.
  Qed.

  Lemma digit_sum_words_le (c : nat) : forall n : Z,
    SinsemillaHash.digit_sum (SinsemillaSpec.words_le c n) =
    n mod 2 ^ (10 * Z.of_nat c).
  Proof.
    induction c as [| c IH]; intros n.
    - cbn [SinsemillaSpec.words_le SinsemillaHash.digit_sum].
      replace (10 * Z.of_nat 0) with 0 by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
    - rewrite words_le_cons.
      cbn [SinsemillaHash.digit_sum].
      rewrite IH.
      replace (10 * Z.of_nat (S c)) with (10 + 10 * Z.of_nat c) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.rem_mul_r
        by (pose proof (pow2_pos 10 ltac:(lia));
            pose proof (pow2_pos (10 * Z.of_nat c) ltac:(lia)); lia).
      reflexivity.
  Qed.

  (** The [bits] column of a Merkle layer region. *)
  Definition mbits (n : Z) : list Z :=
    AMS.bits_column
      (AMS.split_pieces AMS.merkle_lens (SinsemillaSpec.words_le 52 n)).

  Lemma merkle_pieces_eq (n : Z) :
    AMS.split_pieces AMS.merkle_lens (SinsemillaSpec.words_le 52 n) =
    [SinsemillaSpec.words_le 25 n;
     SinsemillaSpec.words_le 2 (n / 2 ^ 250);
     SinsemillaSpec.words_le 25 (n / 2 ^ 270)].
  Proof.
    cbv [AMS.merkle_lens].
    cbn [AMS.split_pieces].
    rewrite (firstn_words_le' 25 27 52 n eq_refl).
    rewrite (skipn_words_le' 25 27 52 n eq_refl).
    replace (10 * Z.of_nat 25) with 250 by lia.
    rewrite (firstn_words_le' 2 25 27 (n / 2 ^ 250) eq_refl).
    rewrite (skipn_words_le' 2 25 27 (n / 2 ^ 250) eq_refl).
    replace (10 * Z.of_nat 2) with 20 by lia.
    rewrite (firstn_words_le' 25 0 25 (n / 2 ^ 250 / 2 ^ 20) eq_refl).
    rewrite Z.div_div by pow_side.
    replace (2 ^ 250 * 2 ^ 20) with (2 ^ 270) by reflexivity.
    reflexivity.
  Qed.

  Lemma mbits_eq (n : Z) :
    mbits n =
    AMS.suffix_digit_sums (SinsemillaSpec.words_le 25 n) ++
    AMS.suffix_digit_sums (SinsemillaSpec.words_le 2 (n / 2 ^ 250)) ++
    AMS.suffix_digit_sums (SinsemillaSpec.words_le 25 (n / 2 ^ 270)).
  Proof.
    unfold mbits.
    rewrite merkle_pieces_eq.
    cbv [AMS.bits_column].
    cbn [List.flat_map].
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

  Ltac sds_len :=
    rewrite AMS.suffix_digit_sums_length, FS.words_le_length; lia.

  Lemma mbits_0 (n : Z) : List.nth 0 (mbits n) 0 = n mod 2 ^ 250.
  Proof.
    rewrite mbits_eq.
    rewrite List.app_nth1 by sds_len.
    rewrite sds_nth. cbn [List.skipn].
    rewrite digit_sum_words_le.
    replace (10 * Z.of_nat 25) with 250 by lia.
    reflexivity.
  Qed.

  Lemma mbits_1 (n : Z) : List.nth 1 (mbits n) 0 = n / 2 ^ 10 mod 2 ^ 240.
  Proof.
    rewrite mbits_eq.
    rewrite List.app_nth1 by sds_len.
    rewrite sds_nth.
    rewrite (skipn_words_le' 1 24 25 n eq_refl).
    rewrite digit_sum_words_le.
    replace (10 * Z.of_nat 1) with 10 by lia.
    replace (10 * Z.of_nat 24) with 240 by lia.
    reflexivity.
  Qed.

  Lemma mbits_25 (n : Z) :
    List.nth 25 (mbits n) 0 = n / 2 ^ 250 mod 2 ^ 20.
  Proof.
    rewrite mbits_eq.
    rewrite List.app_nth2 by sds_len.
    rewrite AMS.suffix_digit_sums_length, FS.words_le_length.
    replace (25 - 25)%nat with 0%nat by lia.
    rewrite List.app_nth1 by sds_len.
    rewrite sds_nth. cbn [List.skipn].
    rewrite digit_sum_words_le.
    replace (10 * Z.of_nat 2) with 20 by lia.
    reflexivity.
  Qed.

  Lemma mbits_26 (n : Z) :
    List.nth 26 (mbits n) 0 = n / 2 ^ 260 mod 2 ^ 10.
  Proof.
    rewrite mbits_eq.
    rewrite List.app_nth2 by sds_len.
    rewrite AMS.suffix_digit_sums_length, FS.words_le_length.
    replace (26 - 25)%nat with 1%nat by lia.
    rewrite List.app_nth1 by sds_len.
    rewrite sds_nth.
    rewrite (skipn_words_le' 1 1 2 (n / 2 ^ 250) eq_refl).
    rewrite digit_sum_words_le.
    replace (10 * Z.of_nat 1) with 10 by lia.
    rewrite Z.div_div by pow_side.
    replace (2 ^ 250 * 2 ^ 10) with (2 ^ 260) by reflexivity.
    reflexivity.
  Qed.

  Lemma mbits_27 (n : Z) :
    List.nth 27 (mbits n) 0 = n / 2 ^ 270 mod 2 ^ 250.
  Proof.
    rewrite mbits_eq.
    rewrite List.app_nth2 by sds_len.
    rewrite AMS.suffix_digit_sums_length, FS.words_le_length.
    replace (27 - 25)%nat with 2%nat by lia.
    rewrite List.app_nth2 by sds_len.
    rewrite AMS.suffix_digit_sums_length, FS.words_le_length.
    replace (2 - 2)%nat with 0%nat by lia.
    rewrite sds_nth. cbn [List.skipn].
    rewrite digit_sum_words_le.
    replace (10 * Z.of_nat 25) with 250 by lia.
    reflexivity.
  Qed.

  Lemma mword_26 (n : Z) :
    List.nth 26 (SinsemillaSpec.words_le 52 n) 0 = n / 2 ^ 260 mod 2 ^ 10.
  Proof.
    rewrite (nth_words_le 26 52 n ltac:(lia)).
    replace (10 * Z.of_nat 26) with 260 by lia.
    reflexivity.
  Qed.

  Lemma mbits_of (n : Z) :
    AMS.bits_column (AMS.split_pieces AMS.merkle_lens
      (SinsemillaSpec.words_le 52 n)) = mbits n.
  Proof. unfold mbits. reflexivity. Qed.

  (** ** The two Merkle gates over abstract row values *)

  Lemma cs_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (a b a' b' sw : Advice.t) (x y s : Z)
      (Ha : Gamma.(Assignment.advice) a region 0 = x)
      (Hb : Gamma.(Assignment.advice) b region 0 = y)
      (Hs : Gamma.(Assignment.advice) sw region 0 = s)
      (Hcase :
        (s = 1 /\ Gamma.(Assignment.advice) a' region 0 = y /\
                  Gamma.(Assignment.advice) b' region 0 = x) \/
        (s = 0 /\ Gamma.(Assignment.advice) a' region 0 = x /\
                  Gamma.(Assignment.advice) b' region 0 = y)) :
    forall body, List.In body (cs_bodies a b a' b' sw) ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    destruct Hcase as [(Hs1 & Ha' & Hb') | (Hs0 & Ha' & Hb')];
      intros body [<- | [<- | [<- | [] ] ] ]; ev_cells;
      rewrite ?Ha, ?Hb, ?Ha', ?Hb', ?Hs, ?Hs1, ?Hs0.
    - mod_ring_solve.
    - mod_ring_solve.
    - apply isbool_from. right. reflexivity.
    - mod_ring_solve.
    - mod_ring_solve.
    - apply isbool_from. left. reflexivity.
  Qed.

  Lemma md_left_core (A B C D E : Z) (HE : E = A + B * 2 ^ 240) :
    A + (B + D * 2 ^ 15 - (C + D * 2 ^ 5) * 2 ^ 10 + C * 2 ^ 10) * 2 ^ 240
      - E = 0.
  Proof. subst E. ring. Qed.

  Lemma md_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (a b c l r : Advice.t)
      (L left right : Z)
      (Ha0 : Gamma.(Assignment.advice) a region 0 =
        L + 2 ^ 10 * (left mod 2 ^ 240))
      (Ha1 : Gamma.(Assignment.advice) a region 1 = left mod 2 ^ 240)
      (Hb0 : Gamma.(Assignment.advice) b region 0 =
        left / 2 ^ 240 + right mod 2 ^ 5 * 2 ^ 15)
      (Hb1 : Gamma.(Assignment.advice) b region 1 =
        left / 2 ^ 250 + right mod 2 ^ 5 * 2 ^ 5)
      (Hc0 : Gamma.(Assignment.advice) c region 0 = right / 2 ^ 5)
      (Hc1 : Gamma.(Assignment.advice) c region 1 = left / 2 ^ 250)
      (Hl0 : Gamma.(Assignment.advice) l region 0 = left)
      (Hl1 : Gamma.(Assignment.advice) l region 1 = right mod 2 ^ 5)
      (Hr0 : Gamma.(Assignment.advice) r region 0 = right)
      (Hr1 : Gamma.(Assignment.advice) r region 1 = L) :
    forall body, List.In body (md_bodies a b c l r) ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [<- | [<- | [<- | [] ] ] ] ]; ev_cells;
      rewrite ?Ha0, ?Ha1, ?Hb0, ?Hb1, ?Hc0, ?Hc1, ?Hl0, ?Hl1, ?Hr0, ?Hr1.
    - field_int; try ring.
    - field_int0.
      exact (md_left_core _ _ _ _ _ (div_mod_split left 240 ltac:(lia))).
    - field_int; try ring.
      symmetry. exact (div_mod_split right 5 ltac:(lia)).
    - field_int; try ring.
  Qed.

  (** ** The Merkle cell dispatch *)

  Ltac mstart Hs :=
    rewrite cell_merkle;
    cbn [OCT.merkle_advice_t];
    rewrite Hs;
    cbn [negb AMS.logical_col];
    rewrite ?(FS.t_layers_nth _ _ (FS.layer_index_lt _));
    cbn [FS.merkle_layer_data OCT.lyd_hash OCT.lyd_node];
    rewrite ?hd_bits_of, ?hd_words_of, ?FS.merkle_words_concat;
    rewrite ?merkle_words_msg, ?mbits_of.

  Lemma layer_left_range (w : HonestInput) (Hvalid : valid w) (i : nat)
      (Hi : (i < 32)%nat) :
    0 <= layer_left w i < 2 ^ 255.
  Proof.
    unfold layer_left.
    destruct (path_bit w i);
      apply FC.p_lt_2_255;
      [ exact (sibling_range w Hvalid i Hi)
      | exact (merkle_node_range w i ltac:(lia)) ].
  Qed.

  Lemma layer_right_range (w : HonestInput) (Hvalid : valid w) (i : nat)
      (Hi : (i < 32)%nat) :
    0 <= layer_right w i < 2 ^ 255.
  Proof.
    unfold layer_right.
    destruct (path_bit w i);
      apply FC.p_lt_2_255;
      [ exact (merkle_node_range w i ltac:(lia))
      | exact (sibling_range w Hvalid i Hi) ].
  Qed.

  Lemma layer_L_range (layer : RegionId.Merkle.Layer.t) :
    0 <= Z.of_nat (Z.to_nat (RegionId.Merkle.Layer.to_index layer)) < 2 ^ 10.
  Proof.
    pose proof (FS.layer_index_lt layer) as Hi.
    replace (2 ^ 10) with 1024 by reflexivity.
    lia.
  Qed.

  (** ** The cond-swap gate at an enabled point

      The [NodePosition] region of a layer carries the running node, the
      sibling and the position bit; the two swap outputs are the children in
      position order, so the gate holds on either branch of the bit.  The two
      lemmas are the two configuration variants: layers 0–15 on [A0..A4],
      layers 16–31 on [A5..A9]. *)

  Lemma cs_point_1 (w : HonestInput) (layer : RegionId.Merkle.Layer.t)
      (Hs : negb (RegionId.Merkle.Layer.to_index layer <? 16) = false) :
    forall body,
      List.In body
        (cs_bodies Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4) ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (RegionId.Merkle layer RegionId.Merkle.Region.NodePosition, 0) body.
  Proof.
    apply (cs_gate_eval _ _ Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (merkle_node w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer)) (hi_path w) 0)
      (if path_bit w (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
       then 1 else 0)).
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
    - destruct (path_bit w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
        eqn:Hbit.
      + left. split; [reflexivity |].
        split; (mstart Hs; rewrite Hbit; reflexivity).
      + right. split; [reflexivity |].
        split; (mstart Hs; rewrite Hbit; reflexivity).
  Qed.

  Lemma cs_point_2 (w : HonestInput) (layer : RegionId.Merkle.Layer.t)
      (Hs : negb (RegionId.Merkle.Layer.to_index layer <? 16) = true) :
    forall body,
      List.In body
        (cs_bodies Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9) ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (RegionId.Merkle layer RegionId.Merkle.Region.NodePosition, 0) body.
  Proof.
    apply (cs_gate_eval _ _ Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
      (merkle_node w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer)) (hi_path w) 0)
      (if path_bit w (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
       then 1 else 0)).
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
    - destruct (path_bit w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
        eqn:Hbit.
      + left. split; [reflexivity |].
        split; (mstart Hs; rewrite Hbit; reflexivity).
      + right. split; [reflexivity |].
        split; (mstart Hs; rewrite Hbit; reflexivity).
  Qed.

  (** ** The node-decomposition gate at an enabled point

      Word 26 of the packing straddles the two children: its low 5 bits are
      the top 5 bits of the left child, its high 5 bits the bottom 5 bits of
      the right one.  Both halves are exact because the left child's top
      slice is itself below [2^5]. *)

  Lemma mb1_low (L left right : Z) (HL : 0 <= L < 2 ^ 10)
      (Hlf : 0 <= left < 2 ^ 255) :
    mnum L left right / 2 ^ 260 mod 2 ^ 10 mod 2 ^ 5 = left / 2 ^ 250.
  Proof.
    rewrite (mb26_val L left right HL Hlf).
    exact (mod_low (left / 2 ^ 250) (right mod 2 ^ 5) 5 ltac:(lia)
      (u_range left Hlf)).
  Qed.

  Lemma mb2_high (L left right : Z) (HL : 0 <= L < 2 ^ 10)
      (Hlf : 0 <= left < 2 ^ 255) :
    mnum L left right / 2 ^ 260 mod 2 ^ 10 / 2 ^ 5 = right mod 2 ^ 5.
  Proof.
    rewrite (mb26_val L left right HL Hlf).
    exact (div_low (left / 2 ^ 250) (right mod 2 ^ 5) 5 ltac:(lia)
      (u_range left Hlf)).
  Qed.

  Lemma md_point_1 (w : HonestInput) (Hvalid : valid w)
      (layer : RegionId.Merkle.Layer.t)
      (Hs : negb (RegionId.Merkle.Layer.to_index layer <? 16) = false) :
    forall body,
      List.In body
        (md_bodies Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4) ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (RegionId.Merkle layer RegionId.Merkle.Region.Decomposition, 0) body.
  Proof.
    pose proof (layer_L_range layer) as HL.
    pose proof (layer_left_range w Hvalid _ (FS.layer_index_lt layer)) as Hlf.
    pose proof (layer_right_range w Hvalid _ (FS.layer_index_lt layer)) as Hrt.
    apply (md_gate_eval _ _ Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (Z.of_nat (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (layer_left w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (layer_right w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))).
    - mstart Hs. rewrite mbits_0. exact (mb0_val _ _ _ HL).
    - mstart Hs. rewrite mbits_1. exact (mb1_val _ _ _ HL).
    - mstart Hs. rewrite mbits_25. exact (mb25_val _ _ _ HL Hlf).
    - mstart Hs. rewrite mbits_26. exact (mb26_val _ _ _ HL Hlf).
    - mstart Hs. rewrite mbits_27. exact (mb27_val _ _ _ HL Hlf Hrt).
    - mstart Hs. rewrite mword_26. exact (mb1_low _ _ _ HL Hlf).
    - mstart Hs. reflexivity.
    - mstart Hs. rewrite mword_26. exact (mb2_high _ _ _ HL Hlf).
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
  Qed.

  Lemma md_point_2 (w : HonestInput) (Hvalid : valid w)
      (layer : RegionId.Merkle.Layer.t)
      (Hs : negb (RegionId.Merkle.Layer.to_index layer <? 16) = true) :
    forall body,
      List.In body
        (md_bodies Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9) ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (RegionId.Merkle layer RegionId.Merkle.Region.Decomposition, 0) body.
  Proof.
    pose proof (layer_L_range layer) as HL.
    pose proof (layer_left_range w Hvalid _ (FS.layer_index_lt layer)) as Hlf.
    pose proof (layer_right_range w Hvalid _ (FS.layer_index_lt layer)) as Hrt.
    apply (md_gate_eval _ _ Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
      (Z.of_nat (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (layer_left w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))
      (layer_right w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))).
    - mstart Hs. rewrite mbits_0. exact (mb0_val _ _ _ HL).
    - mstart Hs. rewrite mbits_1. exact (mb1_val _ _ _ HL).
    - mstart Hs. rewrite mbits_25. exact (mb25_val _ _ _ HL Hlf).
    - mstart Hs. rewrite mbits_26. exact (mb26_val _ _ _ HL Hlf).
    - mstart Hs. rewrite mbits_27. exact (mb27_val _ _ _ HL Hlf Hrt).
    - mstart Hs. rewrite mword_26. exact (mb1_low _ _ _ HL Hlf).
    - mstart Hs. reflexivity.
    - mstart Hs. rewrite mword_26. exact (mb2_high _ _ _ HL Hlf).
    - mstart Hs. reflexivity.
    - mstart Hs. reflexivity.
  Qed.

  (** ** The obligation

      The shape certificate turns an enabled point guarded by one of the six
      selectors into its region and row, the [guarded_*_eq] certificates turn
      the constraint into one of the pinned bodies, and the point lemmas
      discharge it. *)
  Theorem residual_gates_forward : residual_selector_gates_ok.
  Proof.
    intros w Hvalid Hnondeg sel region row Hin Hres gate Hgate name body Hbody.
    pose proof (guarded_complete sel gate name body Hgate Hbody) as Hb.
    clear Hgate Hbody.
    pose proof (proj1 (List.forallb_forall _ _) residual_shape_cert _ Hin)
      as Hsh.
    cbn beta iota in Hsh.
    rewrite Hres in Hsh.
    cbn [implb] in Hsh.
    clear Hin Hres.
    destruct sel;
      try discriminate Hsh;
      destruct region as
        [wi | layer mr | pr | vr | nr | sr | ar | cr | wh ncr
        | | | | | | gr];
      try discriminate Hsh.
    (* [QOrchard]: the whole-circuit checks row. *)
    { cbn [residual_shape] in Hsh.
      apply Z.eqb_eq in Hsh. subst row.
      rewrite guarded_orchard_eq in Hb.
      exact (orchard_point w Hvalid body Hb). }
    (* [QAdd]: the nullifier scalar sum row. *)
    { destruct nr; try discriminate Hsh.
      cbn [residual_shape] in Hsh.
      apply Z.eqb_eq in Hsh. subst row.
      rewrite guarded_add_eq in Hb.
      exact (add_point w body Hb). }
    (* [QCondSwap1]: the [NodePosition] rows of layers 0–15. *)
    { destruct mr; try discriminate Hsh.
      cbn [residual_shape] in Hsh.
      apply andb_true_iff in Hsh.
      destruct Hsh as [Hrow Hsec].
      apply Z.eqb_eq in Hrow. subst row.
      apply negb_true_iff in Hsec.
      rewrite guarded_cs1_eq in Hb.
      exact (cs_point_1 w layer Hsec body Hb). }
    (* [QCondSwap2]: the [NodePosition] rows of layers 16–31. *)
    { destruct mr; try discriminate Hsh.
      cbn [residual_shape] in Hsh.
      apply andb_true_iff in Hsh.
      destruct Hsh as [Hrow Hsec].
      apply Z.eqb_eq in Hrow. subst row.
      rewrite guarded_cs2_eq in Hb.
      exact (cs_point_2 w layer Hsec body Hb). }
    (* [QMerkleDecompose1]: the [Decomposition] rows of layers 0–15. *)
    { destruct mr; try discriminate Hsh.
      cbn [residual_shape] in Hsh.
      apply andb_true_iff in Hsh.
      destruct Hsh as [Hrow Hsec].
      apply Z.eqb_eq in Hrow. subst row.
      apply negb_true_iff in Hsec.
      rewrite guarded_md1_eq in Hb.
      exact (md_point_1 w Hvalid layer Hsec body Hb). }
    (* [QMerkleDecompose2]: the [Decomposition] rows of layers 16–31. *)
    { destruct mr; try discriminate Hsh.
      cbn [residual_shape] in Hsh.
      apply andb_true_iff in Hsh.
      destruct Hsh as [Hrow Hsec].
      apply Z.eqb_eq in Hrow. subst row.
      rewrite guarded_md2_eq in Hb.
      exact (md_point_2 w Hvalid layer Hsec body Hb). }
  Qed.

End OrchardForwardResidual.

