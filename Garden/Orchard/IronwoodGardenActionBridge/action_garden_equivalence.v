(** * Direct equivalence of the translated and native Action functions

    The generated declarations are the mechanical mirror of Ironwood's
    standalone Garden-shaped source.  This file compares that public API
    directly with Garden's protocol specification; no legacy Core Action or
    bridge-local duplicate Action semantics is involved. *)

From Stdlib Require Import FunctionalExtensionality List ZArith Lia.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.EllipticCurve.PallasOrder.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.IronwoodGardenActionBridge.action_garden_bridge.
Require Import Garden.Orchard.IronwoodGardenActionBridge.action_garden_generated.
Require Import Garden.Orchard.IronwoodGardenActionBridge.action_garden_poseidon_bridge.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.main.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Plonky3.M.

Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module ActionGardenEquivalence.
  Module Bridge := ActionGardenBridge.
  Module PoseidonBridge := ActionGardenPoseidonBridge.

  Strategy transparent
    [Bridge.to_garden_point Bridge.from_garden_point
     ActionGardenZ_poseidonFullRound
     ActionGardenZ_poseidonPartialPair
     ActionGardenZ_poseidonPermute
     ActionGardenZ_poseidonHash2
     ActionGardenZ_orchardPoseidonRoundConstants
     ActionGardenZ_orchardPoseidonRoundConstant
     ActionGardenZ_orchardPoseidonMds
     ActionGardenZ_orchardPoseidonParameters
     p128pow5t3.get p128pow5t3.round_constant
     p128pow5t3.round_constants
     OrchardProtocolSpec.mul_spend_auth_g
     OrchardProtocolSpec.mul_value_commit_v
     OrchardProtocolSpec.mul_value_commit_r
     OrchardProtocolSpec.mul_nullifier_k
     OrchardProtocolSpec.mul_note_commit_r
     OrchardProtocolSpec.signed_net_value
     OrchardProtocolSpec.spend_auth_randomize
     OrchardProtocolSpec.value_commit
     OrchardProtocolSpec.nullifier
     OrchardProtocolSpec.note_commit
     OrchardProtocolSpec.OrchardCmx
     OrchardProtocolSpec.orchard_action_spec
     OrchardSpec.anchor
     ActionGardenZ_orchardAction].

  Definition to_garden_params
      (parameters : ActionGardenZ_Params) : OrchardSpec.Params := {|
    OrchardSpec.note_commit_q :=
      Bridge.to_garden_point parameters.(ActionGardenZ_paramsNoteCommitQ);
    OrchardSpec.commit_ivk_q :=
      Bridge.to_garden_point parameters.(ActionGardenZ_paramsCommitIvkQ);
    OrchardSpec.merkle_crh_q :=
      Bridge.to_garden_point parameters.(ActionGardenZ_paramsMerkleCrhQ)
  |}.

  Definition to_garden_action_input
      (input : ActionGardenZ_ActionInputs) : OrchardSpec.ActionInputs := {|
    OrchardSpec.in_ak :=
      Bridge.to_garden_point input.(ActionGardenZ_inAk);
    OrchardSpec.in_nk := input.(ActionGardenZ_inNk);
    OrchardSpec.in_rho_old := input.(ActionGardenZ_inRhoOld);
    OrchardSpec.in_psi_old := input.(ActionGardenZ_inPsiOld);
    OrchardSpec.in_cm_old :=
      Bridge.to_garden_point input.(ActionGardenZ_inCmOld);
    OrchardSpec.in_g_d_old :=
      Bridge.to_garden_point input.(ActionGardenZ_inGdOld);
    OrchardSpec.in_pk_d_old :=
      Bridge.to_garden_point input.(ActionGardenZ_inPkdOld);
    OrchardSpec.in_v_old := input.(ActionGardenZ_inVOld);
    OrchardSpec.in_rivk := input.(ActionGardenZ_inRivk);
    OrchardSpec.in_alpha := input.(ActionGardenZ_inAlpha);
    OrchardSpec.in_anchor_public := input.(ActionGardenZ_inAnchorPublic);
    OrchardSpec.in_rcv := input.(ActionGardenZ_inRcv);
    OrchardSpec.in_magnitude := input.(ActionGardenZ_inMagnitude);
    OrchardSpec.in_sign := input.(ActionGardenZ_inSign);
    OrchardSpec.in_leaf := input.(ActionGardenZ_inLeaf);
    OrchardSpec.in_path := input.(ActionGardenZ_inPath);
    OrchardSpec.in_g_d_new :=
      Bridge.to_garden_point input.(ActionGardenZ_inGdNew);
    OrchardSpec.in_pk_d_new :=
      Bridge.to_garden_point input.(ActionGardenZ_inPkdNew);
    OrchardSpec.in_v_new := input.(ActionGardenZ_inVNew);
    OrchardSpec.in_psi_new := input.(ActionGardenZ_inPsiNew);
    OrchardSpec.in_rcm_new := input.(ActionGardenZ_inRcmNew)
  |}.

  (** The inverse adapter is useful at the native-circuit boundary.  It is a
      representation conversion only: every integer field is copied and every
      point record is rebuilt with the same two coordinates. *)
  Definition from_garden_action_input
      (input : OrchardSpec.ActionInputs) : ActionGardenZ_ActionInputs := {|
    ActionGardenZ_inAk :=
      Bridge.from_garden_point input.(OrchardSpec.in_ak);
    ActionGardenZ_inNk := input.(OrchardSpec.in_nk);
    ActionGardenZ_inRhoOld := input.(OrchardSpec.in_rho_old);
    ActionGardenZ_inPsiOld := input.(OrchardSpec.in_psi_old);
    ActionGardenZ_inCmOld :=
      Bridge.from_garden_point input.(OrchardSpec.in_cm_old);
    ActionGardenZ_inGdOld :=
      Bridge.from_garden_point input.(OrchardSpec.in_g_d_old);
    ActionGardenZ_inPkdOld :=
      Bridge.from_garden_point input.(OrchardSpec.in_pk_d_old);
    ActionGardenZ_inVOld := input.(OrchardSpec.in_v_old);
    ActionGardenZ_inRivk := input.(OrchardSpec.in_rivk);
    ActionGardenZ_inAlpha := input.(OrchardSpec.in_alpha);
    ActionGardenZ_inAnchorPublic := input.(OrchardSpec.in_anchor_public);
    ActionGardenZ_inRcv := input.(OrchardSpec.in_rcv);
    ActionGardenZ_inMagnitude := input.(OrchardSpec.in_magnitude);
    ActionGardenZ_inSign := input.(OrchardSpec.in_sign);
    ActionGardenZ_inLeaf := input.(OrchardSpec.in_leaf);
    ActionGardenZ_inPath := input.(OrchardSpec.in_path);
    ActionGardenZ_inGdNew :=
      Bridge.from_garden_point input.(OrchardSpec.in_g_d_new);
    ActionGardenZ_inPkdNew :=
      Bridge.from_garden_point input.(OrchardSpec.in_pk_d_new);
    ActionGardenZ_inVNew := input.(OrchardSpec.in_v_new);
    ActionGardenZ_inPsiNew := input.(OrchardSpec.in_psi_new);
    ActionGardenZ_inRcmNew := input.(OrchardSpec.in_rcm_new)
  |}.

  Lemma to_from_garden_action_input (input : OrchardSpec.ActionInputs) :
    to_garden_action_input (from_garden_action_input input) = input.
  Proof.
    destruct input.
    cbn [to_garden_action_input from_garden_action_input].
    now repeat rewrite Bridge.to_from_garden_point.
  Qed.

  Definition to_garden_output
      (output : ActionGardenZ_ActionOutputs) : OrchardSpec.ActionOutputs := {|
    OrchardSpec.out_anchor := output.(ActionGardenZ_outAnchor);
    OrchardSpec.out_cv_net :=
      Bridge.to_garden_point output.(ActionGardenZ_outCvNet);
    OrchardSpec.out_nf_old := output.(ActionGardenZ_outNfOld);
    OrchardSpec.out_rk :=
      Bridge.to_garden_point output.(ActionGardenZ_outRk);
    OrchardSpec.out_cmx := output.(ActionGardenZ_outCmx)
  |}.

  Lemma spend_auth_g_eq :
    Bridge.to_garden_point ActionGardenZ_orchardSpendAuthG =
      PallasModel.repr PallasGenerators.spend_auth_g_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_commit_v_eq :
    Bridge.to_garden_point ActionGardenZ_orchardValueCommitVG =
      PallasModel.repr PallasGenerators.value_commit_v_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_commit_r_eq :
    Bridge.to_garden_point ActionGardenZ_orchardValueCommitRG =
      PallasModel.repr PallasGenerators.value_commit_r_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nullifier_k_eq :
    Bridge.to_garden_point ActionGardenZ_orchardNullifierKG =
      PallasModel.repr PallasGenerators.nullifier_k_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma note_commit_r_eq :
    Bridge.to_garden_point ActionGardenZ_orchardNoteCommitRG =
      PallasModel.repr PallasGenerators.note_commit_r_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma commit_ivk_r_eq :
    Bridge.to_garden_point ActionGardenZ_orchardCommitIvkRG =
      PallasModel.repr PallasGenerators.commit_ivk_r_G.
  Proof. vm_compute. reflexivity. Qed.

  (** A compact reflective certificate audits all 1,024 explicit Sinsemilla
      rows without expanding them into every downstream proof term. *)

  Definition same_generator_at (index : nat) : bool :=
    let word := Z.of_nat index in
    let standalone := ActionGardenZ_orchardSinsemillaGenerator word in
    let garden := SinsemillaSpec.generator word in
    (standalone.(actionGardenPointX) =? garden.(Point.x)) &&
    (standalone.(actionGardenPointY) =? garden.(Point.y)).

  Definition generator_table_check : bool :=
    List.forallb same_generator_at (List.seq 0 1024).

  Lemma generator_table_check_true : generator_table_check = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma generator_in_range (word : Z) :
    0 <= word < 1024 ->
    ActionGardenZ_orchardSinsemillaGenerator word =
      Bridge.from_garden_point (SinsemillaSpec.generator word).
  Proof.
    intros Hword.
    assert
      (Hin : List.In (Z.to_nat word) (List.seq 0 1024)).
    {
      apply List.in_seq.
      split; [lia |].
      pose proof
        (Z2Nat.inj_lt word 1024 ltac:(lia) ltac:(lia))
        as HnatBound.
      apply (proj1 HnatBound).
      lia.
    }
    pose proof
      (proj1
        (List.forallb_forall same_generator_at (List.seq 0 1024))
        generator_table_check_true (Z.to_nat word) Hin)
      as Hsame.
    unfold same_generator_at in Hsame.
    rewrite Z2Nat.id in Hsame by lia.
    apply Bool.andb_true_iff in Hsame.
    destruct Hsame as [Hx Hy].
    apply Z.eqb_eq in Hx.
    apply Z.eqb_eq in Hy.
    destruct (ActionGardenZ_orchardSinsemillaGenerator word).
    destruct (SinsemillaSpec.generator word).
    cbn in Hx, Hy |- *.
    now subst.
  Qed.

  (** The 64 Poseidon rows get the same compact treatment as the larger
      Sinsemilla table. *)

  Definition same_poseidon_constant_at (index : nat) : bool :=
    let round := Z.of_nat index in
    let standalone :=
      ActionGardenZ_orchardPoseidonRoundConstant round in
    let garden :=
      Bridge.z_poseidon_parameters.(ActionGardenZ_roundConstant) round in
    (standalone.(ActionGardenZ_x0) =? garden.(ActionGardenZ_x0)) &&
    (standalone.(ActionGardenZ_x1) =? garden.(ActionGardenZ_x1)) &&
    (standalone.(ActionGardenZ_x2) =? garden.(ActionGardenZ_x2)).

  Definition poseidon_table_check : bool :=
    List.forallb same_poseidon_constant_at (List.seq 0 64).

  Lemma poseidon_table_check_true : poseidon_table_check = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma poseidon_constant_in_range (round : Z) :
    0 <= round < 64 ->
    ActionGardenZ_orchardPoseidonRoundConstant round =
      Bridge.z_poseidon_parameters.(ActionGardenZ_roundConstant) round.
  Proof.
    intros Hround.
    assert
      (Hin : List.In (Z.to_nat round) (List.seq 0 64)).
    {
      apply List.in_seq.
      split; [lia |].
      pose proof
        (Z2Nat.inj_lt round 64 ltac:(lia) ltac:(lia))
        as HnatBound.
      apply (proj1 HnatBound).
      lia.
    }
    pose proof
      (proj1
        (List.forallb_forall
          same_poseidon_constant_at (List.seq 0 64))
        poseidon_table_check_true (Z.to_nat round) Hin)
      as Hsame.
    unfold same_poseidon_constant_at in Hsame.
    rewrite Z2Nat.id in Hsame by lia.
    repeat rewrite Bool.andb_true_iff in Hsame.
    destruct Hsame as [HfirstTwo Hx2].
    destruct HfirstTwo as [Hx0 Hx1].
    apply Z.eqb_eq in Hx0.
    apply Z.eqb_eq in Hx1.
    apply Z.eqb_eq in Hx2.
    destruct (ActionGardenZ_orchardPoseidonRoundConstant round).
    destruct
      (Bridge.z_poseidon_parameters.(ActionGardenZ_roundConstant) round).
    cbn in Hx0, Hx1, Hx2 |- *.
    now subst.
  Qed.

  Lemma poseidon_mds_eq :
    ActionGardenZ_orchardPoseidonMds =
      Bridge.z_poseidon_parameters.(ActionGardenZ_mds).
  Proof. vm_compute. reflexivity. Qed.

  Lemma poseidon_array_length :
    Uint63.to_Z
      (PrimArray.length ActionGardenZ_orchardPoseidonRoundConstants) = 64.
  Proof. vm_compute. reflexivity. Qed.

  Lemma poseidon_constant_eq (round : Z) :
    ActionGardenZ_orchardPoseidonRoundConstant round =
      Bridge.z_poseidon_parameters.(ActionGardenZ_roundConstant) round.
  Proof.
    destruct (Z_lt_ge_dec round 0) as [Hnegative | Hnonnegative].
    - transitivity
        (ActionGardenZ_orchardPoseidonRoundConstant 0).
      + unfold ActionGardenZ_orchardPoseidonRoundConstant,
          ActionGardenZ_listGetDAtZ.
        unfold ActionGardenZ_zZero.
        cbn [Z.of_nat].
        rewrite Z.max_l by lia.
        change (Z.max 0 0) with 0.
        reflexivity.
      + rewrite (poseidon_constant_in_range 0) by lia.
        unfold Bridge.z_poseidon_parameters.
        cbn [ActionGardenZ_roundConstant].
        replace (Z.to_nat round) with 0%nat.
        * reflexivity.
        * destruct round; cbn in *; try lia; reflexivity.
    - destruct (Z_lt_ge_dec round 64) as [HinRange | HtooLarge].
      + apply poseidon_constant_in_range. lia.
      + assert
          (Hnat : (64 <= Z.to_nat round)%nat).
        {
          change (Z.to_nat 64 <= Z.to_nat round)%nat.
          apply (proj1 (Z2Nat.inj_le 64 round ltac:(lia) ltac:(lia))).
          lia.
        }
        unfold ActionGardenZ_orchardPoseidonRoundConstant,
          ActionGardenZ_listGetDAtZ.
        unfold ActionGardenZ_zZero.
        cbn [Z.of_nat].
        rewrite Z.max_r by lia.
        replace
          (Uint63.to_Z
            (PrimArray.length
              ActionGardenZ_orchardPoseidonRoundConstants))
          with 64 by exact poseidon_array_length.
        destruct (round <? 64) eqn:Hlookup.
        * apply Z.ltb_lt in Hlookup. lia.
        * unfold Bridge.z_poseidon_parameters.
          cbn [ActionGardenZ_roundConstant].
          unfold p128pow5t3.round_constant, p128pow5t3.get.
          assert
            (HoverFlow :
              (List.length p128pow5t3.round_constants <=
                Z.to_nat round)%nat).
          {
            replace
              (List.length p128pow5t3.round_constants)
              with 64%nat by (vm_compute; reflexivity).
            exact Hnat.
          }
          rewrite
            (List.nth_overflow
              p128pow5t3.round_constants
              (n := Z.to_nat round) [] HoverFlow).
          reflexivity.
  Qed.

  Lemma orchard_poseidon_parameters_eq :
    ActionGardenZ_orchardPoseidonParameters =
      Bridge.z_poseidon_parameters.
  Proof.
    destruct Bridge.z_poseidon_parameters as [gardenConstants gardenMds]
      eqn:Hgarden.
    unfold ActionGardenZ_orchardPoseidonParameters.
    cbn [ActionGardenZ_roundConstant ActionGardenZ_mds].
    assert
      (Hconstants :
        ActionGardenZ_orchardPoseidonRoundConstant = gardenConstants).
    {
      apply functional_extensionality.
      intro round.
      pose proof (poseidon_constant_eq round) as Hround.
      rewrite Hgarden in Hround.
      exact Hround.
    }
    assert (Hmds : ActionGardenZ_orchardPoseidonMds = gardenMds).
    {
      pose proof poseidon_mds_eq as H.
      rewrite Hgarden in H.
      exact H.
    }
    now subst.
  Qed.

  (** ** Total primitive correspondences *)

  Lemma point_add_garden_eq
      (left right : ActionGardenZ_Point) :
    Bridge.to_garden_point
      (ActionGardenZ_pointAddGarden left right) =
    EccSpec.point_add
      (Bridge.to_garden_point left) (Bridge.to_garden_point right).
  Proof.
    destruct left as [leftX leftY].
    destruct right as [rightX rightY].
    unfold ActionGardenZ_pointAddGarden, EccSpec.point_add,
      add_proof.CompleteAddition.output,
      Bridge.to_garden_point, ActionGardenZ_zEq,
      ActionGardenZ_zZero.
    cbn [Z.of_nat Point.x Point.y actionGardenPointX actionGardenPointY].
    rewrite Bridge.base_add_eq.
    destruct (leftX =? 0); [reflexivity |].
    destruct (rightX =? 0); [reflexivity |].
    destruct (leftX =? rightX) eqn:Hx.
    - destruct (leftY +F rightY =? 0); [reflexivity |].
      rewrite !Bridge.base_mul_eq, !Bridge.base_sub_eq,
        Bridge.base_div_eq.
      unfold
        Garden.Halo2.halo2_gadgets.utilities_proof.square,
        ActionGardenZ_zTwo.
      reflexivity.
    - rewrite !Bridge.base_mul_eq, !Bridge.base_sub_eq,
        Bridge.base_div_eq.
      unfold
        Garden.Halo2.halo2_gadgets.utilities_proof.square.
      reflexivity.
  Qed.

  Lemma point_add_incomplete_eq
      (left right : ActionGardenZ_Point) :
    Bridge.to_garden_point
      (ActionGardenZ_pointAddIncomplete left right) =
    EccSpec.point_add_incomplete
      (Bridge.to_garden_point left) (Bridge.to_garden_point right).
  Proof.
    destruct left as [leftX leftY].
    destruct right as [rightX rightY].
    unfold ActionGardenZ_pointAddIncomplete,
      EccSpec.point_add_incomplete,
      add_incomplete_proof.IncompleteAddition.output,
      Bridge.to_garden_point.
    cbn [Point.x Point.y actionGardenPointX actionGardenPointY].
    rewrite Bridge.base_div_eq, !Bridge.base_mul_eq,
      !Bridge.base_sub_eq.
    unfold Garden.Halo2.halo2_gadgets.utilities_proof.square.
    reflexivity.
  Qed.

  Lemma poseidon_hash2_eq (left right : Z) :
    ActionGardenZ_poseidonHash2
      ActionGardenZ_orchardPoseidonParameters left right =
    Poseidon.poseidon_hash2 left right.
  Proof.
    rewrite orchard_poseidon_parameters_eq.
    exact (PoseidonBridge.poseidon_hash2_eq left right).
  Qed.

  Lemma words_le_eq (count : nat) (value : Z) :
    ActionGardenZ_wordsLe count value =
      SinsemillaSpec.words_le count value.
  Proof.
    revert value.
    induction count as [| count IH]; intro value.
    - reflexivity.
    - cbn [ActionGardenZ_wordsLe SinsemillaSpec.words_le].
      unfold ActionGardenZ_zMod, ActionGardenZ_zDiv,
        ActionGardenZ_zPowNat, ActionGardenZ_zTwo,
        SinsemillaSpec.sinsemilla_k.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma sinsemilla_round_eq
      (accumulator : ActionGardenZ_Point) (word : Z)
      (Hword : 0 <= word < 1024) :
    Bridge.to_garden_point
      (ActionGardenZ_sinsemillaRound accumulator word) =
    SinsemillaSpec.round
      (Bridge.to_garden_point accumulator) word.
  Proof.
    unfold ActionGardenZ_sinsemillaRound, SinsemillaSpec.round.
    rewrite point_add_incomplete_eq.
    rewrite point_add_incomplete_eq.
    rewrite generator_in_range by exact Hword.
    rewrite Bridge.to_from_garden_point.
    reflexivity.
  Qed.

  Lemma sinsemilla_hash_to_point_eq
      (domain : ActionGardenZ_Point) (words : list Z)
      (Hwords :
        forall word : Z, In word words -> 0 <= word < 1024) :
    Bridge.to_garden_point
      (ActionGardenZ_sinsemillaHashToPointGarden domain words) =
    SinsemillaSpec.sinsemilla_hash_to_point
      (Bridge.to_garden_point domain) words.
  Proof.
    unfold ActionGardenZ_sinsemillaHashToPointGarden,
      SinsemillaSpec.sinsemilla_hash_to_point.
    revert domain Hwords.
    induction words as [| word rest IH]; intros domain Hwords.
    - reflexivity.
    - cbn [fold_left].
      rewrite
        (IH (ActionGardenZ_sinsemillaRound domain word)).
      + rewrite sinsemilla_round_eq.
        * reflexivity.
        * apply Hwords. now left.
      + intros tail Htail.
        apply Hwords. now right.
  Qed.

  (** The public standalone predicate intentionally uses the same raw
      [(0,0)] identity convention as Garden.  No canonicality premise is
      needed for this representation-only fact. *)
  Lemma scalar_mul_properties
      (scalar : Z) (point : Point.t)
      (Hscalar : Bridge.scalarCanonical scalar)
      (HpointCanonical : Bridge.pointCanonical point)
      (HpointValid : Bridge.pointValid point) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar (Bridge.from_garden_point point)) =
        EccSpec.scalar_mul scalar point /\
    Bridge.pointCanonical (EccSpec.scalar_mul scalar point) /\
    Bridge.pointValid (EccSpec.scalar_mul scalar point).
  Proof.
    split.
    - apply Bridge.scalar_mul_eq; assumption.
    - assert (Hnonnegative : 0 <= scalar)
        by (unfold Bridge.scalarCanonical in Hscalar; lia).
      pose proof
        (Bridge.point_nat_mul_properties
          (Z.to_nat scalar) point HpointCanonical HpointValid)
        as (Heq & Hcanonical & Hvalid).
      rewrite (Z2Nat.id scalar Hnonnegative) in Hcanonical, Hvalid.
      now split.
  Qed.

  Lemma scalar_mul_fixed_eq
      (scalar : Z) (generator : Pallas.point)
      (Hscalar : Bridge.scalarCanonical scalar)
      (HgeneratorCanonical :
        Bridge.pointCanonical (PallasModel.repr generator))
      (HgeneratorValid :
        Bridge.pointValid (PallasModel.repr generator))
      (HgeneratorReduced : Pallas.reduced generator)
      (HgeneratorOnCurve : Pallas.on_curve generator) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar
        (Bridge.from_garden_point (PallasModel.repr generator))) =
        PallasModel.repr (Pallas.mul scalar generator) /\
    Bridge.pointCanonical
      (PallasModel.repr (Pallas.mul scalar generator)) /\
    Bridge.pointValid
      (PallasModel.repr (Pallas.mul scalar generator)).
  Proof.
    pose proof
      (scalar_mul_properties scalar (PallasModel.repr generator)
        Hscalar HgeneratorCanonical HgeneratorValid)
      as (Heq & Hcanonical & Hvalid).
    assert (Hnonnegative : 0 <= scalar)
      by (unfold Bridge.scalarCanonical in Hscalar; lia).
    pose proof
      (PallasModel.mul_equiv_scalar_mul scalar generator
        Hnonnegative HgeneratorReduced HgeneratorOnCurve) as Hprotocol.
    rewrite <- Hprotocol in Heq, Hcanonical, Hvalid.
    now split.
  Qed.

  Lemma words_le_are_words
      (count : nat) (value word : Z)
      (Hword : In word (ActionGardenZ_wordsLe count value)) :
    0 <= word < 1024.
  Proof.
    rewrite words_le_eq in Hword.
    exact (Bridge.words_le_in_range count value word Hword).
  Qed.

  Lemma note_commit_message_eq
      (gd pkd : ActionGardenZ_Point) (value rho psi : Z) :
    ActionGardenZ_noteCommitMessageGarden gd pkd value rho psi =
    OrchardSpec.note_commit_message
      (Bridge.to_garden_point gd) (Bridge.to_garden_point pkd)
      value rho psi.
  Proof.
    unfold ActionGardenZ_noteCommitMessageGarden,
      OrchardSpec.note_commit_message.
    rewrite words_le_eq.
    apply f_equal.
    destruct gd as [gdX gdY].
    destruct pkd as [pkdX pkdY].
    unfold ActionGardenZ_extractXGarden, ActionGardenZ_pointParity,
      ActionGardenZ_zAdd, ActionGardenZ_zMul, ActionGardenZ_zMod,
      ActionGardenZ_zPowNat, ActionGardenZ_zTwo,
      ActionGardenZ_zZero, Bridge.to_garden_point, EccSpec.extract_x.
    cbn [Point.x Point.y actionGardenPointX actionGardenPointY Z.of_nat].
    change
      (gdX + (gdY mod 2) * 2 ^ 255 +
         pkdX * 2 ^ 256 + (pkdY mod 2) * 2 ^ 511 +
         value * 2 ^ 512 + rho * 2 ^ 576 + psi * 2 ^ 831 +
         0 + 0 =
       gdX + (gdY mod 2) * 2 ^ 255 +
         pkdX * 2 ^ 256 + (pkdY mod 2) * 2 ^ 511 +
         value * 2 ^ 512 + rho * 2 ^ 576 + psi * 2 ^ 831).
    ring.
  Qed.

  Lemma commit_ivk_message_eq (ak nk : Z) :
    ActionGardenZ_commitIvkMessageGarden ak nk =
      OrchardSpec.commit_ivk_message ak nk.
  Proof.
    unfold ActionGardenZ_commitIvkMessageGarden,
      OrchardSpec.commit_ivk_message.
    rewrite words_le_eq.
    unfold ActionGardenZ_zAdd, ActionGardenZ_zMul,
      ActionGardenZ_zPowNat, ActionGardenZ_zTwo.
    reflexivity.
  Qed.

  Lemma merkle_message_eq (layer left right : Z) :
    ActionGardenZ_merkleMessageGarden layer left right =
      SinsemillaSpec.merkle_message layer left right.
  Proof.
    unfold ActionGardenZ_merkleMessageGarden,
      SinsemillaSpec.merkle_message.
    rewrite words_le_eq.
    unfold ActionGardenZ_zAdd, ActionGardenZ_zMul,
      ActionGardenZ_zPowNat, ActionGardenZ_zTwo,
      SinsemillaSpec.sinsemilla_k.
    apply f_equal.
    change
      (layer + (left * 2 ^ 10 + right * 2 ^ 265) =
       layer + left * 2 ^ 10 + right * 2 ^ 265).
    ring.
  Qed.

  (** The standalone scalar operation first chooses the canonical residue.
      Repeating that normalization changes neither its iteration count nor its
      result. *)
  Lemma scalar_mul_normalize
      (scalar : Z) (point : ActionGardenZ_Point) :
    ActionGardenZ_scalarMul scalar point =
      ActionGardenZ_scalarMul
        (ActionGardenZ_scalarNormalize scalar) point.
  Proof.
    unfold ActionGardenZ_scalarMul.
    rewrite !Bridge.scalar_normalize_eq.
    rewrite Z.mod_mod by
      (pose proof (prime_range (p := Primes.pallas_q)); lia).
    reflexivity.
  Qed.

  Lemma normalized_scalar_canonical (scalar : Z) :
    Bridge.scalarCanonical (ActionGardenZ_scalarNormalize scalar).
  Proof.
    unfold Bridge.scalarCanonical.
    rewrite Bridge.scalar_normalize_eq.
    apply Z.mod_pos_bound.
    pose proof (prime_range (p := Primes.pallas_q)).
    lia.
  Qed.

  (** Generic all-[Z] bridge for a fixed generator of order [pallas_q].
      The standalone side computes with [scalar mod q]; the order certificate
      proves that Garden's group multiple by the original integer is equal. *)
  Lemma scalar_mul_fixed_total
      (scalar : Z)
      (standaloneGenerator : ActionGardenZ_Point)
      (generator : Pallas.point)
      (Hcoordinates :
        Bridge.to_garden_point standaloneGenerator =
          PallasModel.repr generator)
      (Hcanonical :
        Bridge.pointCanonical (PallasModel.repr generator))
      (Hvalid :
        Bridge.pointValid (PallasModel.repr generator))
      (Hreduced : Pallas.reduced generator)
      (HonCurve : Pallas.on_curve generator)
      (Hinjective :
        forall i j : Z,
          Pallas.mul i generator = Pallas.mul j generator <->
          i mod Primes.pallas_q = j mod Primes.pallas_q) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar standaloneGenerator) =
      PallasModel.repr (Pallas.mul scalar generator).
  Proof.
    assert
      (Hstandalone :
        standaloneGenerator =
          Bridge.from_garden_point (PallasModel.repr generator)).
    {
      apply (proj1
        (Bridge.to_garden_point_eq_iff standaloneGenerator
          (Bridge.from_garden_point (PallasModel.repr generator)))).
      rewrite Bridge.to_from_garden_point.
      exact Hcoordinates.
    }
    rewrite scalar_mul_normalize.
    rewrite Hstandalone.
    pose proof
      (proj1
        (scalar_mul_fixed_eq
          (ActionGardenZ_scalarNormalize scalar) generator
          (normalized_scalar_canonical scalar)
          Hcanonical Hvalid Hreduced HonCurve))
      as Hnormalized.
    rewrite Hnormalized.
    apply f_equal.
    apply
      (proj2
        (Hinjective (ActionGardenZ_scalarNormalize scalar) scalar)).
    rewrite Bridge.scalar_normalize_eq.
    rewrite Z.mod_mod by
      (pose proof (prime_range (p := Primes.pallas_q)); lia).
    reflexivity.
  Qed.

  Lemma spend_auth_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardSpendAuthG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.spend_auth_g_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact spend_auth_g_eq.
    - rewrite <- spend_auth_g_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardSpendAuthG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- spend_auth_g_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardSpendAuthG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.spend_auth_g_reduced.
    - exact PallasGenerators.spend_auth_g_on_curve.
    - exact PallasGeneratorsOrder.spend_auth_g_mul_injective.
  Qed.

  Lemma value_commit_v_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardValueCommitVG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.value_commit_v_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact value_commit_v_eq.
    - rewrite <- value_commit_v_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardValueCommitVG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- value_commit_v_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardValueCommitVG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.value_commit_v_reduced.
    - exact PallasGenerators.value_commit_v_on_curve.
    - exact PallasGeneratorsOrder.value_commit_v_mul_injective.
  Qed.

  Lemma value_commit_r_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardValueCommitRG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.value_commit_r_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact value_commit_r_eq.
    - rewrite <- value_commit_r_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardValueCommitRG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- value_commit_r_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardValueCommitRG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.value_commit_r_reduced.
    - exact PallasGenerators.value_commit_r_on_curve.
    - exact PallasGeneratorsOrder.value_commit_r_mul_injective.
  Qed.

  Lemma nullifier_k_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardNullifierKG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.nullifier_k_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact nullifier_k_eq.
    - rewrite <- nullifier_k_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardNullifierKG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- nullifier_k_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardNullifierKG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.nullifier_k_reduced.
    - exact PallasGenerators.nullifier_k_on_curve.
    - exact PallasGeneratorsOrder.nullifier_k_mul_injective.
  Qed.

  Lemma note_commit_r_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardNoteCommitRG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.note_commit_r_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact note_commit_r_eq.
    - rewrite <- note_commit_r_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardNoteCommitRG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- note_commit_r_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardNoteCommitRG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.note_commit_r_reduced.
    - exact PallasGenerators.note_commit_r_on_curve.
    - exact PallasGeneratorsOrder.note_commit_r_mul_injective.
  Qed.

  Lemma commit_ivk_r_mul_eq (scalar : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardCommitIvkRG) =
    PallasModel.repr
      (Pallas.mul scalar PallasGenerators.commit_ivk_r_G).
  Proof.
    apply scalar_mul_fixed_total.
    - exact commit_ivk_r_eq.
    - rewrite <- commit_ivk_r_eq.
      apply
        (proj1
          (Bridge.zpoint_canonical_iff
            ActionGardenZ_orchardCommitIvkRG)).
      vm_compute. split; reflexivity.
    - right.
      rewrite <- commit_ivk_r_eq.
      apply
        (proj1
          (Bridge.zpoint_on_curve_iff
            ActionGardenZ_orchardCommitIvkRG)).
      vm_compute. reflexivity.
    - exact PallasGenerators.commit_ivk_r_reduced.
    - exact PallasGenerators.commit_ivk_r_on_curve.
    - exact PallasGeneratorsOrder.commit_ivk_r_mul_injective.
  Qed.

  (** ** Total protocol-operation correspondences *)

  Lemma signed_net_value_eq (magnitude sign : Z) :
    ActionGardenZ_signedNetValue magnitude sign =
      OrchardProtocolSpec.signed_net_value magnitude sign.
  Proof.
    unfold ActionGardenZ_signedNetValue,
      OrchardProtocolSpec.signed_net_value,
      ActionGardenZ_zEq, ActionGardenZ_zOne, ActionGardenZ_zNeg.
    cbn [Z.of_nat].
    reflexivity.
  Qed.

  Lemma spend_auth_randomize_eq
      (ak : ActionGardenZ_Point) (alpha : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_spendAuthRandomize ak alpha) =
    OrchardProtocolSpec.spend_auth_randomize
      (Bridge.to_garden_point ak) alpha.
  Proof.
    unfold ActionGardenZ_spendAuthRandomize,
      OrchardProtocolSpec.spend_auth_randomize,
      OrchardProtocolSpec.mul_spend_auth_g.
    rewrite point_add_garden_eq.
    rewrite spend_auth_mul_eq.
    reflexivity.
  Qed.

  Lemma value_commit_eq (value randomness : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_valueCommit value randomness) =
    OrchardProtocolSpec.value_commit value randomness.
  Proof.
    unfold ActionGardenZ_valueCommit,
      OrchardProtocolSpec.value_commit,
      OrchardProtocolSpec.mul_value_commit_v,
      OrchardProtocolSpec.mul_value_commit_r.
    rewrite point_add_garden_eq.
    rewrite value_commit_v_mul_eq.
    rewrite value_commit_r_mul_eq.
    symmetry.
    apply PallasModel.repr_add.
    - apply Weierstrass.mul_reduced.
      exact PallasGenerators.value_commit_v_reduced.
    - apply Weierstrass.mul_reduced.
      exact PallasGenerators.value_commit_r_reduced.
    - exact
        (FixedBaseLadder.pallas_mul_on_curve
          value PallasGenerators.value_commit_v_G
          PallasGenerators.value_commit_v_on_curve).
    - exact
        (FixedBaseLadder.pallas_mul_on_curve
          randomness PallasGenerators.value_commit_r_G
          PallasGenerators.value_commit_r_on_curve).
  Qed.

  Lemma nullifier_eq
      (nk rho psi : Z) (cm : ActionGardenZ_Point) :
    ActionGardenZ_nullifier nk rho psi cm =
    OrchardProtocolSpec.nullifier
      nk rho psi (Bridge.to_garden_point cm).
  Proof.
    unfold ActionGardenZ_nullifier,
      OrchardProtocolSpec.nullifier,
      OrchardProtocolSpec.mul_nullifier_k.
    rewrite poseidon_hash2_eq.
    rewrite Bridge.base_add_eq.
    change
      (EccSpec.extract_x
        (Bridge.to_garden_point
          (ActionGardenZ_pointAddGarden
            (ActionGardenZ_scalarMul
              (Poseidon.poseidon_hash2 nk rho +F psi)
              ActionGardenZ_orchardNullifierKG)
            cm)) =
       EccSpec.extract_x
        (EccSpec.point_add
          (PallasModel.repr
            (Pallas.mul
              (Poseidon.poseidon_hash2 nk rho +F psi)
              PallasGenerators.nullifier_k_G))
          (Bridge.to_garden_point cm))).
    apply f_equal.
    rewrite point_add_garden_eq.
    rewrite nullifier_k_mul_eq.
    reflexivity.
  Qed.

  Lemma note_commit_message_words_range
      (gd pkd : ActionGardenZ_Point) (value rho psi word : Z)
      (Hword :
        In word
          (ActionGardenZ_noteCommitMessageGarden
            gd pkd value rho psi)) :
    0 <= word < 1024.
  Proof.
    unfold ActionGardenZ_noteCommitMessageGarden in Hword.
    exact
      (words_le_are_words 109
        (ActionGardenZ_zAdd
          (ActionGardenZ_zAdd
            (ActionGardenZ_zAdd
              (ActionGardenZ_zAdd
                (ActionGardenZ_zAdd
                  (ActionGardenZ_zAdd
                    (ActionGardenZ_zAdd
                      (ActionGardenZ_zAdd
                        (ActionGardenZ_extractXGarden gd)
                        (ActionGardenZ_zMul
                          (ActionGardenZ_pointParity gd)
                          (ActionGardenZ_zPowNat
                            ActionGardenZ_zTwo 255)))
                      (ActionGardenZ_zMul
                        (ActionGardenZ_extractXGarden pkd)
                        (ActionGardenZ_zPowNat
                          ActionGardenZ_zTwo 256)))
                    (ActionGardenZ_zMul
                      (ActionGardenZ_pointParity pkd)
                      (ActionGardenZ_zPowNat
                        ActionGardenZ_zTwo 511)))
                  (ActionGardenZ_zMul value
                    (ActionGardenZ_zPowNat
                      ActionGardenZ_zTwo 512)))
                (ActionGardenZ_zMul rho
                  (ActionGardenZ_zPowNat
                    ActionGardenZ_zTwo 576)))
              (ActionGardenZ_zMul psi
                (ActionGardenZ_zPowNat
                  ActionGardenZ_zTwo 831)))
            ActionGardenZ_zZero)
          ActionGardenZ_zZero)
        word Hword).
  Qed.

  Lemma commit_ivk_message_words_range
      (ak nk word : Z)
      (Hword :
        In word (ActionGardenZ_commitIvkMessageGarden ak nk)) :
    0 <= word < 1024.
  Proof.
    unfold ActionGardenZ_commitIvkMessageGarden in Hword.
    exact
      (words_le_are_words 51
        (ActionGardenZ_zAdd ak
          (ActionGardenZ_zMul nk
            (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255)))
        word Hword).
  Qed.

  Lemma merkle_message_words_range
      (layer left right word : Z)
      (Hword :
        In word
          (ActionGardenZ_merkleMessageGarden layer left right)) :
    0 <= word < 1024.
  Proof.
    unfold ActionGardenZ_merkleMessageGarden in Hword.
    exact
      (words_le_are_words 52
        (ActionGardenZ_zAdd layer
          (ActionGardenZ_zAdd
            (ActionGardenZ_zMul left
              (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10))
            (ActionGardenZ_zMul right
              (ActionGardenZ_zPowNat ActionGardenZ_zTwo 265))))
        word Hword).
  Qed.

  (** Keep the already-related recursive encoders and folds opaque while the
      component lemmas are composed.  This prevents kernel conversion from
      re-evaluating 109 symbolic rounds at each use. *)
  Strategy opaque
    [ActionGardenZ_wordsLe
     ActionGardenZ_noteCommitMessageGarden
     ActionGardenZ_commitIvkMessageGarden
     ActionGardenZ_merkleMessageGarden
     ActionGardenZ_sinsemillaRound
     ActionGardenZ_sinsemillaHashToPointGarden
     SinsemillaSpec.words_le
     SinsemillaSpec.round
     SinsemillaSpec.sinsemilla_hash_to_point
     SinsemillaSpec.merkle_message
     OrchardSpec.note_commit_message
     OrchardSpec.commit_ivk_message].

  Lemma note_commit_eq
      (parameters : ActionGardenZ_Params)
      (gd pkd : ActionGardenZ_Point)
      (value rho psi randomness : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_noteCommit parameters
        gd pkd value rho psi randomness) =
    OrchardProtocolSpec.note_commit
      (to_garden_params parameters)
      (Bridge.to_garden_point gd)
      (Bridge.to_garden_point pkd)
      value rho psi randomness.
  Proof.
    unfold ActionGardenZ_noteCommit,
      OrchardProtocolSpec.note_commit,
      OrchardProtocolSpec.mul_note_commit_r.
    rewrite point_add_garden_eq.
    rewrite note_commit_r_mul_eq.
    assert
      (Hhash :
        Bridge.to_garden_point
          (ActionGardenZ_sinsemillaHashToPointGarden
            parameters.(ActionGardenZ_paramsNoteCommitQ)
            (ActionGardenZ_noteCommitMessageGarden
              gd pkd value rho psi)) =
        SinsemillaSpec.sinsemilla_hash_to_point
          (Bridge.to_garden_point
            parameters.(ActionGardenZ_paramsNoteCommitQ))
          (OrchardSpec.note_commit_message
            (Bridge.to_garden_point gd)
            (Bridge.to_garden_point pkd)
            value rho psi)).
    {
      pose proof
        (sinsemilla_hash_to_point_eq
          parameters.(ActionGardenZ_paramsNoteCommitQ)
          (ActionGardenZ_noteCommitMessageGarden
            gd pkd value rho psi)
          (fun word Hword =>
            note_commit_message_words_range
              gd pkd value rho psi word Hword))
        as H.
      eapply eq_trans.
      - exact H.
      - apply f_equal.
        exact (note_commit_message_eq gd pkd value rho psi).
    }
    rewrite Hhash.
    reflexivity.
  Qed.

  Lemma commit_ivk_point_eq
      (parameters : ActionGardenZ_Params)
      (ak nk randomness : Z) :
    Bridge.to_garden_point
      (ActionGardenZ_commitIvk parameters ak nk randomness) =
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.commit_ivk_q (to_garden_params parameters))
        (OrchardSpec.commit_ivk_message ak nk))
      (PallasModel.repr
        (Pallas.mul randomness
          PallasGenerators.commit_ivk_r_G)).
  Proof.
    unfold ActionGardenZ_commitIvk.
    rewrite point_add_garden_eq.
    rewrite commit_ivk_r_mul_eq.
    assert
      (Hhash :
        Bridge.to_garden_point
          (ActionGardenZ_sinsemillaHashToPointGarden
            parameters.(ActionGardenZ_paramsCommitIvkQ)
            (ActionGardenZ_commitIvkMessageGarden ak nk)) =
        SinsemillaSpec.sinsemilla_hash_to_point
          (Bridge.to_garden_point
            parameters.(ActionGardenZ_paramsCommitIvkQ))
          (OrchardSpec.commit_ivk_message ak nk)).
    {
      pose proof
        (sinsemilla_hash_to_point_eq
          parameters.(ActionGardenZ_paramsCommitIvkQ)
          (ActionGardenZ_commitIvkMessageGarden ak nk)
          (fun word Hword =>
            commit_ivk_message_words_range
              ak nk word Hword))
        as H.
      eapply eq_trans.
      - exact H.
      - apply f_equal.
        exact (commit_ivk_message_eq ak nk).
    }
    rewrite Hhash.
    reflexivity.
  Qed.

  Lemma merkle_layer_eq
      (domain : ActionGardenZ_Point)
      (layer node sibling : Z) (isRight : bool) :
    ActionGardenZ_merkleLayer
      domain layer node sibling isRight =
    SinsemillaSpec.merkle_layer
      (Bridge.to_garden_point domain)
      layer node sibling isRight.
  Proof.
    unfold ActionGardenZ_merkleLayer,
      SinsemillaSpec.merkle_layer,
      SinsemillaSpec.merkle_crh,
      SinsemillaSpec.sinsemilla_hash,
      ActionGardenZ_extractXGarden,
      EccSpec.extract_x.
    destruct isRight.
    - assert
        (Hhash :
          Bridge.to_garden_point
            (ActionGardenZ_sinsemillaHashToPointGarden domain
              (ActionGardenZ_merkleMessageGarden
                layer sibling node)) =
          SinsemillaSpec.sinsemilla_hash_to_point
            (Bridge.to_garden_point domain)
            (SinsemillaSpec.merkle_message
              layer sibling node)).
      {
        pose proof
          (sinsemilla_hash_to_point_eq domain
            (ActionGardenZ_merkleMessageGarden
              layer sibling node)
            (fun word Hword =>
              merkle_message_words_range
                layer sibling node word Hword))
          as H.
        eapply eq_trans.
        * exact H.
        * apply f_equal.
          exact (merkle_message_eq layer sibling node).
      }
      exact (f_equal Point.x Hhash).
    - assert
        (Hhash :
          Bridge.to_garden_point
            (ActionGardenZ_sinsemillaHashToPointGarden domain
              (ActionGardenZ_merkleMessageGarden
                layer node sibling)) =
          SinsemillaSpec.sinsemilla_hash_to_point
            (Bridge.to_garden_point domain)
            (SinsemillaSpec.merkle_message
              layer node sibling)).
      {
        pose proof
          (sinsemilla_hash_to_point_eq domain
            (ActionGardenZ_merkleMessageGarden
              layer node sibling)
            (fun word Hword =>
              merkle_message_words_range
                layer node sibling word Hword))
          as H.
        eapply eq_trans.
        * exact H.
        * apply f_equal.
          exact (merkle_message_eq layer node sibling).
      }
      exact (f_equal Point.x Hhash).
  Qed.

  Strategy opaque
    [ActionGardenZ_merkleLayer SinsemillaSpec.merkle_layer].

  Lemma fold_left_pointwise
      {A B : Type} (leftStep rightStep : B -> A -> B)
      (values : list A) (initial : B)
      (Hstep :
        forall (accumulator : B) (value : A),
          leftStep accumulator value =
            rightStep accumulator value) :
    fold_left leftStep values initial =
      fold_left rightStep values initial.
  Proof.
    revert initial.
    induction values as [| value rest IH]; intro initial.
    - reflexivity.
    - cbn [fold_left].
      rewrite Hstep.
      apply IH.
  Qed.

  Lemma merkle_root_eq
      (domain : ActionGardenZ_Point)
      (leaf : Z) (path : list (Z * Z * bool)) :
    ActionGardenZ_merkleRootGarden domain leaf path =
      SinsemillaSpec.merkle_root
        (Bridge.to_garden_point domain) leaf path.
  Proof.
    unfold ActionGardenZ_merkleRootGarden,
      SinsemillaSpec.merkle_root.
    apply fold_left_pointwise.
    intros node element.
    destruct element as [pair isRight].
    destruct pair as [layer sibling].
    cbn [fst snd].
    apply merkle_layer_eq.
  Qed.

  (** Compare output records field by field without reducing all cryptographic
      expressions under one record equality. *)
  Lemma action_outputs_ext
      (left right : OrchardSpec.ActionOutputs)
      (Hanchor : OrchardSpec.out_anchor left = OrchardSpec.out_anchor right)
      (Hcv : OrchardSpec.out_cv_net left = OrchardSpec.out_cv_net right)
      (Hnf : OrchardSpec.out_nf_old left = OrchardSpec.out_nf_old right)
      (Hrk : OrchardSpec.out_rk left = OrchardSpec.out_rk right)
      (Hcmx : OrchardSpec.out_cmx left = OrchardSpec.out_cmx right) :
    left = right.
  Proof.
    destruct left as [leftAnchor leftCv leftNf leftRk leftCmx].
    destruct right as [rightAnchor rightCv rightNf rightRk rightCmx].
    cbn in Hanchor, Hcv, Hnf, Hrk, Hcmx.
    subst.
    reflexivity.
  Qed.

  Theorem orchard_action_output_eq
      (parameters : ActionGardenZ_Params)
      (input : ActionGardenZ_ActionInputs) :
    to_garden_output
      (ActionGardenZ_orchardAction parameters input) =
    OrchardProtocolSpec.orchard_action_spec
      (to_garden_params parameters)
      (to_garden_action_input input).
  Proof.
    destruct parameters as [noteQ commitQ merkleQ].
    destruct input as
      [ak nk rhoOld psiOld cmOld gdOld pkdOld vOld rivk alpha
       anchorPublic rcv magnitude sign leaf path gdNew pkdNew
       vNew psiNew rcmNew].
    apply action_outputs_ext.
    - cbv beta iota zeta delta
        [to_garden_output to_garden_params to_garden_action_input
        ActionGardenZ_orchardAction
        OrchardProtocolSpec.orchard_action_spec].
      cbv beta iota zeta delta
        [OrchardSpec.out_anchor ActionGardenZ_outAnchor
         OrchardSpec.in_v_old ActionGardenZ_inVOld
         OrchardSpec.in_anchor_public ActionGardenZ_inAnchorPublic
         OrchardSpec.in_leaf ActionGardenZ_inLeaf
         OrchardSpec.in_path ActionGardenZ_inPath
         OrchardSpec.merkle_crh_q ActionGardenZ_paramsMerkleCrhQ].
      unfold ActionGardenZ_zEq, ActionGardenZ_zZero.
      cbn [Z.of_nat].
      destruct (vOld =? 0).
      + reflexivity.
      + apply merkle_root_eq.
    - cbv beta iota zeta delta
        [to_garden_output to_garden_params to_garden_action_input
        ActionGardenZ_orchardAction
        OrchardProtocolSpec.orchard_action_spec].
      cbv beta iota zeta delta
        [OrchardSpec.out_cv_net ActionGardenZ_outCvNet
         OrchardSpec.in_magnitude ActionGardenZ_inMagnitude
         OrchardSpec.in_sign ActionGardenZ_inSign
         OrchardSpec.in_rcv ActionGardenZ_inRcv].
      rewrite signed_net_value_eq.
      apply value_commit_eq.
    - cbv beta iota zeta delta
        [to_garden_output to_garden_params to_garden_action_input
        ActionGardenZ_orchardAction
        OrchardProtocolSpec.orchard_action_spec].
      cbv beta iota zeta delta
        [OrchardSpec.out_nf_old ActionGardenZ_outNfOld
         OrchardSpec.in_nk ActionGardenZ_inNk
         OrchardSpec.in_rho_old ActionGardenZ_inRhoOld
         OrchardSpec.in_psi_old ActionGardenZ_inPsiOld
         OrchardSpec.in_cm_old ActionGardenZ_inCmOld].
      apply nullifier_eq.
    - cbv beta iota zeta delta
        [to_garden_output to_garden_params to_garden_action_input
        ActionGardenZ_orchardAction
        OrchardProtocolSpec.orchard_action_spec].
      cbv beta iota zeta delta
        [OrchardSpec.out_rk ActionGardenZ_outRk
         OrchardSpec.in_ak ActionGardenZ_inAk
         OrchardSpec.in_alpha ActionGardenZ_inAlpha].
      apply spend_auth_randomize_eq.
    - cbv beta iota zeta delta
        [to_garden_output to_garden_params to_garden_action_input
        ActionGardenZ_orchardAction
        OrchardProtocolSpec.orchard_action_spec].
      cbv beta iota zeta delta
        [OrchardSpec.out_cmx ActionGardenZ_outCmx
         OrchardSpec.in_nk ActionGardenZ_inNk
         OrchardSpec.in_rho_old ActionGardenZ_inRhoOld
         OrchardSpec.in_psi_old ActionGardenZ_inPsiOld
         OrchardSpec.in_cm_old ActionGardenZ_inCmOld
         OrchardSpec.in_g_d_new ActionGardenZ_inGdNew
         OrchardSpec.in_pk_d_new ActionGardenZ_inPkdNew
         OrchardSpec.in_v_new ActionGardenZ_inVNew
         OrchardSpec.in_psi_new ActionGardenZ_inPsiNew
         OrchardSpec.in_rcm_new ActionGardenZ_inRcmNew
         OrchardSpec.note_commit_q ActionGardenZ_paramsNoteCommitQ].
      rewrite nullifier_eq.
      unfold OrchardProtocolSpec.OrchardCmx, EccSpec.extract_x,
        ActionGardenZ_extractXGarden.
      pose proof
        (note_commit_eq
          {| ActionGardenZ_paramsNoteCommitQ := noteQ;
             ActionGardenZ_paramsCommitIvkQ := commitQ;
             ActionGardenZ_paramsMerkleCrhQ := merkleQ |}
          gdNew pkdNew vNew
          (OrchardProtocolSpec.nullifier
            nk rhoOld psiOld (Bridge.to_garden_point cmOld))
          psiNew rcmNew)
        as Hnote.
      exact (f_equal Point.x Hnote).
  Qed.

  (** The three standalone domain-point literals are exactly the concrete
      parameters used by the current Post-NU6.3 Orchard circuit. *)
  Lemma orchard_params_eq :
    to_garden_params ActionGardenZ_orchardParams =
      OrchardActionInputs.orchard_circuit_params.
  Proof. vm_compute. reflexivity. Qed.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** Compose Garden's native circuit theorem with the unconditional function
      equality above.  The result mentions the translated Ironwood function
      directly and therefore has no bridge-local Action semantics. *)
  Theorem orchard_action_output_of_action_statement
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
      (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ)
      (Hold_note_ok : OrchardValidActionInputs.old_note_witness_ok Γ)
      (Hivk_ok : OrchardValidActionInputs.commit_ivk_witness_ok Γ) :
    OrchardActionInputs.read_action_outputs Γ =
      to_garden_output
        (ActionGardenZ_orchardAction ActionGardenZ_orchardParams
          (from_garden_action_input
            (OrchardActionInputs.read_action_inputs Γ))).
  Proof.
    destruct
      (OrchardAction.action_statement Γ Hcircuit
        Hmerkle_ok Hnote_ok Hold_note_ok Hivk_ok)
      as [Houtput _].
    rewrite Houtput.
    symmetry.
    rewrite
      (orchard_action_output_eq ActionGardenZ_orchardParams
        (from_garden_action_input
          (OrchardActionInputs.read_action_inputs Γ))).
    now rewrite orchard_params_eq, to_from_garden_action_input.
  Qed.

  (** Input-side component supplied by the same native Post-NU6.3 theorem.
      This deliberately keeps Garden's Γ-indexed ownership witnesses in their
      native form instead of inventing a second record-level predicate. *)
  Theorem native_valid_action_inputs_of_action_statement
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
      (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ)
      (Hold_note_ok : OrchardValidActionInputs.old_note_witness_ok Γ)
      (Hivk_ok : OrchardValidActionInputs.commit_ivk_witness_ok Γ) :
    OrchardValidActionInputs.ValidActionInputs Γ.
  Proof.
    exact
      (proj2
        (OrchardAction.action_statement Γ Hcircuit
          Hmerkle_ok Hnote_ok Hold_note_ok Hivk_ok)).
  Qed.

End ActionGardenEquivalence.
