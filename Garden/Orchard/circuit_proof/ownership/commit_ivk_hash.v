(** * CommitIvk: hashed-words canonicity, the 51-word hash fold, and the
    ivk complete add

    The [Commit^ivk] sub-circuit ([Garden/Orchard/circuit/commit_ivk.v])
    against [OrchardProtocolSpec.commit_ivk]'s ingredients, from a satisfying
    assignment ([Holds Γ]):

    - [commit_ivk_words_correct] (words canonicity): the 51 grid words hashed
      at [RegionId.CommitIvk.HashToPoint] equal
      [OrchardSpec.commit_ivk_message] of the witnessed [ak] x-coordinate and
      [nk] — §4.18.4's ivk-canonicity MUST, realized by the [QCommitIvk]
      canonicity gate, the a/b/c/d piece decomposition, and the
      [AkLookup]/[NkLookup] running lookups.  Side condition:
      [commit_ivk_short_lookup_ok] — the three short-lookup range cells
      ([b_0] 4 bits, [b_2] 5 bits, [d_0] 9 bits), underivable from [Holds]
      for the same selector-plane reason as
      [NoteCommitNewWords.note_commit_new_short_lookup_ok]
      ([circuit_proof/note_commit/words.v]).

    - [commit_ivk_hash_point_correct] (the hash fold): the hash-to-point
      output cells ([A0]/[A3] at row 51) equal
      [SinsemillaSpec.sinsemilla_hash_to_point] of the CommitIvk domain
      point over those words, under Sinsemilla incomplete-add nondegeneracy
      (the [merkle_layer_ok] precedent; Sinsemilla variant 1).

    - [commit_ivk_point_add_correct] (the complete add): the ivk output
      point (the [CompletePointAdd] region's result cells) is
      [EccSpec.point_add] of the hash point and
      [EccSpec.fixed_scalar_mul] of the CommitIvkR spec table at the read
      scalar/us — the blinding leg as the circuit's ladder fold.  The
      ladder-distinctness precondition is an explicit hypothesis
      ([Hdistinct]); [circuit_proof/ownership/diversified_address.v]
      discharges it from [Holds] via the CommitIvkR certificate set
      ([circuit_proof/commit_ivk_r/], the [ladder/note_commit_r.v] pattern)
      and performs the fold-to-group-multiple switch
      ([protocol_mul/commit_ivk_r.v]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.constants.fixed_bases.commit_ivk_r.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_fold_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.pieces.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module CIvk := Garden.Orchard.circuit.commit_ivk.

(* The consumed fixed-base lemmas carry [is_square]/[field_sqrt]/
   [fixed_window_point_canonical] over the concrete Pallas modulus;
   conversion must compare them by congruence, never unfold. *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module CommitIvkHash.
  Import OrchardActionInputs.
  Import OrchardActionMerkle.
  Module W := NoteCommitNewWords.
  Module MP := NoteCommitMessagePieces.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Region and cell shorthands *)

  Definition cir (r : RegionId.CommitIvk.t) : RegionId.t :=
    RegionId.CommitIvk r.

  (** The CommitIvk hash-to-point region. *)
  Definition HR : RegionId.t := cir RegionId.CommitIvk.HashToPoint.
  (** The two canonicity running-lookup regions. *)
  Definition AKL : RegionId.t := cir RegionId.CommitIvk.AkLookup.
  Definition NKL : RegionId.t := cir RegionId.CommitIvk.NkLookup.
  (** The two-row canonicity-gate region. *)
  Definition CG : RegionId.t := cir RegionId.CommitIvk.CanonicityGate.
  (** The CommitIvkR blinding-leg regions. *)
  Definition CIR : RegionId.t := cir RegionId.CommitIvk.FixedBaseIncomplete.
  Definition CLR : RegionId.t := cir RegionId.CommitIvk.FixedBaseLast.
  (** The "M + [r] R" complete-add region. *)
  Definition CADD : RegionId.t := cir RegionId.CommitIvk.CompletePointAdd.

  (** The witnessed [ak_P] x-cell and [nk] cell fed to [CIvk.synthesize]
      (from [synthesize_witness_inputs]; the cells [read_action_inputs]'s
      [in_ak]/[in_nk] read). *)
  Definition ak_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (RegionId.WitnessInput RegionId.WitnessInput.AkP) Advice.A0 0.
  Definition nk_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (RegionId.WitnessInput RegionId.WitnessInput.Nk) Advice.A0 0.

  (** The four witnessed message-piece cells. *)
  Definition piece_a : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (cir RegionId.CommitIvk.WitnessA) Advice.A6 0.
  Definition piece_b : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (cir RegionId.CommitIvk.WitnessB) Advice.A6 0.
  Definition piece_c : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (cir RegionId.CommitIvk.WitnessC) Advice.A6 0.
  Definition piece_d : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    W.adv (cir RegionId.CommitIvk.WitnessD) Advice.A6 0.

  (** The CommitIvk Sinsemilla domain point [Q("Commit-ivk")], as pinned by
      the hash-to-point synthesis constants. *)
  Definition commit_ivk_Q : Point.t := {|
    Point.x := CIvk.q_commit_ivk_m_x;
    Point.y := CIvk.q_commit_ivk_m_y;
  |}.

  Lemma commit_ivk_Q_eq :
    commit_ivk_Q = OrchardSpec.commit_ivk_q orchard_circuit_params.
  Proof. reflexivity. Qed.

  (** The 51 message words consumed by the CommitIvk hash-to-point region
      (Sinsemilla variant 1: running-sum column A2, [q_s2] column
      [QSinsemilla2_1]) — definitionally
      [OrchardValidActionInputs.commit_ivk_words]. *)
  Definition commit_ivk_words (Γ : Assignment.t columns RegionId.t)
      : list Z :=
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_1 Advice.A2 HR 51.

  (** The message word consumed at a hash-region row. *)
  Definition w51 (Γ : Assignment.t columns RegionId.t) (row : Z) : Z :=
    SinsemillaHash.word_at Γ Fixed.QSinsemilla2_1 Advice.A2 HR row.

  Lemma q_commit_ivk_m_x_reduced :
    UnOp.from CIvk.q_commit_ivk_m_x = CIvk.q_commit_ivk_m_x.
  Proof. vm_compute. reflexivity. Qed.

  Lemma q_commit_ivk_m_y_reduced :
    UnOp.from CIvk.q_commit_ivk_m_y = CIvk.q_commit_ivk_m_y.
  Proof. vm_compute. reflexivity. Qed.

  (** ** Fact extraction: down to [CIvk.synthesize]

      The peel along [synthesize → synthesize_address_integrity →
      commit_ivk.synthesize], with the [ak]/[nk] cells concrete. *)

  Lemma commit_ivk_synth_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ (layouter_facts (CIvk.synthesize ak_cell nk_cell)).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 7 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_address_integrity in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  (** ** The hash-to-point region: facts with concrete piece cells *)

  Lemma commit_ivk_hash_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ (region_facts HR
      (SChip.synthesize_hash_to_point_commit_ivk_region
        HR
        Selector.QSinsemilla1_1 Selector.QSinsemilla4_1
        Fixed.QSinsemilla2_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
        CIvk.q_commit_ivk_m_x CIvk.q_commit_ivk_m_y
        piece_a piece_b piece_c piece_d)).
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 7 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    apply interpret_layouter_facts_in_namespace in H.
    unfold SChip.synthesize_hash_to_point_commit_ivk in H.
    apply interpret_layouter_facts_add_region in H.
    exact H.
  Qed.

  (** The four piece copies: the running-sum cell at each piece offset is
      the witnessed piece cell. *)

  Tactic Notation "peel_hash_piece" hyp(H) integer(k) :=
    do k (apply interpret_region_facts_bind_right in H);
    apply interpret_region_facts_bind_left in H;
    do 2 (apply interpret_region_facts_bind_right in H);
    apply interpret_region_facts_bind_left in H;
    cbn [region_facts interpret_facts interpret_fact List.app] in H;
    destruct H as [H _].

  Lemma commit_ivk_hash_piece_copies
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (W.adv HR Advice.A2 0) = eval_cell Γ piece_a /\
    eval_cell Γ (W.adv HR Advice.A2 25) = eval_cell Γ piece_b /\
    eval_cell Γ (W.adv HR Advice.A2 26) = eval_cell Γ piece_c /\
    eval_cell Γ (W.adv HR Advice.A2 50) = eval_cell Γ piece_d.
  Proof.
    pose proof (commit_ivk_hash_facts Γ Hcircuit) as Hbase.
    unfold SChip.synthesize_hash_to_point_commit_ivk_region in Hbase.
    repeat split.
    - pose proof Hbase as H. peel_hash_piece H 3. exact H.
    - pose proof Hbase as H. peel_hash_piece H 4. exact H.
    - pose proof Hbase as H. peel_hash_piece H 5. exact H.
    - pose proof Hbase as H. peel_hash_piece H 6. exact H.
  Qed.

  (** The whole-region row schedule: [q_sinsemilla1] on all 51 rows,
      [q_s2 = 1] on the running rows, the three inter-piece zeros and the
      final [2]. *)
  Lemma commit_ivk_hash_schedule
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    (forall j : nat, (j < 51)%nat ->
      Γ.(Assignment.selector) Selector.QSinsemilla1_1 HR (Z.of_nat j) = 1) /\
    (forall j : nat, (j < 51)%nat ->
      j <> 24%nat -> j <> 25%nat -> j <> 49%nat -> j <> 50%nat ->
      Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR (Z.of_nat j) = 1) /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 24 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 25 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 49 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 50 = 2.
  Proof.
    pose proof (commit_ivk_hash_facts Γ Hcircuit) as Hbase.
    unfold SChip.synthesize_hash_to_point_commit_ivk_region in Hbase.
    pose proof Hbase as HpA.
    do 3 apply interpret_region_facts_bind_right in HpA.
    apply interpret_region_facts_bind_left in HpA.
    apply NoteCommitNewHash.hash_piece_schedule in HpA.
    destruct HpA as (HselA & HstepA & HlastA).
    pose proof Hbase as HpB.
    do 4 apply interpret_region_facts_bind_right in HpB.
    apply interpret_region_facts_bind_left in HpB.
    apply NoteCommitNewHash.hash_piece_schedule in HpB.
    destruct HpB as (HselB & HstepB & HlastB).
    pose proof Hbase as HpC.
    do 5 apply interpret_region_facts_bind_right in HpC.
    apply interpret_region_facts_bind_left in HpC.
    apply NoteCommitNewHash.hash_piece_schedule in HpC.
    destruct HpC as (HselC & HstepC & HlastC).
    pose proof Hbase as HpD.
    do 6 apply interpret_region_facts_bind_right in HpD.
    apply interpret_region_facts_bind_left in HpD.
    apply NoteCommitNewHash.hash_piece_schedule in HpD.
    destruct HpD as (HselD & HstepD & HlastD).
    clear Hbase.
    pose proof (HlastA ltac:(lia)) as Hq2_24.
    pose proof (HlastB ltac:(lia)) as Hq2_25.
    pose proof (HlastC ltac:(lia)) as Hq2_49.
    pose proof (HlastD ltac:(lia)) as Hq2_50.
    replace (0 + Z.of_nat (25 - 1)) with 24 in Hq2_24 by lia.
    replace (25 + Z.of_nat (1 - 1)) with 25 in Hq2_25 by lia.
    replace (26 + Z.of_nat (24 - 1)) with 49 in Hq2_49 by lia.
    replace (50 + Z.of_nat (1 - 1)) with 50 in Hq2_50 by lia.
    split.
    { intros j Hj.
      destruct (Nat.lt_ge_cases j 25) as [Hc1 | Hc1].
      { replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        apply HselA; lia. }
      destruct (Nat.lt_ge_cases j 26) as [Hc2 | Hc2].
      { replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
        apply HselB; lia. }
      destruct (Nat.lt_ge_cases j 50) as [Hc3 | Hc3].
      { replace (Z.of_nat j) with (26 + Z.of_nat (j - 26)) by lia.
        apply HselC; lia. }
      replace (Z.of_nat j) with (50 + Z.of_nat (j - 50)) by lia.
      apply HselD; lia. }
    split.
    { intros j Hj H24 H25 H49 H50.
      destruct (Nat.lt_ge_cases j 25) as [Hc1 | Hc1].
      { replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        apply HstepA; lia. }
      replace (Z.of_nat j) with (26 + Z.of_nat (j - 26)) by lia.
      apply HstepC; lia. }
    repeat split; assumption.
  Qed.

  (** Ten-bit word bound at any hash-region row (the variant-1 generator
      table lookup). *)
  Lemma hash_word_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 51)%nat) :
    0 <= w51 Γ (Z.of_nat j) < 2 ^ 10.
  Proof.
    destruct (commit_ivk_hash_schedule Γ Hcircuit) as (Hsel & _).
    exact (word_at_bound Γ HR (Z.of_nat j)
      Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
      Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (generator_table_facts Γ Hcircuit)
      (SinsemillaHash.enabled_eq_one Γ Selector.QSinsemilla1_1 HR
        (Z.of_nat j) (Hsel j Hj))
      (generator_table_lookup_holds_1 Γ Hcircuit HR (Z.of_nat j))).
  Qed.

  (** ** The 51-word variant-1 hash fold (part ii)

      The point read off the output cells ([A0]/[A3] at row 51) of the
      CommitIvk hash-to-point region is [sinsemilla_hash_to_point] of the
      CommitIvk domain point over the region's 51 grid words — conditional
      on incomplete-add nondegeneracy of that word list (the
      [merkle_layer_ok] precedent). *)
  Theorem commit_ivk_hash_point_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate commit_ivk_Q (commit_ivk_words Γ)) :
    {|
      Point.x := UnOp.from (eval_cell Γ (W.adv HR Advice.A0 51));
      Point.y := UnOp.from (eval_cell Γ (W.adv HR Advice.A3 51));
    |} =
      SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.commit_ivk_q orchard_circuit_params)
        (commit_ivk_words Γ).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    pose proof (commit_ivk_hash_facts Γ Hcircuit) as Hhash.
    unfold SChip.synthesize_hash_to_point_commit_ivk_region in Hhash.
    (* Seed facts: [q_sinsemilla4] selector, fixed [y_q], constant [x_q]. *)
    pose proof Hhash as HselY.
    apply interpret_region_facts_bind_left in HselY.
    cbn [region_facts interpret_facts interpret_fact] in HselY.
    destruct HselY as [HselY _].
    pose proof Hhash as HfixY.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in HfixY.
    cbn [region_facts interpret_facts interpret_fact] in HfixY.
    destruct HfixY as [HfixY _].
    pose proof Hhash as HconstX.
    do 2 apply interpret_region_facts_bind_right in HconstX.
    apply interpret_region_facts_bind_left in HconstX.
    cbn [region_facts interpret_facts interpret_fact] in HconstX.
    destruct HconstX as [HconstX _].
    clear Hhash.
    (* Row schedules across the four pieces. *)
    destruct (commit_ivk_hash_schedule Γ Hcircuit)
      as (Hsel1 & Hq2_one & Hq2_24 & Hq2_25 & Hq2_49 & Hq2_50).
    assert (Hsel : forall j : nat, (j < 51)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_1 ⟧
          (HR, Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      apply Hsel1. exact Hj. }
    (* [q_s3 = 0] below the final row, [q_s3 = 2] on row 50. *)
    assert (Hq3 : forall j : nat, (S j < 51)%nat ->
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_1 ⟧ (HR, Z.of_nat j) = 0).
    { intros j Hj.
      destruct (Nat.eq_dec j 24) as [-> | H24].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 HR (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity]. }
      destruct (Nat.eq_dec j 25) as [-> | H25].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 HR (Z.of_nat 25) 0);
          [exact Hq2_25 | left; reflexivity]. }
      destruct (Nat.eq_dec j 49) as [-> | H49].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 HR (Z.of_nat 49) 0);
          [exact Hq2_49 | left; reflexivity]. }
      apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 HR (Z.of_nat j) 1);
        [apply Hq2_one; lia | right; reflexivity]. }
    assert (Hq3_final :
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_1 ⟧
          (HR, Z.of_nat (51 - 1)) = 2).
    { apply q_s3_eval_two. exact Hq2_50. }
    (* The two gates of the region, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ SChip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (HR, row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        HR
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ SChip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (HR, 0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        HR
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ HR 0
        Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A3 Advice.A4
        (enabled_nonzero Γ Selector.QSinsemilla4_1 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs0 _ 0
      CIvk.q_commit_ivk_m_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A0 Advice.A1 Advice.A3
      Advice.A4 _ 0 (UnOp.from CIvk.q_commit_ivk_m_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A0 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite q_commit_ivk_m_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite q_commit_ivk_m_y_reduced in Hacc0.
    (* The 51-round point fold at the CommitIvk schedule. *)
    pose proof (SinsemillaHashFold.hash_to_point_rows_correct Γ
        HR
        Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
        Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
        51%nat ltac:(lia) commit_ivk_Q
        Hload Hsel (fun j _ => Hgate_sin (Z.of_nat j))
        (fun j _ =>
          generator_table_lookup_holds_1 Γ Hcircuit HR (Z.of_nat j))
        Hq3 Hq3_final Hacc0 Hnondeg) as Hpoint.
    change (Z.of_nat 51) with 51 in Hpoint.
    rewrite (eval_advice_cur_cell Γ HR Advice.A0 51) in Hpoint.
    rewrite (eval_advice_cur_cell Γ HR Advice.A3 51) in Hpoint.
    exact Hpoint.
  Qed.

  (** ** Word runs of the CommitIvk hash region *)

  Definition Lr (Γ : Assignment.t columns RegionId.t) (off n : nat)
      : list Z :=
    List.map (fun j : nat => w51 Γ (Z.of_nat off + Z.of_nat j))
      (List.seq 0%nat n).

  Lemma Lr_length
      (Γ : Assignment.t columns RegionId.t) (off n : nat) :
    List.length (Lr Γ off n) = n.
  Proof. unfold Lr. now rewrite List.length_map, List.length_seq. Qed.

  Lemma Lr_forall
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 51)%nat) :
    List.Forall (fun x : Z => 0 <= x < 2 ^ 10) (Lr Γ off n).
  Proof.
    unfold Lr.
    rewrite List.Forall_map, List.Forall_forall.
    intros j Hj. rewrite List.in_seq in Hj.
    replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat) by lia.
    apply hash_word_bound; [exact Hcircuit | lia].
  Qed.

  Lemma Lr_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 51)%nat) :
    0 <= SinsemillaHash.digit_sum (Lr Γ off n) < 2 ^ (10 * Z.of_nat n).
  Proof.
    pose proof (SinsemillaHash.digit_sum_bound (Lr Γ off n)) as Hb.
    rewrite Lr_length in Hb.
    apply Hb.
    exact (Lr_forall Γ Hcircuit off n Hrange).
  Qed.

  (** Splitting a word run at an interior offset. *)
  Lemma Lr_split
      (Γ : Assignment.t columns RegionId.t) (off m k : nat) :
    Lr Γ off (m + k)%nat = Lr Γ off m ++ Lr Γ (off + m)%nat k.
  Proof.
    unfold Lr.
    rewrite (map_z_seq_split (w51 Γ) (Z.of_nat off) m k).
    f_equal.
    apply List.map_ext. intros j. f_equal. lia.
  Qed.

  Lemma Lr_single
      (Γ : Assignment.t columns RegionId.t) (off : nat) :
    SinsemillaHash.digit_sum (Lr Γ off 1) = w51 Γ (Z.of_nat off).
  Proof.
    unfold Lr.
    cbn [List.seq List.map SinsemillaHash.digit_sum].
    replace (Z.of_nat off + Z.of_nat 0) with (Z.of_nat off) by lia.
    lia.
  Qed.

  (** The generic piece telescope at a hash-region offset. *)
  Lemma commit_ivk_piece_telescope
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (v : Z)
      (Hn : (0 < n)%nat) (Hrange : (off + n <= 51)%nat)
      (Hlen : 10 * Z.of_nat n <= 250)
      (Hsteps : forall j : nat, (S j < n)%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat j) = 1)
      (Hv : v = 0 \/ v = 2)
      (Hlast :
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat (n - 1)%nat) = v) :
    Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat off) =
      SinsemillaHash.digit_sum (Lr Γ off n).
  Proof.
    unfold Lr, w51.
    apply SinsemillaHash.piece_telescope.
    - exact Hn.
    - intros j Hj.
      apply word_at_step.
      apply Hsteps. exact Hj.
    - apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR
        (Z.of_nat off + Z.of_nat (n - 1)%nat) v Hlast Hv).
    - intros j Hj.
      replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat)
        by lia.
      apply hash_word_bound; [exact Hcircuit | lia].
    - exact Hlen.
  Qed.

  (** ** Canonical value names

      Every quantity of the decomposition, as the reduced value of its home
      cell: the four hashed pieces on their witness cells, the range-checked
      chunks on their [A9] range cells, the two free bits on the gate
      region's [A4] cells, [ak]/[nk] on the witness-input cells, the [z13]
      running sums on the hash region, and the two prime-check running sums
      on the lookup regions. *)

  Definition av (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ piece_a.
  Definition bv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ piece_b.
  Definition cv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ piece_c.
  Definition dv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ piece_d.

  Definition b0v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv (cir RegionId.CommitIvk.RangeB0) Advice.A9 0).
  Definition b2v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv (cir RegionId.CommitIvk.RangeB2) Advice.A9 0).
  Definition d0v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv (cir RegionId.CommitIvk.RangeD0) Advice.A9 0).

  Definition b1v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv CG Advice.A4 0).
  Definition d1v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv CG Advice.A4 1).

  Definition akv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ ak_cell.
  Definition nkv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ nk_cell.

  Definition z13av (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv HR Advice.A2 13).
  Definition z13cv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv HR Advice.A2 39).

  Definition aprimev (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv AKL Advice.A9 0).
  Definition z13apv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv AKL Advice.A9 13).
  Definition bcpv (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv NKL Advice.A9 0).
  Definition z14v (Γ : Assignment.t columns RegionId.t) : Z :=
    W.val Γ (W.adv NKL Advice.A9 14).

  (** ** The telescopes: piece values as digit sums of their word runs *)

  Lemma telescopes
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    av Γ = SinsemillaHash.digit_sum (Lr Γ 0 25) /\
    bv Γ = w51 Γ 25 /\
    cv Γ = SinsemillaHash.digit_sum (Lr Γ 26 24) /\
    dv Γ = w51 Γ 50 /\
    z13av Γ = SinsemillaHash.digit_sum (Lr Γ 13 12) /\
    z13cv Γ = SinsemillaHash.digit_sum (Lr Γ 39 11).
  Proof.
    destruct (commit_ivk_hash_schedule Γ Hcircuit)
      as (Hsel & Hq2one & Hq24 & Hq25 & Hq49 & Hq50).
    destruct (commit_ivk_hash_piece_copies Γ Hcircuit)
      as (HcA & HcB & HcC & HcD).
    (* Piece a: rows 0..24, boundary 24. *)
    assert (Ta :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 0) =
        SinsemillaHash.digit_sum (Lr Γ 0 25)).
    { apply (commit_ivk_piece_telescope Γ Hcircuit 0 25 0); try lia.
      - intros j Hj.
        replace (Z.of_nat 0 + Z.of_nat j) with (Z.of_nat j) by lia.
        apply Hq2one; lia.
      - replace (Z.of_nat 0 + Z.of_nat (25 - 1)%nat) with 24 by lia.
        exact Hq24. }
    (* Sub-run of a: rows 13..24. *)
    assert (T13 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 13) =
        SinsemillaHash.digit_sum (Lr Γ 13 12)).
    { apply (commit_ivk_piece_telescope Γ Hcircuit 13 12 0); try lia.
      - intros j Hj.
        replace (Z.of_nat 13 + Z.of_nat j) with (Z.of_nat (13 + j)%nat) by lia.
        apply Hq2one; lia.
      - replace (Z.of_nat 13 + Z.of_nat (12 - 1)%nat) with 24 by lia.
        exact Hq24. }
    (* Piece c: rows 26..49, boundary 49. *)
    assert (Tc :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 26) =
        SinsemillaHash.digit_sum (Lr Γ 26 24)).
    { apply (commit_ivk_piece_telescope Γ Hcircuit 26 24 0); try lia.
      - intros j Hj.
        replace (Z.of_nat 26 + Z.of_nat j) with (Z.of_nat (26 + j)%nat) by lia.
        apply Hq2one; lia.
      - replace (Z.of_nat 26 + Z.of_nat (24 - 1)%nat) with 49 by lia.
        exact Hq49. }
    (* Sub-run of c: rows 39..49. *)
    assert (T39 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 39) =
        SinsemillaHash.digit_sum (Lr Γ 39 11)).
    { apply (commit_ivk_piece_telescope Γ Hcircuit 39 11 0); try lia.
      - intros j Hj.
        replace (Z.of_nat 39 + Z.of_nat j) with (Z.of_nat (39 + j)%nat) by lia.
        apply Hq2one; lia.
      - replace (Z.of_nat 39 + Z.of_nat (11 - 1)%nat) with 49 by lia.
        exact Hq49. }
    (* Single-word pieces b and d. *)
    assert (Tb :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, 25) =
          w51 Γ 25).
    { apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR 25 0 Hq25).
      left. reflexivity. }
    assert (Td :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, 50) =
          w51 Γ 50).
    { apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR 50 2 Hq50).
      right. reflexivity. }
    unfold av, bv, cv, dv, z13av, z13cv, W.val.
    rewrite <- HcA, <- HcB, <- HcC, <- HcD.
    unfold W.adv.
    repeat rewrite <- eval_advice_cur_cell.
    repeat split.
    - exact Ta.
    - exact Tb.
    - exact Tc.
    - exact Td.
    - exact T13.
    - exact T39.
  Qed.

  (** ** Canonicity-gate region: selector and the fifteen copies *)

  Lemma canonicity_gate_copies
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QCommitIvk CG 0 = 1 /\
    eval_cell Γ (W.adv CG Advice.A0 0) = eval_cell Γ ak_cell /\
    eval_cell Γ (W.adv CG Advice.A1 0) = eval_cell Γ piece_a /\
    eval_cell Γ (W.adv CG Advice.A2 0) = eval_cell Γ piece_b /\
    eval_cell Γ (W.adv CG Advice.A3 0) =
      eval_cell Γ (W.adv (cir RegionId.CommitIvk.RangeB0) Advice.A9 0) /\
    eval_cell Γ (W.adv CG Advice.A5 0) =
      eval_cell Γ (W.adv (cir RegionId.CommitIvk.RangeB2) Advice.A9 0) /\
    eval_cell Γ (W.adv CG Advice.A6 0) =
      eval_cell Γ (W.adv HR Advice.A2 13) /\
    eval_cell Γ (W.adv CG Advice.A7 0) =
      eval_cell Γ (W.adv AKL Advice.A9 0) /\
    eval_cell Γ (W.adv CG Advice.A8 0) =
      eval_cell Γ (W.adv AKL Advice.A9 13) /\
    eval_cell Γ (W.adv CG Advice.A0 1) = eval_cell Γ nk_cell /\
    eval_cell Γ (W.adv CG Advice.A1 1) = eval_cell Γ piece_c /\
    eval_cell Γ (W.adv CG Advice.A2 1) = eval_cell Γ piece_d /\
    eval_cell Γ (W.adv CG Advice.A3 1) =
      eval_cell Γ (W.adv (cir RegionId.CommitIvk.RangeD0) Advice.A9 0) /\
    eval_cell Γ (W.adv CG Advice.A6 1) =
      eval_cell Γ (W.adv HR Advice.A2 39) /\
    eval_cell Γ (W.adv CG Advice.A7 1) =
      eval_cell Γ (W.adv NKL Advice.A9 0) /\
    eval_cell Γ (W.adv CG Advice.A8 1) =
      eval_cell Γ (W.adv NKL Advice.A9 14).
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 10 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    unfold CIvk.assign_cells_used_in_canonicity_gate in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    cbn [region_facts region_value layouter_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      List.app interpret_facts interpret_fact fst snd
      CIvk.witness_message_piece CIvk.synthesize_range_check
      CIvk.synthesize_running_lookup
      CIvk.synthesize_full_fixed_base_mul_commit_ivk_r
      SChip.synthesize_hash_to_point_commit_ivk
      CIvk.LookupResult.z_0 CIvk.LookupResult.z_end
      SChip.CommitIvkHashResult.z13_a SChip.CommitIvkHashResult.z13_c] in H.
    cbn [region_value SChip.synthesize_hash_to_point_commit_ivk_region
      SChip.synthesize_hash_piece Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      SChip.CommitIvkHashResult.z13_a SChip.CommitIvkHashResult.z13_c] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11
      & H12 & H13 & H14 & H15 & H16 & _).
    repeat split; assumption.
  Qed.

  (** ** The two canonicity running lookups: per-row selector schedules *)

  Lemma ak_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup AKL (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning AKL (Z.of_nat j) = 1.
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 8 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    unfold CIvk.synthesize_running_lookup in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (W.running_selectors_of_facts Γ _ 13 H j Hj).
  Qed.

  Lemma nk_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 14)%nat) :
    Γ.(Assignment.selector) Selector.QLookup NKL (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning NKL (Z.of_nat j) = 1.
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 9 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    unfold CIvk.synthesize_running_lookup in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (W.running_selectors_of_facts Γ _ 14 H j Hj).
  Qed.

  (** ** Gate-level soundness of the [QCommitIvk] canonicity gate

      The fourteen constraints of [commit_ivk_canonicity_check_gate] at an
      active row, in expression-evaluation form (the [pieces.v]
      [message_piece_*_sound] style). *)

  Lemma canonicity_gate_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QCommitIvk ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ CIvk.commit_ivk_canonicity_check_gate ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) /\
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (region, row)) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, row)) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) *F
        UnOp.from (2 ^ 4) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)) *F
        UnOp.from (2 ^ 5) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ (region, row)) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, row)) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 9) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row)) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, row)) *F
        UnOp.from (2 ^ 250) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) *F
        UnOp.from (2 ^ 254) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row)) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 5) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 245) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 254) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.next ⟧ (region, row)) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, row)) = 0) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row)) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row)) +F
      UnOp.from (2 ^ 130) -F
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p =
      (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) = 0) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, row)) = 0) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row)) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)) +F
      (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 5) +F
      UnOp.from (2 ^ 140) -F
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p =
      (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row)) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) = 0 \/
     (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row)) = 0).
  Proof.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10
      & H11 & H12 & H13 & H14).
    specialize (H1 Hselector). specialize (H2 Hselector).
    specialize (H3 Hselector). specialize (H4 Hselector).
    specialize (H5 Hselector). specialize (H6 Hselector).
    specialize (H7 Hselector). specialize (H8 Hselector).
    specialize (H9 Hselector). specialize (H10 Hselector).
    specialize (H11 Hselector). specialize (H12 Hselector).
    specialize (H13 Hselector). specialize (H14 Hselector).
    repeat split; assumption.
  Qed.

  (** ** Pure-[Z] exactness of the CommitIvk decompositions *)

  (** Piece [b = b_0 + b_1·2^4 + b_2·2^5] (one word). *)
  Lemma commit_ivk_piece_b_exact (b b0 b1 b2 : Z)
      (Hb :
        b = b0 +F b1 *F UnOp.from (2 ^ 4) +F b2 *F UnOp.from (2 ^ 5))
      (Hb0 : 0 <= b0 < 2 ^ 4)
      (Hb1 : b1 = 0 \/ b1 = 1)
      (Hb2 : 0 <= b2 < 2 ^ 5) :
    b = b0 + b1 * 2 ^ 4 + b2 * 2 ^ 5 /\ 0 <= b < 2 ^ 10.
  Proof.
    pose proof MP.t_p_range as Htp.
    pose proof MP.pallas_p_eq as Hpeq.
    subst b.
    rewrite (MP.addF_mulF_exact b0 b1 (2 ^ 4))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (MP.addF_mulF_exact (b0 + b1 * 2 ^ 4) b2 (2 ^ 5))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  (** Piece [d = d_0 + d_1·2^9] (one word). *)
  Lemma commit_ivk_piece_d_exact (d d0 d1 : Z)
      (Hd : d = d0 +F d1 *F UnOp.from (2 ^ 9))
      (Hd0 : 0 <= d0 < 2 ^ 9)
      (Hd1 : d1 = 0 \/ d1 = 1) :
    d = d0 + d1 * 2 ^ 9 /\ 0 <= d < 2 ^ 10.
  Proof.
    pose proof MP.t_p_range as Htp.
    pose proof MP.pallas_p_eq as Hpeq.
    subst d.
    rewrite (MP.addF_mulF_exact d0 d1 (2 ^ 9))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  (** [nk]-shaped decomposition ([b_2] 5 bits, [c] 240 bits at shift 5,
      [d_0] 9 bits at shift 245, top bit at 254; prime check on the 140-bit
      low part) — the CommitIvk sibling of
      [MP.decomposition_9_240_5_1]. *)
  Lemma decomposition_5_240_9_1
      (xv lo mid hi top prime : Z)
      (Hxv :
        xv =
          lo +F mid *F UnOp.from (2 ^ 5) +F hi *F UnOp.from (2 ^ 245) +F
            top *F UnOp.from (2 ^ 254))
      (Hprime :
        prime =
          lo +F mid *F UnOp.from (2 ^ 5) +F UnOp.from (2 ^ 140) -F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
      (Hlo : 0 <= lo < 2 ^ 5)
      (Hmid : 0 <= mid < 2 ^ 240)
      (Hhi : 0 <= hi < 2 ^ 9)
      (Htop : top = 0 \/ top = 1)
      (Htop_hi : top = 0 \/ hi = 0)
      (Hmid130 : top = 1 -> mid < 2 ^ 130)
      (Hprime_range : top = 1 -> 0 <= prime < 2 ^ 140) :
    xv = lo + mid * 2 ^ 5 + hi * 2 ^ 245 + top * 2 ^ 254 /\
    0 <= lo + mid * 2 ^ 5 + hi * 2 ^ 245 + top * 2 ^ 254 < Primes.pallas_p.
  Proof.
    pose proof MP.t_p_range as Htp.
    pose proof MP.pallas_p_eq as Hpeq.
    assert (Hinner : lo +F mid *F UnOp.from (2 ^ 5) = lo + mid * 2 ^ 5)
      by (apply MP.addF_mulF_exact;
        cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite Hinner in Hxv, Hprime.
    destruct Htop as [Htopz | Htopone].
    - subst top xv.
      rewrite (MP.addF_mulF_exact (lo + mid * 2 ^ 5) hi (2 ^ 245))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (MP.addF_mulF_exact (lo + mid * 2 ^ 5 + hi * 2 ^ 245) 0
        (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
    - assert (Hhiz : hi = 0) by lia.
      specialize (Hmid130 Htopone).
      specialize (Hprime_range Htopone).
      destruct (MP.prime_check_exact 140 (lo + mid * 2 ^ 5) prime
        ltac:(lia) ltac:(lia) Hprime Hprime_range) as [Hlowtp _].
      subst hi top xv.
      rewrite (MP.addF_mulF_exact (lo + mid * 2 ^ 5) 0 (2 ^ 245))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (MP.addF_mulF_exact (lo + mid * 2 ^ 5 + 0 * 2 ^ 245) 1
        (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
  Qed.

  (** ** The side condition: the three short-lookup range cells

      Exactly the [note_commit_new_short_lookup_ok] situation
      ([circuit_proof/note_commit/words.v]): the halo2 short lookup
      constrains its cell only where [q_running = 0], and the relational
      model pins selectors solely through the synthesis [SelectorOn] facts,
      leaving [QRunning] free at the short-range rows — so the three bounds
      are underivable from [Holds] and are named as the side condition. *)
  Definition commit_ivk_short_lookup_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    W.short_ok Γ (cir RegionId.CommitIvk.RangeB0) 4 /\
    W.short_ok Γ (cir RegionId.CommitIvk.RangeB2) 5 /\
    W.short_ok Γ (cir RegionId.CommitIvk.RangeD0) 9.

  (** ** The word-list split *)

  Lemma commit_ivk_words_split
      (Γ : Assignment.t columns RegionId.t) :
    commit_ivk_words Γ =
      Lr Γ 0 25 ++ Lr Γ 25 1 ++ Lr Γ 26 24 ++ Lr Γ 50 1.
  Proof. reflexivity. Qed.

  (** ** The hashed words are the [Commit^ivk] message (part i)

      The 51 grid words of the CommitIvk hash-to-point region equal
      [OrchardSpec.commit_ivk_message] at the circuit's reads: the witnessed
      [ak_P] x-coordinate and the witnessed [nk] — under [Holds] and the
      short-lookup side condition. *)
  Theorem commit_ivk_words_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : commit_ivk_short_lookup_ok Γ) :
    commit_ivk_words Γ =
      OrchardSpec.commit_ivk_message
        (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
        (OrchardSpec.in_nk (read_action_inputs Γ)).
  Proof.
    destruct Hshort as (Hb0 & Hb2 & Hd0).
    unfold W.short_ok in Hb0, Hb2, Hd0.
    change (W.val Γ (W.adv (cir RegionId.CommitIvk.RangeB0) Advice.A9 0))
      with (b0v Γ) in Hb0.
    change (W.val Γ (W.adv (cir RegionId.CommitIvk.RangeB2) Advice.A9 0))
      with (b2v Γ) in Hb2.
    change (W.val Γ (W.adv (cir RegionId.CommitIvk.RangeD0) Advice.A9 0))
      with (d0v Γ) in Hd0.
    destruct (telescopes Γ Hcircuit) as (Hta & Htb & Htc & Htd & Ht13 & Ht39).
    destruct (canonicity_gate_copies Γ Hcircuit)
      as (Hqsel & Hcak & Hca & Hcb & Hcb0 & Hcb2 & Hcz13a & Hcap & Hczap
        & Hcnk & Hcc & Hcd & Hcd0 & Hcz13c & Hcbcp & Hczbcp).
    (* The gate at the active row. *)
    pose proof
      (canonicity_gate_sound Γ CG 0
        (enabled_nonzero Γ Selector.QCommitIvk CG 0 Hqsel)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          CIvk.commit_ivk_canonicity_check_gate
          CG 0
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          (holds_gates Γ Hcircuit))) as Hgate.
    destruct Hgate as (Hb1b & Hd1b & Hbdec & Hddec & Hakdec & Hnkdec
      & Hb0can & Hz13ac & Hapc & Hzapc & Hd0can & Hz13cc & Hbcpc & Hzbcpc).
    (* Route every gate cell to its home value. *)
    assert (EA0c : Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
        (CG, 0) = akv Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcak)).
    assert (EA1c : Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
        (CG, 0) = av Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hca)).
    assert (EA2c : Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧
        (CG, 0) = bv Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcb)).
    assert (EA3c : Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧
        (CG, 0) = b0v Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcb0)).
    assert (EA4c : Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (CG, 0) = b1v Γ)
      by (exact (W.cur_val Γ _ Advice.A4 0)).
    assert (EA5c : Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧
        (CG, 0) = b2v Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcb2)).
    assert (EA6c : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (CG, 0) = z13av Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcz13a)).
    assert (EA7c : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (CG, 0) = aprimev Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hcap)).
    assert (EA8c : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (CG, 0) = z13apv Γ)
      by (exact (W.cur_eq Γ _ _ _ _ Hczap)).
    assert (EA0n : Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.next ⟧
        (CG, 0) = nkv Γ)
      by (exact (W.next_eq Γ _ Advice.A0 0 1 eq_refl _ Hcnk)).
    assert (EA1n : Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.next ⟧
        (CG, 0) = cv Γ)
      by (exact (W.next_eq Γ _ Advice.A1 0 1 eq_refl _ Hcc)).
    assert (EA2n : Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧
        (CG, 0) = dv Γ)
      by (exact (W.next_eq Γ _ Advice.A2 0 1 eq_refl _ Hcd)).
    assert (EA3n : Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧
        (CG, 0) = d0v Γ)
      by (exact (W.next_eq Γ _ Advice.A3 0 1 eq_refl _ Hcd0)).
    assert (EA4n : Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
        (CG, 0) = d1v Γ)
      by (exact (W.next_eq Γ _ Advice.A4 0 1 eq_refl _ eq_refl)).
    assert (EA6n : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
        (CG, 0) = z13cv Γ)
      by (exact (W.next_eq Γ _ Advice.A6 0 1 eq_refl _ Hcz13c)).
    assert (EA7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (CG, 0) = bcpv Γ)
      by (exact (W.next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcbcp)).
    assert (EA8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (CG, 0) = z14v Γ)
      by (exact (W.next_eq Γ _ Advice.A8 0 1 eq_refl _ Hczbcp)).
    rewrite EA4c in Hb1b, Hbdec, Hakdec, Hb0can, Hz13ac, Hzapc.
    rewrite EA4n in Hd1b, Hddec, Hnkdec, Hd0can, Hz13cc, Hzbcpc.
    rewrite EA2c in Hbdec.
    rewrite EA3c in Hbdec, Hakdec, Hb0can.
    rewrite EA5c in Hbdec, Hnkdec, Hbcpc.
    rewrite EA2n in Hddec.
    rewrite EA3n in Hddec, Hnkdec, Hd0can.
    rewrite EA1c in Hakdec, Hapc.
    rewrite EA0c in Hakdec.
    rewrite EA1n in Hnkdec, Hbcpc.
    rewrite EA0n in Hnkdec.
    rewrite EA6c in Hz13ac.
    rewrite EA7c in Hapc.
    rewrite EA8c in Hzapc.
    rewrite EA6n in Hz13cc.
    rewrite EA7n in Hbcpc.
    rewrite EA8n in Hzbcpc.
    (* Boolean bits. *)
    pose proof (MP.isbool_cases _ Hb1b) as Hb1c.
    pose proof (MP.isbool_cases _ Hd1b) as Hd1c.
    (* Word-run bounds. *)
    assert (Hav : 0 <= av Γ < 2 ^ 250).
    { rewrite Hta.
      pose proof (Lr_bound Γ Hcircuit 0 25 ltac:(lia)) as HB.
      change (10 * Z.of_nat 25) with 250 in HB.
      exact HB. }
    assert (Hcv : 0 <= cv Γ < 2 ^ 240).
    { rewrite Htc.
      pose proof (Lr_bound Γ Hcircuit 26 24 ltac:(lia)) as HB.
      change (10 * Z.of_nat 24) with 240 in HB.
      exact HB. }
    (* [b_1 = 1 -> a < 2^130] via the [z13_a] leg and the a-run split. *)
    assert (Ha130 : b1v Γ = 1 -> av Γ < 2 ^ 130).
    { intros H1.
      destruct Hz13ac as [Hz | Hz]; [lia |].
      assert (Hsplit : av Γ =
          SinsemillaHash.digit_sum (Lr Γ 0 13) +
          2 ^ 130 * SinsemillaHash.digit_sum (Lr Γ 13 12)).
      { assert (Happ : Lr Γ 0 25 = Lr Γ 0 13 ++ Lr Γ 13 12)
          by (exact (Lr_split Γ 0 13 12)).
        rewrite Hta, Happ.
        rewrite SinsemillaHash.digit_sum_app.
        rewrite Lr_length.
        change (10 * Z.of_nat 13) with 130.
        reflexivity. }
      rewrite <- Ht13 in Hsplit.
      rewrite Hz in Hsplit.
      pose proof (Lr_bound Γ Hcircuit 0 13 ltac:(lia)) as HB.
      change (10 * Z.of_nat 13) with 130 in HB.
      lia. }
    (* [b_1 = 1 -> a_prime < 2^130] via the AkLookup running chain. *)
    assert (Hap130 : b1v Γ = 1 -> 0 <= aprimev Γ < 2 ^ 130).
    { intros H1.
      destruct Hzapc as [Hz | Hz]; [lia |].
      assert (Hend : W.zv Γ AKL 13 = 0)
        by (exact (W.zv_zero_of_val Γ AKL 13 13 eq_refl Hz)).
      pose proof (W.lookup_z_bound Γ Hcircuit AKL 13 ltac:(lia)
        (ak_lookup_selectors Γ Hcircuit) 13 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      unfold aprimev.
      rewrite (W.zv_val Γ AKL 0 0 eq_refl).
      exact HB. }
    (* [d_1 = 1 -> c < 2^130] via the [z13_c] leg and the c-run split. *)
    assert (Hc130 : d1v Γ = 1 -> cv Γ < 2 ^ 130).
    { intros H1.
      destruct Hz13cc as [Hz | Hz]; [lia |].
      assert (Hsplit : cv Γ =
          SinsemillaHash.digit_sum (Lr Γ 26 13) +
          2 ^ 130 * SinsemillaHash.digit_sum (Lr Γ 39 11)).
      { assert (Happ : Lr Γ 26 24 = Lr Γ 26 13 ++ Lr Γ 39 11)
          by (exact (Lr_split Γ 26 13 11)).
        rewrite Htc, Happ.
        rewrite SinsemillaHash.digit_sum_app.
        rewrite Lr_length.
        change (10 * Z.of_nat 13) with 130.
        reflexivity. }
      rewrite <- Ht39 in Hsplit.
      rewrite Hz in Hsplit.
      pose proof (Lr_bound Γ Hcircuit 26 13 ltac:(lia)) as HB.
      change (10 * Z.of_nat 13) with 130 in HB.
      lia. }
    (* [d_1 = 1 -> b2_c_prime < 2^140] via the NkLookup running chain. *)
    assert (Hbcp140 : d1v Γ = 1 -> 0 <= bcpv Γ < 2 ^ 140).
    { intros H1.
      destruct Hzbcpc as [Hz | Hz]; [lia |].
      assert (Hend : W.zv Γ NKL 14 = 0)
        by (exact (W.zv_zero_of_val Γ NKL 14 14 eq_refl Hz)).
      pose proof (W.lookup_z_bound Γ Hcircuit NKL 14 ltac:(lia)
        (nk_lookup_selectors Γ Hcircuit) 14 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (14 - 0)) with 140 in HB.
      unfold bcpv.
      rewrite (W.zv_val Γ NKL 0 0 eq_refl).
      exact HB. }
    (* The four integer identities. *)
    destruct (commit_ivk_piece_b_exact (bv Γ) (b0v Γ) (b1v Γ) (b2v Γ)
      Hbdec Hb0 Hb1c Hb2) as [HbI HbR].
    destruct (commit_ivk_piece_d_exact (dv Γ) (d0v Γ) (d1v Γ)
      Hddec Hd0 Hd1c) as [HdI HdR].
    destruct (MP.decomposition_250_4_1 (akv Γ) (av Γ) (b0v Γ) (b1v Γ)
      (aprimev Γ) (eq_sym Hakdec) (eq_sym Hapc) Hav Hb0 Hb1c Hb0can
      Ha130 Hap130) as [HakI _].
    destruct (decomposition_5_240_9_1 (nkv Γ) (b2v Γ) (cv Γ) (d0v Γ)
      (d1v Γ) (bcpv Γ) (eq_sym Hnkdec) (eq_sym Hbcpc) Hb2 Hcv Hd0 Hd1c
      Hd0can Hc130 Hbcp140) as [HnkI _].
    (* Packing: the 51 words digit-sum to [ak + nk·2^255]. *)
    assert (Hall : List.Forall (fun x : Z => 0 <= x < 2 ^ 10)
        (commit_ivk_words Γ)).
    { unfold commit_ivk_words, SinsemillaHash.hash_words.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      apply hash_word_bound; [exact Hcircuit | lia]. }
    assert (Hpack : akv Γ + nkv Γ * 2 ^ 255 =
        SinsemillaHash.digit_sum (commit_ivk_words Γ)).
    { rewrite commit_ivk_words_split.
      rewrite !SinsemillaHash.digit_sum_app.
      rewrite !Lr_length.
      cbn [List.length].
      pose proof (Lr_single Γ 25) as HsB.
      pose proof (Lr_single Γ 50) as HsD.
      change (Z.of_nat 25) with 25 in HsB.
      change (Z.of_nat 50) with 50 in HsD.
      rewrite <- Htb in HsB.
      rewrite <- Htd in HsD.
      change (10 * Z.of_nat 25) with 250.
      change (10 * Z.of_nat 1) with 10.
      change (10 * Z.of_nat 24) with 240.
      clear -Hta Htc HsB HsD HbI HdI HakI HnkI.
      rewrite <- Hta, <- Htc, HsB, HsD.
      lia. }
    (* Assembly: [words_le] of the digit sum is the word list itself. *)
    assert (Hread_ak :
        EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)) = akv Γ)
      by reflexivity.
    assert (Hread_nk : OrchardSpec.in_nk (read_action_inputs Γ) = nkv Γ)
      by reflexivity.
    rewrite Hread_ak, Hread_nk.
    unfold OrchardSpec.commit_ivk_message.
    rewrite Hpack.
    pose proof (SinsemillaHash.words_le_digit_sum _ Hall) as Hw.
    unfold commit_ivk_words in Hw |- *.
    rewrite SinsemillaHash.hash_words_length in Hw.
    symmetry. exact Hw.
  Qed.

  (** ** Part iii: the ivk complete add over the CommitIvkR blinding fold

      The [out.v]/[add.v] pattern ([circuit_proof/note_commit_r/out.v],
      [circuit_proof/note_commit/add.v]) at the CommitIvk regions.  The
      ladder-distinctness precondition is an explicit hypothesis throughout:
      its discharge from [Holds] is the per-base certificate chain
      ([ladder/note_commit_r.v] instantiated at CommitIvkR), over the
      [circuit_proof/commit_ivk_r/] certificate files. *)

  Import OrchardActionFixedBase.

  (** *** Table split of the 85-window CommitIvkR spec table *)

  Definition commit_ivk_r_first : EccSpec.fixed_window :=
    List.hd fixed_window_default
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params).

  Definition commit_ivk_r_middle : EccSpec.fixed_table :=
    List.firstn 83
      (List.skipn 1 (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)).

  Definition commit_ivk_r_last : EccSpec.fixed_window :=
    List.nth 84 (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      fixed_window_default.

  Lemma commit_ivk_r_table_split :
    EccSpec.fixed_table_of_rows
      Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows =
    commit_ivk_r_first :: commit_ivk_r_middle ++ [commit_ivk_r_last].
  Proof. reflexivity. Qed.

  Lemma commit_ivk_r_spec_table_split :
    OrchardCircuitSpec.commit_ivk_r orchard_internal_params =
    commit_ivk_r_first :: commit_ivk_r_middle ++ [commit_ivk_r_last].
  Proof. reflexivity. Qed.

  Lemma commit_ivk_r_middle_length :
    List.length commit_ivk_r_middle = 83%nat.
  Proof. reflexivity. Qed.

  Lemma commit_ivk_r_table_length :
    List.length (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) =
      85%nat.
  Proof. reflexivity. Qed.

  (** *** Shape and length of the CommitIvkR constants rows (the
      [us_free/main.v] per-base facts) *)

  Lemma commit_ivk_r_rows_standard :
    List.forallb OrchardActionUsFree.standard_row_shape
      Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma commit_ivk_r_rows_length :
    List.length
      Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows =
      85%nat.
  Proof. reflexivity. Qed.

  (** *** Facts of the CommitIvkR blinding-leg regions, from [Holds]

      [commit_ivk.v]'s ladder combinators are verbatim copies of
      [circuit.v]'s generic ones (only the return record types differ, which
      neither the fact lists nor the output cells mention), so the bridges
      are [reflexivity]. *)

  Lemma commit_ivk_r_incomplete_facts_eq :
    layouter_facts
      (CIvk.synth_full_mul_incomplete
        (CIvk.commit_ivk_region RegionId.CommitIvk.FixedBaseIncomplete)) =
    layouter_facts
      (Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows).
  Proof. reflexivity. Qed.

  Lemma commit_ivk_r_incomplete_facts_raw
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (CIvk.synth_full_mul_incomplete
          (CIvk.commit_ivk_region RegionId.CommitIvk.FixedBaseIncomplete))).
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 7 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    unfold CIvk.synthesize_full_fixed_base_mul_commit_ivk_r in H.
    apply interpret_layouter_facts_bind_left in H.
    exact H.
  Qed.

  Lemma commit_ivk_r_incomplete_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
          Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows)).
  Proof.
    pose proof (commit_ivk_r_incomplete_facts_raw Γ Hcircuit) as H.
    rewrite commit_ivk_r_incomplete_facts_eq in H.
    exact H.
  Qed.

  Lemma commit_ivk_r_fixed_base_facts_eq :
    layouter_facts CIvk.synthesize_full_fixed_base_mul_commit_ivk_r =
    layouter_facts
      (let🞵 result :=
        Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
          Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows in
       Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
         (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast)
         result).
  Proof. reflexivity. Qed.

  Lemma commit_ivk_r_fixed_base_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (let🞵 result :=
          Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
            Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast)
           result)).
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 7 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    rewrite commit_ivk_r_fixed_base_facts_eq in H.
    exact H.
  Qed.

  (** *** The output point of the local ladder, as cell values *)

  Definition civk_point_value
      (Γ : Assignment.t columns RegionId.t)
      (point : CIvk.AssignedPoint.t) : Point.t := {|
    Point.x := eval_cell Γ point.(CIvk.AssignedPoint.x);
    Point.y := eval_cell Γ point.(CIvk.AssignedPoint.y);
  |}.

  Lemma commit_ivk_r_value_eq
      (Γ : Assignment.t columns RegionId.t) :
    civk_point_value Γ
      (layouter_value CIvk.synthesize_full_fixed_base_mul_commit_ivk_r) =
    assigned_point_value Γ
      (layouter_value
        (let🞵 result :=
          Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
            Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast)
           result)).
  Proof. reflexivity. Qed.

  (** *** Per-window correctness against the split spec table *)

  Lemma commit_ivk_r_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (commit_ivk_r_first :: commit_ivk_r_middle ++
            [commit_ivk_r_last]) j = Some w) :
    incomplete_additions_window_point Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
      (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read_scalar_from_windows Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
        j)
      (List.nth j
        (read_us Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
        0).
  Proof.
    rewrite <- commit_ivk_r_spec_table_split in Hnth.
    assert (Hj : (j < 85)%nat).
    { pose proof (proj1 (List.nth_error_Some
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) j)) as Hlt.
      rewrite commit_ivk_r_table_length in Hlt.
      apply Hlt.
      rewrite Hnth.
      discriminate. }
    apply List.nth_error_nth with (d := fixed_window_default) in Hnth.
    rewrite <- Hnth.
    exact
      (OrchardActionUsFree.full_width_table_window_correct Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        commit_ivk_r_rows_standard
        commit_ivk_r_rows_length
        (commit_ivk_r_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        j Hj).
  Qed.

  (** *** Window x-nonzero for the 85 CommitIvkR windows *)

  Lemma commit_ivk_r_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
          (Z.of_nat i))) <> 0.
  Proof.
    apply (full_width_incomplete_window_x_nonzero Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
      Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
      i
      (commit_ivk_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      Hi).
  Qed.

  (** *** The preconditions, under the explicit distinctness hypothesis *)

  Lemma commit_ivk_r_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0)) :
    incomplete_additions_complete_precondition Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0).
  Proof.
    pose proof (commit_ivk_r_incomplete_facts Γ Hcircuit) as Hfacts.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (commit_ivk_r_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (commit_ivk_r_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact Hdistinct.
  Qed.

  Lemma commit_ivk_r_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0)) :
    incomplete_additions_precondition Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (commit_ivk_r_complete_of_holds Γ Hcircuit Hdistinct).
  Qed.

  Lemma commit_ivk_r_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0)) :
    fixed_scalar_mul_circuit_precondition
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
      (read_us Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85).
  Proof.
    pose proof (commit_ivk_r_window_correct Γ Hcircuit 0%nat
      commit_ivk_r_first eq_refl) as Hfirst.
    pose proof (commit_ivk_r_incomplete_facts Γ Hcircuit) as Hfacts.
    rewrite commit_ivk_r_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, commit_ivk_r_middle_length. reflexivity.
    - exact (commit_ivk_r_complete_of_holds Γ Hcircuit Hdistinct).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (commit_ivk_r_window_correct Γ Hcircuit).
      cbn [List.nth_error].
      exact Hnth.
    - apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, commit_ivk_r_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        (S j) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete)
        (1 + Z.of_nat j))).
  Qed.

  (** *** K-out: the blinding-leg output as [fixed_scalar_mul] of the
      CommitIvkR spec table at the read scalar/us *)

  Lemma full_commit_ivk_r_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0)) :
    Field.map_mod
      (civk_point_value Γ
        (layouter_value CIvk.synthesize_full_fixed_base_mul_commit_ivk_r)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
      (read_us Γ
        (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85).
  Proof.
    pose proof (commit_ivk_r_fixed_base_facts Γ Hcircuit) as Hfacts.
    rewrite (commit_ivk_r_value_eq Γ).
    rewrite commit_ivk_r_spec_table_split.
    eapply full_with_rows_scalar_mul_correct
      with (first := commit_ivk_r_first)
           (middle := commit_ivk_r_middle)
           (last := commit_ivk_r_last).
    - exact Hfacts.
    - exact (holds_gates Γ Hcircuit).
    - exact (commit_ivk_r_incomplete_of_holds Γ Hcircuit Hdistinct).
    - exact commit_ivk_r_table_split.
    - exact commit_ivk_r_middle_length.
    - intros j w Hnth.
      exact (commit_ivk_r_window_correct Γ Hcircuit j w Hnth).
    - rewrite <- commit_ivk_r_spec_table_split.
      exact (commit_ivk_r_circuit_precondition_of_holds Γ Hcircuit Hdistinct).
  Qed.

  (** *** The "M + [r] R" complete-add bridge, from [Holds] alone *)

  (** The hash-to-point output cells, as [commit_ivk.v]'s own point record
      (the [m] operand of the complete addition). *)
  Definition ivk_hash_result : SChip.CommitIvkHashResult.t :=
    layouter_value
      (SChip.synthesize_hash_to_point_commit_ivk
        (CIvk.commit_ivk_region RegionId.CommitIvk.HashToPoint)
        CIvk.q_commit_ivk_m_x CIvk.q_commit_ivk_m_y
        piece_a piece_b piece_c piece_d).

  Definition ivk_hash_m : CIvk.AssignedPoint.t := {|
    CIvk.AssignedPoint.x :=
      ivk_hash_result.(SChip.CommitIvkHashResult.x);
    CIvk.AssignedPoint.y :=
      ivk_hash_result.(SChip.CommitIvkHashResult.y);
  |}.

  (** The hash point's cells are the fold output cells of
      [commit_ivk_hash_point_correct] ([A0]/[A3] at row 51). *)
  Lemma ivk_hash_m_x_cell :
    ivk_hash_m.(CIvk.AssignedPoint.x) = W.adv HR Advice.A0 51.
  Proof. reflexivity. Qed.

  Lemma ivk_hash_m_y_cell :
    ivk_hash_m.(CIvk.AssignedPoint.y) = W.adv HR Advice.A3 51.
  Proof. reflexivity. Qed.

  (** Record conversion into [circuit.v]'s point record. *)
  Definition to_circuit_point
      (point : CIvk.AssignedPoint.t)
      : Garden.Orchard.circuit.AssignedPoint.t := {|
    Garden.Orchard.circuit.AssignedPoint.x :=
      point.(CIvk.AssignedPoint.x);
    Garden.Orchard.circuit.AssignedPoint.y :=
      point.(CIvk.AssignedPoint.y);
  |}.

  Lemma ivk_complete_add_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_complete_point_add
          (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd)
          "M + [r] R"
          (to_circuit_point ivk_hash_m)
          (to_circuit_point
            (layouter_value
              CIvk.synthesize_full_fixed_base_mul_commit_ivk_r)))).
  Proof.
    pose proof (commit_ivk_synth_facts Γ Hcircuit) as H.
    unfold CIvk.synthesize in H.
    do 7 apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    do 2 apply interpret_layouter_facts_in_namespace in H.
    do 2 apply interpret_layouter_facts_bind_right in H.
    cbv beta zeta in H.
    apply interpret_layouter_facts_bind_left in H.
    exact H.
  Qed.

  (** The ivk output point equals the complete addition of the hash point
      and the blinding point, from [Holds] alone (the [ak]/[nk] argument
      cells are arbitrary: neither the output cells nor the operand records
      depend on them). *)
  Lemma ivk_point_add_bridge
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (civk_point_value Γ (layouter_value (CIvk.synthesize ak nk))) =
    EccSpec.point_add
      (Field.map_mod (civk_point_value Γ ivk_hash_m))
      (Field.map_mod
        (civk_point_value Γ
          (layouter_value CIvk.synthesize_full_fixed_base_mul_commit_ivk_r))).
  Proof.
    exact
      (complete_point_add_correct Γ
        (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd)
        "M + [r] R"
        (to_circuit_point ivk_hash_m)
        (to_circuit_point
          (layouter_value CIvk.synthesize_full_fixed_base_mul_commit_ivk_r))
        (ivk_complete_add_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)).
  Qed.

  (** ** The composition (part iii): ivk = M + [rivk] CommitIvkR as the
      circuit's ladder fold

      The ivk output point (the value [commit_ivk.synthesize] returns — the
      [CompletePointAdd] result cells) is [point_add] of the hash point and
      [fixed_scalar_mul] of the CommitIvkR spec table at the read
      scalar/us — [read_rivk]'s windows and the [A5] square-root witnesses.
      The fold-to-group-multiple switch ([Pallas.mul] via
      [ProtocolMulCore]) and the discharge of [Hdistinct] from [Holds] are
      performed in [circuit_proof/ownership/diversified_address.v] over the
      CommitIvkR certificate set ([circuit_proof/commit_ivk_r/]). *)
  Theorem commit_ivk_point_add_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0))
      (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (civk_point_value Γ (layouter_value (CIvk.synthesize ak nk))) =
    EccSpec.point_add
      (Field.map_mod (civk_point_value Γ ivk_hash_m))
      (EccSpec.fixed_scalar_mul
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        (read_scalar_from_windows Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
        (read_us Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)).
  Proof.
    rewrite (ivk_point_add_bridge Γ Hcircuit ak nk).
    rewrite (full_commit_ivk_r_scalar_mul_correct Γ Hcircuit Hdistinct).
    reflexivity.
  Qed.

  (** Combined corollary: under nondegeneracy of the hashed words, the hash
      operand is [sinsemilla_hash_to_point] itself — the exact
      [OrchardProtocolSpec.commit_ivk] shape up to the blinding leg's
      fold-to-group-multiple switch. *)
  Corollary commit_ivk_point_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate commit_ivk_Q (commit_ivk_words Γ))
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 0))
      (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (civk_point_value Γ (layouter_value (CIvk.synthesize ak nk))) =
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.commit_ivk_q orchard_circuit_params)
        (commit_ivk_words Γ))
      (EccSpec.fixed_scalar_mul
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        (read_scalar_from_windows Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)
        (read_us Γ
          (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85)).
  Proof.
    rewrite (commit_ivk_point_add_correct Γ Hcircuit Hdistinct ak nk).
    rewrite <- (commit_ivk_hash_point_correct Γ Hcircuit Hnondeg).
    reflexivity.
  Qed.
End CommitIvkHash.
