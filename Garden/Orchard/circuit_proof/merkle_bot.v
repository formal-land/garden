(** * The Merkle-path clause of the adversarial Action statement

    §4.18.4 'Action Statement (Orchard)', 'Merkle path validity': "Either
    v^old = 0; or (path, pos) is a valid Merkle path of depth
    MerkleDepth^Orchard, as defined in section 4.9 'Merkle Path Validity',
    from Extract_P(cm^old) to the anchor rt^OrchardPool."

    This file discharges [OrchardAdversarialApi.anchor_obligation] from
    circuit acceptance with no witness-honesty hypothesis: neither the
    per-layer incomplete-addition nondegeneracy nor the canonicity of the
    witnessed decompositions is assumed.  The two slack sources of
    [OrchardActionMerkle.merkle_layer_ok] are handled differently, as the
    protocol handles them:

    - the Sinsemilla exceptional cases (§5.4.1.9) become the clause's
      second disjunct, the §4.9 escape ("the validity check is permitted
      to be implemented in such a way that it can pass if any hash value
      on the path, including the root, is 0"), spelled as an existential
      over the 32 layers of a ⊥ fold;
    - the wrapped-decomposition slack is absorbed into the *witnessed*
      reading of path validity licensed by the §4.18.4 note ("each layer
      does not check that its input bit sequence is a canonical encoding
      (in {0 .. q_P − 1}) of the integer from the previous layer"): each
      layer hashes a [merkle_message] of an integer pair only congruent
      mod [p] to the running node and the witnessed sibling.

    The middle conjunct of [OrchardActionMerkle.merkle_layer_canonical] is
    not slack at all and is derived outright: the [b_1] and [b_2] pieces
    are 5-bit short-lookup sites, so [b_1 + b_2·2^5 < 2^10 < p] follows
    from operational acceptance through the [ShortSite] machinery of
    [circuit_proof/lookup_closure.v].  Only the two 255-bit
    reconstructions stay in the congruence reading. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Pallas.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_fold_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities.cond_swap_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Field.Lemmas.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.bridges.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.adversarial_api.
Require Import Garden.Orchard.circuit_proof.lookup_closure.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardMerkleBot.
  Import OrchardActionInputs.
  Import OrchardActionMerkle.
  Import OrchardProtocolSpecBot.
  Import OrchardAdversarialApi.
  Import OrchardShortLookupClosure.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** The 64 [b_1]/[b_2] short-lookup sites

      [circuit.synthesize_merkle_hash_layer_{1,2}] range-checks both
      pieces with the shared short-lookup gadget
      ([lookup_range_check.synthesize_short], width 5, inverse constant
      [inv_two_pow_5], checked cell [A9] at offset 0) — the same gadget,
      column and three-row shape as the eleven note-commitment sites.  The
      sites are therefore a plain instantiation of the [ShortSite]
      machinery; the placement row is spelled as the layout function
      itself, so [site_start_ok] is a computation rather than a pinned
      literal. *)

  Definition site_merkle_b1 (layer : Z) : ShortSite := {|
    ss_region :=
      Garden.Orchard.circuit.merkle_region layer
        RegionId.Merkle.Region.RangeB1;
    ss_bits := 5;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5;
    ss_start :=
      region_start_of
        (Garden.Orchard.circuit.merkle_region layer
          RegionId.Merkle.Region.RangeB1);
  |}.

  Definition site_merkle_b2 (layer : Z) : ShortSite := {|
    ss_region :=
      Garden.Orchard.circuit.merkle_region layer
        RegionId.Merkle.Region.RangeB2;
    ss_bits := 5;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5;
    ss_start :=
      region_start_of
        (Garden.Orchard.circuit.merkle_region layer
          RegionId.Merkle.Region.RangeB2);
  |}.

  Definition merkle_sites : list ShortSite :=
    List.map (fun n : nat => site_merkle_b1 (Z.of_nat n))
      (List.seq 0%nat 32%nat) ++
    List.map (fun n : nat => site_merkle_b2 (Z.of_nat n))
      (List.seq 0%nat 32%nat).

  Lemma merkle_facts_cert :
    List.forallb site_facts_ok merkle_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma merkle_start_cert :
    List.forallb site_start_ok merkle_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma merkle_inv_cert :
    List.forallb site_inv_ok merkle_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma merkle_qrunning_cert :
    List.forallb site_qrunning_ok merkle_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** Layer membership: every layer index in range is [Z.of_nat] of an
      element of [seq 0 32]. *)
  Lemma in_layer_seq (i : Z) (Hi : 0 <= i < 32) {A : Type} (f : Z -> A) :
    List.In (f i) (List.map (fun n : nat => f (Z.of_nat n))
      (List.seq 0%nat 32%nat)).
  Proof.
    apply List.in_map_iff.
    exists (Z.to_nat i).
    split.
    - f_equal. lia.
    - apply List.in_seq. lia.
  Qed.

  Lemma site_merkle_b1_in (i : Z) (Hi : 0 <= i < 32) :
    List.In (site_merkle_b1 i) merkle_sites.
  Proof.
    unfold merkle_sites.
    apply List.in_or_app.
    left.
    exact (in_layer_seq i Hi site_merkle_b1).
  Qed.

  Lemma site_merkle_b2_in (i : Z) (Hi : 0 <= i < 32) :
    List.In (site_merkle_b2 i) merkle_sites.
  Proof.
    unfold merkle_sites.
    apply List.in_or_app.
    right.
    exact (in_layer_seq i Hi site_merkle_b2).
  Qed.

  (** ** [merkle_b_range_ok] from operational acceptance *)

  Theorem merkle_b_range_ok_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    merkle_b_range_ok (realize Index.indices region_start_of grid).
  Proof.
    pose proof (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      as Hcircuit.
    intros i Hi.
    split.
    - exact (site_short_bound advice instance_ grid Hreplay Hcircuit
        merkle_sites merkle_facts_cert merkle_start_cert merkle_inv_cert
        merkle_qrunning_cert (site_merkle_b1 i) (site_merkle_b1_in i Hi)).
    - exact (site_short_bound advice instance_ grid Hreplay Hcircuit
        merkle_sites merkle_facts_cert merkle_start_cert merkle_inv_cert
        merkle_qrunning_cert (site_merkle_b2 i) (site_merkle_b2_in i Hi)).
  Qed.

  (** The middle conjunct of [OrchardActionMerkle.merkle_layer_canonical],
      derived rather than assumed: two 5-bit pieces reconstruct below
      [2^10], far below [p].  The two 255-bit reconstructions (conjuncts 1
      and 3) are the slack and stay absorbed in the witnessed
      reading. *)
  Lemma merkle_layer_canonical_middle
      (Γ : Assignment.t columns RegionId.t)
      (Hb : merkle_b_range_ok Γ)
      (i : Z) (Hi : 0 <= i < 32) :
    UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB1)
        Advice.A9 0)) +
      UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB2)
        Advice.A9 0)) * 2 ^ 5
      < Primes.pallas_p.
  Proof.
    destruct (Hb i Hi) as [Hb1 Hb2].
    change (2 ^ 5) with 32 in *.
    pose proof pallas_p_big as Hp.
    change (2 ^ 20) with 1048576 in Hp.
    lia.
  Qed.

  (** ** The canonicity-free per-layer core

      [OrchardActionMerkle.merkle_hash_layer_core] promotes the
      decomposition gate's mod-[p] identities to integer identities using
      all three canonicity conjuncts, and concludes the layer output is
      [merkle_crh] of the *node and sibling values*.  The variant below
      drops that promotion: it concludes (i) the layer output is the
      Sinsemilla hash (§5.4.1.9) of the region's own 52 words — no
      decomposition reasoning at all — and (ii) those 52 words are a
      [merkle_message] (the §5.4.1.3 MerkleCRH layout) of
      an integer pair whose residues are the decomposition gate's
      [left_node] and [right_node] cells.  Only the middle canonicity
      conjunct is used, in the sharper [ShortSite] form ([b_1], [b_2]
      below [2^5]), and it enters solely to identify the [b] piece's
      running-sum word with [b_1 + b_2·2^5].

      This is the §4.18.4 note "each layer does not check that its input
      bit sequence is a canonical encoding (in {0 .. q_P − 1}) of the
      integer from the previous layer", made explicit: the witnessed pair
      is congruent mod [p] to the node/sibling pair and need not be its
      canonical 255-bit encoding. *)
  Lemma merkle_hash_layer_fold
      (Γ : Assignment.t columns RegionId.t)
      (q1 : Selector.t) (q2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (H : RegionId.t)
      (i left right beta1 beta2 : Z)
      (Hi : 0 <= i < 32)
      (Hload : interpret_facts Γ (layouter_facts
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector q1 ⟧ (H, Z.of_nat j) = 1)
      (Hgate : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          q1 q2 x_a x_p lambda_1 lambda_2 ⟧ (H, row))
      (Hlookup : forall row : Z,
        eval_lookup_argument Γ (H, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q1 q2 x_a x_p bits lambda_1 lambda_2))
      (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) q2 H (Z.of_nat j) = 1)
      (Hq2_24 : Γ.(Assignment.fixed) q2 H 24 = 0)
      (Hq2_26 : Γ.(Assignment.fixed) q2 H 26 = 0)
      (Hq2_51 : Γ.(Assignment.fixed) q2 H 51 = 2)
      (Hacc0 : SinsemillaHash.acc_at Γ x_a x_p lambda_1 lambda_2 H 0 = merkle_Q)
      (Hnondeg : SinsemillaHash.nondegenerate merkle_Q
        (SinsemillaHash.hash_words Γ q2 bits H 52))
      (Hbeta1_small : 0 <= beta1 < 2 ^ 5)
      (Hbeta2_small : 0 <= beta2 < 2 ^ 5)
      (Hdec :
        {|
          DecompositionCheck.l_whole := UnOp.from i;
          DecompositionCheck.left_node := left;
          DecompositionCheck.right_node := right;
          DecompositionCheck.z1_b :=
            Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 26);
        |} =
          DecompositionCheck.output
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 0))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 25))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 27))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 1))
            beta1
            beta2) :
    Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (H, 52) =
      EccSpec.extract_x
        (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
          (SinsemillaHash.hash_words Γ q2 bits H 52)) /\
    exists l r : Z,
      SinsemillaHash.hash_words Γ q2 bits H 52 =
        SinsemillaSpec.merkle_message i l r /\
      UnOp.from l = left /\
      UnOp.from r = right.
  Proof.
    (* Row schedule: [q_s3 = 0] below the final row, [q_s3 = 2] on row 51. *)
    assert (Hq3 : forall j : nat, (S j < 52)%nat ->
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧
          (H, Z.of_nat j) = 0).
    { intros j Hj.
      destruct (Nat.eq_dec j 24) as [-> | Hj24].
      - apply (q_s3_eval_zero Γ q2 H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - destruct (Nat.eq_dec j 26) as [-> | Hj26].
        + apply (q_s3_eval_zero Γ q2 H (Z.of_nat 26) 0);
            [exact Hq2_26 | left; reflexivity].
        + apply (q_s3_eval_zero Γ q2 H (Z.of_nat j) 1);
            [apply Hq2_one; lia | right; reflexivity]. }
    assert (Hq3_final :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧
          (H, Z.of_nat (52 - 1)) = 2).
    { apply q_s3_eval_two. exact Hq2_51. }
    (* The 52-round point fold. *)
    pose proof (SinsemillaHashFold.hash_to_point_rows_correct Γ H q1 q2
        x_a x_p bits lambda_1 lambda_2 52 ltac:(lia) merkle_Q
        Hload Hsel (fun j _ => Hgate (Z.of_nat j))
        (fun j _ => Hlookup (Z.of_nat j))
        Hq3 Hq3_final Hacc0 Hnondeg) as Hpoint.
    assert (Hbound : forall j : nat, (j < 52)%nat ->
        0 <= SinsemillaHash.word_at Γ q2 bits H (Z.of_nat j) < 2 ^ 10).
    { intros j Hj.
      apply (word_at_bound Γ H (Z.of_nat j) q1 q2 x_a x_p bits lambda_1
        lambda_2 Hload (Hsel j Hj) (Hlookup (Z.of_nat j))). }
    (* The output-cell reading.  [rewrite <- Hpoint] first: matching a
       projection of the fold against a constant application would send
       the 52-round symbolic fold to unification. *)
    split.
    { unfold EccSpec.extract_x.
      rewrite <- Hpoint.
      cbn [Point.x].
      change (Z.of_nat 52) with 52.
      reflexivity. }
    (* The four piece telescopes (a at 0, its z1 tail at 1, b at 25, c at
       27) and the b-piece's z1 cell. *)
    assert (HA : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 0) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (0 + Z.of_nat j))
          (List.seq 0%nat 25%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (0 + Z.of_nat j) with (Z.of_nat j) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (0 + Z.of_nat (25 - 1)) with (Z.of_nat 24) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - intros j Hj.
        replace (0 + Z.of_nat j) with (Z.of_nat j) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HA1 : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 1) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (1 + Z.of_nat j))
          (List.seq 0%nat 24%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (1 + Z.of_nat (24 - 1)) with (Z.of_nat 24) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - intros j Hj.
        replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HB : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 25) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (25 + Z.of_nat j))
          (List.seq 0%nat 2%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (25 + Z.of_nat j) with (Z.of_nat 25) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (25 + Z.of_nat (2 - 1)) with (Z.of_nat 26) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 26) 0);
          [exact Hq2_26 | left; reflexivity].
      - intros j Hj.
        replace (25 + Z.of_nat j) with (Z.of_nat (25 + j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HC : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 27) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (27 + Z.of_nat j))
          (List.seq 0%nat 25%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (27 + Z.of_nat j) with (Z.of_nat (27 + j)) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (27 + Z.of_nat (25 - 1)) with (Z.of_nat 51) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 51) 2);
          [exact Hq2_51 | right; reflexivity].
      - intros j Hj.
        replace (27 + Z.of_nat j) with (Z.of_nat (27 + j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HB1 : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 26) =
        SinsemillaHash.word_at Γ q2 bits H 26).
    { apply (word_at_last Γ q2 bits H 26 0);
        [exact Hq2_26 | left; reflexivity]. }
    set (w := SinsemillaHash.word_at Γ q2 bits H) in *.
    set (dsA := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (0 + Z.of_nat j)) (List.seq 0%nat 25%nat)))
      in *.
    set (dsA1 := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (1 + Z.of_nat j)) (List.seq 0%nat 24%nat)))
      in *.
    set (dsB := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (25 + Z.of_nat j)) (List.seq 0%nat 2%nat)))
      in *.
    set (dsC := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (27 + Z.of_nat j)) (List.seq 0%nat 25%nat)))
      in *.
    (* Structural digit-sum identities and bounds. *)
    assert (HheadA : dsA = w 0 + 2 ^ 10 * dsA1).
    { unfold dsA, w.
      rewrite (SinsemillaHash.digit_sum_words_head Γ q2 bits H 0 24%nat).
      unfold dsA1, w.
      f_equal. }
    assert (HdsB : dsB = w 25 + 2 ^ 10 * w 26).
    { unfold dsB.
      cbn [List.seq List.map SinsemillaHash.digit_sum].
      replace (25 + Z.of_nat 0) with 25 by lia.
      replace (25 + Z.of_nat 1) with 26 by lia.
      lia. }
    assert (HboundA1 : 0 <= dsA1 < 2 ^ 240).
    { unfold dsA1.
      pose proof (SinsemillaHash.digit_sum_bound
        (List.map (fun j : nat => w (1 + Z.of_nat j)) (List.seq 0%nat 24%nat)))
        as Hb.
      rewrite List.length_map, List.length_seq in Hb.
      apply Hb.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply Hbound. lia. }
    assert (Hw0 : 0 <= w 0 < 2 ^ 10) by (apply (Hbound 0%nat); lia).
    (* The decomposition-gate components.  [Hl] is promoted to an integer
       identity by the layer index's own range; [Hz1b] by the two 5-bit
       lookup bounds.  [Hleft] and [Hright] are kept as the mod-[p]
       identities they are — the witnessed reading. *)
    pose proof (f_equal DecompositionCheck.l_whole Hdec) as Hl.
    pose proof (f_equal DecompositionCheck.left_node Hdec) as Hleft.
    pose proof (f_equal DecompositionCheck.right_node Hdec) as Hright.
    pose proof (f_equal DecompositionCheck.z1_b Hdec) as Hz1b.
    unfold DecompositionCheck.output in Hl, Hleft, Hright, Hz1b.
    cbn [DecompositionCheck.l_whole DecompositionCheck.left_node
      DecompositionCheck.right_node DecompositionCheck.z1_b]
      in Hl, Hleft, Hright, Hz1b.
    rewrite HA, HA1 in Hl.
    rewrite HA1, HB in Hleft.
    rewrite HC in Hright.
    rewrite HB1 in Hz1b.
    clear Hdec.
    assert (Hw26_int : w 26 = beta1 + beta2 * 2 ^ 5)
      by (clear -Hz1b Hbeta1_small Hbeta2_small; field_solve).
    assert (Hi_int : i = w 0)
      by (clear -Hl HheadA HboundA1 Hw0 Hi; field_solve).
    (* The witnessed pair: the two reconstructions read as integers, with
       no wrap assumption. *)
    exists (dsA1 + (w 25 + beta1 * 2 ^ 10) * 2 ^ 240),
      (beta2 + dsC * 2 ^ 5).
    (* Message identification: the 52 row words are exactly
       [merkle_message i left' right']. *)
    assert (Hsplit : SinsemillaHash.hash_words Γ q2 bits H 52 =
      List.map (fun j : nat => w (0 + Z.of_nat j)) (List.seq 0%nat 25%nat) ++
      List.map (fun j : nat => w (25 + Z.of_nat j)) (List.seq 0%nat 2%nat) ++
      List.map (fun j : nat => w (27 + Z.of_nat j)) (List.seq 0%nat 25%nat)).
    { unfold SinsemillaHash.hash_words.
      transitivity (List.map (fun j : nat => w (0 + Z.of_nat j))
        (List.seq 0%nat (25 + 27)%nat)); [reflexivity |].
      rewrite (map_z_seq_split w 0 25 27).
      f_equal. }
    assert (Hall52 : List.Forall (fun x : Z => 0 <= x < 2 ^ 10)
        (SinsemillaHash.hash_words Γ q2 bits H 52)).
    { unfold SinsemillaHash.hash_words.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      apply Hbound. lia. }
    assert (Hpack :
      i + (dsA1 + (w 25 + beta1 * 2 ^ 10) * 2 ^ 240) * 2 ^ 10 +
        (beta2 + dsC * 2 ^ 5) * 2 ^ 265 =
      SinsemillaHash.digit_sum (SinsemillaHash.hash_words Γ q2 bits H 52)).
    { rewrite Hsplit.
      rewrite !SinsemillaHash.digit_sum_app.
      rewrite !List.length_map, !List.length_seq.
      replace (10 * Z.of_nat 25) with 250 by lia.
      replace (10 * Z.of_nat 2) with 20 by lia.
      fold dsA dsB dsC.
      clear -Hi_int HheadA HdsB Hw26_int.
      lia. }
    split; [| split].
    - unfold SinsemillaSpec.merkle_message.
      change SinsemillaSpec.sinsemilla_k with 10.
      replace (10 + 255) with 265 by lia.
      rewrite Hpack.
      pose proof (SinsemillaHash.words_le_digit_sum _ Hall52) as Hw52.
      rewrite SinsemillaHash.hash_words_length in Hw52.
      symmetry.
      exact Hw52.
    - rewrite Hleft, HdsB, Hw26_int.
      mod_ring_solve.
    - rewrite Hright.
      mod_ring_solve.
  Qed.

  (** ** The per-layer statement, variant 1 (layers 0–15)

      The region navigation is that of
      [OrchardActionMerkle.merkle_layer_correct_1]; only the core it feeds
      and the conclusion differ.  The layer's output cell is the
      Sinsemilla hash of the region's own message, and that message is a
      [merkle_message] (§5.4.1.3 MerkleCRH) of a pair whose residues are
      the cond-swapped (node, sibling) pair — the witnessed reading. *)
  Lemma merkle_layer_bot_1
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : Z) (Hi : 0 <= i < 32) (Hlt : (i <? 16) = true)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hb : merkle_b_range_ok Γ)
      (Hnondeg : SinsemillaHash.nondegenerate merkle_Q (merkle_words Γ i)) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      EccSpec.extract_x
        (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
          (merkle_words Γ i)) /\
    exists l r : Z,
      merkle_words Γ i = SinsemillaSpec.merkle_message i l r /\
      UnOp.from l =
        (if read4 Γ (NP i) =? 1
         then read1 Γ (NP i)
         else UnOp.from (eval_cell Γ node)) /\
      UnOp.from r =
        (if read4 Γ (NP i) =? 1
         then UnOp.from (eval_cell Γ node)
         else read1 Γ (NP i)).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    destruct (Hb i Hi) as [Hb1 Hb2].
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hb1, Hb2.
    unfold Garden.Orchard.circuit.synthesize_merkle_layer in Hfacts |- *.
    rewrite Hlt in Hfacts |- *.
    unfold merkle_words, merkle_bits, merkle_q2, HTP in Hnondeg |- *.
    rewrite Hlt in Hnondeg |- *.
    (* Facts of the node-position region: selector and node copy. *)
    pose proof Hfacts as Hnp.
    apply interpret_layouter_facts_bind_left in Hnp.
    unfold Garden.Orchard.circuit.synthesize_node_position_1,
      Garden.Orchard.circuit.synthesize_node_position_instance in Hnp.
    apply interpret_layouter_facts_in_namespace in Hnp.
    apply interpret_layouter_facts_add_region in Hnp.
    cbn [region_facts region_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad List.app
      interpret_facts interpret_fact] in Hnp.
    destruct Hnp as (HselNP & Hcopy_node & _).
    (* Facts of the hash layer: hash region and decomposition region. *)
    pose proof Hfacts as Hh.
    apply interpret_layouter_facts_bind_right in Hh.
    unfold Garden.Orchard.circuit.synthesize_merkle_hash_layer_1 in Hh.
    apply interpret_layouter_facts_in_namespace in Hh.
    do 5 apply interpret_layouter_facts_bind_right in Hh.
    pose proof Hh as Hhash.
    apply interpret_layouter_facts_bind_left in Hhash.
    apply interpret_layouter_facts_in_namespace in Hhash.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_1
      in Hhash.
    apply interpret_layouter_facts_add_region in Hhash.
    pose proof Hh as Hdecf.
    apply interpret_layouter_facts_bind_right,
      interpret_layouter_facts_bind_left in Hdecf.
    unfold Garden.Orchard.circuit.synthesize_merkle_decomposition_1,
      Garden.Orchard.circuit.synthesize_merkle_decomposition_instance in Hdecf.
    apply interpret_layouter_facts_add_region in Hdecf.
    cbn [region_facts region_value layouter_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      List.app interpret_facts interpret_fact] in Hdecf.
    destruct Hdecf as (HselD & Hc_a & Hc_b & Hc_c & Hc_left & Hc_right &
      Hc_z1a & Hc_z1b & Hc_b1 & Hc_b2 & Hconst_l & _).
    cbn in Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2.
    clear Hfacts Hh.
    (* Hash-region facts: seed selector/fixed/constant, per-piece schedules
       and piece copies. *)
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
    pose proof Hhash as HpieceA.
    do 3 apply interpret_region_facts_bind_right in HpieceA.
    apply interpret_region_facts_bind_left in HpieceA.
    pose proof Hhash as HpieceB.
    do 4 apply interpret_region_facts_bind_right in HpieceB.
    apply interpret_region_facts_bind_left in HpieceB.
    pose proof Hhash as HpieceC.
    do 5 apply interpret_region_facts_bind_right in HpieceC.
    apply interpret_region_facts_bind_left in HpieceC.
    clear Hhash.
    pose proof HpieceA as HselA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselA.
    apply interpret_region_facts_bind_left in HselA.
    pose proof HpieceA as Hq2A.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2A.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2A.
    pose proof HpieceA as HcopyA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyA.
    do 2 apply interpret_region_facts_bind_right in HcopyA.
    apply interpret_region_facts_bind_left in HcopyA.
    cbn in HcopyA.
    destruct HcopyA as [HcopyA _].
    pose proof HpieceB as HselB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselB.
    apply interpret_region_facts_bind_left in HselB.
    pose proof HpieceB as Hq2B.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2B.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2B.
    pose proof HpieceB as HcopyB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyB.
    do 2 apply interpret_region_facts_bind_right in HcopyB.
    apply interpret_region_facts_bind_left in HcopyB.
    cbn in HcopyB.
    destruct HcopyB as [HcopyB _].
    pose proof HpieceC as HselC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselC.
    apply interpret_region_facts_bind_left in HselC.
    pose proof HpieceC as Hq2C.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2C.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2C.
    pose proof HpieceC as HcopyC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyC.
    do 2 apply interpret_region_facts_bind_right in HcopyC.
    apply interpret_region_facts_bind_left in HcopyC.
    cbn in HcopyC.
    destruct HcopyC as [HcopyC _].
    clear HpieceA HpieceB HpieceC.
    (* Row schedules assembled across the three pieces. *)
    assert (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_1 ⟧
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint,
            Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ HselA
          (enable_selector_rows_fact _ Selector.QSinsemilla1_1 0 25 j Hj25))
          as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ HselB
            (enable_selector_rows_fact _ Selector.QSinsemilla1_1 25 2 (j - 25)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ HselC
            (enable_selector_rows_fact _ Selector.QSinsemilla1_1 27 25 (j - 27)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint)
          (Z.of_nat j) = 1).
    { intros j Hj H24 H26 H51.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ Hq2A
          (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 0 25 j false
            ltac:(lia))) as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ Hq2B
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 25 2 (j - 25)
              false ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ Hq2C
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 27 25 (j - 27)
              true ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_24 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        24 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2A
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 0 25 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (0 + Z.of_nat (25 - 1)) with 24 in Hf by lia.
      exact Hf. }
    assert (Hq2_26 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        26 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2B
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 25 2 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (25 + Z.of_nat (2 - 1)) with 26 in Hf by lia.
      exact Hf. }
    assert (Hq2_51 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        51 = 2).
    { pose proof (interpret_facts_In Γ _ _ Hq2C
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 27 25 true
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (27 + Z.of_nat (25 - 1)) with 51 in Hf by lia.
      exact Hf. }
    clear HselA HselB HselC Hq2A Hq2B Hq2C.
    (* The four gates of the layer, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_cs :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_dec :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
          Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
          .decomposition_check_gate
          Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0 Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A3 Advice.A4
        (enabled_nonzero Γ Selector.QSinsemilla4_1 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs0 _ 0
      Garden.Orchard.circuit.merkle_q_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A0 Advice.A1 Advice.A3
      Advice.A4 _ 0 (UnOp.from Garden.Orchard.circuit.merkle_q_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A0 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite merkle_q_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite merkle_q_y_reduced in Hacc0.
    (* The decomposition-gate record, routed through the copies to the hash
       region's running-sum cells and the range/swap cells. *)
    pose proof (DecompositionCheck.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0 Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QMerkleDecompose1 _ 0 HselD) Hgate_dec)
      as Hdec.
    cbn in Hconst_l.
    rewrite !(eval_advice_cur_cell Γ) in Hdec.
    rewrite !(eval_advice_next_cell Γ) in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hdec.
    replace (0 + 1) with 1 in Hdec by lia.
    rewrite Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2,
      Hconst_l in Hdec.
    rewrite <- HcopyA, <- HcopyB, <- HcopyC in Hdec.
    clear Hy Hgate_yq Hgate_dec Hc_a Hc_b Hc_c Hc_left Hc_right Hc_z1a Hc_z1b
      Hc_b1 Hc_b2 Hconst_l HselD HselY HfixY HconstX HcopyA HcopyB HcopyC.
    (* The canonicity-free core. *)
    pose proof (merkle_hash_layer_fold Γ Selector.QSinsemilla1_1
      Fixed.QSinsemilla2_1 Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.HashToPoint)
      i
      (UnOp.from (Γ.(Assignment.advice) Advice.A2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A3
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB1) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB2) 0))
      Hi Hload Hsel Hgate_sin
      (fun row => generator_table_lookup_holds_1 Γ Hcircuit _ row)
      Hq2_one Hq2_24 Hq2_26 Hq2_51 Hacc0 Hnondeg Hb1 Hb2 Hdec)
      as Hcore.
    destruct Hcore as (Hout & l & r & Hmsg & Hl & Hr).
    split; [exact Hout |].
    exists l, r.
    split; [exact Hmsg |].
    (* Cond-swap decode: the swapped pair against the [merkle_path_of]
       reads. *)
    pose proof (CondSwap.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QCondSwap1 _ 0 HselNP) Hgate_cs) as Hcs.
    pose proof (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QCondSwap1 _ 0 HselNP) Hgate_cs) as Hbool.
    rewrite (cond_swap_output_if _ _ _ Hbool) in Hcs.
    pose proof (f_equal CondSwap.a_swapped Hcs) as Hleft_sw.
    pose proof (f_equal CondSwap.b_swapped Hcs) as Hright_sw.
    with_strategy opaque [UnOp.from] cbn in Hleft_sw, Hright_sw.
    cbn in Hcopy_node.
    rewrite Hcopy_node in Hleft_sw, Hright_sw.
    rewrite Hl, Hr.
    setoid_rewrite Hleft_sw.
    setoid_rewrite Hright_sw.
    unfold read1, read4, read_advice, NP.
    with_strategy opaque [UnOp.from] cbn.
    destruct (UnOp.from (Γ.(Assignment.advice) Advice.A4
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.NodePosition) 0)
      =? 1) eqn:Hbit.
    - split; rewrite !FieldRewrite.from_from; reflexivity.
    - split; rewrite !FieldRewrite.from_from; reflexivity.
  Qed.
  (** ** The per-layer statement, variant 2 (layers 16–31)

      The variant-1 statement and proof with the second column bundle,
      mirroring [OrchardActionMerkle.merkle_layer_correct_2]: the sibling
      is read on [A6] and the position bit on [A9]. *)
  Lemma merkle_layer_bot_2
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : Z) (Hi : 0 <= i < 32) (Hlt : (i <? 16) = false)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hb : merkle_b_range_ok Γ)
      (Hnondeg : SinsemillaHash.nondegenerate merkle_Q (merkle_words Γ i)) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      EccSpec.extract_x
        (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
          (merkle_words Γ i)) /\
    exists l r : Z,
      merkle_words Γ i = SinsemillaSpec.merkle_message i l r /\
      UnOp.from l =
        (if read9 Γ (NP i) =? 1
         then read6 Γ (NP i)
         else UnOp.from (eval_cell Γ node)) /\
      UnOp.from r =
        (if read9 Γ (NP i) =? 1
         then UnOp.from (eval_cell Γ node)
         else read6 Γ (NP i)).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    destruct (Hb i Hi) as [Hb1 Hb2].
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hb1, Hb2.
    unfold Garden.Orchard.circuit.synthesize_merkle_layer in Hfacts |- *.
    rewrite Hlt in Hfacts |- *.
    unfold merkle_words, merkle_bits, merkle_q2, HTP in Hnondeg |- *.
    rewrite Hlt in Hnondeg |- *.
    (* Facts of the node-position region: selector and node copy. *)
    pose proof Hfacts as Hnp.
    apply interpret_layouter_facts_bind_left in Hnp.
    unfold Garden.Orchard.circuit.synthesize_node_position_2,
      Garden.Orchard.circuit.synthesize_node_position_instance in Hnp.
    apply interpret_layouter_facts_in_namespace in Hnp.
    apply interpret_layouter_facts_add_region in Hnp.
    cbn [region_facts region_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad List.app
      interpret_facts interpret_fact] in Hnp.
    destruct Hnp as (HselNP & Hcopy_node & _).
    (* Facts of the hash layer: hash region and decomposition region. *)
    pose proof Hfacts as Hh.
    apply interpret_layouter_facts_bind_right in Hh.
    unfold Garden.Orchard.circuit.synthesize_merkle_hash_layer_2 in Hh.
    apply interpret_layouter_facts_in_namespace in Hh.
    do 5 apply interpret_layouter_facts_bind_right in Hh.
    pose proof Hh as Hhash.
    apply interpret_layouter_facts_bind_left in Hhash.
    apply interpret_layouter_facts_in_namespace in Hhash.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_2
      in Hhash.
    apply interpret_layouter_facts_add_region in Hhash.
    pose proof Hh as Hdecf.
    apply interpret_layouter_facts_bind_right,
      interpret_layouter_facts_bind_left in Hdecf.
    unfold Garden.Orchard.circuit.synthesize_merkle_decomposition_2,
      Garden.Orchard.circuit.synthesize_merkle_decomposition_instance in Hdecf.
    apply interpret_layouter_facts_add_region in Hdecf.
    cbn [region_facts region_value layouter_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      List.app interpret_facts interpret_fact] in Hdecf.
    destruct Hdecf as (HselD & Hc_a & Hc_b & Hc_c & Hc_left & Hc_right &
      Hc_z1a & Hc_z1b & Hc_b1 & Hc_b2 & Hconst_l & _).
    cbn in Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2.
    clear Hfacts Hh.
    (* Hash-region facts: seed selector/fixed/constant, per-piece schedules
       and piece copies. *)
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
    pose proof Hhash as HpieceA.
    do 3 apply interpret_region_facts_bind_right in HpieceA.
    apply interpret_region_facts_bind_left in HpieceA.
    pose proof Hhash as HpieceB.
    do 4 apply interpret_region_facts_bind_right in HpieceB.
    apply interpret_region_facts_bind_left in HpieceB.
    pose proof Hhash as HpieceC.
    do 5 apply interpret_region_facts_bind_right in HpieceC.
    apply interpret_region_facts_bind_left in HpieceC.
    clear Hhash.
    pose proof HpieceA as HselA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselA.
    apply interpret_region_facts_bind_left in HselA.
    pose proof HpieceA as Hq2A.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2A.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2A.
    pose proof HpieceA as HcopyA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyA.
    do 2 apply interpret_region_facts_bind_right in HcopyA.
    apply interpret_region_facts_bind_left in HcopyA.
    cbn in HcopyA.
    destruct HcopyA as [HcopyA _].
    pose proof HpieceB as HselB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselB.
    apply interpret_region_facts_bind_left in HselB.
    pose proof HpieceB as Hq2B.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2B.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2B.
    pose proof HpieceB as HcopyB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyB.
    do 2 apply interpret_region_facts_bind_right in HcopyB.
    apply interpret_region_facts_bind_left in HcopyB.
    cbn in HcopyB.
    destruct HcopyB as [HcopyB _].
    pose proof HpieceC as HselC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselC.
    apply interpret_region_facts_bind_left in HselC.
    pose proof HpieceC as Hq2C.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2C.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2C.
    pose proof HpieceC as HcopyC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyC.
    do 2 apply interpret_region_facts_bind_right in HcopyC.
    apply interpret_region_facts_bind_left in HcopyC.
    cbn in HcopyC.
    destruct HcopyC as [HcopyC _].
    clear HpieceA HpieceB HpieceC.
    (* Row schedules assembled across the three pieces. *)
    assert (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_2 ⟧
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint,
            Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ HselA
          (enable_selector_rows_fact _ Selector.QSinsemilla1_2 0 25 j Hj25))
          as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ HselB
            (enable_selector_rows_fact _ Selector.QSinsemilla1_2 25 2 (j - 25)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ HselC
            (enable_selector_rows_fact _ Selector.QSinsemilla1_2 27 25 (j - 27)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint)
          (Z.of_nat j) = 1).
    { intros j Hj H24 H26 H51.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ Hq2A
          (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 0 25 j false
            ltac:(lia))) as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ Hq2B
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 25 2 (j - 25)
              false ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ Hq2C
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 27 25 (j - 27)
              true ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_24 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        24 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2A
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 0 25 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (0 + Z.of_nat (25 - 1)) with 24 in Hf by lia.
      exact Hf. }
    assert (Hq2_26 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        26 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2B
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 25 2 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (25 + Z.of_nat (2 - 1)) with 26 in Hf by lia.
      exact Hf. }
    assert (Hq2_51 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        51 = 2).
    { pose proof (interpret_facts_In Γ _ _ Hq2C
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 27 25 true
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (27 + Z.of_nat (25 - 1)) with 51 in Hf by lia.
      exact Hf. }
    clear HselA HselB HselC Hq2A Hq2B Hq2C.
    (* The four gates of the layer, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_cs :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_dec :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
          Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
          .decomposition_check_gate
          Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0 Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
        Advice.A5 Advice.A6 Advice.A8 Advice.A9
        (enabled_nonzero Γ Selector.QSinsemilla4_2 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs1 _ 0
      Garden.Orchard.circuit.merkle_q_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A5 Advice.A6 Advice.A8
      Advice.A9 _ 0 (UnOp.from Garden.Orchard.circuit.merkle_q_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A5 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite merkle_q_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite merkle_q_y_reduced in Hacc0.
    (* The decomposition-gate record, routed through the copies to the hash
       region's running-sum cells and the range/swap cells. *)
    pose proof (DecompositionCheck.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0 Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QMerkleDecompose2 _ 0 HselD) Hgate_dec)
      as Hdec.
    cbn in Hconst_l.
    rewrite !(eval_advice_cur_cell Γ) in Hdec.
    rewrite !(eval_advice_next_cell Γ) in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hdec.
    replace (0 + 1) with 1 in Hdec by lia.
    rewrite Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2,
      Hconst_l in Hdec.
    rewrite <- HcopyA, <- HcopyB, <- HcopyC in Hdec.
    clear Hy Hgate_yq Hgate_dec Hc_a Hc_b Hc_c Hc_left Hc_right Hc_z1a Hc_z1b
      Hc_b1 Hc_b2 Hconst_l HselD HselY HfixY HconstX HcopyA HcopyB HcopyC.
    (* The canonicity-free core. *)
    pose proof (merkle_hash_layer_fold Γ Selector.QSinsemilla1_2
      Fixed.QSinsemilla2_2 Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.HashToPoint)
      i
      (UnOp.from (Γ.(Assignment.advice) Advice.A7
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A8
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB1) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB2) 0))
      Hi Hload Hsel Hgate_sin
      (fun row => generator_table_lookup_holds_2 Γ Hcircuit _ row)
      Hq2_one Hq2_24 Hq2_26 Hq2_51 Hacc0 Hnondeg Hb1 Hb2 Hdec)
      as Hcore.
    destruct Hcore as (Hout & l & r & Hmsg & Hl & Hr).
    split; [exact Hout |].
    exists l, r.
    split; [exact Hmsg |].
    (* Cond-swap decode: the swapped pair against the [merkle_path_of]
       reads. *)
    pose proof (CondSwap.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QCondSwap2 _ 0 HselNP) Hgate_cs) as Hcs.
    pose proof (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QCondSwap2 _ 0 HselNP) Hgate_cs) as Hbool.
    rewrite (cond_swap_output_if _ _ _ Hbool) in Hcs.
    pose proof (f_equal CondSwap.a_swapped Hcs) as Hleft_sw.
    pose proof (f_equal CondSwap.b_swapped Hcs) as Hright_sw.
    with_strategy opaque [UnOp.from] cbn in Hleft_sw, Hright_sw.
    cbn in Hcopy_node.
    rewrite Hcopy_node in Hleft_sw, Hright_sw.
    rewrite Hl, Hr.
    setoid_rewrite Hleft_sw.
    setoid_rewrite Hright_sw.
    unfold read6, read9, read_advice, NP.
    with_strategy opaque [UnOp.from] cbn.
    destruct (UnOp.from (Γ.(Assignment.advice) Advice.A9
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.NodePosition) 0)
      =? 1) eqn:Hbit.
    - split; rewrite !FieldRewrite.from_from; reflexivity.
    - split; rewrite !FieldRewrite.from_from; reflexivity.
  Qed.
  (** The per-layer statement, dispatched across the two column variants
      and reconciled with the layer-dependent authentication-path reads
      of [OrchardAdversarialApi] (sibling on A1/A6, position bit on
      A4/A9). *)
  Lemma merkle_layer_bot
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : Z) (Hi : 0 <= i < 32)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hb : merkle_b_range_ok Γ)
      (Hnondeg : SinsemillaHash.nondegenerate merkle_Q (merkle_words Γ i)) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      EccSpec.extract_x
        (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
          (merkle_words Γ i)) /\
    exists l r : Z,
      merkle_words Γ i = SinsemillaSpec.merkle_message i l r /\
      UnOp.from l =
        (if merkle_swap_at Γ i
         then merkle_sibling_at Γ i
         else UnOp.from (eval_cell Γ node)) /\
      UnOp.from r =
        (if merkle_swap_at Γ i
         then UnOp.from (eval_cell Γ node)
         else merkle_sibling_at Γ i).
  Proof.
    unfold merkle_swap_at, merkle_swap_cell, merkle_sibling_at,
      merkle_node_position.
    destruct (i <? 16) eqn:Hlt.
    - exact (merkle_layer_bot_1 Γ Hcircuit i Hi Hlt node Hfacts Hb Hnondeg).
    - exact (merkle_layer_bot_2 Γ Hcircuit i Hi Hlt node Hfacts Hb Hnondeg).
  Qed.

  (** ** The running node cell along the synthesized path

      [circuit.synthesize_merkle_layers] threads the node cell forward
      from the leaf, incrementing the layer index; [iter_from] is that
      iteration over an abstract step, so the fixpoint body never mentions
      a synthesis constant. *)

  Fixpoint iter_from {A : Type} (step : Z -> A -> A) (layer : Z) (x : A)
      (k : nat) : A :=
    match k with
    | O => x
    | S m => iter_from step (layer + 1) (step layer x) m
    end.

  Definition merkle_step (layer : Z)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    layouter_value (Garden.Orchard.circuit.synthesize_merkle_layer layer node).

  Definition node_from (layer : Z)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) (k : nat)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    iter_from merkle_step layer node k.

  Lemma iter_from_S {A : Type} (step : Z -> A -> A) (k : nat) :
    forall (layer : Z) (x : A),
      iter_from step layer x (S k) =
        step (layer + Z.of_nat k) (iter_from step layer x k).
  Proof.
    induction k as [| k IH]; intros layer x.
    - replace (layer + Z.of_nat 0) with layer by lia.
      reflexivity.
    - assert (E1 : iter_from step layer x (S (S k)) =
        iter_from step (layer + 1) (step layer x) (S k)) by reflexivity.
      assert (E2 : iter_from step layer x (S k) =
        iter_from step (layer + 1) (step layer x) k) by reflexivity.
      rewrite E1, E2, (IH (layer + 1) (step layer x)).
      replace (layer + Z.of_nat (S k)) with (layer + 1 + Z.of_nat k) by lia.
      reflexivity.
  Qed.

  (** The [adversarial_api] node chain is the same iteration started at the
      leaf cell. *)
  Lemma merkle_node_cell_eq (k : nat) :
    merkle_node_cell k = node_from 0 cm_old_x_cell k.
  Proof.
    unfold node_from.
    induction k as [| k IH].
    - reflexivity.
    - rewrite iter_from_S.
      change (0 + Z.of_nat k) with (Z.of_nat k).
      rewrite <- IH.
      reflexivity.
  Qed.

  Lemma layers_value :
    forall (n : nat) (layer : Z)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t),
      layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layers n layer node) =
        node_from layer node n.
  Proof.
    unfold node_from.
    induction n as [| n IH]; intros layer node.
    - reflexivity.
    - cbn [Garden.Orchard.circuit.synthesize_merkle_layers Monad.bind
        Garden.Halo2.Synthesis.LayouterIsMonad layouter_value].
      rewrite (IH (layer + 1)).
      reflexivity.
  Qed.

  (** Every layer of a synthesized run of [n] layers carries its own
      layouter facts, at its own index and running node cell. *)
  Lemma layers_facts (Γ : Assignment.t columns RegionId.t) :
    forall (n : nat) (layer : Z)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t),
      interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layers n layer node)) ->
      forall k : nat, (k < n)%nat ->
        interpret_facts Γ (layouter_facts
          (Garden.Orchard.circuit.synthesize_merkle_layer
            (layer + Z.of_nat k) (node_from layer node k))).
  Proof.
    induction n as [| n IH]; intros layer node Hfacts k Hk; [lia |].
    cbn [Garden.Orchard.circuit.synthesize_merkle_layers Monad.bind
      Garden.Halo2.Synthesis.LayouterIsMonad] in Hfacts.
    destruct k as [| k].
    - apply interpret_layouter_facts_bind_left in Hfacts.
      replace (layer + Z.of_nat 0) with layer by lia.
      exact Hfacts.
    - apply interpret_layouter_facts_bind_right in Hfacts.
      cbv beta in Hfacts.
      pose proof (IH (layer + 1) (merkle_step layer node) Hfacts k
        ltac:(lia)) as Hstep.
      replace (layer + Z.of_nat (S k)) with (layer + 1 + Z.of_nat k) by lia.
      exact Hstep.
  Qed.

  (** ** The §4.9 escape is decidable at the 32 layers

      A layer's fold is undefined or it is not; no classical reasoning is
      needed to split the clause, since the disjunct is an equation
      between options. *)
  Lemma layer_bot_dec (Γ : Assignment.t columns RegionId.t) (n : nat) :
    (exists i : nat, (i < n)%nat /\
       sinsemilla_hash_to_point_bot merkle_Q
         (merkle_words Γ (Z.of_nat i)) = None) \/
    (forall i : nat, (i < n)%nat ->
       sinsemilla_hash_to_point_bot merkle_Q
         (merkle_words Γ (Z.of_nat i)) <> None).
  Proof.
    induction n as [| n IH].
    - right. intros i Hi. lia.
    - destruct IH as [Hex | Hall].
      + left.
        destruct Hex as (i & Hi & Hnone).
        exists i.
        split; [lia | exact Hnone].
      + destruct (sinsemilla_hash_to_point_bot merkle_Q
          (merkle_words Γ (Z.of_nat n))) as [P |] eqn:E.
        * right.
          intros i Hi.
          destruct (Nat.eq_dec i n) as [-> | Hne].
          -- rewrite E. discriminate.
          -- apply Hall. lia.
        * left.
          exists n.
          split; [lia | exact E].
  Qed.

  (** ** The clause

      From acceptance and the two 5-bit lookup ranges alone.  No layer's
      nondegeneracy and no 255-bit canonicity is assumed: an exceptional
      layer lands in disjunct 2 (§4.9), and a non-canonical decomposition
      is absorbed by the witnessed message pair of
      [OrchardAdversarialApi.anchor_path_tracks] (§4.18.4's note on
      non-canonical layer inputs). *)
  Theorem anchor_obligation_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hb : merkle_b_range_ok Γ) :
    anchor_obligation Γ.
  Proof.
    unfold anchor_obligation.
    destruct (Z.eq_dec (OrchardSpec.in_v_old (read_action_inputs Γ)) 0)
      as [Hv0 | Hvold]; [left; exact Hv0 |].
    destruct (layer_bot_dec Γ 32) as [Hex | Hall];
      [right; left; exact Hex |].
    right; right.
    (* Every layer's fold is defined, hence nondegenerate. *)
    assert (Hnd : forall i : nat, (i < 32)%nat ->
        SinsemillaHash.nondegenerate merkle_Q (merkle_words Γ (Z.of_nat i)))
      by (intros i Hi;
          exact (proj1 (hash_to_point_bot_iff merkle_Q _) (Hall i Hi))).
    (* The path's layouter facts, per layer. *)
    pose proof (merkle_path_facts Γ Hcircuit) as Hpath.
    change (interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_path cm_old_x_cell)))
      in Hpath.
    unfold Garden.Orchard.circuit.synthesize_merkle_path in Hpath.
    apply interpret_layouter_facts_in_namespace in Hpath.
    assert (Hlayer : forall i : nat, (i < 32)%nat ->
        interpret_facts Γ (layouter_facts
          (Garden.Orchard.circuit.synthesize_merkle_layer
            (Z.of_nat i) (merkle_node_cell i)))).
    { intros i Hi.
      pose proof (layers_facts Γ 32%nat 0 cm_old_x_cell Hpath i Hi) as Hf.
      change (0 + Z.of_nat i) with (Z.of_nat i) in Hf.
      rewrite (merkle_node_cell_eq i).
      exact Hf. }
    (* The per-layer conclusions. *)
    assert (Hstep : forall i : nat, (i < 32)%nat ->
        UnOp.from (eval_cell Γ (merkle_node_cell (S i))) =
          EccSpec.extract_x
            (SinsemillaSpec.sinsemilla_hash_to_point merkle_Q
              (merkle_words Γ (Z.of_nat i))) /\
        (exists l r : Z,
          merkle_words Γ (Z.of_nat i) =
            SinsemillaSpec.merkle_message (Z.of_nat i) l r /\
          UnOp.from l =
            (if merkle_swap_at Γ (Z.of_nat i)
             then merkle_sibling_at Γ (Z.of_nat i)
             else UnOp.from (eval_cell Γ (merkle_node_cell i))) /\
          UnOp.from r =
            (if merkle_swap_at Γ (Z.of_nat i)
             then UnOp.from (eval_cell Γ (merkle_node_cell i))
             else merkle_sibling_at Γ (Z.of_nat i)))).
    { intros i Hi.
      exact (merkle_layer_bot Γ Hcircuit (Z.of_nat i) ltac:(lia)
        (merkle_node_cell i) (Hlayer i Hi) Hb (Hnd i Hi)). }
    repeat apply conj.
    - (* Each layer's output node is the ⊥-carrying hash of its message. *)
      intros i Hi.
      rewrite (sinsemilla_hash_bot_some merkle_Q _ (Hnd i Hi)).
      unfold merkle_node_at, SinsemillaSpec.sinsemilla_hash.
      f_equal.
      exact (proj1 (Hstep i Hi)).
    - (* Each layer hashes a [merkle_message] of a witnessed pair. *)
      intros i Hi.
      exact (proj2 (Hstep i Hi)).
    - (* The leaf: the path starts at the witnessed old-note commitment. *)
      reflexivity.
    - (* The root: the anchor row, on the active branch. *)
      unfold merkle_node_at.
      rewrite (merkle_node_cell_eq 32%nat).
      rewrite <- (layers_value 32%nat 0 cm_old_x_cell).
      symmetry.
      exact (OrchardActionBridges.anchor_instance_eq_merkle_root_when_active
        Γ Hcircuit Hvold).
  Qed.

  (** The clause at the operational level: replay success and ideal
      acceptance of the serialized circuit discharge both premises — the
      relational [Holds] through [orchard_operational_sound], the two
      5-bit ranges through the [ShortSite] certificates. *)
  Corollary anchor_obligation_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    anchor_obligation (realize Index.indices region_start_of grid).
  Proof.
    exact (anchor_obligation_of_holds
      (realize Index.indices region_start_of grid)
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      (merkle_b_range_ok_operational advice instance_ grid Hreplay Hmock)).
  Qed.

  (** ** The collision-resistance reading of the witnessed pair

      Statement only: no proof is attempted, and none is possible from
      the circuit alone — the wrapped decomposition is exactly the slack
      §4.18.4 grants ("each layer does not check that its input bit
      sequence is a canonical encoding …").  What a cryptographic
      assumption buys is stated here in the style of the balance proof's
      discrete-logarithm reduction: under Theorem 5.4.3
      ([OrchardAdversarialApi.SinsemillaCollisionReduction]), an accepted
      assignment either decomposes canonically at every layer — in which
      case [anchor_path_tracks] collapses to
      [OrchardActionMerkle.merkle_root_cell_correct]'s conclusion, the
      total §4.9 path validity — or exhibits a nontrivial discrete
      logarithm relation among the Merkle domain point and the Sinsemilla
      generators.

      Two caveats belong with the statement, since it is stated and not
      proved.  First, the reduction has content only against a second
      accepted assignment (or a second message) that hashes to the same
      value: a single wrapped witness exhibits no collision by itself, so
      the honest single-assignment reading of the §4.9 escape is the
      exceptional-case one
      ([OrchardAdversarialApi.anchor_exceptional_or_dlog_claim], Theorem
      5.4.4), which this file's [anchor_obligation] already carries as its
      second disjunct.  Second, recovering the canonical pair from a
      collision additionally needs the injectivity of
      [SinsemillaSpec.merkle_message] on the bounded pairs, which the
      decomposition gate provides but [anchor_path_tracks]' existential
      does not record. *)
  Definition anchor_canonical_or_dlog_claim : Prop :=
    SinsemillaCollisionReduction ->
    forall (Γ : Assignment.t columns RegionId.t),
      Holds Γ ->
      merkle_b_range_ok Γ ->
      (forall i : Z, 0 <= i < 32 -> merkle_layer_canonical Γ i) \/
      (exists (c0 : Z) (cs : list (Z * Z)),
         sinsemilla_dlog_relation merkle_Q c0 cs).
End OrchardMerkleBot.
