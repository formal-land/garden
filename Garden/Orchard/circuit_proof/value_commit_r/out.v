(** * ValueCommitR K-out: the [Hblind] hypothesis from [Holds] alone

    Composes the generic full-width wrapper
    [full_with_rows_scalar_mul_correct]
    ([circuit_proof/fixed_base/main.v]) with:
    - the whole full-width program facts peeled from [Holds]
      ([value_commit_r_fixed_base_facts], both regions of
      [synth_value_commit_r_mul]);
    - the ladder-distinctness certificate
      [ValueCommitRLadder.value_commit_r_distinct_holds]
      ([circuit_proof/ladder/value_commit_r.v]), lifted
      through [incomplete_complete_precondition_of_distinct] and
      [incomplete_complete_implies_precondition]
      into the incomplete-additions precondition;
    - the circuit precondition
      [value_commit_r_circuit_precondition_of_holds]
      (the counterpart of the spend_auth_g form in
      [circuit_proof/fixed_base/main.v]);
    - the per-window spec-table match [value_commit_r_window_correct],
      built from the generic
      [OrchardActionUsFree.full_width_table_window_correct].

    The final lemma [value_commit_r_hblind] is verbatim the [Hblind]
    hypothesis of [cv_net_x_correct_of_fixed_base] /
    [cv_net_y_correct_of_fixed_base] ([circuit_proof/bridges.v:545/611]),
    closed from [Holds] alone.  It is the ValueCommitR counterpart of
    [ValueCommitVOut.value_commit_v_hvalue]
    ([circuit_proof/value_commit_v/out.v]) and of
    [full_spend_auth_g_mul_correct_of_complete]
    ([circuit_proof/fixed_base/main.v:2841]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_r.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module ValueCommitROut.
  Import OrchardActionFixedBase.

  (* The consumed ladder/cert lemmas carry [is_square]/[field_sqrt]/
     [fixed_window_point_canonical] over the concrete Pallas modulus;
     conversion must compare them by congruence, never unfold ([modpow] at the
     ~2^253 exponent blows the term up). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Table split of the 85-window ValueCommitR spec table *)

  Definition value_commit_r_first : EccSpec.fixed_window :=
    List.hd fixed_window_default
      (OrchardSpec.value_commit_r orchard_circuit_params).

  Definition value_commit_r_middle : EccSpec.fixed_table :=
    List.firstn 83
      (List.skipn 1 (OrchardSpec.value_commit_r orchard_circuit_params)).

  Definition value_commit_r_last : EccSpec.fixed_window :=
    List.nth 84 (OrchardSpec.value_commit_r orchard_circuit_params)
      fixed_window_default.

  Lemma value_commit_r_table_split :
    EccSpec.fixed_table_of_rows
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows =
    value_commit_r_first :: value_commit_r_middle ++ [value_commit_r_last].
  Proof. reflexivity. Qed.

  Lemma value_commit_r_spec_table_split :
    OrchardSpec.value_commit_r orchard_circuit_params =
    value_commit_r_first :: value_commit_r_middle ++ [value_commit_r_last].
  Proof. reflexivity. Qed.

  Lemma value_commit_r_middle_length :
    List.length value_commit_r_middle = 83%nat.
  Proof. reflexivity. Qed.

  (** ** Facts of the whole full-width program (incomplete + last region),
      from [Holds].  Same peel as
      [OrchardActionUsFree.value_commit_r_incomplete_facts], stopped before
      its final [bind_left] so both regions of
      [synth_value_commit_r_mul] are kept. *)

  Lemma value_commit_r_fixed_base_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        Garden.Orchard.circuit.synth_value_commit_r_mul).
  Proof.
    pose proof (value_commitment_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  (** ** Per-window correctness against the split spec table (through the
      generic [full_width_table_window_correct], not a [do 85] case split) *)

  Lemma value_commit_r_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (value_commit_r_first :: value_commit_r_middle ++
            [value_commit_r_last]) j = Some w) :
    incomplete_additions_window_point Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete) (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read_scalar_from_windows Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
        j)
      (List.nth j
        (read_us Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
        0).
  Proof.
    rewrite <- value_commit_r_spec_table_split in Hnth.
    assert (Hj : (j < 85)%nat).
    { pose proof (proj1 (List.nth_error_Some
        (OrchardSpec.value_commit_r orchard_circuit_params) j)) as Hlt.
      rewrite OrchardActionUsFree.value_commit_r_table_length in Hlt.
      apply Hlt.
      rewrite Hnth.
      discriminate. }
    apply List.nth_error_nth with (d := fixed_window_default) in Hnth.
    rewrite <- Hnth.
    exact
      (OrchardActionUsFree.full_width_table_window_correct Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        OrchardActionUsFree.value_commit_r_rows_standard
        OrchardActionUsFree.value_commit_r_rows_length
        (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        j Hj).
  Qed.

  (** ** Window x-nonzero for the 85 ValueCommitR windows (from the on-curve
      coordinates check; the counterpart of [spend_auth_g_window_x_nonzero]) *)

  Lemma value_commit_r_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitRIncomplete)
          (Z.of_nat i))) <> 0.
  Proof.
    apply (full_width_incomplete_window_x_nonzero Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete)
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
      i
      (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      Hi).
  Qed.

  (** ** The complete precondition from [Holds]: ladder distinctness +
      on-curve + x-nonzero, through
      [incomplete_complete_precondition_of_distinct] *)

  Lemma value_commit_r_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_complete_precondition Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 0).
  Proof.
    pose proof (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (value_commit_r_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (value_commit_r_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact
        (ValueCommitRLadder.value_commit_r_distinct_holds
          Γ Hcircuit).
  Qed.

  Lemma value_commit_r_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_precondition Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (value_commit_r_complete_of_holds Γ Hcircuit).
  Qed.

  (** ** The circuit precondition from [Holds] (the counterpart of
      [spend_auth_g_circuit_of_complete]) *)

  Lemma value_commit_r_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    fixed_scalar_mul_circuit_precondition
      (OrchardSpec.value_commit_r orchard_circuit_params)
      (read_scalar_from_windows Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
      (read_us Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85).
  Proof.
    pose proof (value_commit_r_window_correct Γ Hcircuit 0%nat
      value_commit_r_first eq_refl) as Hfirst.
    pose proof (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    rewrite value_commit_r_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, value_commit_r_middle_length. reflexivity.
    - exact (value_commit_r_complete_of_holds Γ Hcircuit).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (value_commit_r_window_correct Γ Hcircuit).
      cbn [List.nth_error].
      exact Hnth.
    - apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, value_commit_r_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        (S j) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        (1 + Z.of_nat j))).
  Qed.

  (** ** The [Hblind] hypothesis of [cv_net_x_correct_of_fixed_base] /
      [cv_net_y_correct_of_fixed_base] ([circuit_proof/bridges.v:545/611]),
      from [Holds] alone. *)

  Lemma value_commit_r_hblind
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          Garden.Orchard.circuit
            .synth_value_commit_r_mul)) =
    EccSpec.fixed_scalar_mul
      (OrchardSpec.value_commit_r orchard_circuit_params)
      (read_scalar_from_windows Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
      (read_us Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85).
  Proof.
    pose proof (value_commit_r_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synth_value_commit_r_mul
      in Hfacts |- *.
    rewrite value_commit_r_spec_table_split.
    eapply full_with_rows_scalar_mul_correct
      with (first := value_commit_r_first)
           (middle := value_commit_r_middle)
           (last := value_commit_r_last).
    - exact Hfacts.
    - exact (holds_gates Γ Hcircuit).
    - exact
        (value_commit_r_incomplete_of_holds Γ Hcircuit).
    - exact value_commit_r_table_split.
    - exact value_commit_r_middle_length.
    - intros j w Hnth.
      exact (value_commit_r_window_correct Γ Hcircuit j w Hnth).
    - rewrite <- value_commit_r_spec_table_split.
      exact
        (value_commit_r_circuit_precondition_of_holds
          Γ Hcircuit).
  Qed.

End ValueCommitROut.
