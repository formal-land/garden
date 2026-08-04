(** * Mathematical row vectors committed into the Orchard verifying key

    This module fixes the inputs of the abstract [commit_lagrange] theorem.
    Fixed columns come from the model-derived primitive plane.  Permutation
    columns are stated directly from Garden's compiled sigma permutation and
    the mathematical domain constants; generated primitive arrays occur only
    in the refinement proof, not in this public definition. *)

From Stdlib Require Import ZArith Lists.List Arith.PeanoNat.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.provenance.Kinds.
Require Import Garden.Orchard.vk.provenance.ModelColumns.
Require Import Garden.Orchard.vk.provenance.Sigma.

Import ListNotations.

Module VkCommitmentColumns.
  Definition rows_nat : nat := 2048.

  Definition fixed_values (index : nat) : list Z :=
    List.map (fun value => value mod Primes.pallas_p)
      (VkModelColumns.fixed_column index).

  Definition permutation_target (column row : nat) : Plonkish.Sigma.cell :=
    Plonkish.Sigma.perm OrchardCompiled.orchard_sigma (column, row).

  Definition permutation_evaluation (column row : nat) : Z :=
    let target := permutation_target column row in
    (OrchardCompiledAlgebraic.delta ^ Z.of_nat (fst target) *
      PolyDomain.omega ^ Z.of_nat (snd target)) mod Primes.pallas_p.

  Definition permutation_values (index : nat) : list Z :=
    List.map
      (permutation_evaluation index)
      (List.seq O rows_nat).

  Definition values (kind : VkColumnKinds.column_kind) (index : nat)
      : list Z :=
    match kind with
    | VkColumnKinds.Fixed => fixed_values index
    | VkColumnKinds.Permutation => permutation_values index
    end.

  Definition valid_index (kind : VkColumnKinds.column_kind) (index : nat)
      : Prop :=
    match kind with
    | VkColumnKinds.Fixed => (index < VkModelColumns.fixed_count_nat)%nat
    | VkColumnKinds.Permutation => (index < VkSigma.width_nat)%nat
    end.

  Lemma collect_from_length (fuel column row : nat) :
    List.length (VkModelColumns.collect_from fuel column row) = fuel.
  Proof.
    revert row.
    induction fuel as [|fuel IH]; intros row; cbn; [reflexivity |].
    now rewrite IH.
  Qed.

  Lemma collect_from_map (fuel column row : nat) :
    VkModelColumns.collect_from fuel column row =
      List.map (VkModelColumns.fixed_evaluation column)
        (List.seq row fuel).
  Proof.
    revert row.
    induction fuel as [|fuel IH]; intros row; cbn; [reflexivity |].
    now rewrite IH.
  Qed.

  Lemma fixed_values_length (index : nat) :
    List.length (fixed_values index) = rows_nat.
  Proof.
    unfold fixed_values.
    rewrite List.length_map.
    unfold VkModelColumns.fixed_column, rows_nat.
    apply collect_from_length.
  Qed.

  Lemma fixed_values_map (index : nat) :
    fixed_values index =
      List.map
        (fun row =>
          VkModelColumns.fixed_evaluation index row mod Primes.pallas_p)
        (List.seq O rows_nat).
  Proof.
    unfold fixed_values, VkModelColumns.fixed_column.
    rewrite collect_from_map, List.map_map.
    reflexivity.
  Qed.

  Lemma permutation_values_length (index : nat) :
    List.length (permutation_values index) = rows_nat.
  Proof.
    unfold permutation_values.
    now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma values_length (kind : VkColumnKinds.column_kind) (index : nat) :
    List.length (values kind index) = rows_nat.
  Proof.
    destruct kind; [apply fixed_values_length | apply permutation_values_length].
  Qed.

  Lemma fixed_values_range (index : nat) :
    Forall (fun value => 0 <= value < Primes.pallas_p)
      (fixed_values index).
  Proof.
    unfold fixed_values.
    apply Forall_map.
    apply Forall_forall.
    intros value _.
    apply Z.mod_pos_bound.
    exact Primes.pallas_p_pos.
  Qed.

  Lemma permutation_values_range (index : nat) :
    Forall (fun value => 0 <= value < Primes.pallas_p)
      (permutation_values index).
  Proof.
    unfold permutation_values.
    apply Forall_map.
    apply Forall_forall.
    intros row _.
    unfold permutation_evaluation.
    destruct (permutation_target index row) as [target_column target_row].
    cbn [fst snd].
    apply Z.mod_pos_bound.
    exact Primes.pallas_p_pos.
  Qed.

  Lemma values_nonnegative
      (kind : VkColumnKinds.column_kind) (index : nat) :
    Forall (fun value => 0 <= value) (values kind index).
  Proof.
    destruct kind.
    - eapply Forall_impl; [|apply fixed_values_range].
      intros value Hvalue. exact (proj1 Hvalue).
    - eapply Forall_impl; [|apply permutation_values_range].
      intros value Hvalue. exact (proj1 Hvalue).
  Qed.
End VkCommitmentColumns.
