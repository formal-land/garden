(** * Compilation provenance of the abstract fixed-column commitment inputs *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.provenance.ModelColumns.
Require Import Garden.Orchard.vk.provenance.ColumnValues.
Require Import Garden.Orchard.vk.provenance.ModelColumnsCorrect.

Import Plonkish.

Module VkCommitmentColumnsCorrect.
  (** The row vector supplied to mathematical [commit_lagrange] is exactly
      the compiled Garden fixed column, read after selector combinations and
      reduced to the Pallas scalar field. *)
  Theorem fixed_values_compiled_grid
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) :
    Garden.Halo2.realize.main.apply_events orchard_events
      (initial_grid advice instance_) = Some grid ->
    forall index, (index < VkModelColumns.fixed_count_nat)%nat ->
      VkCommitmentColumns.fixed_values index =
      List.map
        (fun row =>
          (OrchardCompiled.with_combinations
            OrchardCompiledCheck.compiled grid).(RawGrid.cell)
              Raw.ColumnKind.Fixed (Z.of_nat index) (Z.of_nat row)
            mod Primes.pallas_p)
        (List.seq O VkCommitmentColumns.rows_nat).
  Proof.
    intros Hreplay index Hindex.
    destruct (VkModelColumnsCorrect.all_columns_match_compiled_grid
      advice instance_ grid Hreplay) as [_ Hagree].
    rewrite VkCommitmentColumns.fixed_values_map.
    apply List.map_ext_in.
    intros row Hrow.
    apply List.in_seq in Hrow.
    destruct Hrow as [Hrow0 Hrow].
    unfold VkModelColumns.fixed_evaluation.
    rewrite (Hagree index row Hindex).
    - reflexivity.
    - unfold VkCommitmentColumns.rows_nat in Hrow.
      unfold VkModelColumns.rows_nat.
      now cbn in Hrow.
  Qed.
End VkCommitmentColumnsCorrect.
