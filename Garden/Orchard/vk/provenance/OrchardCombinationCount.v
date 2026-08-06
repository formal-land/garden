(** * Small closed certificate for the Orchard selector-packing shape

    The expensive compiler-output checks live once in [compiled/check.v].
    This module exposes their lightweight consequences to the primitive-array
    column model and the VK printer. *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.compiled.check.

Import Plonkish.
Local Open Scope Z_scope.

Module OrchardCombinationCount.
  Definition checked_columns : list Z :=
    OrchardCompiledCheck.combination_columns_cache.

  Lemma columns_checked :
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns) =
      checked_columns.
  Proof. exact OrchardCompiledCheck.combination_columns_match. Qed.

  Lemma compiled_columns_checked :
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns) =
      checked_columns.
  Proof. exact columns_checked. Qed.

  Lemma compiled_columns_range_29 :
    List.Forall
      (fun column => 0 <= column < 29)
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_columns).
  Proof.
    rewrite compiled_columns_checked.
    unfold checked_columns, OrchardCompiledCheck.combination_columns_cache.
    repeat constructor; lia.
  Qed.

  Lemma compiled_checked :
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments) = 15%nat.
  Proof. exact OrchardCompiledCheck.combination_assignments_count_match. Qed.
End OrchardCombinationCount.
