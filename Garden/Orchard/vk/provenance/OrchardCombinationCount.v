(** * Small closed certificate for the Orchard selector-packing count

    Row contents are intentionally absent: their length is proved by the
    symbolic [CompressShape] invariant. *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.vk.provenance.CompressShape.

Import Plonkish.
Import ListNotations.

Module OrchardCombinationCount.
  Definition combinations : list (list Z) :=
    fst
      (Compress.process
        (Compile.selector_descriptions orchard_indexed_system
          OrchardCompiledCheck.orchard_infos)
        (system_degree orchard_indexed_system)
        14).

  Lemma checked : List.length combinations = 15%nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma compile_assignments_eq_combinations :
    (Compile.compile
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        14
        OrchardCompiledPinned.permutation_columns
        OrchardCompiledPinned.constants)
        .(CompiledSystem.combination_assignments) = combinations.
  Proof.
    exact
      (CompressShape.compile_combination_assignments_eq_process
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        14
        OrchardCompiledPinned.permutation_columns
        OrchardCompiledPinned.constants).
  Qed.

  Lemma compile_checked :
    List.length
      (Compile.compile
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        14
        OrchardCompiledPinned.permutation_columns
        OrchardCompiledPinned.constants)
        .(CompiledSystem.combination_assignments) = 15%nat.
  Proof.
    rewrite compile_assignments_eq_combinations.
    exact checked.
  Qed.

  Definition columns : list Z :=
    List.map (fun index => 14 + Z.of_nat index)
      (List.seq 0 (List.length combinations)).

  Lemma columns_checked :
    columns = [14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].
  Proof.
    unfold columns.
    rewrite checked.
    reflexivity.
  Qed.

  Lemma compile_columns_eq_columns :
    (Compile.compile
      orchard_indexed_system
      OrchardCompiledCheck.orchard_infos
      14
      OrchardCompiledPinned.permutation_columns
      OrchardCompiledPinned.constants)
      .(CompiledSystem.combination_columns) = columns.
  Proof.
    exact
      (CompressShape.compile_combination_columns_eq_process
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        14
        OrchardCompiledPinned.permutation_columns
        OrchardCompiledPinned.constants).
  Qed.

  Lemma compile_columns_checked :
    (Compile.compile
      orchard_indexed_system
      OrchardCompiledCheck.orchard_infos
      14
      OrchardCompiledPinned.permutation_columns
      OrchardCompiledPinned.constants)
      .(CompiledSystem.combination_columns) =
    [14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].
  Proof.
    rewrite compile_columns_eq_columns.
    exact columns_checked.
  Qed.

  Lemma compiled_columns_checked :
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns) =
    [14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].
  Proof. exact compile_columns_checked. Qed.

  Lemma compiled_columns_range_29 :
    List.Forall
      (fun column => 0 <= column < 29)
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_columns).
  Proof.
    rewrite compiled_columns_checked.
    repeat constructor; lia.
  Qed.

  Lemma compiled_checked :
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments) = 15%nat.
  Proof.
    exact compile_checked.
  Qed.
End OrchardCombinationCount.
