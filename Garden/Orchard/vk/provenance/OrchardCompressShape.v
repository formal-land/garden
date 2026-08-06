(** * Orchard instantiation of selector-compression shape facts *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.vk.provenance.CompressShape.
Require Import Garden.Orchard.vk.provenance.OrchardCombinationCount.

Import Plonkish.
Local Open Scope Z_scope.

Module OrchardCompressShape.
  Import CompressShape.

  Lemma orchard_infos_rows :
    List.Forall
      (fun info =>
        List.length info.(Compile.SelectorInfo.activations) = 2048%nat)
      OrchardCompiledCheck.orchard_infos.
  Proof.
    unfold OrchardCompiledCheck.orchard_infos.
    apply (proj2 (List.Forall_map _ _ _)).
    apply List.Forall_forall.
    intros [selector simple] Hin.
    unfold OrchardCompiledCheck.activation_of.
    cbn [Compile.SelectorInfo.activations].
    now rewrite !List.map_length, List.length_seq.
  Qed.

  Lemma orchard_combination_lengths :
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_columns) =
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments).
  Proof.
    exact
      (compile_from_metadata_combination_lengths
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        OrchardCompiledCheck.keygen_metadata).
  Qed.

  Lemma orchard_combination_values_rows :
    List.Forall
      (values_rows 2048)
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments).
  Proof.
    apply
      (compile_from_metadata_combination_assignments_rows
        orchard_indexed_system
        OrchardCompiledCheck.orchard_infos
        OrchardCompiledCheck.keygen_metadata
        2048).
    exact orchard_infos_rows.
  Qed.

  Lemma orchard_combination_count :
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments) = 15%nat.
  Proof.
    exact OrchardCombinationCount.compiled_checked.
  Qed.

  Lemma orchard_combination_columns_range :
    List.Forall
      (fun column => 0 <= column < 29)
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_columns).
  Proof.
    exact OrchardCombinationCount.compiled_columns_range_29.
  Qed.
End OrchardCompressShape.
