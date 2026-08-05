(** * Executable fixed-column image used by VK provenance certificates

    The relational replay grid is a function built by nesting 19,679 event
    updates. Reading every cell through that function rescans the update spine
    for each of 29 * 2048 cells.

    This module gives the same keygen-facing construction an explicitly
    linear primitive-array implementation.  It starts with the zero fixed
    plane, applies every [AssignFixed]/[FillFromRow] event in order, and then
    installs the selector-combination columns produced by the model's own
    [Compile.compile].  Advice, instance, selector and copy events do not
    write fixed cells.  The returned array is flat, column-major, and its
    observable API is [fixed_evaluation].

    Primitive arrays are persistent in Rocq's logic.  Each loop below uses
    only the newly returned array, so the VM can update in place. *)

From Corelib Require Import PrimArray.
From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.check.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module VkModelColumns.

  Definition rows_nat : nat := 2048.
  Definition fixed_count_nat : nat := 29.
  Definition base_fixed_count_nat : nat := 14.
  Definition flat_size_nat : nat := fixed_count_nat * rows_nat.

  Definition flat_size : PrimInt63.int := ArrayLinear.index flat_size_nat.

  Definition flat_index (column row : nat) : PrimInt63.int :=
    ArrayLinear.index (column * rows_nat + row).

  Definition in_domain (column row : Z) : bool :=
    (0 <=? column) && (column <? Z.of_nat fixed_count_nat)
      && (0 <=? row) && (row <? Z.of_nat rows_nat).

  Definition set_cell (array : PrimArray.array Z)
      (column row value : Z) : PrimArray.array Z :=
    if in_domain column row then
      PrimArray.set array
        (flat_index (Z.to_nat column) (Z.to_nat row)) value
    else array.

  Fixpoint fill_cells (fuel : nat) (array : PrimArray.array Z)
      (column row value : Z) : PrimArray.array Z :=
    match fuel with
    | O => array
    | S fuel =>
        fill_cells fuel (set_cell array column row value)
          column (row + 1) value
    end.

  Definition apply_event (array : PrimArray.array Z) (event : Raw.Event.t)
      : PrimArray.array Z :=
    match event with
    | Raw.Event.AssignFixed column row _ value =>
        set_cell array column row value
    | Raw.Event.FillFromRow column from_row to_row value =>
        fill_cells (Z.to_nat (Z.max 0 (to_row - from_row))) array
          column from_row value
    | _ => array
    end.

  Fixpoint apply_events (events : list Raw.Event.t)
      (array : PrimArray.array Z) : PrimArray.array Z :=
    match events with
    | [] => array
    | event :: events => apply_events events (apply_event array event)
    end.

  Fixpoint install_column (values : list Z) (column row : nat)
      (array : PrimArray.array Z) : PrimArray.array Z :=
    match values with
    | [] => array
    | value :: values =>
        install_column values column (S row)
          (PrimArray.set array (flat_index column row) value)
    end.

  Fixpoint install_combinations (column_ids : list Z)
      (columns : list (list Z)) (array : PrimArray.array Z)
      : PrimArray.array Z :=
    match column_ids, columns with
    | column :: column_ids, values :: columns =>
        install_column values (Z.to_nat column) O
          (install_combinations column_ids columns array)
    | _, _ => array
    end.

  Definition zero : PrimArray.array Z := PrimArray.make flat_size 0.

  Definition base_columns : PrimArray.array Z :=
    apply_events orchard_events zero.

  Definition combination_columns : list Z :=
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns).

  Definition combination_assignments : list (list Z) :=
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_assignments).

  Lemma combination_columns_unfold :
    combination_columns =
      OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns).
  Proof. reflexivity. Qed.

  Lemma combination_assignments_unfold :
    combination_assignments =
      OrchardCompiledCheck.compiled.(CompiledSystem.combination_assignments).
  Proof. reflexivity. Qed.

  Definition all_columns : PrimArray.array Z :=
    install_combinations combination_columns combination_assignments base_columns.

  Definition fixed_evaluation (column row : nat) : Z :=
    PrimArray.get all_columns (flat_index column row).

  Fixpoint collect_from (fuel column row : nat) : list Z :=
    match fuel with
    | O => []
    | S fuel => fixed_evaluation column row :: collect_from fuel column (S row)
    end.

  Definition fixed_column (column : nat) : list Z :=
    collect_from rows_nat column O.

  Lemma flat_size_fits : ArrayLinear.fits_nat flat_size_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma flat_size_allowed :
    PrimInt63.leb flat_size PrimArray.max_length = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_length : PrimArray.length zero = flat_size.
  Proof. vm_compute. reflexivity. Qed.

End VkModelColumns.
