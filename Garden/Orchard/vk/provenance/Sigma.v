(** * Primitive-array view and model checks for Orchard's permutation sigma

    Generated targets are packed as [column * 2048 + row] in one [uint63].
    This is injective on Orchard's 15-by-2048 permutation cell space and,
    unlike a generated matrix of [nat * nat], does not elaborate tens of
    thousands of large Peano numerals. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Lists.List Bool.Bool Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.
Require Import Garden.Orchard.vk.provenance.generated.SigmaData.

Import ListNotations.
Import Plonkish.
Local Open Scope uint63_scope.

Module VkSigma.
  Definition width_nat : nat := 15.
  Definition rows_nat : nat := 2048.
  Definition width : PrimInt63.int := 15.
  Definition rows : PrimInt63.int := 2048.

  Definition pack_cell (cell : nat * nat) : PrimInt63.int :=
    PrimInt63.add
      (PrimInt63.mul (ArrayLinear.index (fst cell)) rows)
      (ArrayLinear.index (snd cell)).

  Definition model_column (column : nat) : PrimArray.array PrimInt63.int :=
    VkJacobian.array_of_list 0
      (List.map pack_cell
        (List.nth column OrchardCompiled.orchard_sigma.(Sigma.mapping) [])).

  Definition generated_column (column : nat)
      : PrimArray.array PrimInt63.int :=
    PrimArray.get VkSigmaData.mapping_array (ArrayLinear.index column).

  Definition column_check (column : nat) : bool :=
    let generated := generated_column column in
    let model := model_column column in
    PrimInt63.eqb (PrimArray.length generated) rows
      && PrimInt63.eqb (PrimArray.length model) rows
      && Prim63Loop.foldi_u63 rows_nat 0
        (fun row ok =>
          ok && PrimInt63.eqb
            (PrimArray.get generated row) (PrimArray.get model row)) true.

  Definition all_columns_check : bool :=
    PrimInt63.eqb (PrimArray.length VkSigmaData.mapping_array) width
      && Prim63Loop.foldi_from width_nat O
        (fun column ok => ok && column_check column) true.

  Definition packed_target (column row : nat) : PrimInt63.int :=
    PrimArray.get (generated_column column) (ArrayLinear.index row).

  Definition evaluation (column row : nat) : PallasP.t :=
    let target := packed_target column row in
    let target_column := PrimInt63.div target rows in
    let target_row := PrimInt63.mod target rows in
    PallasP.mul
      (PrimArray.get VkDomainData.delta_powers_array target_column)
      (PrimArray.get VkDomainData.omega_powers_array target_row).
End VkSigma.
