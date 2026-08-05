(** * Semantic provenance of the generated permutation mapping

    The generated packed sigma columns are only a fast cache.  These lemmas
    turn a successful column check into pointwise equality with Garden's
    [OrchardCompiled.orchard_sigma] matrix. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Bool.Bool Lists.List ZArith micromega.Lia.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.provenance.ArrayOfListRefinement.
Require Import Garden.Orchard.vk.provenance.Sigma.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.
Local Open Scope uint63_scope.

Module VkSigmaRefinement.
  Local Lemma andb_right_true (left right : bool) :
    left && right = true -> right = true.
  Proof. destruct left, right; cbn; auto. Qed.

  Lemma foldi_from_and_true
      (count start : nat) (test : nat -> bool) (ok : bool) :
    Prim63Loop.foldi_from count start
      (fun index previous => previous && test index) ok = true ->
    ok = true /\
    forall index, (start <= index < start + count)%nat ->
      test index = true.
  Proof.
    revert start ok.
    induction count as [|count IH]; intros start ok Hfold.
    - cbn in Hfold. split; [exact Hfold | intros index Hindex; lia].
    - cbn in Hfold.
      destruct (IH (S start) (ok && test start) Hfold)
        as [Hfirst Hrest].
      apply andb_prop in Hfirst as [Hok Htest].
      split; [exact Hok |].
      intros index Hindex.
      destruct (Nat.eq_dec index start) as [-> | Hne]; [exact Htest |].
      apply Hrest. lia.
  Qed.

  Lemma column_check_pointwise (column : nat) :
    VkSigma.column_check column = true ->
    forall row, (row < VkSigma.rows_nat)%nat ->
      PrimArray.get (VkSigma.generated_column column)
        (ArrayLinear.index row) =
      PrimArray.get (VkSigma.model_column column)
        (ArrayLinear.index row).
  Proof.
    unfold VkSigma.column_check.
    intros Hcheck.
    pose proof (andb_right_true _ _ Hcheck) as Hfold.
    change 0%uint63 with (ArrayLinear.index O) in Hfold.
    rewrite Prim63Loop.foldi_u63_index in Hfold by
      exact ArrayLinear.vector_size_fits_word.
    destruct (foldi_from_and_true VkSigma.rows_nat O
      (fun row =>
        PrimInt63.eqb
          (PrimArray.get (VkSigma.generated_column column)
            (ArrayLinear.index row))
          (PrimArray.get (VkSigma.model_column column)
            (ArrayLinear.index row))) true Hfold) as [_ Hall].
    intros row Hrow.
    apply Uint63.eqb_spec.
    apply Hall. lia.
  Qed.

  Lemma orchard_n_rows_exact :
    OrchardCompiled.orchard_n_rows = VkSigma.rows_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma permutation_columns_length :
    List.length OrchardCompiledPinned.permutation_columns = VkSigma.width_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma orchard_mapping_wf :
    matrix_wf OrchardCompiledPinned.permutation_columns
      OrchardCompiled.orchard_n_rows
      OrchardCompiled.orchard_sigma.(Sigma.mapping).
  Proof.
    pose proof (sigma_of_copies_inv
      OrchardCompiledPinned.permutation_columns
      OrchardCompiled.orchard_n_rows
      OrchardCompiled.orchard_copies
      OrchardCompiled.orchard_sigma
      OrchardCompiled.orchard_sigma_eq) as Hinv.
    exact (proj1 (proj2 Hinv)).
  Qed.

  Lemma model_mapping_row_length (column : nat) :
    (column < VkSigma.width_nat)%nat ->
    List.length
      (List.nth column OrchardCompiled.orchard_sigma.(Sigma.mapping) []) =
      VkSigma.rows_nat.
  Proof.
    intros Hcolumn.
    pose proof (matrix_wf_nth
      OrchardCompiledPinned.permutation_columns
      OrchardCompiled.orchard_n_rows
      OrchardCompiled.orchard_sigma.(Sigma.mapping)
      column orchard_mapping_wf) as Hlength.
    rewrite permutation_columns_length in Hlength.
    specialize (Hlength Hcolumn).
    now rewrite orchard_n_rows_exact in Hlength.
  Qed.

  Definition model_target (column row : nat) : Sigma.cell :=
    List.nth row
      (List.nth column OrchardCompiled.orchard_sigma.(Sigma.mapping) [])
      (O, O).

  Lemma model_target_is_perm (column row : nat) :
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    model_target column row =
      Sigma.perm OrchardCompiled.orchard_sigma (column, row).
  Proof.
    intros Hcolumn Hrow.
    unfold model_target, Sigma.perm, Sigma.get2.
    apply List.nth_indep.
    rewrite model_mapping_row_length by exact Hcolumn.
    exact Hrow.
  Qed.

  Lemma model_target_bounds (column row : nat) :
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    (fst (model_target column row) < VkSigma.width_nat)%nat /\
    (snd (model_target column row) < VkSigma.rows_nat)%nat.
  Proof.
    intros Hcolumn Hrow.
    pose proof (sigma_of_copies_dom
      OrchardCompiledPinned.permutation_columns
      OrchardCompiled.orchard_n_rows
      OrchardCompiled.orchard_copies
      OrchardCompiled.orchard_sigma
      OrchardCompiled.orchard_sigma_eq
      (column, row)) as Hdom.
    assert (Hsource :
      cell_dom OrchardCompiledPinned.permutation_columns
        OrchardCompiled.orchard_n_rows (column, row)).
    { split; cbn [fst snd].
      - now rewrite permutation_columns_length.
      - now rewrite orchard_n_rows_exact. }
    specialize (Hdom Hsource).
    rewrite <- (model_target_is_perm column row Hcolumn Hrow) in Hdom.
    destruct Hdom as [Htarget_column Htarget_row].
    split.
    - now rewrite permutation_columns_length in Htarget_column.
    - now rewrite orchard_n_rows_exact in Htarget_row.
  Qed.

  Lemma matrix_size_fits :
    ArrayLinear.fits_nat (VkSigma.width_nat * VkSigma.rows_nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma index_mul (left right : nat) :
    ArrayLinear.fits_nat left ->
    ArrayLinear.fits_nat right ->
    ArrayLinear.fits_nat (left * right) ->
    PrimInt63.mul (ArrayLinear.index left) (ArrayLinear.index right) =
      ArrayLinear.index (left * right).
  Proof.
    intros Hleft Hright Hfits.
    apply Uint63.to_Z_inj.
    rewrite Uint63.mul_spec.
    rewrite (ArrayLinear.to_Z_index left Hleft),
      (ArrayLinear.to_Z_index right Hright),
      (ArrayLinear.to_Z_index (left * right) Hfits).
    rewrite Nat2Z.inj_mul, Z.mod_small; [reflexivity |].
    unfold ArrayLinear.fits_nat, ArrayLinear.word_capacity in Hfits.
    split; lia.
  Qed.

  Lemma rows_as_index :
    VkSigma.rows = ArrayLinear.index VkSigma.rows_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pack_cell_index (cell : Sigma.cell) :
    (fst cell < VkSigma.width_nat)%nat ->
    (snd cell < VkSigma.rows_nat)%nat ->
    VkSigma.pack_cell cell =
      ArrayLinear.index
        (fst cell * VkSigma.rows_nat + snd cell).
  Proof.
    intros Hcolumn Hrow.
    assert (Hproduct :
      ArrayLinear.fits_nat (fst cell * VkSigma.rows_nat)).
    { apply (ArrayLinear.fits_nat_lt
        (fst cell * VkSigma.rows_nat)
        (VkSigma.width_nat * VkSigma.rows_nat)); [nia |].
      exact matrix_size_fits. }
    assert (Hsum : ArrayLinear.fits_nat
      (fst cell * VkSigma.rows_nat + snd cell)).
    { apply (ArrayLinear.fits_nat_lt
        (fst cell * VkSigma.rows_nat + snd cell)
        (VkSigma.width_nat * VkSigma.rows_nat)); [nia |].
      exact matrix_size_fits. }
    assert (Hcolumn_fits : ArrayLinear.fits_nat (fst cell)).
    { apply (ArrayLinear.fits_nat_lt
        (fst cell) VkSigma.width_nat Hcolumn).
      vm_compute. reflexivity. }
    assert (Hrows_fits : ArrayLinear.fits_nat VkSigma.rows_nat).
    { vm_compute. reflexivity. }
    unfold VkSigma.pack_cell.
    rewrite rows_as_index,
      (index_mul _ _ Hcolumn_fits Hrows_fits Hproduct).
    rewrite ArrayLinear.index_add by exact Hsum.
    reflexivity.
  Qed.

  Lemma pack_cell_decode (cell : Sigma.cell) :
    (fst cell < VkSigma.width_nat)%nat ->
    (snd cell < VkSigma.rows_nat)%nat ->
    PrimInt63.div (VkSigma.pack_cell cell) VkSigma.rows =
      ArrayLinear.index (fst cell) /\
    PrimInt63.mod (VkSigma.pack_cell cell) VkSigma.rows =
      ArrayLinear.index (snd cell).
  Proof.
    intros Hcolumn Hrow.
    rewrite pack_cell_index by assumption.
    rewrite rows_as_index.
    assert (Hsum : ArrayLinear.fits_nat
      (fst cell * VkSigma.rows_nat + snd cell)).
    { apply (ArrayLinear.fits_nat_lt
        (fst cell * VkSigma.rows_nat + snd cell)
        (VkSigma.width_nat * VkSigma.rows_nat)); [nia |].
      exact matrix_size_fits. }
    assert (Hcolumn_fits : ArrayLinear.fits_nat (fst cell)).
    { apply (ArrayLinear.fits_nat_lt (fst cell)
        (VkSigma.width_nat * VkSigma.rows_nat)); [nia |].
      exact matrix_size_fits. }
    assert (Hrow_fits : ArrayLinear.fits_nat (snd cell)).
    { apply (ArrayLinear.fits_nat_lt (snd cell) VkSigma.rows_nat);
        [exact Hrow | exact ArrayLinear.vector_size_fits_word]. }
    assert (Hrows_fits : ArrayLinear.fits_nat VkSigma.rows_nat).
    { vm_compute. reflexivity. }
    split; apply Uint63.to_Z_inj.
    - rewrite Uint63.div_spec.
      rewrite (ArrayLinear.to_Z_index
          (fst cell * VkSigma.rows_nat + snd cell) Hsum),
        (ArrayLinear.to_Z_index VkSigma.rows_nat Hrows_fits),
        (ArrayLinear.to_Z_index (fst cell) Hcolumn_fits).
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
      replace
        ((Z.of_nat (fst cell) * Z.of_nat VkSigma.rows_nat +
          Z.of_nat (snd cell))%Z)
        with
        ((Z.of_nat (snd cell) +
          Z.of_nat (fst cell) * Z.of_nat VkSigma.rows_nat)%Z) by ring.
      rewrite Z.div_add by (unfold VkSigma.rows_nat; lia).
      rewrite Z.div_small; [lia |].
      unfold VkSigma.rows_nat in Hrow |- *.
      lia.
    - rewrite Uint63.mod_spec.
      rewrite (ArrayLinear.to_Z_index
          (fst cell * VkSigma.rows_nat + snd cell) Hsum),
        (ArrayLinear.to_Z_index VkSigma.rows_nat Hrows_fits),
        (ArrayLinear.to_Z_index (snd cell) Hrow_fits).
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
      replace
        ((Z.of_nat (fst cell) * Z.of_nat VkSigma.rows_nat +
          Z.of_nat (snd cell))%Z)
        with
        ((Z.of_nat (snd cell) +
          Z.of_nat (fst cell) * Z.of_nat VkSigma.rows_nat)%Z) by ring.
      rewrite Z.mod_add.
      apply Z.mod_small.
      unfold VkSigma.rows_nat in Hrow |- *.
      lia.
    all: unfold VkSigma.rows_nat in *; lia.
  Qed.

  Lemma model_column_get (column row : nat) :
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    PrimArray.get (VkSigma.model_column column)
      (ArrayLinear.index row) =
    VkSigma.pack_cell (model_target column row).
  Proof.
    intros Hcolumn Hrow.
    unfold VkSigma.model_column, model_target.
    eapply VkArrayOfListRefinement.array_of_list_get.
    - rewrite List.length_map, model_mapping_row_length by exact Hcolumn.
      exact ArrayLinear.vector_size_fits_word.
    - rewrite List.length_map, model_mapping_row_length by exact Hcolumn.
      exact ArrayLinear.vector_size_fits_array.
    - rewrite (List.nth_error_nth'
        (List.map VkSigma.pack_cell
          (List.nth column OrchardCompiled.orchard_sigma.(Sigma.mapping) []))
        (n := row) (VkSigma.pack_cell (O, O))).
      + rewrite List.map_nth. reflexivity.
      + rewrite List.length_map,
          model_mapping_row_length by exact Hcolumn.
        exact Hrow.
  Qed.

  Theorem packed_target_refines_model (column row : nat) :
    VkSigma.column_check column = true ->
    (column < VkSigma.width_nat)%nat ->
    (row < VkSigma.rows_nat)%nat ->
    VkSigma.packed_target column row =
      VkSigma.pack_cell (model_target column row).
  Proof.
    intros Hcheck Hcolumn Hrow.
    unfold VkSigma.packed_target.
    rewrite (column_check_pointwise column Hcheck row Hrow).
    now apply model_column_get.
  Qed.
End VkSigmaRefinement.
