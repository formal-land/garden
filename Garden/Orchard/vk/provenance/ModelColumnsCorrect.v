(** * Correctness of the executable VK fixed-column image

    [ModelColumns.v] uses primitive arrays solely as an evaluator.  This
    file connects that evaluator to the ordinary [RawGrid] semantics used by
    the compiled-circuit theorems.  In particular, the proof never reasons
    by reduction about the concrete 19,679-event Orchard trace: it proves a
    generic simulation of every successful event replay. *)

From Corelib Require Import PrimArray ArrayAxioms.
From Stdlib Require Import ZArith Lists.List micromega.Lia.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.compile.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.provenance.ModelColumns.
Require Import Garden.Orchard.vk.provenance.CompressShape.
Require Import Garden.Orchard.vk.provenance.OrchardCompressShape.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module VkModelColumnsCorrect.

  Import VkModelColumns.

  (** Specializing the primitive-array axiom to [Z] once avoids an
      expensive universe/transparent-constant conversion at each use. *)
  Lemma get_make_Z (value : Z) (size index : PrimInt63.int) :
    PrimArray.get (PrimArray.make size value) index = value.
  Proof. exact (@ArrayAxioms.get_make Z value size index). Qed.

  (** Agreement is intentionally limited to the rectangle committed by
      keygen.  Writes outside it are ignored by the primitive evaluator and
      therefore cannot affect this relation. *)
  Definition fixed_agrees (array : PrimArray.array Z) (grid : RawGrid.t) : Prop :=
    forall column row : nat,
      (column < fixed_count_nat)%nat ->
      (row < rows_nat)%nat ->
      PrimArray.get array (flat_index column row) =
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed
          (Z.of_nat column) (Z.of_nat row).

  Definition represents (array : PrimArray.array Z) (state : ReplayState.t) : Prop :=
    PrimArray.length array = flat_size /\
    fixed_agrees array state.(ReplayState.grid).

  Lemma flat_offset_lt (column row : nat) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    (column * rows_nat + row < flat_size_nat)%nat.
  Proof.
    intros Hcolumn Hrow.
    assert (Hstep :
      (column * rows_nat + row < column * rows_nat + rows_nat)%nat).
    { apply Nat.add_lt_mono_l. exact Hrow. }
    eapply Nat.lt_le_trans; [exact Hstep |].
    rewrite <- Nat.mul_succ_l.
    unfold flat_size_nat.
    apply Nat.mul_le_mono_r.
    lia.
  Qed.

  Lemma flat_offset_fits (column row : nat) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    ArrayLinear.fits_nat (column * rows_nat + row).
  Proof.
    intros Hcolumn Hrow.
    eapply ArrayLinear.fits_nat_lt.
    - exact (flat_offset_lt column row Hcolumn Hrow).
    - exact flat_size_fits.
  Qed.

  Lemma flat_index_in_bounds (array : PrimArray.array Z) (column row : nat) :
    PrimArray.length array = flat_size ->
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    ArrayLinear.in_bounds array (flat_index column row).
  Proof.
    intros Hlength Hcolumn Hrow.
    unfold ArrayLinear.in_bounds, flat_index.
    rewrite Hlength.
    apply (proj2 (ArrayLinear.index_ltb_iff
      (column * rows_nat + row) flat_size_nat
      (flat_offset_fits column row Hcolumn Hrow) flat_size_fits)).
    exact (flat_offset_lt column row Hcolumn Hrow).
  Qed.

  Lemma flat_offset_injective
      (column row column' row' : nat) :
    (row < rows_nat)%nat ->
    (row' < rows_nat)%nat ->
    (column * rows_nat + row = column' * rows_nat + row')%nat ->
    column = column' /\ row = row'.
  Proof.
    unfold rows_nat.
    intros Hrow Hrow' Heq.
    nia.
  Qed.

  Lemma flat_index_injective
      (column row column' row' : nat) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    (column' < fixed_count_nat)%nat ->
    (row' < rows_nat)%nat ->
    flat_index column row = flat_index column' row' ->
    column = column' /\ row = row'.
  Proof.
    intros Hcolumn Hrow Hcolumn' Hrow' Hindex.
    unfold flat_index in Hindex.
    apply flat_offset_injective; try assumption.
    exact (ArrayLinear.index_inj _ _
      (flat_offset_fits column row Hcolumn Hrow)
      (flat_offset_fits column' row' Hcolumn' Hrow') Hindex).
  Qed.

  Lemma in_domain_spec (column row : Z) :
    in_domain column row = true <->
      0 <= column < Z.of_nat fixed_count_nat /\
      0 <= row < Z.of_nat rows_nat.
  Proof.
    unfold in_domain.
    rewrite !Bool.andb_true_iff.
    rewrite !Z.leb_le, !Z.ltb_lt.
    tauto.
  Qed.

  Lemma in_domain_of_nat (column row : nat) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    in_domain (Z.of_nat column) (Z.of_nat row) = true.
  Proof.
    intros Hcolumn Hrow.
    apply in_domain_spec.
    split; split; try lia.
  Qed.

  Lemma in_domain_to_nat_column (column row : Z) :
    in_domain column row = true ->
    (Z.to_nat column < fixed_count_nat)%nat.
  Proof.
    rewrite in_domain_spec.
    intros ((Hcolumn0 & Hcolumn) & _).
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by assumption.
    exact Hcolumn.
  Qed.

  Lemma in_domain_to_nat_row (column row : Z) :
    in_domain column row = true ->
    (Z.to_nat row < rows_nat)%nat.
  Proof.
    rewrite in_domain_spec.
    intros (_ & (Hrow0 & Hrow)).
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by assumption.
    exact Hrow.
  Qed.

  Lemma set_cell_length (array : PrimArray.array Z) (column row value : Z) :
    PrimArray.length (set_cell array column row value) =
      PrimArray.length array.
  Proof.
    unfold set_cell.
    destruct (in_domain column row);
      [exact (@ArrayAxioms.length_set Z array
        (flat_index (Z.to_nat column) (Z.to_nat row)) value)
      | reflexivity].
  Qed.

  Lemma set_cell_agrees (array : PrimArray.array Z) (grid : RawGrid.t)
      (column row value : Z) :
    PrimArray.length array = flat_size ->
    fixed_agrees array grid ->
    fixed_agrees (set_cell array column row value)
      (RawGrid.set_fixed grid column row value).
  Proof.
    intros Hlength Hagree query_column query_row Hquery_column Hquery_row.
    unfold set_cell.
    destruct (in_domain column row) eqn:Hdomain.
    - destruct
        (andb (Z.of_nat query_column =? column)
          (Z.of_nat query_row =? row)) eqn:Hsame.
      + apply Bool.andb_true_iff in Hsame.
        destruct Hsame as [Hcolumn Hrow].
        apply Z.eqb_eq in Hcolumn, Hrow.
        subst column row.
        rewrite !Nat2Z.id.
        transitivity value.
        * exact (@ArrayAxioms.get_set_same Z array
            (flat_index query_column query_row) value
            (flat_index_in_bounds array query_column query_row
              Hlength Hquery_column Hquery_row)).
        * cbn [RawGrid.set_fixed RawGrid.cell].
          rewrite !Z.eqb_refl.
          reflexivity.
      + transitivity (PrimArray.get array (flat_index query_column query_row)).
        * apply (@ArrayAxioms.get_set_other Z array
            (flat_index (Z.to_nat column) (Z.to_nat row))
            (flat_index query_column query_row) value).
          intros Hindex.
          assert (Hparts :
            Z.to_nat column = query_column /\ Z.to_nat row = query_row).
          { apply flat_index_injective in Hindex.
            - tauto.
            - exact (in_domain_to_nat_column _ _ Hdomain).
            - exact (in_domain_to_nat_row _ _ Hdomain).
            - exact Hquery_column.
            - exact Hquery_row. }
          destruct Hparts as [Hcolumn Hrow].
          apply Bool.andb_false_iff in Hsame.
          destruct Hsame as [Hneq | Hneq].
          -- apply Z.eqb_neq in Hneq.
             apply Hneq.
             rewrite <- Hcolumn, Z2Nat.id.
             ++ reflexivity.
             ++ apply in_domain_spec in Hdomain; lia.
          -- apply Z.eqb_neq in Hneq.
             apply Hneq.
             rewrite <- Hrow, Z2Nat.id.
             ++ reflexivity.
             ++ apply in_domain_spec in Hdomain; lia.
        * cbn [RawGrid.set_fixed RawGrid.cell].
          rewrite Hsame.
          exact (Hagree query_column query_row Hquery_column Hquery_row).
    - cbn [RawGrid.set_fixed RawGrid.cell].
      destruct
        (andb (Z.of_nat query_column =? column)
          (Z.of_nat query_row =? row)) eqn:Hsame.
      + apply Bool.andb_true_iff in Hsame.
        destruct Hsame as [Hcolumn Hrow].
        apply Z.eqb_eq in Hcolumn, Hrow.
        subst column row.
        rewrite in_domain_of_nat in Hdomain by assumption.
        discriminate.
      + exact (Hagree query_column query_row Hquery_column Hquery_row).
  Qed.

  Lemma set_cell_represents (array : PrimArray.array Z) (state : ReplayState.t)
      (column row value : Z) :
    represents array state ->
    represents (set_cell array column row value)
      {| ReplayState.grid :=
           RawGrid.set_fixed state.(ReplayState.grid) column row value;
         ReplayState.log := state.(ReplayState.log) |}.
  Proof.
    intros [Hlength Hagree].
    split.
    - rewrite set_cell_length. exact Hlength.
    - apply set_cell_agrees; assumption.
  Qed.

  (** A functional-grid counterpart of [fill_cells].  This helper is used
      only in the proof: both recursions perform the same sequence of point
      writes, which is then identified with [RawGrid.fill_fixed]. *)
  Fixpoint fill_grid_cells (fuel : nat) (grid : RawGrid.t)
      (column row value : Z) : RawGrid.t :=
    match fuel with
    | O => grid
    | S fuel =>
        fill_grid_cells fuel (RawGrid.set_fixed grid column row value)
          column (row + 1) value
    end.

  Lemma fill_cells_length (fuel : nat) (array : PrimArray.array Z)
      (column row value : Z) :
    PrimArray.length (fill_cells fuel array column row value) =
      PrimArray.length array.
  Proof.
    revert array row.
    induction fuel as [| fuel IH]; intros array row; cbn [fill_cells].
    - reflexivity.
    - rewrite IH, set_cell_length.
      reflexivity.
  Qed.

  Lemma fill_cells_agrees_grid (fuel : nat) (array : PrimArray.array Z)
      (grid : RawGrid.t) (column row value : Z) :
    PrimArray.length array = flat_size ->
    fixed_agrees array grid ->
    fixed_agrees (fill_cells fuel array column row value)
      (fill_grid_cells fuel grid column row value).
  Proof.
    revert array grid row.
    induction fuel as [| fuel IH]; intros array grid row Hlength Hagree;
      cbn [fill_cells fill_grid_cells].
    - exact Hagree.
    - apply IH.
      + rewrite set_cell_length. exact Hlength.
      + apply set_cell_agrees; assumption.
  Qed.

  Definition fill_test (column row : Z) (fuel : nat)
      (query_column query_row : Z) : bool :=
    (query_column =? column) &&
      ((row <=? query_row) &&
        (query_row <? row + Z.of_nat fuel)).

  Lemma fill_test_spec (column row : Z) (fuel : nat)
      (query_column query_row : Z) :
    fill_test column row fuel query_column query_row = true <->
      query_column = column /\
      row <= query_row < row + Z.of_nat fuel.
  Proof.
    unfold fill_test.
    rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt.
    tauto.
  Qed.

  Lemma fill_test_succ (column row : Z) (fuel : nat)
      (query_column query_row : Z) :
    fill_test column row (S fuel) query_column query_row =
      orb
        (fill_test column (row + 1) fuel query_column query_row)
        (andb (query_column =? column) (query_row =? row)).
  Proof.
    apply Bool.eq_true_iff_eq.
    rewrite fill_test_spec, Bool.orb_true_iff, fill_test_spec.
    rewrite Bool.andb_true_iff, !Z.eqb_eq, Nat2Z.inj_succ.
    lia.
  Qed.

  Lemma fill_grid_cells_read (fuel : nat) (grid : RawGrid.t)
      (column row value query_column query_row : Z) :
    (fill_grid_cells fuel grid column row value).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column query_row =
    if fill_test column row fuel query_column query_row
    then value
    else grid.(RawGrid.cell) Raw.ColumnKind.Fixed query_column query_row.
  Proof.
    revert grid row.
    induction fuel as [| fuel IH]; intros grid row.
    - cbn [fill_grid_cells].
      assert (Hempty :
        fill_test column row O query_column query_row = false).
      { apply Bool.not_true_is_false.
        rewrite fill_test_spec.
        lia. }
      rewrite Hempty.
      reflexivity.
    - cbn [fill_grid_cells].
      rewrite IH.
      cbn [RawGrid.set_fixed RawGrid.cell].
      rewrite fill_test_succ.
      destruct
        (fill_test column (row + 1) fuel query_column query_row),
        (andb (query_column =? column) (query_row =? row));
        reflexivity.
  Qed.

  Lemma fill_fuel_interval (from_row to_row : Z) :
    from_row <= to_row ->
    from_row + Z.of_nat (Z.to_nat (Z.max 0 (to_row - from_row))) =
      to_row.
  Proof.
    intros Hle.
    rewrite Z.max_r by lia.
    rewrite Z2Nat.id by lia.
    lia.
  Qed.

  Lemma fill_fuel_empty (from_row to_row : Z) :
    to_row < from_row ->
    Z.to_nat (Z.max 0 (to_row - from_row)) = O.
  Proof.
    intros Hlt.
    rewrite Z.max_l by lia.
    reflexivity.
  Qed.

  Lemma fill_grid_cells_is_fill (grid : RawGrid.t)
      (column from_row to_row value query_column query_row : Z) :
    (fill_grid_cells
      (Z.to_nat (Z.max 0 (to_row - from_row)))
      grid column from_row value).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column query_row =
    (RawGrid.fill_fixed grid column from_row to_row value).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column query_row.
  Proof.
    rewrite fill_grid_cells_read.
    cbn [RawGrid.fill_fixed RawGrid.cell].
    destruct (Z_le_gt_dec from_row to_row) as [Hle | Hgt].
    - unfold fill_test.
      rewrite (fill_fuel_interval from_row to_row Hle).
      reflexivity.
    - assert (Hempty : to_row < from_row) by lia.
      rewrite (fill_fuel_empty from_row to_row Hempty).
      assert (Htest : fill_test column from_row O
        query_column query_row = false).
      { apply Bool.not_true_is_false.
        rewrite fill_test_spec.
        lia. }
      rewrite Htest.
      destruct (query_column =? column); cbn.
      + destruct (from_row <=? query_row) eqn:Hfrom; cbn.
        * apply Z.leb_le in Hfrom.
          assert (Hto : (query_row <? to_row) = false).
          { apply Z.ltb_ge. lia. }
          rewrite Hto.
          reflexivity.
        * reflexivity.
      + reflexivity.
  Qed.

  Lemma fill_cells_agrees (array : PrimArray.array Z) (grid : RawGrid.t)
      (column from_row to_row value : Z) :
    PrimArray.length array = flat_size ->
    fixed_agrees array grid ->
    fixed_agrees
      (fill_cells (Z.to_nat (Z.max 0 (to_row - from_row)))
        array column from_row value)
      (RawGrid.fill_fixed grid column from_row to_row value).
  Proof.
    intros Hlength Hagree query_column query_row
      Hquery_column Hquery_row.
    rewrite <- fill_grid_cells_is_fill.
    apply (fill_cells_agrees_grid _ _ _ _ _ _ Hlength Hagree);
      assumption.
  Qed.

  Lemma apply_event_represents (array : PrimArray.array Z)
      (state state' : ReplayState.t) (event : Raw.Event.t) :
    Garden.Halo2.realize.main.apply_event state event = Some state' ->
    represents array state ->
    represents (VkModelColumns.apply_event array event) state'.
  Proof.
    intros Happly [Hlength Hagree].
    destruct event as
      [name | name | name | name | column row annotation
      | column row annotation value | left right
      | column from_row to_row value];
      cbn [Garden.Halo2.realize.main.apply_event
        VkModelColumns.apply_event] in Happly |- *.
    - inversion Happly; subst. split; assumption.
    - inversion Happly; subst. split; assumption.
    - inversion Happly; subst. split; assumption.
    - inversion Happly; subst. split; assumption.
    - destruct
        (List.existsb (write_conflicts_write column row 1)
          state.(ReplayState.log).(Log.selectors)) eqn:Hconflict;
        [discriminate |].
      inversion Happly; subst state'; clear Happly.
      split; [exact Hlength |].
      intros query_column query_row Hquery_column Hquery_row.
      cbn [RawGrid.set_selector RawGrid.cell].
      exact (Hagree query_column query_row
        Hquery_column Hquery_row).
    - destruct
        (orb
          (List.existsb (write_conflicts_write column row value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (write_conflicts_fill column row value)
            state.(ReplayState.log).(Log.fills))) eqn:Hconflict;
        [discriminate |].
      inversion Happly; subst state'; clear Happly.
      apply set_cell_represents.
      split; assumption.
    - inversion Happly; subst. split; assumption.
    - destruct
        (orb
          (List.existsb
            (fill_conflicts_write column from_row to_row value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb
            (fill_conflicts_fill column from_row to_row value)
            state.(ReplayState.log).(Log.fills))) eqn:Hconflict;
        [discriminate |].
      inversion Happly; subst state'; clear Happly.
      split.
      + rewrite fill_cells_length. exact Hlength.
      + apply fill_cells_agrees; assumption.
  Qed.

  Theorem apply_events_represents (events : list Raw.Event.t)
      (array : PrimArray.array Z) (state state' : ReplayState.t) :
    apply_events_log events state = Some state' ->
    represents array state ->
    represents (VkModelColumns.apply_events events array) state'.
  Proof.
    revert array state state'.
    induction events as [| event events IH];
      intros array state state' Happly Hrep;
      cbn [apply_events_log VkModelColumns.apply_events] in Happly |- *.
    - inversion Happly; subst. exact Hrep.
    - destruct (Garden.Halo2.realize.main.apply_event state event)
        as [state1 |] eqn:Hevent;
        [| discriminate].
      exact (IH _ _ _ Happly
        (apply_event_represents _ _ _ _ Hevent Hrep)).
  Qed.

  Lemma zero_represents_initial (advice instance_ : Z -> Z -> Z) :
    represents zero (ReplayState.init (initial_grid advice instance_)).
  Proof.
    split.
    - exact zero_length.
    - intros column row Hcolumn Hrow.
      unfold zero.
      transitivity 0.
      + apply get_make_Z.
      + reflexivity.
  Qed.

  Lemma apply_events_match_grid (events : list Raw.Event.t)
      (array : PrimArray.array Z) (initial grid : RawGrid.t) :
    represents array (ReplayState.init initial) ->
    Garden.Halo2.realize.main.apply_events events initial = Some grid ->
    PrimArray.length (VkModelColumns.apply_events events array) = flat_size /\
    fixed_agrees (VkModelColumns.apply_events events array) grid.
  Proof.
    intros Hinitial.
    unfold Garden.Halo2.realize.main.apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hlog; [| discriminate].
    intros Hgrid.
    inversion Hgrid; subst grid.
    exact (apply_events_represents events array _ state Hlog Hinitial).
  Qed.

  Lemma base_columns_unfold :
    base_columns = VkModelColumns.apply_events orchard_events zero.
  Proof. reflexivity. Qed.

  Theorem base_columns_represents (advice instance_ : Z -> Z -> Z)
      (state : ReplayState.t) :
    apply_events_log orchard_events
      (ReplayState.init (initial_grid advice instance_)) = Some state ->
    represents base_columns state.
  Proof.
    intros Hreplay.
    exact (apply_events_represents orchard_events zero
      (ReplayState.init (initial_grid advice instance_)) state
      Hreplay (zero_represents_initial advice instance_)).
  Qed.

  Theorem base_columns_match_replay (advice instance_ : Z -> Z -> Z)
      (grid : RawGrid.t) :
    Garden.Halo2.realize.main.apply_events orchard_events
      (initial_grid advice instance_) = Some grid ->
    PrimArray.length base_columns = flat_size /\
    fixed_agrees base_columns grid.
  Proof.
    rewrite base_columns_unfold.
    intros Hreplay.
    exact (apply_events_match_grid orchard_events zero
      (initial_grid advice instance_) grid
      (zero_represents_initial advice instance_) Hreplay).
  Qed.

  (** ** Combination-column installation *)

  Lemma set_cell_of_nat (array : PrimArray.array Z)
      (column row : nat) (value : Z) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    set_cell array (Z.of_nat column) (Z.of_nat row) value =
      PrimArray.set array (flat_index column row) value.
  Proof.
    intros Hcolumn Hrow.
    unfold set_cell.
    rewrite in_domain_of_nat by assumption.
    rewrite !Nat2Z.id.
    reflexivity.
  Qed.

  Fixpoint install_column_grid (values : list Z) (column row : nat)
      (grid : RawGrid.t) : RawGrid.t :=
    match values with
    | [] => grid
    | value :: values =>
        install_column_grid values column (S row)
          (RawGrid.set_fixed grid (Z.of_nat column) (Z.of_nat row) value)
    end.

  Fixpoint install_combinations_grid (column_ids : list Z)
      (columns : list (list Z)) (grid : RawGrid.t) : RawGrid.t :=
    match column_ids, columns with
    | column :: column_ids, values :: columns =>
        install_column_grid values (Z.to_nat column) O
          (install_combinations_grid column_ids columns grid)
    | _, _ => grid
    end.

  Lemma install_column_length (values : list Z) (column row : nat)
      (array : PrimArray.array Z) :
    PrimArray.length (install_column values column row array) =
      PrimArray.length array.
  Proof.
    revert row array.
    induction values as [| value values IH]; intros row array;
      cbn [install_column].
    - reflexivity.
    - rewrite IH.
      exact (@ArrayAxioms.length_set Z array
        (flat_index column row) value).
  Qed.

  Lemma install_column_agrees (values : list Z) (column row : nat)
      (array : PrimArray.array Z) (grid : RawGrid.t) :
    PrimArray.length array = flat_size ->
    fixed_agrees array grid ->
    (column < fixed_count_nat)%nat ->
    (row + List.length values <= rows_nat)%nat ->
    fixed_agrees (install_column values column row array)
      (install_column_grid values column row grid).
  Proof.
    revert row array grid.
    induction values as [| value values IH];
      intros row array grid Hlength Hagree Hcolumn Hrows;
      cbn [install_column install_column_grid].
    - exact Hagree.
    - apply IH.
      + etransitivity.
        * exact (@ArrayAxioms.length_set Z array
            (flat_index column row) value).
        * exact Hlength.
      + assert (Hrow : (row < rows_nat)%nat).
        { cbn in Hrows. lia. }
        rewrite <- (set_cell_of_nat array column row value Hcolumn Hrow).
        apply set_cell_agrees; assumption.
      + exact Hcolumn.
      + cbn in Hrows. lia.
  Qed.

  Lemma install_combinations_length (column_ids : list Z)
      (columns : list (list Z)) (array : PrimArray.array Z) :
    PrimArray.length (install_combinations column_ids columns array) =
      PrimArray.length array.
  Proof.
    revert columns array.
    induction column_ids as [| column column_ids IH];
      intros [| values columns] array;
      cbn [install_combinations]; try reflexivity.
    rewrite install_column_length, IH.
    reflexivity.
  Qed.

  Lemma install_combinations_agrees
      (column_ids : list Z) (columns : list (list Z))
      (array : PrimArray.array Z) (grid : RawGrid.t) :
    PrimArray.length array = flat_size ->
    fixed_agrees array grid ->
    List.length column_ids = List.length columns ->
    List.Forall
      (fun column => 0 <= column < Z.of_nat fixed_count_nat) column_ids ->
    List.Forall
      (fun values => List.length values = rows_nat) columns ->
    fixed_agrees (install_combinations column_ids columns array)
      (install_combinations_grid column_ids columns grid).
  Proof.
    revert columns array grid.
    induction column_ids as [| column column_ids IH];
      intros [| values columns] array grid Hlength Hagree Hsame
        Hcolumn_ids Hcolumns; cbn in Hsame;
      try discriminate; cbn [install_combinations install_combinations_grid].
    - exact Hagree.
    - inversion Hcolumn_ids as [| ? ? Hcolumn Hcolumn_ids']; subst.
      inversion Hcolumns as [| ? ? Hvalues Hcolumns']; subst.
      apply install_column_agrees.
      + rewrite install_combinations_length. exact Hlength.
      + apply IH; try assumption.
        exact (Nat.succ_inj _ _ Hsame).
      + apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia.
        exact (proj2 Hcolumn).
      + rewrite Hvalues. lia.
  Qed.

  Lemma install_column_grid_other (values : list Z) (column row : nat)
      (grid : RawGrid.t) (query_column query_row : Z) :
    query_column <> Z.of_nat column ->
    (install_column_grid values column row grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column query_row =
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed query_column query_row.
  Proof.
    revert row grid.
    induction values as [| value values IH]; intros row grid Hneq;
      cbn [install_column_grid].
    - reflexivity.
    - rewrite IH by exact Hneq.
      cbn [RawGrid.set_fixed RawGrid.cell].
      assert (Hcolumn : (query_column =? Z.of_nat column) = false).
      { apply Z.eqb_neq. exact Hneq. }
      rewrite Hcolumn.
      reflexivity.
  Qed.

  Lemma install_column_grid_before (values : list Z) (column row : nat)
      (grid : RawGrid.t) (query_column query_row : Z) :
    query_row < Z.of_nat row ->
    (install_column_grid values column row grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column query_row =
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed query_column query_row.
  Proof.
    revert row grid.
    induction values as [| value values IH]; intros row grid Hbefore;
      cbn [install_column_grid].
    - reflexivity.
    - rewrite IH by (rewrite Nat2Z.inj_succ; lia).
      cbn [RawGrid.set_fixed RawGrid.cell].
      destruct (query_column =? Z.of_nat column); cbn.
      + assert (Hrow : (query_row =? Z.of_nat row) = false).
        { apply Z.eqb_neq. lia. }
        rewrite Hrow. reflexivity.
      + reflexivity.
  Qed.

  Lemma install_column_grid_nth (values : list Z) (column row offset : nat)
      (grid : RawGrid.t) (value : Z) :
    List.nth_error values offset = Some value ->
    (install_column_grid values column row grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed (Z.of_nat column) (Z.of_nat (row + offset)) =
    value.
  Proof.
    revert row offset grid.
    induction values as [| head values IH].
    - intros row offset grid Hnth.
      destruct offset; discriminate.
    - intros row [| offset] grid Hnth; cbn in Hnth.
      + inversion Hnth; subst head.
      cbn [install_column_grid].
      rewrite install_column_grid_before.
      + cbn [RawGrid.set_fixed RawGrid.cell].
        replace (row + 0)%nat with row by lia.
        rewrite !Z.eqb_refl.
        reflexivity.
      + rewrite Nat2Z.inj_succ.
        lia.
      + cbn [install_column_grid].
        replace (row + S offset)%nat with (S row + offset)%nat by lia.
        exact (IH (S row) offset
          (RawGrid.set_fixed grid (Z.of_nat column) (Z.of_nat row) head)
          Hnth).
  Qed.

  Lemma column_values_length (column_ids : list Z)
      (columns : list (list Z)) (query_column : Z) (values : list Z) :
    List.Forall (fun values => List.length values = rows_nat) columns ->
    PlonkishCompile.column_values column_ids columns query_column =
      Some values ->
    List.length values = rows_nat.
  Proof.
    revert columns.
    induction column_ids as [| column column_ids IH];
      intros [| head columns] Hcolumns Hfound;
      cbn [PlonkishCompile.column_values] in Hfound; try discriminate.
    inversion Hcolumns as [| ? ? Hhead Hcolumns']; subst.
    destruct (column =? query_column); [congruence |].
    exact (IH columns Hcolumns' Hfound).
  Qed.

  (** The opaque compiled-system argument exposes the fixed cell read without
      asking conversion to normalize the whole concrete Orchard circuit
      through [with_combinations]. *)
  Lemma with_combinations_fixed_read (compiled : CompiledSystem.t)
      (grid : RawGrid.t) (column row : Z) :
    (OrchardCompiled.with_combinations compiled grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed column row =
    match
      PlonkishCompile.column_values
        compiled.(CompiledSystem.combination_columns)
        compiled.(CompiledSystem.combination_assignments) column
    with
    | Some values =>
        if andb (0 <=? row) (row <? Z.of_nat (List.length values))
        then List.nth (Z.to_nat row) values 0
        else grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row
    | None => grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row
    end.
  Proof.
    cbn [OrchardCompiled.with_combinations RawGrid.cell].
    unfold PlonkishCompile.combination_view.
    destruct (PlonkishCompile.column_values
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments) column)
      as [values |].
    - destruct ((0 <=? row) &&
        (row <? Z.of_nat (List.length values)))%bool; reflexivity.
    - reflexivity.
  Qed.

  Lemma install_combinations_grid_read
      (column_ids : list Z) (columns : list (list Z))
      (grid : RawGrid.t) (query_column : Z) (query_row : nat) :
    List.length column_ids = List.length columns ->
    List.Forall (fun column => 0 <= column) column_ids ->
    List.Forall (fun values => List.length values = rows_nat) columns ->
    (query_row < rows_nat)%nat ->
    (install_combinations_grid column_ids columns grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed query_column (Z.of_nat query_row) =
    match PlonkishCompile.column_values column_ids columns query_column with
    | Some values => List.nth query_row values 0
    | None =>
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed
          query_column (Z.of_nat query_row)
    end.
  Proof.
    revert columns grid.
    induction column_ids as [| column column_ids IH];
      intros [| values columns] grid Hsame Hcolumn_ids Hcolumns Hrow;
      cbn in Hsame; try discriminate;
      cbn [install_combinations_grid PlonkishCompile.column_values].
    - reflexivity.
    - inversion Hcolumn_ids as [| ? ? Hcolumn Hcolumn_ids']; subst.
      inversion Hcolumns as [| ? ? Hvalues Hcolumns']; subst.
      destruct (column =? query_column) eqn:Hquery.
      + apply Z.eqb_eq in Hquery. subst column.
        rewrite <- (Z2Nat.id query_column Hcolumn) at 1.
        replace query_row with (O + query_row)%nat at 1 by lia.
        apply install_column_grid_nth.
        apply List.nth_error_nth'.
        rewrite Hvalues.
        exact Hrow.
      + rewrite install_column_grid_other.
        * apply IH; try assumption.
          exact (Nat.succ_inj _ _ Hsame).
        * apply Z.eqb_neq in Hquery.
          rewrite Z2Nat.id by exact Hcolumn.
          congruence.
  Qed.

  Lemma all_columns_unfold :
    all_columns = install_combinations combination_columns
      combination_assignments base_columns.
  Proof. reflexivity. Qed.

  (** These structural facts are symbolic consequences of
      [Compress.process], apart from the small closed certificate that its
      Orchard invocation produces exactly 15 column identifiers. *)
  Lemma orchard_combination_shape :
    List.length combination_columns =
      List.length combination_assignments /\
    List.Forall
      (fun column => 0 <= column < Z.of_nat fixed_count_nat)
      combination_columns /\
    List.Forall
      (fun values => List.length values = rows_nat)
      combination_assignments.
  Proof.
    split.
    - rewrite combination_columns_unfold, combination_assignments_unfold.
      exact OrchardCompressShape.orchard_combination_lengths.
    - split.
      + rewrite combination_columns_unfold.
        exact OrchardCompressShape.orchard_combination_columns_range.
      + rewrite combination_assignments_unfold.
        exact OrchardCompressShape.orchard_combination_values_rows.
  Qed.

  Lemma install_compiled_combinations_grid_read
      (compiled : CompiledSystem.t) (grid : RawGrid.t)
      (column : Z) (row : nat) :
    List.length compiled.(CompiledSystem.combination_columns) =
      List.length compiled.(CompiledSystem.combination_assignments) ->
    List.Forall (fun value => 0 <= value)
      compiled.(CompiledSystem.combination_columns) ->
    List.Forall (fun values => List.length values = rows_nat)
      compiled.(CompiledSystem.combination_assignments) ->
    (row < rows_nat)%nat ->
    (install_combinations_grid
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments) grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed column (Z.of_nat row) =
    (OrchardCompiled.with_combinations compiled grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed column (Z.of_nat row).
  Proof.
    intros Hsame Hcolumns Hvalues Hrow.
    rewrite (install_combinations_grid_read
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments)
      grid column row Hsame Hcolumns Hvalues Hrow).
    rewrite with_combinations_fixed_read.
    destruct (PlonkishCompile.column_values
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments) column)
      as [values |] eqn:Hfound; [| reflexivity].
    rewrite (column_values_length _ _ _ _ Hvalues Hfound).
    assert (Hrow0 : (0 <=? Z.of_nat row) = true).
    { apply Z.leb_le. lia. }
    assert (Hrowb :
      (Z.of_nat row <? Z.of_nat rows_nat) = true).
    { apply Z.ltb_lt. now apply Nat2Z.inj_lt. }
    rewrite Hrow0, Hrowb, Nat2Z.id.
    reflexivity.
  Qed.

  Lemma install_orchard_combinations_grid_read (grid : RawGrid.t)
      (column row : nat) :
    (column < fixed_count_nat)%nat ->
    (row < rows_nat)%nat ->
    (install_combinations_grid combination_columns
      combination_assignments grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed (Z.of_nat column) (Z.of_nat row) =
    (OrchardCompiled.with_combinations OrchardCompiledCheck.compiled grid)
      .(RawGrid.cell) Raw.ColumnKind.Fixed
      (Z.of_nat column) (Z.of_nat row).
  Proof.
    intros _ Hrow.
    destruct orchard_combination_shape as [Hsame [Hcolumns Hvalues]].
    rewrite combination_columns_unfold, combination_assignments_unfold.
    refine (install_compiled_combinations_grid_read
      OrchardCompiledCheck.compiled grid (Z.of_nat column) row _ _ _ Hrow).
    - rewrite <- combination_columns_unfold,
        <- combination_assignments_unfold.
      exact Hsame.
    - rewrite <- combination_columns_unfold.
      eapply List.Forall_impl; [| exact Hcolumns].
      intros value Hvalue. exact (proj1 Hvalue).
    - rewrite <- combination_assignments_unfold.
      exact Hvalues.
  Qed.

  (** The primitive fixed plane read by every inverse-FFT certificate is
      extensionally the fixed plane of the replayed Orchard grid after the
      model's compiled selector-combination columns have been installed. *)
  Theorem all_columns_match_compiled_grid
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) :
    Garden.Halo2.realize.main.apply_events orchard_events
      (initial_grid advice instance_) = Some grid ->
    PrimArray.length all_columns = flat_size /\
    fixed_agrees all_columns
      (OrchardCompiled.with_combinations
        OrchardCompiledCheck.compiled grid).
  Proof.
    intros Hreplay.
    destruct (base_columns_match_replay advice instance_ grid Hreplay)
      as [Hlength Hagree].
    destruct orchard_combination_shape as [Hsame [Hcolumns Hvalues]].
    assert (Hinstalled :
      fixed_agrees
        (install_combinations combination_columns
          combination_assignments base_columns)
        (install_combinations_grid combination_columns
          combination_assignments grid)).
    { apply install_combinations_agrees; try assumption. }
    split.
    - rewrite all_columns_unfold.
      rewrite install_combinations_length.
      exact Hlength.
    - rewrite all_columns_unfold.
      intros column row Hcolumn Hrow.
      transitivity
        ((install_combinations_grid
          combination_columns combination_assignments grid)
          .(RawGrid.cell) Raw.ColumnKind.Fixed
          (Z.of_nat column) (Z.of_nat row)).
      + exact (Hinstalled column row Hcolumn Hrow).
      + apply install_orchard_combinations_grid_read; assumption.
  Qed.

  Definition certificate : Prop :=
    forall (advice instance_ : Z -> Z -> Z),
      exists grid : RawGrid.t,
        Garden.Halo2.realize.main.apply_events orchard_events
          (initial_grid advice instance_) = Some grid /\
        PrimArray.length all_columns = flat_size /\
        fixed_agrees all_columns
          (OrchardCompiled.with_combinations
            OrchardCompiledCheck.compiled grid).

  Theorem checked : certificate.
  Proof.
    intros advice instance_.
    destruct (orchard_replay_some advice instance_) as [grid Hreplay].
    exists grid. split; [exact Hreplay |].
    exact (all_columns_match_compiled_grid advice instance_ grid Hreplay).
  Qed.

End VkModelColumnsCorrect.
