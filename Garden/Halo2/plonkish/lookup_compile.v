(** * Lookup compilation correctness: substituted lookup inputs keep values.

    [Compile.compile] ([plonkish/main.v]) substitutes the selector
    replacement expressions into every lookup input expression, exactly as
    into the gate polynomials ([compile_lookups_substituted] below is the
    lookup twin of [compile_gates_substituted]).  Gate satisfaction only
    needs the zero set of each polynomial, so an indicator substitution may
    rescale by a nonzero factor ([substitute_selectors_eval]); a lookup
    input instead feeds its exact value to the table-membership predicate
    [eval_lookup_argument], so the lookup substitution must preserve
    values.  It does, because every selector occurring in a lookup input is
    complex: its replacement is a plain 0/1 fixed-column query, whose value
    through the combination view equals the selector value at every domain
    row.  That exactness is one decidable check over the compiled output
    ([lookup_replacements_exact_b], evaluated through the fixed-plane
    evaluator [eval_fixed_expression]), the value-level strengthening of
    [selector_assignments_ok_b].

    The statements relate two grids: the witness grid [grid], and a grid
    [cgrid] carrying the keygen-materialized combination fixed planes,
    which synthesis never writes.  [cgrid] is abstract, constrained by
    plane-agreement hypotheses (equal selector, advice and instance planes;
    fixed planes equal off an avoid list; combination view installed);
    [with_combination_planes] is the canonical instance, and the
    [_installed] corollaries discharge every plane hypothesis for it
    definitionally.  The avoid list enters through one decidable check
    ([lookup_columns_avoid_b]): no lookup input queries an avoided fixed
    column and no table column is avoided, so only the replacement leaves
    read the installed planes.

    Allocation independence: as in [compile_correct], no statement mentions
    which combination column a selector landed in — the hypotheses
    constrain the compiled output as a whole and hold for any allocation.

    The headline results:

    - [lookup_compile_correct]: on every domain row, the compiled
      (substituted) lookup arguments hold on [cgrid] exactly when the
      indexed selector-carrying lookup arguments hold on [grid] — the
      value-preserving lookup-substitution equivalence;
    - [plonkish_accepts_compiled] / [plonkish_accepts_compiled_iff]: the
      acceptance reading with the lookup conjunct restated over
      [CompiledSystem.lookups], equivalent to
      [PlonkishMock.plonkish_accepts] under the decidable side
      conditions. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.mock.
Require Import Garden.Halo2.plonkish.compile.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module PlonkishLookup.

Import Plonkish.

(** ** The compiled lookups are the substituted originals

    The lookup twin of [PlonkishCompile.compile_gates_substituted]: the
    compiled lookup arguments are exactly the indexed ones with the
    assignment replacement substituted into every input expression, the
    table columns untouched. *)

Definition substitute_lookup
    (replacement : Z -> option (Expression.t Configure.indexed_columns))
    (lookup : LookupArgument.t Configure.indexed_columns)
    : LookupArgument.t Configure.indexed_columns :=
  {|
    LookupArgument.pairs :=
      List.map
        (fun pair =>
          (substitute_selectors replacement (fst pair), snd pair))
        lookup.(LookupArgument.pairs);
  |}.

Lemma compile_lookups_substituted
    (system : ConstraintSystem.t Configure.indexed_columns)
    (infos : list Compile.SelectorInfo.t)
    (num_fixed_columns : Z)
    (permutation_columns : list Raw.ColumnRef.t)
    (constants : list Z) :
  (Compile.compile system infos num_fixed_columns permutation_columns
    constants).(CompiledSystem.lookups) =
  List.map
    (substitute_lookup
      (Compile.assignment_replacement
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.selector_assignments)))
    system.(ConstraintSystem.lookups).
Proof.
  unfold Compile.compile, Compile.assignment_replacement,
    substitute_lookup.
  cbv zeta.
  destruct (Compress.process _ _ _) as [combinations assignments].
  reflexivity.
Qed.

(** ** Decidable side conditions on the lookup arguments *)

(** No fixed query of the expression names a column of the avoid list. *)
Fixpoint expression_fixed_avoids_b (avoid : list Z)
    (expression : Expression.t Configure.indexed_columns) : bool :=
  match expression with
  | Expression.Constant _ => true
  | Expression.Selector _ => true
  | Expression.Fixed column _ => negb (List.existsb (Z.eqb column) avoid)
  | Expression.Advice _ _ => true
  | Expression.Instance_ _ _ => true
  | Expression.Negated expression => expression_fixed_avoids_b avoid expression
  | Expression.Sum lhs rhs =>
      andb (expression_fixed_avoids_b avoid lhs)
        (expression_fixed_avoids_b avoid rhs)
  | Expression.Product lhs rhs =>
      andb (expression_fixed_avoids_b avoid lhs)
        (expression_fixed_avoids_b avoid rhs)
  | Expression.Scaled expression _ => expression_fixed_avoids_b avoid expression
  end.

(** The selector indexes occurring in the lookup input expressions. *)
Definition lookup_selectors
    (system : ConstraintSystem.t Configure.indexed_columns) : list Z :=
  List.flat_map
    (fun lookup : LookupArgument.t Configure.indexed_columns =>
      List.flat_map
        (fun pair => PlonkishMock.expression_selectors (fst pair))
        lookup.(LookupArgument.pairs))
    system.(ConstraintSystem.lookups).

(** Every lookup input's fixed queries and every lookup table column stay
    off the avoid list — with the combination columns as the avoid list,
    installing the combination planes cannot change an original input
    value or a table read. *)
Definition lookup_columns_avoid_b (avoid : list Z)
    (system : ConstraintSystem.t Configure.indexed_columns) : bool :=
  List.forallb
    (fun lookup : LookupArgument.t Configure.indexed_columns =>
      List.forallb
        (fun pair =>
          andb
            (expression_fixed_avoids_b avoid (fst pair))
            (negb (List.existsb (Z.eqb (snd pair)) avoid)))
        lookup.(LookupArgument.pairs))
    system.(ConstraintSystem.lookups).

(** ** The grid with the combination fixed planes installed

    The canonical [cgrid]: the compiled combination values on the
    combination columns, every other cell — and the whole selector plane —
    read from the underlying grid. *)

Definition with_combination_planes (compiled : CompiledSystem.t)
    (grid : RawGrid.t) : RawGrid.t := {|
  RawGrid.cell := fun kind column row =>
    match kind with
    | Raw.ColumnKind.Fixed =>
        match PlonkishCompile.combination_view compiled column row with
        | Some value => value
        | None => grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row
        end
    | _ => grid.(RawGrid.cell) kind column row
    end;
  RawGrid.sel := grid.(RawGrid.sel);
|}.

Lemma with_combination_planes_view (compiled : CompiledSystem.t)
    (grid : RawGrid.t) :
  forall column row value : Z,
    PlonkishCompile.combination_view compiled column row = Some value ->
    (with_combination_planes compiled grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed column row = value.
Proof.
  intros column row value Hview.
  cbn [with_combination_planes RawGrid.cell].
  rewrite Hview.
  reflexivity.
Qed.

(** A defined combination view names a combination column. *)
Lemma column_values_in (columns : list Z) (values : list (list Z))
    (column : Z) (found : list Z) :
  PlonkishCompile.column_values columns values column = Some found ->
  List.In column columns.
Proof.
  revert values.
  induction columns as [| head columns IH]; intros values Hfound;
    cbn in Hfound; [discriminate |].
  destruct values as [| value values]; [discriminate |].
  destruct (head =? column) eqn:Hhead.
  - left.
    apply Z.eqb_eq in Hhead.
    exact Hhead.
  - right.
    exact (IH values Hfound).
Qed.

(** Off the combination columns the installed grid reads the original. *)
Lemma with_combination_planes_off (compiled : CompiledSystem.t)
    (grid : RawGrid.t) (column row : Z)
    (Hout : ~ List.In column compiled.(CompiledSystem.combination_columns)) :
  (with_combination_planes compiled grid).(RawGrid.cell)
    Raw.ColumnKind.Fixed column row =
  grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row.
Proof.
  cbn [with_combination_planes RawGrid.cell].
  destruct (PlonkishCompile.combination_view compiled column row)
    as [value |] eqn:Hview; [| reflexivity].
  exfalso.
  apply Hout.
  unfold PlonkishCompile.combination_view in Hview.
  destruct
    (PlonkishCompile.column_values
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments) column)
    as [values |] eqn:Hvalues; [| discriminate].
  exact (column_values_in _ _ _ _ Hvalues).
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** The replacement-exactness check

      For every selector occurring in a lookup input: if the compilation
      replaced it, the replacement expression evaluates through the view
      to exactly [1] on the selector's enabled rows and [0] elsewhere, at
      every domain row.  This is the value-level strengthening of
      [selector_assignments_ok_b] that value preservation needs; it holds
      of complex-selector replacements (plain 0/1 fixed-column queries)
      and is decidable on a concrete compiled output. *)

  Definition lookup_replacements_exact_b
      (view : Z -> Z -> option Z)
      (activations : Z -> list bool)
      (n_rows : nat)
      (assignments : list SelectorAssignment.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      : bool :=
    List.forallb
      (fun s =>
        match Compile.assignment_replacement assignments s with
        | Some e =>
            List.forallb
              (fun row =>
                match
                  PlonkishCompile.eval_fixed_expression (p := p) view
                    (Z.of_nat row) e
                with
                | Some value =>
                    value =?
                      (if List.nth row (activations s) false then 1 else 0)
                | None => false
                end)
              (List.seq 0 n_rows)
        | None => true
        end)
      (lookup_selectors system).

  (** ** Acceptance with the compiled lookup conjunct

      [PlonkishMock.plonkish_accepts] with the lookup conjunct restated
      over the compiled system: the substituted, selector-free lookup
      arguments of [CompiledSystem.lookups], evaluated on the grid with
      the combination planes installed.  The gate and copy conjuncts are
      unchanged. *)

  Definition plonkish_accepts_compiled
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (compiled : CompiledSystem.t)
      (events : list Raw.Event.t)
      (grid cgrid : RawGrid.t)
      (table_rows : Z) : Prop :=
    (forall row : Z,
      0 <= row < Domain.n domain ->
      eval_gates (grid_assignment grid) (tt, row)
        system.(ConstraintSystem.gates)) /\
    (forall row : Z,
      0 <= row < Domain.n domain ->
      List.Forall
        (eval_lookup_argument (grid_assignment cgrid) (tt, row) table_rows)
        compiled.(CompiledSystem.lookups)) /\
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) events ->
      raw_cell_read grid left = raw_cell_read grid right).

  Section TwoGrids.
    Variables grid cgrid : RawGrid.t.
    Variable avoid : list Z.

    Hypothesis Hsel_agree :
      forall column row : Z,
        cgrid.(RawGrid.sel) column row = grid.(RawGrid.sel) column row.
    Hypothesis Hadvice_agree :
      forall column row : Z,
        cgrid.(RawGrid.cell) Raw.ColumnKind.Advice column row =
        grid.(RawGrid.cell) Raw.ColumnKind.Advice column row.
    Hypothesis Hinstance_agree :
      forall column row : Z,
        cgrid.(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
        grid.(RawGrid.cell) Raw.ColumnKind.Instance_ column row.
    Hypothesis Hfixed_agree :
      forall column row : Z,
        ~ List.In column avoid ->
        cgrid.(RawGrid.cell) Raw.ColumnKind.Fixed column row =
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row.

    (** ** The value-preserving substitution lemma

        With every replaced selector's replacement evaluating on [cgrid]
        to the exact selector value on [grid], and every fixed query of
        the expression off the avoid list, substitution preserves the
        value — not merely the zero set. *)

    Lemma substitute_selectors_eval_value
        (replacement : Z -> option (Expression.t Configure.indexed_columns))
        (row : Z)
        (expression : Expression.t Configure.indexed_columns) :
      (forall (s : Z) (e : Expression.t Configure.indexed_columns),
        replacement s = Some e ->
        List.In s (PlonkishMock.expression_selectors expression) ->
        eval_expression (grid_assignment cgrid) (tt, row) e =
        eval_selector (grid_assignment grid) (tt, row) s) ->
      expression_fixed_avoids_b avoid expression = true ->
      eval_expression (grid_assignment cgrid) (tt, row)
        (substitute_selectors replacement expression) =
      eval_expression (grid_assignment grid) (tt, row) expression.
    Proof.
      induction expression as
        [ constant | selector | fixed rotation | advice rotation
        | instance rotation | expression IH | lhs IHl rhs IHr
        | lhs IHl rhs IHr | expression IH scale ];
        intros Hval Havoid; cbn [substitute_selectors].
      - (* Constant *)
        reflexivity.
      - (* Selector *)
        destruct (replacement selector) as [e |] eqn:Hrepl.
        + apply (Hval selector e Hrepl).
          left.
          reflexivity.
        + cbn [eval_expression].
          unfold eval_selector.
          cbn [grid_assignment Assignment.selector].
          rewrite Hsel_agree.
          reflexivity.
      - (* Fixed *)
        cbn [expression_fixed_avoids_b] in Havoid.
        apply Bool.negb_true_iff in Havoid.
        cbn [eval_expression grid_assignment Assignment.fixed].
        rewrite Hfixed_agree; [reflexivity |].
        intros Hin.
        assert (Hex : List.existsb (Z.eqb fixed) avoid = true).
        { apply List.existsb_exists.
          exists fixed.
          split; [exact Hin | apply Z.eqb_refl]. }
        congruence.
      - (* Advice *)
        cbn [eval_expression grid_assignment Assignment.advice].
        rewrite Hadvice_agree.
        reflexivity.
      - (* Instance_ *)
        cbn [eval_expression grid_assignment Assignment.instance_].
        rewrite Hinstance_agree.
        reflexivity.
      - (* Negated *)
        cbn [eval_expression].
        rewrite (IH Hval Havoid).
        reflexivity.
      - (* Sum *)
        cbn [expression_fixed_avoids_b] in Havoid.
        apply Bool.andb_true_iff in Havoid.
        destruct Havoid as [Havoid_l Havoid_r].
        assert (Hval_l : forall (s : Z)
            (e : Expression.t Configure.indexed_columns),
          replacement s = Some e ->
          List.In s (PlonkishMock.expression_selectors lhs) ->
          eval_expression (grid_assignment cgrid) (tt, row) e =
          eval_selector (grid_assignment grid) (tt, row) s).
        { intros s e Hrepl Hin.
          apply (Hval s e Hrepl).
          cbn [PlonkishMock.expression_selectors].
          apply List.in_or_app.
          left.
          exact Hin. }
        assert (Hval_r : forall (s : Z)
            (e : Expression.t Configure.indexed_columns),
          replacement s = Some e ->
          List.In s (PlonkishMock.expression_selectors rhs) ->
          eval_expression (grid_assignment cgrid) (tt, row) e =
          eval_selector (grid_assignment grid) (tt, row) s).
        { intros s e Hrepl Hin.
          apply (Hval s e Hrepl).
          cbn [PlonkishMock.expression_selectors].
          apply List.in_or_app.
          right.
          exact Hin. }
        rewrite !eval_expression_sum.
        rewrite (IHl Hval_l Havoid_l), (IHr Hval_r Havoid_r).
        reflexivity.
      - (* Product *)
        cbn [expression_fixed_avoids_b] in Havoid.
        apply Bool.andb_true_iff in Havoid.
        destruct Havoid as [Havoid_l Havoid_r].
        assert (Hval_l : forall (s : Z)
            (e : Expression.t Configure.indexed_columns),
          replacement s = Some e ->
          List.In s (PlonkishMock.expression_selectors lhs) ->
          eval_expression (grid_assignment cgrid) (tt, row) e =
          eval_selector (grid_assignment grid) (tt, row) s).
        { intros s e Hrepl Hin.
          apply (Hval s e Hrepl).
          cbn [PlonkishMock.expression_selectors].
          apply List.in_or_app.
          left.
          exact Hin. }
        assert (Hval_r : forall (s : Z)
            (e : Expression.t Configure.indexed_columns),
          replacement s = Some e ->
          List.In s (PlonkishMock.expression_selectors rhs) ->
          eval_expression (grid_assignment cgrid) (tt, row) e =
          eval_selector (grid_assignment grid) (tt, row) s).
        { intros s e Hrepl Hin.
          apply (Hval s e Hrepl).
          cbn [PlonkishMock.expression_selectors].
          apply List.in_or_app.
          right.
          exact Hin. }
        cbn [eval_expression].
        rewrite (IHl Hval_l Havoid_l), (IHr Hval_r Havoid_r).
        reflexivity.
      - (* Scaled *)
        cbn [eval_expression].
        rewrite (IH Hval Havoid).
        reflexivity.
    Qed.

    (** The exactness check delivers, at every covered row, the value
        facts the substitution lemma consumes: [cgrid] holds the view, the
        [grid] selector plane follows the activations, and the checked
        replacement reads back exactly the 0/1 selector value. *)
    Lemma lookup_replacements_exact_sound
        (view : Z -> Z -> option Z)
        (activations : Z -> list bool)
        (n_rows : nat)
        (assignments : list SelectorAssignment.t)
        (system : ConstraintSystem.t Configure.indexed_columns)
        (Hview : forall column row value : Z,
          view column row = Some value ->
          cgrid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
        (Hexact :
          lookup_replacements_exact_b view activations n_rows assignments
            system = true)
        (row : Z)
        (Hrow : 0 <= row < Z.of_nat n_rows)
        (Hact : forall s : Z,
          grid.(RawGrid.sel) s row =
          (if List.nth (Z.to_nat row) (activations s) false then 1 else 0))
        (s : Z)
        (e : Expression.t Configure.indexed_columns)
        (Hs : List.In s (lookup_selectors system))
        (Hrepl :
          Compile.assignment_replacement assignments s = Some e) :
      eval_expression (grid_assignment cgrid) (tt, row) e =
      eval_selector (grid_assignment grid) (tt, row) s.
    Proof.
      unfold lookup_replacements_exact_b in Hexact.
      rewrite List.forallb_forall in Hexact.
      specialize (Hexact _ Hs).
      cbv beta in Hexact.
      rewrite Hrepl in Hexact.
      cbv beta iota in Hexact.
      rewrite List.forallb_forall in Hexact.
      specialize (Hexact (Z.to_nat row)).
      assert (Hseq : List.In (Z.to_nat row) (List.seq 0 n_rows)).
      { apply List.in_seq.
        lia. }
      specialize (Hexact Hseq).
      cbv beta in Hexact.
      rewrite Z2Nat.id in Hexact by lia.
      destruct (PlonkishCompile.eval_fixed_expression view row e)
        as [value |] eqn:Heval; [| discriminate].
      apply Z.eqb_eq in Hexact.
      subst value.
      rewrite
        (PlonkishCompile.eval_fixed_expression_sound cgrid view Hview row e _
          Heval).
      unfold eval_selector.
      cbn [grid_assignment Assignment.selector].
      rewrite (Hact s).
      destruct (List.nth (Z.to_nat row) (activations s) false).
      - symmetry.
        apply FieldRewrite.from_one.
      - symmetry.
        apply FieldRewrite.from_zero.
    Qed.

    (** ** Per-argument equivalence

        With value-preserving inputs and an untouched table column, the
        substituted lookup argument on [cgrid] and the original on [grid]
        agree — the existential table-row witness carries across. *)

    Lemma substitute_lookup_argument_iff
        (replacement : Z -> option (Expression.t Configure.indexed_columns))
        (table_rows row : Z)
        (arg : LookupArgument.t Configure.indexed_columns)
        (Hinputs : forall pair,
          List.In pair arg.(LookupArgument.pairs) ->
          eval_expression (grid_assignment cgrid) (tt, row)
            (substitute_selectors replacement (fst pair)) =
          eval_expression (grid_assignment grid) (tt, row) (fst pair))
        (Htables : forall pair,
          List.In pair arg.(LookupArgument.pairs) ->
          ~ List.In (snd pair) avoid) :
      eval_lookup_argument (grid_assignment cgrid) (tt, row) table_rows
        (substitute_lookup replacement arg) <->
      eval_lookup_argument (grid_assignment grid) (tt, row) table_rows arg.
    Proof.
      unfold eval_lookup_argument.
      cbn [substitute_lookup LookupArgument.pairs].
      split;
        intros (table_row & Htable_row & Hforall);
        exists table_row;
        (split; [exact Htable_row |]);
        rewrite List.Forall_forall in Hforall |- *.
      - (* Substituted on [cgrid] to original on [grid]. *)
        intros [expression column] Hin.
        pose proof
          (Hforall _
            (List.in_map
              (fun pair =>
                (substitute_selectors replacement (fst pair), snd pair))
              arg.(LookupArgument.pairs) _ Hin)) as Hpair.
        cbn [fst snd grid_assignment Assignment.lookup] in Hpair.
        pose proof (Hinputs _ Hin) as Hval.
        cbn [fst] in Hval.
        pose proof (Htables _ Hin) as Htab.
        cbn [snd] in Htab.
        cbn [grid_assignment Assignment.lookup].
        rewrite <- Hval.
        rewrite <- (Hfixed_agree column table_row Htab).
        exact Hpair.
      - (* Original on [grid] to substituted on [cgrid]. *)
        intros pair' Hin'.
        apply List.in_map_iff in Hin'.
        destruct Hin' as (pair & Hpair' & Hin).
        subst pair'.
        destruct pair as [expression column].
        pose proof (Hforall _ Hin) as Hpair.
        cbn [grid_assignment Assignment.lookup] in Hpair.
        pose proof (Hinputs _ Hin) as Hval.
        cbn [fst] in Hval.
        pose proof (Htables _ Hin) as Htab.
        cbn [snd] in Htab.
        cbn [fst snd grid_assignment Assignment.lookup].
        rewrite Hval.
        rewrite (Hfixed_agree column table_row Htab).
        exact Hpair.
    Qed.

    (** ** The lookup-substitution equivalence

        On every domain row, the compiled lookup arguments hold on the
        installed grid exactly when the indexed selector-carrying ones
        hold on the witness grid.  The hypotheses mirror
        [compile_correct]: the compiled output as a whole (view,
        assignments), the selector-plane link [Hact], and the decidable
        exactness and avoid checks — nothing depends on the allocation. *)

    Theorem lookup_compile_correct
        (domain : Domain.t)
        (system : ConstraintSystem.t Configure.indexed_columns)
        (infos : list Compile.SelectorInfo.t)
        (num_fixed_columns : Z)
        (permutation_columns : list Raw.ColumnRef.t)
        (constants : list Z)
        (compiled : CompiledSystem.t)
        (table_rows : Z)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hview : forall column row value : Z,
          PlonkishCompile.combination_view compiled column row = Some value ->
          cgrid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
        (Hact : forall s row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s) false
           then 1 else 0))
        (Hexact :
          lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid : lookup_columns_avoid_b avoid system = true)
        (row : Z)
        (Hrow : 0 <= row < Domain.n domain) :
      List.Forall
        (eval_lookup_argument (grid_assignment cgrid) (tt, row) table_rows)
        compiled.(CompiledSystem.lookups) <->
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        system.(ConstraintSystem.lookups).
    Proof.
      pose proof
        (compile_lookups_substituted system infos num_fixed_columns
          permutation_columns constants) as Hlookups.
      rewrite <- Hcompiled in Hlookups.
      set (replacement :=
        Compile.assignment_replacement
          compiled.(CompiledSystem.selector_assignments)) in *.
      assert (Hrow' : 0 <= row < Z.of_nat (Z.to_nat (Domain.n domain))).
      { rewrite Z2Nat.id by lia.
        lia. }
      assert (Hargs : forall arg : LookupArgument.t Configure.indexed_columns,
        List.In arg system.(ConstraintSystem.lookups) ->
        (eval_lookup_argument (grid_assignment cgrid) (tt, row) table_rows
          (substitute_lookup replacement arg) <->
        eval_lookup_argument (grid_assignment grid) (tt, row) table_rows
          arg)).
      { intros arg Hargin.
        assert (Hpairs_avoid : forall pair,
          List.In pair arg.(LookupArgument.pairs) ->
          andb
            (expression_fixed_avoids_b avoid (fst pair))
            (negb (List.existsb (Z.eqb (snd pair)) avoid)) = true).
        { intros pair Hpairin.
          unfold lookup_columns_avoid_b in Hlookup_avoid.
          rewrite List.forallb_forall in Hlookup_avoid.
          specialize (Hlookup_avoid _ Hargin).
          cbv beta in Hlookup_avoid.
          rewrite List.forallb_forall in Hlookup_avoid.
          exact (Hlookup_avoid _ Hpairin). }
        apply substitute_lookup_argument_iff.
        - (* Value preservation of every input expression. *)
          intros pair Hpairin.
          pose proof (Hpairs_avoid _ Hpairin) as Hpa.
          apply Bool.andb_true_iff in Hpa.
          destruct Hpa as [Hexpr_avoid _].
          apply substitute_selectors_eval_value; [| exact Hexpr_avoid].
          intros s e Hrepl Hin.
          apply
            (lookup_replacements_exact_sound
              (PlonkishCompile.combination_view compiled)
              (PlonkishCompile.info_activations infos)
              (Z.to_nat (Domain.n domain))
              compiled.(CompiledSystem.selector_assignments)
              system Hview Hexact row Hrow'
              (fun s' => Hact s' row Hrow) s e).
          + (* The selector occurs in a lookup input. *)
            unfold lookup_selectors.
            apply List.in_flat_map.
            exists arg.
            split; [exact Hargin |].
            apply List.in_flat_map.
            exists pair.
            split; [exact Hpairin | exact Hin].
          + exact Hrepl.
        - (* The table column stays off the avoid list. *)
          intros pair Hpairin.
          pose proof (Hpairs_avoid _ Hpairin) as Hpa.
          apply Bool.andb_true_iff in Hpa.
          destruct Hpa as [_ Htab].
          apply Bool.negb_true_iff in Htab.
          intros Hin.
          assert (Hex : List.existsb (Z.eqb (snd pair)) avoid = true).
          { apply List.existsb_exists.
            exists (snd pair).
            split; [exact Hin | apply Z.eqb_refl]. }
          congruence. }
      rewrite Hlookups.
      split; intros HF.
      - rewrite List.Forall_forall in HF |- *.
        intros arg Hargin.
        exact
          (proj1 (Hargs arg Hargin)
            (HF _ (List.in_map (substitute_lookup replacement) _ _ Hargin))).
      - rewrite List.Forall_forall in HF |- *.
        intros carg Hin.
        apply List.in_map_iff in Hin.
        destruct Hin as (arg & Hcarg & Hargin).
        subst carg.
        exact (proj2 (Hargs arg Hargin) (HF _ Hargin)).
    Qed.

    (** ** Equivalence of the two acceptance readings

        The acceptance with the compiled lookup conjunct and
        [PlonkishMock.plonkish_accepts] coincide: the gate and copy
        conjuncts are shared, and the lookup conjuncts are equivalent by
        [lookup_compile_correct] at every domain row. *)

    Theorem plonkish_accepts_compiled_iff
        (domain : Domain.t)
        (system : ConstraintSystem.t Configure.indexed_columns)
        (infos : list Compile.SelectorInfo.t)
        (num_fixed_columns : Z)
        (permutation_columns : list Raw.ColumnRef.t)
        (constants : list Z)
        (compiled : CompiledSystem.t)
        (events : list Raw.Event.t)
        (table_rows : Z)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hview : forall column row value : Z,
          PlonkishCompile.combination_view compiled column row = Some value ->
          cgrid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
        (Hact : forall s row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s) false
           then 1 else 0))
        (Hexact :
          lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid : lookup_columns_avoid_b avoid system = true) :
      plonkish_accepts_compiled domain system compiled events grid cgrid
        table_rows <->
      PlonkishMock.plonkish_accepts domain system events grid table_rows.
    Proof.
      pose proof
        (fun row Hrow =>
          lookup_compile_correct domain system infos num_fixed_columns
            permutation_columns constants compiled table_rows Hcompiled
            Hview Hact Hexact Hlookup_avoid row Hrow) as Hlookup_iff.
      unfold plonkish_accepts_compiled, PlonkishMock.plonkish_accepts.
      split;
        intros (Hgates & Hlookups & Hcopies);
        refine (conj Hgates (conj _ Hcopies));
        intros row Hrow.
      - exact (proj1 (Hlookup_iff row Hrow) (Hlookups row Hrow)).
      - exact (proj2 (Hlookup_iff row Hrow) (Hlookups row Hrow)).
    Qed.

  End TwoGrids.

  (** ** The installed-grid corollaries

      [with_combination_planes] discharges every plane hypothesis
      definitionally, with the combination columns as the avoid list. *)

  Corollary lookup_compile_correct_installed
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (grid : RawGrid.t)
      (compiled : CompiledSystem.t)
      (table_rows : Z)
      (Hcompiled :
        compiled =
        Compile.compile system infos num_fixed_columns permutation_columns
          constants)
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row)
            (PlonkishCompile.info_activations infos s) false
         then 1 else 0))
      (Hexact :
        lookup_replacements_exact_b
          (PlonkishCompile.combination_view compiled)
          (PlonkishCompile.info_activations infos)
          (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments)
          system = true)
      (Hlookup_avoid :
        lookup_columns_avoid_b
          compiled.(CompiledSystem.combination_columns) system = true)
      (row : Z)
      (Hrow : 0 <= row < Domain.n domain) :
    List.Forall
      (eval_lookup_argument
        (grid_assignment (with_combination_planes compiled grid)) (tt, row)
        table_rows)
      compiled.(CompiledSystem.lookups) <->
    List.Forall
      (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
      system.(ConstraintSystem.lookups).
  Proof.
    apply
      (lookup_compile_correct grid (with_combination_planes compiled grid)
        compiled.(CompiledSystem.combination_columns)
        (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl)
        (with_combination_planes_off compiled grid)
        domain system infos num_fixed_columns permutation_columns constants
        compiled table_rows Hcompiled
        (with_combination_planes_view compiled grid)
        Hact Hexact Hlookup_avoid row Hrow).
  Qed.

  Corollary plonkish_accepts_compiled_installed_iff
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (grid : RawGrid.t)
      (compiled : CompiledSystem.t)
      (events : list Raw.Event.t)
      (table_rows : Z)
      (Hcompiled :
        compiled =
        Compile.compile system infos num_fixed_columns permutation_columns
          constants)
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row)
            (PlonkishCompile.info_activations infos s) false
         then 1 else 0))
      (Hexact :
        lookup_replacements_exact_b
          (PlonkishCompile.combination_view compiled)
          (PlonkishCompile.info_activations infos)
          (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments)
          system = true)
      (Hlookup_avoid :
        lookup_columns_avoid_b
          compiled.(CompiledSystem.combination_columns) system = true) :
    plonkish_accepts_compiled domain system compiled events grid
      (with_combination_planes compiled grid) table_rows <->
    PlonkishMock.plonkish_accepts domain system events grid table_rows.
  Proof.
    apply
      (plonkish_accepts_compiled_iff grid
        (with_combination_planes compiled grid)
        compiled.(CompiledSystem.combination_columns)
        (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl)
        (with_combination_planes_off compiled grid)
        domain system infos num_fixed_columns permutation_columns constants
        compiled events table_rows Hcompiled
        (with_combination_planes_view compiled grid)
        Hact Hexact Hlookup_avoid).
  Qed.

End WithPrime.

End PlonkishLookup.
