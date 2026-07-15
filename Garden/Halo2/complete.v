(** * Completeness introduction for [circuit_holds]

    Dual of the extraction bridges in [Garden.Halo2.proof]: an introduction
    lemma ([circuit_holds_intro]) reducing [circuit_holds] — whose gate and
    lookup components quantify over every [(region, row)] pair — to finitely
    many obligations, under an honest assignment:

    - the selector plane is the indicator of the synthesis-enabled points
      ([1] on them, [0] elsewhere), so a selector-guarded gate constraint is
      vacuous off the enabled points of its selector ([UnOp.from 0 = 0]);
    - the fixed plane carries the synthesis-written values with default [0],
      well defined under the [no_conflicting_writes] check (all writes to one
      cell agree, and at most one table load per lookup column);
    - the lookup plane is the loaded table contents, and on rows where every
      selector of a lookup argument evaluates to [0] the argument's
      expressions collapse to constants equal to table row [0]
      ([lookup_defaults_ok], via the partial evaluator
      [zero_selector_value]).

    The residual obligations are: the witness facts
    ([CellsEqual]/[InstanceIs]/[CellIsConstant]), one guarded-constraint
    instance per enabled point of its selector, and one lookup-argument
    instance per (enabled point, argument mentioning that selector) pair.
    The Boolean reflection layer ([check_constraint], [check_gates],
    [check_lookup_argument]) discharges these obligations by [vm_compute]
    for a computable assignment; [eval_expression] itself computes, so no
    separate expression checker is needed.

    The section is parameterized over Boolean equalities (with reflection
    facts) on the selector/fixed/lookup column enums and on [RegionId];
    chips instantiate them for their finite enums. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module Complete.

Fixpoint list_Z_eqb (values1 values2 : list Z) : bool :=
  match values1, values2 with
  | [], [] => true
  | value1 :: values1, value2 :: values2 =>
      Z.eqb value1 value2 && list_Z_eqb values1 values2
  | _, _ => false
  end.

Lemma list_Z_eqb_eq (values1 values2 : list Z) :
  list_Z_eqb values1 values2 = true ->
  values1 = values2.
Proof.
  revert values2.
  induction values1 as [| value1 values1 IH];
    intros [| value2 values2] Heq; cbn in Heq; try discriminate.
  - reflexivity.
  - apply Bool.andb_true_iff in Heq.
    destruct Heq as [Hvalue Hvalues].
    apply Z.eqb_eq in Hvalue.
    f_equal; [exact Hvalue | exact (IH _ Hvalues)].
Qed.

Section Completeness.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  Context
    (selector_eqb :
      columns.(Columns.Selector) -> columns.(Columns.Selector) -> bool)
    (selector_eqb_spec :
      forall selector1 selector2,
        selector_eqb selector1 selector2 = true <-> selector1 = selector2)
    (fixed_eqb :
      columns.(Columns.Fixed) -> columns.(Columns.Fixed) -> bool)
    (fixed_eqb_spec :
      forall column1 column2,
        fixed_eqb column1 column2 = true <-> column1 = column2)
    (lookup_eqb :
      columns.(Columns.Lookup) -> columns.(Columns.Lookup) -> bool)
    (lookup_eqb_spec :
      forall column1 column2,
        lookup_eqb column1 column2 = true <-> column1 = column2)
    (region_eqb : RegionId -> RegionId -> bool)
    (region_eqb_spec :
      forall region1 region2,
        region_eqb region1 region2 = true <-> region1 = region2).

  (** ** Fact-list extraction

      Plain filters over a reified fact list (typically
      [layouter_facts program]), one per fact family, plus membership
      functions built from the Boolean equalities. *)

  Fixpoint enabled_points (facts : list (Fact.t columns RegionId))
      : list (columns.(Columns.Selector) * RegionId * Z) :=
    match facts with
    | [] => []
    | Fact.SelectorOn selector region offset :: facts =>
        (selector, region, offset) :: enabled_points facts
    | _ :: facts => enabled_points facts
    end.

  Fixpoint fixed_writes (facts : list (Fact.t columns RegionId))
      : list (columns.(Columns.Fixed) * RegionId * Z * Z) :=
    match facts with
    | [] => []
    | Fact.FixedIs column region offset value :: facts =>
        (column, region, offset, value) :: fixed_writes facts
    | _ :: facts => fixed_writes facts
    end.

  Fixpoint table_entries (facts : list (Fact.t columns RegionId))
      : list (columns.(Columns.Lookup) * list Z * Z) :=
    match facts with
    | [] => []
    | Fact.LookupTableLoaded column values default_value :: facts =>
        (column, values, default_value) :: table_entries facts
    | _ :: facts => table_entries facts
    end.

  Definition is_witness_fact (fact : Fact.t columns RegionId) : bool :=
    match fact with
    | Fact.CellsEqual _ _ | Fact.InstanceIs _ _ _ | Fact.CellIsConstant _ _ =>
        true
    | _ => false
    end.

  (** The [CellsEqual]/[InstanceIs]/[CellIsConstant] sublist: the facts about
      the advice/instance planes, which stay abstract in the honest planes
      and are consumed as a single [interpret_facts] hypothesis. *)
  Definition witness_facts (facts : list (Fact.t columns RegionId))
      : list (Fact.t columns RegionId) :=
    List.filter is_witness_fact facts.

  Lemma enabled_points_In
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z) :
    List.In (Fact.SelectorOn selector region offset) facts ->
    List.In (selector, region, offset) (enabled_points facts).
  Proof.
    induction facts as [| fact facts IH]; intros Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst fact. cbn. left. reflexivity.
    - destruct fact; cbn; try exact (IH Hin).
      right. exact (IH Hin).
  Qed.

  Lemma fixed_writes_In
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Fixed))
      (region : RegionId) (offset value : Z) :
    List.In (Fact.FixedIs column region offset value) facts ->
    List.In (column, region, offset, value) (fixed_writes facts).
  Proof.
    induction facts as [| fact facts IH]; intros Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst fact. cbn. left. reflexivity.
    - destruct fact; cbn; try exact (IH Hin).
      right. exact (IH Hin).
  Qed.

  Lemma table_entries_In
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Lookup))
      (values : list Z) (default_value : Z) :
    List.In (Fact.LookupTableLoaded column values default_value) facts ->
    List.In (column, values, default_value) (table_entries facts).
  Proof.
    induction facts as [| fact facts IH]; intros Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst fact. cbn. left. reflexivity.
    - destruct fact; cbn; try exact (IH Hin).
      right. exact (IH Hin).
  Qed.

  Lemma witness_facts_In
      (facts : list (Fact.t columns RegionId))
      (fact : Fact.t columns RegionId) :
    List.In fact facts ->
    is_witness_fact fact = true ->
    List.In fact (witness_facts facts).
  Proof.
    intros Hin Hwitness.
    apply List.filter_In.
    split; assumption.
  Qed.

  Definition point_eqb
      (point1 point2 : columns.(Columns.Selector) * RegionId * Z) : bool :=
    let '(selector1, region1, offset1) := point1 in
    let '(selector2, region2, offset2) := point2 in
    selector_eqb selector1 selector2 &&
    region_eqb region1 region2 &&
    Z.eqb offset1 offset2.

  Lemma point_eqb_eq
      (point1 point2 : columns.(Columns.Selector) * RegionId * Z) :
    point_eqb point1 point2 = true ->
    point1 = point2.
  Proof.
    destruct point1 as [ [selector1 region1] offset1].
    destruct point2 as [ [selector2 region2] offset2].
    cbn.
    intros Heq.
    apply Bool.andb_true_iff in Heq.
    destruct Heq as [Heq Hoffset].
    apply Bool.andb_true_iff in Heq.
    destruct Heq as [Hselector Hregion].
    pose proof (proj1 (selector_eqb_spec _ _) Hselector).
    pose proof (proj1 (region_eqb_spec _ _) Hregion).
    apply Z.eqb_eq in Hoffset.
    subst.
    reflexivity.
  Qed.

  Lemma point_eqb_refl
      (point : columns.(Columns.Selector) * RegionId * Z) :
    point_eqb point point = true.
  Proof.
    destruct point as [ [selector region] offset].
    cbn.
    rewrite (proj2 (selector_eqb_spec selector selector) eq_refl).
    rewrite (proj2 (region_eqb_spec region region) eq_refl).
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  Definition enabled_memb
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z) : bool :=
    List.existsb
      (point_eqb (selector, region, offset))
      (enabled_points facts).

  Lemma enabled_memb_sound
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z) :
    enabled_memb facts selector region offset = true ->
    List.In (selector, region, offset) (enabled_points facts).
  Proof.
    unfold enabled_memb.
    intros Hmemb.
    apply List.existsb_exists in Hmemb.
    destruct Hmemb as (point & Hin & Heq).
    apply point_eqb_eq in Heq.
    subst point.
    exact Hin.
  Qed.

  Lemma enabled_memb_complete
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z) :
    List.In (selector, region, offset) (enabled_points facts) ->
    enabled_memb facts selector region offset = true.
  Proof.
    intros Hin.
    unfold enabled_memb.
    apply List.existsb_exists.
    exists (selector, region, offset).
    split; [exact Hin | apply point_eqb_refl].
  Qed.

  (** First-match lookup of a fixed-cell write.  Under
      [no_conflicting_writes] every write to the same cell carries the same
      value, so the first match is "the" written value. *)
  Fixpoint fixed_lookup
      (writes : list (columns.(Columns.Fixed) * RegionId * Z * Z))
      (column : columns.(Columns.Fixed))
      (region : RegionId) (offset : Z) : option Z :=
    match writes with
    | [] => None
    | (column', region', offset', value) :: writes =>
        if fixed_eqb column column' &&
           region_eqb region region' &&
           Z.eqb offset offset'
        then Some value
        else fixed_lookup writes column region offset
    end.

  Definition fixed_write_or_zero
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Fixed))
      (region : RegionId) (offset : Z) : Z :=
    match fixed_lookup (fixed_writes facts) column region offset with
    | Some value => value
    | None => 0
    end.

  (** First-match lookup of a loaded table column.  Under
      [no_conflicting_writes] at most one load per column exists (up to
      equal contents), so the first match is "the" loaded table. *)
  Fixpoint table_lookup
      (entries : list (columns.(Columns.Lookup) * list Z * Z))
      (column : columns.(Columns.Lookup)) : option (list Z * Z) :=
    match entries with
    | [] => None
    | (column', values, default_value) :: entries =>
        if lookup_eqb column column'
        then Some (values, default_value)
        else table_lookup entries column
    end.

  Definition table_value
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Lookup))
      (row : Z) : Z :=
    match table_lookup (table_entries facts) column with
    | Some (values, default_value) => value_at_row row values default_value
    | None => 0
    end.

  (** ** Honest planes

      The selector, fixed and lookup planes read off the synthesis facts;
      the advice and instance planes stay abstract (they are the witness).
      The lookup plane is pinned on non-negative rows only, matching the
      [LookupTableLoaded] interpretation. *)

  Definition honest_selector_plane
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) : Prop :=
    forall selector region offset,
      Γ.(Assignment.selector) selector region offset =
      if enabled_memb facts selector region offset then 1 else 0.

  Definition honest_fixed_plane
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) : Prop :=
    forall column region offset,
      Γ.(Assignment.fixed) column region offset =
      fixed_write_or_zero facts column region offset.

  Definition honest_lookup_plane
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) : Prop :=
    forall column row,
      0 <= row ->
      Γ.(Assignment.lookup) column row = table_value facts column row.

  Definition honest_planes {A : Set}
      (Γ : Assignment.t columns RegionId)
      (program : 𝓛 columns RegionId A) : Prop :=
    honest_selector_plane Γ (layouter_facts program) /\
    honest_fixed_plane Γ (layouter_facts program) /\
    honest_lookup_plane Γ (layouter_facts program).

  Lemma eval_selector_off
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z) :
    honest_selector_plane Γ facts ->
    enabled_memb facts selector region row = false ->
    eval_selector Γ (region, row) selector = 0.
  Proof.
    intros Hselector Hmemb.
    unfold honest_selector_plane in Hselector.
    unfold eval_selector.
    rewrite Hselector, Hmemb.
    reflexivity.
  Qed.

  (** ** Boolean checks on the system and the fact list *)

  (** Every constraint of every gate has [Constraint.Select] as its top
      constructor, so gate satisfaction is vacuous wherever the guarding
      selector evaluates to [0]. *)
  Definition constraint_guarded (constraint : Constraint.t columns) : bool :=
    match constraint with
    | Constraint.Select _ _ => true
    | _ => false
    end.

  Definition selector_guarded (system : ConstraintSystem.t columns) : bool :=
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) => constraint_guarded constraint)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  (** Every fixed-cell write agrees with the first write to the same cell,
      and every table load agrees with the first load of the same column —
      so [fixed_write_or_zero] and [table_value] are well defined. *)
  Definition no_conflicting_writes
      (facts : list (Fact.t columns RegionId)) : bool :=
    List.forallb
      (fun '(column, region, offset, value) =>
        match fixed_lookup (fixed_writes facts) column region offset with
        | Some value' => Z.eqb value value'
        | None => false
        end)
      (fixed_writes facts) &&
    List.forallb
      (fun '(column, values, default_value) =>
        match table_lookup (table_entries facts) column with
        | Some (values', default_value') =>
            list_Z_eqb values values' && Z.eqb default_value default_value'
        | None => false
        end)
      (table_entries facts).

  Lemma no_conflicting_writes_fixed
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Fixed))
      (region : RegionId) (offset value : Z) :
    no_conflicting_writes facts = true ->
    List.In (Fact.FixedIs column region offset value) facts ->
    fixed_write_or_zero facts column region offset = value.
  Proof.
    intros Hconflict Hin.
    apply Bool.andb_true_iff in Hconflict.
    destruct Hconflict as [Hfixed _].
    rewrite List.forallb_forall in Hfixed.
    apply fixed_writes_In in Hin.
    specialize (Hfixed _ Hin).
    cbn in Hfixed.
    unfold fixed_write_or_zero.
    destruct (fixed_lookup (fixed_writes facts) column region offset)
      as [value' |]; [| discriminate].
    apply Z.eqb_eq in Hfixed.
    symmetry.
    exact Hfixed.
  Qed.

  Lemma no_conflicting_writes_table
      (facts : list (Fact.t columns RegionId))
      (column : columns.(Columns.Lookup))
      (values : list Z) (default_value : Z) :
    no_conflicting_writes facts = true ->
    List.In (Fact.LookupTableLoaded column values default_value) facts ->
    forall row,
      table_value facts column row = value_at_row row values default_value.
  Proof.
    intros Hconflict Hin row.
    apply Bool.andb_true_iff in Hconflict.
    destruct Hconflict as [_ Htable].
    rewrite List.forallb_forall in Htable.
    apply table_entries_In in Hin.
    specialize (Htable _ Hin).
    cbn in Htable.
    unfold table_value.
    destruct (table_lookup (table_entries facts) column)
      as [ [values' default_value'] |]; [| discriminate].
    apply Bool.andb_true_iff in Htable.
    destruct Htable as [Hvalues Hdefault].
    apply list_Z_eqb_eq in Hvalues.
    apply Z.eqb_eq in Hdefault.
    subst.
    reflexivity.
  Qed.

  (** ** Lookup padding: partial evaluation under all-zero selectors

      [zero_selector_value expression = Some value] means: whenever every
      selector occurring in [expression] evaluates to [0], the expression
      evaluates to [value] — advice/fixed/instance atoms are unknown
      ([None]) but are killed by a [0] factor in a product.  This shape
      covers the standard lookup-argument padding, where the gating selector
      multiplies every unknown atom. *)
  Fixpoint zero_selector_value (expression : Expression.t columns)
      : option Z :=
    match expression with
    | Expression.Constant value => Some (UnOp.from value)
    | Expression.Selector _ => Some 0
    | Expression.Fixed _ _ => None
    | Expression.Advice _ _ => None
    | Expression.Instance_ _ _ => None
    | Expression.Negated expression =>
        match zero_selector_value expression with
        | Some value => Some (UnOp.opp value)
        | None => None
        end
    | Expression.Sum lhs rhs =>
        match zero_selector_value lhs, zero_selector_value rhs with
        | Some value_l, Some value_r => Some (BinOp.add value_l value_r)
        | _, _ => None
        end
    | Expression.Product lhs rhs =>
        match zero_selector_value lhs, zero_selector_value rhs with
        | Some value_l, Some value_r => Some (BinOp.mul value_l value_r)
        | Some value_l, None => if Z.eqb value_l 0 then Some 0 else None
        | None, Some value_r => if Z.eqb value_r 0 then Some 0 else None
        | None, None => None
        end
    | Expression.Scaled expression scale =>
        match zero_selector_value expression with
        | Some value => Some (BinOp.mul value (UnOp.from scale))
        | None => None
        end
    end.

  (** A selector occurs (as an [Expression.Selector] atom) in an
      expression. *)
  Fixpoint selector_occurs
      (selector : columns.(Columns.Selector))
      (expression : Expression.t columns) : bool :=
    match expression with
    | Expression.Selector selector' => selector_eqb selector selector'
    | Expression.Constant _ | Expression.Fixed _ _
    | Expression.Advice _ _ | Expression.Instance_ _ _ => false
    | Expression.Negated expression => selector_occurs selector expression
    | Expression.Sum lhs rhs | Expression.Product lhs rhs =>
        selector_occurs selector lhs || selector_occurs selector rhs
    | Expression.Scaled expression _ => selector_occurs selector expression
    end.

  (** Some selector occurring in the expression is enabled at
      [(region, row)]. *)
  Fixpoint expr_active
      (facts : list (Fact.t columns RegionId))
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) : bool :=
    match expression with
    | Expression.Selector selector => enabled_memb facts selector region row
    | Expression.Constant _ | Expression.Fixed _ _
    | Expression.Advice _ _ | Expression.Instance_ _ _ => false
    | Expression.Negated expression => expr_active facts region row expression
    | Expression.Sum lhs rhs | Expression.Product lhs rhs =>
        expr_active facts region row lhs || expr_active facts region row rhs
    | Expression.Scaled expression _ => expr_active facts region row expression
    end.

  Definition arg_mentions_selector
      (selector : columns.(Columns.Selector))
      (arg : LookupArgument.t columns) : bool :=
    List.existsb
      (fun '(expression, _) => selector_occurs selector expression)
      arg.(LookupArgument.pairs).

  Definition arg_active
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z) : bool :=
    List.existsb
      (fun '(expression, _) => expr_active facts region row expression)
      arg.(LookupArgument.pairs).

  Lemma add_opp_sub (value_l value_r : Z) :
    BinOp.add value_l (UnOp.opp value_r) = BinOp.sub value_l value_r.
  Proof.
    unfold BinOp.add, BinOp.sub, UnOp.opp.
    pose proof (prime_range (p := p)).
    rewrite Z.add_mod_idemp_r by lia.
    f_equal; lia.
  Qed.

  (** [eval_expression] treats [Sum lhs (Negated rhs)] as a primitive
      subtraction; this lemma gives the uniform compositional reading. *)
  Lemma eval_expression_sum
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (lhs rhs : Expression.t columns) :
    eval_expression Γ index (Expression.Sum lhs rhs) =
    BinOp.add
      (eval_expression Γ index lhs)
      (eval_expression Γ index rhs).
  Proof.
    destruct index as [region row].
    destruct rhs; try reflexivity.
    cbn [eval_expression].
    symmetry.
    apply add_opp_sub.
  Qed.

  Lemma zero_selector_value_sound
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (Hselector : honest_selector_plane Γ facts)
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) :
    forall (value : Z),
      expr_active facts region row expression = false ->
      zero_selector_value expression = Some value ->
      eval_expression Γ (region, row) expression = value.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      intros value Hactive Hvalue; cbn in Hactive, Hvalue.
    - (* Constant *)
      injection Hvalue as Hvalue.
      subst value.
      reflexivity.
    - (* Selector *)
      injection Hvalue as Hvalue.
      subst value.
      exact (eval_selector_off Γ facts selector region row Hselector Hactive).
    - (* Fixed *) discriminate.
    - (* Advice *) discriminate.
    - (* Instance_ *) discriminate.
    - (* Negated *)
      destruct (zero_selector_value expression) as [value' |] eqn:Hinner;
        [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      cbn [eval_expression].
      rewrite (IH value' Hactive eq_refl).
      reflexivity.
    - (* Sum *)
      apply Bool.orb_false_iff in Hactive.
      destruct Hactive as [Hactive_l Hactive_r].
      destruct (zero_selector_value lhs) as [value_l |] eqn:Hl;
        [| discriminate].
      destruct (zero_selector_value rhs) as [value_r |] eqn:Hr;
        [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      rewrite eval_expression_sum.
      rewrite (IHl value_l Hactive_l eq_refl).
      rewrite (IHr value_r Hactive_r eq_refl).
      reflexivity.
    - (* Product *)
      apply Bool.orb_false_iff in Hactive.
      destruct Hactive as [Hactive_l Hactive_r].
      cbn [eval_expression].
      destruct (zero_selector_value lhs) as [value_l |] eqn:Hl;
        destruct (zero_selector_value rhs) as [value_r |] eqn:Hr.
      + injection Hvalue as Hvalue.
        subst value.
        rewrite (IHl value_l Hactive_l eq_refl).
        rewrite (IHr value_r Hactive_r eq_refl).
        reflexivity.
      + destruct (Z.eqb value_l 0) eqn:Hzero; [| discriminate].
        apply Z.eqb_eq in Hzero.
        subst value_l.
        injection Hvalue as Hvalue.
        subst value.
        rewrite (IHl 0 Hactive_l eq_refl).
        apply FieldRewrite.mul_zero_left.
      + destruct (Z.eqb value_r 0) eqn:Hzero; [| discriminate].
        apply Z.eqb_eq in Hzero.
        subst value_r.
        injection Hvalue as Hvalue.
        subst value.
        rewrite (IHr 0 Hactive_r eq_refl).
        apply FieldRewrite.mul_zero_right.
      + discriminate.
    - (* Scaled *)
      destruct (zero_selector_value expression) as [value' |] eqn:Hinner;
        [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      cbn [eval_expression].
      rewrite (IH value' Hactive eq_refl).
      reflexivity.
  Qed.

  Lemma expr_active_ex
      (facts : list (Fact.t columns RegionId))
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) :
    expr_active facts region row expression = true ->
    exists selector,
      selector_occurs selector expression = true /\
      enabled_memb facts selector region row = true.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      cbn; intros Hactive; try discriminate.
    - (* Selector *)
      exists selector.
      split; [| exact Hactive].
      exact (proj2 (selector_eqb_spec selector selector) eq_refl).
    - (* Negated *)
      exact (IH Hactive).
    - (* Sum *)
      apply Bool.orb_true_iff in Hactive.
      destruct Hactive as [Hside | Hside].
      + destruct (IHl Hside) as (selector & Hocc & Hmemb).
        exists selector.
        split; [| exact Hmemb].
        rewrite Hocc.
        reflexivity.
      + destruct (IHr Hside) as (selector & Hocc & Hmemb).
        exists selector.
        split; [| exact Hmemb].
        rewrite Hocc.
        apply Bool.orb_true_r.
    - (* Product *)
      apply Bool.orb_true_iff in Hactive.
      destruct Hactive as [Hside | Hside].
      + destruct (IHl Hside) as (selector & Hocc & Hmemb).
        exists selector.
        split; [| exact Hmemb].
        rewrite Hocc.
        reflexivity.
      + destruct (IHr Hside) as (selector & Hocc & Hmemb).
        exists selector.
        split; [| exact Hmemb].
        rewrite Hocc.
        apply Bool.orb_true_r.
    - (* Scaled *)
      exact (IH Hactive).
  Qed.

  Lemma arg_active_ex
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z) :
    arg_active facts arg region row = true ->
    exists selector,
      arg_mentions_selector selector arg = true /\
      enabled_memb facts selector region row = true.
  Proof.
    unfold arg_active.
    intros Hactive.
    apply List.existsb_exists in Hactive.
    destruct Hactive as ([expression column] & Hin & Hexpr).
    cbn in Hexpr.
    destruct (expr_active_ex facts region row expression Hexpr)
      as (selector & Hocc & Hmemb).
    exists selector.
    split; [| exact Hmemb].
    unfold arg_mentions_selector.
    apply List.existsb_exists.
    exists (expression, column).
    split; [exact Hin |].
    exact Hocc.
  Qed.

  Lemma arg_active_false_pairs
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z)
      (expression : Expression.t columns)
      (column : columns.(Columns.Lookup)) :
    arg_active facts arg region row = false ->
    List.In (expression, column) arg.(LookupArgument.pairs) ->
    expr_active facts region row expression = false.
  Proof.
    intros Hactive Hin.
    destruct (expr_active facts region row expression) eqn:Hexpr;
      [| reflexivity].
    exfalso.
    assert (Htrue : arg_active facts arg region row = true). {
      unfold arg_active.
      apply List.existsb_exists.
      exists (expression, column).
      split; [exact Hin |].
      exact Hexpr.
    }
    congruence.
  Qed.

  (** For a system with lookup arguments: the table has at least one row,
      and each argument's padding tuple — its expressions evaluated with
      every selector at [0] — equals table row [0].  On rows where none of
      an argument's selectors is enabled, row [0] therefore witnesses the
      argument.  A system with no lookup arguments passes trivially (its
      program may load no table at all, so [nb_table_rows] may be [0]). *)
  Definition lookup_defaults_ok
      (system : ConstraintSystem.t columns)
      (facts : list (Fact.t columns RegionId))
      (nb_table_rows : Z) : bool :=
    match system.(ConstraintSystem.lookups) with
    | [] => true
    | _ :: _ =>
        (0 <? nb_table_rows) &&
        List.forallb
          (fun arg =>
            List.forallb
              (fun '(expression, column) =>
                match zero_selector_value expression,
                      table_lookup (table_entries facts) column with
                | Some value, Some (values, default_value) =>
                    Z.eqb value (value_at_row 0 values default_value)
                | _, _ => false
                end)
              arg.(LookupArgument.pairs))
          system.(ConstraintSystem.lookups)
    end.

  (** ** Forall-style introduction of the conjunction shapes *)

  Lemma interpret_facts_forall
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) :
    (forall fact, List.In fact facts -> interpret_fact Γ fact) ->
    interpret_facts Γ facts.
  Proof.
    induction facts as [| fact facts IH]; intros Hall; cbn.
    - exact I.
    - split.
      + apply Hall. left. reflexivity.
      + apply IH. intros fact' Hin. apply Hall. right. exact Hin.
  Qed.

  Lemma eval_constraints_forall
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraints : Constraints.t columns) :
    (forall constraint,
      List.In constraint constraints ->
      eval_named_constraint Γ index constraint) ->
    eval_constraints Γ index constraints.
  Proof.
    induction constraints as [| constraint constraints IH]; intros Hall.
    - exact I.
    - destruct constraints as [| constraint' constraints'].
      + apply Hall. left. reflexivity.
      + cbn.
        split.
        * apply Hall. left. reflexivity.
        * apply IH. intros c Hin. apply Hall. right. exact Hin.
  Qed.

  Lemma eval_gates_forall
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gates : list (Gate.t columns)) :
    (forall gate, List.In gate gates -> eval_gate Γ index gate) ->
    eval_gates Γ index gates.
  Proof.
    induction gates as [| gate gates IH]; intros Hall.
    - exact I.
    - destruct gates as [| gate' gates'].
      + apply Hall. left. reflexivity.
      + cbn.
        split.
        * apply Hall. left. reflexivity.
        * apply IH. intros g Hin. apply Hall. right. exact Hin.
  Qed.

  (** Any named constraint that occurs in an evaluated constraint list holds
      individually — the elimination companion of [eval_constraints_forall]. *)
  Lemma eval_constraints_In
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : option string * Constraint.t columns)
      (constraints : Constraints.t columns) :
    List.In constraint constraints ->
    eval_constraints Γ index constraints ->
    eval_named_constraint Γ index constraint.
  Proof.
    induction constraints as [| constraint' constraints IH];
      intros Hin Hconstraints.
    - destruct Hin.
    - cbn [List.In] in Hin.
      destruct Hin as [Heq | Hin].
      + subst constraint'.
        destruct constraints as [| constraint'' constraints'].
        * exact Hconstraints.
        * exact (proj1 Hconstraints).
      + destruct constraints as [| constraint'' constraints'].
        * destruct Hin.
        * exact (IH Hin (proj2 Hconstraints)).
  Qed.

  (** ** The three components of [circuit_holds] *)

  Lemma interpret_facts_intro
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (Hconflict : no_conflicting_writes facts = true)
      (Hselector : honest_selector_plane Γ facts)
      (Hfixed : honest_fixed_plane Γ facts)
      (Hlookup : honest_lookup_plane Γ facts)
      (Hwitness : interpret_facts Γ (witness_facts facts)) :
    interpret_facts Γ facts.
  Proof.
    apply interpret_facts_forall.
    intros fact Hin.
    destruct fact as
      [ selector region offset | column region offset value
      | left_cell right_cell | cell instance row
      | column values default_value | cell value ].
    - (* SelectorOn *)
      cbn [interpret_fact].
      unfold honest_selector_plane in Hselector.
      rewrite Hselector.
      apply enabled_points_In in Hin.
      apply enabled_memb_complete in Hin.
      rewrite Hin.
      reflexivity.
    - (* FixedIs *)
      cbn [interpret_fact].
      unfold honest_fixed_plane in Hfixed.
      rewrite Hfixed.
      exact (no_conflicting_writes_fixed facts column region offset value
        Hconflict Hin).
    - (* CellsEqual *)
      exact (interpret_facts_In Γ _ (witness_facts facts) Hwitness
        (witness_facts_In facts _ Hin eq_refl)).
    - (* InstanceIs *)
      exact (interpret_facts_In Γ _ (witness_facts facts) Hwitness
        (witness_facts_In facts _ Hin eq_refl)).
    - (* LookupTableLoaded *)
      cbn [interpret_fact].
      intros row Hrow.
      unfold honest_lookup_plane in Hlookup.
      rewrite (Hlookup column row Hrow).
      exact (no_conflicting_writes_table facts column values default_value
        Hconflict Hin row).
    - (* CellIsConstant *)
      exact (interpret_facts_In Γ _ (witness_facts facts) Hwitness
        (witness_facts_In facts _ Hin eq_refl)).
  Qed.

  Lemma satisfies_gates_intro
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (system : ConstraintSystem.t columns)
      (Hguarded : selector_guarded system = true)
      (Hselector : honest_selector_plane Γ facts)
      (Hpoints : forall selector region row,
        List.In (selector, region, row) (enabled_points facts) ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select selector body)
              gate.(Gate.constraints) ->
            eval_constraint Γ (region, row) body) :
    satisfies_gates Γ system.
  Proof.
    intros region row.
    apply eval_gates_forall.
    intros gate Hgate.
    unfold selector_guarded in Hguarded.
    rewrite List.forallb_forall in Hguarded.
    specialize (Hguarded gate Hgate).
    rewrite List.forallb_forall in Hguarded.
    unfold eval_gate.
    apply eval_constraints_forall.
    intros [name constraint] Hconstraint.
    specialize (Hguarded _ Hconstraint).
    cbn in Hguarded.
    cbn [eval_named_constraint].
    destruct constraint as
      [ selector body | lhs rhs | expression | expression range
      | lhs rhs | expression ];
      try discriminate Hguarded.
    cbn [eval_constraint].
    intros Hnonzero.
    destruct (enabled_memb facts selector region row) eqn:Hmemb.
    - apply enabled_memb_sound in Hmemb.
      exact (Hpoints selector region row Hmemb gate Hgate name body
        Hconstraint).
    - exfalso.
      exact (Hnonzero
        (eval_selector_off Γ facts selector region row Hselector Hmemb)).
  Qed.

  Lemma satisfies_lookups_intro
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (system : ConstraintSystem.t columns)
      (nb_table_rows : Z)
      (Hdefaults : lookup_defaults_ok system facts nb_table_rows = true)
      (Hselector : honest_selector_plane Γ facts)
      (Hlookup : honest_lookup_plane Γ facts)
      (Hactive : forall selector region row,
        List.In (selector, region, row) (enabled_points facts) ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          arg_mentions_selector selector arg = true ->
          eval_lookup_argument Γ (region, row) nb_table_rows arg) :
    satisfies_lookups Γ nb_table_rows system.
  Proof.
    unfold lookup_defaults_ok in Hdefaults.
    intros region row.
    destruct (system.(ConstraintSystem.lookups)) as [| arg0 args] eqn:Hsys;
      [constructor |].
    apply Bool.andb_true_iff in Hdefaults.
    destruct Hdefaults as [Hpositive Hdefaults].
    apply Z.ltb_lt in Hpositive.
    rewrite List.forallb_forall in Hdefaults.
    apply List.Forall_forall.
    intros arg Harg.
    destruct (arg_active facts arg region row) eqn:Hact.
    - (* Some selector of the argument is enabled here: finite obligation. *)
      destruct (arg_active_ex facts arg region row Hact)
        as (selector & Hmention & Hmemb).
      apply enabled_memb_sound in Hmemb.
      exact (Hactive selector region row Hmemb arg Harg Hmention).
    - (* Padding row: table row 0 witnesses the argument. *)
      unfold eval_lookup_argument.
      exists 0.
      split; [lia |].
      specialize (Hdefaults arg Harg).
      rewrite List.forallb_forall in Hdefaults.
      apply List.Forall_forall.
      intros [expression column] Hpair.
      specialize (Hdefaults _ Hpair).
      cbn in Hdefaults.
      destruct (zero_selector_value expression) as [value |] eqn:Hvalue;
        [| discriminate].
      destruct (table_lookup (table_entries facts) column)
        as [ [values default_value] |] eqn:Htable; [| discriminate].
      apply Z.eqb_eq in Hdefaults.
      rewrite (zero_selector_value_sound Γ facts Hselector region row
        expression value
        (arg_active_false_pairs facts arg region row expression column
          Hact Hpair)
        Hvalue).
      unfold honest_lookup_plane in Hlookup.
      rewrite (Hlookup column 0) by lia.
      unfold table_value.
      rewrite Htable.
      exact Hdefaults.
  Qed.

  (** ** The introduction theorem *)

  Theorem circuit_holds_intro {A : Set}
      (Γ : Assignment.t columns RegionId)
      (program : 𝓛 columns RegionId A)
      (system : ConstraintSystem.t columns)
      (Hguarded : selector_guarded system = true)
      (Hconflict : no_conflicting_writes (layouter_facts program) = true)
      (Hdefaults : lookup_defaults_ok system (layouter_facts program)
        (layouter_table_rows program) = true)
      (Hplanes : honest_planes Γ program)
      (Hwitness : interpret_facts Γ (witness_facts (layouter_facts program)))
      (Hgates : forall selector region row,
        List.In (selector, region, row)
          (enabled_points (layouter_facts program)) ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select selector body)
              gate.(Gate.constraints) ->
            eval_constraint Γ (region, row) body)
      (Hlookups : forall selector region row,
        List.In (selector, region, row)
          (enabled_points (layouter_facts program)) ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          arg_mentions_selector selector arg = true ->
          eval_lookup_argument Γ (region, row)
            (layouter_table_rows program) arg) :
    circuit_holds Γ program system.
  Proof.
    destruct Hplanes as (Hselector & Hfixed & Hlookup).
    split; [| split].
    - exact (interpret_facts_intro Γ (layouter_facts program)
        Hconflict Hselector Hfixed Hlookup Hwitness).
    - exact (satisfies_gates_intro Γ (layouter_facts program) system
        Hguarded Hselector Hgates).
    - exact (satisfies_lookups_intro Γ (layouter_facts program) system
        (layouter_table_rows program)
        Hdefaults Hselector Hlookup Hlookups).
  Qed.

  (** ** Reflection layer for a computable assignment

      [eval_expression] computes, so the checkers reuse it directly; each
      checker comes with a soundness lemma into the [Prop]-level semantics,
      so the finite obligations of [circuit_holds_intro] discharge by
      [vm_compute] on a computable [Γ]. *)

  Fixpoint check_constraint
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : Constraint.t columns) : bool :=
    match constraint with
    | Constraint.Select selector constraint =>
        if Z.eqb (eval_selector Γ index selector) 0
        then true
        else check_constraint Γ index constraint
    | Constraint.Equal lhs rhs =>
        Z.eqb (eval_expression Γ index lhs) (eval_expression Γ index rhs)
    | Constraint.Boolean expression =>
        let value := eval_expression Γ index expression in
        Z.eqb value 0 || Z.eqb value 1
    | Constraint.Range expression range =>
        let value := eval_expression Γ index expression in
        (0 <=? value) && (value <? Z.of_nat range)
    | Constraint.Either lhs rhs =>
        check_constraint Γ index lhs || check_constraint Γ index rhs
    | Constraint.EqualZeroToPrecise expression =>
        Z.eqb (eval_expression Γ index expression) 0
    end.

  Lemma check_constraint_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : Constraint.t columns) :
    check_constraint Γ index constraint = true ->
    eval_constraint Γ index constraint.
  Proof.
    induction constraint as
      [ selector body IHbody | lhs rhs | expression | expression range
      | lhs IHl rhs IHr | expression ];
      cbn [check_constraint eval_constraint]; intros Hcheck.
    - (* Select *)
      intros Hnonzero.
      destruct (Z.eqb (eval_selector Γ index selector) 0) eqn:Hzero.
      + apply Z.eqb_eq in Hzero.
        contradiction.
      + exact (IHbody Hcheck).
    - (* Equal *)
      apply Z.eqb_eq in Hcheck.
      exact Hcheck.
    - (* Boolean *)
      apply Bool.orb_true_iff in Hcheck.
      destruct Hcheck as [Hzero | Hone].
      + apply Z.eqb_eq in Hzero.
        rewrite Hzero.
        exact (eq_refl 0).
      + apply Z.eqb_eq in Hone.
        rewrite Hone.
        exact (eq_refl 1).
    - (* Range *)
      apply Bool.andb_true_iff in Hcheck.
      destruct Hcheck as [Hlow Hhigh].
      apply Z.leb_le in Hlow.
      apply Z.ltb_lt in Hhigh.
      exact (conj Hlow Hhigh).
    - (* Either *)
      apply Bool.orb_true_iff in Hcheck.
      destruct Hcheck as [Hside | Hside].
      + left. exact (IHl Hside).
      + right. exact (IHr Hside).
    - (* EqualZeroToPrecise *)
      apply Z.eqb_eq in Hcheck.
      exact Hcheck.
  Qed.

  Definition check_named_constraint
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : option string * Constraint.t columns) : bool :=
    check_constraint Γ index (snd constraint).

  Definition check_constraints
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraints : Constraints.t columns) : bool :=
    List.forallb (check_named_constraint Γ index) constraints.

  Lemma check_constraints_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraints : Constraints.t columns) :
    check_constraints Γ index constraints = true ->
    eval_constraints Γ index constraints.
  Proof.
    intros Hcheck.
    apply eval_constraints_forall.
    intros [name constraint] Hin.
    unfold check_constraints in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    specialize (Hcheck _ Hin).
    unfold check_named_constraint in Hcheck.
    cbn in Hcheck.
    exact (check_constraint_sound Γ index constraint Hcheck).
  Qed.

  Definition check_gate
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gate : Gate.t columns) : bool :=
    check_constraints Γ index gate.(Gate.constraints).

  Lemma check_gate_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gate : Gate.t columns) :
    check_gate Γ index gate = true ->
    eval_gate Γ index gate.
  Proof.
    intros Hcheck.
    exact (check_constraints_sound Γ index gate.(Gate.constraints) Hcheck).
  Qed.

  Definition check_gates
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gates : list (Gate.t columns)) : bool :=
    List.forallb (check_gate Γ index) gates.

  Lemma check_gates_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gates : list (Gate.t columns)) :
    check_gates Γ index gates = true ->
    eval_gates Γ index gates.
  Proof.
    intros Hcheck.
    apply eval_gates_forall.
    intros gate Hin.
    unfold check_gates in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    exact (check_gate_sound Γ index gate (Hcheck gate Hin)).
  Qed.

  (** The caller supplies the witnessing table row ([table_row]) instead of
      the checker searching the table — e.g. the looked-up word itself for a
      generator table indexed by words. *)
  Definition check_lookup_argument
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows table_row : Z)
      (arg : LookupArgument.t columns) : bool :=
    (0 <=? table_row) && (table_row <? nb_table_rows) &&
    List.forallb
      (fun '(expression, column) =>
        Z.eqb
          (eval_expression Γ index expression)
          (Γ.(Assignment.lookup) column table_row))
      arg.(LookupArgument.pairs).

  Lemma check_lookup_argument_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows table_row : Z)
      (arg : LookupArgument.t columns) :
    check_lookup_argument Γ index nb_table_rows table_row arg = true ->
    eval_lookup_argument Γ index nb_table_rows arg.
  Proof.
    unfold check_lookup_argument.
    intros Hcheck.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hrange Hpairs].
    apply Bool.andb_true_iff in Hrange.
    destruct Hrange as [Hlow Hhigh].
    apply Z.leb_le in Hlow.
    apply Z.ltb_lt in Hhigh.
    unfold eval_lookup_argument.
    exists table_row.
    split; [lia |].
    rewrite List.forallb_forall in Hpairs.
    apply List.Forall_forall.
    intros [expression column] Hin.
    specialize (Hpairs _ Hin).
    cbn in Hpairs.
    apply Z.eqb_eq in Hpairs.
    exact Hpairs.
  Qed.

  (** The checker for the witness facts ([CellsEqual] / [InstanceIs] /
      [CellIsConstant]): each is a decidable equality between evaluated
      cells, so [witness_facts] obligations discharge by [vm_compute] on a
      computable assignment.  The plane facts ([SelectorOn] / [FixedIs] /
      [LookupTableLoaded]) are handled by the honest planes, not by this
      checker, so it rejects them. *)
  Definition check_witness_fact
      (Γ : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId) : bool :=
    match fact with
    | Fact.CellsEqual left_cell right_cell =>
        Z.eqb (eval_cell Γ left_cell) (eval_cell Γ right_cell)
    | Fact.InstanceIs cell instance row =>
        Z.eqb (eval_cell Γ cell) (Γ.(Assignment.instance_) instance row)
    | Fact.CellIsConstant cell value =>
        Z.eqb (eval_cell Γ cell) value
    | Fact.SelectorOn _ _ _ | Fact.FixedIs _ _ _ _
    | Fact.LookupTableLoaded _ _ _ => false
    end.

  Lemma check_witness_fact_sound
      (Γ : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId) :
    check_witness_fact Γ fact = true ->
    interpret_fact Γ fact.
  Proof.
    destruct fact; cbn [check_witness_fact interpret_fact];
      intros Hcheck; try discriminate; apply Z.eqb_eq in Hcheck; exact Hcheck.
  Qed.

  Definition check_witness_facts
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) : bool :=
    List.forallb (check_witness_fact Γ) facts.

  Lemma check_witness_facts_sound
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) :
    check_witness_facts Γ facts = true ->
    interpret_facts Γ facts.
  Proof.
    intros Hcheck.
    apply interpret_facts_forall.
    intros fact Hin.
    unfold check_witness_facts in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    exact (check_witness_fact_sound Γ fact (Hcheck fact Hin)).
  Qed.

  (** All lookup arguments at one index, with a per-argument table-row hint
      function. *)
  Definition check_lookup_arguments
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows : Z)
      (hint : LookupArgument.t columns -> Z)
      (args : list (LookupArgument.t columns)) : bool :=
    List.forallb
      (fun arg => check_lookup_argument Γ index nb_table_rows (hint arg) arg)
      args.

  Lemma check_lookup_arguments_sound
      (Γ : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows : Z)
      (hint : LookupArgument.t columns -> Z)
      (args : list (LookupArgument.t columns)) :
    check_lookup_arguments Γ index nb_table_rows hint args = true ->
    List.Forall (eval_lookup_argument Γ index nb_table_rows) args.
  Proof.
    intros Hcheck.
    unfold check_lookup_arguments in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    apply List.Forall_forall.
    intros arg Hin.
    exact (check_lookup_argument_sound Γ index nb_table_rows (hint arg) arg
      (Hcheck arg Hin)).
  Qed.
End Completeness.

End Complete.
