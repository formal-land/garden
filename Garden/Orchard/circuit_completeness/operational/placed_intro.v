(** * Placed introduction for [circuit_holds] at a realized assignment

    [Complete.circuit_holds_intro] introduces [circuit_holds] from the
    [Complete.honest_planes] predicate, whose selector conjunct pins the
    selector plane to the *region-local* enabled-point indicator.  That
    predicate is false at an assignment read back off a replayed grid
    ([realize idx rs g]): the placement [rs] need not be row-injective, so
    an offset outside one region's extent can land on the absolute row of
    another region's enabled point, and the realized selector plane — which
    reads the grid at [rs region + offset] — is [1] there.  The lookup plane
    fails for the same reason past the loaded table: the grid carries the
    fill default only inside the fill's half-open extent and [0] beyond,
    while [Complete.table_value] carries the default on every row.

    This file re-runs the two intro lemmas of [Garden.Halo2.complete] against
    the weaker plane hypotheses a placed assignment does satisfy:

    - [placed_selector_off] replaces [Complete.honest_selector_plane]: the
      selector plane reads [0] at every [(region, row)] whose *absolute* row
      [rs region + row] is not the absolute row of an enabled point of the
      same selector.  This is exactly the direction
      [Complete.zero_selector_value_sound] and the gate-padding argument use;
      the converse ("reads 1 on the points") is never needed.
    - a single equation [Γ.(Assignment.lookup) column 0 =
      Complete.table_value … column 0] replaces
      [Complete.honest_lookup_plane]: row [0] is the only table row the
      padding branch of [satisfies_lookups] reads.
    - the residual per-point obligations are stated at every [(region, row)]
      whose absolute row equals an enabled point's, rather than at the point
      itself — the caller moves them back to the point with the row-shift
      form of [realize_eval_expression].

    The first conjunct of [circuit_holds] is assembled from the two halves the
    operational bridge already separates: [determined_facts] (free from replay
    success, [realize.facts]) and [Complete.witness_facts] (the witness
    obligations, supplied by the completeness generator).

    Nothing here is Orchard-specific: the section is parameterized exactly as
    [Complete]'s is. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module Placed.

Section Placed.
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
    (lookup_eqb :
      columns.(Columns.Lookup) -> columns.(Columns.Lookup) -> bool).

  (** ** The placed enabled-point indicator

      [placed_memb rs facts selector region row] holds when some point the
      program enables for [selector] sits at the same *absolute* row
      [rs region + row].  It is implied by (region-local) membership in
      [Complete.enabled_points] — take the point itself — and is in general
      strictly weaker, which is what makes the placed hypotheses provable of
      a realized assignment. *)
  Definition placed_memb
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z) : bool :=
    List.existsb
      (fun '(selector', region', offset') =>
        andb
          (selector_eqb selector selector')
          (Z.eqb (rs region + row) (rs region' + offset')))
      (Complete.enabled_points facts).

  (** The plane hypothesis a replayed grid satisfies: off the absolute rows
      of the enabled points, the selector plane is [0].  [idx] is carried so
      the predicate names the same placement data as [realize idx rs]; the
      condition itself only involves [rs]. *)
  Definition placed_selector_off
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId)) : Prop :=
    forall selector region row,
      List.existsb
        (fun '(selector', region', offset') =>
          andb
            (selector_eqb selector selector')
            (Z.eqb (rs region + row) (rs region' + offset')))
        (Complete.enabled_points facts) = false ->
      Γ.(Assignment.selector) selector region row = 0.

  Lemma placed_selector_off_memb
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId)) :
    placed_selector_off Γ idx rs facts <->
    (forall selector region row,
      placed_memb rs facts selector region row = false ->
      Γ.(Assignment.selector) selector region row = 0).
  Proof.
    unfold placed_selector_off, placed_memb.
    split; intros Hoff; exact Hoff.
  Qed.

  Lemma placed_memb_sound
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z) :
    placed_memb rs facts selector region row = true ->
    exists region' offset',
      List.In (selector, region', offset') (Complete.enabled_points facts) /\
      rs region' + offset' = rs region + row.
  Proof.
    unfold placed_memb.
    intros Hmemb.
    apply List.existsb_exists in Hmemb.
    destruct Hmemb as ([ [selector' region'] offset'] & Hin & Heq).
    apply Bool.andb_true_iff in Heq.
    destruct Heq as [Hselector Hrow].
    pose proof (proj1 (selector_eqb_spec selector selector') Hselector) as Hs.
    apply Z.eqb_eq in Hrow.
    subst selector'.
    exists region', offset'.
    split; [exact Hin | symmetry; exact Hrow].
  Qed.

  Lemma placed_memb_complete
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z)
      (region' : RegionId) (offset' : Z) :
    List.In (selector, region', offset') (Complete.enabled_points facts) ->
    rs region' + offset' = rs region + row ->
    placed_memb rs facts selector region row = true.
  Proof.
    intros Hin Hrow.
    unfold placed_memb.
    apply List.existsb_exists.
    exists (selector, region', offset').
    split; [exact Hin |].
    apply Bool.andb_true_iff.
    split.
    - exact (proj2 (selector_eqb_spec selector selector) eq_refl).
    - apply Z.eqb_eq.
      symmetry.
      exact Hrow.
  Qed.

  Lemma placed_eval_selector_off
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z) :
    placed_selector_off Γ idx rs facts ->
    placed_memb rs facts selector region row = false ->
    eval_selector Γ (region, row) selector = 0.
  Proof.
    intros Hoff Hmemb.
    unfold eval_selector.
    rewrite (proj1 (placed_selector_off_memb Γ idx rs facts) Hoff
      selector region row Hmemb).
    reflexivity.
  Qed.

  (** ** Placed activity of an expression / lookup argument

      The [Complete] originals, with [Complete.enabled_memb] replaced by
      [placed_memb]: "some selector occurring in the expression has an
      enabled point on this absolute row". *)

  Fixpoint placed_expr_active
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) : bool :=
    match expression with
    | Expression.Selector selector => placed_memb rs facts selector region row
    | Expression.Constant _ | Expression.Fixed _ _
    | Expression.Advice _ _ | Expression.Instance_ _ _ => false
    | Expression.Negated expression =>
        placed_expr_active rs facts region row expression
    | Expression.Sum lhs rhs | Expression.Product lhs rhs =>
        placed_expr_active rs facts region row lhs ||
        placed_expr_active rs facts region row rhs
    | Expression.Scaled expression _ =>
        placed_expr_active rs facts region row expression
    end.

  Definition placed_arg_active
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z) : bool :=
    List.existsb
      (fun '(expression, _) => placed_expr_active rs facts region row expression)
      arg.(LookupArgument.pairs).

  (** The padding lemma of [Complete.zero_selector_value_sound], re-proved
      against [placed_selector_off].  The [Fixed] / [Advice] / [Instance_]
      branches are [discriminate] — the padding path never reads the fixed,
      advice or instance planes — so only the selector plane is involved. *)
  Lemma placed_zero_selector_value_sound
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (Hoff : placed_selector_off Γ idx rs facts)
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) :
    forall (value : Z),
      placed_expr_active rs facts region row expression = false ->
      Complete.zero_selector_value expression = Some value ->
      eval_expression Γ (region, row) expression = value.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      intros value Hactive Hvalue;
      cbn [placed_expr_active Complete.zero_selector_value] in Hactive, Hvalue.
    - (* Constant *)
      injection Hvalue as Hvalue.
      subst value.
      reflexivity.
    - (* Selector *)
      injection Hvalue as Hvalue.
      subst value.
      exact (placed_eval_selector_off Γ idx rs facts selector region row
        Hoff Hactive).
    - (* Fixed *) discriminate.
    - (* Advice *) discriminate.
    - (* Instance_ *) discriminate.
    - (* Negated *)
      destruct (Complete.zero_selector_value expression) as [value' |]
        eqn:Hinner; [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      cbn [eval_expression].
      rewrite (IH value' Hactive eq_refl).
      reflexivity.
    - (* Sum *)
      apply Bool.orb_false_iff in Hactive.
      destruct Hactive as [Hactive_l Hactive_r].
      destruct (Complete.zero_selector_value lhs) as [value_l |] eqn:Hl;
        [| discriminate].
      destruct (Complete.zero_selector_value rhs) as [value_r |] eqn:Hr;
        [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      rewrite Complete.eval_expression_sum.
      rewrite (IHl value_l Hactive_l eq_refl).
      rewrite (IHr value_r Hactive_r eq_refl).
      reflexivity.
    - (* Product *)
      apply Bool.orb_false_iff in Hactive.
      destruct Hactive as [Hactive_l Hactive_r].
      cbn [eval_expression].
      destruct (Complete.zero_selector_value lhs) as [value_l |] eqn:Hl;
        destruct (Complete.zero_selector_value rhs) as [value_r |] eqn:Hr.
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
      destruct (Complete.zero_selector_value expression) as [value' |]
        eqn:Hinner; [| discriminate].
      injection Hvalue as Hvalue.
      subst value.
      cbn [eval_expression].
      rewrite (IH value' Hactive eq_refl).
      reflexivity.
  Qed.

  Lemma placed_expr_active_ex
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (region : RegionId) (row : Z)
      (expression : Expression.t columns) :
    placed_expr_active rs facts region row expression = true ->
    exists selector,
      Complete.selector_occurs selector_eqb selector expression = true /\
      placed_memb rs facts selector region row = true.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      cbn [placed_expr_active Complete.selector_occurs];
      intros Hactive; try discriminate.
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

  Lemma placed_arg_active_ex
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z) :
    placed_arg_active rs facts arg region row = true ->
    exists selector,
      Complete.arg_mentions_selector selector_eqb selector arg = true /\
      placed_memb rs facts selector region row = true.
  Proof.
    unfold placed_arg_active.
    intros Hactive.
    apply List.existsb_exists in Hactive.
    destruct Hactive as ([expression column] & Hin & Hexpr).
    cbn in Hexpr.
    destruct (placed_expr_active_ex rs facts region row expression Hexpr)
      as (selector & Hocc & Hmemb).
    exists selector.
    split; [| exact Hmemb].
    unfold Complete.arg_mentions_selector.
    apply List.existsb_exists.
    exists (expression, column).
    split; [exact Hin |].
    exact Hocc.
  Qed.

  Lemma placed_arg_active_false_pairs
      (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z)
      (expression : Expression.t columns)
      (column : columns.(Columns.Lookup)) :
    placed_arg_active rs facts arg region row = false ->
    List.In (expression, column) arg.(LookupArgument.pairs) ->
    placed_expr_active rs facts region row expression = false.
  Proof.
    intros Hactive Hin.
    destruct (placed_expr_active rs facts region row expression) eqn:Hexpr;
      [| reflexivity].
    exfalso.
    assert (Htrue : placed_arg_active rs facts arg region row = true). {
      unfold placed_arg_active.
      apply List.existsb_exists.
      exists (expression, column).
      split; [exact Hin |].
      exact Hexpr.
    }
    congruence.
  Qed.

  (** ** The two placed intro lemmas *)

  (** [Complete.satisfies_gates_intro] against [placed_selector_off]: the
      residual obligation is one guarded constraint body per
      [(region, row)] sharing an enabled point's absolute row, rather than
      per enabled point. *)
  Lemma placed_satisfies_gates_intro
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (system : ConstraintSystem.t columns)
      (Hguarded : Complete.selector_guarded system = true)
      (Hoff : placed_selector_off Γ idx rs facts)
      (Hpoints : forall selector region row region' offset',
        List.In (selector, region', offset') (Complete.enabled_points facts) ->
        rs region' + offset' = rs region + row ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select selector body)
              gate.(Gate.constraints) ->
            eval_constraint Γ (region, row) body) :
    satisfies_gates Γ system.
  Proof.
    intros region row.
    apply Complete.eval_gates_forall.
    intros gate Hgate.
    unfold Complete.selector_guarded in Hguarded.
    rewrite List.forallb_forall in Hguarded.
    specialize (Hguarded gate Hgate).
    rewrite List.forallb_forall in Hguarded.
    unfold eval_gate.
    apply Complete.eval_constraints_forall.
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
    destruct (placed_memb rs facts selector region row) eqn:Hmemb.
    - destruct (placed_memb_sound rs facts selector region row Hmemb)
        as (region' & offset' & Hin & Hrow).
      exact (Hpoints selector region row region' offset' Hin Hrow gate Hgate
        name body Hconstraint).
    - exfalso.
      exact (Hnonzero
        (placed_eval_selector_off Γ idx rs facts selector region row
          Hoff Hmemb)).
  Qed.

  (** [Complete.satisfies_lookups_intro] against [placed_selector_off] and
      the single table-row-[0] equation.  The padding branch reads the
      lookup plane only at row [0] ([Hlookup0]) and the selector plane only
      through [placed_zero_selector_value_sound]. *)
  Lemma placed_satisfies_lookups_intro
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (system : ConstraintSystem.t columns)
      (nb_table_rows : Z)
      (Hdefaults :
        Complete.lookup_defaults_ok lookup_eqb system facts nb_table_rows = true)
      (Hoff : placed_selector_off Γ idx rs facts)
      (Hlookup0 : forall column,
        Γ.(Assignment.lookup) column 0 =
        Complete.table_value lookup_eqb facts column 0)
      (Hactive : forall selector region row region' offset',
        List.In (selector, region', offset') (Complete.enabled_points facts) ->
        rs region' + offset' = rs region + row ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector selector_eqb selector arg = true ->
          eval_lookup_argument Γ (region, row) nb_table_rows arg) :
    satisfies_lookups Γ nb_table_rows system.
  Proof.
    unfold Complete.lookup_defaults_ok in Hdefaults.
    intros region row.
    destruct (system.(ConstraintSystem.lookups)) as [| arg0 args] eqn:Hsys;
      [constructor |].
    apply Bool.andb_true_iff in Hdefaults.
    destruct Hdefaults as [Hpositive Hdefaults].
    apply Z.ltb_lt in Hpositive.
    rewrite List.forallb_forall in Hdefaults.
    apply List.Forall_forall.
    intros arg Harg.
    destruct (placed_arg_active rs facts arg region row) eqn:Hact.
    - (* Some selector of the argument has an enabled point on this
         absolute row: the finite obligation. *)
      destruct (placed_arg_active_ex rs facts arg region row Hact)
        as (selector & Hmention & Hmemb).
      destruct (placed_memb_sound rs facts selector region row Hmemb)
        as (region' & offset' & Hin & Hrow).
      exact (Hactive selector region row region' offset' Hin Hrow arg Harg
        Hmention).
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
      destruct (Complete.zero_selector_value expression) as [value |]
        eqn:Hvalue; [| discriminate].
      destruct (Complete.table_lookup lookup_eqb (Complete.table_entries facts)
        column) as [ [values default_value] |] eqn:Htable; [| discriminate].
      apply Z.eqb_eq in Hdefaults.
      rewrite (placed_zero_selector_value_sound Γ idx rs facts Hoff region row
        expression value
        (placed_arg_active_false_pairs rs facts arg region row expression
          column Hact Hpair)
        Hvalue).
      rewrite (Hlookup0 column).
      unfold Complete.table_value.
      rewrite Htable.
      exact Hdefaults.
  Qed.

  (** ** Assembling the fact conjunct

      [circuit_holds]'s first conjunct splits along exactly the partition the
      operational bridge uses: [determined_facts] (pinned by replay success)
      and [Complete.witness_facts] (the permutation/instance/constant
      obligations, supplied by the witness generator). *)
  Lemma placed_interpret_facts_intro
      (Γ : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      (Hdetermined : interpret_facts Γ (determined_facts facts))
      (Hwitness : interpret_facts Γ (Complete.witness_facts facts)) :
    interpret_facts Γ facts.
  Proof.
    apply interpret_facts_of_in.
    intros fact Hin.
    destruct fact as
      [ selector region offset | column region offset value
      | left_cell right_cell | cell instance row
      | column values default_value | cell value ].
    - exact (interpret_facts_In Γ _ (determined_facts facts) Hdetermined
        (proj2 (List.filter_In fact_is_determined _ facts)
          (conj Hin eq_refl))).
    - exact (interpret_facts_In Γ _ (determined_facts facts) Hdetermined
        (proj2 (List.filter_In fact_is_determined _ facts)
          (conj Hin eq_refl))).
    - exact (interpret_facts_In Γ _ (Complete.witness_facts facts) Hwitness
        (Complete.witness_facts_In facts _ Hin eq_refl)).
    - exact (interpret_facts_In Γ _ (Complete.witness_facts facts) Hwitness
        (Complete.witness_facts_In facts _ Hin eq_refl)).
    - exact (interpret_facts_In Γ _ (determined_facts facts) Hdetermined
        (proj2 (List.filter_In fact_is_determined _ facts)
          (conj Hin eq_refl))).
    - exact (interpret_facts_In Γ _ (Complete.witness_facts facts) Hwitness
        (Complete.witness_facts_In facts _ Hin eq_refl)).
  Qed.

  (** ** The placed introduction theorem *)

  Theorem placed_circuit_holds_intro {A : Set}
      (Γ : Assignment.t columns RegionId)
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (program : 𝓛 columns RegionId A)
      (system : ConstraintSystem.t columns)
      (Hguarded : Complete.selector_guarded system = true)
      (Hdefaults : Complete.lookup_defaults_ok lookup_eqb system
        (layouter_facts program) (layouter_table_rows program) = true)
      (Hoff : placed_selector_off Γ idx rs (layouter_facts program))
      (Hlookup0 : forall column,
        Γ.(Assignment.lookup) column 0 =
        Complete.table_value lookup_eqb (layouter_facts program) column 0)
      (Hdetermined :
        interpret_facts Γ (determined_facts (layouter_facts program)))
      (Hwitness :
        interpret_facts Γ (Complete.witness_facts (layouter_facts program)))
      (Hgates : forall selector region row region' offset',
        List.In (selector, region', offset')
          (Complete.enabled_points (layouter_facts program)) ->
        rs region' + offset' = rs region + row ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select selector body)
              gate.(Gate.constraints) ->
            eval_constraint Γ (region, row) body)
      (Hlookups : forall selector region row region' offset',
        List.In (selector, region', offset')
          (Complete.enabled_points (layouter_facts program)) ->
        rs region' + offset' = rs region + row ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector selector_eqb selector arg = true ->
          eval_lookup_argument Γ (region, row)
            (layouter_table_rows program) arg) :
    circuit_holds Γ program system.
  Proof.
    split; [| split].
    - exact (placed_interpret_facts_intro Γ (layouter_facts program)
        Hdetermined Hwitness).
    - exact (placed_satisfies_gates_intro Γ idx rs (layouter_facts program)
        system Hguarded Hoff Hgates).
    - exact (placed_satisfies_lookups_intro Γ idx rs (layouter_facts program)
        system (layouter_table_rows program) Hdefaults Hoff Hlookup0
        Hlookups).
  Qed.

  (** ** Deriving the table-row-[0] equation from the replayed facts

      For a lookup column the program actually loads with a non-empty table,
      [Hlookup0] is not an extra assumption: [determined_facts] pins row [0]
      of that column (the relational [Fact.LookupTableLoaded] pins exactly
      [[0, length values)], the keygen-faithful range), and
      [Complete.no_conflicting_writes] identifies the loaded contents with
      [Complete.table_value].

      [Complete.no_conflicting_writes] is stated over the fixed and region
      equalities as well, so they enter the section only here. *)
  Context
    (fixed_eqb :
      columns.(Columns.Fixed) -> columns.(Columns.Fixed) -> bool)
    (region_eqb : RegionId -> RegionId -> bool)
    (region_eqb_spec :
      forall region1 region2,
        region_eqb region1 region2 = true <-> region1 = region2).

End Placed.

End Placed.
