(** * E1a: operational completeness at the concrete C1 witness

    The completeness mirror of [Orchard/circuit_operational.v]: the honest
    Orchard witness of the C1 instance ([circuit_completeness/instance/cert.v])
    is accepted by the ideal checker [mock_prover_accepts] that mirrors Rust
    Halo2's [MockProver] over the serialized 19,679-event stream.  This is the
    operational non-vacuity certificate of the whole soundness surface: the
    accepted set of the ideal checker is inhabited by a real honest witness.

    The theorem is not the work — [Halo2/realize/sound.v] already carries the
    bridge.  The work is the *grid identification*: choosing the free planes of
    the initial grid from the honest generator and showing the realized
    assignment [realize Index.indices region_start_of g] satisfies
    [circuit_holds].  Total pointwise agreement between [Γtest] and the
    realized assignment is false — selectors alias across regions placed at
    equal absolute rows, and the lookup plane past the usable rows holds the
    keygen zero rather than the table default — so
    [Complete.circuit_holds_intro] is not applicable at the realized
    assignment.  Instead the three components are re-derived directly:

    - the program-determined facts are free from replay success
      ([determined_facts_hold_incl]);
    - the witness facts, the gate obligations at every enabled point and the
      lookup obligations transfer from [Γtest] by *cell agreement* at the
      finitely many cells they read, and are moved to arbitrary
      [(region, row)] pairs by the row-shift equations of
      [realize_eval_expression] (both sides evaluate at the absolute row);
    - each transfer is licensed by one input-independent [vm_compute]
      certificate over the reified synthesis facts, the event stream and the
      placement — never over the generator's values.  The certificates are
      therefore shared verbatim with the universal (E1b) rung.

    The chosen planes are [orchard_advice] — the pullback of the honest advice
    plane along the placement, through an input-independent inversion table —
    and [orchard_instance], the honest instance plane (which already ignores
    its column). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.instance.cert.
Require Import Garden.Orchard.circuit_operational.
Require Garden.Orchard.circuit_synthesis_constants.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardOperationalConcrete.

(** ** Generic layer: query extraction, cell agreement, row shifts

    Nothing here mentions Orchard: these are the reusable pieces the
    universal rung consumes verbatim. *)

Section Generic.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  (** *** The cells an expression queries at [(region, row)] *)

  Fixpoint expr_adv (e : Expression.t columns) (region : RegionId) (row : Z)
      : list (columns.(Columns.Advice) * RegionId * Z) :=
    match e with
    | Expression.Advice column rotation =>
        [(column, region, rotated_row row rotation)]
    | Expression.Negated e => expr_adv e region row
    | Expression.Scaled e _ => expr_adv e region row
    | Expression.Sum lhs rhs => expr_adv lhs region row ++ expr_adv rhs region row
    | Expression.Product lhs rhs =>
        expr_adv lhs region row ++ expr_adv rhs region row
    | _ => []
    end.

  Fixpoint expr_fix (e : Expression.t columns) (region : RegionId) (row : Z)
      : list (columns.(Columns.Fixed) * RegionId * Z) :=
    match e with
    | Expression.Fixed column rotation =>
        [(column, region, rotated_row row rotation)]
    | Expression.Negated e => expr_fix e region row
    | Expression.Scaled e _ => expr_fix e region row
    | Expression.Sum lhs rhs => expr_fix lhs region row ++ expr_fix rhs region row
    | Expression.Product lhs rhs =>
        expr_fix lhs region row ++ expr_fix rhs region row
    | _ => []
    end.

  Fixpoint expr_sels (e : Expression.t columns)
      : list (columns.(Columns.Selector)) :=
    match e with
    | Expression.Selector selector => [selector]
    | Expression.Negated e => expr_sels e
    | Expression.Scaled e _ => expr_sels e
    | Expression.Sum lhs rhs => expr_sels lhs ++ expr_sels rhs
    | Expression.Product lhs rhs => expr_sels lhs ++ expr_sels rhs
    | _ => []
    end.

  Fixpoint constr_adv (c : Constraint.t columns) (region : RegionId) (row : Z)
      : list (columns.(Columns.Advice) * RegionId * Z) :=
    match c with
    | Constraint.Select _ c => constr_adv c region row
    | Constraint.Equal lhs rhs =>
        expr_adv lhs region row ++ expr_adv rhs region row
    | Constraint.Boolean e => expr_adv e region row
    | Constraint.Range e _ => expr_adv e region row
    | Constraint.Either lhs rhs =>
        constr_adv lhs region row ++ constr_adv rhs region row
    | Constraint.EitherZeroToPrecise lhs rhs =>
        expr_adv lhs region row ++ expr_adv rhs region row
    | Constraint.EqualZeroToPrecise e => expr_adv e region row
    end.

  Fixpoint constr_fix (c : Constraint.t columns) (region : RegionId) (row : Z)
      : list (columns.(Columns.Fixed) * RegionId * Z) :=
    match c with
    | Constraint.Select _ c => constr_fix c region row
    | Constraint.Equal lhs rhs =>
        expr_fix lhs region row ++ expr_fix rhs region row
    | Constraint.Boolean e => expr_fix e region row
    | Constraint.Range e _ => expr_fix e region row
    | Constraint.Either lhs rhs =>
        constr_fix lhs region row ++ constr_fix rhs region row
    | Constraint.EitherZeroToPrecise lhs rhs =>
        expr_fix lhs region row ++ expr_fix rhs region row
    | Constraint.EqualZeroToPrecise e => expr_fix e region row
    end.

  Fixpoint constr_sels (c : Constraint.t columns)
      : list (columns.(Columns.Selector)) :=
    match c with
    | Constraint.Select selector c => selector :: constr_sels c
    | Constraint.Equal lhs rhs => expr_sels lhs ++ expr_sels rhs
    | Constraint.Boolean e => expr_sels e
    | Constraint.Range e _ => expr_sels e
    | Constraint.Either lhs rhs => constr_sels lhs ++ constr_sels rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        expr_sels lhs ++ expr_sels rhs
    | Constraint.EqualZeroToPrecise e => expr_sels e
    end.

  Definition arg_adv (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z)
      : list (columns.(Columns.Advice) * RegionId * Z) :=
    List.flat_map (fun pair => expr_adv (fst pair) region row)
      arg.(LookupArgument.pairs).

  Definition arg_fix (arg : LookupArgument.t columns)
      (region : RegionId) (row : Z)
      : list (columns.(Columns.Fixed) * RegionId * Z) :=
    List.flat_map (fun pair => expr_fix (fst pair) region row)
      arg.(LookupArgument.pairs).

  Definition arg_sels (arg : LookupArgument.t columns)
      : list (columns.(Columns.Selector)) :=
    List.flat_map (fun pair => expr_sels (fst pair))
      arg.(LookupArgument.pairs).

  (** *** Cell agreement between two assignments *)

  Definition adv_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (cells : list (columns.(Columns.Advice) * RegionId * Z)) : Prop :=
    forall column region offset,
      List.In (column, region, offset) cells ->
      Γ1.(Assignment.advice) column region offset =
      Γ2.(Assignment.advice) column region offset.

  Definition fix_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (cells : list (columns.(Columns.Fixed) * RegionId * Z)) : Prop :=
    forall column region offset,
      List.In (column, region, offset) cells ->
      Γ1.(Assignment.fixed) column region offset =
      Γ2.(Assignment.fixed) column region offset.

  Definition sel_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (selectors : list (columns.(Columns.Selector)))
      (region : RegionId) (row : Z) : Prop :=
    forall selector,
      List.In selector selectors ->
      Γ1.(Assignment.selector) selector region row =
      Γ2.(Assignment.selector) selector region row.

  Lemma adv_agree_incl (Γ1 Γ2 : Assignment.t columns RegionId) cells1 cells2 :
    List.incl cells1 cells2 -> adv_agree Γ1 Γ2 cells2 -> adv_agree Γ1 Γ2 cells1.
  Proof. intros Hincl Hagree column region offset Hin. apply Hagree, Hincl, Hin. Qed.

  Lemma fix_agree_incl (Γ1 Γ2 : Assignment.t columns RegionId) cells1 cells2 :
    List.incl cells1 cells2 -> fix_agree Γ1 Γ2 cells2 -> fix_agree Γ1 Γ2 cells1.
  Proof. intros Hincl Hagree column region offset Hin. apply Hagree, Hincl, Hin. Qed.

  Lemma sel_agree_incl (Γ1 Γ2 : Assignment.t columns RegionId) l1 l2 region row :
    List.incl l1 l2 -> sel_agree Γ1 Γ2 l2 region row ->
    sel_agree Γ1 Γ2 l1 region row.
  Proof. intros Hincl Hagree selector Hin. apply Hagree, Hincl, Hin. Qed.

  (** *** Agreement on the queried cells makes evaluation agree *)

  Lemma eval_expression_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (Hinstance : forall column row,
        Γ1.(Assignment.instance_) column row = Γ2.(Assignment.instance_) column row)
      (region : RegionId) (row : Z) (e : Expression.t columns) :
    adv_agree Γ1 Γ2 (expr_adv e region row) ->
    fix_agree Γ1 Γ2 (expr_fix e region row) ->
    sel_agree Γ1 Γ2 (expr_sels e) region row ->
    eval_expression Γ1 (region, row) e = eval_expression Γ2 (region, row) e.
  Proof.
    induction e as
      [ value | selector | column rotation | column rotation
      | column rotation | e IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | e IH scale ];
      intros Hadv Hfix Hsel.
    - reflexivity.
    - cbn [eval_expression eval_selector].
      rewrite (Hsel selector (or_introl eq_refl)).
      reflexivity.
    - cbn [eval_expression].
      rewrite (Hfix column region (rotated_row row rotation)
        (or_introl eq_refl)).
      reflexivity.
    - cbn [eval_expression].
      rewrite (Hadv column region (rotated_row row rotation)
        (or_introl eq_refl)).
      reflexivity.
    - cbn [eval_expression].
      rewrite Hinstance.
      reflexivity.
    - cbn [eval_expression].
      rewrite (IH Hadv Hfix Hsel).
      reflexivity.
    - cbn [expr_adv expr_fix expr_sels] in Hadv, Hfix, Hsel.
      rewrite (Complete.eval_expression_sum Γ1 (region, row) lhs rhs).
      rewrite (Complete.eval_expression_sum Γ2 (region, row) lhs rhs).
      f_equal.
      + apply IHl;
          [ exact (adv_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hadv)
          | exact (fix_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hfix)
          | exact (sel_agree_incl _ _ _ _ _ _
              (List.incl_appl _ (List.incl_refl _)) Hsel) ].
      + apply IHr;
          [ exact (adv_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hadv)
          | exact (fix_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hfix)
          | exact (sel_agree_incl _ _ _ _ _ _
              (List.incl_appr _ (List.incl_refl _)) Hsel) ].
    - cbn [expr_adv expr_fix expr_sels] in Hadv, Hfix, Hsel.
      cbn [eval_expression].
      rewrite IHl, IHr;
        [ reflexivity
        | exact (adv_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hadv)
        | exact (fix_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hfix)
        | exact (sel_agree_incl _ _ _ _ _ _
            (List.incl_appr _ (List.incl_refl _)) Hsel)
        | exact (adv_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hadv)
        | exact (fix_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hfix)
        | exact (sel_agree_incl _ _ _ _ _ _
            (List.incl_appl _ (List.incl_refl _)) Hsel) ].
    - cbn [eval_expression].
      rewrite (IH Hadv Hfix Hsel).
      reflexivity.
  Qed.

  Lemma eval_constraint_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (Hinstance : forall column row,
        Γ1.(Assignment.instance_) column row = Γ2.(Assignment.instance_) column row)
      (region : RegionId) (row : Z) (c : Constraint.t columns) :
    adv_agree Γ1 Γ2 (constr_adv c region row) ->
    fix_agree Γ1 Γ2 (constr_fix c region row) ->
    sel_agree Γ1 Γ2 (constr_sels c) region row ->
    eval_constraint Γ1 (region, row) c -> eval_constraint Γ2 (region, row) c.
  Proof.
    induction c as
      [ selector c IH | lhs rhs | e | e range | lhs IHl rhs IHr
      | lhs rhs | e ];
      intros Hadv Hfix Hsel Heval.
    - (* Select *)
      cbn [eval_constraint] in Heval |- *.
      intros Hnonzero.
      apply IH.
      + exact Hadv.
      + exact Hfix.
      + exact (sel_agree_incl _ _ _ _ _ _
          (List.incl_tl _ (List.incl_refl _)) Hsel).
      + apply Heval.
        unfold eval_selector in Hnonzero |- *.
        rewrite (Hsel selector (or_introl eq_refl)).
        exact Hnonzero.
    - (* Equal *)
      cbn [constr_adv constr_fix constr_sels] in Hadv, Hfix, Hsel.
      cbn [eval_constraint] in Heval |- *.
      rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row lhs
        (adv_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hadv)
        (fix_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hfix)
        (sel_agree_incl _ _ _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hsel)).
      rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row rhs
        (adv_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hadv)
        (fix_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hfix)
        (sel_agree_incl _ _ _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hsel)).
      exact Heval.
    - (* Boolean *)
      cbn [eval_constraint] in Heval |- *.
      rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row e
        Hadv Hfix Hsel).
      exact Heval.
    - (* Range *)
      cbn [eval_constraint] in Heval |- *.
      rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row e
        Hadv Hfix Hsel).
      exact Heval.
    - (* Either *)
      cbn [constr_adv constr_fix constr_sels] in Hadv, Hfix, Hsel.
      cbn [eval_constraint] in Heval |- *.
      destruct Heval as [Heval | Heval].
      + left.
        apply (IHl
          (adv_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hadv)
          (fix_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hfix)
          (sel_agree_incl _ _ _ _ _ _
            (List.incl_appl _ (List.incl_refl _)) Hsel)).
        exact Heval.
      + right.
        apply (IHr
          (adv_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hadv)
          (fix_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hfix)
          (sel_agree_incl _ _ _ _ _ _
            (List.incl_appr _ (List.incl_refl _)) Hsel)).
        exact Heval.
    - (* EitherZeroToPrecise *)
      cbn [constr_adv constr_fix constr_sels] in Hadv, Hfix, Hsel.
      cbn [eval_constraint] in Heval |- *.
      destruct Heval as [Heval | Heval].
      + left.
        rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row lhs
          (adv_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hadv)
          (fix_agree_incl _ _ _ _ (List.incl_appl _ (List.incl_refl _)) Hfix)
          (sel_agree_incl _ _ _ _ _ _
            (List.incl_appl _ (List.incl_refl _)) Hsel)).
        exact Heval.
      + right.
        rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row rhs
          (adv_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hadv)
          (fix_agree_incl _ _ _ _ (List.incl_appr _ (List.incl_refl _)) Hfix)
          (sel_agree_incl _ _ _ _ _ _
            (List.incl_appr _ (List.incl_refl _)) Hsel)).
        exact Heval.
    - (* EqualZeroToPrecise *)
      cbn [eval_constraint] in Heval |- *.
      rewrite <- (eval_expression_agree Γ1 Γ2 Hinstance region row e
        Hadv Hfix Hsel).
      exact Heval.
  Qed.

  Lemma eval_lookup_argument_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (Hinstance : forall column row,
        Γ1.(Assignment.instance_) column row = Γ2.(Assignment.instance_) column row)
      (region : RegionId) (row : Z) (nb_table_rows : Z)
      (arg : LookupArgument.t columns) :
    adv_agree Γ1 Γ2 (arg_adv arg region row) ->
    fix_agree Γ1 Γ2 (arg_fix arg region row) ->
    sel_agree Γ1 Γ2 (arg_sels arg) region row ->
    (forall column table_row,
      0 <= table_row < nb_table_rows ->
      Γ1.(Assignment.lookup) column table_row =
      Γ2.(Assignment.lookup) column table_row) ->
    eval_lookup_argument Γ1 (region, row) nb_table_rows arg ->
    eval_lookup_argument Γ2 (region, row) nb_table_rows arg.
  Proof.
    intros Hadv Hfix Hsel Hlookup Heval.
    destruct Heval as (table_row & Hbound & Hpairs).
    exists table_row.
    split; [exact Hbound |].
    rewrite List.Forall_forall in Hpairs |- *.
    intros [e column] Hpair.
    specialize (Hpairs (e, column) Hpair).
    cbv beta iota in Hpairs |- *.
    rewrite <- (Hlookup column table_row Hbound).
    rewrite <- Hpairs.
    symmetry.
    apply (eval_expression_agree Γ1 Γ2 Hinstance region row e).
    - apply (adv_agree_incl Γ1 Γ2 (expr_adv e region row)
        (arg_adv arg region row)); [| exact Hadv].
      intros x Hx.
      apply List.in_flat_map.
      exists (e, column).
      split; [exact Hpair | exact Hx].
    - apply (fix_agree_incl Γ1 Γ2 (expr_fix e region row)
        (arg_fix arg region row)); [| exact Hfix].
      intros x Hx.
      apply List.in_flat_map.
      exists (e, column).
      split; [exact Hpair | exact Hx].
    - apply (sel_agree_incl Γ1 Γ2 (expr_sels e) (arg_sels arg) region row);
        [| exact Hsel].
      intros x Hx.
      apply List.in_flat_map.
      exists (e, column).
      split; [exact Hpair | exact Hx].
  Qed.

  Lemma eval_cell_agree (Γ1 Γ2 : Assignment.t columns RegionId)
      (Hinstance : forall column row,
        Γ1.(Assignment.instance_) column row = Γ2.(Assignment.instance_) column row)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    (forall column,
      Garden.Halo2.Synthesis.Cell.column cell =
        Garden.Halo2.Synthesis.ColumnRef.Advice column ->
      Γ1.(Assignment.advice) column
        (Garden.Halo2.Synthesis.Cell.region cell)
        (Garden.Halo2.Synthesis.Cell.row_offset cell) =
      Γ2.(Assignment.advice) column
        (Garden.Halo2.Synthesis.Cell.region cell)
        (Garden.Halo2.Synthesis.Cell.row_offset cell)) ->
    (forall column,
      Garden.Halo2.Synthesis.Cell.column cell =
        Garden.Halo2.Synthesis.ColumnRef.Fixed column ->
      Γ1.(Assignment.fixed) column
        (Garden.Halo2.Synthesis.Cell.region cell)
        (Garden.Halo2.Synthesis.Cell.row_offset cell) =
      Γ2.(Assignment.fixed) column
        (Garden.Halo2.Synthesis.Cell.region cell)
        (Garden.Halo2.Synthesis.Cell.row_offset cell)) ->
    eval_cell Γ1 cell = eval_cell Γ2 cell.
  Proof.
    intros Hadv Hfix.
    unfold eval_cell.
    destruct (Garden.Halo2.Synthesis.Cell.column cell) as [column | column | column].
    - exact (Hadv column eq_refl).
    - exact (Hfix column eq_refl).
    - apply Hinstance.
  Qed.

  (** *** Lookup padding under an all-zero selector reading

      The placed variant of [Complete.zero_selector_value_sound]: the
      hypothesis is stated directly on the assignment's selector readings
      rather than through the honest selector plane, which the realized
      assignment does not have. *)
  Lemma zero_selector_value_agree (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z) (e : Expression.t columns) (value : Z) :
    (forall selector,
      List.In selector (expr_sels e) ->
      eval_selector Γ (region, row) selector = 0) ->
    Complete.zero_selector_value e = Some value ->
    eval_expression Γ (region, row) e = value.
  Proof.
    revert value.
    induction e as
      [ constant | selector | column rotation | column rotation
      | column rotation | e IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | e IH scale ];
      intros value Hzero Hvalue; cbn [Complete.zero_selector_value] in Hvalue.
    - injection Hvalue as <-.
      reflexivity.
    - injection Hvalue as <-.
      exact (Hzero selector (or_introl eq_refl)).
    - discriminate Hvalue.
    - discriminate Hvalue.
    - discriminate Hvalue.
    - destruct (Complete.zero_selector_value e) as [value' |] eqn:Hinner;
        [| discriminate Hvalue].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH value' Hzero eq_refl).
      reflexivity.
    - destruct (Complete.zero_selector_value lhs) as [value_l |] eqn:Hl;
        [| discriminate Hvalue].
      destruct (Complete.zero_selector_value rhs) as [value_r |] eqn:Hr;
        [| discriminate Hvalue].
      injection Hvalue as <-.
      rewrite (Complete.eval_expression_sum Γ (region, row) lhs rhs).
      rewrite (IHl value_l
        (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_introl Hs))) eq_refl).
      rewrite (IHr value_r
        (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_intror Hs))) eq_refl).
      reflexivity.
    - cbn [eval_expression].
      destruct (Complete.zero_selector_value lhs) as [value_l |] eqn:Hl;
        destruct (Complete.zero_selector_value rhs) as [value_r |] eqn:Hr.
      + injection Hvalue as <-.
        rewrite (IHl value_l
          (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_introl Hs))) eq_refl).
        rewrite (IHr value_r
          (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_intror Hs))) eq_refl).
        reflexivity.
      + destruct (Z.eqb value_l 0) eqn:Hzl; [| discriminate Hvalue].
        apply Z.eqb_eq in Hzl.
        subst value_l.
        injection Hvalue as <-.
        rewrite (IHl 0
          (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_introl Hs))) eq_refl).
        apply FieldRewrite.mul_zero_left.
      + destruct (Z.eqb value_r 0) eqn:Hzr; [| discriminate Hvalue].
        apply Z.eqb_eq in Hzr.
        subst value_r.
        injection Hvalue as <-.
        rewrite (IHr 0
          (fun s Hs => Hzero s (List.in_or_app _ _ _ (or_intror Hs))) eq_refl).
        apply FieldRewrite.mul_zero_right.
      + discriminate Hvalue.
    - destruct (Complete.zero_selector_value e) as [value' |] eqn:Hinner;
        [| discriminate Hvalue].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH value' Hzero eq_refl).
      reflexivity.
  Qed.

  (** *** Row shifts at a realized assignment

      Every reading of [realize idx rs grid] depends on [(region, row)] only
      through the absolute row [rs region + row], so any two index pairs with
      the same absolute row evaluate identically. *)

  Lemma realize_shift_selector (idx : Indices.t columns) (rs : RegionId -> Z)
      (grid : RawGrid.t) (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z) (selector : columns.(Columns.Selector)) :
    rs region1 + row1 = rs region2 + row2 ->
    eval_selector (realize idx rs grid) (region1, row1) selector =
    eval_selector (realize idx rs grid) (region2, row2) selector.
  Proof.
    intros Hrow.
    unfold eval_selector, realize.
    cbn [Assignment.selector].
    rewrite Hrow.
    reflexivity.
  Qed.

  Lemma realize_shift_expression (idx : Indices.t columns) (rs : RegionId -> Z)
      (grid : RawGrid.t) (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z) (e : Expression.t columns) :
    expression_instance_free e = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_expression (realize idx rs grid) (region1, row1) e =
    eval_expression (realize idx rs grid) (region2, row2) e.
  Proof.
    intros Hfree Hrow.
    rewrite (realize_eval_expression idx rs grid region1 row1 e Hfree).
    rewrite (realize_eval_expression idx rs grid region2 row2 e Hfree).
    rewrite Hrow.
    reflexivity.
  Qed.

  Lemma realize_shift_constraint (idx : Indices.t columns) (rs : RegionId -> Z)
      (grid : RawGrid.t) (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z) (c : Constraint.t columns) :
    constraint_instance_free c = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_constraint (realize idx rs grid) (region2, row2) c ->
    eval_constraint (realize idx rs grid) (region1, row1) c.
  Proof.
    revert row1 row2.
    induction c as
      [ selector c IH | lhs rhs | e | e range | lhs IHl rhs IHr
      | lhs rhs | e ];
      intros row1 row2 Hfree Hrow Heval;
      cbn [constraint_instance_free] in Hfree;
      cbn [eval_constraint] in Heval |- *.
    - intros Hnonzero.
      apply (IH row1 row2 Hfree Hrow).
      apply Heval.
      rewrite <- (realize_shift_selector idx rs grid region1 row1 region2 row2
        selector Hrow).
      exact Hnonzero.
    - apply andb_prop in Hfree.
      destruct Hfree as [Hl Hr].
      rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
        lhs Hl Hrow).
      rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
        rhs Hr Hrow).
      exact Heval.
    - rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
        e Hfree Hrow).
      exact Heval.
    - rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
        e Hfree Hrow).
      exact Heval.
    - apply andb_prop in Hfree.
      destruct Hfree as [Hl Hr].
      destruct Heval as [Heval | Heval].
      + left.
        exact (IHl row1 row2 Hl Hrow Heval).
      + right.
        exact (IHr row1 row2 Hr Hrow Heval).
    - apply andb_prop in Hfree.
      destruct Hfree as [Hl Hr].
      destruct Heval as [Heval | Heval].
      + left.
        rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
          lhs Hl Hrow).
        exact Heval.
      + right.
        rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
          rhs Hr Hrow).
        exact Heval.
    - rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
        e Hfree Hrow).
      exact Heval.
  Qed.

  Lemma realize_shift_lookup (idx : Indices.t columns) (rs : RegionId -> Z)
      (grid : RawGrid.t) (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z) (nb_table_rows : Z)
      (arg : LookupArgument.t columns) :
    lookup_argument_instance_free arg = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_lookup_argument (realize idx rs grid) (region2, row2) nb_table_rows arg ->
    eval_lookup_argument (realize idx rs grid) (region1, row1) nb_table_rows arg.
  Proof.
    unfold lookup_argument_instance_free.
    intros Hfree Hrow Heval.
    rewrite List.forallb_forall in Hfree.
    destruct Heval as (table_row & Hbound & Hpairs).
    exists table_row.
    split; [exact Hbound |].
    rewrite List.Forall_forall in Hpairs |- *.
    intros [e column] Hpair.
    specialize (Hpairs (e, column) Hpair).
    specialize (Hfree (e, column) Hpair).
    cbn [fst] in Hfree.
    cbv beta iota in Hpairs |- *.
    rewrite (realize_shift_expression idx rs grid region1 row1 region2 row2
      e Hfree Hrow).
    exact Hpairs.
  Qed.

  (** *** The ideal checker over a concatenated stream

      Only the third conjunct of [mock_prover_accepts] mentions the events,
      so a trailing block adds exactly its own copy obligations. *)
  Lemma mock_prover_accepts_app
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events tail : list Raw.Event.t) (grid : RawGrid.t) (table_rows : Z) :
    mock_prover_accepts system events grid table_rows ->
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) tail ->
      raw_cell_read grid left = raw_cell_read grid right) ->
    mock_prover_accepts system (events ++ tail) grid table_rows.
  Proof.
    intros (Hgates & Hlookups & Hcopies) Htail.
    split; [exact Hgates |].
    split; [exact Hlookups |].
    intros left right Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - exact (Hcopies left right Hin).
    - exact (Htail left right Hin).
  Qed.

  (** *** The replay-premise-free form of [operational_complete]

      [operational_complete] introduces and discards its replay premise; the
      restatement below drops it, so the checker can be reached at a grid
      obtained by replaying a *longer* stream (the Orchard stream carries the
      floor planner's constants tail).  The proof is the same composition of
      [relational_gates_to_mock], [relational_lookups_to_mock] and
      [layouter_copy_event_fact]. *)
  Lemma operational_complete_events {A : Set}
      (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns) (grid : RawGrid.t)
      (region0 : RegionId) :
    instance_free system ->
    flattening_ok system ->
    circuit_holds (realize idx rs grid) program system ->
    mock_prover_accepts (Configure.to_indexed idx system)
      (snd (V1.eval_layouter idx rs usable_rows program)) grid
      (layouter_table_rows program).
  Proof.
    intros Hinstance_free Hflattening_ok Hholds.
    destruct Hholds as (Hfacts & Hgates & Hlookups).
    split; [| split].
    - exact (relational_gates_to_mock idx rs grid system region0
        Hinstance_free Hflattening_ok Hgates).
    - exact (relational_lookups_to_mock idx rs grid system
        (layouter_table_rows program) region0 Hinstance_free Hlookups).
    - intros left right Hin.
      destruct (layouter_copy_event_fact idx rs usable_rows program left right
        Hin) as
        [ (left_cell & right_cell & Hleft & Hright & Hfact)
        | (cell & instance & row & Hleft & Hright & Hfact) ].
      + subst left right.
        rewrite <- !realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
      + subst left right.
        rewrite <- realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
  Qed.
End Generic.

(** ** The replay leaves the witness planes alone

    [apply_event] only ever calls [set_selector], [set_fixed] and
    [fill_fixed], so the advice and instance planes of the final grid are the
    initial ones, and a non-initial selector cell must carry an
    [EnableSelector] event. *)

Section ReplayPlanes.
  Lemma apply_event_advice (state state' : ReplayState.t) (event : Raw.Event.t)
      (column row : Z) :
    apply_event state event = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    destruct event as
      [name | name | name | name | column' row' annotation
      | column' row' annotation value | left_cell right_cell
      | column' from_row to_row value];
      cbn [apply_event];
      try (intros Heq; injection Heq as <-; reflexivity).
    - destruct (List.existsb (write_conflicts_write column' row' 1)
          state.(ReplayState.log).(Log.selectors));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
    - destruct (orb
          (List.existsb (write_conflicts_write column' row' value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (write_conflicts_fill column' row' value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
    - destruct (orb
          (List.existsb (fill_conflicts_write column' from_row to_row value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (fill_conflicts_fill column' from_row to_row value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
  Qed.

  Lemma apply_event_instance (state state' : ReplayState.t) (event : Raw.Event.t)
      (column row : Z) :
    apply_event state event = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_ column row.
  Proof.
    destruct event as
      [name | name | name | name | column' row' annotation
      | column' row' annotation value | left_cell right_cell
      | column' from_row to_row value];
      cbn [apply_event];
      try (intros Heq; injection Heq as <-; reflexivity).
    - destruct (List.existsb (write_conflicts_write column' row' 1)
          state.(ReplayState.log).(Log.selectors));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
    - destruct (orb
          (List.existsb (write_conflicts_write column' row' value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (write_conflicts_fill column' row' value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
    - destruct (orb
          (List.existsb (fill_conflicts_write column' from_row to_row value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (fill_conflicts_fill column' from_row to_row value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      reflexivity.
  Qed.

  Lemma apply_event_selector_source (state state' : ReplayState.t)
      (event : Raw.Event.t) (column row : Z) :
    apply_event state event = Some state' ->
    state'.(ReplayState.grid).(RawGrid.sel) column row =
      state.(ReplayState.grid).(RawGrid.sel) column row \/
    (exists annotation, event = Raw.Event.EnableSelector column row annotation).
  Proof.
    destruct event as
      [name | name | name | name | column' row' annotation
      | column' row' annotation value | left_cell right_cell
      | column' from_row to_row value];
      cbn [apply_event];
      try (intros Heq; injection Heq as <-; left; reflexivity).
    - destruct (List.existsb (write_conflicts_write column' row' 1)
          state.(ReplayState.log).(Log.selectors));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      cbn [ReplayState.grid RawGrid.set_selector RawGrid.sel].
      destruct (andb (column =? column') (row =? row')) eqn:Hpoint.
      + right.
        apply andb_prop in Hpoint.
        destruct Hpoint as [Hcolumn Hrow].
        apply Z.eqb_eq in Hcolumn, Hrow.
        subst column' row'.
        exists annotation.
        reflexivity.
      + left.
        reflexivity.
    - destruct (orb
          (List.existsb (write_conflicts_write column' row' value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (write_conflicts_fill column' row' value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      left.
      reflexivity.
    - destruct (orb
          (List.existsb (fill_conflicts_write column' from_row to_row value)
            state.(ReplayState.log).(Log.fixeds))
          (List.existsb (fill_conflicts_fill column' from_row to_row value)
            state.(ReplayState.log).(Log.fills)));
        intros Heq; [discriminate Heq |].
      injection Heq as <-.
      left.
      reflexivity.
  Qed.

  Lemma apply_events_log_advice (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Happly;
      cbn [apply_events_log] in Happly.
    - injection Happly as <-.
      reflexivity.
    - destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Happly].
      rewrite (IH state1 Happly).
      exact (apply_event_advice state state1 event column row Hevent).
  Qed.

  Lemma apply_events_log_instance (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_ column row.
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Happly;
      cbn [apply_events_log] in Happly.
    - injection Happly as <-.
      reflexivity.
    - destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Happly].
      rewrite (IH state1 Happly).
      exact (apply_event_instance state state1 event column row Hevent).
  Qed.

  Lemma apply_events_log_selector_source (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    state'.(ReplayState.grid).(RawGrid.sel) column row =
      state.(ReplayState.grid).(RawGrid.sel) column row \/
    (exists annotation,
      List.In (Raw.Event.EnableSelector column row annotation) events).
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Happly;
      cbn [apply_events_log] in Happly.
    - injection Happly as <-.
      left.
      reflexivity.
    - destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Happly].
      destruct (IH state1 Happly) as [Hrest | (annotation & Hin)].
      + destruct (apply_event_selector_source state state1 event column row
          Hevent) as [Hstep | (annotation & Hstep)].
        * left.
          rewrite Hrest.
          exact Hstep.
        * right.
          exists annotation.
          left.
          exact Hstep.
      + right.
        exists annotation.
        right.
        exact Hin.
  Qed.

  Lemma replay_advice_plane (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    final.(RawGrid.cell) Raw.ColumnKind.Advice column row =
    initial.(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal.
    injection Hfinal as <-.
    exact (apply_events_log_advice events _ state column row Hreplay).
  Qed.

  Lemma replay_instance_plane (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    final.(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
    initial.(RawGrid.cell) Raw.ColumnKind.Instance_ column row.
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal.
    injection Hfinal as <-.
    exact (apply_events_log_instance events _ state column row Hreplay).
  Qed.

  Lemma replay_selector_source (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    final.(RawGrid.sel) column row = initial.(RawGrid.sel) column row \/
    (exists annotation,
      List.In (Raw.Event.EnableSelector column row annotation) events).
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal.
    injection Hfinal as <-.
    exact (apply_events_log_selector_source events _ state column row Hreplay).
  Qed.

End ReplayPlanes.

(** ** A small positive trie

    The advice inversion table is a ~156 000-entry map; a binary trie keeps
    every lookup logarithmic inside the certificate's [vm_compute].  Only the
    forward direction is used (the certificate reports, per cell, the region
    the table returns), so no soundness lemma about the trie is needed. *)

Unset Uniform Inductive Parameters.

Inductive PTree (V : Set) : Set :=
| PLeaf : PTree V
| PNode : PTree V -> option V -> PTree V -> PTree V.
Arguments PLeaf {V}.
Arguments PNode {V}.

Fixpoint pget {V : Set} (key : positive) (tree : PTree V) : option V :=
  match tree with
  | PLeaf => None
  | PNode below value above =>
      match key with
      | xH => value
      | xO key => pget key below
      | xI key => pget key above
      end
  end.

Fixpoint pset {V : Set} (key : positive) (value : V) (tree : PTree V)
    : PTree V :=
  match key with
  | xH =>
      match tree with
      | PLeaf => PNode PLeaf (Some value) PLeaf
      | PNode below _ above => PNode below (Some value) above
      end
  | xO key =>
      match tree with
      | PLeaf => PNode (pset key value PLeaf) None PLeaf
      | PNode below o above => PNode (pset key value below) o above
      end
  | xI key =>
      match tree with
      | PLeaf => PNode PLeaf None (pset key value PLeaf)
      | PNode below o above => PNode below o (pset key value above)
      end
  end.

(** The trie key of a (column index, absolute row) pair.  Rows lie well
    inside [(-4096, 4096)] on the 2048-row Orchard grid; the key needs no
    injectivity proof — a collision would simply make the certificate
    report [false]. *)
Definition tkey (column row : Z) : positive :=
  Z.to_pos (1 + column * 8192 + (row + 4096)).

(** ** The Orchard names *)

Definition facts : list (Fact.t columns RegionId.t) :=
  OrchardHonestAssignment.facts.
Definition system : ConstraintSystem.t columns :=
  OrchardCompletenessCertificates.system.
Definition sel_eqb := OrchardDecidableEq.selector_eqb.
Definition fix_eqb := OrchardDecidableEq.fixed_eqb.
Definition lk_eqb := OrchardDecidableEq.lookup_eqb.
Definition reg_eqb := OrchardDecidableEq.region_id_eqb.

(** The reified extractions, hoisted into globals: a [vm_compute] run
    evaluates each once, where an inlined [Complete.enabled_points facts]
    would be re-evaluated at every call of the enclosing checker. *)
Definition enabled : list (Selector.t * RegionId.t * Z) :=
  Complete.enabled_points facts.
Definition fwrites : list (Fixed.t * RegionId.t * Z * Z) :=
  Complete.fixed_writes facts.
Definition tentries : list (Lookup.t * list Z * Z) :=
  Complete.table_entries facts.
Definition wfacts : list (Fact.t columns RegionId.t) :=
  Complete.witness_facts facts.

Definition Gtest : Assignment.t columns RegionId.t :=
  OrchardCompletenessInstanceDefs.Γtest.

(** *** The column-index inverses

    [Index.advice] and [Index.selector] are injective; the inverses below make
    that usable without a quadratic case analysis. *)

Definition advice_col_of (index : Z) : Advice.t :=
  match index with
  | 0 => Advice.A0 | 1 => Advice.A1 | 2 => Advice.A2 | 3 => Advice.A3
  | 4 => Advice.A4 | 5 => Advice.A5 | 6 => Advice.A6 | 7 => Advice.A7
  | 8 => Advice.A8 | _ => Advice.A9
  end.

Lemma advice_col_of_index (column : Advice.t) :
  advice_col_of (Index.advice column) = column.
Proof. destruct column; reflexivity. Qed.

Definition selector_of_index (index : Z) : Selector.t :=
  match index with
  | 0 => Selector.QOrchard | 1 => Selector.QAdd
  | 2 => Selector.QLookup | 3 => Selector.QRunning
  | 4 => Selector.QBitshift | 5 => Selector.QWitnessPoint
  | 6 => Selector.QWitnessPointNonId | 7 => Selector.QAddIncomplete
  | 8 => Selector.QEccAdd | 9 => Selector.QMulIncompleteHi1
  | 10 => Selector.QMulIncompleteHi2 | 11 => Selector.QMulIncompleteHi3
  | 12 => Selector.QMulIncompleteLo1 | 13 => Selector.QMulIncompleteLo2
  | 14 => Selector.QMulIncompleteLo3 | 15 => Selector.QMulDecomposeVar
  | 16 => Selector.QMulOverflow | 17 => Selector.QMulLsb
  | 18 => Selector.QMulFixedRunningSum | 19 => Selector.QMulFixedFull
  | 20 => Selector.QMulFixedShort | 21 => Selector.QMulFixedBaseField
  | 22 => Selector.QPoseidonFull | 23 => Selector.QPoseidonPartial
  | 24 => Selector.QPoseidonPadAndAdd | 25 => Selector.QSinsemilla1_1
  | 26 => Selector.QSinsemilla4_1 | 27 => Selector.QCondSwap1
  | 28 => Selector.QMerkleDecompose1 | 29 => Selector.QSinsemilla1_2
  | 30 => Selector.QSinsemilla4_2 | 31 => Selector.QCondSwap2
  | 32 => Selector.QMerkleDecompose2 | 33 => Selector.QCommitIvk
  | 34 => Selector.QNoteCommitOldB | 35 => Selector.QNoteCommitOldD
  | 36 => Selector.QNoteCommitOldE | 37 => Selector.QNoteCommitOldG
  | 38 => Selector.QNoteCommitOldH | 39 => Selector.QNoteCommitOldGd
  | 40 => Selector.QNoteCommitOldPkd | 41 => Selector.QNoteCommitOldValue
  | 42 => Selector.QNoteCommitOldRho | 43 => Selector.QNoteCommitOldPsi
  | 44 => Selector.QNoteCommitOldYCanon | 45 => Selector.QNoteCommitNewB
  | 46 => Selector.QNoteCommitNewD | 47 => Selector.QNoteCommitNewE
  | 48 => Selector.QNoteCommitNewG | 49 => Selector.QNoteCommitNewH
  | 50 => Selector.QNoteCommitNewGd | 51 => Selector.QNoteCommitNewPkd
  | 52 => Selector.QNoteCommitNewValue | 53 => Selector.QNoteCommitNewRho
  | 54 => Selector.QNoteCommitNewPsi | _ => Selector.QNoteCommitNewYCanon
  end.

Lemma selector_of_index_index (selector : Selector.t) :
  selector_of_index (Index.selector selector) = selector.
Proof. destruct selector; reflexivity. Qed.

Lemma selector_index_inj (selector1 selector2 : Selector.t) :
  Index.selector selector1 = Index.selector selector2 -> selector1 = selector2.
Proof.
  intros Heq.
  rewrite <- (selector_of_index_index selector1),
    <- (selector_of_index_index selector2), Heq.
  reflexivity.
Qed.

(** *** The cells the obligations read

    Per enabled point: the advice and fixed cells queried by the gates the
    point's selector guards, and by the lookup arguments the selector is
    mentioned by; plus the cells named by the witness facts. *)

Definition point_gate_adv (selector : Selector.t) (region : RegionId.t)
    (row : Z) : list (Advice.t * RegionId.t * Z) :=
  List.flat_map
    (fun gate =>
      List.flat_map
        (fun named_constraint =>
          match snd named_constraint with
          | Constraint.Select selector' body =>
              if sel_eqb selector selector' then constr_adv body region row
              else []
          | _ => []
          end)
        gate.(Gate.constraints))
    system.(ConstraintSystem.gates).

Definition point_gate_fix (selector : Selector.t) (region : RegionId.t)
    (row : Z) : list (Fixed.t * RegionId.t * Z) :=
  List.flat_map
    (fun gate =>
      List.flat_map
        (fun named_constraint =>
          match snd named_constraint with
          | Constraint.Select selector' body =>
              if sel_eqb selector selector' then constr_fix body region row
              else []
          | _ => []
          end)
        gate.(Gate.constraints))
    system.(ConstraintSystem.gates).

Definition point_lookup_adv (selector : Selector.t) (region : RegionId.t)
    (row : Z) : list (Advice.t * RegionId.t * Z) :=
  List.flat_map
    (fun arg =>
      if Complete.arg_mentions_selector sel_eqb selector arg
      then arg_adv arg region row else [])
    system.(ConstraintSystem.lookups).

Definition point_lookup_fix (selector : Selector.t) (region : RegionId.t)
    (row : Z) : list (Fixed.t * RegionId.t * Z) :=
  List.flat_map
    (fun arg =>
      if Complete.arg_mentions_selector sel_eqb selector arg
      then arg_fix arg region row else [])
    system.(ConstraintSystem.lookups).

Definition cell_adv (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
    : list (Advice.t * RegionId.t * Z) :=
  match Garden.Halo2.Synthesis.Cell.column cell with
  | Garden.Halo2.Synthesis.ColumnRef.Advice column =>
      [(column, Garden.Halo2.Synthesis.Cell.region cell,
        Garden.Halo2.Synthesis.Cell.row_offset cell)]
  | _ => []
  end.

Definition cell_fix (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
    : list (Fixed.t * RegionId.t * Z) :=
  match Garden.Halo2.Synthesis.Cell.column cell with
  | Garden.Halo2.Synthesis.ColumnRef.Fixed column =>
      [(column, Garden.Halo2.Synthesis.Cell.region cell,
        Garden.Halo2.Synthesis.Cell.row_offset cell)]
  | _ => []
  end.

Definition fact_adv (fact : Fact.t columns RegionId.t)
    : list (Advice.t * RegionId.t * Z) :=
  match fact with
  | Fact.CellsEqual left_cell right_cell => cell_adv left_cell ++ cell_adv right_cell
  | Fact.InstanceIs cell _ _ => cell_adv cell
  | Fact.CellIsConstant cell _ => cell_adv cell
  | _ => []
  end.

Definition fact_fix (fact : Fact.t columns RegionId.t)
    : list (Fixed.t * RegionId.t * Z) :=
  match fact with
  | Fact.CellsEqual left_cell right_cell => cell_fix left_cell ++ cell_fix right_cell
  | Fact.InstanceIs cell _ _ => cell_fix cell
  | Fact.CellIsConstant cell _ => cell_fix cell
  | _ => []
  end.

Definition adv_cells : list (Advice.t * RegionId.t * Z) :=
  List.flat_map
    (fun point =>
      match point with
      | (selector, region, row) =>
          point_gate_adv selector region row ++
          point_lookup_adv selector region row
      end)
    enabled
  ++ List.flat_map fact_adv wfacts.

Definition fix_cells : list (Fixed.t * RegionId.t * Z) :=
  List.flat_map
    (fun point =>
      match point with
      | (selector, region, row) =>
          point_gate_fix selector region row ++
          point_lookup_fix selector region row
      end)
    enabled
  ++ List.flat_map fact_fix wfacts.

(** ** The chosen free planes

    [orchard_advice] is the pullback of the honest advice plane along the
    placement: the inversion table [adv_tbl] sends a (column index, absolute
    row) pair to the region that owns it among the cells the obligations read.
    Outside those cells the value is irrelevant. *)

Definition adv_tbl : PTree RegionId.t :=
  Lists.List.fold_left
    (fun tree cell =>
      match cell with
      | (column, region, row) =>
          pset (tkey (Index.advice column) (region_start_of region + row))
            region tree
      end)
    adv_cells PLeaf.

Definition orchard_advice (column row : Z) : Z :=
  match pget (tkey column row) adv_tbl with
  | Some region =>
      Gtest.(Assignment.advice) (advice_col_of column) region
        (row - region_start_of region)
  | None => 0
  end.

Definition orchard_instance (_ : Z) (row : Z) : Z :=
  Gtest.(Assignment.instance_) Instance_.Primary row.

(** ** The input-independent certificates

    None of the scans below mentions the generator's values: they run over the
    reified synthesis facts, the configured system, the event stream and the
    placement only. *)

Definition adv_check (cell : Advice.t * RegionId.t * Z) : bool :=
  match cell with
  | (column, region, row) =>
      match pget (tkey (Index.advice column) (region_start_of region + row))
        adv_tbl with
      | Some region' => reg_eqb region region'
      | None => false
      end
  end.

Lemma adv_check_eq (column : Advice.t) (region : RegionId.t) (row : Z) :
  adv_check (column, region, row) =
  match pget (tkey (Index.advice column) (region_start_of region + row))
    adv_tbl with
  | Some region' => reg_eqb region region'
  | None => false
  end.
Proof. reflexivity. Qed.

(** Every advice cell an obligation reads is inverted exactly by the
    placement table. *)
Lemma adv_cert : List.forallb adv_check adv_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition fix_check (cell : Fixed.t * RegionId.t * Z) : bool :=
  match cell with
  | (column, region, row) =>
      match Complete.fixed_lookup fix_eqb reg_eqb fwrites column region row with
      | Some _ => true
      | None => false
      end
  end.

Lemma fix_check_eq (column : Fixed.t) (region : RegionId.t) (row : Z) :
  fix_check (column, region, row) =
  match Complete.fixed_lookup fix_eqb reg_eqb fwrites column region row with
  | Some _ => true
  | None => false
  end.
Proof. reflexivity. Qed.

(** Every fixed cell an obligation reads is written by the synthesis program,
    so its value is pinned by the replay. *)
Lemma fix_cert : List.forallb fix_check fix_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition enabled_raw : list (Z * Z) :=
  List.map
    (fun point =>
      match point with
      | (selector, region, row) =>
          (Index.selector selector, region_start_of region + row)
      end)
    enabled.

Definition enable_check (event : Raw.Event.t) : bool :=
  match event with
  | Raw.Event.EnableSelector column row _ =>
      List.existsb
        (fun pair => andb (column =? fst pair) (row =? snd pair)) enabled_raw
  | _ => true
  end.

(** Every selector enable of the stream sits at an enabled point's absolute
    row, under that point's selector index. *)
Lemma enable_cert : List.forallb enable_check orchard_events = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition body_check (named_constraint : option string * Constraint.t columns)
    : bool :=
  match snd named_constraint with
  | Constraint.Select _ body =>
      match constr_sels body with
      | [] => true
      | _ :: _ => false
      end
  | _ => false
  end.

(** No guarded gate body mentions a selector, so gate transfer never needs
    selector-plane agreement. *)
Lemma body_cert :
  List.forallb
    (fun gate => List.forallb body_check gate.(Gate.constraints))
    system.(ConstraintSystem.gates) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition table_check (column : Lookup.t) : bool :=
  match Complete.table_lookup lk_eqb tentries column with
  | Some (values, _) => 1024 <=? Z.of_nat (List.length values)
  | None => false
  end.

(** Each lookup column is loaded with at least [layouter_table_rows = 1024]
    entries, so the realized and honest lookup planes agree on every row the
    lookup arguments can witness. *)
Lemma table_cert :
  List.forallb table_check [Lookup.TableIdx; Lookup.TableX; Lookup.TableY]
    = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition selb_in (selector : Selector.t) (selectors : list Selector.t)
    : bool :=
  List.existsb (sel_eqb selector) selectors.

Definition emb (selector : Selector.t) (region : RegionId.t) (row : Z)
    : bool :=
  List.existsb (Complete.point_eqb sel_eqb reg_eqb (selector, region, row))
    enabled.

(** The selectors mentioned by the lookup arguments a given selector guards. *)
Definition point_lookup_sels (selector : Selector.t) : list Selector.t :=
  List.flat_map
    (fun arg =>
      if Complete.arg_mentions_selector sel_eqb selector arg
      then arg_sels arg else [])
    system.(ConstraintSystem.lookups).

(** The enabled points with their absolute rows precomputed: [region_start_of]
    is a linear scan of the placement list, so a quadratic certificate must
    never call it inside its inner loop. *)
Definition enabled_rows : list (Selector.t * RegionId.t * Z * Z) :=
  List.map
    (fun point =>
      match point with
      | (selector, region, row) =>
          (selector, region, row, region_start_of region + row)
      end)
    enabled.

Definition lookup_sel_row_check (selectors : list Selector.t)
    (region : RegionId.t) (row absolute : Z)
    (point : Selector.t * RegionId.t * Z * Z) : bool :=
  match point with
  | (selector', region', row', absolute') =>
      implb
        (andb (absolute' =? absolute) (selb_in selector' selectors))
        (andb (reg_eqb region' region) (row' =? row))
  end.

Definition lookup_sel_check (point : Selector.t * RegionId.t * Z * Z) : bool :=
  match point with
  | (selector, region, row, absolute) =>
      List.forallb
        (lookup_sel_row_check (point_lookup_sels selector) region row absolute)
        enabled_rows
  end.

Lemma lookup_sel_check_eq (selector : Selector.t) (region : RegionId.t)
    (row absolute : Z) :
  lookup_sel_check (selector, region, row, absolute) =
  List.forallb
    (lookup_sel_row_check (point_lookup_sels selector) region row absolute)
    enabled_rows.
Proof. reflexivity. Qed.

(** At an enabled point, every enabled point sharing its absolute row and
    carrying a selector that the point's lookup arguments mention is *the same*
    point — the restricted region-uniqueness the lookup transfer needs.  It
    fails for arbitrary selectors, which is why the gate side instead relies on
    the selector-freeness of the guarded bodies ([body_cert]). *)
Lemma lookup_sel_cert : List.forallb lookup_sel_check enabled_rows = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition const_entries : list (Raw.Cell.t * Z) :=
  List.flat_map
    (fun fact =>
      match fact with
      | Fact.CellIsConstant cell value =>
          [(Cell.to_raw Index.indices region_start_of cell, value)]
      | _ => []
      end)
    facts.

Definition const_check
    (binding : Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    : bool :=
  List.existsb
    (fun entry =>
      andb
        (raw_cell_eqb (fst entry)
          (Garden.Orchard.circuit_synthesis_constants.advice_cell
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.advice_column)
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.advice_row)))
        (snd entry =?
          binding.(Garden.Orchard.circuit_synthesis_constants
            .ConstantCopy.value)))
    const_entries.

(** Every constants-tail binding is covered by a [Fact.CellIsConstant] of the
    synthesis program: the reverse of [orchard_constants_materialized], which
    is what the tail's copy obligations need. *)
Lemma const_cert :
  List.forallb const_check
    Garden.Orchard.circuit_synthesis_constants.constant_copies = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** ** Plane readings

    Every reading below is a projection of a record literal, so each holds by
    [reflexivity] with no computation. *)

Lemma realize_selector_read (grid : RawGrid.t) (selector : Selector.t)
    (region : RegionId.t) (row : Z) :
  (realize Index.indices region_start_of grid).(Assignment.selector)
    selector region row =
  grid.(RawGrid.sel) (Index.selector selector) (region_start_of region + row).
Proof. reflexivity. Qed.

Lemma realize_advice_read (grid : RawGrid.t) (column : Advice.t)
    (region : RegionId.t) (row : Z) :
  (realize Index.indices region_start_of grid).(Assignment.advice)
    column region row =
  grid.(RawGrid.cell) Raw.ColumnKind.Advice (Index.advice column)
    (region_start_of region + row).
Proof. reflexivity. Qed.

Lemma realize_instance_read (grid : RawGrid.t) (column : Instance_.t) (row : Z) :
  (realize Index.indices region_start_of grid).(Assignment.instance_) column row =
  grid.(RawGrid.cell) Raw.ColumnKind.Instance_ (Index.instance_ column) row.
Proof. reflexivity. Qed.

Lemma initial_advice_read (advice instance_ : Z -> Z -> Z) (column row : Z) :
  (initial_grid advice instance_).(RawGrid.cell) Raw.ColumnKind.Advice column row
    = advice column row.
Proof. reflexivity. Qed.

Lemma initial_instance_read (advice instance_ : Z -> Z -> Z) (column row : Z) :
  (initial_grid advice instance_).(RawGrid.cell) Raw.ColumnKind.Instance_ column row
    = instance_ column row.
Proof. reflexivity. Qed.

Lemma initial_selector_read (advice instance_ : Z -> Z -> Z) (column row : Z) :
  (initial_grid advice instance_).(RawGrid.sel) column row = 0.
Proof. reflexivity. Qed.

Lemma Gtest_selector (selector : Selector.t) (region : RegionId.t) (row : Z) :
  Gtest.(Assignment.selector) selector region row =
  (if emb selector region row then 1 else 0).
Proof. reflexivity. Qed.

Lemma Gtest_fixed (column : Fixed.t) (region : RegionId.t) (row : Z) :
  Gtest.(Assignment.fixed) column region row =
  match Complete.fixed_lookup fix_eqb reg_eqb fwrites column region row with
  | Some value => value
  | None => 0
  end.
Proof. reflexivity. Qed.

Lemma Gtest_lookup (column : Lookup.t) (row : Z) :
  Gtest.(Assignment.lookup) column row =
  match Complete.table_lookup lk_eqb tentries column with
  | Some (values, default_value) => value_at_row row values default_value
  | None => 0
  end.
Proof. reflexivity. Qed.

Lemma Gtest_instance (column : Instance_.t) (row : Z) :
  Gtest.(Assignment.instance_) column row =
  Gtest.(Assignment.instance_) Instance_.Primary row.
Proof. destruct column; reflexivity. Qed.

(** ** Membership converses of the first-match lookups *)

Lemma fixed_lookup_In (writes : list (Fixed.t * RegionId.t * Z * Z))
    (column : Fixed.t) (region : RegionId.t) (offset value : Z) :
  Complete.fixed_lookup fix_eqb reg_eqb writes column region offset =
    Some value ->
  List.In (column, region, offset, value) writes.
Proof.
  induction writes as [| [ [ [column' region'] offset'] value'] writes IH];
    cbn [Complete.fixed_lookup].
  - intros Hlookup.
    discriminate Hlookup.
  - destruct (andb (andb (fix_eqb column column') (reg_eqb region region'))
      (Z.eqb offset offset')) eqn:Hmatch; intros Hlookup.
    + left.
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hmatch Hoffset].
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hcolumn Hregion].
      apply OrchardDecidableEq.fixed_eqb_eq in Hcolumn.
      apply OrchardDecidableEq.region_id_eqb_eq in Hregion.
      apply Z.eqb_eq in Hoffset.
      injection Hlookup as Hvalue.
      subst.
      reflexivity.
    + right.
      exact (IH Hlookup).
Qed.

Lemma fixed_writes_fact (fs : list (Fact.t columns RegionId.t))
    (column : Fixed.t) (region : RegionId.t) (offset value : Z) :
  List.In (column, region, offset, value) (Complete.fixed_writes fs) ->
  List.In (Fact.FixedIs column region offset value) fs.
Proof.
  induction fs as [| fact fs IH]; intros Hin.
  - destruct Hin.
  - destruct fact as
      [ selector' region' offset' | column' region' offset' value'
      | left_cell right_cell | cell instance row
      | column' values default_value | cell value' ];
      cbn [Complete.fixed_writes] in Hin;
      try (right; exact (IH Hin)).
    destruct Hin as [Heq | Hin].
    + left.
      injection Heq as <- <- <- <-.
      reflexivity.
    + right.
      exact (IH Hin).
Qed.

Lemma table_lookup_In (entries : list (Lookup.t * list Z * Z))
    (column : Lookup.t) (values : list Z) (default_value : Z) :
  Complete.table_lookup lk_eqb entries column = Some (values, default_value) ->
  List.In (column, values, default_value) entries.
Proof.
  induction entries as [| [ [column' values'] default_value'] entries IH];
    cbn [Complete.table_lookup].
  - intros Hlookup.
    discriminate Hlookup.
  - destruct (lk_eqb column column') eqn:Hmatch; intros Hlookup.
    + left.
      apply OrchardDecidableEq.lookup_eqb_eq in Hmatch.
      injection Hlookup as <- <-.
      subst.
      reflexivity.
    + right.
      exact (IH Hlookup).
Qed.

Lemma table_entries_fact (fs : list (Fact.t columns RegionId.t))
    (column : Lookup.t) (values : list Z) (default_value : Z) :
  List.In (column, values, default_value) (Complete.table_entries fs) ->
  List.In (Fact.LookupTableLoaded column values default_value) fs.
Proof.
  induction fs as [| fact fs IH]; intros Hin.
  - destruct Hin.
  - destruct fact as
      [ selector' region' offset' | column' region' offset' value'
      | left_cell right_cell | cell instance row
      | column' values' default_value' | cell value' ];
      cbn [Complete.table_entries] in Hin;
      try (right; exact (IH Hin)).
    destruct Hin as [Heq | Hin].
    + left.
      injection Heq as <- <- <-.
      reflexivity.
    + right.
      exact (IH Hin).
Qed.

(** ** Selector membership *)

Lemma selb_in_true (selector : Selector.t) (selectors : list Selector.t) :
  List.In selector selectors -> selb_in selector selectors = true.
Proof.
  intros Hin.
  unfold selb_in.
  apply List.existsb_exists.
  exists selector.
  split; [exact Hin |].
  apply OrchardDecidableEq.selector_eqb_refl.
Qed.

Lemma emb_complete (selector : Selector.t) (region : RegionId.t) (row : Z) :
  List.In (selector, region, row) enabled -> emb selector region row = true.
Proof.
  intros Hin.
  unfold emb.
  apply List.existsb_exists.
  exists (selector, region, row).
  split; [exact Hin |].
  cbn [Complete.point_eqb].
  unfold sel_eqb, reg_eqb.
  rewrite OrchardDecidableEq.selector_eqb_refl,
    OrchardDecidableEq.region_id_eqb_refl, Z.eqb_refl.
  reflexivity.
Qed.

Lemma emb_sound (selector : Selector.t) (region : RegionId.t) (row : Z) :
  emb selector region row = true -> List.In (selector, region, row) enabled.
Proof.
  unfold emb.
  intros Hmemb.
  apply List.existsb_exists in Hmemb.
  destruct Hmemb as ([ [selector' region'] offset'] & Hin & Heq).
  cbn [Complete.point_eqb] in Heq.
  apply andb_prop in Heq.
  destruct Heq as [Heq Hoffset].
  apply andb_prop in Heq.
  destruct Heq as [Hselector Hregion].
  apply OrchardDecidableEq.selector_eqb_eq in Hselector.
  apply OrchardDecidableEq.region_id_eqb_eq in Hregion.
  apply Z.eqb_eq in Hoffset.
  subst.
  exact Hin.
Qed.

Lemma enabled_rows_In (selector : Selector.t) (region : RegionId.t) (row : Z) :
  List.In (selector, region, row) enabled ->
  List.In (selector, region, row, region_start_of region + row) enabled_rows.
Proof.
  intros Hin.
  unfold enabled_rows.
  apply List.in_map_iff.
  exists (selector, region, row).
  split; [reflexivity | exact Hin].
Qed.

Lemma expr_sels_occurs (selector : Selector.t) (e : Expression.t columns) :
  List.In selector (expr_sels e) ->
  Complete.selector_occurs sel_eqb selector e = true.
Proof.
  induction e as
    [ value | selector' | column rotation | column rotation
    | column rotation | e IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | e IH scale ];
    intros Hin; cbn [expr_sels] in Hin;
    cbn [Complete.selector_occurs].
  - destruct Hin.
  - destruct Hin as [Heq | Hfalse]; [| destruct Hfalse].
    subst selector'.
    unfold sel_eqb.
    apply OrchardDecidableEq.selector_eqb_refl.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin.
  - exact (IH Hin).
  - apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + rewrite (IHl Hin).
      reflexivity.
    + rewrite (IHr Hin).
      apply Bool.orb_true_r.
  - apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + rewrite (IHl Hin).
      reflexivity.
    + rewrite (IHr Hin).
      apply Bool.orb_true_r.
  - exact (IH Hin).
Qed.

Lemma arg_sels_mentions (selector : Selector.t)
    (arg : LookupArgument.t columns) :
  List.In selector (arg_sels arg) ->
  Complete.arg_mentions_selector sel_eqb selector arg = true.
Proof.
  unfold arg_sels, Complete.arg_mentions_selector.
  intros Hin.
  apply List.in_flat_map in Hin.
  destruct Hin as ([e column] & Hpair & Hsel).
  apply List.existsb_exists.
  exists (e, column).
  split; [exact Hpair |].
  cbn [fst] in Hsel.
  cbv beta iota.
  exact (expr_sels_occurs selector e Hsel).
Qed.

Lemma point_lookup_sels_In (selector : Selector.t)
    (arg : LookupArgument.t columns) (selector' : Selector.t) :
  List.In arg system.(ConstraintSystem.lookups) ->
  Complete.arg_mentions_selector sel_eqb selector arg = true ->
  List.In selector' (arg_sels arg) ->
  List.In selector' (point_lookup_sels selector).
Proof.
  intros Harg Hmentions Hsel.
  unfold point_lookup_sels.
  apply List.in_flat_map.
  exists arg.
  split; [exact Harg |].
  rewrite Hmentions.
  exact Hsel.
Qed.

(** The restricted region-uniqueness, read off [lookup_sel_cert]. *)
Lemma lookup_sel_unique (selector : Selector.t) (region : RegionId.t) (row : Z)
    (selector' : Selector.t) (region' : RegionId.t) (row' : Z) :
  List.In (selector, region, row) enabled ->
  List.In (selector', region', row') enabled ->
  List.In selector' (point_lookup_sels selector) ->
  region_start_of region' + row' = region_start_of region + row ->
  List.In (selector', region, row) enabled.
Proof.
  intros Hpoint Hpoint' Hsel Hrow.
  pose proof (proj1 (List.forallb_forall lookup_sel_check enabled_rows)
    lookup_sel_cert (selector, region, row, region_start_of region + row)
    (enabled_rows_In selector region row Hpoint)) as Hcheck.
  rewrite lookup_sel_check_eq in Hcheck.
  pose proof (proj1 (List.forallb_forall _ enabled_rows) Hcheck
    (selector', region', row', region_start_of region' + row')
    (enabled_rows_In selector' region' row' Hpoint')) as Hrowcheck.
  cbn [lookup_sel_row_check] in Hrowcheck.
  rewrite Hrow, Z.eqb_refl in Hrowcheck.
  rewrite (selb_in_true selector' (point_lookup_sels selector) Hsel)
    in Hrowcheck.
  cbn [andb implb] in Hrowcheck.
  apply andb_prop in Hrowcheck.
  destruct Hrowcheck as [Hregion Hoffset].
  apply OrchardDecidableEq.region_id_eqb_eq in Hregion.
  apply Z.eqb_eq in Hoffset.
  subst.
  exact Hpoint'.
Qed.

(** ** Membership in the read-cell families *)

Lemma point_gate_adv_In (selector : Selector.t) (region : RegionId.t) (row : Z)
    (gate : Gate.t columns) (name : option string)
    (body : Constraint.t columns) (cell : Advice.t * RegionId.t * Z) :
  List.In gate system.(ConstraintSystem.gates) ->
  List.In (name, Constraint.Select selector body) gate.(Gate.constraints) ->
  List.In cell (constr_adv body region row) ->
  List.In cell (point_gate_adv selector region row).
Proof.
  intros Hgate Hconstraint Hcell.
  unfold point_gate_adv.
  apply List.in_flat_map.
  exists gate.
  split; [exact Hgate |].
  apply List.in_flat_map.
  exists (name, Constraint.Select selector body).
  split; [exact Hconstraint |].
  cbn [snd].
  unfold sel_eqb.
  rewrite OrchardDecidableEq.selector_eqb_refl.
  exact Hcell.
Qed.

Lemma point_gate_fix_In (selector : Selector.t) (region : RegionId.t) (row : Z)
    (gate : Gate.t columns) (name : option string)
    (body : Constraint.t columns) (cell : Fixed.t * RegionId.t * Z) :
  List.In gate system.(ConstraintSystem.gates) ->
  List.In (name, Constraint.Select selector body) gate.(Gate.constraints) ->
  List.In cell (constr_fix body region row) ->
  List.In cell (point_gate_fix selector region row).
Proof.
  intros Hgate Hconstraint Hcell.
  unfold point_gate_fix.
  apply List.in_flat_map.
  exists gate.
  split; [exact Hgate |].
  apply List.in_flat_map.
  exists (name, Constraint.Select selector body).
  split; [exact Hconstraint |].
  cbn [snd].
  unfold sel_eqb.
  rewrite OrchardDecidableEq.selector_eqb_refl.
  exact Hcell.
Qed.

Lemma point_lookup_adv_In (selector : Selector.t) (region : RegionId.t)
    (row : Z) (arg : LookupArgument.t columns)
    (cell : Advice.t * RegionId.t * Z) :
  List.In arg system.(ConstraintSystem.lookups) ->
  Complete.arg_mentions_selector sel_eqb selector arg = true ->
  List.In cell (arg_adv arg region row) ->
  List.In cell (point_lookup_adv selector region row).
Proof.
  intros Harg Hmentions Hcell.
  unfold point_lookup_adv.
  apply List.in_flat_map.
  exists arg.
  split; [exact Harg |].
  rewrite Hmentions.
  exact Hcell.
Qed.

Lemma point_lookup_fix_In (selector : Selector.t) (region : RegionId.t)
    (row : Z) (arg : LookupArgument.t columns)
    (cell : Fixed.t * RegionId.t * Z) :
  List.In arg system.(ConstraintSystem.lookups) ->
  Complete.arg_mentions_selector sel_eqb selector arg = true ->
  List.In cell (arg_fix arg region row) ->
  List.In cell (point_lookup_fix selector region row).
Proof.
  intros Harg Hmentions Hcell.
  unfold point_lookup_fix.
  apply List.in_flat_map.
  exists arg.
  split; [exact Harg |].
  rewrite Hmentions.
  exact Hcell.
Qed.

Lemma adv_cells_point (selector : Selector.t) (region : RegionId.t) (row : Z)
    (cell : Advice.t * RegionId.t * Z) :
  List.In (selector, region, row) enabled ->
  List.In cell
    (point_gate_adv selector region row ++ point_lookup_adv selector region row) ->
  List.In cell adv_cells.
Proof.
  intros Hpoint Hcell.
  unfold adv_cells.
  apply List.in_or_app.
  left.
  apply List.in_flat_map.
  exists (selector, region, row).
  split; [exact Hpoint | exact Hcell].
Qed.

Lemma fix_cells_point (selector : Selector.t) (region : RegionId.t) (row : Z)
    (cell : Fixed.t * RegionId.t * Z) :
  List.In (selector, region, row) enabled ->
  List.In cell
    (point_gate_fix selector region row ++ point_lookup_fix selector region row) ->
  List.In cell fix_cells.
Proof.
  intros Hpoint Hcell.
  unfold fix_cells.
  apply List.in_or_app.
  left.
  apply List.in_flat_map.
  exists (selector, region, row).
  split; [exact Hpoint | exact Hcell].
Qed.

Lemma adv_cells_fact (fact : Fact.t columns RegionId.t)
    (cell : Advice.t * RegionId.t * Z) :
  List.In fact wfacts ->
  List.In cell (fact_adv fact) ->
  List.In cell adv_cells.
Proof.
  intros Hfact Hcell.
  unfold adv_cells.
  apply List.in_or_app.
  right.
  apply List.in_flat_map.
  exists fact.
  split; [exact Hfact | exact Hcell].
Qed.

Lemma fix_cells_fact (fact : Fact.t columns RegionId.t)
    (cell : Fixed.t * RegionId.t * Z) :
  List.In fact wfacts ->
  List.In cell (fact_fix fact) ->
  List.In cell fix_cells.
Proof.
  intros Hfact Hcell.
  unfold fix_cells.
  apply List.in_or_app.
  right.
  apply List.in_flat_map.
  exists fact.
  split; [exact Hfact | exact Hcell].
Qed.

Lemma body_sels_nil (gate : Gate.t columns) (name : option string)
    (selector : Selector.t) (body : Constraint.t columns) :
  List.In gate system.(ConstraintSystem.gates) ->
  List.In (name, Constraint.Select selector body) gate.(Gate.constraints) ->
  constr_sels body = [].
Proof.
  intros Hgate Hconstraint.
  pose proof (proj1 (List.forallb_forall _ _) body_cert gate Hgate) as Hgatecheck.
  pose proof (proj1 (List.forallb_forall body_check _) Hgatecheck
    (name, Constraint.Select selector body) Hconstraint) as Hcheck.
  unfold body_check in Hcheck.
  cbn [snd] in Hcheck.
  destruct (constr_sels body) as [| s ss];
    [reflexivity | discriminate Hcheck].
Qed.

(** ** The lookup padding tuple, read off the defaults certificate *)

Lemma defaults_pair (arg : LookupArgument.t columns)
    (e : Expression.t columns) (column : Lookup.t) :
  List.In arg system.(ConstraintSystem.lookups) ->
  List.In (e, column) arg.(LookupArgument.pairs) ->
  exists value values default_value,
    Complete.zero_selector_value e = Some value /\
    Complete.table_lookup lk_eqb tentries column = Some (values, default_value) /\
    value = value_at_row 0 values default_value.
Proof.
  intros Harg Hpair.
  unfold system in Harg.
  pose proof OrchardCompletenessCertificates.lookup_defaults_certificate as Hd.
  unfold Complete.lookup_defaults_ok in Hd.
  destruct (OrchardCompletenessCertificates.system.(ConstraintSystem.lookups))
    as [| arg0 args] eqn:Hsys.
  - destruct Harg.
  - apply andb_prop in Hd.
    destruct Hd as [_ Hd].
    rewrite List.forallb_forall in Hd.
    specialize (Hd arg Harg).
    rewrite List.forallb_forall in Hd.
    specialize (Hd (e, column) Hpair).
    cbv beta iota in Hd.
    destruct (Complete.zero_selector_value e) as [value |] eqn:Hzero;
      destruct (Complete.table_lookup OrchardCompletenessCertificates.lookup_eqb
        (Complete.table_entries OrchardCompletenessCertificates.facts) column)
        as [ [values default_value] |] eqn:Htable;
      try discriminate Hd.
    apply Z.eqb_eq in Hd.
    exists value, values, default_value.
    split; [reflexivity |].
    split; [exact Htable | exact Hd].
Qed.

Lemma system_lookup_arg_instance_free (arg : LookupArgument.t columns) :
  List.In arg system.(ConstraintSystem.lookups) ->
  lookup_argument_instance_free arg = true.
Proof.
  intros Harg.
  pose proof orchard_instance_free as Hfree.
  unfold instance_free, instance_free_b in Hfree.
  apply andb_prop in Hfree.
  destruct Hfree as [_ Hlookups].
  rewrite List.forallb_forall in Hlookups.
  exact (Hlookups arg Harg).
Qed.

Lemma raw_instance_read (grid : RawGrid.t) (instance : Instance_.t) (row : Z) :
  raw_cell_read grid (Cell.instance_raw Index.indices instance row) =
  (realize Index.indices region_start_of grid).(Assignment.instance_) instance row.
Proof. reflexivity. Qed.

Lemma to_event_list_inv
    (bindings : list Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    (event : Raw.Event.t) :
  List.In event
    (Garden.Orchard.circuit_synthesis_constants.to_event_list bindings) ->
  exists binding,
    List.In binding bindings /\
    List.In event
      (Garden.Orchard.circuit_synthesis_constants.to_events binding).
Proof.
  induction bindings as [| binding bindings IH]; intros Hin.
  - destruct Hin.
  - cbn [Garden.Orchard.circuit_synthesis_constants.to_event_list] in Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exists binding.
      split; [left; reflexivity | exact Hin].
    + destruct (IH Hin) as (binding' & Hb & He).
      exists binding'.
      split; [right; exact Hb | exact He].
Qed.

(** ** The grid identification

    Everything below is relative to a grid [g] obtained by replaying the full
    Orchard stream on the chosen honest planes. *)

Section Grid.
  Variable g : RawGrid.t.
  Hypothesis Hreplay :
    apply_events orchard_events
      (initial_grid orchard_advice orchard_instance) = Some g.

  (** The program-determined facts hold outright: this is the half the
      soundness direction already carries. *)
  Lemma determined_hold :
    interpret_facts (realize Index.indices region_start_of g)
      (determined_facts facts).
  Proof.
    apply (determined_facts_hold_incl Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows
      Garden.Orchard.circuit.synthesize orchard_events
      (initial_grid orchard_advice orchard_instance) g Hreplay).
    unfold orchard_events, orchard_synthesis_events.
    apply List.incl_appl, List.incl_refl.
  Qed.

  Lemma selector_one (selector : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (selector, region, row) enabled ->
    (realize Index.indices region_start_of g).(Assignment.selector)
      selector region row = 1.
  Proof.
    intros Hin.
    exact (interpret_facts_In _ (Fact.SelectorOn selector region row) _
      determined_hold
      (proj2 (List.filter_In _ _ _)
        (conj (OrchardCompletenessCertificates.enabled_points_sound facts
          selector region row Hin) eq_refl))).
  Qed.

  (** A non-zero selector cell of the replayed grid comes from an
      [EnableSelector] event, which [enable_cert] places at an enabled
      point. *)
  Lemma enable_source (selector : Selector.t) (row : Z) :
    g.(RawGrid.sel) (Index.selector selector) row <> 0 ->
    exists region offset,
      List.In (selector, region, offset) enabled /\
      region_start_of region + offset = row.
  Proof.
    intros Hnonzero.
    destruct (replay_selector_source orchard_events
      (initial_grid orchard_advice orchard_instance) g
      (Index.selector selector) row Hreplay) as [Heq | (annotation & Hin)].
    - exfalso.
      apply Hnonzero.
      rewrite Heq.
      apply initial_selector_read.
    - pose proof (proj1 (List.forallb_forall enable_check orchard_events)
        enable_cert _ Hin) as Hcheck.
      cbn [enable_check] in Hcheck.
      apply List.existsb_exists in Hcheck.
      destruct Hcheck as (pair & Hpair & Hmatch).
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hcolumn Hrow].
      apply Z.eqb_eq in Hcolumn.
      apply Z.eqb_eq in Hrow.
      unfold enabled_raw in Hpair.
      apply List.in_map_iff in Hpair.
      destruct Hpair as ([ [selector' region] offset] & Heq & Hin').
      subst pair.
      cbn [fst snd] in Hcolumn, Hrow.
      apply selector_index_inj in Hcolumn.
      subst selector'.
      exists region, offset.
      split; [exact Hin' | symmetry; exact Hrow].
  Qed.

  Lemma selector_zero (selector : Selector.t) (row : Z) :
    (forall region offset,
      List.In (selector, region, offset) enabled ->
      region_start_of region + offset <> row) ->
    g.(RawGrid.sel) (Index.selector selector) row = 0.
  Proof.
    intros Hnone.
    destruct (Z.eq_dec (g.(RawGrid.sel) (Index.selector selector) row) 0)
      as [Hzero | Hnonzero]; [exact Hzero |].
    exfalso.
    destruct (enable_source selector row Hnonzero)
      as (region & offset & Hin & Hrow).
    exact (Hnone region offset Hin Hrow).
  Qed.

  (** The advice plane: the replay never writes it, so the realized reading is
      the chosen plane, which the inversion certificate sends back to the
      honest cell. *)
  Lemma advice_agree (column : Advice.t) (region : RegionId.t) (row : Z) :
    List.In (column, region, row) adv_cells ->
    (realize Index.indices region_start_of g).(Assignment.advice)
      column region row =
    Gtest.(Assignment.advice) column region row.
  Proof.
    intros Hin.
    pose proof (proj1 (List.forallb_forall adv_check adv_cells) adv_cert
      (column, region, row) Hin) as Hcheck.
    rewrite adv_check_eq in Hcheck.
    rewrite realize_advice_read.
    rewrite (replay_advice_plane orchard_events
      (initial_grid orchard_advice orchard_instance) g
      (Index.advice column) (region_start_of region + row) Hreplay).
    rewrite initial_advice_read.
    unfold orchard_advice.
    destruct (pget (tkey (Index.advice column) (region_start_of region + row))
      adv_tbl) as [region' |] eqn:Htable.
    - cbv beta iota in Hcheck.
      apply OrchardDecidableEq.region_id_eqb_eq in Hcheck.
      subst region'.
      rewrite advice_col_of_index.
      replace (region_start_of region + row - region_start_of region) with row
        by lia.
      reflexivity.
    - discriminate Hcheck.
  Qed.

  (** The fixed plane: every read cell is program-written, so the replay pins
      it to the same value the honest first-write plane holds. *)
  Lemma fixed_agree (column : Fixed.t) (region : RegionId.t) (row : Z) :
    List.In (column, region, row) fix_cells ->
    (realize Index.indices region_start_of g).(Assignment.fixed)
      column region row =
    Gtest.(Assignment.fixed) column region row.
  Proof.
    intros Hin.
    pose proof (proj1 (List.forallb_forall fix_check fix_cells) fix_cert
      (column, region, row) Hin) as Hcheck.
    rewrite fix_check_eq in Hcheck.
    rewrite Gtest_fixed.
    destruct (Complete.fixed_lookup fix_eqb reg_eqb fwrites column region row)
      as [value |] eqn:Hlookup.
    - exact (interpret_facts_In _ (Fact.FixedIs column region row value) _
        determined_hold
        (proj2 (List.filter_In _ _ _)
          (conj (fixed_writes_fact facts column region row value
            (fixed_lookup_In fwrites column region row value Hlookup))
            eq_refl))).
    - discriminate Hcheck.
  Qed.

  (** The lookup plane: the loaded rows [0 .. 1024) are program-determined and
      the tables carry at least that many entries. *)
  Lemma lookup_agree (column : Lookup.t) (row : Z) :
    0 <= row < 1024 ->
    (realize Index.indices region_start_of g).(Assignment.lookup) column row =
    Gtest.(Assignment.lookup) column row.
  Proof.
    intros Hrow.
    assert (Hcheck : table_check column = true).
    { apply (proj1 (List.forallb_forall table_check _) table_cert).
      destruct column; cbn [List.In]; auto. }
    unfold table_check in Hcheck.
    rewrite Gtest_lookup.
    destruct (Complete.table_lookup lk_eqb tentries column)
      as [ [values default_value] |] eqn:Htable.
    - cbv beta iota in Hcheck.
      apply Z.leb_le in Hcheck.
      pose proof (interpret_facts_In _
        (Fact.LookupTableLoaded column values default_value) _ determined_hold
        (proj2 (List.filter_In _ _ _)
          (conj (table_entries_fact facts column values default_value
            (table_lookup_In tentries column values default_value Htable))
            eq_refl))) as Hload.
      cbn [interpret_fact] in Hload.
      apply Hload.
      lia.
    - discriminate Hcheck.
  Qed.

  Lemma instance_agree (column : Instance_.t) (row : Z) :
    (realize Index.indices region_start_of g).(Assignment.instance_) column row =
    Gtest.(Assignment.instance_) column row.
  Proof.
    rewrite realize_instance_read.
    rewrite (replay_instance_plane orchard_events
      (initial_grid orchard_advice orchard_instance) g
      (Index.instance_ column) row Hreplay).
    rewrite initial_instance_read.
    unfold orchard_instance.
    symmetry.
    apply Gtest_instance.
  Qed.

  (** The C1 relational instance. *)
  Lemma test_holds :
    circuit_holds Gtest Garden.Orchard.circuit.synthesize system.
  Proof.
    exact (proj1 OrchardCompletenessInstance.orchard_completeness_instance).
  Qed.

  (** *** The gate obligations *)

  Lemma gates_hold :
    satisfies_gates (realize Index.indices region_start_of g) system.
  Proof.
    intros region row.
    apply Complete.eval_gates_forall.
    intros gate Hgate.
    unfold eval_gate.
    apply Complete.eval_constraints_forall.
    intros [name constraint] Hconstraint.
    pose proof OrchardCompletenessCertificates.selector_guarded_certificate
      as Hguarded.
    unfold Complete.selector_guarded in Hguarded.
    pose proof (proj1 (List.forallb_forall _ _) Hguarded gate Hgate)
      as Hgateguard.
    pose proof (proj1 (List.forallb_forall _ _) Hgateguard (name, constraint)
      Hconstraint) as Hguard.
    cbv beta iota in Hguard.
    destruct constraint as
      [ selector body | lhs rhs | e | e range | lhs rhs | left right | e ];
      cbn [Complete.constraint_guarded] in Hguard; try discriminate Hguard.
    cbn [eval_named_constraint eval_constraint].
    intros Hnonzero.
    assert (Hraw : g.(RawGrid.sel) (Index.selector selector)
      (region_start_of region + row) <> 0).
    { intros Hzero.
      apply Hnonzero.
      unfold eval_selector.
      rewrite realize_selector_read, Hzero.
      apply Zmod_0_l. }
    destruct (enable_source selector (region_start_of region + row) Hraw)
      as (region0 & row0 & Hpoint & Hrow0).
    assert (Hfree : constraint_instance_free body = true).
    { pose proof (system_gate_constraint_instance_free system gate name
        (Constraint.Select selector body) orchard_instance_free Hgate
        Hconstraint) as Hfree'.
      cbn [constraint_instance_free] in Hfree'.
      exact Hfree'. }
    apply (realize_shift_constraint Index.indices region_start_of g
      region row region0 row0 body Hfree ltac:(lia)).
    apply (eval_constraint_agree Gtest (realize Index.indices region_start_of g)
      (fun column row' => eq_sym (instance_agree column row')) region0 row0 body).
    - intros column' region' offset' Hcell.
      symmetry.
      apply advice_agree.
      apply (adv_cells_point selector region0 row0 _ Hpoint).
      apply List.in_or_app.
      left.
      exact (point_gate_adv_In selector region0 row0 gate name body _
        Hgate Hconstraint Hcell).
    - intros column' region' offset' Hcell.
      symmetry.
      apply fixed_agree.
      apply (fix_cells_point selector region0 row0 _ Hpoint).
      apply List.in_or_app.
      left.
      exact (point_gate_fix_In selector region0 row0 gate name body _
        Hgate Hconstraint Hcell).
    - rewrite (body_sels_nil gate name selector body Hgate Hconstraint).
      intros selector' Hselector'.
      destruct Hselector'.
    - destruct test_holds as (_ & Htestgates & _).
      specialize (Htestgates region0 row0).
      pose proof (eval_gates_In Gtest (region0, row0) gate
        system.(ConstraintSystem.gates) Hgate Htestgates) as Hgateeval.
      unfold eval_gate in Hgateeval.
      pose proof (Complete.eval_constraints_In Gtest (region0, row0)
        (name, Constraint.Select selector body) gate.(Gate.constraints)
        Hconstraint Hgateeval) as Htest.
      cbn [eval_named_constraint eval_constraint] in Htest.
      apply Htest.
      apply enabled_nonzero.
      rewrite Gtest_selector, (emb_complete selector region0 row0 Hpoint).
      reflexivity.
  Qed.

  (** *** The lookup obligations *)

  Lemma lookups_hold :
    satisfies_lookups (realize Index.indices region_start_of g)
      (layouter_table_rows Garden.Orchard.circuit.synthesize) system.
  Proof.
    intros region row.
    apply List.Forall_forall.
    intros arg Harg.
    destruct (List.existsb
      (fun selector =>
        negb (Z.eqb
          (eval_selector (realize Index.indices region_start_of g) (region, row)
            selector) 0))
      (arg_sels arg)) eqn:Hhot.
    - (* Some selector of the argument is on here. *)
      apply List.existsb_exists in Hhot.
      destruct Hhot as (selector & Hselector & Hnonzero).
      apply Bool.negb_true_iff, Z.eqb_neq in Hnonzero.
      assert (Hraw : g.(RawGrid.sel) (Index.selector selector)
        (region_start_of region + row) <> 0).
      { intros Hzero.
        apply Hnonzero.
        unfold eval_selector.
        rewrite realize_selector_read, Hzero.
        apply Zmod_0_l. }
      destruct (enable_source selector (region_start_of region + row) Hraw)
        as (region0 & row0 & Hpoint & Hrow0).
      pose proof (arg_sels_mentions selector arg Hselector) as Hmentions.
      apply (realize_shift_lookup Index.indices region_start_of g
        region row region0 row0 _ arg
        (system_lookup_arg_instance_free arg Harg) ltac:(lia)).
      apply (eval_lookup_argument_agree Gtest
        (realize Index.indices region_start_of g)
        (fun column row' => eq_sym (instance_agree column row'))
        region0 row0 _ arg).
      + intros column' region' offset' Hcell.
        symmetry.
        apply advice_agree.
        apply (adv_cells_point selector region0 row0 _ Hpoint).
        apply List.in_or_app.
        right.
        exact (point_lookup_adv_In selector region0 row0 arg _
          Harg Hmentions Hcell).
      + intros column' region' offset' Hcell.
        symmetry.
        apply fixed_agree.
        apply (fix_cells_point selector region0 row0 _ Hpoint).
        apply List.in_or_app.
        right.
        exact (point_lookup_fix_In selector region0 row0 arg _
          Harg Hmentions Hcell).
      + intros selector' Hselector'.
        rewrite Gtest_selector.
        destruct (emb selector' region0 row0) eqn:Hmemb.
        * symmetry.
          exact (selector_one selector' region0 row0
            (emb_sound selector' region0 row0 Hmemb)).
        * rewrite realize_selector_read.
          symmetry.
          apply selector_zero.
          intros region1 offset1 Hin1 Hrow1.
          assert (Hin2 : List.In (selector', region0, row0) enabled).
          { exact (lookup_sel_unique selector region0 row0 selector'
              region1 offset1 Hpoint Hin1
              (point_lookup_sels_In selector arg selector' Harg Hmentions
                Hselector')
              Hrow1). }
          rewrite (emb_complete selector' region0 row0 Hin2) in Hmemb.
          discriminate Hmemb.
      + intros column' table_row Hbound.
        rewrite OrchardCompletenessCertificates.layouter_table_rows_eq in Hbound.
        symmetry.
        exact (lookup_agree column' table_row Hbound).
      + destruct test_holds as (_ & _ & Htestlookups).
        specialize (Htestlookups region0 row0).
        rewrite List.Forall_forall in Htestlookups.
        exact (Htestlookups arg Harg).
    - (* Padding row: table row 0 witnesses the argument. *)
      exists 0.
      split;
        [ rewrite OrchardCompletenessCertificates.layouter_table_rows_eq; lia |].
      apply List.Forall_forall.
      intros [e column] Hpair.
      cbv beta iota.
      destruct (defaults_pair arg e column Harg Hpair)
        as (value & values & default_value & Hzero & Htable & Hvalue).
      rewrite (zero_selector_value_agree
        (realize Index.indices region_start_of g) region row e value
        ltac:(intros selector' Hselector';
          assert (Hin : List.In selector' (arg_sels arg)) by
            (unfold arg_sels; apply List.in_flat_map; exists (e, column);
              split; [exact Hpair | exact Hselector']);
          pose proof (existsb_false_forall _ _ Hhot selector' Hin) as Hoff;
          apply Bool.negb_false_iff, Z.eqb_eq in Hoff;
          exact Hoff)
        Hzero).
      rewrite (lookup_agree column 0 ltac:(lia)).
      rewrite Gtest_lookup, Htable.
      exact Hvalue.
  Qed.

  (** *** The witness facts and the copy obligations *)

  Lemma cell_agree_of (fact : Fact.t columns RegionId.t)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    List.In fact wfacts ->
    List.incl (cell_adv cell) (fact_adv fact) ->
    List.incl (cell_fix cell) (fact_fix fact) ->
    eval_cell Gtest cell =
    eval_cell (realize Index.indices region_start_of g) cell.
  Proof.
    intros Hfact Hadv Hfix.
    apply (eval_cell_agree Gtest (realize Index.indices region_start_of g)
      (fun column row => eq_sym (instance_agree column row)) cell).
    - intros column Hcolumn.
      symmetry.
      apply advice_agree.
      apply (adv_cells_fact fact); [exact Hfact |].
      apply Hadv.
      unfold cell_adv.
      rewrite Hcolumn.
      left.
      reflexivity.
    - intros column Hcolumn.
      symmetry.
      apply fixed_agree.
      apply (fix_cells_fact fact); [exact Hfact |].
      apply Hfix.
      unfold cell_fix.
      rewrite Hcolumn.
      left.
      reflexivity.
  Qed.

  Lemma witness_fact_holds (fact : Fact.t columns RegionId.t) :
    List.In fact wfacts ->
    interpret_fact (realize Index.indices region_start_of g) fact.
  Proof.
    intros Hfact.
    pose proof (proj1 (List.filter_In _ _ _) Hfact) as Hsplit.
    destruct Hsplit as [Hin Hwitness].
    destruct test_holds as (Htestfacts & _ & _).
    pose proof (interpret_facts_In Gtest fact facts Htestfacts Hin) as Htest.
    destruct fact as
      [ selector region offset | column region offset value
      | left_cell right_cell | cell instance row
      | column values default_value | cell value ];
      cbn [Complete.is_witness_fact] in Hwitness; try discriminate Hwitness.
    - cbn [interpret_fact] in Htest |- *.
      rewrite <- (cell_agree_of (Fact.CellsEqual left_cell right_cell) left_cell
        Hfact
        ltac:(cbn [fact_adv]; apply List.incl_appl; apply List.incl_refl)
        ltac:(cbn [fact_fix]; apply List.incl_appl; apply List.incl_refl)).
      rewrite <- (cell_agree_of (Fact.CellsEqual left_cell right_cell) right_cell
        Hfact
        ltac:(cbn [fact_adv]; apply List.incl_appr; apply List.incl_refl)
        ltac:(cbn [fact_fix]; apply List.incl_appr; apply List.incl_refl)).
      exact Htest.
    - cbn [interpret_fact] in Htest |- *.
      rewrite <- (cell_agree_of (Fact.InstanceIs cell instance row) cell Hfact
        ltac:(cbn [fact_adv]; apply List.incl_refl)
        ltac:(cbn [fact_fix]; apply List.incl_refl)).
      rewrite (instance_agree instance row).
      exact Htest.
    - cbn [interpret_fact] in Htest |- *.
      rewrite <- (cell_agree_of (Fact.CellIsConstant cell value) cell Hfact
        ltac:(cbn [fact_adv]; apply List.incl_refl)
        ltac:(cbn [fact_fix]; apply List.incl_refl)).
      exact Htest.
  Qed.

  Lemma copies_hold (left right : Raw.Cell.t) :
    List.In (Raw.Event.Copy left right) orchard_events ->
    raw_cell_read g left = raw_cell_read g right.
  Proof.
    unfold orchard_events.
    intros Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - unfold orchard_synthesis_events in Hin.
      destruct (layouter_copy_event_fact Index.indices region_start_of
        Garden.Orchard.circuit.orchard_usable_rows
        Garden.Orchard.circuit.synthesize left right Hin) as
        [ (left_cell & right_cell & Hleft & Hright & Hfacteq)
        | (cell & instance & row & Hleft & Hright & Hfacteq) ].
      + subst left right.
        rewrite <- !realize_eval_cell.
        apply (witness_fact_holds (Fact.CellsEqual left_cell right_cell)).
        apply (proj2 (List.filter_In _ _ _)).
        split; [exact Hfacteq | reflexivity].
      + subst left right.
        rewrite <- realize_eval_cell.
        rewrite raw_instance_read.
        apply (witness_fact_holds (Fact.InstanceIs cell instance row)).
        apply (proj2 (List.filter_In _ _ _)).
        split; [exact Hfacteq | reflexivity].
    - unfold orchard_constants_events,
        Garden.Orchard.circuit_synthesis_constants.events in Hin.
      destruct (to_event_list_inv _ _ Hin) as (binding & Hbinding & Hevent).
      cbn [Garden.Orchard.circuit_synthesis_constants.to_events] in Hevent.
      destruct Hevent as [Hbad | Hevent2]; [discriminate Hbad |].
      destruct Hevent2 as [Heq | Hfalse]; [| destruct Hfalse].
      injection Heq as <- <-.
      assert (Hfixed :
        raw_cell_read g
          (Garden.Orchard.circuit_synthesis_constants.fixed_cell
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.fixed_row)) =
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.value)).
      { unfold raw_cell_read,
          Garden.Orchard.circuit_synthesis_constants.fixed_cell.
        cbn [Raw.Cell.column Raw.Cell.row Raw.ColumnRef.kind
          Raw.ColumnRef.index].
        apply (replay_fixed_pinned orchard_events
          (initial_grid orchard_advice orchard_instance) g 3 _
          binding.(Garden.Orchard.circuit_synthesis_constants
            .ConstantCopy.annotation) _ Hreplay).
        unfold orchard_events.
        apply List.in_or_app.
        right.
        unfold orchard_constants_events,
          Garden.Orchard.circuit_synthesis_constants.events.
        apply (to_event_list_in binding _ _ Hbinding).
        unfold Garden.Orchard.circuit_synthesis_constants.to_events.
        left.
        reflexivity. }
      rewrite Hfixed.
      pose proof (proj1 (List.forallb_forall const_check _) const_cert
        binding Hbinding) as Hcheck.
      unfold const_check in Hcheck.
      apply List.existsb_exists in Hcheck.
      destruct Hcheck as (entry & Hentry & Hmatch).
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hcell Hvalue].
      apply raw_cell_eqb_eq in Hcell.
      apply Z.eqb_eq in Hvalue.
      unfold const_entries in Hentry.
      apply List.in_flat_map in Hentry.
      destruct Hentry as (fact & Hfactin & Hentry).
      destruct fact as
        [ selector' region' offset' | column' region' offset' value'
        | left_cell right_cell | cell' instance' row'
        | column' values' default_value' | cell' value' ];
        cbn [List.In] in Hentry;
        [ destruct Hentry | destruct Hentry | destruct Hentry
        | destruct Hentry | destruct Hentry | ].
      destruct Hentry as [Heq | Hfalse]; [| destruct Hfalse].
      subst entry.
      cbn [fst snd] in Hcell, Hvalue.
      subst value'.
      rewrite <- Hcell.
      rewrite <- realize_eval_cell.
      symmetry.
      apply (witness_fact_holds (Fact.CellIsConstant cell'
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.value))).
      apply (proj2 (List.filter_In _ _ _)).
      split; [exact Hfactin | reflexivity].
  Qed.

  Lemma facts_hold :
    interpret_facts (realize Index.indices region_start_of g) facts.
  Proof.
    apply (circuit_facts_hold Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows
      Garden.Orchard.circuit.synthesize g orchard_events).
    - unfold orchard_events, orchard_synthesis_events.
      apply List.incl_appl, List.incl_refl.
    - exact orchard_constants_materialized.
    - exact determined_hold.
    - exact copies_hold.
    - intros column row annotation value Hin.
      exact (replay_fixed_pinned orchard_events
        (initial_grid orchard_advice orchard_instance) g column row annotation
        value Hreplay Hin).
  Qed.

  (** The grid-identification theorem: the realized assignment of the honest
      grid satisfies the relational package the whole Orchard soundness surface
      consumes. *)
  Theorem orchard_grid_identification :
    circuit_holds (realize Index.indices region_start_of g)
      Garden.Orchard.circuit.synthesize orchard_system.
  Proof.
    split; [| split].
    - exact facts_hold.
    - exact gates_hold.
    - exact lookups_hold.
  Qed.

  (** The E1a headline: the ideal checker accepts the honest grid over the full
      serialized stream, constants tail included. *)
  Theorem orchard_operational_complete_concrete :
    mock_prover_accepts orchard_indexed_system orchard_events g
      orchard_table_rows.
  Proof.
    unfold orchard_events, orchard_indexed_system, orchard_table_rows.
    apply mock_prover_accepts_app.
    - unfold orchard_synthesis_events.
      exact (operational_complete_events Garden.Orchard.circuit.synthesize
        Index.indices region_start_of
        Garden.Orchard.circuit.orchard_usable_rows orchard_system g
        RegionId.NoteCommitOldEquality orchard_instance_free
        orchard_flattening_ok orchard_grid_identification).
    - intros left right Hin.
      apply copies_hold.
      unfold orchard_events.
      apply List.in_or_app.
      right.
      exact Hin.
  Qed.
End Grid.

(** ** Non-vacuity of the ideal checker

    The replay of the Orchard stream succeeds on any planes
    ([orchard_replay_some]), so the honest grid exists and is accepted. *)
Corollary orchard_honest_witness_accepted :
  exists g : RawGrid.t,
    apply_events orchard_events
      (initial_grid orchard_advice orchard_instance) = Some g /\
    circuit_holds (realize Index.indices region_start_of g)
      Garden.Orchard.circuit.synthesize orchard_system /\
    mock_prover_accepts orchard_indexed_system orchard_events g
      orchard_table_rows.
Proof.
  destruct (orchard_replay_some orchard_advice orchard_instance)
    as (g & Hreplay).
  exists g.
  split; [exact Hreplay |].
  split.
  - exact (orchard_grid_identification g Hreplay).
  - exact (orchard_operational_complete_concrete g Hreplay).
Qed.

End OrchardOperationalConcrete.
