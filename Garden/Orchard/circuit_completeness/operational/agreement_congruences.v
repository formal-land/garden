(** * Query-list agreement congruences, and the row shift of a realized
      assignment.

    Two assignments that agree on the finitely many cells an expression — or
    a constraint, a lookup argument, a reified fact — actually queries
    evaluate it identically.  This is the transfer engine of the
    operational-completeness grid identification: the honest witness
    generator and the assignment realized off the replayed grid do *not*
    agree pointwise (the placement's [region_start] map is not row-injective,
    so the realized selector plane reads a neighbour region's enabled point;
    and the realized lookup plane holds [0] past the usable rows where the
    relational table plane holds the column default), yet they do agree at
    every cell the gate bodies, the lookup arguments and the witness facts
    name.  Every statement here demands agreement only on the listed queries,
    at the given [(region, row)], and is proved by structural induction — no
    computation, no functional extensionality.

    A second, independent block gives the row shift for a realized
    assignment.  [realize idx rs grid] reads the grid at the absolute row
    [rs region + offset], so two region-local indices with the same absolute
    row evaluate every instance-free expression, constraint and lookup
    argument identically: both sides go through [realize_eval_expression] to
    the same indexed evaluation at [(tt, R)].

    The module is generic over [columns], [RegionId] and the prime: it
    mentions no Orchard object, no synthesis program, and no replay
    certificate. *)

Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Local Open Scope Z_scope.

Module Agree.

(** A [Forall] over a [flat_map] restricts to the image of any member of the
    index list.  Used once per plane to project a per-list agreement
    hypothesis onto one constraint / one lookup pair / one gate. *)
Lemma Forall_flat_map_In {A B : Type}
    (P : B -> Prop) (f : A -> list B) (l : list A) (a : A) :
  List.In a l ->
  List.Forall P (List.flat_map f l) ->
  List.Forall P (f a).
Proof.
  induction l as [| x l IH]; cbn [List.flat_map]; intros Hin Hall.
  - destruct Hin.
  - apply List.Forall_app in Hall.
    destruct Hall as [Hx Hl].
    destruct Hin as [Heq | Hin].
    + rewrite <- Heq.
      exact Hx.
    + exact (IH Hin Hl).
Qed.

Section Agreement.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** Query extractors on expressions

      The cells an expression reads at an index [(region, row)]: a selector
      is read at [row] itself, a fixed/advice/instance column at the rotated
      row [row + rotation.(Rotation.offset)], so the extractors carry the
      rotation offset and never the index. *)

  Fixpoint selector_queries (e : Expression.t columns)
      : list columns.(Columns.Selector) :=
    match e with
    | Expression.Constant _ => []
    | Expression.Selector selector => [selector]
    | Expression.Fixed _ _ => []
    | Expression.Advice _ _ => []
    | Expression.Instance_ _ _ => []
    | Expression.Negated e => selector_queries e
    | Expression.Sum lhs rhs => selector_queries lhs ++ selector_queries rhs
    | Expression.Product lhs rhs =>
        selector_queries lhs ++ selector_queries rhs
    | Expression.Scaled e _ => selector_queries e
    end.

  Fixpoint fixed_queries (e : Expression.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    match e with
    | Expression.Constant _ => []
    | Expression.Selector _ => []
    | Expression.Fixed column rotation =>
        [(column, rotation.(Rotation.offset))]
    | Expression.Advice _ _ => []
    | Expression.Instance_ _ _ => []
    | Expression.Negated e => fixed_queries e
    | Expression.Sum lhs rhs => fixed_queries lhs ++ fixed_queries rhs
    | Expression.Product lhs rhs => fixed_queries lhs ++ fixed_queries rhs
    | Expression.Scaled e _ => fixed_queries e
    end.

  Fixpoint advice_queries (e : Expression.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    match e with
    | Expression.Constant _ => []
    | Expression.Selector _ => []
    | Expression.Fixed _ _ => []
    | Expression.Advice column rotation =>
        [(column, rotation.(Rotation.offset))]
    | Expression.Instance_ _ _ => []
    | Expression.Negated e => advice_queries e
    | Expression.Sum lhs rhs => advice_queries lhs ++ advice_queries rhs
    | Expression.Product lhs rhs => advice_queries lhs ++ advice_queries rhs
    | Expression.Scaled e _ => advice_queries e
    end.

  Fixpoint instance_queries (e : Expression.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    match e with
    | Expression.Constant _ => []
    | Expression.Selector _ => []
    | Expression.Fixed _ _ => []
    | Expression.Advice _ _ => []
    | Expression.Instance_ column rotation =>
        [(column, rotation.(Rotation.offset))]
    | Expression.Negated e => instance_queries e
    | Expression.Sum lhs rhs => instance_queries lhs ++ instance_queries rhs
    | Expression.Product lhs rhs =>
        instance_queries lhs ++ instance_queries rhs
    | Expression.Scaled e _ => instance_queries e
    end.

  (** ** Plane-wise agreement on a query list *)

  Definition selector_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list columns.(Columns.Selector)) : Prop :=
    List.Forall
      (fun selector =>
        Γ1.(Assignment.selector) selector region row =
        Γ2.(Assignment.selector) selector region row)
      queries.

  Definition fixed_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list (columns.(Columns.Fixed) * Z)) : Prop :=
    List.Forall
      (fun query =>
        Γ1.(Assignment.fixed) (fst query) region (row + snd query) =
        Γ2.(Assignment.fixed) (fst query) region (row + snd query))
      queries.

  Definition advice_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list (columns.(Columns.Advice) * Z)) : Prop :=
    List.Forall
      (fun query =>
        Γ1.(Assignment.advice) (fst query) region (row + snd query) =
        Γ2.(Assignment.advice) (fst query) region (row + snd query))
      queries.

  Definition instance_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (row : Z)
      (queries : list (columns.(Columns.Instance_) * Z)) : Prop :=
    List.Forall
      (fun query =>
        Γ1.(Assignment.instance_) (fst query) (row + snd query) =
        Γ2.(Assignment.instance_) (fst query) (row + snd query))
      queries.

  (** The lookup plane is global (no region, no rotation): a lookup argument
      reads it at an existentially quantified table row below
      [nb_table_rows], so agreement is demanded on that whole window at the
      argument's columns. *)
  Definition lookup_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (nb_table_rows : Z)
      (cols : list columns.(Columns.Lookup)) : Prop :=
    List.Forall
      (fun column =>
        forall table_row,
          0 <= table_row < nb_table_rows ->
          Γ1.(Assignment.lookup) column table_row =
          Γ2.(Assignment.lookup) column table_row)
      cols.

  (** Agreement is a symmetric relation on each plane: the consumer picks the
      orientation its hypotheses come in (the honest generator on the left, or
      the realized assignment on the left) without reproving anything. *)

  Lemma selector_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list columns.(Columns.Selector)) :
    selector_agree Γ1 Γ2 region row queries ->
    selector_agree Γ2 Γ1 region row queries.
  Proof.
    apply List.Forall_impl.
    intros selector Hcell.
    exact (eq_sym Hcell).
  Qed.

  Lemma fixed_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list (columns.(Columns.Fixed) * Z)) :
    fixed_agree Γ1 Γ2 region row queries ->
    fixed_agree Γ2 Γ1 region row queries.
  Proof.
    apply List.Forall_impl.
    intros query Hcell.
    exact (eq_sym Hcell).
  Qed.

  Lemma advice_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (queries : list (columns.(Columns.Advice) * Z)) :
    advice_agree Γ1 Γ2 region row queries ->
    advice_agree Γ2 Γ1 region row queries.
  Proof.
    apply List.Forall_impl.
    intros query Hcell.
    exact (eq_sym Hcell).
  Qed.

  Lemma instance_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (row : Z)
      (queries : list (columns.(Columns.Instance_) * Z)) :
    instance_agree Γ1 Γ2 row queries ->
    instance_agree Γ2 Γ1 row queries.
  Proof.
    apply List.Forall_impl.
    intros query Hcell.
    exact (eq_sym Hcell).
  Qed.

  (** ** Expression congruence *)

  Definition expr_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (e : Expression.t columns) : Prop :=
    selector_agree Γ1 Γ2 region row (selector_queries e) /\
    fixed_agree Γ1 Γ2 region row (fixed_queries e) /\
    advice_agree Γ1 Γ2 region row (advice_queries e) /\
    instance_agree Γ1 Γ2 row (instance_queries e).

  Lemma eval_selector_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (selector : columns.(Columns.Selector)) :
    Γ1.(Assignment.selector) selector region row =
    Γ2.(Assignment.selector) selector region row ->
    eval_selector Γ1 (region, row) selector =
    eval_selector Γ2 (region, row) selector.
  Proof.
    intros Hplane.
    cbn [eval_selector].
    rewrite Hplane.
    reflexivity.
  Qed.

  Lemma eval_expression_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (e : Expression.t columns) :
    expr_agree Γ1 Γ2 region row e ->
    eval_expression Γ1 (region, row) e =
    eval_expression Γ2 (region, row) e.
  Proof.
    induction e as
      [ value | selector | column rotation | column rotation
      | column rotation | e IH | lhs IHlhs rhs IHrhs
      | lhs IHlhs rhs IHrhs | e IH scale ];
      intros [Hsel [Hfix [Hadv Hinst] ] ];
      unfold selector_agree, fixed_agree, advice_agree, instance_agree
        in Hsel, Hfix, Hadv, Hinst;
      cbn [selector_queries fixed_queries advice_queries instance_queries]
        in Hsel, Hfix, Hadv, Hinst.
    - (* Constant *)
      reflexivity.
    - (* Selector *)
      cbn [eval_expression].
      apply eval_selector_agree.
      exact (List.Forall_inv Hsel).
    - (* Fixed *)
      pose proof (List.Forall_inv Hfix) as Hcell.
      cbn [fst snd] in Hcell.
      cbn [eval_expression].
      unfold rotated_row.
      rewrite Hcell.
      reflexivity.
    - (* Advice *)
      pose proof (List.Forall_inv Hadv) as Hcell.
      cbn [fst snd] in Hcell.
      cbn [eval_expression].
      unfold rotated_row.
      rewrite Hcell.
      reflexivity.
    - (* Instance_ *)
      pose proof (List.Forall_inv Hinst) as Hcell.
      cbn [fst snd] in Hcell.
      cbn [eval_expression].
      unfold rotated_row.
      rewrite Hcell.
      reflexivity.
    - (* Negated *)
      cbn [eval_expression].
      rewrite (IH (conj Hsel (conj Hfix (conj Hadv Hinst)))).
      reflexivity.
    - (* Sum *)
      apply List.Forall_app in Hsel, Hfix, Hadv, Hinst.
      destruct Hsel as [Hsel1 Hsel2].
      destruct Hfix as [Hfix1 Hfix2].
      destruct Hadv as [Hadv1 Hadv2].
      destruct Hinst as [Hinst1 Hinst2].
      rewrite !eval_expression_sum.
      rewrite (IHlhs (conj Hsel1 (conj Hfix1 (conj Hadv1 Hinst1)))).
      rewrite (IHrhs (conj Hsel2 (conj Hfix2 (conj Hadv2 Hinst2)))).
      reflexivity.
    - (* Product *)
      apply List.Forall_app in Hsel, Hfix, Hadv, Hinst.
      destruct Hsel as [Hsel1 Hsel2].
      destruct Hfix as [Hfix1 Hfix2].
      destruct Hadv as [Hadv1 Hadv2].
      destruct Hinst as [Hinst1 Hinst2].
      cbn [eval_expression].
      rewrite (IHlhs (conj Hsel1 (conj Hfix1 (conj Hadv1 Hinst1)))).
      rewrite (IHrhs (conj Hsel2 (conj Hfix2 (conj Hadv2 Hinst2)))).
      reflexivity.
    - (* Scaled *)
      cbn [eval_expression].
      rewrite (IH (conj Hsel (conj Hfix (conj Hadv Hinst)))).
      reflexivity.
  Qed.

  (** ** Query extractors and congruence on constraints *)

  Fixpoint constraint_selector_queries (c : Constraint.t columns)
      : list columns.(Columns.Selector) :=
    match c with
    | Constraint.Select selector c => selector :: constraint_selector_queries c
    | Constraint.Equal lhs rhs => selector_queries lhs ++ selector_queries rhs
    | Constraint.Boolean e => selector_queries e
    | Constraint.Range e _ => selector_queries e
    | Constraint.Either lhs rhs =>
        constraint_selector_queries lhs ++ constraint_selector_queries rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        selector_queries lhs ++ selector_queries rhs
    | Constraint.EqualZeroToPrecise e => selector_queries e
    end.

  Fixpoint constraint_fixed_queries (c : Constraint.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    match c with
    | Constraint.Select _ c => constraint_fixed_queries c
    | Constraint.Equal lhs rhs => fixed_queries lhs ++ fixed_queries rhs
    | Constraint.Boolean e => fixed_queries e
    | Constraint.Range e _ => fixed_queries e
    | Constraint.Either lhs rhs =>
        constraint_fixed_queries lhs ++ constraint_fixed_queries rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        fixed_queries lhs ++ fixed_queries rhs
    | Constraint.EqualZeroToPrecise e => fixed_queries e
    end.

  Fixpoint constraint_advice_queries (c : Constraint.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    match c with
    | Constraint.Select _ c => constraint_advice_queries c
    | Constraint.Equal lhs rhs => advice_queries lhs ++ advice_queries rhs
    | Constraint.Boolean e => advice_queries e
    | Constraint.Range e _ => advice_queries e
    | Constraint.Either lhs rhs =>
        constraint_advice_queries lhs ++ constraint_advice_queries rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        advice_queries lhs ++ advice_queries rhs
    | Constraint.EqualZeroToPrecise e => advice_queries e
    end.

  Fixpoint constraint_instance_queries (c : Constraint.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    match c with
    | Constraint.Select _ c => constraint_instance_queries c
    | Constraint.Equal lhs rhs => instance_queries lhs ++ instance_queries rhs
    | Constraint.Boolean e => instance_queries e
    | Constraint.Range e _ => instance_queries e
    | Constraint.Either lhs rhs =>
        constraint_instance_queries lhs ++ constraint_instance_queries rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        instance_queries lhs ++ instance_queries rhs
    | Constraint.EqualZeroToPrecise e => instance_queries e
    end.

  Definition constraint_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (c : Constraint.t columns) : Prop :=
    selector_agree Γ1 Γ2 region row (constraint_selector_queries c) /\
    fixed_agree Γ1 Γ2 region row (constraint_fixed_queries c) /\
    advice_agree Γ1 Γ2 region row (constraint_advice_queries c) /\
    instance_agree Γ1 Γ2 row (constraint_instance_queries c).

  Lemma eval_constraint_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (c : Constraint.t columns) :
    constraint_agree Γ1 Γ2 region row c ->
    (eval_constraint Γ1 (region, row) c <->
     eval_constraint Γ2 (region, row) c).
  Proof.
    induction c as
      [ selector c IH | lhs rhs | e | e range | lhs IHlhs rhs IHrhs
      | lhs rhs | e ];
      intros [Hsel [Hfix [Hadv Hinst] ] ];
      unfold selector_agree, fixed_agree, advice_agree, instance_agree
        in Hsel, Hfix, Hadv, Hinst;
      cbn [constraint_selector_queries constraint_fixed_queries
           constraint_advice_queries constraint_instance_queries]
        in Hsel, Hfix, Hadv, Hinst.
    - (* Select *)
      pose proof (List.Forall_inv Hsel) as Hplane.
      pose proof (List.Forall_inv_tail Hsel) as Hsel'.
      specialize (IH (conj Hsel' (conj Hfix (conj Hadv Hinst)))).
      cbn [eval_constraint].
      rewrite (eval_selector_agree Γ1 Γ2 region row selector Hplane).
      split.
      + intros Hc Hnz.
        exact (proj1 IH (Hc Hnz)).
      + intros Hc Hnz.
        exact (proj2 IH (Hc Hnz)).
    - (* Equal *)
      apply List.Forall_app in Hsel, Hfix, Hadv, Hinst.
      destruct Hsel as [Hsel1 Hsel2].
      destruct Hfix as [Hfix1 Hfix2].
      destruct Hadv as [Hadv1 Hadv2].
      destruct Hinst as [Hinst1 Hinst2].
      cbn [eval_constraint].
      rewrite (eval_expression_agree Γ1 Γ2 region row lhs
        (conj Hsel1 (conj Hfix1 (conj Hadv1 Hinst1)))).
      rewrite (eval_expression_agree Γ1 Γ2 region row rhs
        (conj Hsel2 (conj Hfix2 (conj Hadv2 Hinst2)))).
      reflexivity.
    - (* Boolean *)
      cbn [eval_constraint].
      rewrite (eval_expression_agree Γ1 Γ2 region row e
        (conj Hsel (conj Hfix (conj Hadv Hinst)))).
      reflexivity.
    - (* Range *)
      cbn [eval_constraint].
      rewrite (eval_expression_agree Γ1 Γ2 region row e
        (conj Hsel (conj Hfix (conj Hadv Hinst)))).
      reflexivity.
    - (* Either *)
      apply List.Forall_app in Hsel, Hfix, Hadv, Hinst.
      destruct Hsel as [Hsel1 Hsel2].
      destruct Hfix as [Hfix1 Hfix2].
      destruct Hadv as [Hadv1 Hadv2].
      destruct Hinst as [Hinst1 Hinst2].
      specialize (IHlhs (conj Hsel1 (conj Hfix1 (conj Hadv1 Hinst1)))).
      specialize (IHrhs (conj Hsel2 (conj Hfix2 (conj Hadv2 Hinst2)))).
      cbn [eval_constraint].
      rewrite IHlhs, IHrhs.
      reflexivity.
    - (* EitherZeroToPrecise *)
      apply List.Forall_app in Hsel, Hfix, Hadv, Hinst.
      destruct Hsel as [Hsel1 Hsel2].
      destruct Hfix as [Hfix1 Hfix2].
      destruct Hadv as [Hadv1 Hadv2].
      destruct Hinst as [Hinst1 Hinst2].
      cbn [eval_constraint].
      rewrite (eval_expression_agree Γ1 Γ2 region row lhs
        (conj Hsel1 (conj Hfix1 (conj Hadv1 Hinst1)))).
      rewrite (eval_expression_agree Γ1 Γ2 region row rhs
        (conj Hsel2 (conj Hfix2 (conj Hadv2 Hinst2)))).
      reflexivity.
    - (* EqualZeroToPrecise *)
      cbn [eval_constraint].
      rewrite (eval_expression_agree Γ1 Γ2 region row e
        (conj Hsel (conj Hfix (conj Hadv Hinst)))).
      reflexivity.
  Qed.

  (** ** Lifting to named constraints, gates and gate lists *)

  Definition named_constraint_selector_queries
      (nc : option string * Constraint.t columns)
      : list columns.(Columns.Selector) :=
    constraint_selector_queries (snd nc).

  Definition named_constraint_fixed_queries
      (nc : option string * Constraint.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    constraint_fixed_queries (snd nc).

  Definition named_constraint_advice_queries
      (nc : option string * Constraint.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    constraint_advice_queries (snd nc).

  Definition named_constraint_instance_queries
      (nc : option string * Constraint.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    constraint_instance_queries (snd nc).

  Definition constraints_selector_queries (cs : Constraints.t columns)
      : list columns.(Columns.Selector) :=
    List.flat_map named_constraint_selector_queries cs.

  Definition constraints_fixed_queries (cs : Constraints.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    List.flat_map named_constraint_fixed_queries cs.

  Definition constraints_advice_queries (cs : Constraints.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    List.flat_map named_constraint_advice_queries cs.

  Definition constraints_instance_queries (cs : Constraints.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    List.flat_map named_constraint_instance_queries cs.

  Definition constraints_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (cs : Constraints.t columns) : Prop :=
    selector_agree Γ1 Γ2 region row (constraints_selector_queries cs) /\
    fixed_agree Γ1 Γ2 region row (constraints_fixed_queries cs) /\
    advice_agree Γ1 Γ2 region row (constraints_advice_queries cs) /\
    instance_agree Γ1 Γ2 row (constraints_instance_queries cs).

  Lemma constraints_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (cs : Constraints.t columns) :
    constraints_agree Γ1 Γ2 region row cs ->
    constraints_agree Γ2 Γ1 region row cs.
  Proof.
    intros [Hsel [Hfix [Hadv Hinst] ] ].
    repeat apply conj.
    - exact (selector_agree_sym Γ1 Γ2 region row _ Hsel).
    - exact (fixed_agree_sym Γ1 Γ2 region row _ Hfix).
    - exact (advice_agree_sym Γ1 Γ2 region row _ Hadv).
    - exact (instance_agree_sym Γ1 Γ2 row _ Hinst).
  Qed.

  Lemma constraints_agree_In
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (cs : Constraints.t columns)
      (nc : option string * Constraint.t columns) :
    List.In nc cs ->
    constraints_agree Γ1 Γ2 region row cs ->
    constraint_agree Γ1 Γ2 region row (snd nc).
  Proof.
    intros Hin [Hsel [Hfix [Hadv Hinst] ] ].
    unfold constraints_selector_queries, constraints_fixed_queries,
      constraints_advice_queries, constraints_instance_queries,
      selector_agree, fixed_agree, advice_agree, instance_agree
      in Hsel, Hfix, Hadv, Hinst.
    repeat apply conj.
    - exact (Forall_flat_map_In _ _ _ _ Hin Hsel).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hfix).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hadv).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hinst).
  Qed.

  Lemma eval_constraints_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (cs : Constraints.t columns) :
    constraints_agree Γ1 Γ2 region row cs ->
    eval_constraints Γ1 (region, row) cs ->
    eval_constraints Γ2 (region, row) cs.
  Proof.
    intros Hagree Heval.
    apply eval_constraints_forall.
    intros nc Hin.
    rewrite eval_constraints_forall in Heval.
    specialize (Heval nc Hin).
    destruct nc as [name c].
    cbn [eval_named_constraint] in Heval |- *.
    apply (proj1 (eval_constraint_agree Γ1 Γ2 region row c
      (constraints_agree_In Γ1 Γ2 region row cs (name, c) Hin Hagree))).
    exact Heval.
  Qed.

  Definition gate_selector_queries (gate : Gate.t columns)
      : list columns.(Columns.Selector) :=
    constraints_selector_queries gate.(Gate.constraints).

  Definition gate_fixed_queries (gate : Gate.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    constraints_fixed_queries gate.(Gate.constraints).

  Definition gate_advice_queries (gate : Gate.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    constraints_advice_queries gate.(Gate.constraints).

  Definition gate_instance_queries (gate : Gate.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    constraints_instance_queries gate.(Gate.constraints).

  Definition gate_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (gate : Gate.t columns) : Prop :=
    constraints_agree Γ1 Γ2 region row gate.(Gate.constraints).

  Lemma eval_gate_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (gate : Gate.t columns) :
    gate_agree Γ1 Γ2 region row gate ->
    eval_gate Γ1 (region, row) gate ->
    eval_gate Γ2 (region, row) gate.
  Proof.
    intros Hagree Heval.
    exact (eval_constraints_agree Γ1 Γ2 region row
      gate.(Gate.constraints) Hagree Heval).
  Qed.

  Definition gates_selector_queries (gates : list (Gate.t columns))
      : list columns.(Columns.Selector) :=
    List.flat_map gate_selector_queries gates.

  Definition gates_fixed_queries (gates : list (Gate.t columns))
      : list (columns.(Columns.Fixed) * Z) :=
    List.flat_map gate_fixed_queries gates.

  Definition gates_advice_queries (gates : list (Gate.t columns))
      : list (columns.(Columns.Advice) * Z) :=
    List.flat_map gate_advice_queries gates.

  Definition gates_instance_queries (gates : list (Gate.t columns))
      : list (columns.(Columns.Instance_) * Z) :=
    List.flat_map gate_instance_queries gates.

  Definition gates_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (gates : list (Gate.t columns)) : Prop :=
    selector_agree Γ1 Γ2 region row (gates_selector_queries gates) /\
    fixed_agree Γ1 Γ2 region row (gates_fixed_queries gates) /\
    advice_agree Γ1 Γ2 region row (gates_advice_queries gates) /\
    instance_agree Γ1 Γ2 row (gates_instance_queries gates).

  Lemma gates_agree_In
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (gates : list (Gate.t columns))
      (gate : Gate.t columns) :
    List.In gate gates ->
    gates_agree Γ1 Γ2 region row gates ->
    gate_agree Γ1 Γ2 region row gate.
  Proof.
    intros Hin [Hsel [Hfix [Hadv Hinst] ] ].
    unfold gates_selector_queries, gates_fixed_queries,
      gates_advice_queries, gates_instance_queries,
      selector_agree, fixed_agree, advice_agree, instance_agree
      in Hsel, Hfix, Hadv, Hinst.
    repeat apply conj.
    - exact (Forall_flat_map_In _ _ _ _ Hin Hsel).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hfix).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hadv).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hinst).
  Qed.

  (** ** Lookup arguments *)

  Definition arg_selector_queries (arg : LookupArgument.t columns)
      : list columns.(Columns.Selector) :=
    List.flat_map
      (fun pair => selector_queries (fst pair))
      arg.(LookupArgument.pairs).

  Definition arg_fixed_queries (arg : LookupArgument.t columns)
      : list (columns.(Columns.Fixed) * Z) :=
    List.flat_map
      (fun pair => fixed_queries (fst pair))
      arg.(LookupArgument.pairs).

  Definition arg_advice_queries (arg : LookupArgument.t columns)
      : list (columns.(Columns.Advice) * Z) :=
    List.flat_map
      (fun pair => advice_queries (fst pair))
      arg.(LookupArgument.pairs).

  Definition arg_instance_queries (arg : LookupArgument.t columns)
      : list (columns.(Columns.Instance_) * Z) :=
    List.flat_map
      (fun pair => instance_queries (fst pair))
      arg.(LookupArgument.pairs).

  Definition arg_lookup_columns (arg : LookupArgument.t columns)
      : list columns.(Columns.Lookup) :=
    List.map snd arg.(LookupArgument.pairs).

  Definition arg_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (arg : LookupArgument.t columns) : Prop :=
    selector_agree Γ1 Γ2 region row (arg_selector_queries arg) /\
    fixed_agree Γ1 Γ2 region row (arg_fixed_queries arg) /\
    advice_agree Γ1 Γ2 region row (arg_advice_queries arg) /\
    instance_agree Γ1 Γ2 row (arg_instance_queries arg).

  Lemma arg_agree_pair
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (arg : LookupArgument.t columns)
      (pair : Expression.t columns * columns.(Columns.Lookup)) :
    List.In pair arg.(LookupArgument.pairs) ->
    arg_agree Γ1 Γ2 region row arg ->
    expr_agree Γ1 Γ2 region row (fst pair).
  Proof.
    intros Hin [Hsel [Hfix [Hadv Hinst] ] ].
    unfold arg_selector_queries, arg_fixed_queries, arg_advice_queries,
      arg_instance_queries, selector_agree, fixed_agree, advice_agree,
      instance_agree in Hsel, Hfix, Hadv, Hinst.
    repeat apply conj.
    - exact (Forall_flat_map_In _ _ _ _ Hin Hsel).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hfix).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hadv).
    - exact (Forall_flat_map_In _ _ _ _ Hin Hinst).
  Qed.

  Lemma eval_lookup_argument_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (nb_table_rows : Z)
      (arg : LookupArgument.t columns) :
    arg_agree Γ1 Γ2 region row arg ->
    lookup_agree Γ1 Γ2 nb_table_rows (arg_lookup_columns arg) ->
    eval_lookup_argument Γ1 (region, row) nb_table_rows arg ->
    eval_lookup_argument Γ2 (region, row) nb_table_rows arg.
  Proof.
    intros Hagree Hlookup Heval.
    destruct Heval as [table_row [Hbound Hpairs] ].
    exists table_row.
    split; [exact Hbound |].
    rewrite List.Forall_forall in Hpairs.
    apply List.Forall_forall.
    intros pair Hin.
    specialize (Hpairs pair Hin).
    unfold lookup_agree in Hlookup.
    rewrite List.Forall_forall in Hlookup.
    assert (Hcol :
      Γ1.(Assignment.lookup) (snd pair) table_row =
      Γ2.(Assignment.lookup) (snd pair) table_row).
    { apply Hlookup; [| exact Hbound].
      unfold arg_lookup_columns.
      apply List.in_map.
      exact Hin. }
    pose proof (eval_expression_agree Γ1 Γ2 region row (fst pair)
      (arg_agree_pair Γ1 Γ2 region row arg pair Hin Hagree)) as Hexpr.
    destruct pair as [e column].
    cbn [fst snd] in Hcol, Hexpr.
    cbn beta iota in Hpairs |- *.
    rewrite <- Hexpr, Hpairs.
    exact Hcol.
  Qed.

  (** ** Reified facts *)

  (** The cells a reified fact names, as an agreement condition on the two
      assignments.  [Fact.LookupTableLoaded] pins only the assigned rows
      [0 .. length values), matching the keygen-faithful relational reading
      of [interpret_fact]: past that window the table column is not
      program-determined, so no agreement is demanded there. *)
  Definition cell_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) : Prop :=
    match cell.(Garden.Halo2.Synthesis.Cell.column) with
    | Garden.Halo2.Synthesis.ColumnRef.Advice column =>
        Γ1.(Assignment.advice) column
          cell.(Garden.Halo2.Synthesis.Cell.region)
          cell.(Garden.Halo2.Synthesis.Cell.row_offset) =
        Γ2.(Assignment.advice) column
          cell.(Garden.Halo2.Synthesis.Cell.region)
          cell.(Garden.Halo2.Synthesis.Cell.row_offset)
    | Garden.Halo2.Synthesis.ColumnRef.Fixed column =>
        Γ1.(Assignment.fixed) column
          cell.(Garden.Halo2.Synthesis.Cell.region)
          cell.(Garden.Halo2.Synthesis.Cell.row_offset) =
        Γ2.(Assignment.fixed) column
          cell.(Garden.Halo2.Synthesis.Cell.region)
          cell.(Garden.Halo2.Synthesis.Cell.row_offset)
    | Garden.Halo2.Synthesis.ColumnRef.Instance_ column =>
        Γ1.(Assignment.instance_) column
          cell.(Garden.Halo2.Synthesis.Cell.row_offset) =
        Γ2.(Assignment.instance_) column
          cell.(Garden.Halo2.Synthesis.Cell.row_offset)
    end.

  Lemma eval_cell_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    cell_agree Γ1 Γ2 cell ->
    eval_cell Γ1 cell = eval_cell Γ2 cell.
  Proof.
    destruct cell as [[column | column | column] region offset];
      unfold cell_agree, eval_cell; cbn [Garden.Halo2.Synthesis.Cell.column
        Garden.Halo2.Synthesis.Cell.region
        Garden.Halo2.Synthesis.Cell.row_offset];
      intros Hcell; exact Hcell.
  Qed.

  Definition fact_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId) : Prop :=
    match fact with
    | Fact.SelectorOn selector region offset =>
        Γ1.(Assignment.selector) selector region offset =
        Γ2.(Assignment.selector) selector region offset
    | Fact.FixedIs column region offset _ =>
        Γ1.(Assignment.fixed) column region offset =
        Γ2.(Assignment.fixed) column region offset
    | Fact.CellsEqual left_cell right_cell =>
        cell_agree Γ1 Γ2 left_cell /\ cell_agree Γ1 Γ2 right_cell
    | Fact.InstanceIs cell instance row =>
        cell_agree Γ1 Γ2 cell /\
        Γ1.(Assignment.instance_) instance row =
        Γ2.(Assignment.instance_) instance row
    | Fact.LookupTableLoaded column values _ =>
        forall row,
          0 <= row < Z.of_nat (List.length values) ->
          Γ1.(Assignment.lookup) column row =
          Γ2.(Assignment.lookup) column row
    | Fact.CellIsConstant cell _ => cell_agree Γ1 Γ2 cell
    end.

  Lemma cell_agree_sym
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    cell_agree Γ1 Γ2 cell ->
    cell_agree Γ2 Γ1 cell.
  Proof.
    destruct cell as [[column | column | column] region offset];
      unfold cell_agree;
      cbn [Garden.Halo2.Synthesis.Cell.column];
      intros Hcell; exact (eq_sym Hcell).
  Qed.

  Lemma interpret_fact_agree
      (Γ1 Γ2 : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId) :
    fact_agree Γ1 Γ2 fact ->
    interpret_fact Γ1 fact ->
    interpret_fact Γ2 fact.
  Proof.
    destruct fact as
      [ selector region offset
      | column region offset value
      | left_cell right_cell
      | cell instance row
      | column values default_value
      | cell value ];
      cbn [fact_agree interpret_fact].
    - (* SelectorOn *)
      intros Hplane Hfact.
      rewrite <- Hplane.
      exact Hfact.
    - (* FixedIs *)
      intros Hplane Hfact.
      rewrite <- Hplane.
      exact Hfact.
    - (* CellsEqual *)
      intros [Hleft Hright] Hfact.
      rewrite <- (eval_cell_agree Γ1 Γ2 left_cell Hleft).
      rewrite <- (eval_cell_agree Γ1 Γ2 right_cell Hright).
      exact Hfact.
    - (* InstanceIs *)
      intros [Hcell Hplane] Hfact.
      rewrite <- (eval_cell_agree Γ1 Γ2 cell Hcell).
      rewrite <- Hplane.
      exact Hfact.
    - (* LookupTableLoaded *)
      intros Hplane Hfact row Hrow.
      rewrite <- (Hplane row Hrow).
      exact (Hfact row Hrow).
    - (* CellIsConstant *)
      intros Hcell Hfact.
      rewrite <- (eval_cell_agree Γ1 Γ2 cell Hcell).
      exact Hfact.
  Qed.

  (** ** The row shift of a realized assignment

      [realize idx rs grid] resolves a region-local index [(region, row)] to
      the absolute grid row [rs region + row].  Two indices with the same
      absolute row therefore evaluate every instance-free expression (and
      every constraint, gate and lookup argument built from such
      expressions) identically: both sides travel through
      [realize_eval_expression] to the same indexed evaluation at [(tt, R)].
      The instance plane is the one exception the relational model addresses
      differently — it is absolute on both sides but is not shifted — which
      is why the hypotheses are the [instance_free] decision procedures of
      [realize/main.v]. *)

  Lemma realize_eval_selector_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (selector : columns.(Columns.Selector)) :
    rs region1 + row1 = rs region2 + row2 ->
    eval_selector (realize idx rs grid) (region1, row1) selector =
    eval_selector (realize idx rs grid) (region2, row2) selector.
  Proof.
    intros Hrow.
    cbn [eval_selector realize Assignment.selector].
    rewrite Hrow.
    reflexivity.
  Qed.

  Lemma realize_eval_expression_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (e : Expression.t columns) :
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

  Lemma realize_eval_constraint_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (Hrow : rs region1 + row1 = rs region2 + row2)
      (c : Constraint.t columns) :
    constraint_instance_free c = true ->
    (eval_constraint (realize idx rs grid) (region1, row1) c <->
     eval_constraint (realize idx rs grid) (region2, row2) c).
  Proof.
    induction c as
      [ selector c IH | lhs rhs | e | e range | lhs IHlhs rhs IHrhs
      | lhs rhs | e ];
      intros Hfree; cbn [constraint_instance_free] in Hfree.
    - (* Select *)
      specialize (IH Hfree).
      cbn [eval_constraint].
      rewrite (realize_eval_selector_shift idx rs grid
        region1 row1 region2 row2 selector Hrow).
      split.
      + intros Hc Hnz.
        exact (proj1 IH (Hc Hnz)).
      + intros Hc Hnz.
        exact (proj2 IH (Hc Hnz)).
    - (* Equal *)
      apply Bool.andb_true_iff in Hfree.
      destruct Hfree as [Hlhs Hrhs].
      cbn [eval_constraint].
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 lhs Hlhs Hrow).
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 rhs Hrhs Hrow).
      reflexivity.
    - (* Boolean *)
      cbn [eval_constraint].
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 e Hfree Hrow).
      reflexivity.
    - (* Range *)
      cbn [eval_constraint].
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 e Hfree Hrow).
      reflexivity.
    - (* Either *)
      apply Bool.andb_true_iff in Hfree.
      destruct Hfree as [Hlhs Hrhs].
      specialize (IHlhs Hlhs).
      specialize (IHrhs Hrhs).
      cbn [eval_constraint].
      rewrite IHlhs, IHrhs.
      reflexivity.
    - (* EitherZeroToPrecise *)
      apply Bool.andb_true_iff in Hfree.
      destruct Hfree as [Hlhs Hrhs].
      cbn [eval_constraint].
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 lhs Hlhs Hrow).
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 rhs Hrhs Hrow).
      reflexivity.
    - (* EqualZeroToPrecise *)
      cbn [eval_constraint].
      rewrite (realize_eval_expression_shift idx rs grid
        region1 row1 region2 row2 e Hfree Hrow).
      reflexivity.
  Qed.

  Lemma realize_eval_constraints_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (cs : Constraints.t columns) :
    List.forallb
      (fun nc => constraint_instance_free (snd nc)) cs = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_constraints (realize idx rs grid) (region1, row1) cs ->
    eval_constraints (realize idx rs grid) (region2, row2) cs.
  Proof.
    intros Hfree Hrow Heval.
    apply eval_constraints_forall.
    intros nc Hin.
    rewrite eval_constraints_forall in Heval.
    specialize (Heval nc Hin).
    rewrite List.forallb_forall in Hfree.
    specialize (Hfree nc Hin).
    destruct nc as [name c].
    cbn [snd] in Hfree.
    cbn [eval_named_constraint] in Heval |- *.
    apply (proj1 (realize_eval_constraint_shift idx rs grid
      region1 row1 region2 row2 Hrow c Hfree)).
    exact Heval.
  Qed.

  Lemma realize_eval_gate_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (gate : Gate.t columns) :
    gate_instance_free gate = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_gate (realize idx rs grid) (region1, row1) gate ->
    eval_gate (realize idx rs grid) (region2, row2) gate.
  Proof.
    intros Hfree Hrow Heval.
    exact (realize_eval_constraints_shift idx rs grid
      region1 row1 region2 row2 gate.(Gate.constraints) Hfree Hrow Heval).
  Qed.

  Lemma realize_eval_lookup_argument_shift
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region1 : RegionId) (row1 : Z)
      (region2 : RegionId) (row2 : Z)
      (nb_table_rows : Z)
      (arg : LookupArgument.t columns) :
    lookup_argument_instance_free arg = true ->
    rs region1 + row1 = rs region2 + row2 ->
    eval_lookup_argument (realize idx rs grid) (region1, row1)
      nb_table_rows arg ->
    eval_lookup_argument (realize idx rs grid) (region2, row2)
      nb_table_rows arg.
  Proof.
    intros Hfree Hrow Heval.
    destruct Heval as [table_row [Hbound Hpairs] ].
    exists table_row.
    split; [exact Hbound |].
    rewrite List.Forall_forall in Hpairs.
    apply List.Forall_forall.
    intros pair Hin.
    specialize (Hpairs pair Hin).
    unfold lookup_argument_instance_free in Hfree.
    rewrite List.forallb_forall in Hfree.
    specialize (Hfree pair Hin).
    destruct pair as [e column].
    cbn [fst] in Hfree.
    cbn beta iota in Hpairs |- *.
    rewrite <- (realize_eval_expression_shift idx rs grid
      region1 row1 region2 row2 e Hfree Hrow).
    exact Hpairs.
  Qed.

  (** ** The placed transfer corollaries

      The two composites the operational-completeness join consumes: a
      relational fact proved of the honest assignment at the *enabled point*
      [(region_pt, row_pt)] discharges the corresponding obligation of the
      realized assignment at *any* index [(region, row)] with the same
      absolute row, given agreement at the enabled point on the cells the
      constraint (resp. the lookup argument) queries.  The absolute-row
      equation moves the obligation to the point; the query-list agreement
      swaps the assignment. *)

  Lemma realize_constraint_transfer
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (region_pt : RegionId) (row_pt : Z)
      (c : Constraint.t columns) :
    constraint_instance_free c = true ->
    rs region + row = rs region_pt + row_pt ->
    constraint_agree Γ (realize idx rs grid) region_pt row_pt c ->
    eval_constraint Γ (region_pt, row_pt) c ->
    eval_constraint (realize idx rs grid) (region, row) c.
  Proof.
    intros Hfree Hrow Hagree Heval.
    apply (proj2 (realize_eval_constraint_shift idx rs grid
      region row region_pt row_pt Hrow c Hfree)).
    exact (proj1 (eval_constraint_agree Γ (realize idx rs grid)
      region_pt row_pt c Hagree) Heval).
  Qed.

  Lemma realize_lookup_argument_transfer
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (region_pt : RegionId) (row_pt : Z)
      (nb_table_rows : Z)
      (arg : LookupArgument.t columns) :
    lookup_argument_instance_free arg = true ->
    rs region + row = rs region_pt + row_pt ->
    arg_agree Γ (realize idx rs grid) region_pt row_pt arg ->
    lookup_agree Γ (realize idx rs grid) nb_table_rows
      (arg_lookup_columns arg) ->
    eval_lookup_argument Γ (region_pt, row_pt) nb_table_rows arg ->
    eval_lookup_argument (realize idx rs grid) (region, row)
      nb_table_rows arg.
  Proof.
    intros Hfree Hrow Hagree Hlookup Heval.
    apply (realize_eval_lookup_argument_shift idx rs grid
      region_pt row_pt region row nb_table_rows arg Hfree (eq_sym Hrow)).
    exact (eval_lookup_argument_agree Γ (realize idx rs grid)
      region_pt row_pt nb_table_rows arg Hagree Hlookup Heval).
  Qed.
End Agreement.

End Agree.
