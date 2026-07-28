(** * Compiled-plonkish soundness of the whole Orchard action circuit.

    The compiled plonkish layer ([Halo2/plonkish/]) instantiated on the full
    Orchard action circuit: acceptance of the compiled system — the
    selector-compressed gates on the cyclic [2^11]-row domain, the lookup
    arguments on the domain rows, and grid invariance under the permutation
    σ built from the copy obligations over the pinned permutation columns —
    implies [mock_prover_accepts] of the serialized circuit, hence
    [circuit_holds] of the realized assignment, hence the §4.18.4 Action
    statement.

    The compiled system is [OrchardCompiledCheck.compiled] =
    [Compile.compile] on [orchard_indexed_system] with the activations of
    the serialized events and the pinned permutation-column and constants
    data of [compiled/pinned.v].  The parity certificates of
    [compiled/check.v] identify this object with the deployed
    description [circuit_description_fixed] component by component — the
    193 gate polynomials (indicator factors included), the query tables,
    the lookup arguments, the constants column — so the acceptance
    hypothesis below reads on the deployed compiled circuit, not merely on
    the model's own compilation output.

    The pieces:

    - [with_combinations]: the replayed grid with the combination fixed
      planes of the compiled output installed — the keygen step that
      materializes the packed selector columns as fixed polynomials, which
      synthesis itself never writes;
    - [orchard_selector_plane]: the replayed selector planes follow the
      activation vectors of [OrchardCompiledCheck.orchard_infos] on every
      domain row — the selector-plane linking hypothesis of
      [compile_correct], proved from the replay-pinning lemmas plus a
      selector-index bound certificate, never by evaluating the symbolic
      grid;
    - [vm_compute] certificates for every decidable premise: the activation
      bound, selector vacuity, multiplicative substitution positions, the
      per-assignment indicator check (sharded — the whole scan costs ≈ 78 s,
      each 14-assignment shard ≈ 20 s), the finite-domain layout bundle of
      [plonkish_of_mock_prover], the combination-column disjointness of the
      original gates, the σ construction success, and the resolvability of
      every copy cell in the pinned permutation columns;
    - [orchard_compiled_sound]: compiled acceptance of a replayed grid
      implies [mock_prover_accepts] — the gate conjunct through
      [compile_correct_domain] plus the combination-plane transfer, the
      copy conjunct through [sigma_correct], the row-domain extension
      through [plonkish_of_mock_prover];
    - [orchard_compiled_operational_sound] /
      [orchard_compiled_action_statement]: the composition with
      [orchard_operational_sound] and the Orchard action surface, ending at
      the Action statement and [ValidActionInputs].

    The lookup conjunct of the acceptance is stated over the indexed,
    selector-carrying system on the replayed grid — the interface of
    [plonkish_accepts], whose lookup inputs the compiled system's
    substituted inputs mirror through the parity certificates
    ([lookup_inputs_match]); the compiled-gate conjunct is where the
    selector compression is consumed. *)

Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.mock.
Require Import Garden.Halo2.plonkish.compile.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.compiled.check.
Require Garden.Orchard.circuit.
Require Garden.Orchard.protocol_spec.
Require Garden.Orchard.circuit_proof.inputs.
Require Garden.Orchard.circuit_proof.merkle.
Require Garden.Orchard.circuit_proof.note_commit.cmx.
Require Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompiled.

(** ** Option combinators

    Projections of option values are routed through combinators whose
    [match] is on a bound variable, so no concrete heavy computation ever
    sits in scrutinee position at elaboration time. *)

Definition option_default {A : Type} (default : A) (value : option A) : A :=
  match value with
  | Some a => a
  | None => default
  end.

Definition opt_is_some {A : Type} (value : option A) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

Lemma opt_is_some_default {A : Type} (default : A) (value : option A) :
  opt_is_some value = true ->
  value = Some (option_default default value).
Proof.
  destruct value; [reflexivity | discriminate].
Qed.

(** ** Splitting a [forallb] scan into four chunks

    The shape of the sharded per-assignment certificate: the full scan is
    the conjunction of the scans of four [firstn]/[skipn] windows. *)

Lemma forallb_chunk4 {A : Type} (check : A -> bool) (l : list A) (n : nat) :
  List.forallb check (List.firstn n l) = true ->
  List.forallb check (List.firstn n (List.skipn n l)) = true ->
  List.forallb check (List.firstn n (List.skipn n (List.skipn n l))) = true ->
  List.forallb check (List.skipn n (List.skipn n (List.skipn n l))) = true ->
  List.forallb check l = true.
Proof.
  intros H0 H1 H2 H3.
  rewrite <- (List.firstn_skipn n l), List.forallb_app, H0.
  rewrite <- (List.firstn_skipn n (List.skipn n l)), List.forallb_app, H1.
  rewrite <- (List.firstn_skipn n (List.skipn n (List.skipn n l))),
    List.forallb_app, H2, H3.
  reflexivity.
Qed.

(** ** The grid with the combination fixed planes installed

    Keygen materializes the combination columns of the compiled output as
    fixed polynomials; synthesis never writes them, so the replayed grid
    holds [0] there.  [with_combinations] installs the compiled values on
    the combination columns and leaves every other cell — and the whole
    selector, advice and instance planes — untouched. *)

Definition with_combinations (compiled : CompiledSystem.t)
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

(** The installed planes agree with the combination view — the [Hview]
    hypothesis of [compile_correct], definitionally. *)
Lemma with_combinations_view (compiled : CompiledSystem.t)
    (grid : RawGrid.t) :
  forall column row value : Z,
    PlonkishCompile.combination_view compiled column row = Some value ->
    (with_combinations compiled grid).(RawGrid.cell)
      Raw.ColumnKind.Fixed column row = value.
Proof.
  intros column row value Hview.
  cbn [with_combinations RawGrid.cell].
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
Lemma with_combinations_fixed_off (compiled : CompiledSystem.t)
    (grid : RawGrid.t) (column row : Z)
    (Hout : ~ List.In column compiled.(CompiledSystem.combination_columns)) :
  (with_combinations compiled grid).(RawGrid.cell)
    Raw.ColumnKind.Fixed column row =
  grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row.
Proof.
  cbn [with_combinations RawGrid.cell].
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

(** No fixed query of the expression names a column of the avoid list —
    the decidable disjointness under which installing the combination
    planes cannot change the expression's value. *)
Fixpoint fixed_avoids_b (avoid : list Z)
    (expression : Expression.t Configure.indexed_columns) : bool :=
  match expression with
  | Expression.Constant _ => true
  | Expression.Selector _ => true
  | Expression.Fixed column _ => negb (List.existsb (Z.eqb column) avoid)
  | Expression.Advice _ _ => true
  | Expression.Instance_ _ _ => true
  | Expression.Negated expression => fixed_avoids_b avoid expression
  | Expression.Sum lhs rhs =>
      andb (fixed_avoids_b avoid lhs) (fixed_avoids_b avoid rhs)
  | Expression.Product lhs rhs =>
      andb (fixed_avoids_b avoid lhs) (fixed_avoids_b avoid rhs)
  | Expression.Scaled expression _ => fixed_avoids_b avoid expression
  end.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** Expressions whose fixed queries avoid the combination columns
      evaluate identically on the original and the installed grid. *)
  Lemma with_combinations_eval (compiled : CompiledSystem.t)
      (grid : RawGrid.t) (row : Z)
      (expression : Expression.t Configure.indexed_columns)
      (Havoid :
        fixed_avoids_b compiled.(CompiledSystem.combination_columns)
          expression = true) :
    eval_expression (grid_assignment (with_combinations compiled grid))
      (tt, row) expression =
    eval_expression (grid_assignment grid) (tt, row) expression.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      cbn [fixed_avoids_b] in Havoid;
      try reflexivity.
    - (* Fixed *)
      cbn [eval_expression grid_assignment Assignment.fixed].
      rewrite with_combinations_fixed_off; [reflexivity |].
      apply Bool.negb_true_iff in Havoid.
      intros Hin.
      assert (Hex :
        List.existsb (Z.eqb fixed)
          compiled.(CompiledSystem.combination_columns) = true).
      { apply List.existsb_exists.
        exists fixed.
        split; [exact Hin | apply Z.eqb_refl]. }
      congruence.
    - (* Negated *)
      cbn [eval_expression].
      rewrite (IH Havoid).
      reflexivity.
    - (* Sum *)
      apply Bool.andb_true_iff in Havoid.
      destruct Havoid as [Hl Hr].
      rewrite !eval_expression_sum.
      rewrite (IHl Hl), (IHr Hr).
      reflexivity.
    - (* Product *)
      apply Bool.andb_true_iff in Havoid.
      destruct Havoid as [Hl Hr].
      cbn [eval_expression].
      rewrite (IHl Hl), (IHr Hr).
      reflexivity.
    - (* Scaled *)
      cbn [eval_expression].
      rewrite (IH Havoid).
      reflexivity.
  Qed.
End WithPrime.

(** ** Reading raw copy cells through the permutation cell set *)

Lemma sigma_column_kind_eqb_eq (a b : Raw.ColumnKind.t) :
  Sigma.column_kind_eqb a b = true -> a = b.
Proof.
  destruct a, b; cbn [Sigma.column_kind_eqb]; intros Hab;
    (reflexivity || discriminate).
Qed.

Lemma sigma_column_eqb_eq (a b : Raw.ColumnRef.t) :
  Sigma.column_eqb a b = true -> a = b.
Proof.
  destruct a as [kind_a index_a], b as [kind_b index_b].
  unfold Sigma.column_eqb.
  cbn [Raw.ColumnRef.kind Raw.ColumnRef.index].
  intros Hab.
  apply andb_prop in Hab.
  destruct Hab as [Hkind Hindex].
  apply sigma_column_kind_eqb_eq in Hkind.
  apply Z.eqb_eq in Hindex.
  congruence.
Qed.

Lemma column_position_nth_error (columns : list Raw.ColumnRef.t)
    (column : Raw.ColumnRef.t) (position : nat) :
  Sigma.column_position columns column = Some position ->
  List.nth_error columns position = Some column.
Proof.
  revert position.
  induction columns as [| head columns IH]; intros position Hposition;
    cbn in Hposition; [discriminate |].
  destruct (Sigma.column_eqb head column) eqn:Hhead.
  - injection Hposition as <-.
    cbn [List.nth_error].
    rewrite (sigma_column_eqb_eq head column Hhead).
    reflexivity.
  - destruct (Sigma.column_position columns column) as [tail_position |];
      cbn in Hposition; [| discriminate].
    injection Hposition as <-.
    cbn [List.nth_error].
    exact (IH tail_position eq_refl).
Qed.

(** The value function of the equality-enabled cell set: a [Sigma.cell]
    reads the grid at its permutation column and row. *)
Definition permutation_cell_value (columns : list Raw.ColumnRef.t)
    (grid : RawGrid.t) (c : Sigma.cell) : Z :=
  match List.nth_error columns (fst c) with
  | Some column =>
      grid.(RawGrid.cell)
        column.(Raw.ColumnRef.kind)
        column.(Raw.ColumnRef.index)
        (Z.of_nat (snd c))
  | None => 0
  end.

(** On a resolvable raw cell the value function reads the raw grid cell. *)
Lemma permutation_cell_value_read (columns : list Raw.ColumnRef.t)
    (grid : RawGrid.t) (cell : Raw.Cell.t) (position : nat)
    (Hrow : 0 <= cell.(Raw.Cell.row))
    (Hposition :
      Sigma.column_position columns cell.(Raw.Cell.column) = Some position) :
  permutation_cell_value columns grid
    (position, Z.to_nat cell.(Raw.Cell.row)) =
  raw_cell_read grid cell.
Proof.
  unfold permutation_cell_value, raw_cell_read.
  cbn [fst snd].
  rewrite (column_position_nth_error _ _ _ Hposition).
  rewrite Z2Nat.id by exact Hrow.
  reflexivity.
Qed.

(** Copy events are entries of the extracted copy list. *)
Lemma copies_of_events_in (events : list Raw.Event.t)
    (left right : Raw.Cell.t) :
  List.In (Raw.Event.Copy left right) events ->
  List.In (left, right) (Sigma.copies_of_events events).
Proof.
  intros Hin.
  apply List.in_flat_map.
  exists (Raw.Event.Copy left right).
  split; [exact Hin |].
  left.
  reflexivity.
Qed.

(** ...and conversely: the extraction invents no copies. *)
Lemma copies_of_events_inv (events : list Raw.Event.t)
    (left right : Raw.Cell.t) :
  List.In (left, right) (Sigma.copies_of_events events) ->
  List.In (Raw.Event.Copy left right) events.
Proof.
  intros Hin.
  apply List.in_flat_map in Hin.
  destruct Hin as (event & Hevent & Hpair).
  destruct event; cbn [List.In] in Hpair; try contradiction.
  destruct Hpair as [Heq | Hfalse]; [| contradiction].
  injection Heq as Hleft Hright.
  subst.
  exact Hevent.
Qed.

(** ** The selector plane of a replayed stream

    The two generic halves of the selector-plane linking: the activation
    read of the serialized stream is exactly the [EnableSelector] point
    scan, and selectors outside a checked index bound are never enabled. *)

Lemma enable_pairs_existsb (events : list Raw.Event.t) (s row : Z) :
  List.existsb (Z.eqb row)
    (List.map snd
      (List.filter (fun pair : Z * Z => fst pair =? s)
        (List.flat_map
          (fun event =>
            match event with
            | Raw.Event.EnableSelector selector row' _ => [(selector, row')]
            | _ => []
            end)
          events))) =
  PlonkishMock.enable_selector_at_b events s row.
Proof.
  unfold PlonkishMock.enable_selector_at_b.
  induction events as [| event events IH]; [reflexivity |].
  cbn [List.flat_map List.existsb].
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    cbn [List.app List.filter List.map List.existsb fst snd];
    try exact IH.
  destruct (selector' =? s) eqn:Hsel.
  - cbn [List.map List.existsb snd andb].
    rewrite IH, (Z.eqb_sym row row').
    reflexivity.
  - exact IH.
Qed.

Lemma enable_selector_bounded_off (events : list Raw.Event.t)
    (bound s row : Z)
    (Hbounded :
      List.forallb
        (fun event =>
          match event with
          | Raw.Event.EnableSelector selector _ _ =>
              andb (0 <=? selector) (selector <? bound)
          | _ => true
          end)
        events = true)
    (Hs : ~ (0 <= s < bound)) :
  PlonkishMock.enable_selector_at_b events s row = false.
Proof.
  destruct (PlonkishMock.enable_selector_at_b events s row) eqn:Henable;
    [| reflexivity].
  exfalso.
  unfold PlonkishMock.enable_selector_at_b in Henable.
  apply List.existsb_exists in Henable.
  destruct Henable as (event & Hin & Hcheck).
  rewrite List.forallb_forall in Hbounded.
  specialize (Hbounded _ Hin).
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    try discriminate Hcheck.
  apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [Hselector _].
  apply Z.eqb_eq in Hselector.
  subst selector'.
  apply Bool.andb_true_iff in Hbounded.
  destruct Hbounded as [Hlow Hhigh].
  apply Z.leb_le in Hlow.
  apply Z.ltb_lt in Hhigh.
  lia.
Qed.

(** ** The Orchard domain

    [k = 11] (2048 rows), per the pinned description; the blinding factors
    are computed from the compiled advice query table
    ([CompiledSystem.blinding_factors], the port of
    [ConstraintSystem::blinding_factors]), which the parity certificate
    [advice_queries_match] identifies with the deployed one. *)

Definition orchard_domain : Domain.t := {|
  Domain.k := 11;
  Domain.blinding_factors :=
    CompiledSystem.blinding_factors OrchardCompiledCheck.compiled;
|}.

Lemma orchard_domain_n : Domain.n orchard_domain = 2048.
Proof.
  reflexivity.
Qed.

Lemma orchard_blinding_nonneg : 0 <= orchard_domain.(Domain.blinding_factors).
Proof.
  unfold orchard_domain.
  cbn [Domain.blinding_factors].
  unfold CompiledSystem.blinding_factors.
  lia.
Qed.

(** ** The decidable-premise certificates *)

(** Every [EnableSelector] event names a selector index in [[0, 56)]. *)
Lemma orchard_selectors_bounded :
  List.forallb
    (fun event =>
      match event with
      | Raw.Event.EnableSelector selector _ _ =>
          andb (0 <=? selector) (selector <? 56)
      | _ => true
      end)
    orchard_events = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** Every activation point lies below the usable-row prefix. *)
Lemma orchard_activations_within :
  PlonkishCompile.activations_within_b (Domain.usable_rows orchard_domain)
    OrchardCompiledCheck.orchard_infos = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** Every constraint of the indexed system is a flattened polynomial. *)
Lemma orchard_system_flattened :
  PlonkishCompile.system_flattened_b orchard_indexed_system = true.
Proof.
  unfold orchard_indexed_system.
  apply PlonkishCompile.to_indexed_flattened.
Qed.

(** Every gate constraint is satisfied outright at all-zero selectors. *)
Lemma orchard_gates_vacuous :
  PlonkishMock.gates_selector_vacuous_b (p := Primes.pallas_p)
    orchard_indexed_system = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** Every replaced selector occurs multiplicatively in every gate
    polynomial. *)
Lemma orchard_substitution_ok :
  PlonkishCompile.gates_substitution_ok_b
    (OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments))
    orchard_indexed_system = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** The per-assignment indicator check: at every domain row, each
    assignment's expression evaluates through the combination view to a
    nonzero value exactly on its selector's enabled rows.  The whole
    56-assignment scan costs ≈ 78 s of VM time, so it is sharded into four
    windows of 14 assignments (≈ 20 s each) and reassembled by
    [forallb_chunk4]. *)

Lemma orchard_assignments_ok_shard_0 :
  List.forallb
    (fun assignment =>
      PlonkishCompile.selector_assignment_ok_b (p := Primes.pallas_p)
        (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          assignment.(SelectorAssignment.selector))
        (Z.to_nat (Domain.n orchard_domain))
        assignment)
    (List.firstn 14
      (OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments)))
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_assignments_ok_shard_1 :
  List.forallb
    (fun assignment =>
      PlonkishCompile.selector_assignment_ok_b (p := Primes.pallas_p)
        (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          assignment.(SelectorAssignment.selector))
        (Z.to_nat (Domain.n orchard_domain))
        assignment)
    (List.firstn 14
      (List.skipn 14
        (OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments))))
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_assignments_ok_shard_2 :
  List.forallb
    (fun assignment =>
      PlonkishCompile.selector_assignment_ok_b (p := Primes.pallas_p)
        (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          assignment.(SelectorAssignment.selector))
        (Z.to_nat (Domain.n orchard_domain))
        assignment)
    (List.firstn 14
      (List.skipn 14
        (List.skipn 14
          (OrchardCompiledCheck.compiled
            .(CompiledSystem.selector_assignments)))))
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_assignments_ok_shard_3 :
  List.forallb
    (fun assignment =>
      PlonkishCompile.selector_assignment_ok_b (p := Primes.pallas_p)
        (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          assignment.(SelectorAssignment.selector))
        (Z.to_nat (Domain.n orchard_domain))
        assignment)
    (List.skipn 14
      (List.skipn 14
        (List.skipn 14
          (OrchardCompiledCheck.compiled
            .(CompiledSystem.selector_assignments)))))
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_assignments_ok :
  PlonkishCompile.selector_assignments_ok_b (p := Primes.pallas_p)
    (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
    (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos)
    (Z.to_nat (Domain.n orchard_domain))
    (OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments))
  = true.
Proof.
  unfold PlonkishCompile.selector_assignments_ok_b.
  apply (forallb_chunk4 _ _ 14%nat).
  - exact orchard_assignments_ok_shard_0.
  - exact orchard_assignments_ok_shard_1.
  - exact orchard_assignments_ok_shard_2.
  - exact orchard_assignments_ok_shard_3.
Qed.

(** The finite-domain layout bundle of [plonkish_of_mock_prover]: selector
    footprint inside the usable rows, selector vacuity, gate rotations
    inside the domain, lookup padding pinned to table row [0], tables as
    row prefixes below the usable rows. *)
Lemma orchard_finite_domain_ok :
  PlonkishMock.finite_domain_ok_b (p := Primes.pallas_p) orchard_domain
    orchard_indexed_system orchard_events orchard_table_rows = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** No original gate polynomial queries a combination column: the
    combination planes extend the fixed columns above every configure-time
    index, so installing them cannot change an original gate's value. *)
Lemma orchard_gate_polys_avoid :
  List.forallb
    (fixed_avoids_b
      (OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns)))
    (gate_polys orchard_indexed_system) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** ** The permutation σ of the Orchard copy obligations *)

Definition orchard_copies : list (Raw.Cell.t * Raw.Cell.t) :=
  Sigma.copies_of_events orchard_events.

Definition orchard_n_rows : nat := Z.to_nat (Domain.n orchard_domain).

(** The closed assembly of the 2 964 copy obligations over the pinned
    permutation columns. *)
Definition orchard_sigma : Sigma.t :=
  option_default
    (Sigma.init OrchardCompiledPinned.permutation_columns orchard_n_rows)
    (Sigma.sigma_of_copies OrchardCompiledPinned.permutation_columns
      orchard_n_rows orchard_copies).

(** The σ construction succeeds: every copy names a pinned permutation
    column and an in-range row. *)
Lemma orchard_sigma_some :
  opt_is_some
    (Sigma.sigma_of_copies OrchardCompiledPinned.permutation_columns
      orchard_n_rows orchard_copies) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_sigma_eq :
  Sigma.sigma_of_copies OrchardCompiledPinned.permutation_columns
    orchard_n_rows orchard_copies = Some orchard_sigma.
Proof.
  exact
    (opt_is_some_default
      (Sigma.init OrchardCompiledPinned.permutation_columns orchard_n_rows)
      _ orchard_sigma_some).
Qed.

(** Every copy cell resolves in the pinned permutation columns at a
    nonnegative row — the reading conditions of
    [permutation_cell_value_read]. *)
Lemma orchard_copies_resolvable :
  List.forallb
    (fun pair : Raw.Cell.t * Raw.Cell.t =>
      andb
        (andb
          (0 <=? (fst pair).(Raw.Cell.row))
          (opt_is_some
            (Sigma.column_position OrchardCompiledPinned.permutation_columns
              (fst pair).(Raw.Cell.column))))
        (andb
          (0 <=? (snd pair).(Raw.Cell.row))
          (opt_is_some
            (Sigma.column_position OrchardCompiledPinned.permutation_columns
              (snd pair).(Raw.Cell.column)))))
    orchard_copies = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** ** The selector plane of the replayed Orchard grid

    On every domain row the replayed selector plane is the activation bit
    of [orchard_infos]: enabled points are pinned to [1] by the replay,
    untouched points keep the initial [0], and the activation vectors are
    by construction the [EnableSelector] point scans of the stream. *)

Lemma activation_of_nth (s row : Z) (Hrow : 0 <= row < 2048) :
  List.nth (Z.to_nat row) (OrchardCompiledCheck.activation_of s) false =
  PlonkishMock.enable_selector_at_b orchard_events s row.
Proof.
  assert (Hlt : (Z.to_nat row < 2048)%nat) by lia.
  unfold OrchardCompiledCheck.activation_of.
  rewrite List.map_map.
  rewrite nth_map_seq by exact Hlt.
  cbv beta.
  rewrite Z2Nat.id by lia.
  unfold OrchardCompiledCheck.rows_of, OrchardCompiledCheck.enable_pairs.
  exact (enable_pairs_existsb orchard_events s row).
Qed.

Lemma orchard_info_activations_in (s : Z) (Hs : 0 <= s < 56) :
  PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos s =
  OrchardCompiledCheck.activation_of s.
Proof.
  assert (Hlt : (Z.to_nat s < 56)%nat) by lia.
  unfold PlonkishCompile.info_activations.
  destruct (s <? 0) eqn:Hneg.
  { apply Z.ltb_lt in Hneg.
    exfalso.
    lia. }
  unfold OrchardCompiledCheck.orchard_infos.
  rewrite List.map_map.
  rewrite nth_map_seq by exact Hlt.
  cbv beta.
  cbn [Compile.SelectorInfo.activations].
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma orchard_info_activations_out (s : Z) (Hs : ~ (0 <= s < 56)) :
  PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos s = [].
Proof.
  unfold PlonkishCompile.info_activations.
  destruct (s <? 0) eqn:Hneg; [reflexivity |].
  apply Z.ltb_ge in Hneg.
  apply List.nth_overflow.
  rewrite List.length_map.
  unfold OrchardCompiledCheck.orchard_infos.
  rewrite List.length_map, List.length_seq.
  lia.
Qed.

Lemma orchard_selector_plane
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid) :
  forall s row : Z,
    0 <= row < Domain.n orchard_domain ->
    grid.(RawGrid.sel) s row =
    (if List.nth (Z.to_nat row)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          s)
        false
     then 1 else 0).
Proof.
  intros s row Hrow.
  rewrite orchard_domain_n in Hrow.
  destruct (andb (0 <=? s) (s <? 56)) eqn:Hs.
  - (* A described selector index: the activation bit decides the plane. *)
    apply Bool.andb_true_iff in Hs.
    destruct Hs as [Hlow Hhigh].
    apply Z.leb_le in Hlow.
    apply Z.ltb_lt in Hhigh.
    rewrite (orchard_info_activations_in s (conj Hlow Hhigh)).
    rewrite (activation_of_nth s row Hrow).
    destruct (PlonkishMock.enable_selector_at_b orchard_events s row)
      eqn:Henable.
    + unfold PlonkishMock.enable_selector_at_b in Henable.
      apply List.existsb_exists in Henable.
      destruct Henable as (event & Hin & Hcheck).
      destruct event as
        [ name | name | name | name | selector' row' annotation
        | column' row' annotation value | left_cell right_cell
        | column' from_row to_row value ];
        (* [discriminate] is targeted at [Hcheck]: the bare form scans the
           whole context and whnf-normalizes [Hin], forcing the 19,617-event
           stream on the lazy machine. *)
        try discriminate Hcheck.
      apply Bool.andb_true_iff in Hcheck.
      destruct Hcheck as [Hselector Hrow'].
      apply Z.eqb_eq in Hselector, Hrow'.
      subst selector' row'.
      exact (replay_selector_pinned _ _ _ _ _ _ Hreplay Hin).
    + rewrite (PlonkishMock.replay_selector_off _ _ _ _ _ Hreplay Henable).
      reflexivity.
  - (* Outside the described range: never enabled, empty activations. *)
    assert (Hout : ~ (0 <= s < 56)).
    { apply Bool.andb_false_iff in Hs.
      destruct Hs as [Hs | Hs];
        [apply Z.leb_gt in Hs | apply Z.ltb_ge in Hs];
        clear - Hs;
        lia. }
    rewrite (orchard_info_activations_out s Hout).
    rewrite (PlonkishMock.replay_selector_off _ _ _ _ _ Hreplay
      (enable_selector_bounded_off orchard_events 56 s row
        orchard_selectors_bounded Hout)).
    destruct (Z.to_nat row); reflexivity.
Qed.

(** ** Compiled acceptance of the pinned Orchard system *)

(** [OrchardCompiledCheck.compiled] unfolds to the compilation of the
    indexed Orchard system.  Stated once, closed on the VM: letting the
    unifier prove this by conversion mid-application evaluates the whole
    packing on the lazy machine. *)
Lemma orchard_compiled_eq :
  OrchardCompiledCheck.compiled =
  Compile.compile orchard_indexed_system OrchardCompiledCheck.orchard_infos
    14 OrchardCompiledPinned.permutation_columns
    OrchardCompiledPinned.constants.
Proof.
  vm_cast_no_check
    (@eq_refl CompiledSystem.t OrchardCompiledCheck.compiled).
Qed.

(** The replayed grid with the compiled combination planes installed. *)
Definition orchard_compiled_grid (grid : RawGrid.t) : RawGrid.t :=
  with_combinations OrchardCompiledCheck.compiled grid.

Lemma orchard_compiled_grid_act
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid) :
  forall s row : Z,
    0 <= row < Domain.n orchard_domain ->
    (orchard_compiled_grid grid).(RawGrid.sel) s row =
    (if List.nth (Z.to_nat row)
        (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos
          s)
        false
     then 1 else 0).
Proof.
  intros s row Hrow.
  exact (orchard_selector_plane advice instance_ grid Hreplay s row Hrow).
Qed.

(** Acceptance of the compiled Orchard system over a witness grid:

    - every compiled gate polynomial — the 193 selector-substituted
      polynomials the parity certificates match against the deployed
      description — vanishes on every domain row of the grid with the
      combination planes installed;
    - every lookup argument of the indexed system holds on every domain
      row;
    - the grid is invariant under the permutation σ closed from the copy
      obligations over the pinned permutation columns — the compiled form
      of the permutation argument's content. *)
Definition orchard_compiled_accepts (grid : RawGrid.t) : Prop :=
  PlonkishCompile.compiled_gates_hold orchard_domain
    OrchardCompiledCheck.compiled (orchard_compiled_grid grid) /\
  (forall row : Z,
    0 <= row < Domain.n orchard_domain ->
    List.Forall
      (eval_lookup_argument (grid_assignment grid) (tt, row)
        orchard_table_rows)
      orchard_indexed_system.(ConstraintSystem.lookups)) /\
  grid_invariant
    (permutation_cell_value OrchardCompiledPinned.permutation_columns grid)
    orchard_sigma.

(** ** The compiled-to-operational soundness theorem

    Compiled acceptance of a replayed grid implies acceptance by the ideal
    operational checker: the compiled gates transfer through
    [compile_correct_domain] and the combination-plane agreement, the σ
    invariance yields every copy equality through [sigma_correct], and
    [plonkish_of_mock_prover] extends the domain-row reading to all
    integer rows. *)
Theorem orchard_compiled_sound
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Haccepts : orchard_compiled_accepts grid) :
  mock_prover_accepts orchard_indexed_system orchard_events grid
    orchard_table_rows.
Proof.
  destruct Haccepts as (Hgates & Hlookups & Hsigma).
  (* The compiled gates read back as the selector-gated original gates on
     the installed grid, over the whole domain. *)
  pose proof
    (proj1
      (PlonkishCompile.compile_correct_domain orchard_domain
        orchard_indexed_system OrchardCompiledCheck.orchard_infos 14
        OrchardCompiledPinned.permutation_columns
        OrchardCompiledPinned.constants (orchard_compiled_grid grid)
        OrchardCompiledCheck.compiled orchard_compiled_eq
        orchard_blinding_nonneg
        (orchard_compiled_grid_act advice instance_ grid Hreplay)
        orchard_activations_within
        (with_combinations_view OrchardCompiledCheck.compiled grid)
        orchard_system_flattened orchard_gates_vacuous
        orchard_substitution_ok orchard_assignments_ok)
      Hgates)
    as Hextended_gates.
  (* The original gates never query a combination column, so satisfaction
     transfers from the installed grid to the replayed grid. *)
  assert (Hgates_domain : forall row : Z,
    0 <= row < Domain.n orchard_domain ->
    eval_gates (grid_assignment grid) (tt, row)
      orchard_indexed_system.(ConstraintSystem.gates)).
  { intros row Hrow.
    apply (proj2 (PlonkishCompile.flattened_gates_iff (grid_assignment grid)
      (tt, row) orchard_indexed_system orchard_system_flattened)).
    intros poly Hpoly.
    rewrite <- (with_combinations_eval OrchardCompiledCheck.compiled grid row
      poly
      (proj1 (List.forallb_forall _ _) orchard_gate_polys_avoid poly Hpoly)).
    exact
      (proj1
        (PlonkishCompile.flattened_gates_iff
          (grid_assignment (orchard_compiled_grid grid)) (tt, row)
          orchard_indexed_system orchard_system_flattened)
        (Hextended_gates row Hrow) poly Hpoly). }
  (* σ invariance delivers every copy obligation as a raw cell equality. *)
  assert (Hcopies : forall left right : Raw.Cell.t,
    List.In (Raw.Event.Copy left right) orchard_events ->
    raw_cell_read grid left = raw_cell_read grid right).
  { intros left right Hin.
    pose proof
      (proj1 (List.forallb_forall _ _) orchard_copies_resolvable
        (left, right) (copies_of_events_in orchard_events left right Hin))
      as Hok.
    cbn [fst snd] in Hok.
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok_left Hok_right].
    apply Bool.andb_true_iff in Hok_left.
    destruct Hok_left as [Hrow_left Hpos_left].
    apply Bool.andb_true_iff in Hok_right.
    destruct Hok_right as [Hrow_right Hpos_right].
    apply Z.leb_le in Hrow_left, Hrow_right.
    destruct
      (Sigma.column_position OrchardCompiledPinned.permutation_columns
        left.(Raw.Cell.column))
      as [position_left |] eqn:Hleft; [| discriminate Hpos_left].
    destruct
      (Sigma.column_position OrchardCompiledPinned.permutation_columns
        right.(Raw.Cell.column))
      as [position_right |] eqn:Hright; [| discriminate Hpos_right].
    pose proof
      (proj1 (List.Forall_forall _ _)
        (proj1
          (sigma_correct
            (permutation_cell_value OrchardCompiledPinned.permutation_columns
              grid)
            OrchardCompiledPinned.permutation_columns orchard_n_rows
            orchard_copies orchard_sigma orchard_sigma_eq)
          Hsigma)
        (left, right)
        (copies_of_events_in orchard_events left right Hin))
      as Hcopy.
    unfold copy_holds, resolve_cell in Hcopy.
    cbn [fst snd] in Hcopy.
    rewrite Hleft, Hright in Hcopy.
    rewrite <- (permutation_cell_value_read
      OrchardCompiledPinned.permutation_columns grid left position_left
      Hrow_left Hleft).
    rewrite <- (permutation_cell_value_read
      OrchardCompiledPinned.permutation_columns grid right position_right
      Hrow_right Hright).
    exact Hcopy. }
  exact
    (proj2
      (PlonkishMock.plonkish_of_mock_prover orchard_domain
        orchard_indexed_system orchard_events advice instance_ grid
        orchard_table_rows Hreplay orchard_finite_domain_ok)
      (conj Hgates_domain (conj Hlookups Hcopies))).
Qed.

(** ** The compiled-to-operational completeness theorem

    The converse of [orchard_compiled_sound], along the same three seams
    read backwards — each of them an equivalence.
    [PlonkishMock.plonkish_of_mock_prover] restricts the all-integer-row
    reading of the ideal checker to the domain rows;
    [PlonkishCompile.compile_correct_domain] turns the selector-gated
    original gates back into the compiled ones on the installed grid; and
    [sigma_correct] closes the copy equalities back into σ invariance. *)
Theorem orchard_compiled_complete
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Haccepts :
      mock_prover_accepts orchard_indexed_system orchard_events grid
        orchard_table_rows) :
  orchard_compiled_accepts grid.
Proof.
  destruct
    (proj1
      (PlonkishMock.plonkish_of_mock_prover orchard_domain
        orchard_indexed_system orchard_events advice instance_ grid
        orchard_table_rows Hreplay orchard_finite_domain_ok)
      Haccepts)
    as (Hgates_domain & Hlookups & Hcopies).
  refine (conj _ (conj Hlookups _)).
  - (* The original gates transfer to the installed grid, where
       [compile_correct_domain] reads them back as the compiled ones. *)
    apply
      (proj2
        (PlonkishCompile.compile_correct_domain orchard_domain
          orchard_indexed_system OrchardCompiledCheck.orchard_infos 14
          OrchardCompiledPinned.permutation_columns
          OrchardCompiledPinned.constants (orchard_compiled_grid grid)
          OrchardCompiledCheck.compiled orchard_compiled_eq
          orchard_blinding_nonneg
          (orchard_compiled_grid_act advice instance_ grid Hreplay)
          orchard_activations_within
          (with_combinations_view OrchardCompiledCheck.compiled grid)
          orchard_system_flattened orchard_gates_vacuous
          orchard_substitution_ok orchard_assignments_ok)).
    unfold orchard_compiled_grid.
    intros row Hrow.
    apply
      (proj2
        (PlonkishCompile.flattened_gates_iff
          (grid_assignment
            (with_combinations OrchardCompiledCheck.compiled grid))
          (tt, row) orchard_indexed_system orchard_system_flattened)).
    intros poly Hpoly.
    rewrite (with_combinations_eval OrchardCompiledCheck.compiled grid row
      poly
      (proj1 (List.forallb_forall _ _) orchard_gate_polys_avoid poly Hpoly)).
    exact
      (proj1
        (PlonkishCompile.flattened_gates_iff (grid_assignment grid) (tt, row)
          orchard_indexed_system orchard_system_flattened)
        (Hgates_domain row Hrow) poly Hpoly).
  - (* Every copy obligation holds as a raw cell equality, so σ closes. *)
    apply
      (proj2
        (sigma_correct
          (permutation_cell_value OrchardCompiledPinned.permutation_columns
            grid)
          OrchardCompiledPinned.permutation_columns orchard_n_rows
          orchard_copies orchard_sigma orchard_sigma_eq)).
    apply List.Forall_forall.
    intros pair Hpair.
    pose proof
      (proj1 (List.forallb_forall _ _) orchard_copies_resolvable pair Hpair)
      as Hok.
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok_left Hok_right].
    apply Bool.andb_true_iff in Hok_left.
    destruct Hok_left as [Hrow_left Hpos_left].
    apply Bool.andb_true_iff in Hok_right.
    destruct Hok_right as [Hrow_right Hpos_right].
    apply Z.leb_le in Hrow_left, Hrow_right.
    unfold copy_holds, resolve_cell.
    destruct
      (Sigma.column_position OrchardCompiledPinned.permutation_columns
        (fst pair).(Raw.Cell.column))
      as [position_left |] eqn:Hleft; [| exact I].
    destruct
      (Sigma.column_position OrchardCompiledPinned.permutation_columns
        (snd pair).(Raw.Cell.column))
      as [position_right |] eqn:Hright; [| exact I].
    rewrite (permutation_cell_value_read
      OrchardCompiledPinned.permutation_columns grid (fst pair) position_left
      Hrow_left Hleft).
    rewrite (permutation_cell_value_read
      OrchardCompiledPinned.permutation_columns grid (snd pair)
      position_right Hrow_right Hright).
    apply Hcopies.
    apply copies_of_events_inv.
    rewrite <- (surjective_pairing pair).
    exact Hpair.
Qed.

(** ** Composition down to the Action statement *)

(** Compiled acceptance gives the relational [circuit_holds] of the
    realized assignment — the [Holds] hypothesis of the Orchard action
    theorem surface. *)
Theorem orchard_compiled_operational_sound
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Haccepts : orchard_compiled_accepts grid) :
  circuit_holds (realize Index.indices region_start_of grid)
    Garden.Orchard.circuit.synthesize
    orchard_system.
Proof.
  exact (orchard_operational_sound advice instance_ grid Hreplay
    (orchard_compiled_sound advice instance_ grid Hreplay Haccepts)).
Qed.

(** Compiled acceptance, together with the four witness-honesty side
    conditions, gives the §4.18.4 Action statement and
    [ValidActionInputs] of the realized assignment: the chain from the
    deployed compiled description — pinned by the parity certificates —
    ends at the protocol surface. *)
Corollary orchard_compiled_action_statement
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Haccepts : orchard_compiled_accepts grid)
    (Hmerkle_ok :
      Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle.merkle_witness_ok
        (realize Index.indices region_start_of grid))
    (Hnote_ok :
      Garden.Orchard.circuit_proof.note_commit.cmx.NoteCommitNewCmx
        .note_commit_witness_ok
        (realize Index.indices region_start_of grid))
    (Hold_note_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .old_note_witness_ok
        (realize Index.indices region_start_of grid))
    (Hivk_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .commit_ivk_witness_ok
        (realize Index.indices region_start_of grid)) :
  (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs.read_action_outputs
      (realize Index.indices region_start_of grid) =
    Garden.Orchard.protocol_spec.OrchardProtocolSpec.orchard_action_spec
      Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .orchard_circuit_params
      (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .read_action_inputs
        (realize Index.indices region_start_of grid))) /\
  Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
    .ValidActionInputs
    (realize Index.indices region_start_of grid).
Proof.
  exact (orchard_action_statement_operational advice instance_ grid Hreplay
    (orchard_compiled_sound advice instance_ grid Hreplay Haccepts)
    Hmerkle_ok Hnote_ok Hold_note_ok Hivk_ok).
Qed.

End OrchardCompiled.
