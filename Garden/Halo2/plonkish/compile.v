(** * Compilation correctness: compiled-gate satisfaction ↔ selector gating.

    [Compile.compile] ([plonkish/main.v]) substitutes every packed selector
    of the indexed system by an indicator polynomial over its combination
    fixed column, and every retained selector by a plain 0/1 fixed-column
    query.  This file proves the substitution correct: for a grid whose
    selector planes are boolean and [0] off the program-enabled points, the
    compiled gate polynomials vanish on every row of the cyclic domain
    [[0, 2^k)] exactly when the original selector-gated gates hold on the
    usable-row prefix ([compile_correct]).

    Two lemma families carry the proof:

    - indicator-polynomial evaluation ([indicator_expression_eval] /
      [indicator_expression_on] / [indicator_expression_off]): at a row
      where the combination column holds value [w], the indicator for
      assigned root [v] evaluates to a nonzero constant when [w = v] and to
      [0] when [w] is [0] or another combination value distinct from [v] —
      the distinctness of the assigned values per combination column enters
      as the [value <> root] / range side conditions, which are computable
      on a concrete compiled system.  The per-assignment semantic content is
      packaged as one decidable check over the compiled output
      ([selector_assignments_ok_b], evaluated row by row through the
      fixed-plane evaluator [eval_fixed_expression]), so the theorem never
      inspects the packing choices;
    - blinding-row vacuity ([compiled_gates_blinding_vacuous]): off the
      usable rows every selector is disabled ([activations_within_b], a
      computable fact of the activation vectors) and every combination
      column reads [0] (the same [selector_assignments_ok_b] rows), so both
      the original and the compiled gates vanish there — every compiled
      gate carries its selector-derived fixed factor, which is [0] outside
      the usable prefix.

    Allocation independence: no statement below mentions which combination
    column a selector landed in.  The hypotheses constrain the compiled
    output as a whole — the grid agrees with the combination values
    ([combination_view]), and each assignment's expression tracks its
    selector's activations ([selector_assignments_ok_b]) — and hold for any
    allocation; only the parity certificate pins the concrete Rust choices.

    The equivalence composes with [plonkish_of_mock_prover]
    ([plonkish/mock.v]) at the [[0, n)] satisfaction interface:
    [compile_correct_domain] restates the original side over the full
    domain, which is the gate conjunct of [plonkish_accepts]. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.mock.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module PlonkishCompile.

Import Plonkish.

(** [Plonky3.M] carries an inner [List] module (monadic folds) that shadows
    the qualified [List.fold_left]; the alias pins the standard one. *)
Module StdList := Stdlib.Lists.List.

(** The compiled gates are exactly the flattened gate polynomials with the
    assignment replacement substituted in. *)
Lemma compile_gates_substituted
    (system : ConstraintSystem.t Configure.indexed_columns)
    (infos : list Compile.SelectorInfo.t)
    (num_fixed_columns : Z)
    (permutation_columns : list Raw.ColumnRef.t)
    (constants : list Z) :
  (Compile.compile system infos num_fixed_columns permutation_columns
    constants).(CompiledSystem.gates) =
  List.map
    (substitute_selectors
      (Compile.assignment_replacement
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.selector_assignments)))
    (gate_polys system).
Proof.
  unfold Compile.compile, Compile.compile_with_minimum,
    Compile.assignment_replacement.
  cbv zeta.
  destruct (Compress.process _ _ _) as [combinations assignments].
  reflexivity.
Qed.

(** ** Multiplicative substitution positions

    [substitute_selectors] preserves the zero set of an expression when
    every replaced selector occurs multiplicatively: replaced selectors may
    sit under [Negated], [Scaled] and [Product] nodes, but not under a
    [Sum].  This is the shape Rust enforces for simple selectors (the
    [Add]/[Sub] impls of [Expression] reject simple selectors), and the
    flattened [Select]-guarded constraints of [Configure.to_indexed] have
    it: the selector is the left factor of a top-level [Product]. *)

Fixpoint contains_replaced_b
    (replacement : Z -> option (Expression.t Configure.indexed_columns))
    (expression : Expression.t Configure.indexed_columns)
    : bool :=
  match expression with
  | Expression.Constant _ => false
  | Expression.Selector selector =>
      match replacement selector with
      | Some _ => true
      | None => false
      end
  | Expression.Fixed _ _ => false
  | Expression.Advice _ _ => false
  | Expression.Instance_ _ _ => false
  | Expression.Negated expression => contains_replaced_b replacement expression
  | Expression.Sum lhs rhs =>
      orb (contains_replaced_b replacement lhs)
        (contains_replaced_b replacement rhs)
  | Expression.Product lhs rhs =>
      orb (contains_replaced_b replacement lhs)
        (contains_replaced_b replacement rhs)
  | Expression.Scaled expression _ => contains_replaced_b replacement expression
  end.

Lemma substitute_selectors_id
    (replacement : Z -> option (Expression.t Configure.indexed_columns))
    (expression : Expression.t Configure.indexed_columns) :
  contains_replaced_b replacement expression = false ->
  substitute_selectors replacement expression = expression.
Proof.
  induction expression as
    [ constant | selector | fixed rotation | advice rotation
    | instance rotation | expression IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | expression IH scale ];
    intros Hfree; cbn in Hfree; cbn [substitute_selectors];
    try reflexivity.
  - (* Selector *)
    destruct (replacement selector); [discriminate | reflexivity].
  - (* Negated *)
    rewrite (IH Hfree).
    reflexivity.
  - (* Sum *)
    apply Bool.orb_false_iff in Hfree.
    destruct Hfree as [Hl Hr].
    rewrite (IHl Hl), (IHr Hr).
    reflexivity.
  - (* Product *)
    apply Bool.orb_false_iff in Hfree.
    destruct Hfree as [Hl Hr].
    rewrite (IHl Hl), (IHr Hr).
    reflexivity.
  - (* Scaled *)
    rewrite (IH Hfree).
    reflexivity.
Qed.

Fixpoint substitution_multiplicative_b
    (replacement : Z -> option (Expression.t Configure.indexed_columns))
    (expression : Expression.t Configure.indexed_columns)
    : bool :=
  match expression with
  | Expression.Constant _ => true
  | Expression.Selector _ => true
  | Expression.Fixed _ _ => true
  | Expression.Advice _ _ => true
  | Expression.Instance_ _ _ => true
  | Expression.Negated expression =>
      substitution_multiplicative_b replacement expression
  | Expression.Sum lhs rhs =>
      andb (negb (contains_replaced_b replacement lhs))
        (negb (contains_replaced_b replacement rhs))
  | Expression.Product lhs rhs =>
      andb (substitution_multiplicative_b replacement lhs)
        (substitution_multiplicative_b replacement rhs)
  | Expression.Scaled expression _ =>
      substitution_multiplicative_b replacement expression
  end.

(** Every flattened gate polynomial of the system is in multiplicative
    position for the compiled system's replacement — a decidable
    well-formedness fact of the concrete system and packing output. *)
Definition gates_substitution_ok_b
    (assignments : list SelectorAssignment.t)
    (system : ConstraintSystem.t Configure.indexed_columns)
    : bool :=
  List.forallb
    (substitution_multiplicative_b (Compile.assignment_replacement assignments))
    (gate_polys system).

(** ** Flattened systems

    Every constraint of the indexed system is an [EqualZeroToPrecise]
    polynomial — the shape [Configure.to_indexed] produces, under which
    gate satisfaction is exactly the vanishing of the flattened gate
    polynomials. *)

Definition constraint_flattened_b {columns0 : Columns.t}
    (constraint : Constraint.t columns0) : bool :=
  match constraint with
  | Constraint.EqualZeroToPrecise _ => true
  | _ => false
  end.

Definition system_flattened_b {columns0 : Columns.t}
    (system : ConstraintSystem.t columns0) : bool :=
  List.forallb
    (fun gate =>
      List.forallb
        (fun named_constraint =>
          constraint_flattened_b (snd named_constraint))
        gate.(Gate.constraints))
    system.(ConstraintSystem.gates).

Lemma to_indexed_flattened {columns0 : Columns.t}
    (indices : Indices.t columns0)
    (system : ConstraintSystem.t columns0) :
  system_flattened_b (Configure.to_indexed indices system) = true.
Proof.
  unfold system_flattened_b.
  apply List.forallb_forall.
  intros gate Hgate.
  cbn in Hgate.
  apply List.in_map_iff in Hgate.
  destruct Hgate as (gate0 & Hgate & _).
  subst gate.
  apply List.forallb_forall.
  intros named_constraint Hin.
  unfold Configure.map_gate in Hin.
  cbn in Hin.
  unfold Configure.map_constraints in Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as (named_constraint0 & Hin & _).
  destruct named_constraint0 as [name constraint].
  subst named_constraint.
  reflexivity.
Qed.

(** ** The combination fixed planes of a compiled system

    The value pinned by the compiled output for a combination column at a
    row: [None] off the combination columns or outside the value vector. *)

Fixpoint column_values
    (columns : list Z)
    (values : list (list Z))
    (column : Z)
    : option (list Z) :=
  match columns, values with
  | [], _ | _, [] => None
  | c :: columns, v :: values =>
      if c =? column then Some v else column_values columns values column
  end.

Definition combination_view (compiled : CompiledSystem.t)
    (column row : Z) : option Z :=
  match
    column_values
      compiled.(CompiledSystem.combination_columns)
      compiled.(CompiledSystem.combination_assignments)
      column
  with
  | Some values =>
      if andb (0 <=? row) (row <? Z.of_nat (List.length values))
      then Some (List.nth (Z.to_nat row) values 0)
      else None
  | None => None
  end.

(** ** Selector activations

    The activation vector of a selector index, read off the compilation
    input; selectors outside the described range have no enabled rows. *)

Definition info_activations
    (infos : list Compile.SelectorInfo.t)
    (selector : Z)
    : list bool :=
  if selector <? 0 then []
  else
    List.nth
      (Z.to_nat selector)
      (List.map Compile.SelectorInfo.activations infos)
      [].

(** Every enabled activation point lies below [bound] — the computable
    counterpart, on the compilation input, of the selector footprint
    staying inside the usable-row prefix. *)
Definition activations_within_b
    (bound : Z)
    (infos : list Compile.SelectorInfo.t)
    : bool :=
  List.forallb
    (fun info =>
      List.forallb
        (fun (indexed : nat * bool) =>
          if snd indexed then Z.of_nat (fst indexed) <? bound else true)
        (enumerate info.(Compile.SelectorInfo.activations)))
    infos.

Lemma enumerate_nth_In {A : Set} (l : list A) (d : A) (i : nat) :
  (i < List.length l)%nat ->
  List.In (i, List.nth i l d) (enumerate l).
Proof.
  intros Hi.
  unfold enumerate.
  replace (i, List.nth i l d)
    with (List.nth i (List.combine (List.seq 0 (List.length l)) l) (O, d)).
  - apply List.nth_In.
    rewrite List.length_combine, List.length_seq.
    lia.
  - rewrite List.combine_nth by apply List.length_seq.
    rewrite List.seq_nth by exact Hi.
    reflexivity.
Qed.

Lemma activations_within_off
    (bound : Z)
    (infos : list Compile.SelectorInfo.t)
    (Hwithin : activations_within_b bound infos = true)
    (selector row : Z)
    (Hrow : 0 <= row)
    (Hbound : bound <= row) :
  List.nth (Z.to_nat row) (info_activations infos selector) false = false.
Proof.
  unfold info_activations.
  destruct (selector <? 0); [destruct (Z.to_nat row); reflexivity |].
  destruct (List.nth_error infos (Z.to_nat selector)) as [info |] eqn:Hinfo.
  - assert (Hnth :
      List.nth (Z.to_nat selector)
        (List.map Compile.SelectorInfo.activations infos) [] =
      info.(Compile.SelectorInfo.activations)).
    { apply List.nth_error_nth.
      apply List.map_nth_error.
      exact Hinfo. }
    rewrite Hnth.
    destruct
      (Nat.lt_ge_cases (Z.to_nat row)
        (List.length info.(Compile.SelectorInfo.activations)))
      as [Hlt | Hge].
    2: { apply List.nth_overflow. exact Hge. }
    destruct
      (List.nth (Z.to_nat row) info.(Compile.SelectorInfo.activations) false)
      eqn:Hbit; [| reflexivity].
    exfalso.
    unfold activations_within_b in Hwithin.
    rewrite List.forallb_forall in Hwithin.
    specialize (Hwithin info (List.nth_error_In _ _ Hinfo)).
    rewrite List.forallb_forall in Hwithin.
    pose proof
      (enumerate_nth_In info.(Compile.SelectorInfo.activations) false
        (Z.to_nat row) Hlt) as Hpair.
    rewrite Hbit in Hpair.
    specialize (Hwithin _ Hpair).
    cbn in Hwithin.
    apply Z.ltb_lt in Hwithin.
    lia.
  - apply List.nth_error_None in Hinfo.
    rewrite
      (List.nth_overflow (List.map Compile.SelectorInfo.activations infos))
      by (rewrite List.length_map; exact Hinfo).
    destruct (Z.to_nat row); reflexivity.
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** Reduced evaluation values

      Every expression evaluation lands in the canonical residue range:
      the head operation of each branch is a [mod p]. *)

  Lemma from_opp (x : Z) : UnOp.from (UnOp.opp x) = UnOp.opp x.
  Proof.
    unfold UnOp.from, UnOp.opp.
    apply Z.mod_mod.
    pose proof (prime_range (p := p)).
    lia.
  Qed.

  Lemma eval_expression_reduced {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (expression : Expression.t columns0) :
    UnOp.from (eval_expression Γ (region, row) expression) =
    eval_expression Γ (region, row) expression.
  Proof.
    destruct expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression | lhs rhs | lhs rhs
      | expression scale ].
    - apply FieldRewrite.from_from.
    - cbn [eval_expression].
      unfold eval_selector.
      apply FieldRewrite.from_from.
    - apply FieldRewrite.from_from.
    - apply FieldRewrite.from_from.
    - apply FieldRewrite.from_from.
    - cbn [eval_expression].
      apply from_opp.
    - rewrite eval_expression_sum.
      apply FieldRewrite.from_add.
    - cbn [eval_expression].
      apply FieldRewrite.from_mul.
    - cbn [eval_expression].
      apply FieldRewrite.from_mul.
  Qed.

  Lemma opp_mul_right (u x : Z) :
    UnOp.opp (BinOp.mul u x) = BinOp.mul u (UnOp.opp x).
  Proof.
    unfold UnOp.opp, BinOp.mul.
    rewrite Zmult_mod_idemp_r.
    rewrite <- (Z.sub_0_l ((u * x) mod p)).
    rewrite Zminus_mod_idemp_r.
    f_equal.
    ring.
  Qed.

  Lemma mul_mul_shuffle (ul xl ur xr : Z) :
    BinOp.mul (BinOp.mul ul xl) (BinOp.mul ur xr) =
    BinOp.mul (ul * ur) (BinOp.mul xl xr).
  Proof.
    unfold BinOp.mul.
    rewrite !Zmult_mod_idemp_l, !Zmult_mod_idemp_r.
    f_equal.
    ring.
  Qed.

  Lemma mul_assoc_left (u x s : Z) :
    BinOp.mul (BinOp.mul u x) s = BinOp.mul u (BinOp.mul x s).
  Proof.
    unfold BinOp.mul.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
    f_equal.
    ring.
  Qed.

  Lemma mul_one_eval {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (expression : Expression.t columns0) :
    BinOp.mul 1 (eval_expression Γ (region, row) expression) =
    eval_expression Γ (region, row) expression.
  Proof.
    rewrite FieldRewrite.mul_one_left.
    apply eval_expression_reduced.
  Qed.

  Lemma mul_eval_one {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (expression : Expression.t columns0) :
    BinOp.mul (eval_expression Γ (region, row) expression) 1 =
    eval_expression Γ (region, row) expression.
  Proof.
    rewrite FieldRewrite.mul_one_right.
    apply eval_expression_reduced.
  Qed.

  (** ** The substitution lemma

      With every replaced selector either off (both the selector and its
      replacement evaluate to [0]) or on (the selector evaluates to [1] and
      the replacement to a nonzero value), substituting into an expression
      in multiplicative position rescales its value by a nonzero field
      element — so the zero set is preserved. *)

  Lemma substitute_selectors_eval {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (replacement : Z -> option (Expression.t Configure.indexed_columns))
      (Hval : forall (s : Z) (e : Expression.t Configure.indexed_columns),
        replacement s = Some e ->
        (eval_selector Γ (region, row) s = 0 /\
          eval_expression Γ (region, row) e = 0) \/
        (eval_selector Γ (region, row) s = 1 /\
          eval_expression Γ (region, row) e <> 0))
      (expression : Expression.t Configure.indexed_columns) :
    substitution_multiplicative_b replacement expression = true ->
    exists u : Z,
      UnOp.from u <> 0 /\
      eval_expression Γ (region, row)
        (substitute_selectors replacement expression) =
      BinOp.mul u (eval_expression Γ (region, row) expression).
  Proof.
    assert (Hone : UnOp.from 1 <> 0).
    { rewrite FieldRewrite.from_one. lia. }
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      intros Hok.
    - (* Constant *)
      exists 1.
      split; [exact Hone |].
      cbn [substitute_selectors].
      symmetry.
      apply mul_one_eval.
    - (* Selector *)
      cbn [substitute_selectors].
      destruct (replacement selector) as [e |] eqn:Hrepl.
      + destruct (Hval selector e Hrepl) as [ [Hsel He] | [Hsel He] ].
        * exists 1.
          split; [exact Hone |].
          rewrite He.
          cbn [eval_expression].
          rewrite Hsel.
          reflexivity.
        * exists (eval_expression Γ (region, row) e).
          split; [rewrite eval_expression_reduced; exact He |].
          cbn [eval_expression].
          rewrite Hsel.
          symmetry.
          apply mul_eval_one.
      + exists 1.
        split; [exact Hone |].
        symmetry.
        apply mul_one_eval.
    - (* Fixed *)
      exists 1.
      split; [exact Hone |].
      cbn [substitute_selectors].
      symmetry.
      apply mul_one_eval.
    - (* Advice *)
      exists 1.
      split; [exact Hone |].
      cbn [substitute_selectors].
      symmetry.
      apply mul_one_eval.
    - (* Instance_ *)
      exists 1.
      split; [exact Hone |].
      cbn [substitute_selectors].
      symmetry.
      apply mul_one_eval.
    - (* Negated *)
      cbn [substitution_multiplicative_b] in Hok.
      destruct (IH Hok) as (u & Hu & Heq).
      exists u.
      split; [exact Hu |].
      cbn [substitute_selectors].
      cbn [eval_expression].
      rewrite Heq.
      apply opp_mul_right.
    - (* Sum *)
      cbn [substitution_multiplicative_b] in Hok.
      apply Bool.andb_true_iff in Hok.
      destruct Hok as [Hl Hr].
      apply Bool.negb_true_iff in Hl, Hr.
      exists 1.
      split; [exact Hone |].
      cbn [substitute_selectors].
      rewrite (substitute_selectors_id replacement lhs Hl).
      rewrite (substitute_selectors_id replacement rhs Hr).
      symmetry.
      apply mul_one_eval.
    - (* Product *)
      cbn [substitution_multiplicative_b] in Hok.
      apply Bool.andb_true_iff in Hok.
      destruct Hok as [Hokl Hokr].
      destruct (IHl Hokl) as (ul & Hul & Heql).
      destruct (IHr Hokr) as (ur & Hur & Heqr).
      exists (ul * ur).
      split.
      { intros Hzero.
        change (UnOp.from (ul * ur)) with (BinOp.mul ul ur) in Hzero.
        destruct (proj1 (mul_zero_implies_zero ul ur) Hzero) as [Hz | Hz];
          [exact (Hul Hz) | exact (Hur Hz)]. }
      cbn [substitute_selectors].
      cbn [eval_expression].
      rewrite Heql, Heqr.
      apply mul_mul_shuffle.
    - (* Scaled *)
      cbn [substitution_multiplicative_b] in Hok.
      destruct (IH Hok) as (u & Hu & Heq).
      exists u.
      split; [exact Hu |].
      cbn [substitute_selectors].
      cbn [eval_expression].
      rewrite Heq.
      apply mul_assoc_left.
  Qed.

  Lemma substitute_selectors_zero_iff {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (replacement : Z -> option (Expression.t Configure.indexed_columns))
      (Hval : forall (s : Z) (e : Expression.t Configure.indexed_columns),
        replacement s = Some e ->
        (eval_selector Γ (region, row) s = 0 /\
          eval_expression Γ (region, row) e = 0) \/
        (eval_selector Γ (region, row) s = 1 /\
          eval_expression Γ (region, row) e <> 0))
      (expression : Expression.t Configure.indexed_columns)
      (Hok : substitution_multiplicative_b replacement expression = true) :
    eval_expression Γ (region, row)
      (substitute_selectors replacement expression) = 0 <->
    eval_expression Γ (region, row) expression = 0.
  Proof.
    destruct
      (substitute_selectors_eval Γ region row replacement Hval expression Hok)
      as (u & Hu & Heq).
    rewrite Heq.
    split.
    - intros Hzero.
      destruct (proj1 (mul_zero_implies_zero _ _) Hzero) as [Hz | Hz];
        [contradiction |].
      rewrite eval_expression_reduced in Hz.
      exact Hz.
    - intros Hzero.
      rewrite Hzero.
      apply FieldRewrite.mul_zero_right.
  Qed.

  (** ** Indicator-polynomial evaluation

      The value of [Compress.indicator_expression]: the query value times
      the product of [(root - query)] over the non-assigned roots.  At the
      assigned root the value is a nonzero constant (all factors are
      differences of distinct values below [p] — the distinctness of the
      assigned combination values); at [0] or at another combination value
      it is [0]. *)

  Definition indicator_value (combination_len : nat) (assigned_root value : Z)
      : Z :=
    StdList.fold_left
      (fun acc root =>
        if root =? assigned_root then acc
        else BinOp.mul acc (BinOp.sub root value))
      (List.map Z.of_nat (List.seq 1 combination_len))
      value.

  Lemma indicator_fold_eval {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (query : Expression.t Configure.indexed_columns)
      (assigned_root : Z)
      (roots : list Z) :
    forall acc : Expression.t Configure.indexed_columns,
      eval_expression Γ (region, row)
        (StdList.fold_left
          (fun expression root =>
            if root =? assigned_root then expression
            else
              Expression.Product
                expression
                (Expression.Sum (Expression.Constant root)
                  (Expression.Negated query)))
          roots
          acc) =
      StdList.fold_left
        (fun value root =>
          if root =? assigned_root then value
          else
            BinOp.mul value
              (BinOp.sub root (eval_expression Γ (region, row) query)))
        roots
        (eval_expression Γ (region, row) acc).
  Proof.
    induction roots as [| root roots IH]; intros acc; cbn [StdList.fold_left].
    - reflexivity.
    - destruct (root =? assigned_root); [apply IH |].
      rewrite IH.
      cbn [eval_expression].
      rewrite FieldRewrite.sub_from_left.
      reflexivity.
  Qed.

  Lemma indicator_expression_eval {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (query : Expression.t Configure.indexed_columns)
      (combination_len : nat)
      (assigned_root : Z) :
    eval_expression Γ (region, row)
      (Compress.indicator_expression query combination_len assigned_root) =
    indicator_value combination_len assigned_root
      (eval_expression Γ (region, row) query).
  Proof.
    unfold Compress.indicator_expression, indicator_value.
    apply indicator_fold_eval.
  Qed.

  Lemma indicator_fold_nonzero (assigned_root bound : Z)
      (Hassigned : 1 <= assigned_root <= bound)
      (Hbound : bound < p)
      (roots : list Z) :
    forall acc : Z,
      List.Forall (fun root => 1 <= root <= bound) roots ->
      UnOp.from acc = acc ->
      acc <> 0 ->
      UnOp.from
        (StdList.fold_left
          (fun value root =>
            if root =? assigned_root then value
            else BinOp.mul value (BinOp.sub root assigned_root))
          roots
          acc) =
      StdList.fold_left
        (fun value root =>
          if root =? assigned_root then value
          else BinOp.mul value (BinOp.sub root assigned_root))
        roots
        acc /\
      StdList.fold_left
        (fun value root =>
          if root =? assigned_root then value
          else BinOp.mul value (BinOp.sub root assigned_root))
        roots
        acc <> 0.
  Proof.
    induction roots as [| root roots IH];
      intros acc Hroots Hreduced Hnonzero; cbn [StdList.fold_left].
    - split; [exact Hreduced | exact Hnonzero].
    - inversion Hroots as [| ? ? Hroot Hrest]; subst.
      destruct (root =? assigned_root) eqn:Hcase.
      + exact (IH acc Hrest Hreduced Hnonzero).
      + apply Z.eqb_neq in Hcase.
        apply IH; [exact Hrest | apply FieldRewrite.from_mul |].
        intros Hzero.
        destruct (proj1 (mul_zero_implies_zero _ _) Hzero) as [Hz | Hz].
        * rewrite Hreduced in Hz.
          exact (Hnonzero Hz).
        * rewrite FieldRewrite.from_sub in Hz.
          assert (Hbounds : -p < root - assigned_root < p) by lia.
          pose proof (proj1 (is_zero_small _ Hbounds) Hz) as Hdiff.
          lia.
  Qed.

  (** At a row where the combination column reads back the assigned root,
      the indicator value is nonzero. *)
  Lemma indicator_value_root_nonzero (combination_len : nat)
      (assigned_root : Z)
      (Hroot : 1 <= assigned_root <= Z.of_nat combination_len)
      (Hlen : Z.of_nat combination_len < p) :
    indicator_value combination_len assigned_root assigned_root <> 0.
  Proof.
    unfold indicator_value.
    refine
      (proj2
        (indicator_fold_nonzero assigned_root (Z.of_nat combination_len)
          Hroot Hlen _ assigned_root _ _ _)).
    - apply List.Forall_forall.
      intros root Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as (k & Hk & Hin).
      apply List.in_seq in Hin.
      lia.
    - unfold UnOp.from.
      apply Z.mod_small.
      lia.
    - lia.
  Qed.

  Lemma indicator_fold_zero_absorb (assigned_root value : Z)
      (roots : list Z) :
    StdList.fold_left
      (fun acc root =>
        if root =? assigned_root then acc
        else BinOp.mul acc (BinOp.sub root value))
      roots
      0 = 0.
  Proof.
    induction roots as [| root roots IH]; cbn [StdList.fold_left].
    - reflexivity.
    - destruct (root =? assigned_root); [exact IH |].
      rewrite FieldRewrite.mul_zero_left.
      exact IH.
  Qed.

  (** At a row where the combination column reads [0] (every member
      selector off) or another member's assigned value, the indicator
      value is [0]. *)
  Lemma indicator_value_off_zero (combination_len : nat)
      (assigned_root value : Z)
      (Hvalue :
        value = 0 \/
        (1 <= value <= Z.of_nat combination_len /\ value <> assigned_root)) :
    indicator_value combination_len assigned_root value = 0.
  Proof.
    unfold indicator_value.
    destruct Hvalue as [Hvalue | [Hrange Hdistinct] ].
    - subst value.
      apply indicator_fold_zero_absorb.
    - assert (Hin : List.In value (List.map Z.of_nat (List.seq 1 combination_len))).
      { apply List.in_map_iff.
        exists (Z.to_nat value).
        split; [lia |].
        apply List.in_seq.
        lia. }
      apply List.in_split in Hin.
      destruct Hin as (prefix & suffix & Hsplit).
      rewrite Hsplit, StdList.fold_left_app.
      cbn [StdList.fold_left].
      destruct (value =? assigned_root) eqn:Hcase;
        [apply Z.eqb_eq in Hcase; lia |].
      assert (Hself : BinOp.sub value value = 0).
      { unfold BinOp.sub.
        rewrite Z.sub_diag.
        reflexivity. }
      rewrite Hself, FieldRewrite.mul_zero_right.
      apply indicator_fold_zero_absorb.
  Qed.

  (** The two headline readings: the indicator for assigned root [v]
      evaluated where the combination column holds [w]. *)

  Lemma indicator_expression_on {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (query : Expression.t Configure.indexed_columns)
      (combination_len : nat)
      (assigned_root : Z)
      (Hroot : 1 <= assigned_root <= Z.of_nat combination_len)
      (Hlen : Z.of_nat combination_len < p)
      (Hquery : eval_expression Γ (region, row) query = assigned_root) :
    eval_expression Γ (region, row)
      (Compress.indicator_expression query combination_len assigned_root)
      <> 0.
  Proof.
    rewrite indicator_expression_eval, Hquery.
    exact (indicator_value_root_nonzero combination_len assigned_root
      Hroot Hlen).
  Qed.

  Lemma indicator_expression_off {RegionId0 : Set}
      (Γ : Assignment.t Configure.indexed_columns RegionId0)
      (region : RegionId0) (row : Z)
      (query : Expression.t Configure.indexed_columns)
      (combination_len : nat)
      (assigned_root value : Z)
      (Hquery : eval_expression Γ (region, row) query = value)
      (Hvalue :
        value = 0 \/
        (1 <= value <= Z.of_nat combination_len /\ value <> assigned_root)) :
    eval_expression Γ (region, row)
      (Compress.indicator_expression query combination_len assigned_root)
      = 0.
  Proof.
    rewrite indicator_expression_eval, Hquery.
    exact (indicator_value_off_zero combination_len assigned_root value
      Hvalue).
  Qed.

  (** ** The fixed-plane evaluator

      Evaluation of a fixed-only expression against a partial view of the
      fixed planes: defined on expressions whose leaves are constants and
      fixed queries the view covers, and agreeing with [eval_expression]
      on the grid wherever it is defined.  The compiled assignment
      expressions are of this shape (a combination-column query, or its
      indicator polynomial), so their per-row behavior is decidable from
      the compiled output alone. *)

  Fixpoint eval_fixed_expression
      (view : Z -> Z -> option Z)
      (row : Z)
      (expression : Expression.t Configure.indexed_columns)
      : option Z :=
    match expression with
    | Expression.Constant value => Some (UnOp.from value)
    | Expression.Selector _ => None
    | Expression.Fixed column rotation =>
        match view column (rotated_row row rotation) with
        | Some value => Some (UnOp.from value)
        | None => None
        end
    | Expression.Advice _ _ => None
    | Expression.Instance_ _ _ => None
    | Expression.Negated expression =>
        match eval_fixed_expression view row expression with
        | Some value => Some (UnOp.opp value)
        | None => None
        end
    | Expression.Sum lhs rhs =>
        match
          eval_fixed_expression view row lhs,
          eval_fixed_expression view row rhs
        with
        | Some lhs, Some rhs => Some (BinOp.add lhs rhs)
        | _, _ => None
        end
    | Expression.Product lhs rhs =>
        match
          eval_fixed_expression view row lhs,
          eval_fixed_expression view row rhs
        with
        | Some lhs, Some rhs => Some (BinOp.mul lhs rhs)
        | _, _ => None
        end
    | Expression.Scaled expression scale =>
        match eval_fixed_expression view row expression with
        | Some value => Some (BinOp.mul value (UnOp.from scale))
        | None => None
        end
    end.

  Lemma eval_fixed_expression_sound
      (grid : RawGrid.t)
      (view : Z -> Z -> option Z)
      (Hview : forall column row value,
        view column row = Some value ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
      (row : Z)
      (expression : Expression.t Configure.indexed_columns) :
    forall value : Z,
      eval_fixed_expression view row expression = Some value ->
      eval_expression (grid_assignment grid) (tt, row) expression = value.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      intros value Hvalue; cbn in Hvalue.
    - (* Constant *)
      injection Hvalue as <-.
      reflexivity.
    - (* Selector *) discriminate.
    - (* Fixed *)
      destruct (view fixed (rotated_row row rotation)) as [pinned |]
        eqn:Hpinned; [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression grid_assignment Assignment.fixed].
      rewrite (Hview _ _ _ Hpinned).
      reflexivity.
    - (* Advice *) discriminate.
    - (* Instance_ *) discriminate.
    - (* Negated *)
      destruct (eval_fixed_expression view row expression) as [inner |]
        eqn:Hinner; [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH inner eq_refl).
      reflexivity.
    - (* Sum *)
      destruct (eval_fixed_expression view row lhs) as [value_l |] eqn:Hl;
        [| discriminate].
      destruct (eval_fixed_expression view row rhs) as [value_r |] eqn:Hr;
        [| discriminate].
      injection Hvalue as <-.
      rewrite eval_expression_sum.
      rewrite (IHl value_l eq_refl), (IHr value_r eq_refl).
      reflexivity.
    - (* Product *)
      destruct (eval_fixed_expression view row lhs) as [value_l |] eqn:Hl;
        [| discriminate].
      destruct (eval_fixed_expression view row rhs) as [value_r |] eqn:Hr;
        [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IHl value_l eq_refl), (IHr value_r eq_refl).
      reflexivity.
    - (* Scaled *)
      destruct (eval_fixed_expression view row expression) as [inner |]
        eqn:Hinner; [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH inner eq_refl).
      reflexivity.
  Qed.

  (** ** The per-assignment side condition

      One decidable check over the compiled output: at every domain row,
      each assignment's expression evaluates through the combination view
      to a nonzero value exactly on its selector's enabled rows and to [0]
      elsewhere.  This is the computable form of the indicator lemmas
      above — it subsumes the distinctness of the assigned combination
      values (a shared or colliding value would make some disabled row
      evaluate nonzero) — and it is what the concrete Orchard instance
      discharges by [vm_compute]. *)

  Definition selector_assignment_ok_b
      (view : Z -> Z -> option Z)
      (activations : list bool)
      (n_rows : nat)
      (assignment : SelectorAssignment.t)
      : bool :=
    List.forallb
      (fun row =>
        match
          eval_fixed_expression view (Z.of_nat row)
            assignment.(SelectorAssignment.expression)
        with
        | Some value =>
            if List.nth row activations false
            then negb (value =? 0)
            else value =? 0
        | None => false
        end)
      (List.seq 0 n_rows).

  Definition selector_assignments_ok_b
      (view : Z -> Z -> option Z)
      (activations : Z -> list bool)
      (n_rows : nat)
      (assignments : list SelectorAssignment.t)
      : bool :=
    List.forallb
      (fun assignment =>
        selector_assignment_ok_b view
          (activations assignment.(SelectorAssignment.selector))
          n_rows
          assignment)
      assignments.

  (** The check delivers, at every covered row of a grid whose selector
      planes follow the activations and whose fixed planes agree with the
      view, exactly the per-selector facts the substitution lemma
      consumes. *)
  Lemma selector_assignments_ok_sound
      (grid : RawGrid.t)
      (view : Z -> Z -> option Z)
      (activations : Z -> list bool)
      (n_rows : nat)
      (assignments : list SelectorAssignment.t)
      (Hview : forall column row value,
        view column row = Some value ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
      (Hcheck :
        selector_assignments_ok_b view activations n_rows assignments = true)
      (row : Z)
      (Hrow : 0 <= row < Z.of_nat n_rows)
      (Hact : forall s : Z,
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row) (activations s) false then 1 else 0)) :
    forall (s : Z) (e : Expression.t Configure.indexed_columns),
      Compile.assignment_replacement assignments s = Some e ->
      (eval_selector (grid_assignment grid) (tt, row) s = 0 /\
        eval_expression (grid_assignment grid) (tt, row) e = 0) \/
      (eval_selector (grid_assignment grid) (tt, row) s = 1 /\
        eval_expression (grid_assignment grid) (tt, row) e <> 0).
  Proof.
    intros s e Hrepl.
    unfold Compile.assignment_replacement in Hrepl.
    destruct (List.find _ assignments) as [assignment |] eqn:Hfind;
      [| discriminate].
    injection Hrepl as <-.
    apply List.find_some in Hfind.
    destruct Hfind as [Hin Heqb].
    apply Z.eqb_eq in Heqb.
    subst s.
    unfold selector_assignments_ok_b in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    specialize (Hcheck _ Hin).
    unfold selector_assignment_ok_b in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    specialize (Hcheck (Z.to_nat row)).
    rewrite Z2Nat.id in Hcheck by lia.
    assert (Hseq : List.In (Z.to_nat row) (List.seq 0 n_rows)).
    { apply List.in_seq. lia. }
    specialize (Hcheck Hseq).
    destruct
      (eval_fixed_expression view row
        assignment.(SelectorAssignment.expression))
      as [value |] eqn:Heval; [| discriminate].
    pose proof
      (eval_fixed_expression_sound grid view Hview row
        assignment.(SelectorAssignment.expression) value Heval)
      as Hexpression.
    assert (Hselector :
      eval_selector (grid_assignment grid) (tt, row)
        assignment.(SelectorAssignment.selector) =
      UnOp.from
        (if
          List.nth (Z.to_nat row)
            (activations assignment.(SelectorAssignment.selector)) false
         then 1 else 0)).
    { unfold eval_selector.
      cbn [grid_assignment Assignment.selector].
      rewrite (Hact assignment.(SelectorAssignment.selector)).
      reflexivity. }
    destruct
      (List.nth (Z.to_nat row)
        (activations assignment.(SelectorAssignment.selector)) false)
      eqn:Hbit.
    - right.
      apply Bool.negb_true_iff, Z.eqb_neq in Hcheck.
      split.
      + rewrite Hselector.
        apply FieldRewrite.from_one.
      + rewrite Hexpression.
        exact Hcheck.
    - left.
      apply Z.eqb_eq in Hcheck.
      split.
      + rewrite Hselector.
        apply FieldRewrite.from_zero.
      + rewrite Hexpression.
        exact Hcheck.
  Qed.

  (** ** Gate satisfaction of a flattened system

      For a system whose constraints are all [EqualZeroToPrecise], gate
      satisfaction at an index is the vanishing of every flattened gate
      polynomial. *)

  Lemma flattened_gates_iff {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (index : RegionId0 * Z)
      (system : ConstraintSystem.t columns0)
      (Hflat : system_flattened_b system = true) :
    eval_gates Γ index system.(ConstraintSystem.gates) <->
    (forall poly : Expression.t columns0,
      List.In poly (gate_polys system) ->
      eval_expression Γ index poly = 0).
  Proof.
    unfold system_flattened_b in Hflat.
    rewrite List.forallb_forall in Hflat.
    rewrite eval_gates_forall.
    split.
    - intros Hgates poly Hpoly.
      unfold gate_polys in Hpoly.
      apply List.in_flat_map in Hpoly.
      destruct Hpoly as (gate & Hgate & Hpoly).
      apply List.in_map_iff in Hpoly.
      destruct Hpoly as (named_constraint & Hpoly & Hconstraint).
      specialize (Hgates gate Hgate).
      unfold eval_gate in Hgates.
      rewrite eval_constraints_forall in Hgates.
      specialize (Hgates _ Hconstraint).
      specialize (Hflat gate Hgate).
      rewrite List.forallb_forall in Hflat.
      specialize (Hflat _ Hconstraint).
      destruct named_constraint as [name constraint].
      destruct constraint as
        [ selector inner | lhs rhs | inner | inner range | lhs rhs
        | lhs rhs | inner ];
        cbn in Hflat; try discriminate.
      cbn in Hpoly, Hgates.
      subst poly.
      exact Hgates.
    - intros Hpolys gate Hgate.
      unfold eval_gate.
      rewrite eval_constraints_forall.
      intros named_constraint Hconstraint.
      specialize (Hflat gate Hgate).
      rewrite List.forallb_forall in Hflat.
      specialize (Hflat _ Hconstraint).
      destruct named_constraint as [name constraint].
      destruct constraint as
        [ selector inner | lhs rhs | inner | inner range | lhs rhs
        | lhs rhs | inner ];
        cbn in Hflat; try discriminate.
      cbn.
      apply Hpolys.
      unfold gate_polys.
      apply List.in_flat_map.
      exists gate.
      split; [exact Hgate |].
      exact
        (List.in_map
          (fun named_constraint =>
            Configure.constraint_to_expression (snd named_constraint))
          _ _ Hconstraint).
  Qed.

  (** ** Vacuity at all-zero selectors

      The polynomial reading of [PlonkishMock.gates_selector_vacuous_b]:
      at an index where every selector evaluates to [0], every flattened
      gate polynomial evaluates to [0]. *)

  Lemma gate_polys_vacuous_eval {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (system : ConstraintSystem.t columns0)
      (Hvacuous :
        PlonkishMock.gates_selector_vacuous_b (p := p) system = true)
      (Hselectors :
        forall selector, eval_selector Γ (region, row) selector = 0) :
    forall poly : Expression.t columns0,
      List.In poly (gate_polys system) ->
      eval_expression Γ (region, row) poly = 0.
  Proof.
    intros poly Hpoly.
    unfold gate_polys in Hpoly.
    apply List.in_flat_map in Hpoly.
    destruct Hpoly as (gate & Hgate & Hpoly).
    apply List.in_map_iff in Hpoly.
    destruct Hpoly as (named_constraint & Hpoly & Hconstraint).
    unfold PlonkishMock.gates_selector_vacuous_b in Hvacuous.
    rewrite List.forallb_forall in Hvacuous.
    specialize (Hvacuous _ Hgate).
    unfold PlonkishMock.gate_selector_vacuous_b in Hvacuous.
    rewrite List.forallb_forall in Hvacuous.
    specialize (Hvacuous _ Hconstraint).
    destruct named_constraint as [name constraint].
    unfold PlonkishMock.constraint_selector_vacuous_b in Hvacuous.
    cbn [snd] in Hvacuous, Hpoly.
    destruct constraint as
      [ selector inner | lhs rhs | inner | inner range | lhs rhs
      | lhs rhs | inner ];
      try discriminate.
    - (* Select *)
      destruct inner;
        cbn [Configure.constraint_to_expression] in Hpoly;
        subst poly;
        cbn [eval_expression];
        rewrite (Hselectors selector);
        autorewrite with field_rewrite;
        reflexivity.
    - (* EqualZeroToPrecise *)
      destruct (Complete.zero_selector_value (p := p) inner)
        as [value |] eqn:Hvalue; [| discriminate].
      apply Z.eqb_eq in Hvacuous.
      subst value.
      cbn [Configure.constraint_to_expression] in Hpoly.
      subst poly.
      exact
        (PlonkishMock.zero_selector_value_eval Γ region row Hselectors
          inner 0 Hvalue).
  Qed.

  (** Every selector reads [0] at the rows past the usable prefix: the
      activations stop below [usable_rows] and the selector planes follow
      the activations. *)
  Lemma blinding_selectors_zero
      (domain : Domain.t)
      (infos : list Compile.SelectorInfo.t)
      (grid : RawGrid.t)
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row) (info_activations infos s) false
         then 1 else 0))
      (Hwithin :
        activations_within_b (Domain.usable_rows domain) infos = true)
      (row : Z)
      (Hrow : 0 <= row < Domain.n domain)
      (Hblind : Domain.usable_rows domain <= row) :
    forall selector : Z,
      eval_selector (grid_assignment grid) (tt, row) selector = 0.
  Proof.
    intros selector.
    unfold eval_selector.
    cbn [grid_assignment Assignment.selector].
    rewrite (Hact selector row Hrow).
    rewrite
      (activations_within_off _ _ Hwithin selector row (proj1 Hrow) Hblind).
    apply FieldRewrite.from_zero.
  Qed.

  (** ** Blinding-row vacuity of the compiled gates

      Outside the usable rows every compiled gate polynomial evaluates to
      [0]: the selector-derived factor substituted into each gate — the
      combination-column indicator — reads the all-zero tail of its
      combination column there, and the residual polynomial is the
      selector-vacuous original. *)

  Lemma compiled_gates_blinding_vacuous
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (grid : RawGrid.t)
      (compiled : CompiledSystem.t)
      (Hcompiled_gates :
        compiled.(CompiledSystem.gates) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.gates))
      (Hcompiled_selectors :
        compiled.(CompiledSystem.selector_assignments) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.selector_assignments))
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row) (info_activations infos s) false
         then 1 else 0))
      (Hwithin :
        activations_within_b (Domain.usable_rows domain) infos = true)
      (Hview : forall column row value,
        combination_view compiled column row = Some value ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
      (Hvacuous :
        PlonkishMock.gates_selector_vacuous_b (p := p) system = true)
      (Hmult :
        gates_substitution_ok_b
          compiled.(CompiledSystem.selector_assignments) system = true)
      (Hcheck :
        selector_assignments_ok_b (combination_view compiled)
          (info_activations infos) (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments) = true)
      (row : Z)
      (Hrow : 0 <= row < Domain.n domain)
      (Hblind : Domain.usable_rows domain <= row) :
    forall poly : Expression.t Configure.indexed_columns,
      List.In poly compiled.(CompiledSystem.gates) ->
      eval_expression (grid_assignment grid) (tt, row) poly = 0.
  Proof.
    intros poly Hpoly.
    pose proof
      (compile_gates_substituted system infos num_fixed_columns
        permutation_columns constants) as Hgates.
    rewrite <- Hcompiled_gates in Hgates.
    rewrite <- Hcompiled_selectors in Hgates.
    rewrite Hgates in Hpoly.
    apply List.in_map_iff in Hpoly.
    destruct Hpoly as (source & Hpoly & Hsource).
    subst poly.
    apply substitute_selectors_zero_iff.
    - apply
        (selector_assignments_ok_sound grid (combination_view compiled)
          (info_activations infos) (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments) Hview Hcheck row).
      + rewrite Z2Nat.id by lia.
        exact Hrow.
      + intros s.
        exact (Hact s row Hrow).
    - unfold gates_substitution_ok_b in Hmult.
      rewrite List.forallb_forall in Hmult.
      exact (Hmult _ Hsource).
    - exact
        (gate_polys_vacuous_eval (grid_assignment grid) tt row system
          Hvacuous
          (blinding_selectors_zero domain infos grid Hact Hwithin row Hrow
            Hblind)
          source Hsource).
  Qed.

  (** ** Compilation correctness

      Vanishing of every compiled gate polynomial on the full cyclic
      domain is equivalent to satisfaction of the original selector-gated
      gates on the usable-row prefix.  The hypotheses are the selector-off
      shape of the grid ([Hact]: the selector planes are boolean and [0]
      off the program-enabled points), the loaded combination planes
      ([Hview]), and the decidable well-formedness facts of the concrete
      system and packing output — nothing depends on which combination
      column any selector landed in. *)

  Definition compiled_gates_hold
      (domain : Domain.t)
      (compiled : CompiledSystem.t)
      (grid : RawGrid.t)
      : Prop :=
    forall row : Z,
      0 <= row < Domain.n domain ->
      forall poly : Expression.t Configure.indexed_columns,
        List.In poly compiled.(CompiledSystem.gates) ->
        eval_expression (grid_assignment grid) (tt, row) poly = 0.

  Theorem compile_correct
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (grid : RawGrid.t)
      (compiled : CompiledSystem.t)
      (Hcompiled_gates :
        compiled.(CompiledSystem.gates) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.gates))
      (Hcompiled_selectors :
        compiled.(CompiledSystem.selector_assignments) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.selector_assignments))
      (Hblinding : 0 <= domain.(Domain.blinding_factors))
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row) (info_activations infos s) false
         then 1 else 0))
      (Hwithin :
        activations_within_b (Domain.usable_rows domain) infos = true)
      (Hview : forall column row value,
        combination_view compiled column row = Some value ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
      (Hflat : system_flattened_b system = true)
      (Hvacuous :
        PlonkishMock.gates_selector_vacuous_b (p := p) system = true)
      (Hmult :
        gates_substitution_ok_b
          compiled.(CompiledSystem.selector_assignments) system = true)
      (Hcheck :
        selector_assignments_ok_b (combination_view compiled)
          (info_activations infos) (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments) = true) :
    compiled_gates_hold domain compiled grid <->
    (forall row : Z,
      0 <= row < Domain.usable_rows domain ->
      eval_gates (grid_assignment grid) (tt, row)
        system.(ConstraintSystem.gates)).
  Proof.
    pose proof
      (compile_gates_substituted system infos num_fixed_columns
        permutation_columns constants) as Hgates.
    rewrite <- Hcompiled_gates, <- Hcompiled_selectors in Hgates.
    assert (Hval_row : forall row : Z,
      0 <= row < Domain.n domain ->
      forall (s : Z) (e : Expression.t Configure.indexed_columns),
        Compile.assignment_replacement
          compiled.(CompiledSystem.selector_assignments) s = Some e ->
        (eval_selector (grid_assignment grid) (tt, row) s = 0 /\
          eval_expression (grid_assignment grid) (tt, row) e = 0) \/
        (eval_selector (grid_assignment grid) (tt, row) s = 1 /\
          eval_expression (grid_assignment grid) (tt, row) e <> 0)).
    { intros row Hrow.
      apply
        (selector_assignments_ok_sound grid (combination_view compiled)
          (info_activations infos) (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments) Hview Hcheck row).
      - rewrite Z2Nat.id by lia.
        exact Hrow.
      - intros s.
        exact (Hact s row Hrow). }
    assert (Hiff : forall row : Z,
      0 <= row < Domain.n domain ->
      forall poly : Expression.t Configure.indexed_columns,
        List.In poly (gate_polys system) ->
        (eval_expression (grid_assignment grid) (tt, row)
          (substitute_selectors
            (Compile.assignment_replacement
              compiled.(CompiledSystem.selector_assignments))
            poly) = 0 <->
        eval_expression (grid_assignment grid) (tt, row) poly = 0)).
    { intros row Hrow poly Hpoly.
      apply substitute_selectors_zero_iff; [exact (Hval_row row Hrow) |].
      unfold gates_substitution_ok_b in Hmult.
      rewrite List.forallb_forall in Hmult.
      exact (Hmult _ Hpoly). }
    split.
    - (* Compiled satisfaction implies gated satisfaction. *)
      intros Hcompiled_holds row Hrow.
      assert (Hrow_domain : 0 <= row < Domain.n domain).
      { unfold Domain.usable_rows in Hrow.
        lia. }
      apply (flattened_gates_iff (grid_assignment grid) (tt, row) system
        Hflat).
      intros poly Hpoly.
      apply (proj1 (Hiff row Hrow_domain poly Hpoly)).
      apply (Hcompiled_holds row Hrow_domain).
      rewrite Hgates.
      exact (List.in_map _ _ _ Hpoly).
    - (* Gated satisfaction implies compiled satisfaction. *)
      intros Horiginal row Hrow poly Hpoly.
      destruct (Z.ltb row (Domain.usable_rows domain)) eqn:Hcase.
      + apply Z.ltb_lt in Hcase.
        rewrite Hgates in Hpoly.
        apply List.in_map_iff in Hpoly.
        destruct Hpoly as (source & Hpoly & Hsource).
        subst poly.
        apply (proj2 (Hiff row Hrow source Hsource)).
        exact
          (proj1
            (flattened_gates_iff (grid_assignment grid) (tt, row) system
              Hflat)
            (Horiginal row (conj (proj1 Hrow) Hcase))
            source Hsource).
      + apply Z.ltb_ge in Hcase.
        exact
          (compiled_gates_blinding_vacuous domain system infos
            num_fixed_columns permutation_columns constants grid compiled
            Hcompiled_gates Hcompiled_selectors Hact Hwithin Hview Hvacuous
            Hmult Hcheck row Hrow Hcase poly Hpoly).
  Qed.

  (** The full-domain reading of the original side — the gate conjunct of
      [PlonkishMock.plonkish_accepts], where the compiled equivalence
      composes with [plonkish_of_mock_prover]: off the usable rows the
      selector-gated gates hold vacuously. *)

  Corollary compile_correct_domain
      (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (grid : RawGrid.t)
      (compiled : CompiledSystem.t)
      (Hcompiled_gates :
        compiled.(CompiledSystem.gates) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.gates))
      (Hcompiled_selectors :
        compiled.(CompiledSystem.selector_assignments) =
        (Compile.compile system infos num_fixed_columns permutation_columns
          constants).(CompiledSystem.selector_assignments))
      (Hblinding : 0 <= domain.(Domain.blinding_factors))
      (Hact : forall s row : Z,
        0 <= row < Domain.n domain ->
        grid.(RawGrid.sel) s row =
        (if List.nth (Z.to_nat row) (info_activations infos s) false
         then 1 else 0))
      (Hwithin :
        activations_within_b (Domain.usable_rows domain) infos = true)
      (Hview : forall column row value,
        combination_view compiled column row = Some value ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value)
      (Hflat : system_flattened_b system = true)
      (Hvacuous :
        PlonkishMock.gates_selector_vacuous_b (p := p) system = true)
      (Hmult :
        gates_substitution_ok_b
          compiled.(CompiledSystem.selector_assignments) system = true)
      (Hcheck :
        selector_assignments_ok_b (combination_view compiled)
          (info_activations infos) (Z.to_nat (Domain.n domain))
          compiled.(CompiledSystem.selector_assignments) = true) :
    compiled_gates_hold domain compiled grid <->
    (forall row : Z,
      0 <= row < Domain.n domain ->
      eval_gates (grid_assignment grid) (tt, row)
        system.(ConstraintSystem.gates)).
  Proof.
    pose proof
      (compile_correct domain system infos num_fixed_columns
        permutation_columns constants grid compiled Hcompiled_gates
        Hcompiled_selectors Hblinding Hact Hwithin Hview Hflat Hvacuous
        Hmult Hcheck) as Hmain.
    split.
    - intros Hcompiled_holds row Hrow.
      destruct (Z.ltb row (Domain.usable_rows domain)) eqn:Hcase.
      + apply Z.ltb_lt in Hcase.
        exact
          (proj1 Hmain Hcompiled_holds row (conj (proj1 Hrow) Hcase)).
      + apply Z.ltb_ge in Hcase.
        exact
          (PlonkishMock.gates_selector_vacuous_sound (grid_assignment grid)
            tt row system Hvacuous
            (blinding_selectors_zero domain infos grid Hact Hwithin row
              Hrow Hcase)).
    - intros Horiginal.
      apply (proj2 Hmain).
      intros row Hrow.
      apply Horiginal.
      unfold Domain.usable_rows in Hrow.
      lia.
  Qed.

End WithPrime.

End PlonkishCompile.
