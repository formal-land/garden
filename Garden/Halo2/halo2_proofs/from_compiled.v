(** * Compiled plonkish system → transcribed verifier constraint system

    Data glue between the L2 compiled system ([Halo2/plonkish/main.v]
    [CompiledSystem.t]: column-and-rotation expressions after selector
    compression) and the query-indexed verifying-key surface the
    transcribed [verify_proof] consumes ([Halo2/halo2_proofs/plonk.v]).

    [reindex] replaces each [Advice]/[Fixed]/[Instance_] leaf
    [(column, rotation.offset)] by the position of that pair in the
    corresponding query table — the same resolution
    [halo2_proofs/src/plonk.rs] records as [Expression::{Advice,Fixed,Instance}
    { query_index, column_index, rotation }]. [constraint_system_of]
    rebuilds the verifier [ConstraintSystem] from those tables, the
    reindexed gate polynomials (one singleton list per compiled poly, the
    flattening [gate_expressions] in [plonk/verifier.rs] performs), and the
    lookup pairs with table columns mapped to current-rotation fixed
    queries.
    [vk_of_orchard] fills the CS fields that way and takes the cryptographic
    VK pieces (domain, fixed and permutation commitments, transcript
    binding scalar) as parameters.

    [reindex_preserves_eval] is the semantic content of the reindex: on a
    selector-free expression whose leaves sit in the query tables, the
    verifier's [Expression.evaluate] against the three eval lists obtained
    by reading each query at [row + offset] equals the compiled
    row-evaluator [eval_at_row]. [eval_at_row] is the same function as
    [eval_expression] ([Halo2/proof.v]) at [p = PastaPrimes.pallas_p]
    ([UnOp.from] = [Fp.from], [BinOp.add] = [Fp.add], [BinOp.mul] =
    [Fp.mul], [UnOp.opp] = [Fp.opp]), reading
    [assignment.fixed col _ (row + offset)] as [read_fixed col (row + offset)]
    (and likewise for advice; instance ignores the region). The
    [Sum (Negated _)] special case in [eval_expression] agrees with
    [x +s Fp.opp y] in the field. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.

Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Garden.Halo2.halo2_proofs.plonk.

Import List.ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module V := Garden.Halo2.halo2_proofs.plonk.

Module FromCompiled.

(** ** Query-table index

    First-match position of [(column, rotation offset)] in a query table,
    matching [index_of_go] in [Orchard/vk/print.v]. Missing queries return
    the table length (past-the-end); [Vec.nth] then yields the default
    [0]. *)

Fixpoint query_index_go (queries : list (Z * Z)) (q : Z * Z) (i : nat) : nat :=
  match queries with
  | [] => i
  | x :: rest =>
      if Queries.query_eqb x q then i
      else query_index_go rest q (S i)
  end.

Definition query_index (queries : list (Z * Z)) (col rot : Z) : nat :=
  query_index_go queries (col, rot) 0.

Definition query_in (queries : list (Z * Z)) (col rot : Z) : bool :=
  List.existsb (fun x => Queries.query_eqb x (col, rot)) queries.

(** ** Reindex: column-and-rotation leaves → query indices *)

Fixpoint reindex
    (advice_qs fixed_qs instance_qs : list (Z * Z))
    (e : Expression.t Configure.indexed_columns) : V.Expression.t :=
  match e with
  | Expression.Constant value => V.Expression.Constant value
  | Expression.Selector _ =>
      (* Compiled gates are selector-free ([CompiledSystem.selector_free_b]).
         The dummy keeps [reindex] total. *)
      V.Expression.Constant 0
  | Expression.Fixed column rotation =>
      V.Expression.Fixed
        (usize_of (Z.of_nat (query_index fixed_qs column rotation.(Rotation.offset))))
  | Expression.Advice column rotation =>
      V.Expression.Advice
        (usize_of (Z.of_nat (query_index advice_qs column rotation.(Rotation.offset))))
  | Expression.Instance_ column rotation =>
      V.Expression.Instance
        (usize_of (Z.of_nat (query_index instance_qs column rotation.(Rotation.offset))))
  | Expression.Negated e => V.Expression.Negated (reindex advice_qs fixed_qs instance_qs e)
  | Expression.Sum a b =>
      V.Expression.Sum
        (reindex advice_qs fixed_qs instance_qs a)
        (reindex advice_qs fixed_qs instance_qs b)
  | Expression.Product a b =>
      V.Expression.Product
        (reindex advice_qs fixed_qs instance_qs a)
        (reindex advice_qs fixed_qs instance_qs b)
  | Expression.Scaled e scale =>
      V.Expression.Scaled (reindex advice_qs fixed_qs instance_qs e) scale
  end.

Definition reindex_compiled
    (compiled : CompiledSystem.t)
    (e : Expression.t Configure.indexed_columns) : V.Expression.t :=
  reindex
    compiled.(CompiledSystem.advice_queries)
    compiled.(CompiledSystem.fixed_queries)
    compiled.(CompiledSystem.instance_queries)
    e.

(** Every [Advice]/[Fixed]/[Instance_] leaf of [e] occurs in the matching
    query table. *)
Fixpoint queries_registered
    (advice_qs fixed_qs instance_qs : list (Z * Z))
    (e : Expression.t Configure.indexed_columns) : bool :=
  match e with
  | Expression.Constant _ => true
  | Expression.Selector _ => true
  | Expression.Fixed column rotation =>
      query_in fixed_qs column rotation.(Rotation.offset)
  | Expression.Advice column rotation =>
      query_in advice_qs column rotation.(Rotation.offset)
  | Expression.Instance_ column rotation =>
      query_in instance_qs column rotation.(Rotation.offset)
  | Expression.Negated e => queries_registered advice_qs fixed_qs instance_qs e
  | Expression.Sum a b =>
      andb
        (queries_registered advice_qs fixed_qs instance_qs a)
        (queries_registered advice_qs fixed_qs instance_qs b)
  | Expression.Product a b =>
      andb
        (queries_registered advice_qs fixed_qs instance_qs a)
        (queries_registered advice_qs fixed_qs instance_qs b)
  | Expression.Scaled e _ => queries_registered advice_qs fixed_qs instance_qs e
  end.

(** ** Row evaluators

    [cell_evals read row qs] is the eval list the verifier would hold if
    each query [(col, rot)] opened to the cell [read col (row + rot)]
    reduced into [F_{pallas_p}]. [eval_at_row] is the compiled expression
    evaluated against the same readers. *)

Definition cell_evals
    (read : Z -> Z -> Z)
    (row : Z)
    (qs : list (Z * Z)) : list Z :=
  List.map (fun q => Fp.from (read (fst q) (row + snd q))) qs.

Fixpoint eval_at_row
    (read_fixed read_advice read_instance : Z -> Z -> Z)
    (row : Z)
    (e : Expression.t Configure.indexed_columns) : Z :=
  match e with
  | Expression.Constant value => Fp.from value
  | Expression.Selector _ => Fp.from 0
  | Expression.Fixed column rotation =>
      Fp.from (read_fixed column (row + rotation.(Rotation.offset)))
  | Expression.Advice column rotation =>
      Fp.from (read_advice column (row + rotation.(Rotation.offset)))
  | Expression.Instance_ column rotation =>
      Fp.from (read_instance column (row + rotation.(Rotation.offset)))
  | Expression.Negated e =>
      Fp.opp (eval_at_row read_fixed read_advice read_instance row e)
  | Expression.Sum a b =>
      eval_at_row read_fixed read_advice read_instance row a
        +s eval_at_row read_fixed read_advice read_instance row b
  | Expression.Product a b =>
      eval_at_row read_fixed read_advice read_instance row a
        *s eval_at_row read_fixed read_advice read_instance row b
  | Expression.Scaled e scale =>
      eval_at_row read_fixed read_advice read_instance row e *s Fp.from scale
  end.

(** A [nat] fits in [usize] (unsigned 64-bit wrap). Query tables in every
    Halo 2 circuit, Orchard included, are far smaller. *)
Definition usize_fits (n : nat) : Prop := Z.of_nat n < 2 ^ 64.

(** ** Query-index lemmas *)

Lemma query_eqb_true (a b : Z * Z) :
  Queries.query_eqb a b = true -> a = b.
Proof.
  destruct a as [c1 r1]; destruct b as [c2 r2].
  unfold Queries.query_eqb; cbn.
  intros H.
  apply andb_true_iff in H.
  destruct H as [Hc Hr].
  apply Z.eqb_eq in Hc, Hr.
  subst.
  reflexivity.
Qed.

Lemma query_index_go_spec (qs : list (Z * Z)) (q : Z * Z) (i : nat) :
  List.existsb (fun x => Queries.query_eqb x q) qs = true ->
  exists n : nat,
    query_index_go qs q i = (i + n)%nat /\
    (n < List.length qs)%nat /\
    List.nth n qs q = q.
Proof.
  revert i.
  induction qs as [|x rest IH]; intros i Hin.
  - cbn in Hin. discriminate Hin.
  - cbn [query_index_go List.existsb] in *.
    destruct (Queries.query_eqb x q) eqn:Heq.
    + exists 0%nat.
      repeat split.
      * rewrite Nat.add_0_r. reflexivity.
      * cbn [List.length]. lia.
      * apply query_eqb_true in Heq. rewrite Heq. reflexivity.
    + cbn [orb] in Hin.
      destruct (IH (S i) Hin) as [n [Hgo [Hlt Hnth]]].
      exists (S n).
      repeat split.
      * rewrite Hgo. lia.
      * cbn [List.length]. lia.
      * exact Hnth.
Qed.

Lemma usize_to_nat_of_nat (n : nat) :
  usize_fits n ->
  Integer.to_nat (usize_of (Z.of_nat n)) = n.
Proof.
  intros Hn.
  unfold usize_of, Integer.make, Integer.to_nat, IntegerKind.normalize_wrap,
    IntegerKind.modulus, IntegerKind.bit_size, IntegerKind.is_signed, usize_fits in *.
  cbn.
  rewrite Z.mod_small.
  - rewrite Nat2Z.id. reflexivity.
  - split.
    + apply Nat2Z.is_nonneg.
    + exact Hn.
Qed.

Lemma usize_fits_lt (n m : nat) :
  (n < m)%nat ->
  usize_fits m ->
  usize_fits n.
Proof.
  intros Hlt Hm.
  unfold usize_fits in *.
  apply Z.lt_trans with (m := Z.of_nat m); [| exact Hm].
  apply Nat2Z.inj_lt.
  exact Hlt.
Qed.

Lemma map_nth_in {A B : Type}
    (f : A -> B) (l : list A) (n : nat) (dA : A) (dB : B) :
  (n < List.length l)%nat ->
  List.nth n (List.map f l) dB = f (List.nth n l dA).
Proof.
  intros Hlt.
  rewrite (List.nth_indep (List.map f l) dB (f dA)).
  - apply List.map_nth.
  - rewrite List.length_map. exact Hlt.
Qed.

Lemma cell_evals_nth
    (read : Z -> Z -> Z)
    (row : Z)
    (qs : list (Z * Z))
    (col rot : Z) :
  query_in qs col rot = true ->
  usize_fits (List.length qs) ->
  Vec.nth (A := Z) (cell_evals read row qs)
    (usize_of (Z.of_nat (query_index qs col rot)))
  = Fp.from (read col (row + rot)).
Proof.
  intros Hin Hfit.
  unfold query_in in Hin.
  destruct (query_index_go_spec qs (col, rot) 0 Hin)
    as [n [Heq [Hlt Hnth]]].
  rewrite Nat.add_0_l in Heq.
  unfold query_index, Vec.nth, cell_evals.
  rewrite Heq.
  rewrite usize_to_nat_of_nat
    by (eapply usize_fits_lt; [exact Hlt | exact Hfit]).
  rewrite (map_nth_in
    (fun q => Fp.from (read (fst q) (row + snd q)))
    qs n (col, rot) Default.default Hlt).
  rewrite Hnth.
  cbn [fst snd].
  reflexivity.
Qed.

(** ** Reindex preserves evaluation

    If every leaf of [e] is registered in the query tables (and those
    tables fit in [usize]), the verifier evaluator on the reindexed tree
    against [cell_evals] agrees with [eval_at_row]. Selector leaves are
    excluded: they do not survive compression, and [reindex] maps them to
    the dummy [Constant 0]. *)

Lemma reindex_preserves_eval
    (advice_qs fixed_qs instance_qs : list (Z * Z))
    (read_fixed read_advice read_instance : Z -> Z -> Z)
    (row : Z)
    (e : Expression.t Configure.indexed_columns) :
  expression_selector_free e = true ->
  queries_registered advice_qs fixed_qs instance_qs e = true ->
  usize_fits (List.length advice_qs) ->
  usize_fits (List.length fixed_qs) ->
  usize_fits (List.length instance_qs) ->
  V.Expression.evaluate
    (reindex advice_qs fixed_qs instance_qs e)
    (cell_evals read_fixed row fixed_qs)
    (cell_evals read_advice row advice_qs)
    (cell_evals read_instance row instance_qs)
  = eval_at_row read_fixed read_advice read_instance row e.
Proof.
  intros Hfree Hreg Haf Hff Hif.
  induction e as
    [ value
    | selector
    | column rotation
    | column rotation
    | column rotation
    | e IH
    | a IHa b IHb
    | a IHa b IHb
    | e IH scale ];
    cbn [reindex eval_at_row V.Expression.evaluate
         expression_selector_free queries_registered] in *.
  - reflexivity.
  - discriminate Hfree.
  - apply cell_evals_nth; assumption.
  - apply cell_evals_nth; assumption.
  - apply cell_evals_nth; assumption.
  - rewrite IH; [reflexivity | exact Hfree | exact Hreg].
  - apply andb_true_iff in Hfree; destruct Hfree as [Hfreea Hfreeb].
    apply andb_true_iff in Hreg; destruct Hreg as [Hrega Hregb].
    rewrite IHa, IHb; [reflexivity | | | | ]; assumption.
  - apply andb_true_iff in Hfree; destruct Hfree as [Hfreea Hfreeb].
    apply andb_true_iff in Hreg; destruct Hreg as [Hrega Hregb].
    rewrite IHa, IHb; [reflexivity | | | | ]; assumption.
  - rewrite IH; [reflexivity | exact Hfree | exact Hreg].
Qed.

Lemma reindex_compiled_preserves_eval
    (compiled : CompiledSystem.t)
    (read_fixed read_advice read_instance : Z -> Z -> Z)
    (row : Z)
    (e : Expression.t Configure.indexed_columns) :
  expression_selector_free e = true ->
  queries_registered
    compiled.(CompiledSystem.advice_queries)
    compiled.(CompiledSystem.fixed_queries)
    compiled.(CompiledSystem.instance_queries)
    e = true ->
  usize_fits (List.length compiled.(CompiledSystem.advice_queries)) ->
  usize_fits (List.length compiled.(CompiledSystem.fixed_queries)) ->
  usize_fits (List.length compiled.(CompiledSystem.instance_queries)) ->
  V.Expression.evaluate
    (reindex_compiled compiled e)
    (cell_evals read_fixed row compiled.(CompiledSystem.fixed_queries))
    (cell_evals read_advice row compiled.(CompiledSystem.advice_queries))
    (cell_evals read_instance row compiled.(CompiledSystem.instance_queries))
  = eval_at_row read_fixed read_advice read_instance row e.
Proof.
  intros.
  unfold reindex_compiled.
  apply reindex_preserves_eval; assumption.
Qed.

(** ** Constraint system and verifying key *)

Definition column_of_query (ty : V.ColumnType.t) (q : Z * Z)
    : V.Column.t * V.Rotation.t :=
  ({| V.Column.column_type := ty; V.Column.index := usize_of (fst q) |},
   snd q).

Definition of_query_table (ty : V.ColumnType.t) (qs : list (Z * Z))
    : list (V.Column.t * V.Rotation.t) :=
  List.map (column_of_query ty) qs.

Definition column_of_ref (c : Raw.ColumnRef.t) : V.Column.t :=
  {|
    V.Column.column_type :=
      match c.(Raw.ColumnRef.kind) with
      | Raw.ColumnKind.Advice => V.ColumnType.Advice
      | Raw.ColumnKind.Fixed => V.ColumnType.Fixed
      | Raw.ColumnKind.Instance_ => V.ColumnType.Instance
      end;
    V.Column.index := usize_of c.(Raw.ColumnRef.index);
  |}.

(** Identity lookup-index → fixed-column map. For Orchard this is the
    correspondence certified by [OrchardConfigure.lookup_fixed_columns_eq]
    ([compiled/configuration.v]): table columns [0; 1; 2] occupy fixed
    columns [0; 1; 2]. *)
Definition lookup_as_fixed_id (lookup_index : Z) : Z := lookup_index.

Definition of_lookup
    (compiled : CompiledSystem.t)
    (lookup_as_fixed : Z -> Z)
    (arg : LookupArgument.t Configure.indexed_columns)
    : V.LookupArgument.t :=
  {|
    V.LookupArgument.input_expressions :=
      List.map
        (fun pair => reindex_compiled compiled (fst pair))
        arg.(LookupArgument.pairs);
    V.LookupArgument.table_expressions :=
      List.map
        (fun pair =>
          reindex_compiled compiled
            (@Expression.Fixed Configure.indexed_columns
              (lookup_as_fixed (snd pair))
              Rotation.cur))
        arg.(LookupArgument.pairs);
  |}.

(** Degree of a compiled system, the same formula as [system_degree] on
    the compressed gates and lookups (permutation argument 3, each lookup
    [lookup_required_degree], each gate polynomial [expression_degree],
    floor 1). *)
Definition compiled_degree (self : CompiledSystem.t) : nat :=
  let d_perm := 3%nat in
  let d_lookup :=
    List.fold_left
      (fun acc lookup => Nat.max acc (lookup_required_degree lookup))
      self.(CompiledSystem.lookups)
      1%nat in
  let d_gates :=
    List.fold_left
      (fun acc poly => Nat.max acc (expression_degree poly))
      self.(CompiledSystem.gates)
      O in
  Nat.max (Nat.max d_perm d_lookup) (Nat.max d_gates 1%nat).

Definition constraint_system_of
    (compiled : CompiledSystem.t)
    (num_advice_columns num_instance_columns : Z)
    (lookup_as_fixed : Z -> Z)
    : V.ConstraintSystem.t :=
  {|
    V.ConstraintSystem.num_instance_columns := usize_of num_instance_columns;
    V.ConstraintSystem.num_advice_columns := usize_of num_advice_columns;
    V.ConstraintSystem.instance_queries :=
      of_query_table V.ColumnType.Instance
        compiled.(CompiledSystem.instance_queries);
    V.ConstraintSystem.advice_queries :=
      of_query_table V.ColumnType.Advice
        compiled.(CompiledSystem.advice_queries);
    V.ConstraintSystem.fixed_queries :=
      of_query_table V.ColumnType.Fixed
        compiled.(CompiledSystem.fixed_queries);
    V.ConstraintSystem.gates :=
      List.map
        (fun g => [reindex_compiled compiled g])
        compiled.(CompiledSystem.gates);
    V.ConstraintSystem.lookups :=
      List.map
        (of_lookup compiled lookup_as_fixed)
        compiled.(CompiledSystem.lookups);
    V.ConstraintSystem.permutation :=
      {|
        V.PermutationArgument.columns :=
          List.map column_of_ref compiled.(CompiledSystem.permutation_columns);
      |};
    V.ConstraintSystem.blinding_factors :=
      usize_of (CompiledSystem.blinding_factors compiled);
    V.ConstraintSystem.degree :=
      usize_of (Z.of_nat (compiled_degree compiled));
  |}.

(** Verifying key whose CS is that of [compiled]. Commitments, the
    evaluation domain, and the Fiat–Shamir binding scalar are parameters:
    they come from the cryptographic keygen / the pinned VK, not from the
    compiled polynomials. *)
Definition vk_of_orchard
    (compiled : CompiledSystem.t)
    (num_advice_columns num_instance_columns : Z)
    (lookup_as_fixed : Z -> Z)
    (domain : EvaluationDomain.t)
    (fixed_commitments : list VestaCurve.point)
    (permutation_commitments : list VestaCurve.point)
    (transcript_repr : Z)
    : V.VerifyingKey.t :=
  let cs :=
    constraint_system_of
      compiled num_advice_columns num_instance_columns lookup_as_fixed in
  {|
    V.VerifyingKey.domain := domain;
    V.VerifyingKey.fixed_commitments := fixed_commitments;
    V.VerifyingKey.permutation :=
      {| V.PermutationVK.commitments := permutation_commitments |};
    V.VerifyingKey.cs := cs;
    V.VerifyingKey.cs_degree := cs.(V.ConstraintSystem.degree);
    V.VerifyingKey.transcript_repr := transcript_repr;
  |}.

(** ** Small closed checks *)

Example query_index_first :
  query_index [(0, 0); (1, -1); (0, 1)] 0 1 = 2%nat.
Proof. reflexivity. Qed.

Example query_index_missing :
  query_index [(0, 0)] 3 0 = 1%nat.
Proof. reflexivity. Qed.

Definition sample_expr : Expression.t Configure.indexed_columns :=
  Expression.Sum
    (@Expression.Advice Configure.indexed_columns 0 Rotation.cur)
    (@Expression.Fixed Configure.indexed_columns 2 Rotation.next).

Definition sample_advice_qs : list (Z * Z) := [(0, 0); (1, 0)].
Definition sample_fixed_qs : list (Z * Z) := [(2, 1)].
Definition sample_instance_qs : list (Z * Z) := [].

Definition sample_read (col row : Z) : Z := col + 10 * row.

Example sample_reindex_eval :
  V.Expression.evaluate
    (reindex sample_advice_qs sample_fixed_qs sample_instance_qs sample_expr)
    (cell_evals sample_read 5 sample_fixed_qs)
    (cell_evals sample_read 5 sample_advice_qs)
    (cell_evals sample_read 5 sample_instance_qs)
  = eval_at_row sample_read sample_read sample_read 5 sample_expr.
Proof. vm_compute. reflexivity. Qed.

Example sample_reindex_eval_lemma :
  V.Expression.evaluate
    (reindex sample_advice_qs sample_fixed_qs sample_instance_qs sample_expr)
    (cell_evals sample_read 5 sample_fixed_qs)
    (cell_evals sample_read 5 sample_advice_qs)
    (cell_evals sample_read 5 sample_instance_qs)
  = eval_at_row sample_read sample_read sample_read 5 sample_expr.
Proof.
  apply reindex_preserves_eval.
  - reflexivity.
  - reflexivity.
  - unfold usize_fits. cbn. lia.
  - unfold usize_fits. cbn. lia.
  - unfold usize_fits. cbn. lia.
Qed.

End FromCompiled.
