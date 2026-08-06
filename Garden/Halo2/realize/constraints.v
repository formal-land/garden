(** * Flattening correctness: relational constraints vs. their gate polynomial.

    [serialize.v] lowers every gate constraint through
    [Configure.constraint_to_expression] into a single polynomial that the
    operational gate check compares against zero.  This file proves the
    field-level equivalence between the relational [eval_constraint] and that
    flattened form: for every constraint [c] outside the degenerate
    [Constraint.Range _ 0] class ([constraint_flattening_ok]),
    [eval_constraint Γ ix c] holds iff the flattened expression evaluates to
    zero.  It is pure modular-field algebra — the zero-product property over a
    prime for [Select]/[Either]/[Boolean]/[Range], a difference for [Equal] —
    and depends on none of the event-replay machinery. *)

Require Import Garden.Field.Field.
Require Garden.Plonky3.M.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.

Import ListNotations.
Global Open Scope Z_scope.

(** [Garden.Plonky3.M] is loaded but deliberately not imported: it carries a
    bracket notation that shadows the tactic intro-pattern grammar.  The one
    name needed from it, [IsBool], is reached through this alias. *)
Module IsBool := Garden.Plonky3.M.IsBool.

Section Correct.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  (** Normalized field values sit in [[0, p)], so their [UnOp.from] is the
      identity — the bridge between the modular operators and plain equality. *)
  Lemma from_id (x : Z) : 0 <= x < p -> UnOp.from x = x.
  Proof.
    intros Hx. unfold UnOp.from. apply Zmod_small. exact Hx.
  Qed.

  Lemma from_idemp (x : Z) : UnOp.from (UnOp.from x) = UnOp.from x.
  Proof.
    unfold UnOp.from.
    rewrite Z.mod_mod by (pose proof (prime_range (p := p)); lia).
    reflexivity.
  Qed.

  (** Every expression evaluates to a normalized value: each leaf and combinator
      of [eval_expression] ends in a [mod p]. *)
  Lemma eval_expression_range
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (e : Expression.t columns) :
    0 <= eval_expression assignment index e < p.
  Proof.
    pose proof (prime_range (p := p)) as Hp.
    destruct index as [region row].
    destruct e; try destruct e2;
      cbn [eval_expression];
      unfold eval_selector, UnOp.from, UnOp.opp, BinOp.add, BinOp.sub, BinOp.mul;
      apply Z.mod_pos_bound; lia.
  Qed.

  (** ** The range-check polynomial *)

  (** Pushing [eval_expression] through the [range_check_expression] fold turns
      a syntactic product of [(i - word)] factors into a numeric [BinOp.mul]
      fold over the same index list. *)
  Lemma eval_range_check_fold
      (assignment : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (word : Expression.t columns)
      (l : list nat) (seed : Expression.t columns) :
    eval_expression assignment (region, row)
      (List.fold_left
        (fun acc i =>
          Expression.Product acc
            (Expression.Sum
              (Expression.Constant (Z.of_nat i))
              (Expression.Negated word)))
        l seed)
    = List.fold_left
        (fun acc i =>
          BinOp.mul acc
            (BinOp.sub
              (UnOp.from (Z.of_nat i))
              (eval_expression assignment (region, row) word)))
        l (eval_expression assignment (region, row) seed).
  Proof.
    revert seed. induction l as [| i l IH]; intros seed; cbn [List.fold_left].
    - reflexivity.
    - rewrite IH. f_equal.
  Qed.

  (** A [BinOp.mul] fold is zero iff its seed is zero or some factor is: the
      integral-domain property lifted over a list. *)
  Lemma mul_fold_zero
      (h : nat -> Z) (l : list nat) (seed : Z) :
    0 <= seed < p ->
    List.fold_left (fun acc i => BinOp.mul acc (h i)) l seed = 0 <->
    seed = 0 \/ (exists i, List.In i l /\ UnOp.from (h i) = 0).
  Proof.
    revert seed. induction l as [| j l IH]; intros seed Hseed;
      cbn [List.fold_left].
    - split.
      + intros Hs. left. exact Hs.
      + intros [Hs | Hex].
        * exact Hs.
        * destruct Hex as [i Hex2]. destruct Hex2 as [Hin Hzero].
          destruct Hin.
    - set (seed' := BinOp.mul seed (h j)).
      assert (Hs' : 0 <= seed' < p).
      { unfold seed', BinOp.mul.
        pose proof (prime_range (p := p)). apply Z.mod_pos_bound. lia. }
      rewrite (IH seed' Hs').
      assert (Hz : seed' = 0 <-> seed = 0 \/ UnOp.from (h j) = 0).
      { unfold seed'. rewrite mul_zero_implies_zero.
        rewrite (from_id seed Hseed). reflexivity. }
      rewrite Hz. clear Hz IH.
      split.
      + intros [[Hs | Hj] | [i [Hin Hi]]].
        * left. exact Hs.
        * right. exists j. split; [ left; reflexivity | exact Hj ].
        * right. exists i. split; [ right; exact Hin | exact Hi ].
      + intros [Hs | [i [Hin Hi]]].
        * left. left. exact Hs.
        * destruct Hin as [Hj | Hin].
          -- left. right. rewrite Hj. exact Hi.
          -- right. exists i. split; [ exact Hin | exact Hi ].
  Qed.

  (** The range-check polynomial vanishes exactly when the normalized word
      lands in [[0, range)].  Both directions use that [eval_expression] is
      normalized: a factor [(i - word)] is zero iff [i mod p] equals the word,
      and [i mod p <= i < range]. *)
  Lemma range_check_expression_zero_iff
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (word : Expression.t columns) (range : nat) :
    (range <> 0)%nat ->
    eval_expression assignment index
      (Configure.range_check_expression word range) = 0 <->
    0 <= eval_expression assignment index word < Z.of_nat range.
  Proof.
    intros Hrange.
    destruct index as [region row].
    pose proof (prime_range (p := p)) as Hp.
    set (wv := eval_expression assignment (region, row) word).
    assert (Hwv : 0 <= wv < p) by apply eval_expression_range.
    unfold Configure.range_check_expression.
    rewrite eval_range_check_fold. fold wv.
    rewrite (mul_fold_zero
      (fun i => BinOp.sub (UnOp.from (Z.of_nat i)) wv)
      (List.seq 1 (Nat.pred range)) wv Hwv).
    (* Simplify the per-factor zero condition to [Z.of_nat i mod p = wv]. *)
    assert (Hfactor : forall i,
      UnOp.from (BinOp.sub (UnOp.from (Z.of_nat i)) wv) = 0 <->
      UnOp.from (Z.of_nat i) = wv).
    { intros i.
      assert (Hsub : 0 <= BinOp.sub (UnOp.from (Z.of_nat i)) wv < p).
      { unfold BinOp.sub. apply Z.mod_pos_bound. lia. }
      rewrite (from_id _ Hsub).
      rewrite sub_zero_equiv.
      rewrite from_idemp, (from_id wv Hwv). reflexivity. }
    (* Rephrase the existential using [Hfactor] and [in_seq]. *)
    assert (Hexists :
      (exists i, List.In i (List.seq 1 (Nat.pred range)) /\
        UnOp.from (BinOp.sub (UnOp.from (Z.of_nat i)) wv) = 0) <->
      (exists i, (1 <= i < range)%nat /\ UnOp.from (Z.of_nat i) = wv)).
    { split; intros [i [Hin Hi]]; exists i.
      - rewrite in_seq in Hin. rewrite Hfactor in Hi.
        split; [ lia | exact Hi ].
      - rewrite Hfactor. split; [ rewrite in_seq; lia | exact Hi ]. }
    rewrite Hexists. clear Hexists Hfactor.
    (* Interval characterization. *)
    split.
    - intros [Hz | [i [Hi Heq]]].
      + split; [ exact (proj1 Hwv) |].
        rewrite Hz. lia.
      + split; [ exact (proj1 Hwv) |].
        rewrite <- Heq. unfold UnOp.from.
        assert (Z.of_nat i mod p <= Z.of_nat i).
        { apply Z.mod_le; lia. }
        assert (Z.of_nat i < Z.of_nat range) by (apply Nat2Z.inj_lt; lia).
        lia.
    - intros [Hlo Hhi].
      destruct (Z.eq_dec wv 0) as [Hz | Hnz].
      + left. exact Hz.
      + right. exists (Z.to_nat wv).
        assert (HZ : Z.of_nat (Z.to_nat wv) = wv) by (rewrite Z2Nat.id; lia).
        split.
        * split.
          -- assert (0 < wv) by lia.
             assert (1 <= Z.to_nat wv)%nat by lia.
             lia.
          -- apply Nat2Z.inj_lt. rewrite HZ. exact Hhi.
        * rewrite HZ. apply from_id. exact Hwv.
  Qed.

  (** [IsBool.t] over [Z] is exactly membership in [{0, 1}]. *)
  Lemma isbool_iff (v : Z) : IsBool.t v <-> (v = 0 \/ v = 1).
  Proof.
    unfold IsBool.t, IsBool.ZIsBool; cbn.
    split.
    - intros Hv. destruct (Z.odd v) eqn:Hodd; cbn in Hv; [ right | left ]; exact Hv.
    - intros [Hv | Hv]; subst v; reflexivity.
  Qed.

  Lemma selected_zero_correct (selector value : Z) :
    0 <= selector < p ->
    0 <= value < p ->
    (selector <> 0 -> value = 0) <-> BinOp.mul selector value = 0.
  Proof.
    intros Hselector Hvalue.
    rewrite mul_zero_implies_zero,
      (from_id selector Hselector), (from_id value Hvalue).
    destruct (Z.eq_dec selector 0); tauto.
  Qed.

  Lemma selected_either_zero_correct (selector lhs rhs : Z) :
    0 <= selector < p ->
    0 <= lhs < p ->
    0 <= rhs < p ->
    (selector <> 0 -> lhs = 0 \/ rhs = 0) <->
      BinOp.mul (BinOp.mul selector lhs) rhs = 0.
  Proof.
    intros Hselector Hlhs Hrhs.
    rewrite mul_zero_implies_zero_3,
      (from_id selector Hselector),
      (from_id lhs Hlhs), (from_id rhs Hrhs).
    destruct (Z.eq_dec selector 0); tauto.
  Qed.

  (** ** The flattening theorem *)

  (** For every constraint outside the [Constraint.Range _ 0] class, relational
      satisfaction agrees with the gate polynomial being zero. *)
  Theorem constraint_to_expression_correct
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (c : Constraint.t columns) :
    constraint_flattening_ok c = true ->
    eval_constraint assignment index c <->
    eval_expression assignment index
      (Configure.constraint_to_expression c) = 0.
  Proof.
    destruct index as [region row].
    induction c as
      [ s c' IHc' | l r | e | e range | cl IHl cr IHr
      | l r | e ];
      intros Hfo.
    - (* Select *)
      cbn [constraint_flattening_ok] in Hfo.
      specialize (IHc' Hfo).
      destruct c' as
        [s' c'' | l r | e | e range | cl cr | l r | e];
        cbn [Configure.constraint_to_expression eval_constraint]
          in IHc' |- *.
      all: pose proof (eval_expression_range assignment (region, row)
        (Expression.Selector s)) as Hsv.
      all: cbn [eval_expression] in Hsv.
      all: try match type of IHc' with
        | ?body <-> eval_expression ?a ?ix ?flat = 0 =>
            let Hev := fresh "Hev" in
            pose proof (eval_expression_range a ix flat) as Hev;
            rewrite IHc';
            cbn [eval_expression];
            exact (selected_zero_correct
              (eval_selector assignment (region, row) s)
              (eval_expression a ix flat) Hsv Hev)
        end.
      (* [EitherZeroToPrecise] uses the exact deployed association. *)
      pose proof (eval_expression_range assignment (region, row) l) as Hlv.
      pose proof (eval_expression_range assignment (region, row) r) as Hrv.
      cbn [eval_expression].
      exact (selected_either_zero_correct
        (eval_selector assignment (region, row) s)
        (eval_expression assignment (region, row) l)
        (eval_expression assignment (region, row) r) Hsv Hlv Hrv).
      (* [EqualZeroToPrecise] reduces before the generic IH matcher. *)
      pose proof (eval_expression_range assignment (region, row) e) as He.
      cbn [eval_expression].
      exact (selected_zero_correct
        (eval_selector assignment (region, row) s)
        (eval_expression assignment (region, row) e) Hsv He).
    - (* Equal *)
      cbn [Configure.constraint_to_expression eval_expression eval_constraint].
      pose proof (eval_expression_range assignment (region, row) l) as Hl.
      pose proof (eval_expression_range assignment (region, row) r) as Hr.
      rewrite sub_zero_equiv.
      rewrite (from_id _ Hl), (from_id _ Hr). reflexivity.
    - (* Boolean *)
      cbn [Configure.constraint_to_expression eval_constraint].
      rewrite (range_check_expression_zero_iff assignment (region, row) e 2)
        by (intro Hc; discriminate).
      rewrite isbool_iff.
      change (Z.of_nat 2) with 2.
      split.
      + intros [Hv | Hv]; lia.
      + intro Hb. lia.
    - (* Range *)
      cbn [constraint_flattening_ok] in Hfo.
      rewrite Bool.negb_true_iff, Nat.eqb_neq in Hfo.
      cbn [Configure.constraint_to_expression eval_constraint].
      rewrite (range_check_expression_zero_iff assignment (region, row) e range Hfo).
      reflexivity.
    - (* Either *)
      cbn [constraint_flattening_ok] in Hfo.
      apply andb_prop in Hfo. destruct Hfo as [Hfl Hfr].
      specialize (IHl Hfl). specialize (IHr Hfr).
      cbn [Configure.constraint_to_expression eval_expression eval_constraint].
      set (el := eval_expression assignment (region, row)
        (Configure.constraint_to_expression cl)) in *.
      set (er := eval_expression assignment (region, row)
        (Configure.constraint_to_expression cr)) in *.
      assert (Hel : 0 <= el < p) by (unfold el; apply eval_expression_range).
      assert (Her : 0 <= er < p) by (unfold er; apply eval_expression_range).
      rewrite mul_zero_implies_zero, (from_id el Hel), (from_id er Her),
        IHl, IHr.
      reflexivity.
    - (* EitherZeroToPrecise *)
      cbn [Configure.constraint_to_expression eval_expression eval_constraint].
      pose proof (eval_expression_range assignment (region, row) l) as Hl.
      pose proof (eval_expression_range assignment (region, row) r) as Hr.
      rewrite mul_zero_implies_zero, (from_id _ Hl), (from_id _ Hr).
      reflexivity.
    - (* EqualZeroToPrecise *)
      cbn [Configure.constraint_to_expression eval_constraint].
      reflexivity.
  Qed.
End Correct.
