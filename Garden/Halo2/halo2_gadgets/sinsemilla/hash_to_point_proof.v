Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** The point-level Sinsemilla round: the [y] companion to
    [Sinsemilla.deterministic] (which pins the next-row [x_a] only), combined
    with [GeneratorTable.sound] into the full point-level round
    equation [(x_a, y_a)@next = SinsemillaSpec.round (x_a, y_a)@cur word].

    The chip's running ordinate is the *doubled* value [y_a] (the [chip.y_a]
    expression); the actual accumulator ordinate is that expression halved by
    [two_inv]. Both incomplete additions folded into one [round] step carry a
    genuine nondegeneracy precondition (the accumulator's x-coordinate must
    differ from the generator's, and from the first partial sum's) — the
    circuit gate is only sound where its own incomplete-addition formulas are
    (halo2's documented Sinsemilla exceptional case). The two round theorems
    live in [hash_to_point_round_proof.v] /
    [hash_to_point_round_final_proof.v] and the row fold in
    [hash_to_point_fold_proof.v] (so the two heavy per-row proofs compile
    in parallel); this file holds the shared definitions and the pure
    word-list algebra they and the fold consume. *)
Module SinsemillaHash.
  (* The derived accumulator point at a row: [x_a] directly, and the actual
     (halved) ordinate recovered from the chip's doubled [y_a] expression. *)
  Definition acc_at
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (x_a x_p lambda_1 lambda_2 : Advice.t) (region : RegionId) (row : Z)
      : Point.t := {|
    Point.x := Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row);
    Point.y :=
      (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
          .y_a x_a x_p lambda_1 lambda_2 Rotation.cur ⟧ (region, row))
        *F Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv;
  |}.

  (* The message word consumed at a row, read off the running-sum slice the
     lookup argument pins. *)
  Definition word_at
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId) (row : Z)
      : Z :=
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
        .generator_table_word q_sinsemilla2 bits ⟧ (region, row).

  (* Literal reduction: [2] and [two_inv] are exact multiplicative inverses in
     the Pallas base field. Cheap ([two_inv] is a single concrete literal), no
     table involved. *)
  Lemma two_mul_two_inv :
    UnOp.from 2 *F Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* Doubling a halved value recovers the original (reduced) value. *)
  Lemma double_half (x : Z) :
    UnOp.from 2 *F (x *F Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv)
      = UnOp.from x.
  Proof.
    rewrite <- field_mul_assoc, (field_mul_comm (UnOp.from 2) x),
      field_mul_assoc, two_mul_two_inv.
    apply FieldRewrite.mul_one_right.
  Qed.

  (* [Selector.eval] on an [= 1] fact reduces to the literal [1]: the boolean
     reading [GeneratorTable.sound] needs, sharper than [enabled_nonzero]'s
     [<> 0]. *)
  Lemma enabled_eq_one
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (selector : columns.(Columns.Selector))
      (region : RegionId) (row : Z)
      (Henabled : Γ.(Assignment.selector) selector region row = 1) :
    Γ ⊢ ⟦ Expression.Selector selector ⟧ (region, row) = 1.
  Proof.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression eval_selector].
    rewrite Henabled.
    apply FieldRewrite.from_one.
  Qed.


  (** * Message-fold correctness *)

  (** The words consumed by rows [0 .. n-1] of a hash-to-point region, read
      off the running-sum slices the lookup argument pins. *)
  Definition hash_words
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId) (n : nat)
      : list Z :=
    List.map (fun j => word_at Γ q_sinsemilla2 bits region (Z.of_nat j))
      (List.seq 0%nat n).

  (** The Sinsemilla incomplete-addition nondegeneracy of a message from [Q]:
      at every round, the accumulator's x-coordinate differs from the
      generator's and from the first partial sum's (halo2's documented
      exceptional cases, under which the witnessed gradients are free). *)
  Definition nondegenerate (Q : Point.t) (words : list Z) : Prop :=
    forall k : nat, (k < List.length words)%nat ->
      let acc :=
        SinsemillaSpec.sinsemilla_hash_to_point Q (List.firstn k words) in
      let w := List.nth k words 0 in
      Point.x acc <> Point.x (SinsemillaSpec.generator w) /\
      Point.x acc <>
        Point.x (EccSpec.point_add_incomplete acc (SinsemillaSpec.generator w)).

  Lemma hash_words_length
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId) (n : nat) :
    List.length (hash_words Γ q_sinsemilla2 bits region n) = n.
  Proof.
    unfold hash_words. now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma hash_words_S
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId) (n : nat) :
    hash_words Γ q_sinsemilla2 bits region (S n) =
      hash_words Γ q_sinsemilla2 bits region n
        ++ [word_at Γ q_sinsemilla2 bits region (Z.of_nat n)].
  Proof.
    unfold hash_words.
    now rewrite List.seq_S, List.map_app, Nat.add_0_l.
  Qed.

  Lemma hash_words_firstn
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId)
      (k n : nat) :
    (k <= n)%nat ->
    List.firstn k (hash_words Γ q_sinsemilla2 bits region n) =
      hash_words Γ q_sinsemilla2 bits region k.
  Proof.
    intros Hkn.
    unfold hash_words.
    replace n with (k + (n - k))%nat by lia.
    rewrite List.seq_app, List.map_app, List.firstn_app.
    rewrite List.length_map, List.length_seq.
    rewrite List.firstn_all2
      by (rewrite List.length_map, List.length_seq; lia).
    rewrite Nat.sub_diag. cbn [List.firstn]. apply List.app_nil_r.
  Qed.

  Lemma hash_words_nth
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId)
      (k n : nat) :
    (k < n)%nat ->
    List.nth k (hash_words Γ q_sinsemilla2 bits region n) 0 =
      word_at Γ q_sinsemilla2 bits region (Z.of_nat k).
  Proof.
    intros Hk. unfold hash_words. now rewrite nth_map_seq.
  Qed.

  (** The seed: the [InitialYQ] output equation pins the accumulator at the
      first hash row to the domain point [(x_a cell, y_q)] — the bridge from
      [InitialYQ.deterministic] to the fold's initial condition. *)
  Lemma acc_at_init
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (x_a x_p lambda_1 lambda_2 : Advice.t) (region : RegionId) (row : Z)
      (y_q : Z)
      (Hy :
        {|
          InitialYQ.y_a :=
            Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
                .y_a x_a x_p lambda_1 lambda_2 Rotation.cur ⟧ (region, row);
        |} = InitialYQ.output y_q) :
    acc_at Γ x_a x_p lambda_1 lambda_2 region row =
      {|
        Point.x := Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row);
        Point.y := UnOp.from y_q;
      |}.
  Proof.
    pose proof (f_equal InitialYQ.y_a Hy) as Hya.
    unfold InitialYQ.output in Hya.
    cbn [InitialYQ.y_a] in Hya.
    unfold acc_at.
    f_equal.
    rewrite Hya.
    rewrite field_mul_assoc, two_mul_two_inv.
    apply FieldRewrite.mul_one_right.
  Qed.


  (** * Running-sum / word-list algebra

      The pure-[Z] bridge between the per-row words and the piece values the
      decomposition gates check: [digit_sum] packs a little-endian 10-bit word
      list into an integer, [words_le] (the spec-side decomposition) is its
      inverse on bounded words, and [piece_telescope] recovers the exact
      integer [digit_sum] from the chained running-sum field equations (no
      wrap-around: a piece is at most 250 bits, below the Pallas modulus). *)

  Fixpoint digit_sum (ws : list Z) : Z :=
    match ws with
    | [] => 0
    | w :: ws => w + 2 ^ 10 * digit_sum ws
    end.

  Lemma digit_sum_bound (ws : list Z) :
    List.Forall (fun w => 0 <= w < 2 ^ 10) ws ->
    0 <= digit_sum ws < 2 ^ (10 * Z.of_nat (List.length ws)).
  Proof.
    induction ws as [| w ws IH]; intros Hall.
    - cbn. lia.
    - inversion Hall as [| ? ? Hw Hws]; subst.
      specialize (IH Hws).
      cbn [digit_sum List.length].
      rewrite Nat2Z.inj_succ.
      replace (10 * Z.succ (Z.of_nat (List.length ws)))
        with (10 + 10 * Z.of_nat (List.length ws)) by lia.
      rewrite Z.pow_add_r by lia.
      nia.
  Qed.

  (** [digit_sum] of an append: the tail is shifted by the head's width. *)
  Lemma digit_sum_app (xs ys : list Z) :
    digit_sum (xs ++ ys) =
      digit_sum xs + 2 ^ (10 * Z.of_nat (List.length xs)) * digit_sum ys.
  Proof.
    induction xs as [| x xs IH];
      cbn [List.app digit_sum List.length].
    - lia.
    - rewrite IH, Nat2Z.inj_succ.
      replace (10 * Z.succ (Z.of_nat (List.length xs)))
        with (10 + 10 * Z.of_nat (List.length xs)) by lia.
      rewrite Z.pow_add_r by lia.
      ring.
  Qed.

  Lemma words_le_digit_sum (ws : list Z) :
    List.Forall (fun w => 0 <= w < 2 ^ 10) ws ->
    SinsemillaSpec.words_le (List.length ws) (digit_sum ws) = ws.
  Proof.
    induction ws as [| w ws IH]; intros Hall; [reflexivity |].
    inversion Hall as [| ? ? Hw Hws]; subst.
    assert (Hp10 : 0 < 2 ^ 10) by (apply Z.pow_pos_nonneg; lia).
    cbn [List.length SinsemillaSpec.words_le digit_sum].
    unfold SinsemillaSpec.sinsemilla_k.
    assert (Hmod : (w + 2 ^ 10 * digit_sum ws) mod 2 ^ 10 = w).
    { rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (Hdiv : (w + 2 ^ 10 * digit_sum ws) / 2 ^ 10 = digit_sum ws).
    { rewrite Z.mul_comm, Z_div_plus_full by lia.
      rewrite Z.div_small by lia. lia. }
    rewrite Hmod, Hdiv.
    now rewrite (IH Hws).
  Qed.

  Lemma words_le_app (m n : nat) (x y : Z) :
    0 <= x < 2 ^ (10 * Z.of_nat m) ->
    0 <= y ->
    SinsemillaSpec.words_le (m + n) (x + y * 2 ^ (10 * Z.of_nat m)) =
      SinsemillaSpec.words_le m x ++ SinsemillaSpec.words_le n y.
  Proof.
    induction m as [| m IH] in x, y |- *; intros Hx Hy.
    - replace (2 ^ (10 * Z.of_nat 0)) with 1 in Hx |- * by reflexivity.
      replace (x + y * 1) with y by lia.
      reflexivity.
    - assert (Hp10 : 0 < 2 ^ 10) by (apply Z.pow_pos_nonneg; lia).
      assert (Hpm : 0 < 2 ^ (10 * Z.of_nat m))
        by (apply Z.pow_pos_nonneg; lia).
      assert (Hpow :
          2 ^ (10 * Z.of_nat (S m)) = 2 ^ (10 * Z.of_nat m) * 2 ^ 10).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      rewrite Hpow in Hx |- *.
      cbn [Nat.add SinsemillaSpec.words_le List.app].
      unfold SinsemillaSpec.sinsemilla_k.
      replace (x + y * (2 ^ (10 * Z.of_nat m) * 2 ^ 10))
        with (x + y * 2 ^ (10 * Z.of_nat m) * 2 ^ 10) by ring.
      assert (Hmod :
          (x + y * 2 ^ (10 * Z.of_nat m) * 2 ^ 10) mod 2 ^ 10 = x mod 2 ^ 10)
        by apply Z_mod_plus_full.
      assert (Hdiv :
          (x + y * 2 ^ (10 * Z.of_nat m) * 2 ^ 10) / 2 ^ 10 =
            x / 2 ^ 10 + y * 2 ^ (10 * Z.of_nat m))
        by (apply Z_div_plus_full; lia).
      rewrite Hmod, Hdiv.
      f_equal.
      apply IH; [| exact Hy].
      split.
      + apply Z.div_pos; lia.
      + apply Z.div_lt_upper_bound; lia.
  Qed.

  (** One running-sum step, mod-free: a bounded word plus a shifted bounded
      tail stays below [p], so the field equation is an integer identity. *)
  Lemma field_digit_step (a s : Z)
      (Ha : 0 <= a) (Hs : 0 <= s)
      (Hlt : a + 2 ^ 10 * s < Primes.pallas_p) :
    a +F (UnOp.from (2 ^ 10) *F s) = a + 2 ^ 10 * s.
  Proof.
    assert (Hp10a : 0 <= 2 ^ 10) by (apply Z.pow_nonneg; lia).
    assert (Hp10b : 2 ^ 10 < Primes.pallas_p) by (vm_compute; reflexivity).
    assert (Hprod : 0 <= 2 ^ 10 * s) by (apply Z.mul_nonneg_nonneg; lia).
    unfold BinOp.add, BinOp.mul, UnOp.from.
    rewrite (Z.mod_small (2 ^ 10)) by lia.
    rewrite (Z.mod_small (2 ^ 10 * s)) by lia.
    apply Z.mod_small. lia.
  Qed.

  (** Splitting off the first word of a piece's word list. *)
  Lemma digit_sum_words_head
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId)
      (offset : Z) (m : nat) :
    digit_sum (List.map
      (fun j : nat => word_at Γ q_sinsemilla2 bits region (offset + Z.of_nat j))
      (List.seq 0%nat (S m))) =
      word_at Γ q_sinsemilla2 bits region offset +
        2 ^ 10 * digit_sum (List.map
          (fun j : nat =>
            word_at Γ q_sinsemilla2 bits region (offset + 1 + Z.of_nat j))
          (List.seq 0%nat m)).
  Proof.
    cbn [List.seq List.map digit_sum].
    replace (offset + Z.of_nat 0) with offset by lia.
    f_equal.
    f_equal.
    rewrite <- List.seq_shift, List.map_map.
    f_equal.
    apply List.map_ext. intros j. f_equal. lia.
  Qed.

  (** The telescope (the field-to-integer bridge of the row fold): over a run
      of [n] running-sum rows — the chained [q_s2 = 1] word equations [Hstep]
      and the final-row equation [Hlast] — the piece cell at [offset] holds
      *exactly* the integer [digit_sum] of the row words, with no modular
      wrap, because the packed value is below [2^250 < p]. *)
  Lemma piece_telescope
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_sinsemilla2 : Fixed.t) (bits : Advice.t) (region : RegionId)
      (offset : Z) (n : nat)
      (Hn : (0 < n)%nat)
      (Hstep : forall j : nat, (S j < n)%nat ->
        Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧
            (region, offset + Z.of_nat j) =
          word_at Γ q_sinsemilla2 bits region (offset + Z.of_nat j) +F
            (UnOp.from (2 ^ 10) *F
              (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧
                (region, offset + Z.of_nat j + 1))))
      (Hlast :
        Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧
            (region, offset + Z.of_nat (n - 1)) =
          word_at Γ q_sinsemilla2 bits region (offset + Z.of_nat (n - 1)))
      (Hbound : forall j : nat, (j < n)%nat ->
        0 <= word_at Γ q_sinsemilla2 bits region (offset + Z.of_nat j) < 2 ^ 10)
      (Hlen : 10 * Z.of_nat n <= 250) :
    Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (region, offset) =
      digit_sum (List.map
        (fun j : nat =>
          word_at Γ q_sinsemilla2 bits region (offset + Z.of_nat j))
        (List.seq 0%nat n)).
  Proof.
    induction n as [| n' IH] in offset, Hn, Hstep, Hlast, Hbound, Hlen |- *;
      [lia |].
    destruct n' as [| n''].
    - (* A single row: the piece cell is the row word. *)
      rewrite digit_sum_words_head.
      cbn [List.seq List.map digit_sum].
      replace (offset + Z.of_nat (1 - 1)) with offset in Hlast by lia.
      rewrite Hlast.
      lia.
    - (* Head step: split off row [offset] and recurse at [offset + 1]. *)
      assert (Htail :
          Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (region, offset + 1) =
            digit_sum (List.map
              (fun j : nat =>
                word_at Γ q_sinsemilla2 bits region (offset + 1 + Z.of_nat j))
              (List.seq 0%nat (S n'')))).
      { apply IH.
        - lia.
        - intros j Hj.
          specialize (Hstep (S j) ltac:(lia)).
          replace (offset + Z.of_nat (S j)) with (offset + 1 + Z.of_nat j)
            in Hstep by lia.
          exact Hstep.
        - replace (offset + Z.of_nat (S (S n'') - 1))
            with (offset + 1 + Z.of_nat (S n'' - 1)) in Hlast by lia.
          exact Hlast.
        - intros j Hj.
          specialize (Hbound (S j) ltac:(lia)).
          replace (offset + Z.of_nat (S j)) with (offset + 1 + Z.of_nat j)
            in Hbound by lia.
          exact Hbound.
        - lia. }
      pose proof (Hstep 0%nat ltac:(lia)) as Hhead.
      replace (offset + Z.of_nat 0) with offset in Hhead by lia.
      pose proof (Hbound 0%nat ltac:(lia)) as Hb0.
      replace (offset + Z.of_nat 0) with offset in Hb0 by lia.
      assert (Hall : List.Forall (fun w => 0 <= w < 2 ^ 10)
          (List.map
            (fun j : nat =>
              word_at Γ q_sinsemilla2 bits region (offset + 1 + Z.of_nat j))
            (List.seq 0%nat (S n'')))).
      { rewrite List.Forall_map, List.Forall_forall.
        intros j Hj. rewrite List.in_seq in Hj.
        specialize (Hbound (S j) ltac:(lia)).
        replace (offset + Z.of_nat (S j)) with (offset + 1 + Z.of_nat j)
          in Hbound by lia.
        exact Hbound. }
      pose proof (digit_sum_bound _ Hall) as Hds.
      rewrite List.length_map, List.length_seq in Hds.
      rewrite digit_sum_words_head.
      rewrite Hhead, Htail.
      assert (Hp10 : 0 < 2 ^ 10) by (apply Z.pow_pos_nonneg; lia).
      assert (Hpow1 : 2 ^ 10 * 2 ^ (10 * Z.of_nat (S n'')) =
          2 ^ (10 + 10 * Z.of_nat (S n''))).
      { rewrite Z.pow_add_r by lia. reflexivity. }
      assert (Hpow2 : 2 ^ (10 + 10 * Z.of_nat (S n'')) <= 2 ^ 250)
        by (apply Z.pow_le_mono_r; lia).
      assert (Hpbig : 2 ^ 250 < Primes.pallas_p)
        by (vm_compute; reflexivity).
      apply field_digit_step; [lia | lia | nia].
  Qed.
End SinsemillaHash.
