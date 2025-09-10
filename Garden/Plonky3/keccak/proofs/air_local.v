Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.proofs.air_small_parts.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

(** In this definition, we group all the constraints about the current [local] row. *)
Definition eval_local {p} `{Prime p} (local : KeccakCols.t) : M.t unit :=
  let* _ := preimage_a.eval local in
  let* _ := export_bool.eval local in
  let* _ := export_zero.eval local in
  let* _ := c_c_prime.eval local in
  let* _ := a_a_prime_c_c_prime.eval local in
  let* _ := a_prime_c_prime.eval local in
  let* _ := a_prime_prime.eval local in
  let* _ := a_prime_prime_0_0_bits_bools.eval local in
  let* _ := a_prime_prime_0_0_limbs.eval local in
  let* _ := a_prime_prime_prime_0_0_limbs.eval local in
  M.pure tt.

Definition xorbs (bs : list bool) : bool :=
  Lists.List.fold_left xorb bs false.

Module FirstRowsFrom_a.
  Module From.
    Record t (local : KeccakCols.t) : Prop := {
      c_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c_c_prime (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_a local x y z =
        xorbs [
          KeccakCols.Bool.get_a_prime local x y z;
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c_prime local x z
        ];
      a_prime_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_a_prime local x 0 z;
          KeccakCols.Bool.get_a_prime local x 1 z;
          KeccakCols.Bool.get_a_prime local x 2 z;
          KeccakCols.Bool.get_a_prime local x 3 z;
          KeccakCols.Bool.get_a_prime local x 4 z
        ];
    }.
  End From.

  Module To.
    Record t (local : KeccakCols.t) : Prop := {
      a_c (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c local x z =
        xorbs [
          KeccakCols.Bool.get_a local x 0 z;
          KeccakCols.Bool.get_a local x 1 z;
          KeccakCols.Bool.get_a local x 2 z;
          KeccakCols.Bool.get_a local x 3 z;
          KeccakCols.Bool.get_a local x 4 z
        ];
      c_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_a_prime local x y z =
        xorbs [
          KeccakCols.Bool.get_a local x y z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
    }.
  End To.

  (** The lemma explains why the calculation for the first rows is deterministic. *)
  Lemma from_implies_to (local : KeccakCols.t) :
    From.t local ->
    To.t local.
  Proof.
    intros []; constructor; intros; cbn in *.
    { repeat rewrite a_a_prime_c_c_prime by lia.
      repeat rewrite a_prime_c_prime by lia.
      repeat destruct (KeccakCols.Bool.get_c _);
        repeat destruct (KeccakCols.Bool.get_a_prime _);
        reflexivity.
    }
    { hauto l: on. }
    { rewrite a_a_prime_c_c_prime by lia.
      rewrite c_c_prime by lia.
      repeat destruct (KeccakCols.Bool.get_a_prime _);
        repeat destruct (KeccakCols.Bool.get_c _);
        reflexivity.
    }
  Qed.
End FirstRowsFrom_a.

Lemma sum_eq {p} `{Prime p}
    (b0 b1 b2 b3 b4 : bool) :
    Lists.List.fold_left BinOp.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 =
    Lists.List.fold_left Z.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 mod p.
Proof.
  cbn; unfold UnOp.from, BinOp.add.
  show_equality_modulo.
Qed.

Lemma mul_diff_or_eq {p} `{Prime p} (H_p : 6 <= p)
    (b0 b1 b2 b3 b4 b : bool)
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            Z.b2z b0;
            Z.b2z b1;
            Z.b2z b2;
            Z.b2z b3;
            Z.b2z b4
          ] 0 in
        BinOp.sub sum (Z.b2z b) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  let sum :=
    Lists.List.fold_left Z.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 in
  let diff :=
    sum - Z.b2z b in
  diff = 0 \/ diff - 2 = 0 \/ diff - 4 = 0.
Proof.
  intros.
  rewrite sum_eq in H_sum_diff.
  fold sum in H_sum_diff.
  rewrite M.mul_zero_implies_zero_3 in H_sum_diff.
  cbn -[sum] in H_sum_diff.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b - 2))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b - 4))
    in H_sum_diff
    by show_equality_modulo.
  repeat (rewrite M.is_zero_small in H_sum_diff by (destruct_all bool; cbn in *; lia)).
  trivial.
Qed.

(** Lemma to show that the calculation with the [diff] is actually a calculation of XOR. *)
Lemma xor_sum_diff_eq {p} `{Prime p} (H_p : 6 <= p) (local : KeccakCols.t) (x z : Z)
    (H_a_prime_bools :
      forall x y z,
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_a_prime local x y z)
    )
    (H_c_prime_bools :
      forall x z,
        0 <= x < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_c_prime local x z)
    )
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            KeccakCols.get_a_prime local x 0 z;
            KeccakCols.get_a_prime local x 1 z;
            KeccakCols.get_a_prime local x 2 z;
            KeccakCols.get_a_prime local x 3 z;
            KeccakCols.get_a_prime local x 4 z
          ] 0 in
        BinOp.sub sum (KeccakCols.get_c_prime local x z) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  KeccakCols.Bool.get_c_prime local x z =
  xorbs [
    KeccakCols.Bool.get_a_prime local x 0 z;
    KeccakCols.Bool.get_a_prime local x 1 z;
    KeccakCols.Bool.get_a_prime local x 2 z;
    KeccakCols.Bool.get_a_prime local x 3 z;
    KeccakCols.Bool.get_a_prime local x 4 z
  ].
Proof.
  intros.
  unfold KeccakCols.Bool.get_a_prime, KeccakCols.Bool.get_c_prime.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff by lia)
    );
    let b := fresh "b" in
    set (b := Z.odd _) in H_sum_diff;
    fold b;
    clearbody b
  ).
  epose proof (mul_diff_or_eq H_p _ _ _ _ _ _ H_sum_diff) as H_sum_diff_bis.
  clear H_sum_diff.
  destruct_all bool; cbn in *; destruct H_sum_diff_bis as [|[|] ]; congruence.
Qed.

Definition p_goldilocks : Z :=
  2^64 - 2^32 + 1.

(** As an experiment, we do the same proof as above but using an explicit value for the prime. The
    proof both happens to be faster and much simpler to write. *)
Lemma xor_sum_diff_eq_goldilocks `{Prime p_goldilocks} (local : KeccakCols.t) (x z : Z)
    (H_a_prime_bools :
      forall x y z,
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_a_prime local x y z)
    )
    (H_c_prime_bools :
      forall x z,
        0 <= x < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_c_prime local x z)
    )
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            KeccakCols.get_a_prime local x 0 z;
            KeccakCols.get_a_prime local x 1 z;
            KeccakCols.get_a_prime local x 2 z;
            KeccakCols.get_a_prime local x 3 z;
            KeccakCols.get_a_prime local x 4 z
          ] 0 in
        BinOp.sub sum (KeccakCols.get_c_prime local x z) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  KeccakCols.Bool.get_c_prime local x z =
  xorbs [
    KeccakCols.Bool.get_a_prime local x 0 z;
    KeccakCols.Bool.get_a_prime local x 1 z;
    KeccakCols.Bool.get_a_prime local x 2 z;
    KeccakCols.Bool.get_a_prime local x 3 z;
    KeccakCols.Bool.get_a_prime local x 4 z
  ].
Proof.
  intros.
  unfold KeccakCols.Bool.get_a_prime, KeccakCols.Bool.get_c_prime.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff by lia)
    );
    let b := fresh "b" in
    set (b := Z.odd _) in H_sum_diff;
    fold b;
    clearbody b
  ).
  destruct_all bool; cbv in H_sum_diff; cbv; congruence.
Qed.

Module Pre.
  Record t (local : KeccakCols.t) : Prop := {
    a_bools (x y z : Z) :
      0 <= x < 5 ->
      0 <= y < 5 ->
      0 <= z < 64 ->
      IsBool.t (KeccakCols.get_a local x y z)
  }.
End Pre.

Lemma eval_local_implies {p} `{Prime p} (H_p : 6 <= p) (local' : KeccakCols.t) :
  let local := M.map_mod local' in
  Pre.t local ->
  {{ eval_local local 🔽
    tt,
    FirstRowsFrom_a.From.t local
  }}.
Proof.
  intros * [].
  unfold eval_local.
  eapply Run.LetAccumulate. {
    apply preimage_a.implies.
  }
  intros H_eval_assert_preimage_a.
  eapply Run.LetAccumulate. {
    apply export_bool.implies.
  }
  intros H_eval_assert_export_bool.
  eapply Run.LetAccumulate. {
    apply export_zero.implies.
  }
  intros H_eval_assert_export_zero.
  eapply Run.LetAccumulate. {
    apply c_c_prime.implies.
  }
  intros [].
  eapply Run.LetAccumulate. {
    apply a_a_prime_c_c_prime.implies.
  }
  intros [].
  eapply Run.LetAccumulate. {
    apply a_prime_c_prime.implies.
  }
  intros H_eval_assert_a_prime_c_prime.
  eapply Run.LetAccumulate. {
    apply a_prime_prime.implies.
  }
  intros H_eval_assert_a_prime_prime.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_bits_bools.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_bits_bools.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_limbs.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_prime_0_0_limbs.
  eapply Run.Implies. {
    apply Run.Pure.
  }
  intros [].
  assert (c_prime_bools :
    forall x z,
    0 <= x < 5 ->
    0 <= z < 64 ->
    IsBool.t (KeccakCols.get_c_prime local x z)
  ). {
    intros.
    rewrite c_c_prime_eq by lia.
    apply M.xor3_is_bool; apply c_bools; lia.
  }
  constructor; intros.
  { unfold KeccakCols.Bool.get_c, KeccakCols.Bool.get_c_prime.
    rewrite c_c_prime_eq by lia.
    repeat rewrite c_bools by lia.
    rewrite xor3_eq.
    repeat (cbn || f_equal || rewrite odd_b2z_eq).
  }
  { unfold KeccakCols.Bool.get_a.
    unfold KeccakCols.get_a in a_a_prime_c_c_prime_eq.
    erewrite Limbs.get_bit_of_bools_eqs; try (unfold U64_LIMBS, BITS_PER_LIMB; lia).
    3: {
      intros.
      apply a_a_prime_c_c_prime_eq; lia.
    }
    2: {
      intros.
      unfold a_a_prime_c_c_prime.get_bit.
      apply M.xor3_is_bool; cbn in *.
      { apply a_prime_bools; lia. }
      { apply c_bools; lia. }
      { apply c_prime_bools; lia. }
    }
    unfold a_a_prime_c_c_prime.get_bit.
    cbn - [local].
    rewrite <- odd_b2z_eq; f_equal.
    rewrite <- M.xor3_eq; f_equal.
    { apply a_prime_bools; lia. }
    { apply c_bools; lia. }
    { apply c_prime_bools; lia. }
  }
  { apply xor_sum_diff_eq; trivial.
    apply H_eval_assert_a_prime_c_prime; lia.
  }
Qed.
