Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.air_small_parts.
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
      BinOp.mul diff (BinOp.mul (BinOp.sub diff 2) (BinOp.sub diff 4)) = 0
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
  rewrite BinOp.mul_zero_implies_zero in H_sum_diff.
  assert (from_mul : forall a b, UnOp.from (BinOp.mul a b) = BinOp.mul a b). {
    intros.
    unfold UnOp.from, BinOp.mul.
    apply Z.mod_small; lia.
  }
  rewrite from_mul in H_sum_diff.
  rewrite BinOp.mul_zero_implies_zero in H_sum_diff.
  clear from_mul.
  assert (H_q_minus_1 : forall n, -p < n < 0 -> p + n = n mod p). {
    intros.
    apply Z.mod_unique with (q := -1); lia.
  }
  assert (H_q_0 : forall n, 0 <= n < p -> n = n mod p). {
    intros.
    apply Z.mod_unique with (q := 0); lia.
  }
  unfold KeccakCols.Bool.get_a_prime in *.
  unfold KeccakCols.Bool.get_c_prime in *.
  do 6 (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff by lia)
    );
    destruct (Z.odd _)
  ).
  all: cbn in *; try reflexivity.
  all: unfold UnOp.from, BinOp.add, BinOp.sub in *; cbn in *.
  all: repeat (
    cbn in * ||
    (rewrite Z.mod_small with (a := 1) in * by lia) ||
    (rewrite Z.mod_small with (a := 2) in * by lia) ||
    (rewrite Z.mod_small with (a := 3) in * by lia) ||
    (rewrite Z.mod_small with (a := 4) in * by lia) ||
    (rewrite Z.mod_small with (a := 5) in * by lia)
  ).
  all: try lia.
  all:
    repeat match goal with
    | H_sum_diff : context [Z.modulo ?n ?p] |- _ =>
      (rewrite <- (H_q_minus_1 n) in H_sum_diff by lia) ||
      (rewrite <- (H_q_0 n) in H_sum_diff by lia)
    end.
  all: lia.
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
