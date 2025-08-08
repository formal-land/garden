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
Lemma xor_sum_diff_eq (local : KeccakCols.t) (x z : Z)
  (H_sum_diff :
    let diff :=
      Lists.List.fold_left Z.add [
        Z.b2z (KeccakCols.Bool.get_a_prime local x 0 z);
        Z.b2z (KeccakCols.Bool.get_a_prime local x 1 z);
        Z.b2z (KeccakCols.Bool.get_a_prime local x 2 z);
        Z.b2z (KeccakCols.Bool.get_a_prime local x 3 z);
        Z.b2z (KeccakCols.Bool.get_a_prime local x 4 z)
      ] 0 -
      Z.b2z (KeccakCols.Bool.get_c_prime local x z) in
    diff = 0 \/ diff = 2 \/ diff = 4
  ) :
  KeccakCols.Bool.get_c_prime local x z =
  xorbs [
    KeccakCols.Bool.get_a_prime local x 0 z;
    KeccakCols.Bool.get_a_prime local x 1 z;
    KeccakCols.Bool.get_a_prime local x 2 z;
    KeccakCols.Bool.get_a_prime local x 3 z;
    KeccakCols.Bool.get_a_prime local x 4 z
  ].
Proof.
  destruct (KeccakCols.Bool.get_c_prime _);
    repeat destruct (KeccakCols.Bool.get_a_prime _);
    cbn in *;
    lia.
Qed.

Lemma odd_b2z_eq (b : bool) :
  Z.odd (Z.b2z b) = b.
Proof.
  destruct b; cbn; reflexivity.
Qed.

Lemma eval_local_implies {p} `{Prime p} (local : KeccakCols.t) :
  let local := M.map_mod local in
  {{ eval_local local 🔽
    tt,
    FirstRowsFrom_a.From.t local
  }}.
Proof.
  intros *.
  unfold eval_local.
  eapply Run.LetAccumulate with (P1 := True). {
    admit.
  }
  intros [].
  eapply Run.LetAccumulate with (P1 := True). {
    admit.
  }
  intros [].
  eapply Run.LetAccumulate with (P1 := True). {
    admit.
  }
  intros [].
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
      admit.
    }
    unfold a_a_prime_c_c_prime.get_bit.
    cbn.
    admit.
  }
  { apply xor_sum_diff_eq.
    admit.
  }
Admitted.
