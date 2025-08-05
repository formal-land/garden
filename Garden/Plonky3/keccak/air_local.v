Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.air_small_parts.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

(** In this definition, we group all the constraints about the current [local] row. *)
Definition eval_local {p} `{Prime p} (local : KeccakCols.t) : M.t unit :=
  let* _ := eval_preimage_a local in
  let* _ := eval_assert_export_bool local in
  let* _ := eval_assert_export_zero local in
  let* _ := eval_assert_c_c_prime local in
  let* _ := eval_assert_a_a_prime_c_c_prime local in
  let* _ := eval_assert_a_prime_c_prime local in
  let* _ := eval_assert_a_prime_prime local in
  let* _ := eval_assert_a_prime_prime_0_0_bits_bools local in
  let* _ := eval_assert_a_prime_prime_0_0_limbs local in
  let* _ := eval_assert_a_prime_prime_prime_0_0_limbs local in
  M.pure tt.

Module KeccakCols.
  Definition get_a (local : KeccakCols.t) (y x z : Z) : bool :=
    Limbs.get_bit BITS_PER_LIMB ((local.(KeccakCols.a).(Array.get) y).(Array.get) x) z.

  Definition get_c (local : KeccakCols.t) (x z : Z) : bool :=
    Z.odd ((local.(KeccakCols.c).(Array.get) x).(Array.get) z).

  Definition get_c_prime (local : KeccakCols.t) (x z : Z) : bool :=
    Z.odd ((local.(KeccakCols.c_prime).(Array.get) x).(Array.get) z).

  Definition get_a_prime (local : KeccakCols.t) (y x z : Z) : bool :=
    Z.odd (((local.(KeccakCols.a_prime).(Array.get) y).(Array.get) x).(Array.get) z).
End KeccakCols.

Definition xorbs (bs : list bool) : bool :=
  Lists.List.fold_left xorb bs false.

Module FirstRowsFrom_a.
  Module From.
    Record t (local : KeccakCols.t) : Set := {
      c_c_prime (x z : Z) :
        KeccakCols.get_c_prime local x z =
        xorbs [
          KeccakCols.get_c local x z;
          KeccakCols.get_c local ((x + 4) mod 5) z;
          KeccakCols.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c_c_prime (x y z : Z) :
        KeccakCols.get_a local x y z =
        xorbs [
          KeccakCols.get_a_prime local x y z;
          KeccakCols.get_c local x z;
          KeccakCols.get_c_prime local x z
        ];
      a_prime_c_prime (x z : Z) :
        KeccakCols.get_c_prime local x z =
        xorbs [
          KeccakCols.get_a_prime local x 0 z;
          KeccakCols.get_a_prime local x 1 z;
          KeccakCols.get_a_prime local x 2 z;
          KeccakCols.get_a_prime local x 3 z;
          KeccakCols.get_a_prime local x 4 z
        ];
    }.
  End From.

  Module To.
    Record t (local : KeccakCols.t) : Set := {
      a_c (x z : Z) :
        KeccakCols.get_c local x z =
        xorbs [
          KeccakCols.get_a local x 0 z;
          KeccakCols.get_a local x 1 z;
          KeccakCols.get_a local x 2 z;
          KeccakCols.get_a local x 3 z;
          KeccakCols.get_a local x 4 z
        ];
      c_c_prime (x z : Z) :
        KeccakCols.get_c_prime local x z =
        xorbs [
          KeccakCols.get_c local x z;
          KeccakCols.get_c local ((x + 4) mod 5) z;
          KeccakCols.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c (x y z : Z) :
        KeccakCols.get_a_prime local x y z =
        xorbs [
          KeccakCols.get_a local x y z;
          KeccakCols.get_c local ((x + 4) mod 5) z;
          KeccakCols.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
    }.
  End To.

  (** The lemma explains why the calculation for the first rows is deterministic. *)
  Lemma from_implies_to (local : KeccakCols.t) :
    From.t local ->
    To.t local.
  Proof.
    intros []; constructor; intros; cbn in *.
    { repeat rewrite a_a_prime_c_c_prime.
      repeat rewrite a_prime_c_prime.
      repeat destruct (KeccakCols.get_c _);
        repeat destruct (KeccakCols.get_a_prime _);
        reflexivity.
    }
    { congruence. }
    { rewrite a_a_prime_c_c_prime.
      rewrite c_c_prime.
      repeat destruct (KeccakCols.get_a_prime _);
        repeat destruct (KeccakCols.get_c _);
        reflexivity.
    }
  Qed.
End FirstRowsFrom_a.

(** Lemma to show that the calculation with the [diff] is actually a calculation of XOR. *)
Lemma xor_sum_diff_eq (local : KeccakCols.t) (x z : Z)
  (H_sum_diff :
    let diff :=
      Lists.List.fold_left Z.add [
        Z.b2z (KeccakCols.get_a_prime local x 0 z);
        Z.b2z (KeccakCols.get_a_prime local x 1 z);
        Z.b2z (KeccakCols.get_a_prime local x 2 z);
        Z.b2z (KeccakCols.get_a_prime local x 3 z);
        Z.b2z (KeccakCols.get_a_prime local x 4 z)
      ] 0 -
      Z.b2z (KeccakCols.get_c_prime local x z) in
    diff = 0 \/ diff = 2 \/ diff = 4
  ) :
  KeccakCols.get_c_prime local x z =
  xorbs [
    KeccakCols.get_a_prime local x 0 z;
    KeccakCols.get_a_prime local x 1 z;
    KeccakCols.get_a_prime local x 2 z;
    KeccakCols.get_a_prime local x 3 z;
    KeccakCols.get_a_prime local x 4 z
  ].
Proof.
  destruct (KeccakCols.get_c_prime _);
    repeat destruct (KeccakCols.get_a_prime _);
    cbn in *;
    lia.
Qed.
