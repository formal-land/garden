Require Import Plonky3.M.
Require Import Plonky3.MExpr.
Require Import Plonky3.keccak.proofs.air_small_parts.
Require Import Plonky3.keccak.columns.
Require Import Plonky3.keccak.constants.
Require Import Plonky3.keccak.round_flags.

(** Definition grouping all the constraints. *)
Definition eval_local {p} `{Prime p} (SQUARE_SIZE : Z)
    (local next : KeccakCols.t)
    (is_first_row is_transition : Z) :
    M.t unit :=
  msg* "eval_round_flags" in
  let* _ := eval_round_flags local next is_first_row is_transition in
  msg* "preimage_a" in
  let* _ := preimage_a.eval SQUARE_SIZE local in
  msg* "preimage_next_preimage" in
  let* _ := preimage_next_preimage.eval SQUARE_SIZE local next is_transition in
  msg* "export_bool" in
  let* _ := export_bool.eval local in
  msg* "export_zero" in
  let* _ := export_zero.eval local in
  msg* "c_c_prime" in
  let* _ := c_c_prime.eval SQUARE_SIZE local in
  msg* "a_a_prime_c_c_prime" in
  let* _ := a_a_prime_c_c_prime.eval SQUARE_SIZE local in
  msg* "a_prime_c_prime" in
  let* _ := a_prime_c_prime.eval SQUARE_SIZE local in
  msg* "a_prime_prime" in
  let* _ := a_prime_prime.eval SQUARE_SIZE local in
  msg* "a_prime_prime_0_0_bits_bools" in
  let* _ := a_prime_prime_0_0_bits_bools.eval local in
  msg* "a_prime_prime_0_0_limbs" in
  let* _ := a_prime_prime_0_0_limbs.eval local in
  msg* "a_prime_prime_prime_0_0_limbs" in
  let* _ := a_prime_prime_prime_0_0_limbs.eval local in
  msg* "a_prime_prime_prime_next_a" in
  let* _ := a_prime_prime_prime_next_a.eval SQUARE_SIZE local next is_transition in
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
    a_prime_c_prime.get_sum [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] =
    Lists.List.fold_right Z.add 0 [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] mod p.
Proof.
  cbn; unfold UnOp.from, BinOp.add.
  show_equality_modulo.
  sauto lq: on.
Qed.

Lemma mul_diff_or_eq {p} `{Prime p} (H_p : 6 <= p)
    (b0 b1 b2 b3 b4 b : bool)
    (H_sum_diff :
      let diff :=
        let sum :=
          a_prime_c_prime.get_sum [
            Z.b2z b0;
            Z.b2z b1;
            Z.b2z b2;
            Z.b2z b3;
            Z.b2z b4
          ] in
        sum -F (Z.b2z b) in
      diff *F (diff -F 2) *F (diff -F 4) = 0
    ) :
  let sum :=
    Lists.List.fold_right Z.add 0 [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] in
  let diff :=
    sum - Z.b2z b in
  diff = 0 \/ diff - 2 = 0 \/ diff - 4 = 0.
Proof.
  intros.
  rewrite sum_eq in H_sum_diff.
  fold sum in H_sum_diff.
  rewrite M.mul_zero_implies_zero_3 in H_sum_diff.
  cbn -[sum] in H_sum_diff.
  replace (UnOp.from (_ -F _))
    with (UnOp.from (sum - Z.b2z b))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (_ -F _))
    with (UnOp.from (sum - Z.b2z b - 2))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (_ -F _))
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
          a_prime_c_prime.get_sum [
            KeccakCols.get_a_prime local x 0 z;
            KeccakCols.get_a_prime local x 1 z;
            KeccakCols.get_a_prime local x 2 z;
            KeccakCols.get_a_prime local x 3 z;
            KeccakCols.get_a_prime local x 4 z
          ] in
        sum -F (KeccakCols.get_c_prime local x z) in
      diff *F (diff -F 2) *F (diff -F 4) = 0
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
        sum -F (KeccakCols.get_c_prime local x z) in
      diff *F (diff -F 2) *F (diff -F 4) = 0
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

Module Post.
  Record t {p} `{Prime p}
      (local next : KeccakCols.t)
      (is_first_row is_transition : bool) :
    Prop :=
  {
    round_flags : round_flags.Spec.t local next is_first_row is_transition;
    preimage_a : preimage_a.Spec.t local;
    to : FirstRowsFrom_a.To.t local;
    a_prime_prime : a_prime_prime.Post.t 5 local;
    a_prime_prime_0_0_bits_bools : a_prime_prime_0_0_bits_bools.Post.t local;
    a_prime_prime_0_0_limbs : a_prime_prime_0_0_limbs.Post.t local;
    a_prime_prime_prime_0_0_limbs : a_prime_prime_prime_0_0_limbs.Post.t local;
  }.
End Post.

Lemma eval_implies {p} `{Prime p} (H_p : 6 <= p)
    (local' next' : KeccakCols.t)
    (is_first_row is_transition : bool) :
  let local := M.map_mod local' in
  let next := M.map_mod next' in
  Pre.t local ->
  {{ eval_local 5 local next (Z.b2z is_first_row) (Z.b2z is_transition) 🔽
    tt,
    Post.t local next is_first_row is_transition
  }}.
Proof.
  intros * [].
  unfold eval_local.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply round_flags.implies.
  }
  intros H_eval_round_flags.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply preimage_a.implies.
  }
  intros H_eval_assert_preimage_a.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply preimage_next_preimage.implies.
  }
  intros H_eval_preimage_next_preimage.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply export_bool.implies.
  }
  intros H_eval_assert_export_bool.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply export_zero.implies.
  }
  intros H_eval_assert_export_zero.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply c_c_prime.implies.
  }
  intros [].
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_a_prime_c_c_prime.implies.
  }
  intros [].
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_c_prime.implies.
  }
  intros H_eval_assert_a_prime_c_prime.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime.implies.
  }
  intros H_eval_assert_a_prime_prime.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_bits_bools.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_bits_bools.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_limbs.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_prime_0_0_limbs.
  apply Run.Message; eapply Run.LetAccumulate. {
    Run.run.
  }
  intros _.
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
  constructor.
  { trivial. }
  { trivial. }
  { apply FirstRowsFrom_a.from_implies_to.
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
  }
  { assumption. }
  { assumption. }
  { assumption. }
  { assumption. }
Qed.

Module FunctionalSpec.
  Module Input.
    Record t : Set := {
      step : Z;
      export : bool;
      preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
      a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    }.

    Definition apply (input : t) (local : KeccakCols.t) : KeccakCols.t :=
      local
        <| KeccakCols.step_flags := {| Array.get r := Z.b2z (r =? input.(step)) |} |>
        <| KeccakCols.export := Z.b2z input.(export) |>
        <| KeccakCols.preimage := input.(preimage) |>
        <| KeccakCols.a := input.(a) |>.
  End Input.

  (*
    let get_xored_bit = |i| {
        let mut rc_bit_i = AB::Expr::ZERO;
        for r in 0..NUM_ROUNDS {
            let this_round = local.step_flags[r];
            let this_round_constant = AB::Expr::from_bool(rc_value_bit(r, i) != 0);
            rc_bit_i += this_round * this_round_constant;
        }

        rc_bit_i.xor(&local.a_prime_prime_0_0_bits[i].into())
    };
  *)
  (** Boolean version of the function above. *)
  Definition get_xored_bit {p} `{Prime p}
      (step : Z)
      (a_prime_prime_0_0_bits : Array.t bool 64)
      (i : Z) :
      bool :=
    xorb (rc_value_bit step i) a_prime_prime_0_0_bits.[i].

  Definition local_of_input {p} `{Prime p}
      (input : Input.t) :
      KeccakCols.t :=
    let step_flags : Array.t bool NUM_ROUNDS :=
      {|
        Array.get r := r =? input.(Input.step);
      |} in
    let c : Array.t (Array.t bool 64) 5 :=
      {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[0].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[1].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[2].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[3].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[4].[x] z
            ];
        |}
      |} in
    let c_prime : Array.t (Array.t bool 64) 5 :=
      {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              c.[x].[z];
              c.[(x + 4) mod 5].[z];
              c.[(x + 1) mod 5].[(z + 63) mod 64]
            ];
        |}
      |} in
    let a_prime : Array.t (Array.t (Array.t bool 64) 5) 5 :=
      {|
        Array.get y := {|
          Array.get x := {|
            Array.get z :=
              xorbs [
                Limbs.get_bit BITS_PER_LIMB input.(Input.a).[y].[x] z;
                c.[(x + 4) mod 5].[z];
                c.[(x + 1) mod 5].[(z + 63) mod 64]
              ];
            |}
        |}
      |} in
    let a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5 :=
      {|
        Array.get y := {|
          Array.get x :=
            Limbs.of_bools U64_LIMBS BITS_PER_LIMB {|
              Array.get z :=
                let andn :=
                  andb
                    (Impl_KeccakCols.b_of_a_prime a_prime ((x + 1) mod 5) y z)
                    (Impl_KeccakCols.b_of_a_prime a_prime ((x + 2) mod 5) y z) in
                Z.b2z (xorb andn (Impl_KeccakCols.b_of_a_prime a_prime x y z));
            |};
        |}
      |} in
    let a_prime_prime_0_0_bits : Array.t bool 64 :=
      {|
        Array.get z :=
          Limbs.get_bit BITS_PER_LIMB a_prime_prime.[0].[0] z;
      |} in
    let a_prime_prime_prime_0_0_limbs : Array.t Z U64_LIMBS :=
      Limbs.of_bools U64_LIMBS BITS_PER_LIMB {|
        Array.get z := Z.b2z (get_xored_bit input.(Input.step) a_prime_prime_0_0_bits z);
      |} in
    {|
      KeccakCols.step_flags := Array.map Z.b2z step_flags;
      KeccakCols.export := Z.b2z input.(Input.export);
      KeccakCols.preimage := input.(Input.preimage);
      KeccakCols.a := input.(Input.a);
      KeccakCols.c := Array.map (Array.map Z.b2z) c;
      KeccakCols.c_prime := Array.map (Array.map Z.b2z) c_prime;
      KeccakCols.a_prime := Array.map (Array.map (Array.map Z.b2z)) a_prime;
      KeccakCols.a_prime_prime := a_prime_prime;
      KeccakCols.a_prime_prime_0_0_bits := Array.map Z.b2z a_prime_prime_0_0_bits;
      KeccakCols.a_prime_prime_prime_0_0_limbs := a_prime_prime_prime_0_0_limbs;
    |}.

  Lemma implied_by_post {p} `{Prime p}
      (local' : KeccakCols.t)
      (input : Input.t) :
    let local := M.map_mod (Input.apply input local') in
    forall
      (H_pre : Pre.t local)
      (H_post : Post.t local),
    local = local_of_input input.
  Proof.
    intros.
    cbn in local.
    unfold local in *; clear local.
    destruct local'; cbn in *.
    unfold local_of_input; f_equal.
  Admitted.
End FunctionalSpec.
