Require Import Plonky3.M.
Require Import Plonky3.MExpr.
Require Import Plonky3.keccak.air.
Require Import Plonky3.keccak.columns.
Require Import Plonky3.keccak.constants.
Require Import Plonky3.keccak.round_flags.

Module FirstRowsFrom_a.
  Module From.
    Record t
        (local : KeccakCols.t)
        (a : Array.t (Array.t (Array.t bool 64) 5) 5) :
        Prop := {
      a_prime_bools : IsBool.t local.(KeccakCols.a_prime);
      c_bools : IsBool.t local.(KeccakCols.c);
      c_c_prime :
        forall x, 0 <= x < 5 ->
        forall z, 0 <= z < 64 ->
        local.(KeccakCols.c_prime).[x].[z] =
        Z.b2z (xorbs [
          Z.odd (local.(KeccakCols.c).[x].[z]);
          Z.odd (local.(KeccakCols.c).[(x + 4) mod 5].[z]);
          Z.odd (local.(KeccakCols.c).[(x + 1) mod 5].[(z + 63) mod 64])
        ]);
      a_a_prime_c_c_prime (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        a.[y].[x].[z] =
        xorbs [
          Z.odd (local.(KeccakCols.a_prime).[y].[x].[z]);
          Z.odd (local.(KeccakCols.c).[x].[z]);
          Z.odd (local.(KeccakCols.c_prime).[x].[z])
        ];
      a_prime_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        local.(KeccakCols.c_prime).[x].[z] =
        Z.b2z (xorbs [
          Z.odd (local.(KeccakCols.a_prime).[0].[x].[z]);
          Z.odd (local.(KeccakCols.a_prime).[1].[x].[z]);
          Z.odd (local.(KeccakCols.a_prime).[2].[x].[z]);
          Z.odd (local.(KeccakCols.a_prime).[3].[x].[z]);
          Z.odd (local.(KeccakCols.a_prime).[4].[x].[z])
        ]);
    }.
  End From.

  Module To.
    Record t
        (local : KeccakCols.t)
        (a : Array.t (Array.t (Array.t bool 64) 5) 5) :
        Prop := {
      a_c (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        local.(KeccakCols.c).[x].[z] =
        Z.b2z (xorbs [
          a.[0].[x].[z];
          a.[1].[x].[z];
          a.[2].[x].[z];
          a.[3].[x].[z];
          a.[4].[x].[z]
        ]);
      c_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        local.(KeccakCols.c_prime).[x].[z] =
        Z.b2z (xorbs [
          Z.odd (local.(KeccakCols.c).[x].[z]);
          Z.odd (local.(KeccakCols.c).[(x + 4) mod 5].[z]);
          Z.odd (local.(KeccakCols.c).[(x + 1) mod 5].[(z + 63) mod 64])
        ]);
      a_a_prime_c (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        local.(KeccakCols.a_prime).[y].[x].[z] =
        Z.b2z (xorbs [
          a.[y].[x].[z];
          Z.odd (local.(KeccakCols.c).[(x + 4) mod 5].[z]);
          Z.odd (local.(KeccakCols.c).[(x + 1) mod 5].[(z + 63) mod 64])
        ]);
    }.
  End To.

  (** The lemma explains why the calculation for the first rows is deterministic. *)
  Lemma from_implies_to (local : KeccakCols.t) (a : Array.t (Array.t (Array.t bool 64) 5) 5) :
    From.t local a ->
    To.t local a.
  Proof.
    intros []; constructor; intros; cbn in *.
    { repeat rewrite a_a_prime_c_c_prime by lia.
      repeat rewrite a_prime_c_prime by lia.
      rewrite c_bools at 1 by lia.
      repeat rewrite odd_b2z_eq.
      repeat destruct (Z.odd _); reflexivity.
    }
    { hauto l: on. }
    { rewrite a_prime_bools by lia.
      rewrite a_a_prime_c_c_prime by lia.
      rewrite c_c_prime by lia.
      repeat rewrite odd_b2z_eq.
      repeat destruct (Z.odd _); reflexivity.
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
    (H_a_prime_bools : IsBool.t local.(KeccakCols.a_prime))
    (H_c_prime_bools : IsBool.t local.(KeccakCols.c_prime))
    (H_sum_diff :
      let diff :=
        let sum :=
          a_prime_c_prime.get_sum [
            local.(KeccakCols.a_prime).[0].[x].[z];
            local.(KeccakCols.a_prime).[1].[x].[z];
            local.(KeccakCols.a_prime).[2].[x].[z];
            local.(KeccakCols.a_prime).[3].[x].[z];
            local.(KeccakCols.a_prime).[4].[x].[z]
          ] in
        sum -F (local.(KeccakCols.c_prime).[x].[z]) in
      diff *F (diff -F 2) *F (diff -F 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  local.(KeccakCols.c_prime).[x].[z] =
  Z.b2z (xorbs [
    Z.odd (local.(KeccakCols.a_prime).[0].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[1].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[2].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[3].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[4].[x].[z])
  ]).
Proof.
  intros.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff |- * by lia)
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
    (H_a_prime_bools : IsBool.t local.(KeccakCols.a_prime))
    (H_c_prime_bools : IsBool.t local.(KeccakCols.c_prime))
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            local.(KeccakCols.a_prime).[0].[x].[z];
            local.(KeccakCols.a_prime).[1].[x].[z];
            local.(KeccakCols.a_prime).[2].[x].[z];
            local.(KeccakCols.a_prime).[3].[x].[z];
            local.(KeccakCols.a_prime).[4].[x].[z]
          ] 0 in
        sum -F (local.(KeccakCols.c_prime).[x].[z]) in
      diff *F (diff -F 2) *F (diff -F 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  local.(KeccakCols.c_prime).[x].[z] =
  Z.b2z (xorbs [
    Z.odd (local.(KeccakCols.a_prime).[0].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[1].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[2].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[3].[x].[z]);
    Z.odd (local.(KeccakCols.a_prime).[4].[x].[z])
  ]).
Proof.
  intros.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff |- * by lia)
    );
    let b := fresh "b" in
    set (b := Z.odd _) in H_sum_diff;
    fold b;
    clearbody b
  ).
  destruct_all bool; cbv in H_sum_diff; cbv; congruence.
Qed.

Module Post.
  Record t {p} `{Prime p}
      (local next : KeccakCols.t)
      (is_first_row is_transition : bool) :
    Prop :=
  {
    round_flags : round_flags.Spec.t local next is_first_row is_transition;
    preimage_a : preimage_a.Spec.t local;
    preimage_next_preimage : preimage_next_preimage.Spec.t local next is_transition;
    to :
      forall a,
      a.Valid.t local a ->
      FirstRowsFrom_a.To.t local a;
    a_prime_is_bool : IsBool.t local.(KeccakCols.a_prime);
    a_prime_prime : a_prime_prime.Post.t local;
    a_prime_prime_0_0_bits_bools : a_prime_prime_0_0_bits_bools.Post.t local;
    a_prime_prime_0_0_limbs : a_prime_prime_0_0_limbs.Post.t local;
    a_prime_prime_prime_0_0_limbs : a_prime_prime_prime_0_0_limbs.Post.t local;
  }.
End Post.

Lemma eval_implies {p} `{Prime p} (H_p : 2 ^ BITS_PER_LIMB < p)
    (local' next' : KeccakCols.t)
    (is_first_row is_transition : bool) :
  let local := M.map_mod local' in
  let next := M.map_mod next' in
  {{ eval local next (Z.b2z is_first_row) (Z.b2z is_transition) 🔽
    tt,
    Post.t local next is_first_row is_transition
  }}.
Proof.
  intros.
  unfold eval.
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
    apply a_a_prime_c_c_prime.implies; assumption.
  }
  intros [].
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_c_prime.implies.
  }
  intros H_eval_assert_a_prime_c_prime.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime.implies; assumption.
  }
  intros H_eval_assert_a_prime_prime.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_bits_bools.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_bits_bools.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_limbs.implies; assumption.
  }
  intros H_eval_assert_a_prime_prime_0_0_limbs.
  apply Run.Message; eapply Run.LetAccumulate. {
    apply a_prime_prime_prime_0_0_limbs.implies; assumption.
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
  assert (c_prime_bools : IsBool.t local.(KeccakCols.c_prime)). {
    cbn; intros x H_x z H_z.
    cbn in c_c_prime_eq.
    rewrite c_c_prime_eq by lia.
    apply M.xor3_is_bool; apply c_bools; lia.
  }
  constructor.
  { trivial. }
  { trivial. }
  { trivial. }
  { intros a H_a.
    pose proof (
      a_a_prime_c_c_prime_eq a H_a ltac:(assumption) ltac:(assumption)
    ) as H_a_a_prime_c_c_prime_eq; clear H_a_a_prime_c_c_prime_eq.
    apply FirstRowsFrom_a.from_implies_to.
    constructor; intros.
    { assumption. }
    { assumption. }
    { rewrite c_c_prime_eq by assumption.
      repeat (rewrite c_bools by lia; set (Z.odd _)).
      rewrite xor3_eq.
      reflexivity.
    }
    { now rewrite <- a_a_prime_c_c_prime_eq. }
    { apply xor_sum_diff_eq; trivial.
      { cbn in H_p; lia. }
      { apply H_eval_assert_a_prime_c_prime; lia. }
    }
  }
  { assumption. }
  { assumption. }
  { assumption. }
  { assumption. }
  { assumption. }
Qed.

Module ComputeKeccak.
  Definition compute_c (a : Array.t (Array.t (Array.t bool 64) 5) 5) :
      Array.t (Array.t bool 64) 5 :=
    {|
      Array.get x := {|
        Array.get z :=
          xorbs [
            a.[0].[x].[z];
            a.[1].[x].[z];
            a.[2].[x].[z];
            a.[3].[x].[z];
            a.[4].[x].[z]
          ];
      |}
    |}.

  Definition compute_c_prime (c : Array.t (Array.t bool 64) 5) :
      Array.t (Array.t bool 64) 5 :=
    {|
      Array.get x := {|
        Array.get z :=
          xorbs [
            c.[x].[z];
            c.[(x + 4) mod 5].[z];
            c.[(x + 1) mod 5].[(z + 63) mod 64]
          ];
      |}
    |}.

  Definition compute_a_prime
      (a : Array.t (Array.t (Array.t bool 64) 5) 5) 
      (c : Array.t (Array.t bool 64) 5) :
      Array.t (Array.t (Array.t bool 64) 5) 5 :=
    {|
      Array.get y := {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              a.[y].[x].[z];
              c.[(x + 4) mod 5].[z];
              c.[(x + 1) mod 5].[(z + 63) mod 64]
            ];
        |}
      |}
    |}.

  Definition compute_b (a_prime : Array.t (Array.t (Array.t bool 64) 5) 5) :
      Array.t (Array.t (Array.t bool 64) 5) 5 :=
    {|
      Array.get y := {|
        Array.get x := {|
          Array.get z :=
            let a := (x + 3 * y) mod 5 in
            let b := x in
            let rot := R.[a].[b] in
            a_prime.[b].[a].[(z + 64 - rot) mod 64];
        |}
      |}
    |}.

  Definition compute_a_prime_prime
      (b : Array.t (Array.t (Array.t bool 64) 5) 5) :
      Array.t (Array.t (Array.t bool 64) 5) 5 :=
    {|
      Array.get y := {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              andb
                (negb b.[y].[(x + 1) mod 5].[z])
                b.[y].[(x + 2) mod 5].[z];
              b.[y].[x].[z]
            ];
        |};
      |}
    |}.

  Definition compute_a_prime_prime_prime_0_0
      (a_prime_prime : Array.t (Array.t (Array.t bool 64) 5) 5)
      (round : Z) :
      Array.t bool 64 :=
    {|
      Array.get z :=
        xorbs [
          rc_value_bit round z;
          a_prime_prime.[0].[0].[z]
        ];
    |}.

  Definition compute_a_prime_prime_prime
      (a_prime_prime : Array.t (Array.t (Array.t bool 64) 5) 5)
      (a_prime_prime_prime_0_0 : Array.t bool 64) :
      Array.t (Array.t (Array.t bool 64) 5) 5 :=
    {|
      Array.get y := {|
        Array.get x := {|
          Array.get z :=
            if (y =? 0) && (x =? 0) then
              a_prime_prime_prime_0_0.[z]
            else
              a_prime_prime.[y].[x].[z]
        |}
      |}
    |}.
End ComputeKeccak.

Lemma post_implies_round_computation {p} `{Prime p}
    (local' next' : KeccakCols.t)
    (is_first_row is_transition : bool)
    (a : Array.t (Array.t (Array.t bool 64) 5) 5)
    (round : Z) :
  let local := M.map_mod local' in
  let next := M.map_mod next' in
  Post.t local next is_first_row is_transition ->
  a.Valid.t local a ->
  0 <= round < NUM_ROUNDS ->
  step_flags.Valid.t local round ->
  let c := ComputeKeccak.compute_c a in
  let c_prime := ComputeKeccak.compute_c_prime c in
  let a_prime := ComputeKeccak.compute_a_prime a c in
  let b := ComputeKeccak.compute_b a_prime in
  let a_prime_prime := ComputeKeccak.compute_a_prime_prime b in
  let a_prime_prime_prime_0_0 := ComputeKeccak.compute_a_prime_prime_prime_0_0 a_prime_prime round in
  (
    forall x, 0 <= x < 5 ->
    forall y, 0 <= y < 5 ->
    forall limb, 0 <= limb < U64_LIMBS ->
    Impl_KeccakCols.a_prime_prime_prime local y x limb =
    Limbs.of_bools BITS_PER_LIMB
      (Array.get (ComputeKeccak.compute_a_prime_prime_prime a_prime_prime a_prime_prime_prime_0_0).[y].[x])
      limb
  ).
Proof.
  intros * H_Post H_a H_round H_step_flags c c_prime a_prime b a_prime_prime a_prime_prime_prime_0_0.
  destruct H_Post, (to a H_a); clear to.
  assert (H_c :
    forall x, 0 <= x < 5 ->
    forall z, 0 <= z < 64 ->
    local.(KeccakCols.c).[x].[z] =
    Z.b2z (c.[x].[z])
  ). {
    intros.
    rewrite a_c by assumption.
    now repeat rewrite H_a by assumption.
  }
  assert (H_c_prime :
    forall x, 0 <= x < 5 ->
    forall z, 0 <= z < 64 ->
    local.(KeccakCols.c_prime).[x].[z] =
    Z.b2z (c_prime.[x].[z])
  ). {
    intros.
    rewrite c_c_prime by assumption.
    repeat rewrite H_c by lia.
    now repeat rewrite odd_b2z_eq.
  }
  assert (H_a_prime :
    forall x, 0 <= x < 5 ->
    forall y, 0 <= y < 5 ->
    forall z, 0 <= z < 64 ->
    local.(KeccakCols.a_prime).[y].[x].[z] =
    Z.b2z (a_prime.[y].[x].[z])
  ). {
    intros.
    rewrite a_a_prime_c by lia.
    repeat rewrite H_c by lia.
    now repeat rewrite odd_b2z_eq.
  }
  assert (H_b :
    forall x, 0 <= x < 5 ->
    forall y, 0 <= y < 5 ->
    forall z, 0 <= z < 64 ->
    Impl_KeccakCols.b local x y z =
    Z.b2z (b.[y].[x].[z])
  ). {
    intros.
    unfold Impl_KeccakCols.b, Impl_KeccakCols.b_of_a_prime.
    now rewrite H_a_prime by lia.
  }
  assert (H_a_prime_prime_bits :
    forall x, 0 <= x < 5 ->
    forall y, 0 <= y < 5 ->
    forall z, 0 <= z < 64 ->
    a_prime_prime.get_bit_bool local y x z =
    a_prime_prime.[y].[x].[z]
  ). {
    intros.
    unfold a_prime_prime.get_bit_bool.
    repeat rewrite H_b by lia.
    repeat rewrite odd_b2z_eq.
    reflexivity.
  }
  assert (H_a_prime_prime_0_0_bits :
    forall z, 0 <= z < 64 ->
    local.(KeccakCols.a_prime_prime_0_0_bits).[z] =
    Z.b2z (a_prime_prime.[0].[0].[z])
  ). {
    intros z H_z.
    unfold a_prime_prime_0_0_limbs.Post.t in a_prime_prime_0_0_limbs.
    unfold a_prime_prime.Post.t in a_prime_prime0.
    rewrite a_prime_prime_0_0_bits_bools by assumption; f_equal.
    rewrite <- H_a_prime_prime_bits by lia.
    generalize z H_z; clear z H_z.
    apply (Limbs.limbs_eq_implies_bools_eq U64_LIMBS BITS_PER_LIMB); intros.
    rewrite <- a_prime_prime0 by (assumption || lia).
    rewrite <- a_prime_prime_0_0_limbs by assumption.
    reflexivity.
  }
  assert (H_a_prime_prime_prime_0_0 :
    forall z, 0 <= z < 64 ->
    a_prime_prime_prime_0_0_limbs.get_xored_bit_bool local round z =
    a_prime_prime_prime_0_0.[z]
  ). {
    intros z H_z.
    unfold a_prime_prime_prime_0_0_limbs.get_xored_bit_bool.
    cbn - [xorb rc_value_bit a_prime_prime].
    cbn - [a_prime_prime] in H_a_prime_prime_0_0_bits.
    rewrite H_a_prime_prime_0_0_bits by assumption.
    rewrite odd_b2z_eq.
    reflexivity.
  }
  intros x H_x y H_y limb H_limb.
  unfold Impl_KeccakCols.a_prime_prime_prime, ComputeKeccak.compute_a_prime_prime_prime.
  unfold Array.get.
  destruct ((y =? 0) && (x =? 0)).
  { rewrite a_prime_prime_prime_0_0_limbs by eassumption.
    apply (Limbs.of_bools_eq U64_LIMBS BITS_PER_LIMB); intros.
    now apply H_a_prime_prime_prime_0_0.
  }
  { rewrite a_prime_prime0 by assumption.
    apply (Limbs.of_bools_eq U64_LIMBS BITS_PER_LIMB); intros.
    now apply H_a_prime_prime_bits.
  }
Qed.

(*
Module BoolArray.
  Definition to_bits (a : Array.t bool 64) : Array.t Z 64 :=
    Array.map Z.b2z a.

  Definition to_limbs {p} `{Prime p} (a : Array.t bool 64) : Array.t Z U64_LIMBS :=
    Limbs.of_bools U64_LIMBS BITS_PER_LIMB (to_bits a).
End BoolArray.

Module WithPreimage.
  Definition t {p} `{Prime p}
      (pre_image : Array.t (Array.t (Array.t bool 64) 5) 5)
      (local : KeccakCols.t) :
      Prop :=
    forall y, 0 <= y < 5 ->
    forall x, 0 <= x < 5 ->
    forall limb, 0 <= limb < U64_LIMBS ->
    (BoolArray.to_limbs pre_image.[y].[x]).[limb] =
    local.(KeccakCols.preimage).[y].[x].[limb].
End WithPreimage.

(* Module WithPreImages.
  Definition t {p} `{Prime p}
      (pre_images : list (Array.t (Array.t (Array.t bool 64) 5) 5))
      (matrix : list KeccakCols.t) :
      Prop :=
    forall i,
    0 <= i < Z.of_nat (List.length pre_images) ->
    WithPreimage.t
      (List.nth (Z.to_nat i) pre_images Default.default)
      (List.nth (Z.to_nat (24 * i)) matrix Default.default).
End WithPreImages. *)

Module MatrixSpec.
  Fixpoint t {p} `{Prime p}
      (matrix : list KeccakCols.t)
      (dummy : KeccakCols.t)
      (is_first_row : bool) :
      Prop :=
    match matrix with
    | [] => is_first_row = false
    | local :: matrix =>
      let '(is_transition, next) :=
        match matrix with
        | [] => (false, dummy)
        | next :: _ => (true, next)
        end in
      Post.t local next is_first_row is_transition /\
      t matrix next false
    end.

  (* Lemma implies {p} `{Prime p}
      (matrix' : list KeccakCols.t)
      (dummy' : KeccakCols.t)
      (pre_images : list (Array.t (Array.t (Array.t bool 64) 5) 5)) :
    let matrix := List.map M.map_mod matrix' in
    let dummy := M.map_mod dummy' in
    MatrixSpec.t matrix dummy true ->

    {{ eval_local local next (Z.b2z is_first_row) (Z.b2z is_transition) 🔽
      tt,
      MatrixSpec.t matrix dummy is_first_row
    }}.
  Proof.
    induction matrix; intros; cbn in *. *)
End MatrixSpec.

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
      (local' next' : KeccakCols.t)
      (is_first_row is_transition : bool)
      (input : Input.t) :
    let local := M.map_mod (Input.apply input local') in
    let next := M.map_mod (Input.apply input next') in
    forall
      (H_post : Post.t local next is_first_row is_transition),
    local = local_of_input input.
  Proof.
    intros.
    cbn in local.
    unfold local in *; clear local.
    destruct local'; cbn in *.
    unfold local_of_input; f_equal.
  Admitted.
End FunctionalSpec.
*)
