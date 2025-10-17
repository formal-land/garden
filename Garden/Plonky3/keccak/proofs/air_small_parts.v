Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.
Require Import Garden.Plonky3.keccak.round_flags.

(*
  for y in 0..5 {
      for x in 0..5 {
          builder
              .when(first_step)
              .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                  local.preimage[y][x][limb] - local.a[y][x][limb]
              }));
      }
  }
*)
Module preimage_a.
  Definition eval {p} `{Prime p} (SQUARE_SIZE : Z) (local : KeccakCols.t) : M.t unit :=
    let first_step := local.(KeccakCols.step_flags).(Array.get) 0 in
    M.for_in_zero_to_n SQUARE_SIZE (fun y =>
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
      M.when first_step (
        M.assert_zeros (N := U64_LIMBS) {|
          Array.get limb :=
            local.(KeccakCols.preimage).[y].[x].[limb] -F local.(KeccakCols.a).[y].[x].[limb]
        |}
      )
    )).

  Module Spec.
    Definition t (local : KeccakCols.t) : Prop :=
      local.(KeccakCols.step_flags).[0] <> 0 ->
      local.(KeccakCols.preimage) =F local.(KeccakCols.a).
  End Spec.

  Lemma implies {p} `{Prime p} (local' : KeccakCols.t) :
    let local := M.map_mod local' in
    {{ eval 5 local 🔽
      tt,
      Spec.t local
    }}.
  Proof.
    intros.
    unfold eval.
    { eapply Run.Implies. {
        Run.run.
      }
      unfold Spec.t; cbn.
      FieldRewrite.run.
      hauto l: on.
    }
  Qed.
End preimage_a.

(*
  for y in 0..5 {
      for x in 0..5 {
          builder
              .when(not_final_step.clone())
              .when_transition()
              .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                  local.preimage[y][x][limb] - next.preimage[y][x][limb]
              }));
      }
  }
*)
Module preimage_next_preimage.
  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local next : KeccakCols.t)
      (is_transition : Z) :
      M.t unit :=
    let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
    let not_final_step := 1 -F final_step in
    M.for_in_zero_to_n SQUARE_SIZE (fun y =>
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
      M.when not_final_step (
      M.when is_transition (
        M.assert_zeros (N := U64_LIMBS) {|
          Array.get limb :=
            local.(KeccakCols.preimage).[y].[x].[limb] -F next.(KeccakCols.preimage).[y].[x].[limb]
        |}
      )
    ))).

  Lemma implies {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local next : KeccakCols.t)
      (is_transition : bool) :
      let local := M.map_mod local in
      let next := M.map_mod next in
      let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
      let not_final_step := 1 -F final_step in
      {{ eval SQUARE_SIZE local next (Z.b2z is_transition) 🔽
        tt,
        if is_transition then
          not_final_step <> 0 ->
          forall (y x limb : Z),
          0 <= y < SQUARE_SIZE ->
          0 <= x < SQUARE_SIZE ->
          0 <= limb < U64_LIMBS ->
          KeccakCols.get_preimage local x y limb =
          KeccakCols.get_preimage next x y limb
        else
          True
      }}.
  Proof.
    intros.
    unfold eval.
    unfold not_final_step, final_step in *.
    destruct is_transition.
    { eapply Run.Implies. {
        Run.run.
      }
      cbn.
      rewrite_db field_rewrite.
      hauto l: on.
    }
    { eapply Run.Implies. {
        Run.run.
      }
      easy.
    }
  Qed.
End preimage_next_preimage.

(*
  builder.assert_bool(local.export);
*)
Module export_bool.
  Definition eval {p} `{Prime p}
      (local : KeccakCols.t) :
      M.t unit :=
    M.assert_bool local.(KeccakCols.export). 

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    {{
      eval local 🔽
      tt,
      IsBool.t local.(KeccakCols.export)
    }}.
  Proof.
    intros.
    apply Run.AssertBool.
  Qed.
End export_bool.

(*
  builder
    .when(not_final_step.clone())
    .assert_zero(local.export);
*)
Module export_zero.
  Definition eval {p} `{Prime p}
      (local : KeccakCols.t) :
      M.t unit :=
    let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
    let not_final_step := 1 -F final_step in
    M.when not_final_step (
      M.assert_zero local.(KeccakCols.export)
    ).

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
      let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
      let not_final_step := 1 -F final_step in
      {{ eval local 🔽
        tt,
        not_final_step <> 0 ->
        local.(KeccakCols.export) = 0
      }}.
  Proof.
    intros.
    unfold eval.
    unfold not_final_step, final_step in *.
    { eapply Run.Implies. {
        Run.run.
      }
      tauto.
    }
  Qed.
End export_zero.

(*
  for x in 0..5 {
      builder.assert_bools(local.c[x]);
      builder.assert_zeros::<64, _>(array::from_fn(|z| {
          let xor = local.c[x][z].into().xor3(
              &local.c[(x + 4) % 5][z].into(),
              &local.c[(x + 1) % 5][(z + 63) % 64].into(),
          );
          local.c_prime[x][z] - xor
      }));
  }
*)
Module c_c_prime.
  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) :
      M.t unit :=
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
      let* _ := M.assert_bools (local.(KeccakCols.c).(Array.get) x) in
      M.assert_zeros (N := 64) {|
        Array.get z :=
          let xor :=
            xor3
              (local.(KeccakCols.c).[x].[z])
              (local.(KeccakCols.c).[(x + 4) mod SQUARE_SIZE].[z])
              (local.(KeccakCols.c).[(x + 1) mod SQUARE_SIZE].[(z + 63) mod 64]) in
          local.(KeccakCols.c_prime).[x].[z] -F xor
      |}
    ).

  Module Valid.
    Record t {p} `{Prime p} (SQUARE_SIZE : Z) (local : KeccakCols.t) : Prop := {
      c_c_prime_eq (x z : Z) :
        0 <= x < SQUARE_SIZE ->
        0 <= z < 64 ->
        KeccakCols.get_c_prime local x z =
        M.xor3
          (KeccakCols.get_c local x z)
          (KeccakCols.get_c local ((x + 4) mod SQUARE_SIZE) z)
          (KeccakCols.get_c local ((x + 1) mod SQUARE_SIZE) ((z + 63) mod 64));
      c_bools (x z : Z) :
        0 <= x < SQUARE_SIZE ->
        0 <= z < 64 ->
        KeccakCols.get_c local x z =
        Z.b2z (KeccakCols.Bool.get_c local x z)
    }.
  End Valid.

  Lemma implies {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local' : KeccakCols.t) :
    let local := M.map_mod local' in
    {{ eval SQUARE_SIZE local 🔽
      tt,
      Valid.t SQUARE_SIZE local
    }}.
  Proof.
    intros.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    cbn; rewrite_db field_rewrite.
    unfold M.xor3; setoid_rewrite M.from_xor_eq.
    intros; constructor; cbn; intros.
    { hauto l: on. }
    { sauto lq: on rew: off. }
  Qed.
End c_c_prime.

(*
  for y in 0..5 {
      for x in 0..5 {
          let get_bit = |z| {
              Into::<AB::Expr>::into(local.a_prime[y][x][z]).xor3(
                  &Into::<AB::Expr>::into(local.c[x][z]),
                  &Into::<AB::Expr>::into(local.c_prime[x][z]),
              )
          };

          // Check that all entries of A'[y][x] are boolean.
          builder.assert_bools(local.a_prime[y][x]);

          builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
              let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                  .rev()
                  .fold(AB::Expr::ZERO, |acc, z| {
                      // Check to ensure all entries of A' are bools.
                      acc.double() + get_bit(z)
                  });
              computed_limb - local.a[y][x][limb]
          }));
      }
  }
*)
Module a_a_prime_c_c_prime.
  Definition get_bit {p} `{Prime p}
      (local : KeccakCols.t) (y x : Z)
      (z : Z) :
      Z :=
    M.xor3
      local.(KeccakCols.a_prime).[y].[x].[z]
      local.(KeccakCols.c).[x].[z]
      local.(KeccakCols.c_prime).[x].[z].

  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) :
      M.t unit :=
      M.for_in_zero_to_n SQUARE_SIZE (fun y =>
      M.for_in_zero_to_n SQUARE_SIZE (fun x =>
        let* _ := M.assert_bools local.(KeccakCols.a_prime).[y].[x] in

        M.assert_zeros (N := U64_LIMBS) {|
          Array.get limb :=
            let computed_limb : Z :=
              let l : list nat :=
                List.rev (
                  List.seq
                    (Z.to_nat (limb * BITS_PER_LIMB))%Z
                    (Z.to_nat BITS_PER_LIMB)
                ) in
              Lists.List.fold_left (fun acc (z : nat) =>
                let z : Z := Z.of_nat z in
                (2 *F acc) +F
                get_bit local y x z
              ) l 0 in
            computed_limb -F local.(KeccakCols.a).[y].[x].[limb]
        |}
      )).

  Module Valid.
    Record t {p} `{Prime p} (SQUARE_SIZE : Z) (local : KeccakCols.t) : Prop := {
      a_prime_bools (x y z : Z) :
        0 <= x < SQUARE_SIZE ->
        0 <= y < SQUARE_SIZE ->
        0 <= z < 64 ->
        KeccakCols.get_a_prime local x y z =
        Z.b2z (KeccakCols.Bool.get_a_prime local x y z);
      a_a_prime_c_c_prime_eq (x y limb : Z) :
        0 <= x < SQUARE_SIZE ->
        0 <= y < SQUARE_SIZE ->
        0 <= limb < U64_LIMBS ->
        let a' : Array.t Z U64_LIMBS :=
          Limbs.of_bools U64_LIMBS BITS_PER_LIMB {| Array.get z := get_bit local y x z; |} in
        KeccakCols.get_a local x y limb =
        UnOp.from a'.[limb]
    }.
  End Valid.

  Lemma implies {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local' : KeccakCols.t) :
      let local := M.map_mod local' in
    {{ eval SQUARE_SIZE local 🔽
      tt,
      Valid.t SQUARE_SIZE local
    }}.
  Proof.
    intros.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Limbs.of_bools; cbn; rewrite_db field_rewrite.
    intros H_run; constructor.
    { intros x y z H_x H_y H_z.
      unfold KeccakCols.Bool.get_a_prime; cbn.
      hauto lq: on rew: off.
    }
    { intros x y limb H_x H_y H_limb.
      unfold get_bit in *.
      cbn in *.
      pose proof (H_run y H_y x H_x) as [_ H_run_limb].
      now rewrite (H_run_limb limb H_limb).
    }
  Qed.
End a_a_prime_c_c_prime.

(*
  for x in 0..5 {
      let four = AB::Expr::TWO.double();
      builder.assert_zeros::<64, _>(array::from_fn(|z| {
          let sum: AB::Expr = (0..5).map(|y| local.a_prime[y][x][z].into()).sum();
          let diff = sum - local.c_prime[x][z];
          diff.clone() * (diff.clone() - AB::Expr::TWO) * (diff - four.clone())
      }));
  }
*)
Module a_prime_c_prime.
  Fixpoint get_sum {p} `{Prime p} (l : list Z) : Z :=
    match l with
    | [] => 0
    | [z] => z
    | z :: l => z +F get_sum l
    end.

  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) :
      M.t unit :=
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
      let four : Z := 4 in
      M.assert_zeros (N := 64) {|
        Array.get z :=
          let sum : Z :=
            get_sum (
              List.map
                (fun y => local.(KeccakCols.a_prime).[Z.of_nat y].[x].[z])
                (List.seq 0 (Z.to_nat SQUARE_SIZE))
            ) in
          let diff := sum -F local.(KeccakCols.c_prime).[x].[z] in
          (diff *F (diff -F 2)) *F (diff -F four)
        |}
      ).

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    let SQUARE_SIZE := 5 in
    {{ eval SQUARE_SIZE local 🔽
      tt,
      forall (x z : Z),
      0 <= x < SQUARE_SIZE ->
      0 <= z < 64 ->
      let diff :=
        let sum :=
          get_sum (
            List.map
              (fun y => KeccakCols.get_a_prime local x (Z.of_nat y) z)
              (List.seq 0 (Z.to_nat SQUARE_SIZE))
          ) in
        sum -F local.(KeccakCols.c_prime).[x].[z] in
      (diff *F (diff -F 2)) *F (diff -F 4) =
      0
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    sauto.
  Qed.
End a_prime_c_prime.

(*
  for y in 0..5 {
      for x in 0..5 {
          let get_bit = |z| {
              let andn = local
                  .b((x + 1) % 5, y, z)
                  .into()
                  .andn(&local.b((x + 2) % 5, y, z).into());
              andn.xor(&local.b(x, y, z).into())
          };
          builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
              let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                  .rev()
                  .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_bit(z));
              computed_limb - local.a_prime_prime[y][x][limb]
          }));
      }
  }
*)
Module a_prime_prime.
  Definition get_bit {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) (y x : Z)
      (z : Z) :
      Z :=
    let andn :=
      M.andn
        (Impl_KeccakCols.b local ((x + 1) mod SQUARE_SIZE) y z)
        (Impl_KeccakCols.b local ((x + 2) mod SQUARE_SIZE) y z) in
    M.xor andn (Impl_KeccakCols.b local x y z).

  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) :
      M.t unit :=
    M.for_in_zero_to_n SQUARE_SIZE (fun y =>
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
      M.assert_zeros (N := U64_LIMBS) {|
        Array.get limb :=
          let computed_limb : Z :=
            let l : list nat :=
              List.rev (
                List.seq
                  (Z.to_nat (limb * BITS_PER_LIMB))
                  (Z.to_nat BITS_PER_LIMB)
              ) in
            Lists.List.fold_left (fun acc (z : nat) =>
              let z : Z := Z.of_nat z in
              (2 *F acc) +F
              get_bit SQUARE_SIZE local y x z
            ) l 0 in
          computed_limb -F local.(KeccakCols.a_prime_prime).[y].[x].[limb]
        |}
      )).

  Module Post.
    Definition t {p} `{Prime p} (SQUARE_SIZE : Z) (local : KeccakCols.t) : Prop :=
      forall (y x : Z),
      0 <= y < SQUARE_SIZE ->
      0 <= x < SQUARE_SIZE ->
      let a_prime_prime' : Array.t Z U64_LIMBS :=
        Limbs.of_bools U64_LIMBS BITS_PER_LIMB
          {| Array.get z := get_bit SQUARE_SIZE local y x z; |} in
      forall (limb : Z),
      0 <= limb < U64_LIMBS ->
      KeccakCols.get_a_prime_prime local x y limb =
      UnOp.from a_prime_prime'.[limb].
  End Post.

  Lemma implies {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    {{ eval SQUARE_SIZE local 🔽
      tt,
      Post.t SQUARE_SIZE local
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Post.t.
    cbn; rewrite_db field_rewrite.
    intros H_run.
    intros y x H_y H_x limb H_limb.
    now rewrite (H_run y H_y x H_x limb H_limb).
  Qed.
End a_prime_prime.

(*
  builder.assert_bools(local.a_prime_prime_0_0_bits);
*)
Module a_prime_prime_0_0_bits_bools.
  Definition eval {p} `{Prime p}
      (local : KeccakCols.t) :
      M.t unit :=
    M.assert_bools local.(KeccakCols.a_prime_prime_0_0_bits).

  Module Post.
    Definition t {p} `{Prime p} (local : KeccakCols.t) : Prop :=
      forall (z : Z),
      0 <= z < 64 ->
      IsBool.t local.(KeccakCols.a_prime_prime_0_0_bits).[z].
  End Post.

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    {{ eval local 🔽
      tt,
      Post.t local
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Post.t.
    sfirstorder.
  Qed.
End a_prime_prime_0_0_bits_bools.

(*
  builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
      let computed_a_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
          ..(limb + 1) * BITS_PER_LIMB)
          .rev()
          .fold(AB::Expr::ZERO, |acc, z| {
              acc.double() + local.a_prime_prime_0_0_bits[z]
          });
      computed_a_prime_prime_0_0_limb - local.a_prime_prime[0][0][limb]
  }));
*)
Module a_prime_prime_0_0_limbs.
  Definition eval {p} `{Prime p}
      (local : KeccakCols.t) :
      M.t unit :=
    M.assert_zeros (N := U64_LIMBS) {|
      Array.get limb :=
        let computed_a_prime_prime_0_0_limb : Z :=
          let l : list nat :=
            List.rev (
              List.seq
                (Z.to_nat (limb * BITS_PER_LIMB))
                (Z.to_nat BITS_PER_LIMB)
              ) in
          Lists.List.fold_left (fun acc (z : nat) =>
            let z : Z := Z.of_nat z in
            (2 *F acc) +F local.(KeccakCols.a_prime_prime_0_0_bits).[z]
          ) l 0 in
        computed_a_prime_prime_0_0_limb -F
          local.(KeccakCols.a_prime_prime).[0].[0].[limb]
    |}.

  Module Post.
    Definition t {p} `{Prime p} (local : KeccakCols.t) : Prop :=
      forall (limb : Z),
      0 <= limb < U64_LIMBS ->
      UnOp.from local.(KeccakCols.a_prime_prime).[0].[0].[limb] =
      UnOp.from (Limbs.of_bools U64_LIMBS BITS_PER_LIMB local.(KeccakCols.a_prime_prime_0_0_bits)).[limb].
  End Post.

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    {{ eval local 🔽
      tt,
      Post.t local
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Post.t.
    cbn.
    hauto l: on.
  Qed.
End a_prime_prime_0_0_limbs.

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
Definition get_xored_bit {p} `{Prime p}
    (local : KeccakCols.t)
    (i : Z) :
    Z :=
  let rc_bit_i : Z :=
    Lists.List.fold_left (fun acc r =>
      let this_round := local.(KeccakCols.step_flags).[r] in
      let this_round_constant :=
        Z.b2z (rc_value_bit r i) in
      acc +F (this_round *F this_round_constant)
    )
    (List.map Z.of_nat (List.seq 0 (Z.to_nat NUM_ROUNDS))) 0 in
  M.xor rc_bit_i local.(KeccakCols.a_prime_prime_0_0_bits).[i].

(*
  builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
      let computed_a_prime_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
          ..(limb + 1) * BITS_PER_LIMB)
          .rev()
          .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_xored_bit(z));
      computed_a_prime_prime_prime_0_0_limb - local.a_prime_prime_prime_0_0_limbs[limb]
  }));
*)
Module a_prime_prime_prime_0_0_limbs.
  Definition eval {p} `{Prime p}
      (local : KeccakCols.t) :
      M.t unit :=
    M.assert_zeros (N := U64_LIMBS) {|
      Array.get limb :=
        let computed_a_prime_prime_prime_0_0_limb : Z :=
          let l : list nat :=
            List.rev (
              List.seq
                (Z.to_nat (limb * BITS_PER_LIMB))
                (Z.to_nat BITS_PER_LIMB)
              ) in
          Lists.List.fold_left (fun acc (z : nat) =>
            let z : Z := Z.of_nat z in
            (2 *F acc) +F get_xored_bit local z
          ) l 0 in
        computed_a_prime_prime_prime_0_0_limb -F
          local.(KeccakCols.a_prime_prime_prime_0_0_limbs).[limb]
    |}.

  Module Post.
    Definition t {p} `{Prime p} (local : KeccakCols.t) : Prop :=
      forall (limb : Z),
      0 <= limb < U64_LIMBS ->
      UnOp.from local.(KeccakCols.a_prime_prime_prime_0_0_limbs).[limb] =
      UnOp.from (Limbs.of_bools U64_LIMBS BITS_PER_LIMB {| Array.get z := get_xored_bit local z; |}).[limb].
  End Post.

  Lemma implies {p} `{Prime p}
      (local : KeccakCols.t) :
      let local := M.map_mod local in
    {{ eval local 🔽
      tt,
      Post.t local
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Post.t.
    hauto l: on.
  Qed.
End a_prime_prime_prime_0_0_limbs.

(*
  for x in 0..5 {
      for y in 0..5 {
          builder
              .when_transition()
              .when(not_final_step.clone())
              .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                  local.a_prime_prime_prime(y, x, limb) - next.a[y][x][limb]
              }));
      }
  }
*)
Module a_prime_prime_prime_next_a.
  Definition eval {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local next : KeccakCols.t)
      (is_transition : Z) :
      M.t unit :=
    let final_step := local.(KeccakCols.step_flags).[NUM_ROUNDS - 1] in
    let not_final_step := 1 -F final_step in
    M.for_in_zero_to_n SQUARE_SIZE (fun x =>
    M.for_in_zero_to_n SQUARE_SIZE (fun y =>
      M.when is_transition (
      M.when not_final_step (
        M.assert_zeros (N := U64_LIMBS) {|
          Array.get limb :=
            Impl_KeccakCols.a_prime_prime_prime local y x limb -F
              next.(KeccakCols.a).[y].[x].[limb]
        |}
      ))
    )).

  Module Post.
    Definition t {p} `{Prime p} (SQUARE_SIZE : Z) (local next : KeccakCols.t) : Prop :=
      forall (y x : Z),
      0 <= y < SQUARE_SIZE ->
      0 <= x < SQUARE_SIZE ->
      forall (limb : Z),
      0 <= limb < U64_LIMBS ->
      UnOp.from (Impl_KeccakCols.a_prime_prime_prime local y x limb) =
      UnOp.from (next.(KeccakCols.a).[y].[x].[limb]).
  End Post.

  Lemma implies {p} `{Prime p}
      (SQUARE_SIZE : Z)
      (local next : KeccakCols.t)
      (is_transition : bool) :
    let local := M.map_mod local in
    let next := M.map_mod next in
    let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
    let not_final_step := 1 -F final_step in
    not_final_step <> 0 ->
    {{ eval SQUARE_SIZE local next (Z.b2z is_transition) 🔽
      tt,
      if is_transition then
        Post.t SQUARE_SIZE local next
      else
        True
    }}.
  Proof.
    intros * H_not_final_step.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    unfold Post.t.
    destruct is_transition.
    { hauto lq: on rew: off. }
    { easy. }
  Qed.
End a_prime_prime_prime_next_a.
