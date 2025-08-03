Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

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
Definition eval_preimage_a {p} `{Prime p}
    (first_step : Z)
    (preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5) :
    M.t unit :=
  M.for_in_zero_to_n 5 (fun y =>
  M.for_in_zero_to_n 5 (fun x =>
    M.when first_step (
      M.assert_zeros (N := U64_LIMBS) {|
        Array.get limb :=
          BinOp.sub
            (Array.get (Array.get (Array.get preimage y) x) limb)
            (Array.get (Array.get (Array.get a y) x) limb)
      |}
    )
  )).

Lemma eval_preimage_a_implies {p} `{Prime p}
    (first_step : Z)
    (preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5) :
    let first_step := M.map_mod first_step in
    let preimage := M.map_mod preimage in
    let a := M.map_mod a in
    first_step <> 0 ->
    {{ eval_preimage_a first_step preimage a 🔽
      tt,
      forall (y x limb : Z),
      0 <= y < 5 ->
      0 <= x < 5 ->
      0 <= limb < U64_LIMBS ->
      ((preimage.(Array.get) y).(Array.get) x).(Array.get) limb =
      ((a.(Array.get) y).(Array.get) x).(Array.get) limb
    }}.
Proof.
  intros * H_not_first_step.
  eapply Run.Implies. {
    eapply Run.ForInZeroToN. {
      intros.
      eapply Run.ForInZeroToN. {
        intros.
        unfold M.when.
        destruct (_ =? 0) eqn:H_first_step_eq; [lia|].
        apply Run.AssertZerosFromFnSub.
      }
    }
  }
  hauto l: on drew: off.
Qed.

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
Definition eval_preimage_next_preimage {p} `{Prime p}
    (not_final_step : Z)
    (is_transition : bool)
    (local_preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (next_preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5) :
    M.t unit :=
  M.for_in_zero_to_n 5 (fun y =>
  M.for_in_zero_to_n 5 (fun x =>
    M.when not_final_step (
    M.when_bool is_transition (
      M.assert_zeros (N := U64_LIMBS) {|
        Array.get limb :=
          BinOp.sub
            (Array.get (Array.get (Array.get local_preimage y) x) limb)
            (Array.get (Array.get (Array.get next_preimage y) x) limb)
      |}
    )
  ))).

Lemma eval_preimage_next_preimage_transition_implies {p} `{Prime p}
    (not_final_step : Z)
    (local_preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (next_preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5) :
    let not_final_step := M.map_mod not_final_step in
    let local_preimage := M.map_mod local_preimage in
    let next_preimage := M.map_mod next_preimage in
    not_final_step <> 0 ->
    {{ eval_preimage_next_preimage not_final_step true local_preimage next_preimage 🔽
      tt,
      forall (y x limb : Z),
      0 <= y < 5 ->
      0 <= x < 5 ->
      0 <= limb < U64_LIMBS ->
      ((local_preimage.(Array.get) y).(Array.get) x).(Array.get) limb =
      ((next_preimage.(Array.get) y).(Array.get) x).(Array.get) limb
    }}.
Proof.
  intros * H_not_final_step.
  eapply Run.Implies. {
    eapply Run.ForInZeroToN. {
      intros.
      eapply Run.ForInZeroToN. {
        intros.
        unfold M.when.
        destruct (_ =? 0) eqn:H_not_final_step_eq; [lia|].
        apply Run.AssertZerosFromFnSub.
      }
    }
  }
  hauto l: on drew: off.
Qed.

(* builder.assert_bool(local.export); *)
Definition eval_assert_export_bool {p} `{Prime p}
    (export : Z) :
    M.t unit :=
  M.assert_bool export. 

Lemma eval_assert_export_bool_implies {p} `{Prime p}
    (export : Z) :
    let export := M.map_mod export in
  {{
    eval_assert_export_bool export 🔽
    tt,
    exists (b : bool), export = Z.b2z b
  }}.
Proof.
  intros.
  unfold eval_assert_export_bool.
  apply Run.AssertBool.
Qed.

(*
  builder
    .when(not_final_step.clone())
    .assert_zero(local.export);
*)
Definition eval_assert_export_zero {p} `{Prime p}
    (not_final_step : Z)
    (export : Z) :
    M.t unit :=
  M.when not_final_step (
    M.assert_zero export
  ).

Lemma eval_assert_export_zero_implies {p} `{Prime p}
    (not_final_step : Z)
    (export : Z) :
    let not_final_step := M.map_mod not_final_step in
    let export := M.map_mod export in
    not_final_step <> 0 ->
    {{ eval_assert_export_zero not_final_step export 🔽
      tt,
      export = 0
    }}.
Proof.
  intros.
  unfold eval_assert_export_zero.
  eapply Run.Implies. {
    unfold M.when.
    destruct (_ =? 0) eqn:H_not_final_step_eq; [lia|].
    apply Run.Equal.
  }
  easy.
Qed.

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
Definition eval_assert_c_c_prime {p} `{Prime p}
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    M.t unit :=
  M.for_in_zero_to_n 5 (fun x =>
    let* _ := M.assert_bools (c.(Array.get) x) in
    M.assert_zeros (N := 64) {|
      Array.get z :=
        let xor :=
          xor3
            ((c.(Array.get) x).(Array.get) z)
            ((c.(Array.get) ((x + 4) mod 5)).(Array.get) z)
            ((c.(Array.get) ((x + 1) mod 5)).(Array.get) ((z + 63) mod 64))
        in
        BinOp.sub
          ((c_prime.(Array.get) x).(Array.get) z)
          xor
    |}
  ).

Lemma eval_assert_c_c_prime_implies_c_bools {p} `{Prime p}
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    let c := M.map_mod c in
    let c_prime := M.map_mod c_prime in
    {{ eval_assert_c_c_prime c c_prime 🔽
      tt,
      forall (x z : Z),
      0 <= x < 5 ->
      0 <= z < 64 ->
      exists (b : bool),
      ((c.(Array.get) x).(Array.get) z) = Z.b2z b
    }}.
Proof.
  intros.
  unfold eval_assert_c_c_prime.
  eapply Run.Implies. {
    repeat (econstructor || intros).
  }
  hauto l: on.
Qed.

Lemma eval_assert_c_c_prime_implies_c_c_prime {p} `{Prime p}
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    let c := M.map_mod c in
    let c_prime := M.map_mod c_prime in
    {{ eval_assert_c_c_prime c c_prime 🔽
      tt,
      forall (x z : Z),
      0 <= x < 5 ->
      0 <= z < 64 ->
      (c_prime.(Array.get) x).(Array.get) z =
      M.xor3
        ((c.(Array.get) x).(Array.get) z)
        ((c.(Array.get) ((x + 4) mod 5)).(Array.get) z)
        ((c.(Array.get) ((x + 1) mod 5)).(Array.get) ((z + 63) mod 64))
    }}.
Proof.
  intros.
  unfold eval_assert_c_c_prime.
  eapply Run.Implies. {
    eapply Run.ForInZeroToN. {
      intros.
      eapply Run.Let. {
        repeat (econstructor || intros).
      }
      intros.
      eapply Run.AssertZerosFromFnSub.
    }
  }
  hauto l: on.
Qed.

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
Definition eval_assert_a_a_prime_c_c_prime {p} `{Prime p}
    (a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (a_prime : Array.t (Array.t (Array.t Z 64) 5) 5)
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    M.t unit :=
    M.for_in_zero_to_n 5 (fun y =>
    M.for_in_zero_to_n 5 (fun x =>
      let get_bit (z : Z) : Z :=
        xor3
          (((a_prime.(Array.get) y).(Array.get) x).(Array.get) z)
          ((c.(Array.get) x).(Array.get) z)
          ((c_prime.(Array.get) x).(Array.get) z)
      in

      let* _ := M.assert_bools ((a_prime.(Array.get) y).(Array.get) x) in

      M.assert_zeros (N := U64_LIMBS) {|
        Array.get limb :=
          let computed_limb : Z :=
            let l : list nat :=
              List.rev (
                List.seq
                  (Z.to_nat (limb * BITS_PER_LIMB))%Z
                  (Z.to_nat (limb * BITS_PER_LIMB + BITS_PER_LIMB))%Z
              ) in
            Lists.List.fold_left (fun acc (z : nat) =>
              let z : Z := Z.of_nat z in
              BinOp.add (BinOp.mul 2 acc) (get_bit z)
            ) l 0 in
          BinOp.sub
            computed_limb
            (((a.(Array.get) y).(Array.get) x).(Array.get) limb)
      |}
    )).

Definition eval_assert_a_a_prime_c_c_prime_implies_a_prime_bools {p} `{Prime p}
    (a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (a_prime : Array.t (Array.t (Array.t Z 64) 5) 5)
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    let a := M.map_mod a in
    let a_prime := M.map_mod a_prime in
    let c := M.map_mod c in
    let c_prime := M.map_mod c_prime in
    {{ eval_assert_a_a_prime_c_c_prime a a_prime c c_prime 🔽
      tt,
      forall (y x z : Z),
      0 <= y < 5 ->
      0 <= x < 5 ->
      0 <= z < 64 ->
      exists (b : bool),
      ((a_prime.(Array.get) y).(Array.get) x).(Array.get) z = Z.b2z b
    }}.
Proof.
  intros.
  unfold eval_assert_a_a_prime_c_c_prime.
  eapply Run.Implies. {
    repeat (econstructor || intros).
  }
  hauto l: on.
Qed.

Lemma eval_assert_a_a_prime_c_c_prime_implies_a_a_prime_c_c_prime {p} `{Prime p}
    (a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5)
    (a_prime : Array.t (Array.t (Array.t Z 64) 5) 5)
    (c : Array.t (Array.t Z 64) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    let a := M.map_mod a in
    let a_prime := M.map_mod a_prime in
    let c := M.map_mod c in
    let c_prime := M.map_mod c_prime in
  {{ eval_assert_a_a_prime_c_c_prime a a_prime c c_prime 🔽
    tt,
    forall (y x : Z),
    0 <= y < 5 ->
    0 <= x < 5 ->
    let a' : Array.t Z U64_LIMBS :=
      Limbs.of_bools U64_LIMBS BITS_PER_LIMB
        {|
          Array.get z :=
            M.xor3
              (((a_prime.(Array.get) y).(Array.get) x).(Array.get) z)
              ((c.(Array.get) x).(Array.get) z)
              ((c_prime.(Array.get) x).(Array.get) z);
        |} in
    forall (limb : Z),
    0 <= limb < U64_LIMBS ->
    ((a.(Array.get) y).(Array.get) x).(Array.get) limb =
    a'.(Array.get) limb
  }}.
Proof.
  intros.
  unfold eval_assert_a_a_prime_c_c_prime.
  eapply Run.Implies. {
    repeat (econstructor || intros).
  }
  hauto q: on.
Qed.

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
Definition eval_assert_a_prime_c_prime {p} `{Prime p}
    (a_prime : Array.t (Array.t (Array.t Z 64) 5) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    M.t unit :=
  M.for_in_zero_to_n 5 (fun x =>
    let four : Z := 4 in
    M.assert_zeros (N := 64) {|
      Array.get z :=
        let sum : Z :=
          Lists.List.fold_left (fun acc y =>
            BinOp.add acc
              (Array.get (Array.get (Array.get a_prime y) x) z)
          )
          (List.map Z.of_nat (List.seq 0 5)) 0 in
        let diff := BinOp.sub sum (Array.get (Array.get c_prime x) z) in
        BinOp.mul diff (BinOp.mul (BinOp.sub diff 2) (BinOp.sub diff four))
      |}
    ).

Lemma eval_assert_a_prime_c_prime_implies {p} `{Prime p}
    (a_prime : Array.t (Array.t (Array.t Z 64) 5) 5)
    (c_prime : Array.t (Array.t Z 64) 5) :
    let a_prime := M.map_mod a_prime in
    let c_prime := M.map_mod c_prime in
    {{ eval_assert_a_prime_c_prime a_prime c_prime 🔽
      tt,
      forall (x z : Z),
      0 <= x < 5 ->
      0 <= z < 64 ->
      (c_prime.(Array.get) x).(Array.get) z =
      M.xor
        (((a_prime.(Array.get) x).(Array.get) 0).(Array.get) z)
        (M.xor
          (((a_prime.(Array.get) x).(Array.get) 1).(Array.get) z)
          (M.xor
            (((a_prime.(Array.get) x).(Array.get) 2).(Array.get) z)
            (((a_prime.(Array.get) x).(Array.get) 3).(Array.get) z)
          )
        )
    }}.
Proof.
Admitted.
(*
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
Definition eval_assert_a_prime_prime {p} `{Prime p}
    (a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5) :
    M.t unit :=
  M.for_in_zero_to_n 5 (fun y =>
  M.for_in_zero_to_n 5 (fun x =>
    let get_bit (z : Z) : Z :=
      let andn :=
        andn
          (Impl_KeccakCols.b local ((x + 1) mod 5) y z)
          (Impl_KeccakCols.b local ((x + 2) mod 5) y z) in
        xor
          andn
          (Impl_KeccakCols.b local x y z) in
    M.zeros (N := U64_LIMBS) {|
      Array.get limb :=
        let computed_limb : Z :=
          let l : list Z :=
            List.rev (List.map
              (fun n => limb * BITS_PER_LIMB + Z.of_nat n)
              (List.seq 0 (Z.to_nat BITS_PER_LIMB))
            ) in
          Lists.List.fold_left (fun acc z => BinOp.add (BinOp.mul 2 acc) (get_bit z)) l 0 in
        BinOp.sub
          computed_limb
          (((local.(KeccakCols.a_prime_prime).(Array.get) y).(Array.get) x).(Array.get) limb)
      |}
    )).

  (*
  builder.assert_bools(local.a_prime_prime_0_0_bits);
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
  let* _ := assert_bools local.(KeccakCols.a_prime_prime_0_0_bits) in
  let* _ :=
    M.zeros (N := U64_LIMBS) {|
      Array.get limb :=
        let computed_a_prime_prime_0_0_limb : Z :=
          let l : list Z :=
            List.rev (List.map
              (fun n => limb * BITS_PER_LIMB + Z.of_nat n)
              (List.seq 0 (Z.to_nat BITS_PER_LIMB))
            ) in
          Lists.List.fold_left (fun acc z => BinOp.add (BinOp.mul 2 acc) (Array.get local.(KeccakCols.a_prime_prime_0_0_bits) z)) l 0 in
        BinOp.sub
          computed_a_prime_prime_0_0_limb
          (((local.(KeccakCols.a_prime_prime).(Array.get) 0).(Array.get) 0).(Array.get) limb)
    |} in

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
  let get_xored_bit (i : Z) : Z :=
    let rc_bit_i : Z :=
      Lists.List.fold_left (fun acc r =>
        let this_round := Array.get local.(KeccakCols.step_flags) r in
        let this_round_constant :=
          Z.b2z (rc_value_bit r i) in
        BinOp.add acc
          (BinOp.mul this_round this_round_constant)
      )
      (List.map Z.of_nat (List.seq 0 (Z.to_nat NUM_ROUNDS))) 0 in
    xor rc_bit_i (Array.get local.(KeccakCols.a_prime_prime_0_0_bits) i) in

  (*
  builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
      let computed_a_prime_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
          ..(limb + 1) * BITS_PER_LIMB)
          .rev()
          .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_xored_bit(z));
      computed_a_prime_prime_prime_0_0_limb - local.a_prime_prime_prime_0_0_limbs[limb]
  }));
  *)
  let* _ :=
    M.zeros (N := U64_LIMBS) {|
      Array.get limb :=
        let computed_a_prime_prime_prime_0_0_limb : Z :=
          let l : list Z :=
            List.rev (List.map
              (fun n => limb * BITS_PER_LIMB + Z.of_nat n)
              (List.seq 0 (Z.to_nat BITS_PER_LIMB))
            ) in
          Lists.List.fold_left (fun acc z => BinOp.add (BinOp.mul 2 acc) (get_xored_bit z)) l 0 in
        BinOp.sub
          computed_a_prime_prime_prime_0_0_limb
          (Array.get local.(KeccakCols.a_prime_prime_prime_0_0_limbs) limb)
    |} in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun x =>
    M.for_in_zero_to_n 5 (fun y =>
      when_bool is_transition (
      when_bool is_not_final_step (
        M.zeros (N := U64_LIMBS) {|
          Array.get limb :=
            BinOp.sub
              (Impl_KeccakCols.a_prime_prime_prime local y x limb)
              (Array.get (Array.get (Array.get next.(KeccakCols.a) y) x) limb)
        |}
      ))
    )) in

  M.pure tt.
*)
