Require Import Garden.Plonky3.MLessEffects.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.
Require Import Garden.Plonky3.keccak.round_flags.

(* fn eval(&self, builder: &mut AB) *)
Definition eval_transition_as_spec
    {p} `{Prime p}
    (is_first_row is_first_step is_not_final_step : bool)
    (local next : KeccakCols.t)
    (round : Z) (H_round : 0 <= round < NUM_ROUNDS)
    (H_local : local.(KeccakCols.step_flags) = round_indicator round) :
    M.t unit :=
  (* eval_round_flags(builder); *)
  let* _ := eval_round_flags is_first_row true local next in

  (*
  let main = builder.main();
  let (local, next) = (
      main.row_slice(0).expect("The matrix is empty?"),
      main.row_slice(1).expect("The matrix only has 1 row?"),
  );
  let local: &KeccakCols<AB::Var> = ( *local).borrow();
  let next: &KeccakCols<AB::Var> = ( *next).borrow();

  let first_step = local.step_flags[0];
  let final_step = local.step_flags[NUM_ROUNDS - 1];
  let not_final_step = AB::Expr::ONE - final_step;
  *)
  let first_step := local.(KeccakCols.step_flags).(Array.get) 0 in
  let final_step := local.(KeccakCols.step_flags).(Array.get) (NUM_ROUNDS - 1) in
  let not_final_step := BinOp.sub 1 final_step in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun y =>
    M.for_in_zero_to_n 5 (fun x =>
      when_bool is_first_step (
        M.zeros (N := U64_LIMBS) {|
          Array.get limb :=
            BinOp.sub
              (Array.get (Array.get (Array.get local.(KeccakCols.preimage) y) x) limb)
              (Array.get (Array.get (Array.get local.(KeccakCols.a) y) x) limb)
        |}
      )
    )) in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun y =>
    M.for_in_zero_to_n 5 (fun x =>
      when_bool is_not_final_step (
        M.zeros (N := U64_LIMBS) {|
          Array.get limb :=
            BinOp.sub
              (Array.get (Array.get (Array.get local.(KeccakCols.preimage) y) x) limb)
              (Array.get (Array.get (Array.get next.(KeccakCols.preimage) y) x) limb)
        |}
      )
    )) in

  (* builder.assert_bool(local.export); *)
  let* _ := assert_bool local.(KeccakCols.export) in

  (*
  builder
    .when(not_final_step.clone())
    .assert_zero(local.export);
  *)
  let* _ := when_bool is_not_final_step (
    assert_zero local.(KeccakCols.export)
  ) in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun x =>
      let* _ := assert_bools (local.(KeccakCols.c).(Array.get) x) in
      M.zeros (N := 64) {|
        Array.get z :=
          let xor :=
            xor3
              ((local.(KeccakCols.c).(Array.get) x).(Array.get) z)
              ((local.(KeccakCols.c).(Array.get) ((x + 4) mod 5)).(Array.get) z)
              ((local.(KeccakCols.c).(Array.get) ((x + 1) mod 5)).(Array.get) ((z + 63) mod 64))
          in
          BinOp.sub
            ((local.(KeccakCols.c_prime).(Array.get) x).(Array.get) z)
            xor
      |}
    ) in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun y =>
    M.for_in_zero_to_n 5 (fun x =>
      let get_bit (z : Z) : Z :=
        xor3
          (((local.(KeccakCols.a_prime).(Array.get) y).(Array.get) x).(Array.get) z)
          ((local.(KeccakCols.c).(Array.get) x).(Array.get) z)
          ((local.(KeccakCols.c_prime).(Array.get) x).(Array.get) z)
      in

      let* _ := assert_bools ((local.(KeccakCols.a_prime).(Array.get) y).(Array.get) x) in

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
            (((local.(KeccakCols.a).(Array.get) y).(Array.get) x).(Array.get) limb)
      |}
    )) in

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
  let* _ :=
    M.for_in_zero_to_n 5 (fun x =>
      let four : Z := 4 in
      M.zeros (N := 64) {|
        Array.get z :=
          let sum : Z :=
            Lists.List.fold_left (fun acc y =>
              BinOp.add acc
                (Array.get (Array.get (Array.get local.(KeccakCols.a_prime) y) x) z)
            )
            (List.map Z.of_nat (List.seq 0 5)) 0 in
          let diff := BinOp.sub sum (Array.get (Array.get local.(KeccakCols.c_prime) x) z) in
          BinOp.mul diff (BinOp.mul (BinOp.sub diff 2) (BinOp.sub diff four))
        |}
      ) in

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
  let* _ :=
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
      )) in

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
      when_bool is_not_final_step (
        M.zeros (N := U64_LIMBS) {|
          Array.get limb :=
            BinOp.sub
              (Impl_KeccakCols.a_prime_prime_prime local y x limb)
              (Array.get (Array.get (Array.get next.(KeccakCols.a) y) x) limb)
        |}
      )
    )) in

  M.pure tt.
