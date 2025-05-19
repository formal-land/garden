Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.
Require Import Garden.Plonky3.keccak.round_flags.

(* fn eval(&self, builder: &mut AB) *)
Definition eval
    (is_first_row is_first_step is_not_final_step is_transition : bool)
    (local next : KeccakCols.t) :
    M.t unit :=
  (* eval_round_flags(builder); *)
  let* _ := eval_round_flags is_first_row is_transition local next in

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
  let* first_step := [[ Array.get (| local.(KeccakCols.step_flags), 0 |) ]] in
  let* final_step := [[ Array.get (| local.(KeccakCols.step_flags), NUM_ROUNDS - 1 |) ]] in
  let* not_final_step := [[ M.sub (| 1, final_step |) ]] in

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
    for_in_zero_to_n 5 (fun y =>
    for_in_zero_to_n 5 (fun x =>
      when is_first_step [[
        assert_zeros (N := U64_LIMBS) (|
          Array.from_fn (| fun limb => [[
            M.sub (|
              Array.get (| Array.get (| Array.get (| local.(KeccakCols.preimage), y |), x |), limb |),
              Array.get (| Array.get (| Array.get (| local.(KeccakCols.a), y |), x |), limb |)
            |)
          ]] |)
        |)
      ]]
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
    for_in_zero_to_n 5 (fun y =>
    for_in_zero_to_n 5 (fun x =>
      when (is_not_final_step && is_transition) [[
        assert_zeros (N := U64_LIMBS) (|
          Array.from_fn (| fun limb => [[
            M.sub (|
              Array.get (| Array.get (| Array.get (| local.(KeccakCols.preimage), y |), x |), limb |),
              Array.get (| Array.get (| Array.get (| next.(KeccakCols.preimage), y |), x |), limb |)
            |)
          ]] |)
        |)
      ]]
    )) in

  (* builder.assert_bool(local.export); *)
  let* _ := [[ assert_bool (| local.(KeccakCols.export) |) ]] in

  (*
  builder
    .when(not_final_step.clone())
    .assert_zero(local.export);
  *)
  let* _ := when is_not_final_step [[
    assert_zero (| local.(KeccakCols.export) |)
  ]] in

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
    for_in_zero_to_n 5 (fun x =>
      let* _ := [[ assert_bools (| Array.get (| local.(KeccakCols.c), x |) |) ]] in
      let* _ := [[
        assert_zeros (|
          Array.from_fn (N := 64) (| fun z =>
            let* xor := [[
              xor3 (|
                Array.get (| Array.get (| local.(KeccakCols.c), x |), z |),
                Array.get (| Array.get (| local.(KeccakCols.c), (x + 4) mod 5 |), z |),
                Array.get (| Array.get (| local.(KeccakCols.c), (x + 1) mod 5 |), (z + 63) mod 64 |)
              |)
            ]] in
            [[
              M.sub (|
                Array.get (| Array.get (| local.(KeccakCols.c_prime), x |), z |),
                xor
              |)
            ]]
          |)
        |)
      ]] in
      M.Pure tt
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
    for_in_zero_to_n 5 (fun y =>
    for_in_zero_to_n 5 (fun x =>
      let get_bit (z : Z) : M.t Z := [[
        xor3 (|
          Array.get (| Array.get (| Array.get (| local.(KeccakCols.a_prime), y |), x |), z |),
          Array.get (| Array.get (| local.(KeccakCols.c), x |), z |),
          Array.get (| Array.get (| local.(KeccakCols.c_prime), x |), z |)
        |)
      ]] in

      let* _ := [[
        assert_bools (| Array.get (| Array.get (| local.(KeccakCols.a_prime), y |), x |) |)
      ]] in

      [[
        assert_zeros (N := U64_LIMBS) (|
          Array.from_fn (| fun limb =>
            let* computed_limb :=
              let l : list Z :=
                List.rev (List.map
                  (fun n => limb * BITS_PER_LIMB + Z.of_nat n)
                  (List.seq 0 (Z.to_nat BITS_PER_LIMB))
                ) in
              [[
                fold (|
                  0,
                  l,
                  fun acc z => [[
                    M.add (|
                      M.mul (| 2, acc |),
                      get_bit (| z |)
                    |)
                  ]]
                |)
              ]] in
            [[
              M.sub (|
                computed_limb,
                Array.get (| Array.get (| Array.get (| local.(KeccakCols.a), y |), x |), limb |)
              |)
            ]]
          |)
        |)
      ]]
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
    for_in_zero_to_n 5 (fun x =>
      let four : Z := 4 in
      [[
        assert_zeros (N := 64) (|
          Array.from_fn (| fun z =>
            let* sum := [[
              fold (|
                0,
                List.map Z.of_nat (List.seq 0 5),
                fun acc y => [[
                  M.add (|
                    acc,
                    Array.get (| Array.get (| Array.get (| local.(KeccakCols.a_prime), y |), x |), z |)
                  |)
                ]]
              |)
            ]] in
            let* diff := [[
              M.sub (|
                sum,
                Array.get (| Array.get (| local.(KeccakCols.c_prime), x |), z |)
              |)
            ]] in
            [[
              M.mul (|
                M.mul (| diff, M.sub (| diff, 2 |) |),
                M.sub (| diff, four |)
              |)
            ]]
          |)
        |)
      ]]
    ) in

  (* TODO: complete the rest of the function *)

  M.Pure tt.
