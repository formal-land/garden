Require Import Garden.Plonky3.M.

(*

/// Pack a collection of bits into a number.
///
/// Given `vec = [v_0, v_1, ..., v_n]` returns `v_0 + 2v_1 + ... + 2^n v_n`
#[inline]
pub fn pack_bits_le<R, Var, I>(iter: I) -> R
where
    R: PrimeCharacteristicRing,
    Var: Into<R> + Clone,
    I: DoubleEndedIterator<Item = Var>,
{
    iter.rev()
        .map(Into::into)
        .reduce(|acc, elem| acc.double() + elem)
        .unwrap_or(R::ZERO)
}

*)
Definition pack_bits_le (bits : list Z) : M.t Z :=
  let reversed_bits := List.rev bits in
  [[
    fold (|
      0,  (* Start with zero accumulator *)
      reversed_bits,
      fun acc bit => [[
        M.add (| M.mul (| 2, acc |), bit |)  (* acc * 2 + bit *)
      ]]
    |)
  ]].

(* Helper function to compute XOR of bit arrays with shift *)
(*
#[inline]
pub fn xor_32_shift<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; 2],
    b: &[AB::Var; 32],
    c: &[AB::Var; 32],
    shift: usize,
) {
    // First we range check all elements of c.
    builder.assert_bools( *c);

    // Next we compute (b ^ (c << shift)) and pack the result into two 16-bit integers.
    let xor_shift_c_0_16 = b[..16]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( * elem).into().xor(&c[(32 + i - shift) % 32].into()));
    let sum_0_16: AB::Expr = pack_bits_le(xor_shift_c_0_16);

    let xor_shift_c_16_32 = b[16..]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( * elem).into().xor(&c[(32 + (i + 16) - shift) % 32].into()));
    let sum_16_32: AB::Expr = pack_bits_le(xor_shift_c_16_32);

    // As both b and c have been range checked to be boolean, all the (b ^ (c << shift))
    // are also boolean and so this final check additionally has the effect of range checking a[0], a[1].
    builder.assert_zeros([a[0] - sum_0_16, a[1] - sum_16_32]);
}

*)
Definition xor_32_shift 
    (a : Array.t Z 2)      (* Result array with 2 limbs *)
    (b : Array.t Z 32)     (* First input array with 32 bits *)
    (c : Array.t Z 32)     (* Second input array with 32 bits *)
    (shift : Z)            (* Shift amount *)
    : M.t unit := 
  (* 
  // First we range check all elements of c.
  builder.assert_bools( *c); 
  *)
  let* _ := [[ assert_bools (| c |) ]] in

  (*
    // Next we compute (b ^ (c << shift)) and pack the result into two 16-bit integers.
    let xor_shift_c_0_16 = b[..16]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( *elem).into().xor(&c[(32 + i - shift) % 32].into()));  
  *)
  let* xor_shift_c_0_16 := [[
    Array.from_fn (N := 16) (| fun i => 
      let* elem := [[ Array.get (| b, i |) ]] in
      let* c_elem := [[ Array.get (| c, (32 + i - shift) mod 32 |) ]] in
      [[ M.xor (| elem, c_elem |) ]]
    |)

  ]] in
  (* let sum_0_16: AB::Expr = pack_bits_le(xor_shift_c_0_16); *)
  let* sum_0_16 := [[ pack_bits_le (| xor_shift_c_0_16.(Array.value) |) ]] in

  (*
    let xor_shift_c_16_32 = b[16..]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( *elem).into().xor(&c[(32 + (i + 16) - shift) % 32].into()));  
  *)
  let* xor_shift_c_16_32 := [[
    Array.from_fn (N := 16) (| fun i => 
      let* elem := [[ Array.get (| b, i + 16 |) ]] in
      let* c_elem := [[ Array.get (| c, (32 + (i + 16) - shift) mod 32 |) ]] in
      [[ M.xor (| elem, c_elem |) ]]
    |)
  ]] in
  (* let sum_16_32: AB::Expr = pack_bits_le(xor_shift_c_16_32); *)
  let* sum_16_32 := [[ pack_bits_le (| xor_shift_c_16_32.(Array.value) |) ]] in

  (* As both b and c have been range checked to be boolean, all the (b ^ (c << shift))
    are also boolean and so this final check additionally has the effect of range checking a[0], a[1]. *)
  (* builder.assert_zeros([a[0] - sum_0_16, a[1] - sum_16_32]); *)
  let* a0 := [[ Array.get (| a, 0 |) ]] in
  let* a1 := [[ Array.get (| a, 1 |) ]] in
  let differences : Array.t Z 2 := {| Array.value := [
    M.sub (| a0, sum_0_16 |);
    M.sub (| a1, sum_16_32 |)
  ] |} in
  [[ assert_zeros (| differences |) ]].

(*
#[inline]
pub fn add3<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; 2],
    b: &[AB::Var; 2],
    c: &[AB::Expr; 2],
    d: &[AB::Expr; 2],
) {
    // Define:
    //  acc    = a - b - c - d (mod P)
    //  acc_16 = a[0] - b[0] - c[0] - d[0] (mod P)
    //
    // We perform 2 checks:
    //
    // (1) acc*(acc + 2^32)*(acc + 2*2^32) = 0.
    // (2) acc_16*(acc_16 + 2^16)*(acc_16 + 2*2^16) = 0.

    // No overflow can occur mod 2^16 P as 2^16 P > 3*2^32 and a, b, c, d < 2^32. Hence we conclude that
    // over the integers a - b - c - d = 0, -2^32 or -2*2^32 which implies a = b + c + d mod 2^32.

    // By assumption P > 3*2^16 so 1 << 16 will be less than P. We use the checked version just to be safe.
    // The compiler should optimize it away.
    let two_16 =
        <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(1 << 16)
            .unwrap();
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0].clone() - d[0].clone();
    let acc_32 = a[1] - b[1] - c[1].clone() - d[1].clone();
    let acc = acc_16.clone() + acc_32.mul_2exp_u64(16);

    builder.assert_zeros([
        acc.clone()
            * (acc.clone() + AB::Expr::from_prime_subfield(two_32))
            * (acc + AB::Expr::from_prime_subfield(two_32.double())),
        acc_16.clone()
            * (acc_16.clone() + AB::Expr::from_prime_subfield(two_16))
            * (acc_16 + AB::Expr::from_prime_subfield(two_16.double())),
    ]);
}
*)
(* Verify that a = b + c + d mod 2^32 *)
Definition add3 
    (a : Array.t Z 2)  
    (b : Array.t Z 2) 
    (c : Array.t Z 2) 
    (d : Array.t Z 2)  
    : M.t unit :=
  
  (* Define constants *)
  let two_16 := Z.pow 2 16 in  (* 2^16 *)
  let two_32 := Z.pow 2 32 in  (* 2^32 *)
  
  (* Get array elements *)
  let* a_0 := [[ Array.get (| a, 0 |) ]] in
  let* a_1 := [[ Array.get (| a, 1 |) ]] in
  let* b_0 := [[ Array.get (| b, 0 |) ]] in
  let* b_1 := [[ Array.get (| b, 1 |) ]] in
  let* c_0 := [[ Array.get (| c, 0 |) ]] in
  let* c_1 := [[ Array.get (| c, 1 |) ]] in
  let* d_0 := [[ Array.get (| d, 0 |) ]] in
  let* d_1 := [[ Array.get (| d, 1 |) ]] in
  
  (* Compute acc_16 = a[0] - b[0] - c[0] - d[0] *)
  let* acc_16 := [[
    M.sub (|
      M.sub (|
        M.sub (| a_0, b_0 |),
        c_0
      |),
      d_0
    |)
  ]] in
  
  (* Compute acc_32 = a[1] - b[1] - c[1] - d[1] *)
  let* acc_32 := [[
    M.sub (|
      M.sub (|
        M.sub (| a_1, b_1 |),
        c_1
      |),
      d_1
    |)
  ]] in
  
  (* Compute acc = acc_16 + acc_32 * 2^16 *)
  let* acc := [[
    M.add (|
      acc_16,
      M.mul (| acc_32, two_16 |)
    |)
  ]] in
  
  (* First constraint: acc * (acc + 2^32) * (acc + 2*2^32) = 0 *)
  let* constraint1 := [[
    M.mul (|
      M.mul (|
        acc,
        M.add (| acc, two_32 |)
      |),
      M.add (| acc, 2 * two_32 |)
    |)
  ]] in
  
  (* Second constraint: acc_16 * (acc_16 + 2^16) * (acc_16 + 2*2^16) = 0 *)
  let* constraint2 := [[
    M.mul (|
      M.mul (|
        acc_16,
        M.add (| acc_16, two_16 |)
      |),
      M.add (| acc_16, 2 * two_16 |)
    |)
  ]] in
  
  (* Assert both constraints equal zero *)
  let constraints : Array.t Z 2 := {| Array.value := [ constraint1; constraint2 ] |} in

  [[ assert_zeros (| constraints |) ]]. 



(*
#[inline]
pub fn add2<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; 2],
    b: &[AB::Var; 2],
    c: &[AB::Expr; 2],
) {
    // Define:
    //  acc    = a - b - c (mod P)
    //  acc_16 = a[0] - b[0] - c[0] (mod P)
    //
    // We perform 2 checks:
    //
    // (1) acc*(acc + 2^32) = 0.
    // (2) acc_16*(acc_16 + 2^16) = 0.
    //
    // We give a short proof for why this lets us conclude that a = b + c mod 2^32:
    //
    // As all 16 bit limbs have been range checked, we know that a, b, c lie in [0, 2^32) and hence
    // a = b + c mod 2^32 if and only if, over the integers, a - b - c = 0 or -2^32.
    //
    // Equation (1) verifies that either a - b - c = 0 mod P or a - b - c = -2^32 mod P.
    //
    // Field overflow cannot occur when computing acc_16 as our characteristic is larger than 2^17.
    // Hence, equation (2) verifies that, over the integers, a[0] - b[0] - c[0] = 0 or -2^16.
    // Either way we can immediately conclude that a - b - c = 0 mod 2^16.
    //
    // Now we can use the chinese remainder theorem to combine these results to conclude that
    // either a - b - c = 0 mod 2^16 P or a - b - c = -2^32 mod 2^16 P.
    //
    // No overflow can occur mod 2^16 P as 2^16 P > 2^33 and a, b, c < 2^32. Hence we conclude that
    // over the integers a - b - c = 0 or a - b - c = -2^32 which is equivalent to a = b + c mod 2^32.

    // By assumption P > 2^17 so 1 << 16 will be less than P. We use the checked version just to be safe.
    // The compiler should optimize it away.
    let two_16 =
        <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(1 << 16)
            .unwrap();
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0].clone();
    let acc_32 = a[1] - b[1] - c[1].clone();
    let acc = acc_16.clone() + acc_32.mul_2exp_u64(16);

    builder.assert_zeros([
        acc.clone() * (acc + AB::Expr::from_prime_subfield(two_32)),
        acc_16.clone() * (acc_16 + AB::Expr::from_prime_subfield(two_16)),
    ]);
}
*)
Definition add2
    (a : Array.t Z 2)  
    (b : Array.t Z 2) 
    (c : Array.t Z 2) 
    : M.t unit := 
  (*
    let two_16 =
      <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(1 << 16)
          .unwrap();
    let two_32 = two_16.square();
  *)
  let two_16 := Z.pow 2 16 in  (* 2^16 *)
  let two_32 := Z.pow 2 32 in  (* 2^32 *)
  (* Might need some changes here as I believe we should use something specific to prime fields*)

  (*
    let acc_16 = a[0] - b[0] - c[0].clone();
    let acc_32 = a[1] - b[1] - c[1].clone();
  *)
  let* acc_16 := [[
    M.sub (|
      M.sub (| Array.get (| a, 0 |), Array.get (| b, 0 |) |),
      Array.get (| c, 0 |)
    |)
  ]] in
  let* acc_32 := [[
    M.sub (|
      M.sub (| Array.get (| a, 1 |), Array.get (| b, 1 |) |),
      Array.get (| c, 1 |)
    |)
  ]] in
  (* let acc = acc_16.clone() + acc_32.mul_2exp_u64(16); *)
  let* acc := [[
    M.add (|
      acc_16,
      M.mul (| acc_32, two_16 |)
    |)
  ]] in

  (*
  builder.assert_zeros([
    acc.clone() * (acc + AB::Expr::from_prime_subfield(two_32)),
    acc_16.clone() * (acc_16 + AB::Expr::from_prime_subfield(two_16)),
  ]);
  *)
  let* constraint1 := 
    [[
      M.mul (|
        acc,
        M.add (| acc, two_32 |)
      |)
    ]]
  in
  let* constraint2 :=
    [[
      M.mul (|
        acc_16,
        M.add (| acc_16, two_16 |)
      |)
    ]]
  in
  
  let constraints : Array.t Z 2 := {| Array.value := [ constraint1; constraint2 ] |} in

  [[ assert_zeros (| constraints |) ]]. 

  
