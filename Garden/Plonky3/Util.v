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

Definition pack_bits_le_list {p} `{Prime p} (bits : list Z) : M.t Z := 
    let reversed_bits := List.rev bits in 
    List.fold_left (fun acc x => M.pure (BinOp.add (BinOp.mul 2 acc) x)) 0 reversed_bits.

Definition pack_bits_le_array {p} `{Prime p} {N : Z} (bits : Array.t Z N) : Z :=
    M.sum_for_in_zero_to_n N (fun i => BinOp.mul (Array.get bits i) (2 ^ i)).


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
Definition xor_32_shift {p} `{Prime p} 
    (a : Array.t Z 2)      (* Result array with 2 limbs *)
    (b : Array.t Z 32)     (* First input array with 32 bits *)
    (c : Array.t Z 32)     (* Second input array with 32 bits *)
    (shift : Z)            (* Shift amount *)
    : M.t unit :=
  (* 
  // First we range check all elements of c.
  builder.assert_bools( *c); 
  *)
  let* _ := assert_bools c in
  (*
    // Next we compute (b ^ (c << shift)) and pack the result into two 16-bit integers.
    let xor_shift_c_0_16 = b[..16]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( *elem).into().xor(&c[(32 + i - shift) % 32].into()));  
  *)
  let xor_shift_c_0_16 : Array.t Z 16 := {|
    Array.get i := 
      let elem := b.(Array.get) i in
      let c_elem := c.(Array.get) ((32 + i - shift) mod 32) in
      xor elem c_elem
  |} in 

  (* let sum_0_16: AB::Expr = pack_bits_le(xor_shift_c_0_16); *)
  let sum_0_16 := pack_bits_le_array xor_shift_c_0_16 in

  (*
      let xor_shift_c_16_32 = b[16..]
        .iter()
        .enumerate()
        .map(|(i, elem)| ( * elem).into().xor(&c[(32 + (i + 16) - shift) % 32].into()));
  *)
  let xor_shift_c_16_32 : Array.t Z 16 := {|
    Array.get i := 
      let elem := b.(Array.get) (i + 16) in
      let c_elem := c.(Array.get) ((32 + (i + 16) - shift) mod 32) in
      xor elem c_elem
  |} in

  (* let sum_16_32: AB::Expr = pack_bits_le(xor_shift_c_16_32); *)
  let sum_16_32 := pack_bits_le_array xor_shift_c_16_32 in

  (* builder.assert_zeros([a[0] - sum_0_16, a[1] - sum_16_32]); *)
  let* zero_1 := assert_zero (BinOp.sub (Array.get a 0) sum_0_16) in
  let* zero_2 := assert_zero (BinOp.sub (Array.get a 1) sum_16_32) in
  M.Pure tt.


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
Definition add2 {p} `{Prime p} 
    (a : Array.t Z 2)      (* Result array with 2 limbs *)
    (b : Array.t Z 2)      (* First input array with 2 limbs *)
    (c : Array.t Z 2)      (* Second input array with 2 limbs *)
    : M.t unit :=
    (*
    let two_16 =
        <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(1 << 16)
            .unwrap();    
    *)
    let two_16 := UnOp.from (2 ^ 16) in
    (* let two_32 = two_16.square(); *)
    let two_32 := BinOp.mul two_16 two_16 in
    (* let acc_16 = a[0] - b[0] - c[0].clone(); *)
    let acc_16 := BinOp.sub (BinOp.sub (Array.get a 0) (Array.get b 0)) (Array.get c 0) in
    (* let acc_32 = a[1] - b[1] - c[1].clone(); *)
    let acc_32 := BinOp.sub (BinOp.sub (Array.get a 1) (Array.get b 1)) (Array.get c 1) in
    (* let acc = acc_16.clone() + acc_32.mul_2exp_u64(16); *)
    let acc := BinOp.add acc_16 (BinOp.mul acc_32 (2 ^ 16)) in
    (*     
    builder.assert_zeros([
        acc.clone() * (acc + AB::Expr::from_prime_subfield(two_32)),
        acc_16.clone() * (acc_16 + AB::Expr::from_prime_subfield(two_16)),
    ]); 
    *)
    let* _ := assert_zero (BinOp.mul acc (BinOp.add acc two_32)) in
    let* _ := assert_zero (BinOp.mul acc_16 (BinOp.add acc_16 two_16)) in
    M.Pure tt.

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
Definition add3 {p} `{Prime p} 
    (a : Array.t Z 2)      (* Result array with 2 limbs *)
    (b : Array.t Z 2)      (* First input array with 2 limbs *)
    (c : Array.t Z 2)      (* Second input array with 2 limbs *)
    (d : Array.t Z 2)      (* Third input array with 2 limbs *)
    : M.t unit :=
    (*
    let two_16 =
        <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(1 << 16)
            .unwrap();    
    *)
    let two_16 := UnOp.from (2 ^ 16) in
    (* let two_32 = two_16.square(); *)
    let two_32 := BinOp.mul two_16 two_16 in
    (* let acc_16 = a[0] - b[0] - c[0].clone() - d[0].clone(); *)
    let acc_16 := BinOp.sub (BinOp.sub (BinOp.sub (Array.get a 0) (Array.get b 0)) (Array.get c 0)) (Array.get d 0) in
    (* let acc_32 = a[1] - b[1] - c[1].clone() - d[1].clone(); *)
    let acc_32 := BinOp.sub (BinOp.sub (BinOp.sub (Array.get a 1) (Array.get b 1)) (Array.get c 1)) (Array.get d 1) in
    (* let acc = acc_16.clone() + acc_32.mul_2exp_u64(16); *)
    let acc := BinOp.add acc_16 (BinOp.mul acc_32 (2 ^ 16)) in
    (*     
    builder.assert_zeros([
        acc.clone()
            * (acc.clone() + AB::Expr::from_prime_subfield(two_32))
            * (acc + AB::Expr::from_prime_subfield(two_32.double())),
        acc_16.clone()
            * (acc_16.clone() + AB::Expr::from_prime_subfield(two_16))
            * (acc_16 + AB::Expr::from_prime_subfield(two_16.double())),
    ]);
    *)
    let* _ := assert_zero 
      (BinOp.mul 
        (BinOp.mul acc (BinOp.add acc two_32))
        (BinOp.add acc (double two_32))) in
    let* _ := assert_zero 
      (BinOp.mul 
        (BinOp.mul acc_16 (BinOp.add acc_16 two_16))
        (BinOp.add acc_16 (double two_16))) in
    M.Pure tt.

