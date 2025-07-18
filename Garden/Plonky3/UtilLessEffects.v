Require Import Garden.Plonky3.MLessEffects.

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

Definition pack_bits_le_array {p} `{Prime p} {N : Z} (bits : Array.t Z N) : M.t Z :=
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
  let* sum_0_16 := pack_bits_le_array xor_shift_c_0_16 in

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
  let* sum_16_32 := pack_bits_le_array xor_shift_c_16_32 in

  (* builder.assert_zeros([a[0] - sum_0_16, a[1] - sum_16_32]); *)
  let* zero_1 := assert_zero (BinOp.sub (Array.get a 0) sum_0_16) in
  let* zero_2 := assert_zero (BinOp.sub (Array.get a 1) sum_16_32) in
  M.Pure tt.
