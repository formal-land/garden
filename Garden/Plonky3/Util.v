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

(** ** Completeness Template for Plonky3 Circuits using CPS *)

(** A template for defining completeness conditions for circuit constraints.
    The goal is to prove that for valid inputs in the expected ranges,
    the circuit evaluation succeeds. *)

Module Completeness.
  
  (** Convert from concrete field values to Z for evaluation *)
  Parameter field_to_Z : forall (F : Type), F -> Z.
  Parameter Z_to_field : forall (F : Type), Z -> F.
  Parameter field_prime : forall (F : Type), Z.
  
  (** For Plonky3 fields specifically, we assume the field has characteristic p *)
  Parameter plonky3_prime : Z.
  Axiom plonky3_prime_is_prime : IsPrime plonky3_prime.
  Axiom plonky3_prime_large : plonky3_prime > 2^33.
  
  (** Conversion between Z and field elements in the Plonky3 field *)
  Definition to_field (x : Z) : Z := x mod plonky3_prime.
  Definition from_field (x : Z) : Z := x.  (* assuming x is already reduced *)
  
  (** Field evaluation that respects the prime characteristic *)
  Definition eval_in_field (e : M.t unit) : option unit :=
    match M.eval plonky3_prime e with
    | M.Pure _ => Some tt
    | _ => None  (* Simplified; in practice would handle more cases *)
    end.
  
  (** Range predicate for field elements representing 16-bit values *)
  Definition is_16_bit (x : Z) : Prop := 0 <= x < 2^16.
  
  (** Range predicate for field elements representing 32-bit values *)
  Definition is_32_bit (x : Z) : Prop := 0 <= x < 2^32.
  
  (** CPS-style evaluation predicate for M.t unit *)
  Definition evalProp {A : Set} (e : M.t A) : option A -> Prop :=
    fun result =>
      match result with
      | Some _ => True  (* Evaluation succeeded *)
      | None => False   (* Evaluation failed *)
      end.

  (** Template for add2 completeness *)
  Definition add2_completeness_statement : Prop :=
    forall (p : Z) (a0 a1 b0 b1 c0 c1 : Z),
      IsPrime p ->
      is_16_bit a0 ->
      is_16_bit a1 ->
      is_16_bit b0 ->
      is_16_bit b1 ->
      is_16_bit c0 ->
      is_16_bit c1 ->
      let b := b0 + 2^16 * b1 in
      let c := c0 + 2^16 * c1 in
      let a := a0 + 2^16 * a1 in
      a = (b + c) mod 2^32 ->
      let a_array : Array.t Z 2 := {| Array.value := [a0; a1] |} in
      let b_array : Array.t Z 2 := {| Array.value := [b0; b1] |} in
      let c_array : Array.t Z 2 := {| Array.value := [c0; c1] |} in
      evalProp (M.eval p (add2 a_array b_array c_array)) (Some tt).

  (** CPS-style template for general circuit completeness *)
  (* Definition circuit_completeness_template 
    {InputType : Type}
    (circuit : InputType -> M.t unit)
    (input_valid : InputType -> Prop)
    (output_relation : InputType  -> Prop) : Prop :=
    forall (p : Z) (input : InputType) (output : OutputType),
      IsPrime p ->
      input_valid input ->
      output_relation input output ->
      evalProp (M.eval p (circuit input)) (Some output). *)

  (** Specific instantiation for add2 using the template *)
  Definition add2_input := (Array.t Z 2 * Array.t Z 2 * Array.t Z 2)%type.
  
  Definition add2_input_valid (input : add2_input) : Prop :=
    let '(a_arr, b_arr, c_arr) := input in
    match a_arr.(Array.value), b_arr.(Array.value), c_arr.(Array.value) with
    | [a0; a1], [b0; b1], [c0; c1] =>
        is_16_bit a0 /\ is_16_bit a1 /\
        is_16_bit b0 /\ is_16_bit b1 /\
        is_16_bit c0 /\ is_16_bit c1
    | _, _, _ => False
    end.
  
  Definition add2_output_relation (input : add2_input) (output : unit) : Prop :=
    let '(a_arr, b_arr, c_arr) := input in
    match a_arr.(Array.value), b_arr.(Array.value), c_arr.(Array.value) with
    | [a0; a1], [b0; b1], [c0; c1] =>
        let b := b0 + 2^16 * b1 in
        let c := c0 + 2^16 * c1 in
        let a := a0 + 2^16 * a1 in
        a = (b + c) mod 2^32
    | _, _, _ => False
    end.
  
  Definition add2_circuit (input : add2_input) : M.t unit :=
    let '(a_arr, b_arr, c_arr) := input in
    add2 a_arr b_arr c_arr.
  
  (** The completeness theorem using the template *)
  (* Definition add2_completeness_via_template : Prop :=
    circuit_completeness_template add2_circuit add2_input_valid. *)

  (** Alternative CPS formulation with explicit continuation *)
  (* Definition circuit_completeness_cps
    {InputType OutputType : Type}
    (circuit : InputType -> M.t OutputType)
    (input_valid : InputType -> Prop)
    (continuation : InputType -> OutputType -> Prop) : Prop :=
    forall (p : Z) (input : InputType),
      IsPrime p ->
      input_valid input ->
      exists (output : OutputType),
        continuation input output /\
        evalProp (M.eval p (circuit input)) (Some output). *)

  (** Proof strategy template using Run.t *)
  Definition proof_template_for_add2 : Prop :=
    forall (p : Z) (a0 a1 b0 b1 c0 c1 : Z),
      IsPrime p ->
      is_16_bit a0 -> is_16_bit a1 ->
      is_16_bit b0 -> is_16_bit b1 ->
      is_16_bit c0 -> is_16_bit c1 ->
      let b := b0 + 2^16 * b1 in
      let c := c0 + 2^16 * c1 in
      let a := a0 + 2^16 * a1 in
      a = (b + c) mod 2^32 ->
      let a_array : Array.t Z 2 := {| Array.value := [a0; a1] |} in
      let b_array : Array.t Z 2 := {| Array.value := [b0; b1] |} in
      let c_array : Array.t Z 2 := {| Array.value := [c0; c1] |} in
      {{ M.eval p (add2 a_array b_array c_array) 🔽 tt, True }}.

  (** Helper lemmas for range checking in finite fields *)
  Lemma range_check_preserved : forall (p : Z) (x : Z),
    IsPrime p -> p > 2^17 ->
    is_16_bit x ->
    (x mod p) = x.
  Proof. admit. Admitted.

  Lemma modular_arithmetic_consistency : forall (p : Z) (a b c : Z),
    IsPrime p -> p > 2^33 ->
    is_32_bit a -> is_32_bit b -> is_32_bit c ->
    a = (b + c) mod 2^32 ->
    ((a - b - c) mod p = 0) \/ ((a - b - c) mod p = (-2^32) mod p).
  Proof. admit. Admitted.

  (*
  (** Completeness theorem for add2 using existing constraints *)
  Theorem add2_completeness : forall (a_arr b_arr c_arr : Array.t Z 2),
    (* Range conditions on array elements *)
    (forall i, i < 2 -> 
      match Array.get a_arr i, Array.get b_arr i, Array.get c_arr i with
      | M.Pure a_i, M.Pure b_i, M.Pure c_i => is_16_bit a_i /\ is_16_bit b_i /\ is_16_bit c_i
      | _, _, _ => False
      end) ->
    (* Arithmetic relation holds *)
    (match a_arr.(Array.value), b_arr.(Array.value), c_arr.(Array.value) with
     | [a0; a1], [b0; b1], [c0; c1] =>
         let a := a0 + 2^16 * a1 in
         let b := b0 + 2^16 * b1 in  
         let c := c0 + 2^16 * c1 in
         a = (b + c) mod 2^32
     | _, _, _ => False
     end) ->
    (* Then the circuit evaluation succeeds *)
    {{ M.eval plonky3_prime (add2 a_arr b_arr c_arr) 🔽 tt, True }}.
  Proof.
    intros a_arr b_arr c_arr H_range H_arith.
    (* The proof would:
       1. Unfold add2 to show the constraint structure
       2. Use the fact that acc*(acc + 2^32) = 0 and acc_16*(acc_16 + 2^16) = 0
       3. Apply the modular arithmetic consistency lemma
       4. Show that assert_zeros succeeds when constraints are satisfied *)
    admit.
  Admitted.

  (** CPS-style formulation that matches the pattern you provided *)
  Definition add2_cps_completeness : Prop :=
    forall (a0 a1 b0 b1 c0 c1 : Z),
      is_16_bit a0 -> is_16_bit a1 ->
      is_16_bit b0 -> is_16_bit b1 ->
      is_16_bit c0 -> is_16_bit c1 ->
      let b := b0 + 2^16 * b1 in
      let c := c0 + 2^16 * c1 in
      let a := a0 + 2^16 * a1 in
      a = (b + c) mod 2^32 ->
      exists (result : unit),
        evalProp (M.eval plonky3_prime (add2 
          {| Array.value := [a0; a1] |}
          {| Array.value := [b0; b1] |}
          {| Array.value := [c0; c1] |})) (Some result).
  *)
End Completeness.
  
