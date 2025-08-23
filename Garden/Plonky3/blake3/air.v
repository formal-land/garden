Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.Util.
Require Import Garden.Plonky3.blake3.columns.
Require Import Garden.Plonky3.blake3.constants.

Definition quarter_round_function {p} `{Prime p} (trace : QuarterRound.t Z Z) : M.t unit :=    
    (*
    let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().copied());
    let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().copied());  
    *)
    let b_bits_low := Array.slice_first trace.(QuarterRound.b) BITS_PER_LIMB in
    let b_0_16 := pack_bits_le_array b_bits_low in

    let b_bits_high := Array.slice_from trace.(QuarterRound.b) BITS_PER_LIMB in
    let b_16_32 := pack_bits_le_array b_bits_high in  


    (*
    add3(
        builder,
        trace.a_prime,
        trace.a,
        &[b_0_16, b_16_32],
        trace.m_two_i,
    );  
    *)
    let trace_a_prime := trace.(QuarterRound.a_prime) in
    let trace_a := trace.(QuarterRound.a) in
    let trace_m_two_i := trace.(QuarterRound.m_two_i) in
    let b_packed := double_val b_0_16 b_16_32 in
    let* _ := add3 trace_a_prime trace_a b_packed trace_m_two_i in

    (*
    xor_32_shift(builder, trace.a_prime, trace.d, trace.d_prime, 16);  
    *)  
    
    let trace_d := trace.(QuarterRound.d) in
    let trace_d_prime := trace.(QuarterRound.d_prime) in
    let* _ := xor_32_shift trace_a_prime trace_d trace_d_prime 16 in

    (*
        let d_output_0_16 = pack_bits_le(trace.d_output[..BITS_PER_LIMB].iter().copied());
        let d_output_16_32 = pack_bits_le(trace.d_output[BITS_PER_LIMB..].iter().copied());  
    *)    
    let d_output_bits_low := Array.slice_first trace.(QuarterRound.d_output) BITS_PER_LIMB in
    let d_output_0_16 := pack_bits_le_array d_output_bits_low in
    let d_output_bits_high := Array.slice_from trace.(QuarterRound.d_output) BITS_PER_LIMB in
    let d_output_16_32 := pack_bits_le_array d_output_bits_high in
    (*
        add2(
            builder,
            trace.c_output,
            trace.c_prime,
            &[d_output_0_16, d_output_16_32],
            );  
    *)    
    let* _ := add2 trace.(QuarterRound.c_output) trace.(QuarterRound.c_prime) (double_val d_output_0_16 d_output_16_32) in

    (*
    xor_32_shift(builder, trace.c_output, trace.b_prime, trace.b_output, 7);
    *)
    let* _ := xor_32_shift trace.(QuarterRound.c_output) trace.(QuarterRound.b_prime) trace.(QuarterRound.b_output) 7 in

    M.Pure tt.

(*
    const fn full_round_to_column_quarter_round<'a, T: Copy, U>(
        &self,
        input: &'a Blake3State<T>,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[U; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T, U> {
        QuarterRound {
            a: &input.row0[index],
            b: &input.row1[index],
            c: &input.row2[index],
            d: &input.row3[index],

            m_two_i: &m_vector[2 * index],

            a_prime: &round_data.state_prime.row0[index],
            b_prime: &round_data.state_prime.row1[index],
            c_prime: &round_data.state_prime.row2[index],
            d_prime: &round_data.state_prime.row3[index],

            m_two_i_plus_one: &m_vector[2 * index + 1],

            a_output: &round_data.state_middle.row0[index],
            b_output: &round_data.state_middle.row1[index],
            c_output: &round_data.state_middle.row2[index],
            d_output: &round_data.state_middle.row3[index],
        }
    }
*)
Definition full_round_to_column_quarter_round {p} `{Prime p}
  {T U : Set} (input : Blake3State.t T) (round_data : FullRound.t T)
  (m_vector : Array.t (Array.t U 2) 16) (index : Z)
  : QuarterRound.t T U :=
  {| QuarterRound.a := Array.get input.(Blake3State.row0) index;
     QuarterRound.b := Array.get input.(Blake3State.row1) index;
     QuarterRound.c := Array.get input.(Blake3State.row2) index;
     QuarterRound.d := Array.get input.(Blake3State.row3) index;

     QuarterRound.m_two_i := Array.get m_vector (2 * index);

     QuarterRound.a_prime := Array.get round_data.(FullRound.state_prime).(Blake3State.row0) index;
     QuarterRound.b_prime := Array.get round_data.(FullRound.state_prime).(Blake3State.row1) index;
     QuarterRound.c_prime := Array.get round_data.(FullRound.state_prime).(Blake3State.row2) index;
     QuarterRound.d_prime := Array.get round_data.(FullRound.state_prime).(Blake3State.row3) index;

     QuarterRound.m_two_i_plus_one := Array.get m_vector (2 * index + 1);

     QuarterRound.a_output := Array.get round_data.(FullRound.state_middle).(Blake3State.row0) index;
     QuarterRound.b_output := Array.get round_data.(FullRound.state_middle).(Blake3State.row1) index;
     QuarterRound.c_output := Array.get round_data.(FullRound.state_middle).(Blake3State.row2) index;
     QuarterRound.d_output := Array.get round_data.(FullRound.state_middle).(Blake3State.row3) index
  |}.

(*
    const fn full_round_to_diagonal_quarter_round<'a, T: Copy, U>(
        &self,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[U; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T, U> {
        QuarterRound {
            a: &round_data.state_middle.row0[index],
            b: &round_data.state_middle.row1[(index + 1) % 4],
            c: &round_data.state_middle.row2[(index + 2) % 4],
            d: &round_data.state_middle.row3[(index + 3) % 4],

            m_two_i: &m_vector[2 * index + 8],

            a_prime: &round_data.state_middle_prime.row0[index],
            b_prime: &round_data.state_middle_prime.row1[(index + 1) % 4],
            c_prime: &round_data.state_middle_prime.row2[(index + 2) % 4],
            d_prime: &round_data.state_middle_prime.row3[(index + 3) % 4],

            m_two_i_plus_one: &m_vector[2 * index + 9],

            a_output: &round_data.state_output.row0[index],
            b_output: &round_data.state_output.row1[(index + 1) % 4],
            c_output: &round_data.state_output.row2[(index + 2) % 4],
            d_output: &round_data.state_output.row3[(index + 3) % 4],
        }
    }
*)
Definition full_round_to_diagonal_quarter_round {p} `{Prime p}
  {T U : Set} (round_data : FullRound.t T)
  (m_vector : Array.t (Array.t U 2) 16) (index : Z)
  : QuarterRound.t T U :=
  {| QuarterRound.a := Array.get round_data.(FullRound.state_middle).(Blake3State.row0) index;
     QuarterRound.b := Array.get round_data.(FullRound.state_middle).(Blake3State.row1) ((index + 1) mod 4);
     QuarterRound.c := Array.get round_data.(FullRound.state_middle).(Blake3State.row2) ((index + 2) mod 4);
     QuarterRound.d := Array.get round_data.(FullRound.state_middle).(Blake3State.row3) ((index + 3) mod 4);

     QuarterRound.m_two_i := Array.get m_vector (2 * index + 8);

     QuarterRound.a_prime := Array.get round_data.(FullRound.state_middle_prime).(Blake3State.row0) index;
     QuarterRound.b_prime := Array.get round_data.(FullRound.state_middle_prime).(Blake3State.row1) ((index + 1) mod 4);
     QuarterRound.c_prime := Array.get round_data.(FullRound.state_middle_prime).(Blake3State.row2) ((index + 2) mod 4);
     QuarterRound.d_prime := Array.get round_data.(FullRound.state_middle_prime).(Blake3State.row3) ((index + 3) mod 4);

     QuarterRound.m_two_i_plus_one := Array.get m_vector (2 * index + 9);

     QuarterRound.a_output := Array.get round_data.(FullRound.state_output).(Blake3State.row0) index;
     QuarterRound.b_output := Array.get round_data.(FullRound.state_output).(Blake3State.row1) ((index + 1) mod 4);
     QuarterRound.c_output := Array.get round_data.(FullRound.state_output).(Blake3State.row2) ((index + 2) mod 4);
     QuarterRound.d_output := Array.get round_data.(FullRound.state_output).(Blake3State.row3) ((index + 3) mod 4)
  |}.

(* Verify a round of the Blake3 algorithm *)
Definition verify_round {p} `{Prime p}
    (state_input : Blake3State.t Z) 
    (round_data : FullRound.t Z) 
    (m_vector : Array.t (Array.t Z 2) 16) : M.t unit :=
    (*
    let trace_column_0 =
        self.full_round_to_column_quarter_round(input, round_data, m_vector, 0);
    self.quarter_round_function(builder, &trace_column_0);  
    *)
    let trace_column_0 := full_round_to_column_quarter_round state_input round_data m_vector 0 in
    let* _ := quarter_round_function trace_column_0 in
    (*
    let trace_column_1 =
        self.full_round_to_column_quarter_round(input, round_data, m_vector, 1);
    self.quarter_round_function(builder, &trace_column_1);  
    *)
    let trace_column_1 := full_round_to_column_quarter_round state_input round_data m_vector 1 in
    let* _ := quarter_round_function trace_column_1 in
    (*
    let trace_column_2 =
        self.full_round_to_column_quarter_round(input, round_data, m_vector, 2);
    self.quarter_round_function(builder, &trace_column_2);  
    *)
    let trace_column_2 := full_round_to_column_quarter_round state_input round_data m_vector 2 in
    let* _ := quarter_round_function trace_column_2 in
    (*
    let trace_column_3 =
        self.full_round_to_column_quarter_round(input, round_data, m_vector, 3);
    self.quarter_round_function(builder, &trace_column_3);  
    *)
    let trace_column_3 := full_round_to_column_quarter_round state_input round_data m_vector 3 in
    let* _ := quarter_round_function trace_column_3 in
    (*
    let trace_diagonal_0 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 0);
    self.quarter_round_function(builder, &trace_diagonal_0);  
    *)
    let trace_diagonal_0 := full_round_to_diagonal_quarter_round round_data m_vector 0 in
    let* _ := quarter_round_function trace_diagonal_0 in
    (*
    let trace_diagonal_1 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 1);
    self.quarter_round_function(builder, &trace_diagonal_1);
    *)
    let trace_diagonal_1 := full_round_to_diagonal_quarter_round round_data m_vector 1 in
    let* _ := quarter_round_function trace_diagonal_1 in
    (*
    let trace_diagonal_2 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 2);
    self.quarter_round_function(builder, &trace_diagonal_2);  
    *)
    let trace_diagonal_2 := full_round_to_diagonal_quarter_round round_data m_vector 2 in
    let* _ := quarter_round_function trace_diagonal_2 in
    (*
    let trace_diagonal_3 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 3);
    self.quarter_round_function(builder, &trace_diagonal_3);  
    *)
    let trace_diagonal_3 := full_round_to_diagonal_quarter_round round_data m_vector 3 in
    let* _ := quarter_round_function trace_diagonal_3 in
    (* end *)
    M.Pure tt.

Definition eval {p} `{Prime p} (local : Blake3Cols.t Z) : M.t unit :=
  (*
    let initial_row_3 = [
      local.counter_low,
      local.counter_hi,
      local.block_len,
      local.flags,
  ];
  *)
  let initial_row_3 : Array.t (Array.t Z 32) 4 := {| Array.get i := 
        match i with
        | 0 => local.(Blake3Cols.counter_low)
        | 1 => local.(Blake3Cols.counter_hi)
        | 2 => local.(Blake3Cols.block_len)
        | 3 => local.(Blake3Cols.flags)
        | _ => Array.placeholder 0
        end
  |} in
  (*
        local
          .inputs
          .iter()
          .chain(local.chaining_values[0].iter())
          .chain(local.chaining_values[1].iter())
          .chain(initial_row_3.iter())
          .for_each(|elem| elem.iter().for_each(|&bool| builder.assert_bool(bool)));
  *)
  let* _ := M.for_each (M.for_each (fun x => M.assert_bool x)) local.(Blake3Cols.inputs) in
  let chaining_values_0 := Array.get local.(Blake3Cols.chaining_values) 0 in
  let* _ := M.for_each (M.for_each (fun x => M.assert_bool x)) chaining_values_0 in
  let chaining_values_1 := Array.get local.(Blake3Cols.chaining_values) 1 in
  let* _ := M.for_each (M.for_each (fun x => M.assert_bool x)) chaining_values_1 in

  (*
  local.chaining_values[0]
    .iter()
    .zip(local.initial_row0)
    .for_each(|(bits, word)| {
        let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().copied());
        let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().copied());
        builder.assert_eq(low_16, word[0]);
        builder.assert_eq(hi_16, word[1]);
    });
  *)
  let initial_row_0 := local.(Blake3Cols.initial_row0) in
  let* _ :=
    M.for_in_zero_to_n 4 ( fun i =>
      let bits := Array.get chaining_values_0 i in
      let word := Array.get initial_row_0 i in
      let low_16 := pack_bits_le_array (Array.slice_first bits BITS_PER_LIMB) in
      let hi_16 := pack_bits_le_array (Array.slice_from bits BITS_PER_LIMB) in
      let* _ := M.equal low_16 (Array.get word 0) in
      let* _ := M.equal hi_16 (Array.get word 1) in
      M.pure tt
    ) in
  (*
  local
    .initial_row2
    .iter()
    .zip(IV)
    .for_each(|(row_elem, constant)| {
        builder.assert_eq(row_elem[0], AB::Expr::from_u16(constant[0]));
        builder.assert_eq(row_elem[1], AB::Expr::from_u16(constant[1]));
    });
  *)

  let* _ := M.for_in_zero_to_n 4 (fun i => 
    let row_elem := Array.get (local.(Blake3Cols.initial_row2)) i in
    let constant := Array.get IV i in

    let* _ := M.equal (Array.get row_elem 0) (UnOp.from (Array.get constant 0)) in
    let* _ := M.equal (Array.get row_elem 1) (UnOp.from (Array.get constant 1)) in
    M.Pure tt
  ) in

  (*
      let mut m_values: [[AB::Expr; 2]; 16] = local.inputs.map(|bits| {
        [
            pack_bits_le(bits[..BITS_PER_LIMB].iter().copied()),
            pack_bits_le(bits[BITS_PER_LIMB..].iter().copied()),
        ]
    });
  *) 
  let m_values := Array.map (fun bits =>
    let bits_low := Array.slice_first bits BITS_PER_LIMB in
    let bits_high := Array.slice_from bits BITS_PER_LIMB in
    double_val (pack_bits_le_array bits_low) (pack_bits_le_array bits_high)
  ) local.(Blake3Cols.inputs) in

  (*
    let initial_state = Blake3State {
        row0: local.initial_row0,
        row1: local.chaining_values[1],
        row2: local.initial_row2,
        row3: initial_row_3,
    };  
  *)
  let initial_state : Blake3State.t Z := {|
    Blake3State.row0 := local.(Blake3Cols.initial_row0);
    Blake3State.row1 := Array.get local.(Blake3Cols.chaining_values) 1;
    Blake3State.row2 := local.(Blake3Cols.initial_row2);
    Blake3State.row3 := initial_row_3
  |} in

  (* Now we can move to verifying that each of the seven rounds have been computed correctly. *)

  (*
  // Round 1:
  self.verify_round(builder, &initial_state, &local.full_rounds[0], &m_values);
  *)
  let full_round_0 := Array.get local.(Blake3Cols.full_rounds) 0 in
  let* _ := verify_round initial_state full_round_0 m_values in

  (* 
  // Permute the vector of m_values.
  permute(&mut m_values);  
  *)
  let m_values := permute m_values in

  (*
    // Round 2:
    self.verify_round(
        builder,
        &local.full_rounds[0].state_output,
        &local.full_rounds[1],
        &m_values,
    );  
  *)
  let full_round_1 := Array.get local.(Blake3Cols.full_rounds) 1 in
  let* _ := verify_round full_round_0.(FullRound.state_output) full_round_1 m_values in

  (* permute(&mut m_values); *)
  let m_values := permute m_values in
  (*
    // Round 3:
    self.verify_round(
        builder,
        &local.full_rounds[1].state_output,
        &local.full_rounds[2],
        &m_values,
    );
  *)
  let full_round_2 := Array.get local.(Blake3Cols.full_rounds) 2 in
  let* _ := verify_round full_round_1.(FullRound.state_output) full_round_2 m_values in
  (* permute(&mut m_values); *)
  let m_values := permute m_values in
  (*
    // Round 4:
    self.verify_round(
        builder,
        &local.full_rounds[2].state_output,
        &local.full_rounds[3],
        &m_values,
    );
  *)
  let full_round_3 := Array.get local.(Blake3Cols.full_rounds) 3 in
  let* _ := verify_round full_round_2.(FullRound.state_output) full_round_3 m_values in
  (* permute(&mut m_values); *)
  let m_values := permute m_values in
  (*
    // Round 5:
    self.verify_round(
        builder,
        &local.full_rounds[3].state_output,
        &local.full_rounds[4],
        &m_values,
    );
  *)
  let full_round_4 := Array.get local.(Blake3Cols.full_rounds) 4 in
  let* _ := verify_round full_round_3.(FullRound.state_output) full_round_4 m_values in
  (* permute(&mut m_values); *)
  let m_values := permute m_values in
  (*
    // Round 6:
    self.verify_round(
        builder,
        &local.full_rounds[4].state_output,
        &local.full_rounds[5],
        &m_values,
    );
  *)
  let full_round_5 := Array.get local.(Blake3Cols.full_rounds) 5 in
  let* _ := verify_round full_round_4.(FullRound.state_output) full_round_5 m_values in
  (* permute(&mut m_values); *)
  let m_values := permute m_values in
  (*
    // Round 7:
    self.verify_round(
        builder,
        &local.full_rounds[5].state_output,
        &local.full_rounds[6],
        &m_values,
    );
  *)
  let full_round_6 := Array.get local.(Blake3Cols.full_rounds) 6 in
  let* _ := verify_round full_round_5.(FullRound.state_output) full_round_6 m_values in

  (*
  local
    .final_round_helpers
    .iter()
    .zip(local.full_rounds[6].state_output.row2)
    .for_each(|(bits, word)| {
        let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().copied());
        let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().copied());
        builder.assert_eq(low_16, word[0]);
        builder.assert_eq(hi_16, word[1]);
    });
  *)
  let* _ := 
    M.for_in_zero_to_n 4 (fun i =>
      (* Get the bits array and the corresponding word *)
      let bits := Array.get local.(Blake3Cols.final_round_helpers) i in
      let word := Array.get full_round_6.(FullRound.state_output).(Blake3State.row2) i in
      (* Pack the bits into two 16-bit words *)
      let low_16 := pack_bits_le_array (Array.slice_first bits BITS_PER_LIMB) in
      let hi_16 := pack_bits_le_array (Array.slice_from bits BITS_PER_LIMB) in
      (* Assert that the packed values match the corresponding word *)
      let* _ := M.equal low_16 (Array.get word 0) in
      let* _ := M.equal hi_16 (Array.get word 1) in
      M.Pure tt
    ) in 

  (*
  local
    .final_round_helpers
    .iter()
    .chain(local.outputs[0].iter())
    .for_each(|bits| bits.iter().for_each(|&bit| builder.assert_bool(bit)));
  *)
  (* final_round_helpers *)
  let* _ := 
    M.for_each (M.for_each (fun x => M.assert_bool x)) local.(Blake3Cols.final_round_helpers) in
  (* outputs[0] *)
  let* _ := M.for_each (M.for_each (fun x => M.assert_bool x)) (Array.get local.(Blake3Cols.outputs) 0) in    
  
  (*
    // Finally we check the xor by xor'ing the output with final_round_helpers, packing the bits
    // and comparing with the words in local.full_rounds[6].state_output.row0.

    for (out_bits, left_words, right_bits) in izip!(
        local.outputs[0],
        local.full_rounds[6].state_output.row0,
        local.final_round_helpers
    ) {
        xor_32_shift(builder, &left_words, &out_bits, &right_bits, 0)
    }
  *)
  let* _ := 
    M.for_in_zero_to_n 4 (fun i => 
      let out_bits := Array.get (Array.get local.(Blake3Cols.outputs) 0) i in
      let left_words := Array.get full_round_6.(FullRound.state_output).(Blake3State.row0) i in
      let right_bits := Array.get local.(Blake3Cols.final_round_helpers) i in
      (* Perform the xor operation *)
      let* _ := xor_32_shift left_words out_bits right_bits 0 in
      M.Pure tt
    )
   in

  (*
  for (out_bits, left_bits, right_bits) in izip!(
      local.outputs[1], // [[T; 32]; 4],
      local.full_rounds[6].state_output.row1, // [[T; 32]; 4],
      local.full_rounds[6].state_output.row3   // [[T; 32]; 4],
  ) {
      // then out_bits, left_bits, right_bits are all [T; 32]
      for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
          builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
      }
  }
  *)

  let* _ := M.for_in_zero_to_n 4 (fun i => 
    let out_bits := Array.get (Array.get local.(Blake3Cols.outputs) 1) i in
    let left_bits := Array.get full_round_6.(FullRound.state_output).(Blake3State.row1) i in
    let right_bits := Array.get full_round_6.(FullRound.state_output).(Blake3State.row3) i in
    let* _ := 
      M.for_in_zero_to_n 32 (fun j =>
        let out_bit := Array.get out_bits j in
        let left_bit := Array.get left_bits j in
        let right_bit := Array.get right_bits j in
        let left_xor_right := xor left_bit right_bit in
        M.equal out_bit left_xor_right
      )
    in
    M.Pure tt
  ) in

  (*
    for (out_bits, left_bits, right_bits) in izip!(
        local.outputs[2],
        local.chaining_values[0],
        local.final_round_helpers
    ) {
        for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
            builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
        }
    }  
  *)
  let* _ := M.for_in_zero_to_n 4 (fun i => 
    let out_bits := Array.get (Array.get local.(Blake3Cols.outputs) 2) i in
    let left_bits := Array.get (Array.get local.(Blake3Cols.chaining_values) 0) i in
    let right_bits := Array.get local.(Blake3Cols.final_round_helpers) i in
    let* _ := 
      M.for_in_zero_to_n 32 (fun j =>
        let out_bit := Array.get out_bits j in
        let left_bit := Array.get left_bits j in
        let right_bit := Array.get right_bits j in
        let left_xor_right := xor left_bit right_bit in
        M.equal out_bit left_xor_right
      )
    in
    M.Pure tt
  ) in

  (*
    for (out_bits, left_bits, right_bits) in izip!(
        local.outputs[3],
        local.chaining_values[1],
        local.full_rounds[6].state_output.row3
    ) {
        for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
            builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
        }
    }
  *)
  let* _ := M.for_in_zero_to_n 4 (fun i => 
    let out_bits := Array.get (Array.get local.(Blake3Cols.outputs) 3) i in
    let left_bits := Array.get (Array.get local.(Blake3Cols.chaining_values) 1) i in
    let right_bits := Array.get full_round_6.(FullRound.state_output).(Blake3State.row3) i in
    (* For each bit in the out_bits, left_bits, and right_bits arrays *)
    let* _ := 
      M.for_in_zero_to_n 32 (fun j =>
        let out_bit := Array.get out_bits j in
        let left_bit := Array.get left_bits j in
        let right_bit := Array.get right_bits j in
        let left_xor_right := xor left_bit right_bit in
        M.equal out_bit left_xor_right
      )
    in
    M.Pure tt
  ) in  
  M.Pure tt.
