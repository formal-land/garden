Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.Util.
Require Import Garden.Plonky3.blake3.columns.
Require Import Garden.Plonky3.blake3.constants.


Definition eval (local : Blake3Cols.t Z) : M.t unit :=
  (*
    let initial_row_3 = [
      local.counter_low,
      local.counter_hi,
      local.block_len,
      local.flags,
  ];
  *)
  let initial_row_3 : Array.t (Array.t Z 32) 4 := {| 
    Array.value := [
      local.(Blake3Cols.counter_low);
      local.(Blake3Cols.counter_hi);
      local.(Blake3Cols.block_len);
      local.(Blake3Cols.flags)
      ] 
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
  (* Check that all bits in inputs are boolean *)
  let* _ := 
    for_in local.(Blake3Cols.inputs).(Array.value) (fun input_array =>
      [[ assert_bools (| input_array |) ]]
    ) in
    
  (* Check that all bits in chaining_values[0] are boolean *)
  let* chaining_values_0 := [[ Array.get (| local.(Blake3Cols.chaining_values), 0 |) ]] in
  let* _ :=
    for_in chaining_values_0.(Array.value) (fun cv_array =>
      [[ assert_bools (| cv_array |) ]]
  ) in
    
  (* Check that all bits in chaining_values[1] are boolean *)
  let* chaining_values_1 := [[ Array.get (| local.(Blake3Cols.chaining_values), 1 |) ]] in
  let* _ :=
    for_in chaining_values_1.(Array.value) (fun cv_array =>
      [[ assert_bools (| cv_array |) ]]
  ) in
    
  (* Check that all bits in initial_row_3 are boolean *)
  let* _ := 
    for_in initial_row_3.(Array.value) (fun row_array =>
      [[ assert_bools (| row_array |) ]]
    ) in
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
  (* Check that row0 contains the packing of the first 4 chaining values *)
  let* _ := 
    for_in_zero_to_n 4 (fun i =>
      (* Get the bits array and the corresponding word *)
      let* bits := [[ Array.get (| chaining_values_0, i |) ]] in
      let* word := [[ Array.get (| local.(Blake3Cols.initial_row0), i |) ]] in
      
      (* Extract the first BITS_PER_LIMB bits and the remaining bits *)
      let bits_low_list := List.firstn (Z.to_nat BITS_PER_LIMB) bits.(Array.value) in
      let bits_high_list := List.skipn (Z.to_nat BITS_PER_LIMB) bits.(Array.value) in
      
      let* low_16 := [[ pack_bits_le (| bits_low_list |) ]] in
      let* hi_16 := [[ pack_bits_le (| bits_high_list |) ]] in
      
      let* word_low := [[ Array.get (| word, 0 |) ]] in
      let* word_high := [[ Array.get (| word, 1 |) ]] in
      
      let* _ := [[ M.equal (| low_16, word_low |) ]] in
      let* _ := [[ M.equal (| hi_16, word_high |) ]] in
      
      M.Pure tt
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
  let* _ := for_in_zero_to_n 4 ( fun i => 
    let* row_elem := [[ Array.get (| local.(Blake3Cols.initial_row2), i |) ]] in
    let* constant := [[ Array.get (| IV, i |) ]] in

    let* row_elem_0 := [[ Array.get (| row_elem, 0 |) ]] in
    let* row_elem_1 := [[ Array.get (| row_elem, 1 |) ]] in
    let* constant_0 := [[ Array.get (| constant, 0 |) ]] in
    let* constant_1 := [[ Array.get (| constant, 1 |) ]] in
    let* _ := [[ M.equal (| row_elem_0, constant_0 |) ]] in
    let* _ := [[ M.equal (| row_elem_1, constant_1 |) ]] in
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
  let* m_values := 
    [[
      Array.from_fn (N := 16) (| fun i =>
        let* input := [[ Array.get (| local.(Blake3Cols.inputs), i |) ]] in
        let bits_low := List.firstn (Z.to_nat BITS_PER_LIMB) input.(Array.value) in
        let bits_high := List.skipn (Z.to_nat BITS_PER_LIMB) input.(Array.value) in
        
        let* low_packed := [[ pack_bits_le (| bits_low |) ]] in
        let* high_packed := [[ pack_bits_le (| bits_high |) ]] in
        
        M.Pure ({| Array.value := [low_packed; high_packed] |} : Array.t Z 2)
      |)
    ]] in
  
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
    Blake3State.row1 := Array.get (| local.(Blake3Cols.chaining_values), 1 |);
    Blake3State.row2 := local.(Blake3Cols.initial_row2);
    Blake3State.row3 := initial_row_3
  |} in
  
  M.Pure tt.

