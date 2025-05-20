Require Import Garden.Plonky3.M.
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
    
  M.Pure tt.