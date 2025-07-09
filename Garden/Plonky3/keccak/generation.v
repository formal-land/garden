Require Import Garden.Plonky3.MLessEffects.
Require Import Garden.Plonky3.keccak.constants.
Require Import List ZArith Nat.

Module F.
  Parameter t : Type.
  Parameter zero : t.
  Parameter one : t.
  Parameter add : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter of_Z : Z -> t.
  
  Parameter eqb : t -> t -> bool.
  Parameter ltb : t -> t -> bool.
  Parameter leb : t -> t -> bool.
End F.

Module M.
  Parameter t : Type -> Type.
  Parameter pure : forall {A : Type}, A -> M.t A.
  Parameter bind : forall {A B : Type}, M.t A -> (A -> M.t B) -> M.t B. 
  Parameter get_prime : M.t Z.
  
  Notation "let* x := a in b" := (bind a (fun x => b)) 
    (at level 200, x ident, a at level 100, b at level 200).
End M.


Parameter NUM_KECCAK_COLS : nat.
Definition KeccakInput := list Z.
Definition KeccakCols := list F.t.

Record RowMajorMatrix := {
  values : list F.t;
  num_cols : nat
}.

Module KeccakGeneration.
Open Scope nat.
  Fixpoint next_power_of_two_helper (n current : nat) (fuel : nat) : nat :=
    match fuel with
    | 0 => current 
    | S fuel' =>
        if n <=? current then current
        else next_power_of_two_helper n (current * 2) fuel'
    end.

  Definition next_power_of_two (n : nat) : nat :=
    if n =? 0 then 1
    else next_power_of_two_helper n 1 (32). 


  Definition zero_vec (length : nat) : list F.t :=
    repeat F.zero length.

  Definition div_ceil (a b : nat) : nat :=
    if b =? 0 then 0 else (a + b - 1) / b.

  Definition pad_list {A : Type} (l : list A) (default : A) (target_length : nat) : list A :=
    let current_length := length l in
    if target_length <=? current_length then l
    else l ++ repeat default (target_length - current_length).

  Parameter generate_trace_rows_for_perm : KeccakInput -> list KeccakCols.

  Definition generate_trace_rows 
    (inputs : list KeccakInput) 
    (extra_capacity_bits : nat) : RowMajorMatrix :=
    
    let num_input_rows := length inputs * (Z.to_nat NUM_ROUNDS) in
    let num_rows := next_power_of_two num_input_rows in
    let trace_length := num_rows * NUM_KECCAK_COLS in
    
    let num_permutations_needed := div_ceil num_rows (Z.to_nat NUM_ROUNDS) in
    let num_padding_inputs := num_permutations_needed - length inputs in

    let zero_input := repeat (0%Z) 25 in
    let padded_inputs := pad_list inputs zero_input num_permutations_needed in
    
    let all_traces := map generate_trace_rows_for_perm padded_inputs in
    
    let flattened_traces := concat all_traces in
    
    let all_field_elements := concat flattened_traces in
    
    let final_values := 
      let current_length := length all_field_elements in
      if current_length <? trace_length then
        all_field_elements ++ repeat F.zero (trace_length - current_length)
      else
        firstn trace_length all_field_elements in
    
    {|
      values := final_values;
      num_cols := NUM_KECCAK_COLS
    |}.

End KeccakGeneration.
