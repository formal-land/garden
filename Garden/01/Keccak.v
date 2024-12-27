Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import ListNotations.

(*
pub const DIM: usize = 5;
pub const QUARTERS: usize = 4;
*)

Definition QUARTERS : Z := 4.
Definition DIM : Z := 5.

Module Sponges.
  Parameter t : Set.
End Sponges.

Module Steps.
  Inductive t : Set :=
  | Round (n : Z)
  | Sponge (s : Sponges.t)
  .
End Steps.

Module Variable_.
  Parameter t : Set.

  Parameter add : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter one : t.
  Parameter zero : t.
End Variable_.

Module Keccak.

  Fixpoint two_pow (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * two_pow n'
  end.

  Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)) :=
    let state_c := repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_d := repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_e := repeat (repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM) in
                
    let indices := seq 0 (Z.to_nat DIM) in
    let '(state_c, state_d, state_e) := 
      fold_left (fun self x =>
        let word_c := from_quarters (vec_dense_c) None x_z in
        let rem_c := from_quarters (vec_remainder_c) None x_z in
        let rot_c := from_quarters (vec_dense_rot_c) None x_z).
      
End Keccak.