Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import ListNotations.

(*
pub const DIM: usize = 5;
pub const QUARTERS: usize = 4;
*)

Definition QUARTERS : Z := 4.
Definition DIM : Z := 3.

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

    Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)) :=
      (*
          let mut state_c = vec![vec![Self::zero(); QUARTERS]; DIM];
          let mut state_d = vec![vec![Self::zero(); QUARTERS]; DIM];
          let mut state_e = vec![vec![vec![Self::zero(); QUARTERS]; DIM]; DIM];
      *)
      let state_c := repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
      let state_d := repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
      let state_e := repeat (repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM) in
                  
End Keccak.