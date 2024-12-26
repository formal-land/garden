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
    Definition state_c : list (list Variable_.t) :=
    repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM).

  Definition state_d : list (list Variable_.t) :=
    repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM).

  Definition state_e : list (list (list Variable_.t)) :=
    repeat (repeat (repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM).

    Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)).
    Admitted.
End Keccak.