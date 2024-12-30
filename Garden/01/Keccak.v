Require Import Coq.ZArith.ZArith.

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
  Fixpoint var_two_pow (n : nat) : Variable_.t :=
    match n with
    | 0 => Variable_.one
    | S n' => Variable_.mul (Variable_.add Variable_.one Variable_.one) (var_two_pow n')
    end.

  Definition nth_or_default {A : Set} (default : A) (l : list A) (n : nat) : A :=
    List.nth n l default.

  (*
  #[macro_export]
  macro_rules! grid {
    [...]
    (20, $v:expr) => {{
        |x: usize, q: usize| $v[q + QUARTERS * x].clone()
    }};
    [...]
    (100, $v:expr) => {{
        |y: usize, x: usize, q: usize| $v[q + QUARTERS * (x + DIM * y)].clone()
    }};
    [...]
  }
  *)

  Definition grid_100 (quarters : list Variable_.t) (y x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * y)).

  Definition grid_20 (quarters : list Variable_.t) (x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * x).

  Definition from_quarters (quarters : list Variable_.t) (y : option nat) (x : nat) : option Variable_.t :=
    match y with
    | Some y' =>
      if Nat.eqb (length quarters) 100 then
        let v :=
          Variable_.add (grid_100 quarters y' x 0) (Variable_.add
            (Variable_.mul (var_two_pow 16) (grid_100 quarters y' x 1))
            (Variable_.add
            (Variable_.mul (var_two_pow 32) (grid_100 quarters y' x 2))
            (Variable_.mul (var_two_pow 48) (grid_100 quarters y' x 3)))) in Some v
      else None
    | None =>
      if length quarters =? 20 then
        let v :=
          Variable_.add (grid_20 quarters x 0) (Variable_.add
            (Variable_.mul (var_two_pow 16) (grid_20 quarters x 1))
            (Variable_.add
            (Variable_.mul (var_two_pow 32) (grid_20 quarters x 2))
            (Variable_.mul (var_two_pow 48) (grid_20 quarters x 3)))) in Some v
        else None
    end.

  Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)) :=
    let state_c := List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_d := List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_e := List.repeat (List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM) in
                
    let indices := seq 0 (Z.to_nat DIM) in
    let '(state_c, state_d, state_e) := 
      fold_left (fun self x =>
        let word_c := from_quarters (vec_dense_c) None x_z in
        let rem_c := from_quarters (vec_remainder_c) None x_z in
        let rot_c := from_quarters (vec_dense_rot_c) None x_z).
End Keccak.