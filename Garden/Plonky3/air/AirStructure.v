Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Import ListNotations.
Require Export primefield.  
Open Scope Z_scope.

Module AIR (F : PrimeField).
  
  Inductive Var := 
    | LocalVar : nat -> Var 
    | NextVar : nat -> Var.  
  
  Inductive Expr :=
    | Const : Z -> Expr
    | FromVariable : Var -> Expr
    | Add : Expr -> Expr -> Expr
    | Mul : Expr -> Expr -> Expr
    | Sub : Expr -> Expr -> Expr.
  
  (* Builder type for constructing AIR constraints. Every element should evaluate to zero. *)
  Record AirBuilder := {
    constraints : list Expr;
  }.
  
  (* Basic operations on the AIR builder *)
  Definition new_builder : AirBuilder := {| constraints := [] |}.
  
  Definition assert_eq (builder : AirBuilder) (lhs rhs : Expr) : AirBuilder :=
    {| constraints := Sub lhs rhs :: builder.(constraints) |}.
    
  Definition assert_bool (builder : AirBuilder) (expr : Expr) : AirBuilder :=
    let zero := Const F.zero in
    let one := Const F.one in
    let bool_constraint := Mul expr (Sub expr one) in
    assert_eq builder bool_constraint zero.
  
  (* Pack bits as an expression *)
  Fixpoint pack_bits_le_helper (bits : list Expr) (acc : Expr) (place : nat) : Expr :=
    match bits with
    | [] => acc
    | bit :: rest =>
      let place_val := Const (F.of_nat (2^place)) in
      let term := Mul bit place_val in
      pack_bits_le_helper rest (Add acc term) (S place)
    end.
  
  Definition pack_bits_le (bits : list Expr) : Expr :=
    pack_bits_le_helper bits (Const F.zero) 0.
  
  (* Core AIR interface types *)
  Class BaseAir := {
    width : nat;  (* Width of the AIR trace *)
  }.
  
  Class AirConstraints := {
    base_air :: BaseAir;
    eval : AirBuilder -> AirBuilder;  (* Evaluate AIR constraints *)
  }.
End AIR.