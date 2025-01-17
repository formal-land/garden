(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module ASignals.
  Record t : Set := {
    in_ : F.t;
  }.
End ASignals.

(* Template body *)
Definition A : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ ([] : list F.t) ]] in
  (* Component *)
  do~ M.declare_component "h0" in
  do~ M.substitute_var "h0" [[ M.call_function ~(| "K", [ 8 ] |) ]] in
  (* Var *)
  do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "lc" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "e" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "e" [[ 1 ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 32 |) ]] (
    do~ M.substitute_var "lc" [[ InfixOp.add ~(| M.var ~(| "lc" |), InfixOp.mul ~(| M.var ~(| "e" |), M.var_access ~(| "h0", [Access.Component "out"; Access.Array (M.var ~(| "i" |))] |) |) |) ]] in
    do~ M.substitute_var "e" [[ InfixOp.mul ~(| M.var ~(| "e" |), 2 |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.equality_constraint
    [[ M.var ~(| "lc" |) ]]
    [[ M.var ~(| "in" |) ]]
  in
  M.pure BlockUnit.Tt.
