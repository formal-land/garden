(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module T2Signals.
  Record t : Set := {
    a : list F.t;
    b : list F.t;
    c : list F.t;
    out : list F.t;
  }.
End T2Signals.

(* Template body *)
Definition T2 : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "a" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "b" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "c" [[ [ 32 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 32 ] ]] in
  (* Var *)
  do~ M.declare_var "k" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "bigsigma0" in
  do~ M.substitute_var "bigsigma0" [[ M.call_function ~(| "BigSigma", [ 2; 13; 22 ] |) ]] in
  (* Component *)
  do~ M.declare_component "maj" in
  do~ M.substitute_var "maj" [[ M.call_function ~(| "Maj_t", [ 32 ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "k" |), 32 |) ]] (
    do~ M.substitute_var "bigsigma0" [[ M.var_access ~(| "a", [Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "maj" [[ M.var_access ~(| "a", [Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "maj" [[ M.var_access ~(| "b", [Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "maj" [[ M.var_access ~(| "c", [Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var ~(| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "sum" in
  do~ M.substitute_var "sum" [[ M.call_function ~(| "BinSum", [ 32; 2 ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "k" |), 32 |) ]] (
    do~ M.substitute_var "sum" [[ M.var_access ~(| "bigsigma0", [Access.Component "out"; Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "sum" [[ M.var_access ~(| "maj", [Access.Component "out"; Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var ~(| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "k" |), 32 |) ]] (
    do~ M.substitute_var "out" [[ M.var_access ~(| "sum", [Access.Component "out"; Access.Array (M.var ~(| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var ~(| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.
