(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module T1Signals.
  Record t : Set := {
    h : list F.t;
    e : list F.t;
    f : list F.t;
    g : list F.t;
    k : list F.t;
    w : list F.t;
    out : list F.t;
  }.
End T1Signals.

(* Template body *)
Definition T1 : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "h" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "e" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "f" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "g" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "k" [[ [ 32 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "w" [[ [ 32 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 32 ] ]] in
  (* Var *)
  do~ M.declare_var "ki" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "ki" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "ch" in
  do~ M.substitute_var "ch" [[ M.call_function ~(| "Ch_t", [ 32 ] |) ]] in
  (* Component *)
  do~ M.declare_component "bigsigma1" in
  do~ M.substitute_var "bigsigma1" [[ M.call_function ~(| "BigSigma", [ 6; 11; 25 ] |) ]] in
  do~ M.substitute_var "ki" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "ki" |), 32 |) ]] (
    do~ M.substitute_var "bigsigma1" [[ M.var_access (| "e", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ch" [[ M.var_access (| "e", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ch" [[ M.var_access (| "f", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ch" [[ M.var_access (| "g", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ki" [[ InfixOp.add ~(| M.var (| "ki" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "sum" in
  do~ M.substitute_var "sum" [[ M.call_function ~(| "BinSum", [ 32; 5 ] |) ]] in
  do~ M.substitute_var "ki" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "ki" |), 32 |) ]] (
    do~ M.substitute_var "sum" [[ M.var_access (| "h", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "sum" [[ M.var_access (| "bigsigma1", [Access.Component "out"; Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "sum" [[ M.var_access (| "ch", [Access.Component "out"; Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "sum" [[ M.var_access (| "k", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "sum" [[ M.var_access (| "w", [Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ki" [[ InfixOp.add ~(| M.var (| "ki" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "ki" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "ki" |), 32 |) ]] (
    do~ M.substitute_var "out" [[ M.var_access (| "sum", [Access.Component "out"; Access.Array (M.var (| "ki" |))] |) ]] in
    do~ M.substitute_var "ki" [[ InfixOp.add ~(| M.var (| "ki" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.