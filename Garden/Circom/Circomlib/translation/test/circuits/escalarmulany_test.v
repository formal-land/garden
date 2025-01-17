(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MainSignals.
  Record t : Set := {
    e : F.t;
    p : list F.t;
    out : list F.t;
  }.
End MainSignals.

(* Template body *)
Definition Main : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "e" [[ ([] : list F.t) ]] in
  (* Signal Input *)
  do~ M.declare_signal "p" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Component *)
  do~ M.declare_component "n2b" in
  do~ M.substitute_var "n2b" [[ M.call_function ~(| "Num2Bits", [ 253 ] |) ]] in
  (* Component *)
  do~ M.declare_component "escalarMulAny" in
  do~ M.substitute_var "escalarMulAny" [[ M.call_function ~(| "EscalarMulAny", [ 253 ] |) ]] in
  do~ M.substitute_var "escalarMulAny" [[ M.var_access (| "p", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "escalarMulAny" [[ M.var_access (| "p", [Access.Array (1)] |) ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.substitute_var "n2b" [[ M.var (| "e" |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 253 |) ]] (
    do~ M.substitute_var "escalarMulAny" [[ M.var_access (| "n2b", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "out" [[ M.var_access (| "escalarMulAny", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "out" [[ M.var_access (| "escalarMulAny", [Access.Component "out"; Access.Array (1)] |) ]] in
  M.pure BlockUnit.Tt.
