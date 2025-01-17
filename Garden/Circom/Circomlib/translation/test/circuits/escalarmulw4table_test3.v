(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MainSignals.
  Record t : Set := {
    in_ : F.t;
    out : list (list F.t);
  }.
End MainSignals.

(* Template body *)
Definition Main : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ ([] : list F.t) ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 16; 2 ] ]] in
  (* Var *)
  do~ M.declare_var "base" [[ [ 2 ] ]] in
  do~ M.substitute_var "base" [[ array_with_repeat (0) (2) ]] in
  do~ M.substitute_var "base" [[ [ 5299619240641551281634865583518297030282874472190772894086521144482721001553; 16950150798460657717958625567821834550301663161624707787222815936182638968203 ] ]] in
  (* Var *)
  do~ M.declare_var "escalarMul" [[ [ 16; 2 ] ]] in
  do~ M.substitute_var "escalarMul" [[ array_with_repeat (array_with_repeat (0) (2)) (16) ]] in
  do~ M.substitute_var "escalarMul" [[ M.call_function ~(| "EscalarMulW4Table", [ M.var (| "base" |); 3 ] |) ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 16 |) ]] (
    do~ M.substitute_var "out" [[ InfixOp.mul ~(| M.var_access (| "escalarMul", [Access.Array (M.var (| "i" |)); Access.Array (0)] |), M.var (| "in" |) |) ]] in
    do~ M.substitute_var "out" [[ InfixOp.mul ~(| M.var_access (| "escalarMul", [Access.Array (M.var (| "i" |)); Access.Array (1)] |), M.var (| "in" |) |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.
