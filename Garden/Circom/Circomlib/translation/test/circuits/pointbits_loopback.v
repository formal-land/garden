(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MainSignals.
  Record t : Set := {
    in_ : list F.t;
  }.
End MainSignals.

(* Template body *)
Definition Main : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "p2b" in
  do~ M.substitute_var "p2b" [[ M.call_function ~(| "Point2Bits_Strict", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "b2p" in
  do~ M.substitute_var "b2p" [[ M.call_function ~(| "Bits2Point_Strict", ([] : list F.t) |) ]] in
  do~ M.substitute_var "p2b" [[ M.var_access ~(| "in", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "p2b" [[ M.var_access ~(| "in", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "b2p" [[ M.var_access ~(| "p2b", [Access.Component "out"; Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.equality_constraint
    [[ M.var_access ~(| "b2p", [Access.Component "out"; Access.Array (0)] |) ]]
    [[ M.var_access ~(| "in", [Access.Array (0)] |) ]]
  in
  do~ M.equality_constraint
    [[ M.var_access ~(| "b2p", [Access.Component "out"; Access.Array (1)] |) ]]
    [[ M.var_access ~(| "in", [Access.Array (1)] |) ]]
  in
  M.pure BlockUnit.Tt.
