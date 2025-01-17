(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MultiMux2Signals.
  Record t : Set := {
    c : list (list F.t);
    s : list F.t;
    out : list F.t;
    a10 : list F.t;
    a1 : list F.t;
    a0 : list F.t;
    a : list F.t;
    s10 : F.t;
  }.
End MultiMux2Signals.

(* Template body *)
Definition MultiMux2 (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "c" [[ [ M.var ~(| "n" |); 4 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "s" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "a10" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "a1" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "a0" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "a" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "s10" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "s10" [[ InfixOp.mul ~(| M.var_access ~(| "s", [Access.Array (1)] |), M.var_access ~(| "s", [Access.Array (0)] |) |) ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "n" |) |) ]] (
    do~ M.substitute_var "a10" [[ InfixOp.mul ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (3)] |), M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (2)] |) |), M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (1)] |) |), M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (0)] |) |), M.var ~(| "s10" |) |) ]] in
    do~ M.substitute_var "a1" [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (2)] |), M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (0)] |) |), M.var_access ~(| "s", [Access.Array (1)] |) |) ]] in
    do~ M.substitute_var "a0" [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (1)] |), M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (0)] |) |), M.var_access ~(| "s", [Access.Array (0)] |) |) ]] in
    do~ M.substitute_var "a" [[ M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |)); Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var_access ~(| "a10", [Access.Array (M.var ~(| "i" |))] |), M.var_access ~(| "a1", [Access.Array (M.var ~(| "i" |))] |) |), M.var_access ~(| "a0", [Access.Array (M.var ~(| "i" |))] |) |), M.var_access ~(| "a", [Access.Array (M.var ~(| "i" |))] |) |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module Mux2Signals.
  Record t : Set := {
    c : list F.t;
    s : list F.t;
    out : F.t;
  }.
End Mux2Signals.

(* Template body *)
Definition Mux2 : M.t (BlockUnit.t Empty_set) :=
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Signal Input *)
  do~ M.declare_signal "c" [[ [ 4 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "s" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
  (* Component *)
  do~ M.declare_component "mux" in
  do~ M.substitute_var "mux" [[ M.call_function ~(| "MultiMux2", [ 1 ] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 4 |) ]] (
    do~ M.substitute_var "mux" [[ M.var_access ~(| "c", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 2 |) ]] (
    do~ M.substitute_var "mux" [[ M.var_access ~(| "s", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "out" [[ M.var_access ~(| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
  M.pure BlockUnit.Tt.
