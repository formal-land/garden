(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MultiMux3Signals.
  Record t : Set := {
    (* Input *)
    c : list (list F.t);
    (* Input *)
    s : list F.t;
    (* Output *)
    out : list F.t;
    (* Intermediate *)
    a210 : list F.t;
    (* Intermediate *)
    a21 : list F.t;
    (* Intermediate *)
    a20 : list F.t;
    (* Intermediate *)
    a2 : list F.t;
    (* Intermediate *)
    a10 : list F.t;
    (* Intermediate *)
    a1 : list F.t;
    (* Intermediate *)
    a0 : list F.t;
    (* Intermediate *)
    a : list F.t;
    (* Intermediate *)
    s10 : F.t;
  }.
End MultiMux3Signals.

(* Template body *)
Definition MultiMux3 (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "c" [[ [ M.var (| "n" |); 8 ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "s" [[ [ 3 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a210" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a21" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a20" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a2" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a10" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a1" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a0" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "a" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "s10" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "s10" [[ InfixOp.mul ~(| M.var_access (| "s", [Access.Array (1)] |), M.var_access (| "s", [Access.Array (0)] |) |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "a210" [[ InfixOp.mul ~(| InfixOp.sub ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (7)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (6)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (5)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (4)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (3)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var (| "s10" |) |) ]] in
      do~ M.substitute_var "a21" [[ InfixOp.mul ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (6)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (4)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (1)] |) |) ]] in
      do~ M.substitute_var "a20" [[ InfixOp.mul ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (5)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (4)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (0)] |) |) ]] in
      do~ M.substitute_var "a2" [[ InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (4)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |) ]] in
      do~ M.substitute_var "a10" [[ InfixOp.mul ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (3)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var (| "s10" |) |) ]] in
      do~ M.substitute_var "a1" [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (1)] |) |) ]] in
      do~ M.substitute_var "a0" [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (0)] |) |) ]] in
      do~ M.substitute_var "a" [[ M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) ]] in
      do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var_access (| "a210", [Access.Array (M.var (| "i" |))] |), M.var_access (| "a21", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a20", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a2", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "s", [Access.Array (2)] |) |), InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var_access (| "a10", [Access.Array (M.var (| "i" |))] |), M.var_access (| "a1", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a0", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a", [Access.Array (M.var (| "i" |))] |) |) |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition MultiMux3_not_under_constrained (n : F.t) c s : Prop :=
  exists! out,
  exists a210 a21 a20 a2 a10 a1 a0 a s10,
  let signals := MultiMux3Signals.Build_t c s out a210 a21 a20 a2 a10 a1 a0 a s10 in
  True (* NotUnderConstrained MultiMux3 n signals *).

(* Template signals *)
Module Mux3Signals.
  Record t : Set := {
    (* Input *)
    c : list F.t;
    (* Input *)
    s : list F.t;
    (* Output *)
    out : F.t;
  }.
End Mux3Signals.

(* Template body *)
Definition Mux3 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Signal Input *)
    do~ M.declare_signal "c" [[ [ 8 ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "s" [[ [ 3 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    (* Component *)
    do~ M.declare_component "mux" in
    do~ M.substitute_var "mux" [[ M.call_function ~(| "MultiMux3", [ 1 ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 8 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "c", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 3 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "s", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Mux3_not_under_constrained c s : Prop :=
  exists! out,
  let signals := Mux3Signals.Build_t c s out in
  True (* NotUnderConstrained Mux3 signals *).
