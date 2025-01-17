(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Edwards2MontgomerySignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
  }.
End Edwards2MontgomerySignals.

(* Template body *)
Definition Edwards2Montgomery : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  do~ M.substitute_var "out" [[ InfixOp.div ~(| InfixOp.add ~(| 1, M.var_access ~(| "in", [Access.Array (1)] |) |), InfixOp.sub ~(| 1, M.var_access ~(| "in", [Access.Array (1)] |) |) |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.div ~(| M.var_access ~(| "out", [Access.Array (0)] |), M.var_access ~(| "in", [Access.Array (0)] |) |) ]] in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var_access ~(| "out", [Access.Array (0)] |), InfixOp.sub ~(| 1, M.var_access ~(| "in", [Access.Array (1)] |) |) |) ]]
    [[ InfixOp.add ~(| 1, M.var_access ~(| "in", [Access.Array (1)] |) |) ]]
  in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var_access ~(| "out", [Access.Array (1)] |), M.var_access ~(| "in", [Access.Array (0)] |) |) ]]
    [[ M.var_access ~(| "out", [Access.Array (0)] |) ]]
  in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module Montgomery2EdwardsSignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
  }.
End Montgomery2EdwardsSignals.

(* Template body *)
Definition Montgomery2Edwards : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  do~ M.substitute_var "out" [[ InfixOp.div ~(| M.var_access ~(| "in", [Access.Array (0)] |), M.var_access ~(| "in", [Access.Array (1)] |) |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.div ~(| InfixOp.sub ~(| M.var_access ~(| "in", [Access.Array (0)] |), 1 |), InfixOp.add ~(| M.var_access ~(| "in", [Access.Array (0)] |), 1 |) |) ]] in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var_access ~(| "out", [Access.Array (0)] |), M.var_access ~(| "in", [Access.Array (1)] |) |) ]]
    [[ M.var_access ~(| "in", [Access.Array (0)] |) ]]
  in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var_access ~(| "out", [Access.Array (1)] |), InfixOp.add ~(| M.var_access ~(| "in", [Access.Array (0)] |), 1 |) |) ]]
    [[ InfixOp.sub ~(| M.var_access ~(| "in", [Access.Array (0)] |), 1 |) ]]
  in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module MontgomeryAddSignals.
  Record t : Set := {
    in1 : list F.t;
    in2 : list F.t;
    out : list F.t;
    lamda : F.t;
  }.
End MontgomeryAddSignals.

(* Template body *)
Definition MontgomeryAdd : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in1" [[ [ 2 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "in2" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "a" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "a" [[ 168700 ]] in
  (* Var *)
  do~ M.declare_var "d" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "d" [[ 168696 ]] in
  (* Var *)
  do~ M.declare_var "A" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "A" [[ InfixOp.div ~(| InfixOp.mul ~(| 2, InfixOp.add ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |), InfixOp.sub ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |) ]] in
  (* Var *)
  do~ M.declare_var "B" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "B" [[ InfixOp.div ~(| 4, InfixOp.sub ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "lamda" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "lamda" [[ InfixOp.div ~(| InfixOp.sub ~(| M.var_access ~(| "in2", [Access.Array (1)] |), M.var_access ~(| "in1", [Access.Array (1)] |) |), InfixOp.sub ~(| M.var_access ~(| "in2", [Access.Array (0)] |), M.var_access ~(| "in1", [Access.Array (0)] |) |) |) ]] in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var ~(| "lamda" |), InfixOp.sub ~(| M.var_access ~(| "in2", [Access.Array (0)] |), M.var_access ~(| "in1", [Access.Array (0)] |) |) |) ]]
    [[ InfixOp.sub ~(| M.var_access ~(| "in2", [Access.Array (1)] |), M.var_access ~(| "in1", [Access.Array (1)] |) |) ]]
  in
  do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.sub ~(| InfixOp.sub ~(| InfixOp.mul ~(| InfixOp.mul ~(| M.var ~(| "B" |), M.var ~(| "lamda" |) |), M.var ~(| "lamda" |) |), M.var ~(| "A" |) |), M.var_access ~(| "in1", [Access.Array (0)] |) |), M.var_access ~(| "in2", [Access.Array (0)] |) |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.mul ~(| M.var ~(| "lamda" |), InfixOp.sub ~(| M.var_access ~(| "in1", [Access.Array (0)] |), M.var_access ~(| "out", [Access.Array (0)] |) |) |), M.var_access ~(| "in1", [Access.Array (1)] |) |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module MontgomeryDoubleSignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
    lamda : F.t;
    x1_2 : F.t;
  }.
End MontgomeryDoubleSignals.

(* Template body *)
Definition MontgomeryDouble : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "a" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "a" [[ 168700 ]] in
  (* Var *)
  do~ M.declare_var "d" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "d" [[ 168696 ]] in
  (* Var *)
  do~ M.declare_var "A" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "A" [[ InfixOp.div ~(| InfixOp.mul ~(| 2, InfixOp.add ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |), InfixOp.sub ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |) ]] in
  (* Var *)
  do~ M.declare_var "B" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "B" [[ InfixOp.div ~(| 4, InfixOp.sub ~(| M.var ~(| "a" |), M.var ~(| "d" |) |) |) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "lamda" [[ ([] : list F.t) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "x1_2" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "x1_2" [[ InfixOp.mul ~(| M.var_access ~(| "in", [Access.Array (0)] |), M.var_access ~(| "in", [Access.Array (0)] |) |) ]] in
  do~ M.substitute_var "lamda" [[ InfixOp.div ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.mul ~(| 3, M.var ~(| "x1_2" |) |), InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var ~(| "A" |) |), M.var_access ~(| "in", [Access.Array (0)] |) |) |), 1 |), InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var ~(| "B" |) |), M.var_access ~(| "in", [Access.Array (1)] |) |) |) ]] in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var ~(| "lamda" |), InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var ~(| "B" |) |), M.var_access ~(| "in", [Access.Array (1)] |) |) |) ]]
    [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.mul ~(| 3, M.var ~(| "x1_2" |) |), InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var ~(| "A" |) |), M.var_access ~(| "in", [Access.Array (0)] |) |) |), 1 |) ]]
  in
  do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.sub ~(| InfixOp.mul ~(| InfixOp.mul ~(| M.var ~(| "B" |), M.var ~(| "lamda" |) |), M.var ~(| "lamda" |) |), M.var ~(| "A" |) |), InfixOp.mul ~(| 2, M.var_access ~(| "in", [Access.Array (0)] |) |) |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.mul ~(| M.var ~(| "lamda" |), InfixOp.sub ~(| M.var_access ~(| "in", [Access.Array (0)] |), M.var_access ~(| "out", [Access.Array (0)] |) |) |), M.var_access ~(| "in", [Access.Array (1)] |) |) ]] in
  M.pure BlockUnit.Tt.
