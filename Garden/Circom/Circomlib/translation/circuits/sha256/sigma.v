(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SmallSigmaSignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
  }.
End SmallSigmaSignals.

(* Template body *)
Definition SmallSigma (ra rb rc : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 32 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 32 ] ]] in
  (* Var *)
  do~ M.declare_var "k" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "rota" in
  do~ M.substitute_var "rota" [[ M.call_function ~(| "RotR", [ 32; M.var (| "ra" |) ] |) ]] in
  (* Component *)
  do~ M.declare_component "rotb" in
  do~ M.substitute_var "rotb" [[ M.call_function ~(| "RotR", [ 32; M.var (| "rb" |) ] |) ]] in
  (* Component *)
  do~ M.declare_component "shrc" in
  do~ M.substitute_var "shrc" [[ M.call_function ~(| "ShR", [ 32; M.var (| "rc" |) ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "rota" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "rotb" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "shrc" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "xor3" in
  do~ M.substitute_var "xor3" [[ M.call_function ~(| "Xor3", [ 32 ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "xor3" [[ M.var_access (| "rota", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "xor3" [[ M.var_access (| "rotb", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "xor3" [[ M.var_access (| "shrc", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "out" [[ M.var_access (| "xor3", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module BigSigmaSignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
  }.
End BigSigmaSignals.

(* Template body *)
Definition BigSigma (ra rb rc : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 32 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 32 ] ]] in
  (* Var *)
  do~ M.declare_var "k" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "rota" in
  do~ M.substitute_var "rota" [[ M.call_function ~(| "RotR", [ 32; M.var (| "ra" |) ] |) ]] in
  (* Component *)
  do~ M.declare_component "rotb" in
  do~ M.substitute_var "rotb" [[ M.call_function ~(| "RotR", [ 32; M.var (| "rb" |) ] |) ]] in
  (* Component *)
  do~ M.declare_component "rotc" in
  do~ M.substitute_var "rotc" [[ M.call_function ~(| "RotR", [ 32; M.var (| "rc" |) ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "rota" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "rotb" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "rotc" [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "xor3" in
  do~ M.substitute_var "xor3" [[ M.call_function ~(| "Xor3", [ 32 ] |) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "xor3" [[ M.var_access (| "rota", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "xor3" [[ M.var_access (| "rotb", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "xor3" [[ M.var_access (| "rotc", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
    do~ M.substitute_var "out" [[ M.var_access (| "xor3", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.