(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module ConstantsSignals.
  Record t : Set := {
    (* Output *)
    out : list F.t;
  }.
End ConstantsSignals.

(* Template body *)
Definition Constants : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 16 ] ]] in
    do~ M.substitute_var "out" [[ 123 ]] in
    do~ M.substitute_var "out" [[ 456 ]] in
    do~ M.substitute_var "out" [[ 789 ]] in
    do~ M.substitute_var "out" [[ 12 ]] in
    do~ M.substitute_var "out" [[ 111 ]] in
    do~ M.substitute_var "out" [[ 222 ]] in
    do~ M.substitute_var "out" [[ 333 ]] in
    do~ M.substitute_var "out" [[ 4546 ]] in
    do~ M.substitute_var "out" [[ 134523 ]] in
    do~ M.substitute_var "out" [[ 44356 ]] in
    do~ M.substitute_var "out" [[ 15623 ]] in
    do~ M.substitute_var "out" [[ 4566 ]] in
    do~ M.substitute_var "out" [[ 1223 ]] in
    do~ M.substitute_var "out" [[ 4546 ]] in
    do~ M.substitute_var "out" [[ 4256 ]] in
    do~ M.substitute_var "out" [[ 4456 ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Constants_not_under_constrained : Prop :=
  exists! out,
  let signals := ConstantsSignals.Build_t out in
  True (* NotUnderConstrained Constants signals *).

(* Template signals *)
Module MainSignals.
  Record t : Set := {
    (* Input *)
    selector : F.t;
    (* Output *)
    out : F.t;
  }.
End MainSignals.

(* Template body *)
Definition Main : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Signal Input *)
    do~ M.declare_signal "selector" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    (* Component *)
    do~ M.declare_component "mux" in
    do~ M.substitute_var "mux" [[ M.call_function ~(| "Mux4", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "n2b" in
    do~ M.substitute_var "n2b" [[ M.call_function ~(| "Num2Bits", [ 4 ] |) ]] in
    (* Component *)
    do~ M.declare_component "cst" in
    do~ M.substitute_var "cst" [[ M.call_function ~(| "Constants", ([] : list F.t) |) ]] in
    do~ M.substitute_var "n2b" [[ M.var (| "selector" |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 4 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "n2b", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 16 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "cst", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access (| "mux", [Access.Component "out"] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Main_not_under_constrained selector : Prop :=
  exists! out,
  let signals := MainSignals.Build_t selector out in
  True (* NotUnderConstrained Main signals *).
