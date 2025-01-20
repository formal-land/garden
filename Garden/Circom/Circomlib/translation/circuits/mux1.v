(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MultiMux1Signals.
  Record t : Set := {
    (* Input *)
    c : list (list F.t);
    (* Input *)
    s : F.t;
    (* Output *)
    out : list F.t;
  }.
End MultiMux1Signals.

(* Template body *)
Definition MultiMux1 (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "c" [[ [ M.var (| "n" |); 2 ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "s" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ M.var (| "n" |) ] ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var (| "s" |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition MultiMux1_not_under_constrained (n : F.t) c s : Prop :=
  exists! out,
  let signals := MultiMux1Signals.Build_t c s out in
  True (* NotUnderConstrained MultiMux1 n signals *).

(* Template signals *)
Module Mux1Signals.
  Record t : Set := {
    (* Input *)
    c : list F.t;
    (* Input *)
    s : F.t;
    (* Output *)
    out : F.t;
  }.
End Mux1Signals.

(* Template body *)
Definition Mux1 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Signal Input *)
    do~ M.declare_signal "c" [[ [ 2 ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "s" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    (* Component *)
    do~ M.declare_component "mux" in
    do~ M.substitute_var "mux" [[ M.call_function ~(| "MultiMux1", [ 1 ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 2 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "c", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "mux" [[ M.var (| "s" |) ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Mux1_not_under_constrained c s : Prop :=
  exists! out,
  let signals := Mux1Signals.Build_t c s out in
  True (* NotUnderConstrained Mux1 signals *).
