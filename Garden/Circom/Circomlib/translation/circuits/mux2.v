(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MultiMux2Signals.
  Record t : Set := {
    (* Input *)
    c : list (list F.t);
    (* Input *)
    s : list F.t;
    (* Output *)
    out : list F.t;
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

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | c : P _ c "c"
    | s : P _ s "s"
    | out : P _ out "out"
    | a10 : P _ a10 "a10"
    | a1 : P _ a1 "a1"
    | a0 : P _ a0 "a0"
    | a : P _ a "a"
    | s10 : P _ s10 "s10".
  End IsNamed.
End MultiMux2Signals.

(* Template body *)
Definition MultiMux2 (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "c" in
    (* Signal Input *)
    do~ M.declare_signal "s" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "a10" in
    (* Signal Intermediate *)
    do~ M.declare_signal "a1" in
    (* Signal Intermediate *)
    do~ M.declare_signal "a0" in
    (* Signal Intermediate *)
    do~ M.declare_signal "a" in
    (* Signal Intermediate *)
    do~ M.declare_signal "s10" in
    do~ M.substitute_var "s10" [] [[ InfixOp.mul ~(| M.var_access (| "s", [Access.Array (1)] |), M.var_access (| "s", [Access.Array (0)] |) |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "a10" [Access.Array (M.var (| "i" |))] [[ InfixOp.mul ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (3)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |) |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var (| "s10" |) |) ]] in
      do~ M.substitute_var "a1" [Access.Array (M.var (| "i" |))] [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (2)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (1)] |) |) ]] in
      do~ M.substitute_var "a0" [Access.Array (M.var (| "i" |))] [[ InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (1)] |), M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) |), M.var_access (| "s", [Access.Array (0)] |) |) ]] in
      do~ M.substitute_var "a" [Access.Array (M.var (| "i" |))] [[ M.var_access (| "c", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) ]] in
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var_access (| "a10", [Access.Array (M.var (| "i" |))] |), M.var_access (| "a1", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a0", [Access.Array (M.var (| "i" |))] |) |), M.var_access (| "a", [Access.Array (M.var (| "i" |))] |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition MultiMux2_not_under_constrained (n : F.t) c s : Prop :=
  exists! out,
  exists a10 a1 a0 a s10,
  let signals := MultiMux2Signals.Build_t c s out a10 a1 a0 a s10 in
  True (* NotUnderConstrained MultiMux2 n signals *).

(* Template signals *)
Module Mux2Signals.
  Record t : Set := {
    (* Input *)
    c : list F.t;
    (* Input *)
    s : list F.t;
    (* Output *)
    out : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | c : P _ c "c"
    | s : P _ s "s"
    | out : P _ out "out".
  End IsNamed.
End Mux2Signals.

(* Template body *)
Definition Mux2 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Signal Input *)
    do~ M.declare_signal "c" in
    (* Signal Input *)
    do~ M.declare_signal "s" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Component *)
    do~ M.declare_component "mux" in
    do~ M.substitute_var "mux" [] [[ M.call_function ~(| "MultiMux2", [ 1 ] |) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 4 |) ]] (
      do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (M.var (| "i" |))] [[ M.var_access (| "c", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 2 |) ]] (
      do~ M.substitute_var "mux" [Access.Component "s"; Access.Array (M.var (| "i" |))] [[ M.var_access (| "s", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [] [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Mux2_not_under_constrained c s : Prop :=
  exists! out,
  let signals := Mux2Signals.Build_t c s out in
  True (* NotUnderConstrained Mux2 signals *).
