(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Maj_tSignals.
  Record t : Set := {
    (* Input *)
    a : list F.t;
    (* Input *)
    b : list F.t;
    (* Input *)
    c : list F.t;
    (* Output *)
    out : list F.t;
    (* Intermediate *)
    mid : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | a : P _ a "a"
    | b : P _ b "b"
    | c : P _ c "c"
    | out : P _ out "out"
    | mid : P _ mid "mid".
  End IsNamed.
End Maj_tSignals.

(* Template body *)
Definition Maj_t (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "a" in
    (* Signal Input *)
    do~ M.declare_signal "b" in
    (* Signal Input *)
    do~ M.declare_signal "c" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "mid" in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "mid" [Access.Array (M.var (| "k" |))] [[ InfixOp.mul ~(| M.var_access (| "b", [Access.Array (M.var (| "k" |))] |), M.var_access (| "c", [Access.Array (M.var (| "k" |))] |) |) ]] in
      do~ M.substitute_var "out" [Access.Array (M.var (| "k" |))] [[ InfixOp.add ~(| InfixOp.mul ~(| M.var_access (| "a", [Access.Array (M.var (| "k" |))] |), InfixOp.sub ~(| InfixOp.add ~(| M.var_access (| "b", [Access.Array (M.var (| "k" |))] |), M.var_access (| "c", [Access.Array (M.var (| "k" |))] |) |), InfixOp.mul ~(| 2, M.var_access (| "mid", [Access.Array (M.var (| "k" |))] |) |) |) |), M.var_access (| "mid", [Access.Array (M.var (| "k" |))] |) |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Maj_t_not_under_constrained (n : F.t) a b c : Prop :=
  exists! out,
  exists mid,
  let signals := Maj_tSignals.Build_t a b c out mid in
  True (* NotUnderConstrained Maj_t n signals *).
