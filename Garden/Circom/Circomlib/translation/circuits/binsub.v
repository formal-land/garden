(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module BinSubSignals.
  Record t : Set := {
    (* Input *)
    in_ : list (list F.t);
    (* Output *)
    out : list F.t;
    (* Intermediate *)
    aux : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out"
    | aux : P _ aux "aux".
  End IsNamed.
End BinSubSignals.

(* Template body *)
Definition BinSub (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "aux" in
    (* Var *)
    do~ M.declare_var "lin" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lin" [] [[ InfixOp.pow ~(| 2, M.var (| "n" |) |) ]] in
    (* Var *)
    do~ M.declare_var "lout" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lout" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "lin" [] [[ InfixOp.add ~(| M.var (| "lin" |), InfixOp.mul ~(| M.var_access (| "in", [Access.Array (0); Access.Array (M.var (| "i" |))] |), InfixOp.pow ~(| 2, M.var (| "i" |) |) |) |) ]] in
      do~ M.substitute_var "lin" [] [[ InfixOp.sub ~(| M.var (| "lin" |), InfixOp.mul ~(| M.var_access (| "in", [Access.Array (1); Access.Array (M.var (| "i" |))] |), InfixOp.pow ~(| 2, M.var (| "i" |) |) |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "lin" |), M.var (| "i" |) |), 1 |) ]] in
      do~ M.equality_constraint
        [[ InfixOp.mul ~(| M.var_access (| "out", [Access.Array (M.var (| "i" |))] |), InfixOp.sub ~(| M.var_access (| "out", [Access.Array (M.var (| "i" |))] |), 1 |) |) ]]
        [[ 0 ]]
      in
      do~ M.substitute_var "lout" [] [[ InfixOp.add ~(| M.var (| "lout" |), InfixOp.mul ~(| M.var_access (| "out", [Access.Array (M.var (| "i" |))] |), InfixOp.pow ~(| 2, M.var (| "i" |) |) |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "aux" [] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "lin" |), M.var (| "n" |) |), 1 |) ]] in
    do~ M.equality_constraint
      [[ InfixOp.mul ~(| M.var (| "aux" |), InfixOp.sub ~(| M.var (| "aux" |), 1 |) |) ]]
      [[ 0 ]]
    in
    do~ M.substitute_var "lout" [] [[ InfixOp.add ~(| M.var (| "lout" |), InfixOp.mul ~(| M.var (| "aux" |), InfixOp.pow ~(| 2, M.var (| "n" |) |) |) |) ]] in
    do~ M.equality_constraint
      [[ M.var (| "lin" |) ]]
      [[ M.var (| "lout" |) ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition BinSub_not_under_constrained (n : F.t) in_ : Prop :=
  exists! out,
  exists aux,
  let signals := BinSubSignals.Build_t in_ out aux in
  True (* NotUnderConstrained BinSub n signals *).
