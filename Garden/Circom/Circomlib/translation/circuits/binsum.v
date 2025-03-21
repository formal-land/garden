(* Generated by Garden *)
Require Import Garden.Garden.

(* Function *)
Definition nbits (a : F.t) : M.t F.t :=
  M.function_body [("a", a)] (
    (* Var *)
    do~ M.declare_var "n" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "n" [] [[ 1 ]] in
    (* Var *)
    do~ M.declare_var "r" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "r" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| InfixOp.sub ~(| M.var (| "n" |), 1 |), M.var (| "a" |) |) ]] (
      do~ M.substitute_var "r" [] [[ InfixOp.add ~(| M.var (| "r" |), 1 |) ]] in
      do~ M.substitute_var "n" [] [[ InfixOp.mul ~(| M.var (| "n" |), 2 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.return_ [[ M.var (| "r" |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template signals *)
Module BinSumSignals.
  Record t : Set := {
    (* Input *)
    in_ : list (list F.t);
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out".
  End IsNamed.
End BinSumSignals.

(* Template body *)
Definition BinSum (n ops : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n); ("ops", ops)] (
    (* Var *)
    do~ M.declare_var "nout" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nout" [] [[ M.call_function ~(| "nbits", [ InfixOp.mul ~(| InfixOp.sub ~(| InfixOp.pow ~(| 2, M.var (| "n" |) |), 1 |), M.var (| "ops" |) |) ] |) ]] in
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "lin" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lin" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "lout" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lout" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "e2" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "e2" [] [[ 0 ]] in
    do~ M.substitute_var "e2" [] [[ 1 ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "n" |) |) ]] (
      do~ M.substitute_var "j" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "ops" |) |) ]] (
        do~ M.substitute_var "lin" [] [[ InfixOp.add ~(| M.var (| "lin" |), InfixOp.mul ~(| M.var_access (| "in", [Access.Array (M.var (| "j" |)); Access.Array (M.var (| "k" |))] |), M.var (| "e2" |) |) |) ]] in
        do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "e2" [] [[ InfixOp.add ~(| M.var (| "e2" |), M.var (| "e2" |) |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "e2" [] [[ 1 ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "nout" |) |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "k" |))] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "lin" |), M.var (| "k" |) |), 1 |) ]] in
      do~ M.equality_constraint
        [[ InfixOp.mul ~(| M.var_access (| "out", [Access.Array (M.var (| "k" |))] |), InfixOp.sub ~(| M.var_access (| "out", [Access.Array (M.var (| "k" |))] |), 1 |) |) ]]
        [[ 0 ]]
      in
      do~ M.substitute_var "lout" [] [[ InfixOp.add ~(| M.var (| "lout" |), InfixOp.mul ~(| M.var_access (| "out", [Access.Array (M.var (| "k" |))] |), M.var (| "e2" |) |) |) ]] in
      do~ M.substitute_var "e2" [] [[ InfixOp.add ~(| M.var (| "e2" |), M.var (| "e2" |) |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ M.var (| "lin" |) ]]
      [[ M.var (| "lout" |) ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition BinSum_not_under_constrained (n ops : F.t) in_ : Prop :=
  exists! out,
  let signals := BinSumSignals.Build_t in_ out in
  True (* NotUnderConstrained BinSum n ops signals *).
