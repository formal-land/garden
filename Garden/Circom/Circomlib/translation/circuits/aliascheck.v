(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module AliasCheckSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in".
  End IsNamed.
End AliasCheckSignals.

(* Template body *)
Definition AliasCheck : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Component *)
    do~ M.declare_component "compConstant" in
    do~ M.substitute_var "compConstant" [] [[ M.call_function ~(| "CompConstant", [ PrefixOp.sub ~(| 1 |) ] |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "compConstant" [Access.Component "in"; Access.Array (M.var (| "i" |))] [[ M.var_access (| "in", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ M.var_access (| "compConstant", [Access.Component "out"] |) ]]
      [[ 0 ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition AliasCheck_not_under_constrained in_ : Prop :=
  let signals := AliasCheckSignals.Build_t in_ in
  True (* NotUnderConstrained AliasCheck signals *).
