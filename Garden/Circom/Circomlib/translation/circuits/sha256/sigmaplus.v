(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SigmaPlusSignals.
  Record t : Set := {
    (* Input *)
    in2 : list F.t;
    (* Input *)
    in7 : list F.t;
    (* Input *)
    in15 : list F.t;
    (* Input *)
    in16 : list F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in2 : P _ in2 "in2"
    | in7 : P _ in7 "in7"
    | in15 : P _ in15 "in15"
    | in16 : P _ in16 "in16"
    | out : P _ out "out".
  End IsNamed.
End SigmaPlusSignals.

(* Template body *)
Definition SigmaPlus : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in2" in
    (* Signal Input *)
    do~ M.declare_signal "in7" in
    (* Signal Input *)
    do~ M.declare_signal "in15" in
    (* Signal Input *)
    do~ M.declare_signal "in16" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "sigma1" in
    do~ M.substitute_var "sigma1" [] [[ M.call_function ~(| "SmallSigma", [ 17; 19; 10 ] |) ]] in
    (* Component *)
    do~ M.declare_component "sigma0" in
    do~ M.substitute_var "sigma0" [] [[ M.call_function ~(| "SmallSigma", [ 7; 18; 3 ] |) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.substitute_var "sigma1" [Access.Component "in"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "in2", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "sigma0" [Access.Component "in"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "in15", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "sum" in
    do~ M.substitute_var "sum" [] [[ M.call_function ~(| "BinSum", [ 32; 4 ] |) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.substitute_var "sum" [Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "sigma1", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "sum" [Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "in7", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "sum" [Access.Component "in"; Access.Array (2); Access.Array (M.var (| "k" |))] [[ M.var_access (| "sigma0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "sum" [Access.Component "in"; Access.Array (3); Access.Array (M.var (| "k" |))] [[ M.var_access (| "in16", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "k" |))] [[ M.var_access (| "sum", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SigmaPlus_not_under_constrained in2 in7 in15 in16 : Prop :=
  exists! out,
  let signals := SigmaPlusSignals.Build_t in2 in7 in15 in16 out in
  True (* NotUnderConstrained SigmaPlus signals *).
