(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module CompConstantSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : F.t;
    (* Intermediate *)
    parts : list F.t;
    (* Intermediate *)
    sout : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out"
    | parts : P _ parts "parts"
    | sout : P _ sout "sout".
  End IsNamed.
End CompConstantSignals.

(* Template body *)
Definition CompConstant (ct : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("ct", ct)] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "parts" in
    (* Signal Intermediate *)
    do~ M.declare_signal "sout" in
    (* Var *)
    do~ M.declare_var "clsb" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "clsb" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "cmsb" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "cmsb" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "slsb" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "slsb" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "smsb" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "smsb" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "sum" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "sum" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "b" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "b" [] [[ InfixOp.sub ~(| InfixOp.shiftL ~(| 1, 128 |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "a" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "a" [] [[ 1 ]] in
    (* Var *)
    do~ M.declare_var "e" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "e" [] [[ 1 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 127 |) ]] (
      do~ M.substitute_var "clsb" [] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "ct" |), InfixOp.mul ~(| M.var (| "i" |), 2 |) |), 1 |) ]] in
      do~ M.substitute_var "cmsb" [] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "ct" |), InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 2 |), 1 |) |), 1 |) ]] in
      do~ M.substitute_var "slsb" [] [[ M.var_access (| "in", [Access.Array (InfixOp.mul ~(| M.var (| "i" |), 2 |))] |) ]] in
      do~ M.substitute_var "smsb" [] [[ M.var_access (| "in", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 2 |), 1 |))] |) ]] in
      do~ M.if_ [[ InfixOp.boolAnd ~(| InfixOp.eq ~(| M.var (| "cmsb" |), 0 |), InfixOp.eq ~(| M.var (| "clsb" |), 0 |) |) ]] (* then *) (
        do~ M.substitute_var "parts" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.mul ~(| InfixOp.mul ~(| PrefixOp.sub ~(| M.var (| "b" |) |), M.var (| "smsb" |) |), M.var (| "slsb" |) |), InfixOp.mul ~(| M.var (| "b" |), M.var (| "smsb" |) |) |), InfixOp.mul ~(| M.var (| "b" |), M.var (| "slsb" |) |) |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.if_ [[ InfixOp.boolAnd ~(| InfixOp.eq ~(| M.var (| "cmsb" |), 0 |), InfixOp.eq ~(| M.var (| "clsb" |), 1 |) |) ]] (* then *) (
          do~ M.substitute_var "parts" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| InfixOp.sub ~(| InfixOp.add ~(| InfixOp.sub ~(| InfixOp.mul ~(| InfixOp.mul ~(| M.var (| "a" |), M.var (| "smsb" |) |), M.var (| "slsb" |) |), InfixOp.mul ~(| M.var (| "a" |), M.var (| "slsb" |) |) |), InfixOp.mul ~(| M.var (| "b" |), M.var (| "smsb" |) |) |), InfixOp.mul ~(| M.var (| "a" |), M.var (| "smsb" |) |) |), M.var (| "a" |) |) ]] in
          M.pure BlockUnit.Tt
        ) (* else *) (
          do~ M.if_ [[ InfixOp.boolAnd ~(| InfixOp.eq ~(| M.var (| "cmsb" |), 1 |), InfixOp.eq ~(| M.var (| "clsb" |), 0 |) |) ]] (* then *) (
            do~ M.substitute_var "parts" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| InfixOp.sub ~(| InfixOp.mul ~(| InfixOp.mul ~(| M.var (| "b" |), M.var (| "smsb" |) |), M.var (| "slsb" |) |), InfixOp.mul ~(| M.var (| "a" |), M.var (| "smsb" |) |) |), M.var (| "a" |) |) ]] in
            M.pure BlockUnit.Tt
          ) (* else *) (
            do~ M.substitute_var "parts" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.mul ~(| PrefixOp.sub ~(| M.var (| "a" |) |), M.var (| "smsb" |) |), M.var (| "slsb" |) |), M.var (| "a" |) |) ]] in
            M.pure BlockUnit.Tt
          ) in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "sum" [] [[ InfixOp.add ~(| M.var (| "sum" |), M.var_access (| "parts", [Access.Array (M.var (| "i" |))] |) |) ]] in
      do~ M.substitute_var "b" [] [[ InfixOp.sub ~(| M.var (| "b" |), M.var (| "e" |) |) ]] in
      do~ M.substitute_var "a" [] [[ InfixOp.add ~(| M.var (| "a" |), M.var (| "e" |) |) ]] in
      do~ M.substitute_var "e" [] [[ InfixOp.mul ~(| M.var (| "e" |), 2 |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "sout" [] [[ M.var (| "sum" |) ]] in
    (* Component *)
    do~ M.declare_component "num2bits" in
    do~ M.substitute_var "num2bits" [] [[ M.call_function ~(| "Num2Bits", [ 135 ] |) ]] in
    do~ M.substitute_var "num2bits" [Access.Component "in"] [[ M.var (| "sout" |) ]] in
    do~ M.substitute_var "out" [] [[ M.var_access (| "num2bits", [Access.Component "out"; Access.Array (127)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition CompConstant_not_under_constrained (ct : F.t) in_ : Prop :=
  exists! out,
  exists parts sout,
  let signals := CompConstantSignals.Build_t in_ out parts sout in
  True (* NotUnderConstrained CompConstant ct signals *).
