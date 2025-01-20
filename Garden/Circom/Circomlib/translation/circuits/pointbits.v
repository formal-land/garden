(* Generated by Garden *)
Require Import Garden.Garden.

(* Function *)
Definition sqrt (n : F.t) : M.t F.t :=
  M.function_body [("n", n)] (
    do~ M.if_ [[ InfixOp.eq ~(| M.var (| "n" |), 0 |) ]] (* then *) (
      do~ M.return_ [[ 0 ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      M.pure BlockUnit.Tt
    ) in
    (* Var *)
    do~ M.declare_var "res" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "res" [[ InfixOp.pow ~(| M.var (| "n" |), InfixOp.shiftR ~(| PrefixOp.sub ~(| 1 |), 1 |) |) ]] in
    do~ M.if_ [[ InfixOp.notEq ~(| M.var (| "res" |), 1 |) ]] (* then *) (
      do~ M.return_ [[ 0 ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      M.pure BlockUnit.Tt
    ) in
    (* Var *)
    do~ M.declare_var "m" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "m" [[ 28 ]] in
    (* Var *)
    do~ M.declare_var "c" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "c" [[ 19103219067921713944291392827692070036145651957329286315305642004821462161904 ]] in
    (* Var *)
    do~ M.declare_var "t" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "t" [[ InfixOp.pow ~(| M.var (| "n" |), 81540058820840996586704275553141814055101440848469862132140264610111 |) ]] in
    (* Var *)
    do~ M.declare_var "r" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "r" [[ InfixOp.pow ~(| M.var (| "n" |), InfixOp.shiftR ~(| InfixOp.add ~(| 81540058820840996586704275553141814055101440848469862132140264610111, 1 |), 1 |) |) ]] in
    (* Var *)
    do~ M.declare_var "sq" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "sq" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "b" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "b" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [[ 0 ]] in
    do~ M.while [[ InfixOp.boolAnd ~(| InfixOp.notEq ~(| M.var (| "r" |), 0 |), InfixOp.notEq ~(| M.var (| "t" |), 1 |) |) ]] (
      do~ M.substitute_var "sq" [[ InfixOp.mul ~(| M.var (| "t" |), M.var (| "t" |) |) ]] in
      do~ M.substitute_var "i" [[ 1 ]] in
      do~ M.while [[ InfixOp.notEq ~(| M.var (| "sq" |), 1 |) ]] (
        do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
        do~ M.substitute_var "sq" [[ InfixOp.mul ~(| M.var (| "sq" |), M.var (| "sq" |) |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "b" [[ M.var (| "c" |) ]] in
      do~ M.substitute_var "j" [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), InfixOp.sub ~(| InfixOp.sub ~(| M.var (| "m" |), M.var (| "i" |) |), 1 |) |) ]] (
        do~ M.substitute_var "b" [[ InfixOp.mul ~(| M.var (| "b" |), M.var (| "b" |) |) ]] in
        do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "m" [[ M.var (| "i" |) ]] in
      do~ M.substitute_var "c" [[ InfixOp.mul ~(| M.var (| "b" |), M.var (| "b" |) |) ]] in
      do~ M.substitute_var "t" [[ InfixOp.mul ~(| M.var (| "t" |), M.var (| "c" |) |) ]] in
      do~ M.substitute_var "r" [[ InfixOp.mul ~(| M.var (| "r" |), M.var (| "b" |) |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.if_ [[ InfixOp.lesser ~(| M.var (| "r" |), 0 |) ]] (* then *) (
      do~ M.substitute_var "r" [[ PrefixOp.sub ~(| M.var (| "r" |) |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      M.pure BlockUnit.Tt
    ) in
    do~ M.return_ [[ M.var (| "r" |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template signals *)
Module Bits2PointSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.
End Bits2PointSignals.

(* Template body *)
Definition Bits2Point : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ 256 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 2 ] ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Bits2Point_not_under_constrained in_ : Prop :=
  exists! out,
  let signals := Bits2PointSignals.Build_t in_ out in
  True (* NotUnderConstrained Bits2Point signals *).

(* Template signals *)
Module Bits2Point_StrictSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.
End Bits2Point_StrictSignals.

(* Template body *)
Definition Bits2Point_Strict : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ 256 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 2 ] ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "aliasCheckY" in
    do~ M.substitute_var "aliasCheckY" [[ M.call_function ~(| "AliasCheck", ([] : list F.t) |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "aliasCheckY" [[ M.var_access (| "in", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ M.var_access (| "in", [Access.Array (254)] |) ]]
      [[ 0 ]]
    in
    (* Component *)
    do~ M.declare_component "b2nY" in
    do~ M.substitute_var "b2nY" [[ M.call_function ~(| "Bits2Num", [ 254 ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "b2nY" [[ M.var_access (| "in", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access (| "b2nY", [Access.Component "out"] |) ]] in
    (* Var *)
    do~ M.declare_var "a" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "a" [[ 168700 ]] in
    (* Var *)
    do~ M.declare_var "d" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "d" [[ 168696 ]] in
    (* Var *)
    do~ M.declare_var "y2" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "y2" [[ InfixOp.mul ~(| M.var_access (| "out", [Access.Array (1)] |), M.var_access (| "out", [Access.Array (1)] |) |) ]] in
    (* Var *)
    do~ M.declare_var "x" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "x" [[ M.call_function ~(| "sqrt", [ InfixOp.div ~(| InfixOp.sub ~(| 1, M.var (| "y2" |) |), InfixOp.sub ~(| M.var (| "a" |), InfixOp.mul ~(| M.var (| "d" |), M.var (| "y2" |) |) |) |) ] |) ]] in
    do~ M.if_ [[ InfixOp.eq ~(| M.var_access (| "in", [Access.Array (255)] |), 1 |) ]] (* then *) (
      do~ M.substitute_var "x" [[ PrefixOp.sub ~(| M.var (| "x" |) |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var (| "x" |) ]] in
    (* Component *)
    do~ M.declare_component "babyCheck" in
    do~ M.substitute_var "babyCheck" [[ M.call_function ~(| "BabyCheck", ([] : list F.t) |) ]] in
    do~ M.substitute_var "babyCheck" [[ M.var_access (| "out", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "babyCheck" [[ M.var_access (| "out", [Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "n2bX" in
    do~ M.substitute_var "n2bX" [[ M.call_function ~(| "Num2Bits", [ 254 ] |) ]] in
    do~ M.substitute_var "n2bX" [[ M.var_access (| "out", [Access.Array (0)] |) ]] in
    (* Component *)
    do~ M.declare_component "aliasCheckX" in
    do~ M.substitute_var "aliasCheckX" [[ M.call_function ~(| "AliasCheck", ([] : list F.t) |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "aliasCheckX" [[ M.var_access (| "n2bX", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "signCalc" in
    do~ M.substitute_var "signCalc" [[ M.call_function ~(| "CompConstant", [ 10944121435919637611123202872628637544274182200208017171849102093287904247808 ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "signCalc" [[ M.var_access (| "n2bX", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ M.var_access (| "signCalc", [Access.Component "out"] |) ]]
      [[ M.var_access (| "in", [Access.Array (255)] |) ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Bits2Point_Strict_not_under_constrained in_ : Prop :=
  exists! out,
  let signals := Bits2Point_StrictSignals.Build_t in_ out in
  True (* NotUnderConstrained Bits2Point_Strict signals *).

(* Template signals *)
Module Point2BitsSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.
End Point2BitsSignals.

(* Template body *)
Definition Point2Bits : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ 2 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 256 ] ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Point2Bits_not_under_constrained in_ : Prop :=
  exists! out,
  let signals := Point2BitsSignals.Build_t in_ out in
  True (* NotUnderConstrained Point2Bits signals *).

(* Template signals *)
Module Point2Bits_StrictSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.
End Point2Bits_StrictSignals.

(* Template body *)
Definition Point2Bits_Strict : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ 2 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 256 ] ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "n2bX" in
    do~ M.substitute_var "n2bX" [[ M.call_function ~(| "Num2Bits", [ 254 ] |) ]] in
    do~ M.substitute_var "n2bX" [[ M.var_access (| "in", [Access.Array (0)] |) ]] in
    (* Component *)
    do~ M.declare_component "n2bY" in
    do~ M.substitute_var "n2bY" [[ M.call_function ~(| "Num2Bits", [ 254 ] |) ]] in
    do~ M.substitute_var "n2bY" [[ M.var_access (| "in", [Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "aliasCheckX" in
    do~ M.substitute_var "aliasCheckX" [[ M.call_function ~(| "AliasCheck", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "aliasCheckY" in
    do~ M.substitute_var "aliasCheckY" [[ M.call_function ~(| "AliasCheck", ([] : list F.t) |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "aliasCheckX" [[ M.var_access (| "n2bX", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "aliasCheckY" [[ M.var_access (| "n2bY", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "signCalc" in
    do~ M.substitute_var "signCalc" [[ M.call_function ~(| "CompConstant", [ 10944121435919637611123202872628637544274182200208017171849102093287904247808 ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "signCalc" [[ M.var_access (| "n2bX", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 254 |) ]] (
      do~ M.substitute_var "out" [[ M.var_access (| "n2bY", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ 0 ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "signCalc", [Access.Component "out"] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Point2Bits_Strict_not_under_constrained in_ : Prop :=
  exists! out,
  let signals := Point2Bits_StrictSignals.Build_t in_ out in
  True (* NotUnderConstrained Point2Bits_Strict signals *).
