
(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module EdDSAVerifierSignals.
  Record t : Set := {
    msg : list F.t;
    A : list F.t;
    R8 : list F.t;
    S : list F.t;
    Ax : F.t;
    Ay : F.t;
    R8x : F.t;
    R8y : F.t;
  }.
End EdDSAVerifierSignals.

(* Template body *)
Definition EdDSAVerifier (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "msg" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "A" [[ [ 256 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "R8" [[ [ 256 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "S" [[ [ 256 ] ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "Ax" [[ ([] : list F.t) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "Ay" [[ ([] : list F.t) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "R8x" [[ ([] : list F.t) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "R8y" [[ ([] : list F.t) ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "compConstant" in
  do~ M.substitute_var "compConstant" [[ M.call_function ~(| "CompConstant", [ 2736030358979909402780800718157159386076813972158567259200215660948447373040 ] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 254 |) ]] (
    do~ M.substitute_var "compConstant" [[ M.var_access ~(| "S", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.equality_constraint
    [[ M.var_access ~(| "compConstant", [Access.Component "out"] |) ]]
    [[ 0 ]]
  in
  do~ M.equality_constraint
    [[ M.var_access ~(| "S", [Access.Array (254)] |) ]]
    [[ 0 ]]
  in
  do~ M.equality_constraint
    [[ M.var_access ~(| "S", [Access.Array (255)] |) ]]
    [[ 0 ]]
  in
  (* Component *)
  do~ M.declare_component "bits2pointA" in
  do~ M.substitute_var "bits2pointA" [[ M.call_function ~(| "Bits2Point_Strict", ([] : list F.t) |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "bits2pointA" [[ M.var_access ~(| "A", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "Ax" [[ M.var_access ~(| "bits2pointA", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "Ay" [[ M.var_access ~(| "bits2pointA", [Access.Component "out"; Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "bits2pointR8" in
  do~ M.substitute_var "bits2pointR8" [[ M.call_function ~(| "Bits2Point_Strict", ([] : list F.t) |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "bits2pointR8" [[ M.var_access ~(| "R8", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "R8x" [[ M.var_access ~(| "bits2pointR8", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "R8y" [[ M.var_access ~(| "bits2pointR8", [Access.Component "out"; Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "hash" in
  do~ M.substitute_var "hash" [[ M.call_function ~(| "Pedersen", [ InfixOp.add ~(| 512, M.var ~(| "n" |) |) ] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "hash" [[ M.var_access ~(| "R8", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "hash" [[ M.var_access ~(| "A", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "n" |) |) ]] (
    do~ M.substitute_var "hash" [[ M.var_access ~(| "msg", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "point2bitsH" in
  do~ M.substitute_var "point2bitsH" [[ M.call_function ~(| "Point2Bits_Strict", ([] : list F.t) |) ]] in
  do~ M.substitute_var "point2bitsH" [[ M.var_access ~(| "hash", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "point2bitsH" [[ M.var_access ~(| "hash", [Access.Component "out"; Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "dbl1" in
  do~ M.substitute_var "dbl1" [[ M.call_function ~(| "BabyDbl", ([] : list F.t) |) ]] in
  do~ M.substitute_var "dbl1" [[ M.var ~(| "Ax" |) ]] in
  do~ M.substitute_var "dbl1" [[ M.var ~(| "Ay" |) ]] in
  (* Component *)
  do~ M.declare_component "dbl2" in
  do~ M.substitute_var "dbl2" [[ M.call_function ~(| "BabyDbl", ([] : list F.t) |) ]] in
  do~ M.substitute_var "dbl2" [[ M.var_access ~(| "dbl1", [Access.Component "xout"] |) ]] in
  do~ M.substitute_var "dbl2" [[ M.var_access ~(| "dbl1", [Access.Component "yout"] |) ]] in
  (* Component *)
  do~ M.declare_component "dbl3" in
  do~ M.substitute_var "dbl3" [[ M.call_function ~(| "BabyDbl", ([] : list F.t) |) ]] in
  do~ M.substitute_var "dbl3" [[ M.var_access ~(| "dbl2", [Access.Component "xout"] |) ]] in
  do~ M.substitute_var "dbl3" [[ M.var_access ~(| "dbl2", [Access.Component "yout"] |) ]] in
  (* Component *)
  do~ M.declare_component "isZero" in
  do~ M.substitute_var "isZero" [[ M.call_function ~(| "IsZero", ([] : list F.t) |) ]] in
  do~ M.substitute_var "isZero" [[ M.var_access ~(| "dbl3", [Access.Component "x"] |) ]] in
  do~ M.equality_constraint
    [[ M.var_access ~(| "isZero", [Access.Component "out"] |) ]]
    [[ 0 ]]
  in
  (* Component *)
  do~ M.declare_component "mulAny" in
  do~ M.substitute_var "mulAny" [[ M.call_function ~(| "EscalarMulAny", [ 256 ] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "mulAny" [[ M.var_access ~(| "point2bitsH", [Access.Component "out"; Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "mulAny" [[ M.var_access ~(| "dbl3", [Access.Component "xout"] |) ]] in
  do~ M.substitute_var "mulAny" [[ M.var_access ~(| "dbl3", [Access.Component "yout"] |) ]] in
  (* Component *)
  do~ M.declare_component "addRight" in
  do~ M.substitute_var "addRight" [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
  do~ M.substitute_var "addRight" [[ M.var ~(| "R8x" |) ]] in
  do~ M.substitute_var "addRight" [[ M.var ~(| "R8y" |) ]] in
  do~ M.substitute_var "addRight" [[ M.var_access ~(| "mulAny", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "addRight" [[ M.var_access ~(| "mulAny", [Access.Component "out"; Access.Array (1)] |) ]] in
  (* Var *)
  do~ M.declare_var "BASE8" [[ [ 2 ] ]] in
  do~ M.substitute_var "BASE8" [[ array_with_repeat (0) (2) ]] in
  do~ M.substitute_var "BASE8" [[ [ 5299619240641551281634865583518297030282874472190772894086521144482721001553; 16950150798460657717958625567821834550301663161624707787222815936182638968203 ] ]] in
  (* Component *)
  do~ M.declare_component "mulFix" in
  do~ M.substitute_var "mulFix" [[ M.call_function ~(| "EscalarMulFix", [ 256; M.var ~(| "BASE8" |) ] |) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), 256 |) ]] (
    do~ M.substitute_var "mulFix" [[ M.var_access ~(| "S", [Access.Array (M.var ~(| "i" |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.equality_constraint
    [[ M.var_access ~(| "mulFix", [Access.Component "out"; Access.Array (0)] |) ]]
    [[ M.var_access ~(| "addRight", [Access.Component "xout"] |) ]]
  in
  do~ M.equality_constraint
    [[ M.var_access ~(| "mulFix", [Access.Component "out"; Access.Array (1)] |) ]]
    [[ M.var_access ~(| "addRight", [Access.Component "yout"] |) ]]
  in
  M.pure BlockUnit.Tt.