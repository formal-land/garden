(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SMTVerifierSignals.
  Record t : Set := {
    (* Input *)
    enabled : F.t;
    (* Input *)
    root : F.t;
    (* Input *)
    siblings : list F.t;
    (* Input *)
    oldKey : F.t;
    (* Input *)
    oldValue : F.t;
    (* Input *)
    isOld0 : F.t;
    (* Input *)
    key : F.t;
    (* Input *)
    value : F.t;
    (* Input *)
    fnc : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | enabled : P _ enabled "enabled"
    | root : P _ root "root"
    | siblings : P _ siblings "siblings"
    | oldKey : P _ oldKey "oldKey"
    | oldValue : P _ oldValue "oldValue"
    | isOld0 : P _ isOld0 "isOld0"
    | key : P _ key "key"
    | value : P _ value "value"
    | fnc : P _ fnc "fnc".
  End IsNamed.
End SMTVerifierSignals.

(* Template body *)
Definition SMTVerifier (nLevels : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("nLevels", nLevels)] (
    (* Signal Input *)
    do~ M.declare_signal "enabled" in
    (* Signal Input *)
    do~ M.declare_signal "root" in
    (* Signal Input *)
    do~ M.declare_signal "siblings" in
    (* Signal Input *)
    do~ M.declare_signal "oldKey" in
    (* Signal Input *)
    do~ M.declare_signal "oldValue" in
    (* Signal Input *)
    do~ M.declare_signal "isOld0" in
    (* Signal Input *)
    do~ M.declare_signal "key" in
    (* Signal Input *)
    do~ M.declare_signal "value" in
    (* Signal Input *)
    do~ M.declare_signal "fnc" in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "hash1Old" in
    do~ M.substitute_var "hash1Old" [] [[ M.call_function ~(| "SMTHash1", ([] : list F.t) |) ]] in
    do~ M.substitute_var "hash1Old" [Access.Component "key"] [[ M.var (| "oldKey" |) ]] in
    do~ M.substitute_var "hash1Old" [Access.Component "value"] [[ M.var (| "oldValue" |) ]] in
    (* Component *)
    do~ M.declare_component "hash1New" in
    do~ M.substitute_var "hash1New" [] [[ M.call_function ~(| "SMTHash1", ([] : list F.t) |) ]] in
    do~ M.substitute_var "hash1New" [Access.Component "key"] [[ M.var (| "key" |) ]] in
    do~ M.substitute_var "hash1New" [Access.Component "value"] [[ M.var (| "value" |) ]] in
    (* Component *)
    do~ M.declare_component "n2bOld" in
    do~ M.substitute_var "n2bOld" [] [[ M.call_function ~(| "Num2Bits_strict", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "n2bNew" in
    do~ M.substitute_var "n2bNew" [] [[ M.call_function ~(| "Num2Bits_strict", ([] : list F.t) |) ]] in
    do~ M.substitute_var "n2bOld" [Access.Component "in"] [[ M.var (| "oldKey" |) ]] in
    do~ M.substitute_var "n2bNew" [Access.Component "in"] [[ M.var (| "key" |) ]] in
    (* Component *)
    do~ M.declare_component "smtLevIns" in
    do~ M.substitute_var "smtLevIns" [] [[ M.call_function ~(| "SMTLevIns", [ M.var (| "nLevels" |) ] |) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nLevels" |) |) ]] (
      do~ M.substitute_var "smtLevIns" [Access.Component "siblings"; Access.Array (M.var (| "i" |))] [[ M.var_access (| "siblings", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "smtLevIns" [Access.Component "enabled"] [[ M.var (| "enabled" |) ]] in
    (* Component *)
    do~ M.declare_component "sm" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nLevels" |) |) ]] (
      do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "SMTVerifierSM", ([] : list F.t) |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_top"] [[ M.var (| "enabled" |) ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_i0"] [[ 0 ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_inew"] [[ 0 ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_iold"] [[ 0 ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_na"] [[ InfixOp.sub ~(| 1, M.var (| "enabled" |) |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_top"] [[ M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "st_top"] |) ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_i0"] [[ M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "st_i0"] |) ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_inew"] [[ M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "st_inew"] |) ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_iold"] [[ M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "st_iold"] |) ]] in
        do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "prev_na"] [[ M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "st_na"] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "is0"] [[ M.var (| "isOld0" |) ]] in
      do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "fnc"] [[ M.var (| "fnc" |) ]] in
      do~ M.substitute_var "sm" [Access.Array (M.var (| "i" |)); Access.Component "levIns"] [[ M.var_access (| "smtLevIns", [Access.Component "levIns"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "nLevels" |), 1 |)); Access.Component "st_na"] |), M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "nLevels" |), 1 |)); Access.Component "st_iold"] |) |), M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "nLevels" |), 1 |)); Access.Component "st_inew"] |) |), M.var_access (| "sm", [Access.Array (InfixOp.sub ~(| M.var (| "nLevels" |), 1 |)); Access.Component "st_i0"] |) |) ]]
      [[ 1 ]]
    in
    (* Component *)
    do~ M.declare_component "levels" in
    do~ M.substitute_var "i" [] [[ InfixOp.sub ~(| M.var (| "nLevels" |), 1 |) ]] in
    do~ M.while [[ InfixOp.notEq ~(| M.var (| "i" |), PrefixOp.sub ~(| 1 |) |) ]] (
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "SMTVerifierLevel", ([] : list F.t) |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "st_top"] [[ M.var_access (| "sm", [Access.Array (M.var (| "i" |)); Access.Component "st_top"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "st_i0"] [[ M.var_access (| "sm", [Access.Array (M.var (| "i" |)); Access.Component "st_i0"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "st_inew"] [[ M.var_access (| "sm", [Access.Array (M.var (| "i" |)); Access.Component "st_inew"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "st_iold"] [[ M.var_access (| "sm", [Access.Array (M.var (| "i" |)); Access.Component "st_iold"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "st_na"] [[ M.var_access (| "sm", [Access.Array (M.var (| "i" |)); Access.Component "st_na"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "sibling"] [[ M.var_access (| "siblings", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "old1leaf"] [[ M.var_access (| "hash1Old", [Access.Component "out"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "new1leaf"] [[ M.var_access (| "hash1New", [Access.Component "out"] |) ]] in
      do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "lrbit"] [[ M.var_access (| "n2bNew", [Access.Component "out"; Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), InfixOp.sub ~(| M.var (| "nLevels" |), 1 |) |) ]] (* then *) (
        do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "child"] [[ 0 ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "levels" [Access.Array (M.var (| "i" |)); Access.Component "child"] [[ M.var_access (| "levels", [Access.Array (InfixOp.add ~(| M.var (| "i" |), 1 |)); Access.Component "root"] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [] [[ InfixOp.sub ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "areKeyEquals" in
    do~ M.substitute_var "areKeyEquals" [] [[ M.call_function ~(| "IsEqual", ([] : list F.t) |) ]] in
    do~ M.substitute_var "areKeyEquals" [Access.Component "in"; Access.Array (0)] [[ M.var (| "oldKey" |) ]] in
    do~ M.substitute_var "areKeyEquals" [Access.Component "in"; Access.Array (1)] [[ M.var (| "key" |) ]] in
    (* Component *)
    do~ M.declare_component "keysOk" in
    do~ M.substitute_var "keysOk" [] [[ M.call_function ~(| "MultiAND", [ 4 ] |) ]] in
    do~ M.substitute_var "keysOk" [Access.Component "in"; Access.Array (0)] [[ M.var (| "fnc" |) ]] in
    do~ M.substitute_var "keysOk" [Access.Component "in"; Access.Array (1)] [[ InfixOp.sub ~(| 1, M.var (| "isOld0" |) |) ]] in
    do~ M.substitute_var "keysOk" [Access.Component "in"; Access.Array (2)] [[ M.var_access (| "areKeyEquals", [Access.Component "out"] |) ]] in
    do~ M.substitute_var "keysOk" [Access.Component "in"; Access.Array (3)] [[ M.var (| "enabled" |) ]] in
    do~ M.equality_constraint
      [[ M.var_access (| "keysOk", [Access.Component "out"] |) ]]
      [[ 0 ]]
    in
    (* Component *)
    do~ M.declare_component "checkRoot" in
    do~ M.substitute_var "checkRoot" [] [[ M.call_function ~(| "ForceEqualIfEnabled", ([] : list F.t) |) ]] in
    do~ M.substitute_var "checkRoot" [Access.Component "enabled"] [[ M.var (| "enabled" |) ]] in
    do~ M.substitute_var "checkRoot" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "levels", [Access.Array (0); Access.Component "root"] |) ]] in
    do~ M.substitute_var "checkRoot" [Access.Component "in"; Access.Array (1)] [[ M.var (| "root" |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SMTVerifier_not_under_constrained (nLevels : F.t) enabled root siblings oldKey oldValue isOld0 key value fnc : Prop :=
  let signals := SMTVerifierSignals.Build_t enabled root siblings oldKey oldValue isOld0 key value fnc in
  True (* NotUnderConstrained SMTVerifier nLevels signals *).
