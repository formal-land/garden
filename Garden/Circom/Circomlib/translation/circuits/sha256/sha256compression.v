(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Sha256compressionSignals.
  Record t : Set := {
    (* Input *)
    hin : list F.t;
    (* Input *)
    inp : list F.t;
    (* Output *)
    out : list F.t;
    (* Intermediate *)
    a : list (list F.t);
    (* Intermediate *)
    b : list (list F.t);
    (* Intermediate *)
    c : list (list F.t);
    (* Intermediate *)
    d : list (list F.t);
    (* Intermediate *)
    e : list (list F.t);
    (* Intermediate *)
    f : list (list F.t);
    (* Intermediate *)
    g : list (list F.t);
    (* Intermediate *)
    h : list (list F.t);
    (* Intermediate *)
    w : list (list F.t);
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | hin : P _ hin "hin"
    | inp : P _ inp "inp"
    | out : P _ out "out"
    | a : P _ a "a"
    | b : P _ b "b"
    | c : P _ c "c"
    | d : P _ d "d"
    | e : P _ e "e"
    | f : P _ f "f"
    | g : P _ g "g"
    | h : P _ h "h"
    | w : P _ w "w".
  End IsNamed.
End Sha256compressionSignals.

(* Template body *)
Definition Sha256compression : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "hin" in
    (* Signal Input *)
    do~ M.declare_signal "inp" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "a" in
    (* Signal Intermediate *)
    do~ M.declare_signal "b" in
    (* Signal Intermediate *)
    do~ M.declare_signal "c" in
    (* Signal Intermediate *)
    do~ M.declare_signal "d" in
    (* Signal Intermediate *)
    do~ M.declare_signal "e" in
    (* Signal Intermediate *)
    do~ M.declare_signal "f" in
    (* Signal Intermediate *)
    do~ M.declare_signal "g" in
    (* Signal Intermediate *)
    do~ M.declare_signal "h" in
    (* Signal Intermediate *)
    do~ M.declare_signal "w" in
    (* Var *)
    do~ M.declare_var "outCalc" [[ [ 256 ] ]] in
    do~ M.substitute_var "outCalc" [] [[ array_with_repeat (0) (256) ]] in
    do~ M.substitute_var "outCalc" [] [[ M.call_function ~(| "sha256compression", [ M.var (| "hin" |); M.var (| "inp" |) ] |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 256 |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ M.var_access (| "outCalc", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "sigmaPlus" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 48 |) ]] (
      do~ M.substitute_var "sigmaPlus" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "SigmaPlus", ([] : list F.t) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "ct_k" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.substitute_var "ct_k" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "K", [ M.var (| "i" |) ] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "t1" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.substitute_var "t1" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "T1", ([] : list F.t) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "t2" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.substitute_var "t2" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "T2", ([] : list F.t) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "suma" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.substitute_var "suma" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "BinSum", [ 32; 2 ] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "sume" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.substitute_var "sume" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "BinSum", [ 32; 2 ] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "fsum" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 8 |) ]] (
      do~ M.substitute_var "fsum" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "BinSum", [ 32; 2 ] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "t" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "t" [] [[ 0 ]] in
    do~ M.substitute_var "t" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "t" |), 64 |) ]] (
      do~ M.if_ [[ InfixOp.lesser ~(| M.var (| "t" |), 16 |) ]] (* then *) (
        do~ M.substitute_var "k" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
          do~ M.substitute_var "w" [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "inp", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| M.var (| "t" |), 32 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "k" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
          do~ M.substitute_var "sigmaPlus" [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Component "in2"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 2 |)); Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sigmaPlus" [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Component "in7"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 7 |)); Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sigmaPlus" [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Component "in15"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 15 |)); Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sigmaPlus" [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Component "in16"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "k" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
          do~ M.substitute_var "w" [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "sigmaPlus", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 16 |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "t" [] [[ InfixOp.add ~(| M.var (| "t" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.substitute_var "a" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "b" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 1 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "c" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 2 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "d" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 3 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "e" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 4 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "f" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 5 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "g" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 6 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "h" [Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 7 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "t" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "t" |), 64 |) ]] (
      do~ M.substitute_var "k" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "h"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "h", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "e"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "e", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "f"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "f", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "g"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "g", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "k"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "ct_k", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t1" [Access.Array (M.var (| "t" |)); Access.Component "w"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "w", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t2" [Access.Array (M.var (| "t" |)); Access.Component "a"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "a", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t2" [Access.Array (M.var (| "t" |)); Access.Component "b"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "b", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "t2" [Access.Array (M.var (| "t" |)); Access.Component "c"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "c", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "k" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
        do~ M.substitute_var "sume" [Access.Array (M.var (| "t" |)); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "d", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "sume" [Access.Array (M.var (| "t" |)); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "t1", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "suma" [Access.Array (M.var (| "t" |)); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "t1", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "suma" [Access.Array (M.var (| "t" |)); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "t2", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "k" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
        do~ M.substitute_var "h" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "g", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "g" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "f", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "f" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "e", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "e" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "sume", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "d" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "c", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "c" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "b", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "b" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "a", [Access.Array (M.var (| "t" |)); Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "a" [Access.Array (InfixOp.add ~(| M.var (| "t" |), 1 |)); Access.Array (M.var (| "k" |))] [[ M.var_access (| "suma", [Access.Array (M.var (| "t" |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "t" [] [[ InfixOp.add ~(| M.var (| "t" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.substitute_var "fsum" [Access.Array (0); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 0 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (0); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "a", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (1); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 1 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (1); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "b", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (2); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 2 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (2); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "c", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (3); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 3 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (3); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "d", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (4); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 4 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (4); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "e", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (5); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 5 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (5); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "f", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (6); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 6 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (6); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "g", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (7); Access.Component "in"; Access.Array (0); Access.Array (M.var (| "k" |))] [[ M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 7 |), M.var (| "k" |) |))] |) ]] in
      do~ M.substitute_var "fsum" [Access.Array (7); Access.Component "in"; Access.Array (1); Access.Array (M.var (| "k" |))] [[ M.var_access (| "h", [Access.Array (64); Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| 31, M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (0); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 32, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (1); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 64, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (2); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 96, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (3); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 128, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (4); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 160, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (5); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 192, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (6); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.equality_constraint
        [[ M.var_access (| "out", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| 224, 31 |), M.var (| "k" |) |))] |) ]]
        [[ M.var_access (| "fsum", [Access.Array (7); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]]
      in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Sha256compression_not_under_constrained hin inp : Prop :=
  exists! out,
  exists a b c d e f g h w,
  let signals := Sha256compressionSignals.Build_t hin inp out a b c d e f g h w in
  True (* NotUnderConstrained Sha256compression signals *).
