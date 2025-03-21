(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Sha256Signals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
    (* Intermediate *)
    paddedIn : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out"
    | paddedIn : P _ paddedIn "paddedIn".
  End IsNamed.
End Sha256Signals.

(* Template body *)
Definition Sha256 (nBits : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("nBits", nBits)] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "nBlocks" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nBlocks" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "bitsLastBlock" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "bitsLastBlock" [] [[ 0 ]] in
    do~ M.substitute_var "nBlocks" [] [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.add ~(| M.var (| "nBits" |), 64 |), 512 |), 1 |) ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "paddedIn" in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "nBits" |) |) ]] (
      do~ M.substitute_var "paddedIn" [Access.Array (M.var (| "k" |))] [[ M.var_access (| "in", [Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "paddedIn" [Access.Array (M.var (| "nBits" |))] [[ 1 ]] in
    do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "nBits" |), 1 |) ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), InfixOp.sub ~(| InfixOp.mul ~(| M.var (| "nBlocks" |), 512 |), 64 |) |) ]] (
      do~ M.substitute_var "paddedIn" [Access.Array (M.var (| "k" |))] [[ 0 ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 64 |) ]] (
      do~ M.substitute_var "paddedIn" [Access.Array (InfixOp.sub ~(| InfixOp.sub ~(| InfixOp.mul ~(| M.var (| "nBlocks" |), 512 |), M.var (| "k" |) |), 1 |))] [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var (| "nBits" |), M.var (| "k" |) |), 1 |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "ha0" in
    do~ M.substitute_var "ha0" [] [[ M.call_function ~(| "H", [ 0 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hb0" in
    do~ M.substitute_var "hb0" [] [[ M.call_function ~(| "H", [ 1 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hc0" in
    do~ M.substitute_var "hc0" [] [[ M.call_function ~(| "H", [ 2 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hd0" in
    do~ M.substitute_var "hd0" [] [[ M.call_function ~(| "H", [ 3 ] |) ]] in
    (* Component *)
    do~ M.declare_component "he0" in
    do~ M.substitute_var "he0" [] [[ M.call_function ~(| "H", [ 4 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hf0" in
    do~ M.substitute_var "hf0" [] [[ M.call_function ~(| "H", [ 5 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hg0" in
    do~ M.substitute_var "hg0" [] [[ M.call_function ~(| "H", [ 6 ] |) ]] in
    (* Component *)
    do~ M.declare_component "hh0" in
    do~ M.substitute_var "hh0" [] [[ M.call_function ~(| "H", [ 7 ] |) ]] in
    (* Component *)
    do~ M.declare_component "sha256compression" in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nBlocks" |) |) ]] (
      do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "Sha256compression", ([] : list F.t) |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "k" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 0, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "ha0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 1, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hb0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 2, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hc0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 3, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hd0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 4, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "he0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 5, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hf0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 6, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hg0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 7, 32 |), M.var (| "k" |) |))] [[ M.var_access (| "hh0", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
          do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "k" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 32 |) ]] (
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 0 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 0 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 1 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 1 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 2 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 2 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 3 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 3 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 4 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 4 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 5 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 5 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 6 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 6 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "hin"; Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 32, 7 |), M.var (| "k" |) |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| 32, 7 |), 31 |), M.var (| "k" |) |))] |) ]] in
          do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "k" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 512 |) ]] (
        do~ M.substitute_var "sha256compression" [Access.Array (M.var (| "i" |)); Access.Component "inp"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "paddedIn", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 512 |), M.var (| "k" |) |))] |) ]] in
        do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), 256 |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "k" |))] [[ M.var_access (| "sha256compression", [Access.Array (InfixOp.sub ~(| M.var (| "nBlocks" |), 1 |)); Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Sha256_not_under_constrained (nBits : F.t) in_ : Prop :=
  exists! out,
  exists paddedIn,
  let signals := Sha256Signals.Build_t in_ out paddedIn in
  True (* NotUnderConstrained Sha256 nBits signals *).
