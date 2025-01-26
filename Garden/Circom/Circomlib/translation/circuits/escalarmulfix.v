(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module WindowMulFixSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Input *)
    base : list F.t;
    (* Output *)
    out : list F.t;
    (* Output *)
    out8 : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | base : P _ base "base"
    | out : P _ out "out"
    | out8 : P _ out8 "out8".
  End IsNamed.
End WindowMulFixSignals.

(* Template body *)
Definition WindowMulFix : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Input *)
    do~ M.declare_signal "base" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Output *)
    do~ M.declare_signal "out8" in
    (* Component *)
    do~ M.declare_component "mux" in
    do~ M.substitute_var "mux" [] [[ M.call_function ~(| "MultiMux3", [ 2 ] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "s"; Access.Array (0)] [[ M.var_access (| "in", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "s"; Access.Array (1)] [[ M.var_access (| "in", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "s"; Access.Array (2)] [[ M.var_access (| "in", [Access.Array (2)] |) ]] in
    (* Component *)
    do~ M.declare_component "dbl2" in
    do~ M.substitute_var "dbl2" [] [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr3" in
    do~ M.substitute_var "adr3" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr4" in
    do~ M.substitute_var "adr4" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr5" in
    do~ M.substitute_var "adr5" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr6" in
    do~ M.substitute_var "adr6" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr7" in
    do~ M.substitute_var "adr7" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adr8" in
    do~ M.substitute_var "adr8" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (0)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "dbl2" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "dbl2" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (1)] [[ M.var_access (| "dbl2", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (1)] [[ M.var_access (| "dbl2", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr3" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr3" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr3" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "dbl2", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr3" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "dbl2", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (2)] [[ M.var_access (| "adr3", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (2)] [[ M.var_access (| "adr3", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr4" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr4" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr4" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "adr3", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr4" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "adr3", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (3)] [[ M.var_access (| "adr4", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (3)] [[ M.var_access (| "adr4", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr5" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr5" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr5" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "adr4", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr5" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "adr4", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (4)] [[ M.var_access (| "adr5", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (4)] [[ M.var_access (| "adr5", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr6" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr6" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr6" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "adr5", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr6" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "adr5", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (5)] [[ M.var_access (| "adr6", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (5)] [[ M.var_access (| "adr6", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr7" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr7" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr7" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "adr6", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr7" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "adr6", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (6)] [[ M.var_access (| "adr7", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (6)] [[ M.var_access (| "adr7", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr8" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr8" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adr8" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "adr7", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adr8" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "adr7", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (0); Access.Array (7)] [[ M.var_access (| "adr8", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "mux" [Access.Component "c"; Access.Array (1); Access.Array (7)] [[ M.var_access (| "adr8", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "out8" [Access.Array (0)] [[ M.var_access (| "adr8", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out8" [Access.Array (1)] [[ M.var_access (| "adr8", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "out" [Access.Array (0)] [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [Access.Array (1)] [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition WindowMulFix_not_under_constrained in_ base : Prop :=
  exists! out out8,
  let signals := WindowMulFixSignals.Build_t in_ base out out8 in
  True (* NotUnderConstrained WindowMulFix signals *).

(* Template signals *)
Module SegmentMulFixSignals.
  Record t : Set := {
    (* Input *)
    e : list F.t;
    (* Input *)
    base : list F.t;
    (* Output *)
    out : list F.t;
    (* Output *)
    dbl : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | e : P _ e "e"
    | base : P _ base "base"
    | out : P _ out "out"
    | dbl : P _ dbl "dbl".
  End IsNamed.
End SegmentMulFixSignals.

(* Template body *)
Definition SegmentMulFix (nWindows : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("nWindows", nWindows)] (
    (* Signal Input *)
    do~ M.declare_signal "e" in
    (* Signal Input *)
    do~ M.declare_signal "base" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Output *)
    do~ M.declare_signal "dbl" in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [] [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "e2m" in
    do~ M.substitute_var "e2m" [] [[ M.call_function ~(| "Edwards2Montgomery", ([] : list F.t) |) ]] in
    do~ M.substitute_var "e2m" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "base", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "e2m" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "base", [Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "windows" in
    (* Component *)
    do~ M.declare_component "adders" in
    (* Component *)
    do~ M.declare_component "cadders" in
    (* Component *)
    do~ M.declare_component "dblLast" in
    do~ M.substitute_var "dblLast" [] [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nWindows" |) |) ]] (
      do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "WindowMulFix", ([] : list F.t) |) ]] in
      do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |)); Access.Component "base"; Access.Array (0)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |)); Access.Component "base"; Access.Array (1)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |)); Access.Component "base"; Access.Array (0)] [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out8"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |)); Access.Component "base"; Access.Array (1)] [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out8"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "cadders", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "cadders", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "j" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), 3 |) ]] (
        do~ M.substitute_var "windows" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ M.var_access (| "e", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 3, M.var (| "i" |) |), M.var (| "j" |) |))] |) ]] in
        do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.if_ [[ InfixOp.lesser ~(| M.var (| "i" |), InfixOp.sub ~(| M.var (| "nWindows" |), 1 |) |) ]] (* then *) (
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out8"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out8"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "dblLast" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out8"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "dblLast" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out8"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "dblLast", [Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "cadders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "dblLast", [Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nWindows" |) |) ]] (
      do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "dblLast", [Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "dblLast", [Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [Access.Array (M.var (| "i" |)); Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    (* Component *)
    do~ M.declare_component "m2e" in
    do~ M.substitute_var "m2e" [] [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "cm2e" in
    do~ M.substitute_var "cm2e" [] [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
    do~ M.substitute_var "m2e" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "m2e" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "cm2e" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "cadders", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "cm2e" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "cadders", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "cAdd" in
    do~ M.substitute_var "cAdd" [] [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
    do~ M.substitute_var "cAdd" [Access.Component "x1"] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "cAdd" [Access.Component "y1"] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "cAdd" [Access.Component "x2"] [[ PrefixOp.sub ~(| M.var_access (| "cm2e", [Access.Component "out"; Access.Array (0)] |) |) ]] in
    do~ M.substitute_var "cAdd" [Access.Component "y2"] [[ M.var_access (| "cm2e", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "out" [Access.Array (0)] [[ M.var_access (| "cAdd", [Access.Component "xout"] |) ]] in
    do~ M.substitute_var "out" [Access.Array (1)] [[ M.var_access (| "cAdd", [Access.Component "yout"] |) ]] in
    do~ M.substitute_var "dbl" [Access.Array (0)] [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out8"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "dbl" [Access.Array (1)] [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "nWindows" |), 1 |)); Access.Component "out8"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SegmentMulFix_not_under_constrained (nWindows : F.t) e base : Prop :=
  exists! out dbl,
  let signals := SegmentMulFixSignals.Build_t e base out dbl in
  True (* NotUnderConstrained SegmentMulFix nWindows signals *).

(* Template signals *)
Module EscalarMulFixSignals.
  Record t : Set := {
    (* Input *)
    e : list F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | e : P _ e "e"
    | out : P _ out "out".
  End IsNamed.
End EscalarMulFixSignals.

(* Template body *)
Definition EscalarMulFix (n BASE : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n); ("BASE", BASE)] (
    (* Signal Input *)
    do~ M.declare_signal "e" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "nsegments" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nsegments" [] [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var (| "n" |), 1 |), 246 |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "nlastsegment" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nlastsegment" [] [[ InfixOp.sub ~(| M.var (| "n" |), InfixOp.mul ~(| InfixOp.sub ~(| M.var (| "nsegments" |), 1 |), 249 |) |) ]] in
    (* Component *)
    do~ M.declare_component "segments" in
    (* Component *)
    do~ M.declare_component "m2e" in
    (* Component *)
    do~ M.declare_component "adders" in
    (* Var *)
    do~ M.declare_var "s" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "s" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "nseg" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nseg" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "nWindows" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nWindows" [] [[ 0 ]] in
    do~ M.substitute_var "s" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "s" |), M.var (| "nsegments" |) |) ]] (
      do~ M.substitute_var "nseg" [] [[ ternary_expression (InfixOp.lesser ~(| M.var (| "s" |), InfixOp.sub ~(| M.var (| "nsegments" |), 1 |) |)) (249) (M.var (| "nlastsegment" |)) ]] in
      do~ M.substitute_var "nWindows" [] [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var (| "nseg" |), 1 |), 3 |), 1 |) ]] in
      do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |))] [[ M.call_function ~(| "SegmentMulFix", [ M.var (| "nWindows" |) ] |) ]] in
      do~ M.substitute_var "i" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nseg" |) |) ]] (
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "e"; Access.Array (M.var (| "i" |))] [[ M.var_access (| "e", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "s" |), 249 |), M.var (| "i" |) |))] |) ]] in
        do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [] [[ M.var (| "nseg" |) ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), InfixOp.mul ~(| M.var (| "nWindows" |), 3 |) |) ]] (
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "e"; Access.Array (M.var (| "i" |))] [[ 0 ]] in
        do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "s" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "base"; Access.Array (0)] [[ M.var_access (| "BASE", [Access.Array (0)] |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "base"; Access.Array (1)] [[ M.var_access (| "BASE", [Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |))] [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
        do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |))] [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (0)] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "dbl"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (1)] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "dbl"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "base"; Access.Array (0)] [[ M.var_access (| "m2e", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "base"; Access.Array (1)] [[ M.var_access (| "m2e", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        do~ M.if_ [[ InfixOp.eq ~(| M.var (| "s" |), 1 |) ]] (* then *) (
          do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "x1"] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
          do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "y1"] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
          M.pure BlockUnit.Tt
        ) (* else *) (
          do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "x1"] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 2 |)); Access.Component "xout"] |) ]] in
          do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "y1"] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 2 |)); Access.Component "yout"] |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "x2"] [[ M.var_access (| "segments", [Access.Array (M.var (| "s" |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "y2"] [[ M.var_access (| "segments", [Access.Array (M.var (| "s" |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "s" [] [[ InfixOp.add ~(| M.var (| "s" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.if_ [[ InfixOp.eq ~(| M.var (| "nsegments" |), 1 |) ]] (* then *) (
      do~ M.substitute_var "out" [Access.Array (0)] [[ M.var_access (| "segments", [Access.Array (0); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "out" [Access.Array (1)] [[ M.var_access (| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.substitute_var "out" [Access.Array (0)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nsegments" |), 2 |)); Access.Component "xout"] |) ]] in
      do~ M.substitute_var "out" [Access.Array (1)] [[ M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nsegments" |), 2 |)); Access.Component "yout"] |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition EscalarMulFix_not_under_constrained (n BASE : F.t) e : Prop :=
  exists! out,
  let signals := EscalarMulFixSignals.Build_t e out in
  True (* NotUnderConstrained EscalarMulFix n BASE signals *).
