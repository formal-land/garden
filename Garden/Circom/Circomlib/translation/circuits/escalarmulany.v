(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Multiplexor2Signals.
  Record t : Set := {
    (* Input *)
    sel : F.t;
    (* Input *)
    in_ : list (list F.t);
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | sel : P _ sel "sel"
    | in_ : P _ in_ "in"
    | out : P _ out "out".
  End IsNamed.
End Multiplexor2Signals.

(* Template body *)
Definition Multiplexor2 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "sel" in
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    do~ M.substitute_var "out" [Access.Array (0)] [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "in", [Access.Array (1); Access.Array (0)] |), M.var_access (| "in", [Access.Array (0); Access.Array (0)] |) |), M.var (| "sel" |) |), M.var_access (| "in", [Access.Array (0); Access.Array (0)] |) |) ]] in
    do~ M.substitute_var "out" [Access.Array (1)] [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.sub ~(| M.var_access (| "in", [Access.Array (1); Access.Array (1)] |), M.var_access (| "in", [Access.Array (0); Access.Array (1)] |) |), M.var (| "sel" |) |), M.var_access (| "in", [Access.Array (0); Access.Array (1)] |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Multiplexor2_not_under_constrained sel in_ : Prop :=
  exists! out,
  let signals := Multiplexor2Signals.Build_t sel in_ out in
  True (* NotUnderConstrained Multiplexor2 signals *).

(* Template signals *)
Module BitElementMulAnySignals.
  Record t : Set := {
    (* Input *)
    sel : F.t;
    (* Input *)
    dblIn : list F.t;
    (* Input *)
    addIn : list F.t;
    (* Output *)
    dblOut : list F.t;
    (* Output *)
    addOut : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | sel : P _ sel "sel"
    | dblIn : P _ dblIn "dblIn"
    | addIn : P _ addIn "addIn"
    | dblOut : P _ dblOut "dblOut"
    | addOut : P _ addOut "addOut".
  End IsNamed.
End BitElementMulAnySignals.

(* Template body *)
Definition BitElementMulAny : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "sel" in
    (* Signal Input *)
    do~ M.declare_signal "dblIn" in
    (* Signal Input *)
    do~ M.declare_signal "addIn" in
    (* Signal Output *)
    do~ M.declare_signal "dblOut" in
    (* Signal Output *)
    do~ M.declare_signal "addOut" in
    (* Component *)
    do~ M.declare_component "doubler" in
    do~ M.substitute_var "doubler" [] [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "adder" in
    do~ M.substitute_var "adder" [] [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "selector" in
    do~ M.substitute_var "selector" [] [[ M.call_function ~(| "Multiplexor2", ([] : list F.t) |) ]] in
    do~ M.substitute_var "selector" [Access.Component "sel"] [[ M.var (| "sel" |) ]] in
    do~ M.substitute_var "doubler" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "dblIn", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "doubler" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "dblIn", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adder" [Access.Component "in1"; Access.Array (0)] [[ M.var_access (| "doubler", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adder" [Access.Component "in1"; Access.Array (1)] [[ M.var_access (| "doubler", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "adder" [Access.Component "in2"; Access.Array (0)] [[ M.var_access (| "addIn", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adder" [Access.Component "in2"; Access.Array (1)] [[ M.var_access (| "addIn", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "selector" [Access.Component "in"; Access.Array (0); Access.Array (0)] [[ M.var_access (| "addIn", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "selector" [Access.Component "in"; Access.Array (0); Access.Array (1)] [[ M.var_access (| "addIn", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "selector" [Access.Component "in"; Access.Array (1); Access.Array (0)] [[ M.var_access (| "adder", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "selector" [Access.Component "in"; Access.Array (1); Access.Array (1)] [[ M.var_access (| "adder", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "dblOut" [Access.Array (0)] [[ M.var_access (| "doubler", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "dblOut" [Access.Array (1)] [[ M.var_access (| "doubler", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "addOut" [Access.Array (0)] [[ M.var_access (| "selector", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "addOut" [Access.Array (1)] [[ M.var_access (| "selector", [Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition BitElementMulAny_not_under_constrained sel dblIn addIn : Prop :=
  exists! dblOut addOut,
  let signals := BitElementMulAnySignals.Build_t sel dblIn addIn dblOut addOut in
  True (* NotUnderConstrained BitElementMulAny signals *).

(* Template signals *)
Module SegmentMulAnySignals.
  Record t : Set := {
    (* Input *)
    e : list F.t;
    (* Input *)
    p : list F.t;
    (* Output *)
    out : list F.t;
    (* Output *)
    dbl : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | e : P _ e "e"
    | p : P _ p "p"
    | out : P _ out "out"
    | dbl : P _ dbl "dbl".
  End IsNamed.
End SegmentMulAnySignals.

(* Template body *)
Definition SegmentMulAny (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "e" in
    (* Signal Input *)
    do~ M.declare_signal "p" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Output *)
    do~ M.declare_signal "dbl" in
    (* Component *)
    do~ M.declare_component "bits" in
    (* Component *)
    do~ M.declare_component "e2m" in
    do~ M.substitute_var "e2m" [] [[ M.call_function ~(| "Edwards2Montgomery", ([] : list F.t) |) ]] in
    do~ M.substitute_var "e2m" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "p", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "e2m" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "p", [Access.Array (1)] |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.substitute_var "bits" [Access.Array (0)] [[ M.call_function ~(| "BitElementMulAny", ([] : list F.t) |) ]] in
    do~ M.substitute_var "bits" [Access.Array (0); Access.Component "dblIn"; Access.Array (0)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "bits" [Access.Array (0); Access.Component "dblIn"; Access.Array (1)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "bits" [Access.Array (0); Access.Component "addIn"; Access.Array (0)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "bits" [Access.Array (0); Access.Component "addIn"; Access.Array (1)] [[ M.var_access (| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "bits" [Access.Array (0); Access.Component "sel"] [[ M.var_access (| "e", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "i" [] [[ 1 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), InfixOp.sub ~(| M.var (| "n" |), 1 |) |) ]] (
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "BitElementMulAny", ([] : list F.t) |) ]] in
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |)); Access.Component "dblIn"; Access.Array (0)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "dblOut"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |)); Access.Component "dblIn"; Access.Array (1)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "dblOut"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |)); Access.Component "addIn"; Access.Array (0)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "addOut"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |)); Access.Component "addIn"; Access.Array (1)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "addOut"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "bits" [Access.Array (M.var (| "i" |)); Access.Component "sel"] [[ M.var_access (| "e", [Access.Array (InfixOp.add ~(| M.var (| "i" |), 1 |))] |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "dbl" [Access.Array (0)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "n" |), 2 |)); Access.Component "dblOut"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "dbl" [Access.Array (1)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "n" |), 2 |)); Access.Component "dblOut"; Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "m2e" in
    do~ M.substitute_var "m2e" [] [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
    do~ M.substitute_var "m2e" [Access.Component "in"; Access.Array (0)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "n" |), 2 |)); Access.Component "addOut"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "m2e" [Access.Component "in"; Access.Array (1)] [[ M.var_access (| "bits", [Access.Array (InfixOp.sub ~(| M.var (| "n" |), 2 |)); Access.Component "addOut"; Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "eadder" in
    do~ M.substitute_var "eadder" [] [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
    do~ M.substitute_var "eadder" [Access.Component "x1"] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "eadder" [Access.Component "y1"] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "eadder" [Access.Component "x2"] [[ PrefixOp.sub ~(| M.var_access (| "p", [Access.Array (0)] |) |) ]] in
    do~ M.substitute_var "eadder" [Access.Component "y2"] [[ M.var_access (| "p", [Access.Array (1)] |) ]] in
    (* Component *)
    do~ M.declare_component "lastSel" in
    do~ M.substitute_var "lastSel" [] [[ M.call_function ~(| "Multiplexor2", ([] : list F.t) |) ]] in
    do~ M.substitute_var "lastSel" [Access.Component "sel"] [[ M.var_access (| "e", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "lastSel" [Access.Component "in"; Access.Array (0); Access.Array (0)] [[ M.var_access (| "eadder", [Access.Component "xout"] |) ]] in
    do~ M.substitute_var "lastSel" [Access.Component "in"; Access.Array (0); Access.Array (1)] [[ M.var_access (| "eadder", [Access.Component "yout"] |) ]] in
    do~ M.substitute_var "lastSel" [Access.Component "in"; Access.Array (1); Access.Array (0)] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "lastSel" [Access.Component "in"; Access.Array (1); Access.Array (1)] [[ M.var_access (| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "out" [Access.Array (0)] [[ M.var_access (| "lastSel", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [Access.Array (1)] [[ M.var_access (| "lastSel", [Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SegmentMulAny_not_under_constrained (n : F.t) e p : Prop :=
  exists! out dbl,
  let signals := SegmentMulAnySignals.Build_t e p out dbl in
  True (* NotUnderConstrained SegmentMulAny n signals *).

(* Template signals *)
Module EscalarMulAnySignals.
  Record t : Set := {
    (* Input *)
    e : list F.t;
    (* Input *)
    p : list F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | e : P _ e "e"
    | p : P _ p "p"
    | out : P _ out "out".
  End IsNamed.
End EscalarMulAnySignals.

(* Template body *)
Definition EscalarMulAny (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "e" in
    (* Signal Input *)
    do~ M.declare_signal "p" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "nsegments" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nsegments" [] [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var (| "n" |), 1 |), 148 |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "nlastsegment" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nlastsegment" [] [[ InfixOp.sub ~(| M.var (| "n" |), InfixOp.mul ~(| InfixOp.sub ~(| M.var (| "nsegments" |), 1 |), 148 |) |) ]] in
    (* Component *)
    do~ M.declare_component "segments" in
    (* Component *)
    do~ M.declare_component "doublers" in
    (* Component *)
    do~ M.declare_component "m2e" in
    (* Component *)
    do~ M.declare_component "adders" in
    (* Component *)
    do~ M.declare_component "zeropoint" in
    do~ M.substitute_var "zeropoint" [] [[ M.call_function ~(| "IsZero", ([] : list F.t) |) ]] in
    do~ M.substitute_var "zeropoint" [Access.Component "in"] [[ M.var_access (| "p", [Access.Array (0)] |) ]] in
    (* Var *)
    do~ M.declare_var "s" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "s" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "nseg" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nseg" [] [[ 0 ]] in
    do~ M.substitute_var "s" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "s" |), M.var (| "nsegments" |) |) ]] (
      do~ M.substitute_var "nseg" [] [[ ternary_expression (InfixOp.lesser ~(| M.var (| "s" |), InfixOp.sub ~(| M.var (| "nsegments" |), 1 |) |)) (148) (M.var (| "nlastsegment" |)) ]] in
      do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |))] [[ M.call_function ~(| "SegmentMulAny", [ M.var (| "nseg" |) ] |) ]] in
      do~ M.substitute_var "i" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nseg" |) |) ]] (
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "e"; Access.Array (M.var (| "i" |))] [[ M.var_access (| "e", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "s" |), 148 |), M.var (| "i" |) |))] |) ]] in
        do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "s" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "p"; Access.Array (0)] [[ InfixOp.add ~(| M.var_access (| "p", [Access.Array (0)] |), InfixOp.mul ~(| InfixOp.sub ~(| 5299619240641551281634865583518297030282874472190772894086521144482721001553, M.var_access (| "p", [Access.Array (0)] |) |), M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "p"; Access.Array (1)] [[ InfixOp.add ~(| M.var_access (| "p", [Access.Array (1)] |), InfixOp.mul ~(| InfixOp.sub ~(| 16950150798460657717958625567821834550301663161624707787222815936182638968203, M.var_access (| "p", [Access.Array (1)] |) |), M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "doublers" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |))] [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |))] [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
        do~ M.substitute_var "adders" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |))] [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
        do~ M.substitute_var "doublers" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (0)] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "dbl"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "doublers" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (1)] [[ M.var_access (| "segments", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "dbl"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (0)] [[ M.var_access (| "doublers", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "m2e" [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "in"; Access.Array (1)] [[ M.var_access (| "doublers", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "p"; Access.Array (0)] [[ M.var_access (| "m2e", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "segments" [Access.Array (M.var (| "s" |)); Access.Component "p"; Access.Array (1)] [[ M.var_access (| "m2e", [Access.Array (InfixOp.sub ~(| M.var (| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
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
      do~ M.substitute_var "out" [Access.Array (0)] [[ InfixOp.mul ~(| M.var_access (| "segments", [Access.Array (0); Access.Component "out"; Access.Array (0)] |), InfixOp.sub ~(| 1, M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      do~ M.substitute_var "out" [Access.Array (1)] [[ InfixOp.add ~(| M.var_access (| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |), InfixOp.mul ~(| InfixOp.sub ~(| 1, M.var_access (| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) |), M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.substitute_var "out" [Access.Array (0)] [[ InfixOp.mul ~(| M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nsegments" |), 2 |)); Access.Component "xout"] |), InfixOp.sub ~(| 1, M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      do~ M.substitute_var "out" [Access.Array (1)] [[ InfixOp.add ~(| M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nsegments" |), 2 |)); Access.Component "yout"] |), InfixOp.mul ~(| InfixOp.sub ~(| 1, M.var_access (| "adders", [Access.Array (InfixOp.sub ~(| M.var (| "nsegments" |), 2 |)); Access.Component "yout"] |) |), M.var_access (| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition EscalarMulAny_not_under_constrained (n : F.t) e p : Prop :=
  exists! out,
  let signals := EscalarMulAnySignals.Build_t e p out in
  True (* NotUnderConstrained EscalarMulAny n signals *).
