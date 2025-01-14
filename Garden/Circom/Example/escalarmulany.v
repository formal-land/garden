
(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Multiplexor2Signals.
  Record t : Set := {
    sel : F.t;
    in_ : list (list F.t);
    out : list F.t;
  }.
End Multiplexor2Signals.

(* Template body *)
Definition Multiplexor2 : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "sel" [[ ([] : list F.t) ]] in
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 2; 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.sub ~(| M.var_access ~(| "in", [Access.Array (1); Access.Array (0)] |), M.var_access ~(| "in", [Access.Array (0); Access.Array (0)] |) |), M.var ~(| "sel" |) |), M.var_access ~(| "in", [Access.Array (0); Access.Array (0)] |) |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.sub ~(| M.var_access ~(| "in", [Access.Array (1); Access.Array (1)] |), M.var_access ~(| "in", [Access.Array (0); Access.Array (1)] |) |), M.var ~(| "sel" |) |), M.var_access ~(| "in", [Access.Array (0); Access.Array (1)] |) |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module BitElementMulAnySignals.
  Record t : Set := {
    sel : F.t;
    dblIn : list F.t;
    addIn : list F.t;
    dblOut : list F.t;
    addOut : list F.t;
  }.
End BitElementMulAnySignals.

(* Template body *)
Definition BitElementMulAny : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "sel" [[ ([] : list F.t) ]] in
  (* Signal Input *)
  do~ M.declare_signal "dblIn" [[ [ 2 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "addIn" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "dblOut" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "addOut" [[ [ 2 ] ]] in
  (* Component *)
  do~ M.declare_component "doubler" in
  do~ M.substitute_var "doubler" [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adder" in
  do~ M.substitute_var "adder" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "selector" in
  do~ M.substitute_var "selector" [[ M.call_function ~(| "Multiplexor2", ([] : list F.t) |) ]] in
  do~ M.substitute_var "selector" [[ M.var ~(| "sel" |) ]] in
  do~ M.substitute_var "doubler" [[ M.var_access ~(| "dblIn", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "doubler" [[ M.var_access ~(| "dblIn", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adder" [[ M.var_access ~(| "doubler", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adder" [[ M.var_access ~(| "doubler", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adder" [[ M.var_access ~(| "addIn", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adder" [[ M.var_access ~(| "addIn", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "selector" [[ M.var_access ~(| "addIn", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "selector" [[ M.var_access ~(| "addIn", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "selector" [[ M.var_access ~(| "adder", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "selector" [[ M.var_access ~(| "adder", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "dblOut" [[ M.var_access ~(| "doubler", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "dblOut" [[ M.var_access ~(| "doubler", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "addOut" [[ M.var_access ~(| "selector", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "addOut" [[ M.var_access ~(| "selector", [Access.Component "out"; Access.Array (1)] |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module SegmentMulAnySignals.
  Record t : Set := {
    e : list F.t;
    p : list F.t;
    out : list F.t;
    dbl : list F.t;
  }.
End SegmentMulAnySignals.

(* Template body *)
Definition SegmentMulAny (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "e" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "p" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "dbl" [[ [ 2 ] ]] in
  (* Component *)
  do~ M.declare_component "bits" in
  (* Component *)
  do~ M.declare_component "e2m" in
  do~ M.substitute_var "e2m" [[ M.call_function ~(| "Edwards2Montgomery", ([] : list F.t) |) ]] in
  do~ M.substitute_var "e2m" [[ M.var_access ~(| "p", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "e2m" [[ M.var_access ~(| "p", [Access.Array (1)] |) ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.substitute_var "bits" [[ M.call_function ~(| "BitElementMulAny", ([] : list F.t) |) ]] in
  do~ M.substitute_var "bits" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "bits" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "bits" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "bits" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "bits" [[ M.var_access ~(| "e", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "i" [[ 1 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), InfixOp.sub ~(| M.var ~(| "n" |), 1 |) |) ]] (
    do~ M.substitute_var "bits" [[ M.call_function ~(| "BitElementMulAny", ([] : list F.t) |) ]] in
    do~ M.substitute_var "bits" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "dblOut"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "bits" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "dblOut"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "bits" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "addOut"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "bits" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "addOut"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "bits" [[ M.var_access ~(| "e", [Access.Array (InfixOp.add ~(| M.var ~(| "i" |), 1 |))] |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "dbl" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "n" |), 2 |)); Access.Component "dblOut"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "dbl" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "n" |), 2 |)); Access.Component "dblOut"; Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "m2e" in
  do~ M.substitute_var "m2e" [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
  do~ M.substitute_var "m2e" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "n" |), 2 |)); Access.Component "addOut"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "m2e" [[ M.var_access ~(| "bits", [Access.Array (InfixOp.sub ~(| M.var ~(| "n" |), 2 |)); Access.Component "addOut"; Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "eadder" in
  do~ M.substitute_var "eadder" [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
  do~ M.substitute_var "eadder" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "eadder" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "eadder" [[ PrefixOp.sub ~(| M.var_access ~(| "p", [Access.Array (0)] |) |) ]] in
  do~ M.substitute_var "eadder" [[ M.var_access ~(| "p", [Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "lastSel" in
  do~ M.substitute_var "lastSel" [[ M.call_function ~(| "Multiplexor2", ([] : list F.t) |) ]] in
  do~ M.substitute_var "lastSel" [[ M.var_access ~(| "e", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "lastSel" [[ M.var_access ~(| "eadder", [Access.Component "xout"] |) ]] in
  do~ M.substitute_var "lastSel" [[ M.var_access ~(| "eadder", [Access.Component "yout"] |) ]] in
  do~ M.substitute_var "lastSel" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "lastSel" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "out" [[ M.var_access ~(| "lastSel", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "out" [[ M.var_access ~(| "lastSel", [Access.Component "out"; Access.Array (1)] |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module EscalarMulAnySignals.
  Record t : Set := {
    e : list F.t;
    p : list F.t;
    out : list F.t;
  }.
End EscalarMulAnySignals.

(* Template body *)
Definition EscalarMulAny (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "e" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "p" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "nsegments" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nsegments" [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var ~(| "n" |), 1 |), 148 |), 1 |) ]] in
  (* Var *)
  do~ M.declare_var "nlastsegment" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nlastsegment" [[ InfixOp.sub ~(| M.var ~(| "n" |), InfixOp.mul ~(| InfixOp.sub ~(| M.var ~(| "nsegments" |), 1 |), 148 |) |) ]] in
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
  do~ M.substitute_var "zeropoint" [[ M.call_function ~(| "IsZero", ([] : list F.t) |) ]] in
  do~ M.substitute_var "zeropoint" [[ M.var_access ~(| "p", [Access.Array (0)] |) ]] in
  (* Var *)
  do~ M.declare_var "s" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "s" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "nseg" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nseg" [[ 0 ]] in
  do~ M.substitute_var "s" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "s" |), M.var ~(| "nsegments" |) |) ]] (
    do~ M.substitute_var "nseg" [[ ternary_expression (InfixOp.lesser ~(| M.var ~(| "s" |), InfixOp.sub ~(| M.var ~(| "nsegments" |), 1 |) |)) (148) (M.var ~(| "nlastsegment" |)) ]] in
    do~ M.substitute_var "segments" [[ M.call_function ~(| "SegmentMulAny", [ M.var ~(| "nseg" |) ] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "nseg" |) |) ]] (
      do~ M.substitute_var "segments" [[ M.var_access ~(| "e", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var ~(| "s" |), 148 |), M.var ~(| "i" |) |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "s" |), 0 |) ]] (* then *) (
      do~ M.substitute_var "segments" [[ InfixOp.add ~(| M.var_access ~(| "p", [Access.Array (0)] |), InfixOp.mul ~(| InfixOp.sub ~(| 5299619240641551281634865583518297030282874472190772894086521144482721001553, M.var_access ~(| "p", [Access.Array (0)] |) |), M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      do~ M.substitute_var "segments" [[ InfixOp.add ~(| M.var_access ~(| "p", [Access.Array (1)] |), InfixOp.mul ~(| InfixOp.sub ~(| 16950150798460657717958625567821834550301663161624707787222815936182638968203, M.var_access ~(| "p", [Access.Array (1)] |) |), M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.substitute_var "doublers" [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
      do~ M.substitute_var "m2e" [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
      do~ M.substitute_var "adders" [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
      do~ M.substitute_var "doublers" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "dbl"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "doublers" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "dbl"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "m2e" [[ M.var_access ~(| "doublers", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "m2e" [[ M.var_access ~(| "doublers", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "segments" [[ M.var_access ~(| "m2e", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "segments" [[ M.var_access ~(| "m2e", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "s" |), 1 |) ]] (* then *) (
        do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 2 |)); Access.Component "xout"] |) ]] in
        do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "s" |), 2 |)); Access.Component "yout"] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (M.var ~(| "s" |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (M.var ~(| "s" |)); Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "s" [[ InfixOp.add ~(| M.var ~(| "s" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "nsegments" |), 1 |) ]] (* then *) (
    do~ M.substitute_var "out" [[ InfixOp.mul ~(| M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (0)] |), InfixOp.sub ~(| 1, M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
    do~ M.substitute_var "out" [[ InfixOp.add ~(| M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |), InfixOp.mul ~(| InfixOp.sub ~(| 1, M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) |), M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
    M.pure BlockUnit.Tt
  ) (* else *) (
    do~ M.substitute_var "out" [[ InfixOp.mul ~(| M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nsegments" |), 2 |)); Access.Component "xout"] |), InfixOp.sub ~(| 1, M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
    do~ M.substitute_var "out" [[ InfixOp.add ~(| M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nsegments" |), 2 |)); Access.Component "yout"] |), InfixOp.mul ~(| InfixOp.sub ~(| 1, M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nsegments" |), 2 |)); Access.Component "yout"] |) |), M.var_access ~(| "zeropoint", [Access.Component "out"] |) |) |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.