(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module EscalarProductSignals.
  Record t : Set := {
    in1 : list F.t;
    in2 : list F.t;
    out : F.t;
    aux : list F.t;
  }.
End EscalarProductSignals.

(* Template body *)
Definition EscalarProduct (w : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in1" [[ [ M.var ~(| "w" |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "in2" [[ [ M.var ~(| "w" |) ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
  (* Signal Intermediate *)
  do~ M.declare_signal "aux" [[ [ M.var ~(| "w" |) ] ]] in
  (* Var *)
  do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "lc" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "w" |) |) ]] (
    do~ M.substitute_var "aux" [[ InfixOp.mul ~(| M.var_access ~(| "in1", [Access.Array (M.var ~(| "i" |))] |), M.var_access ~(| "in2", [Access.Array (M.var ~(| "i" |))] |) |) ]] in
    do~ M.substitute_var "lc" [[ InfixOp.add ~(| M.var ~(| "lc" |), M.var_access ~(| "aux", [Access.Array (M.var ~(| "i" |))] |) |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "out" [[ M.var ~(| "lc" |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module DecoderSignals.
  Record t : Set := {
    inp : F.t;
    out : list F.t;
    success : F.t;
  }.
End DecoderSignals.

(* Template body *)
Definition Decoder (w : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "inp" [[ ([] : list F.t) ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ M.var ~(| "w" |) ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "success" [[ ([] : list F.t) ]] in
  (* Var *)
  do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "lc" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "w" |) |) ]] (
    do~ M.substitute_var "out" [[ ternary_expression (InfixOp.eq ~(| M.var ~(| "inp" |), M.var ~(| "i" |) |)) (1) (0) ]] in
    do~ M.equality_constraint
      [[ InfixOp.mul ~(| M.var_access ~(| "out", [Access.Array (M.var ~(| "i" |))] |), InfixOp.sub ~(| M.var ~(| "inp" |), M.var ~(| "i" |) |) |) ]]
      [[ 0 ]]
    in
    do~ M.substitute_var "lc" [[ InfixOp.add ~(| M.var ~(| "lc" |), M.var_access ~(| "out", [Access.Array (M.var ~(| "i" |))] |) |) ]] in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "success" [[ M.var ~(| "lc" |) ]] in
  do~ M.equality_constraint
    [[ InfixOp.mul ~(| M.var ~(| "success" |), InfixOp.sub ~(| M.var ~(| "success" |), 1 |) |) ]]
    [[ 0 ]]
  in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module MultiplexerSignals.
  Record t : Set := {
    inp : list (list F.t);
    sel : F.t;
    out : list F.t;
  }.
End MultiplexerSignals.

(* Template body *)
Definition Multiplexer (wIn nIn : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "inp" [[ [ M.var ~(| "nIn" |); M.var ~(| "wIn" |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "sel" [[ ([] : list F.t) ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ M.var ~(| "wIn" |) ] ]] in
  (* Component *)
  do~ M.declare_component "dec" in
  do~ M.substitute_var "dec" [[ M.call_function ~(| "Decoder", [ M.var ~(| "nIn" |) ] |) ]] in
  (* Component *)
  do~ M.declare_component "ep" in
  (* Var *)
  do~ M.declare_var "k" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "k" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "k" |), M.var ~(| "wIn" |) |) ]] (
    do~ M.substitute_var "ep" [[ M.call_function ~(| "EscalarProduct", [ M.var ~(| "nIn" |) ] |) ]] in
    do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var ~(| "k" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "dec" [[ M.var ~(| "sel" |) ]] in
  (* Var *)
  do~ M.declare_var "j" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "j" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "j" |), M.var ~(| "wIn" |) |) ]] (
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "k" |), M.var ~(| "nIn" |) |) ]] (
      do~ M.substitute_var "ep" [[ M.var_access ~(| "inp", [Access.Array (M.var ~(| "k" |)); Access.Array (M.var ~(| "j" |))] |) ]] in
      do~ M.substitute_var "ep" [[ M.var_access ~(| "dec", [Access.Component "out"; Access.Array (M.var ~(| "k" |))] |) ]] in
      do~ M.substitute_var "k" [[ InfixOp.add ~(| M.var ~(| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access ~(| "ep", [Access.Array (M.var ~(| "j" |)); Access.Component "out"] |) ]] in
    do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var ~(| "j" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.equality_constraint
    [[ M.var_access ~(| "dec", [Access.Component "success"] |) ]]
    [[ 1 ]]
  in
  M.pure BlockUnit.Tt.
