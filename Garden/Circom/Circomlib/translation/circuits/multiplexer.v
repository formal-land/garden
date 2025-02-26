(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module EscalarProductSignals.
  Record t : Set := {
    (* Input *)
    in1 : list F.t;
    (* Input *)
    in2 : list F.t;
    (* Output *)
    out : F.t;
    (* Intermediate *)
    aux : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in1 : P _ in1 "in1"
    | in2 : P _ in2 "in2"
    | out : P _ out "out"
    | aux : P _ aux "aux".
  End IsNamed.
End EscalarProductSignals.

(* Template body *)
Definition EscalarProduct (w : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("w", w)] (
    (* Signal Input *)
    do~ M.declare_signal "in1" in
    (* Signal Input *)
    do~ M.declare_signal "in2" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "aux" in
    (* Var *)
    do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lc" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "w" |) |) ]] (
      do~ M.substitute_var "aux" [Access.Array (M.var (| "i" |))] [[ InfixOp.mul ~(| M.var_access (| "in1", [Access.Array (M.var (| "i" |))] |), M.var_access (| "in2", [Access.Array (M.var (| "i" |))] |) |) ]] in
      do~ M.substitute_var "lc" [] [[ InfixOp.add ~(| M.var (| "lc" |), M.var_access (| "aux", [Access.Array (M.var (| "i" |))] |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [] [[ M.var (| "lc" |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition EscalarProduct_not_under_constrained (w : F.t) in1 in2 : Prop :=
  exists! out,
  exists aux,
  let signals := EscalarProductSignals.Build_t in1 in2 out aux in
  True (* NotUnderConstrained EscalarProduct w signals *).

(* Template signals *)
Module DecoderSignals.
  Record t : Set := {
    (* Input *)
    inp : F.t;
    (* Output *)
    out : list F.t;
    (* Output *)
    success : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | inp : P _ inp "inp"
    | out : P _ out "out"
    | success : P _ success "success".
  End IsNamed.
End DecoderSignals.

(* Template body *)
Definition Decoder (w : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("w", w)] (
    (* Signal Input *)
    do~ M.declare_signal "inp" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Output *)
    do~ M.declare_signal "success" in
    (* Var *)
    do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lc" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "w" |) |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ ternary_expression (InfixOp.eq ~(| M.var (| "inp" |), M.var (| "i" |) |)) (1) (0) ]] in
      do~ M.equality_constraint
        [[ InfixOp.mul ~(| M.var_access (| "out", [Access.Array (M.var (| "i" |))] |), InfixOp.sub ~(| M.var (| "inp" |), M.var (| "i" |) |) |) ]]
        [[ 0 ]]
      in
      do~ M.substitute_var "lc" [] [[ InfixOp.add ~(| M.var (| "lc" |), M.var_access (| "out", [Access.Array (M.var (| "i" |))] |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "success" [] [[ M.var (| "lc" |) ]] in
    do~ M.equality_constraint
      [[ InfixOp.mul ~(| M.var (| "success" |), InfixOp.sub ~(| M.var (| "success" |), 1 |) |) ]]
      [[ 0 ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Decoder_not_under_constrained (w : F.t) inp : Prop :=
  exists! out success,
  let signals := DecoderSignals.Build_t inp out success in
  True (* NotUnderConstrained Decoder w signals *).

(* Template signals *)
Module MultiplexerSignals.
  Record t : Set := {
    (* Input *)
    inp : list (list F.t);
    (* Input *)
    sel : F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | inp : P _ inp "inp"
    | sel : P _ sel "sel"
    | out : P _ out "out".
  End IsNamed.
End MultiplexerSignals.

(* Template body *)
Definition Multiplexer (wIn nIn : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("wIn", wIn); ("nIn", nIn)] (
    (* Signal Input *)
    do~ M.declare_signal "inp" in
    (* Signal Input *)
    do~ M.declare_signal "sel" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Component *)
    do~ M.declare_component "dec" in
    do~ M.substitute_var "dec" [] [[ M.call_function ~(| "Decoder", [ M.var (| "nIn" |) ] |) ]] in
    (* Component *)
    do~ M.declare_component "ep" in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "wIn" |) |) ]] (
      do~ M.substitute_var "ep" [Access.Array (M.var (| "k" |))] [[ M.call_function ~(| "EscalarProduct", [ M.var (| "nIn" |) ] |) ]] in
      do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "dec" [Access.Component "inp"] [[ M.var (| "sel" |) ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "wIn" |) |) ]] (
      (* Var *)
      do~ M.declare_var "k" [[ ([] : list F.t) ]] in
      do~ M.substitute_var "k" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "k" |), M.var (| "nIn" |) |) ]] (
        do~ M.substitute_var "ep" [Access.Array (M.var (| "j" |)); Access.Component "in1"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "inp", [Access.Array (M.var (| "k" |)); Access.Array (M.var (| "j" |))] |) ]] in
        do~ M.substitute_var "ep" [Access.Array (M.var (| "j" |)); Access.Component "in2"; Access.Array (M.var (| "k" |))] [[ M.var_access (| "dec", [Access.Component "out"; Access.Array (M.var (| "k" |))] |) ]] in
        do~ M.substitute_var "k" [] [[ InfixOp.add ~(| M.var (| "k" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "out" [Access.Array (M.var (| "j" |))] [[ M.var_access (| "ep", [Access.Array (M.var (| "j" |)); Access.Component "out"] |) ]] in
      do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.equality_constraint
      [[ M.var_access (| "dec", [Access.Component "success"] |) ]]
      [[ 1 ]]
    in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Multiplexer_not_under_constrained (wIn nIn : F.t) inp sel : Prop :=
  exists! out,
  let signals := MultiplexerSignals.Build_t inp sel out in
  True (* NotUnderConstrained Multiplexer wIn nIn signals *).
