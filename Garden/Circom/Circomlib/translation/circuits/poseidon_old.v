(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SigmaSignals.
  Record t : Set := {
    (* Input *)
    in_ : F.t;
    (* Output *)
    out : F.t;
    (* Intermediate *)
    in2 : F.t;
    (* Intermediate *)
    in4 : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out"
    | in2 : P _ in2 "in2"
    | in4 : P _ in4 "in4".
  End IsNamed.
End SigmaSignals.

(* Template body *)
Definition Sigma : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Signal Intermediate *)
    do~ M.declare_signal "in2" in
    (* Signal Intermediate *)
    do~ M.declare_signal "in4" in
    do~ M.substitute_var "in2" [] [[ InfixOp.mul ~(| M.var (| "in" |), M.var (| "in" |) |) ]] in
    do~ M.substitute_var "in4" [] [[ InfixOp.mul ~(| M.var (| "in2" |), M.var (| "in2" |) |) ]] in
    do~ M.substitute_var "out" [] [[ InfixOp.mul ~(| M.var (| "in4" |), M.var (| "in" |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Sigma_not_under_constrained in_ : Prop :=
  exists! out,
  exists in2 in4,
  let signals := SigmaSignals.Build_t in_ out in2 in4 in
  True (* NotUnderConstrained Sigma signals *).

(* Template signals *)
Module ArkSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out".
  End IsNamed.
End ArkSignals.

(* Template body *)
Definition Ark (t C r : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("t", t); ("C", C); ("r", r)] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "t" |) |) ]] (
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ InfixOp.add ~(| M.var_access (| "in", [Access.Array (M.var (| "i" |))] |), M.var_access (| "C", [Access.Array (InfixOp.add ~(| M.var (| "i" |), M.var (| "r" |) |))] |) |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Ark_not_under_constrained (t C r : F.t) in_ : Prop :=
  exists! out,
  let signals := ArkSignals.Build_t in_ out in
  True (* NotUnderConstrained Ark t C r signals *).

(* Template signals *)
Module MixSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | in_ : P _ in_ "in"
    | out : P _ out "out".
  End IsNamed.
End MixSignals.

(* Template body *)
Definition Mix (t M : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("t", t); ("M", M)] (
    (* Signal Input *)
    do~ M.declare_signal "in" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "lc" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "lc" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "t" |) |) ]] (
      do~ M.substitute_var "lc" [] [[ 0 ]] in
      (* Var *)
      do~ M.declare_var "j" [[ ([] : list F.t) ]] in
      do~ M.substitute_var "j" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "t" |) |) ]] (
        do~ M.substitute_var "lc" [] [[ InfixOp.add ~(| M.var (| "lc" |), InfixOp.mul ~(| M.var_access (| "M", [Access.Array (M.var (| "i" |)); Access.Array (M.var (| "j" |))] |), M.var_access (| "in", [Access.Array (M.var (| "j" |))] |) |) |) ]] in
        do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "out" [Access.Array (M.var (| "i" |))] [[ M.var (| "lc" |) ]] in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Mix_not_under_constrained (t M : F.t) in_ : Prop :=
  exists! out,
  let signals := MixSignals.Build_t in_ out in
  True (* NotUnderConstrained Mix t M signals *).

(* Template signals *)
Module PoseidonSignals.
  Record t : Set := {
    (* Input *)
    inputs : list F.t;
    (* Output *)
    out : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | inputs : P _ inputs "inputs"
    | out : P _ out "out".
  End IsNamed.
End PoseidonSignals.

(* Template body *)
Definition Poseidon (nInputs : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("nInputs", nInputs)] (
    (* Signal Input *)
    do~ M.declare_signal "inputs" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Var *)
    do~ M.declare_var "N_ROUNDS_P" [[ [ 16 ] ]] in
    do~ M.substitute_var "N_ROUNDS_P" [] [[ array_with_repeat (0) (16) ]] in
    do~ M.substitute_var "N_ROUNDS_P" [] [[ [ 56; 57; 56; 60; 60; 63; 64; 63; 60; 66; 60; 65; 70; 60; 64; 68 ] ]] in
    (* Var *)
    do~ M.declare_var "t" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "t" [] [[ InfixOp.add ~(| M.var (| "nInputs" |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "nRoundsF" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nRoundsF" [] [[ 8 ]] in
    (* Var *)
    do~ M.declare_var "nRoundsP" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nRoundsP" [] [[ M.var_access (| "N_ROUNDS_P", [Access.Array (InfixOp.sub ~(| M.var (| "t" |), 2 |))] |) ]] in
    (* Var *)
    do~ M.declare_var "C" [[ [ InfixOp.mul ~(| M.var (| "t" |), InfixOp.add ~(| M.var (| "nRoundsF" |), M.var (| "nRoundsP" |) |) |) ] ]] in
    do~ M.substitute_var "C" [] [[ array_with_repeat (0) (InfixOp.mul ~(| M.var (| "t" |), InfixOp.add ~(| M.var (| "nRoundsF" |), M.var (| "nRoundsP" |) |) |)) ]] in
    do~ M.substitute_var "C" [] [[ M.call_function ~(| "POSEIDON_C", [ M.var (| "t" |) ] |) ]] in
    (* Var *)
    do~ M.declare_var "M" [[ [ M.var (| "t" |); M.var (| "t" |) ] ]] in
    do~ M.substitute_var "M" [] [[ array_with_repeat (array_with_repeat (0) (M.var (| "t" |))) (M.var (| "t" |)) ]] in
    do~ M.substitute_var "M" [] [[ M.call_function ~(| "POSEIDON_M", [ M.var (| "t" |) ] |) ]] in
    (* Component *)
    do~ M.declare_component "ark" in
    (* Component *)
    do~ M.declare_component "sigmaF" in
    (* Component *)
    do~ M.declare_component "sigmaP" in
    (* Component *)
    do~ M.declare_component "mix" in
    (* Var *)
    do~ M.declare_var "k" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "k" [] [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [] [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), InfixOp.add ~(| M.var (| "nRoundsF" |), M.var (| "nRoundsP" |) |) |) ]] (
      do~ M.substitute_var "ark" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "Ark", [ M.var (| "t" |); M.var (| "C" |); InfixOp.mul ~(| M.var (| "t" |), M.var (| "i" |) |) ] |) ]] in
      (* Var *)
      do~ M.declare_var "j" [[ ([] : list F.t) ]] in
      do~ M.substitute_var "j" [] [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "t" |) |) ]] (
        do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
          do~ M.if_ [[ InfixOp.greater ~(| M.var (| "j" |), 0 |) ]] (* then *) (
            do~ M.substitute_var "ark" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ M.var_access (| "inputs", [Access.Array (InfixOp.sub ~(| M.var (| "j" |), 1 |))] |) ]] in
            M.pure BlockUnit.Tt
          ) (* else *) (
            do~ M.substitute_var "ark" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ 0 ]] in
            M.pure BlockUnit.Tt
          ) in
          M.pure BlockUnit.Tt
        ) (* else *) (
          do~ M.substitute_var "ark" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ M.var_access (| "mix", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (M.var (| "j" |))] |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.if_ [[ InfixOp.boolOr ~(| InfixOp.lesser ~(| M.var (| "i" |), InfixOp.div ~(| M.var (| "nRoundsF" |), 2 |) |), InfixOp.greaterEq ~(| M.var (| "i" |), InfixOp.add ~(| M.var (| "nRoundsP" |), InfixOp.div ~(| M.var (| "nRoundsF" |), 2 |) |) |) |) ]] (* then *) (
        do~ M.substitute_var "k" [] [[ ternary_expression (InfixOp.lesser ~(| M.var (| "i" |), InfixOp.div ~(| M.var (| "nRoundsF" |), 2 |) |)) (M.var (| "i" |)) (InfixOp.sub ~(| M.var (| "i" |), M.var (| "nRoundsP" |) |)) ]] in
        do~ M.substitute_var "mix" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "Mix", [ M.var (| "t" |); M.var (| "M" |) ] |) ]] in
        (* Var *)
        do~ M.declare_var "j" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "j" [] [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "t" |) |) ]] (
          do~ M.substitute_var "sigmaF" [Access.Array (M.var (| "k" |)); Access.Array (M.var (| "j" |))] [[ M.call_function ~(| "Sigma", ([] : list F.t) |) ]] in
          do~ M.substitute_var "sigmaF" [Access.Array (M.var (| "k" |)); Access.Array (M.var (| "j" |)); Access.Component "in"] [[ M.var_access (| "ark", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (M.var (| "j" |))] |) ]] in
          do~ M.substitute_var "mix" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ M.var_access (| "sigmaF", [Access.Array (M.var (| "k" |)); Access.Array (M.var (| "j" |)); Access.Component "out"] |) ]] in
          do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "k" [] [[ InfixOp.sub ~(| M.var (| "i" |), InfixOp.div ~(| M.var (| "nRoundsF" |), 2 |) |) ]] in
        do~ M.substitute_var "mix" [Access.Array (M.var (| "i" |))] [[ M.call_function ~(| "Mix", [ M.var (| "t" |); M.var (| "M" |) ] |) ]] in
        do~ M.substitute_var "sigmaP" [Access.Array (M.var (| "k" |))] [[ M.call_function ~(| "Sigma", ([] : list F.t) |) ]] in
        do~ M.substitute_var "sigmaP" [Access.Array (M.var (| "k" |)); Access.Component "in"] [[ M.var_access (| "ark", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "mix" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (0)] [[ M.var_access (| "sigmaP", [Access.Array (M.var (| "k" |)); Access.Component "out"] |) ]] in
        (* Var *)
        do~ M.declare_var "j" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "j" [] [[ 1 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "t" |) |) ]] (
          do~ M.substitute_var "mix" [Access.Array (M.var (| "i" |)); Access.Component "in"; Access.Array (M.var (| "j" |))] [[ M.var_access (| "ark", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (M.var (| "j" |))] |) ]] in
          do~ M.substitute_var "j" [] [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [] [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [] [[ M.var_access (| "mix", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| M.var (| "nRoundsF" |), M.var (| "nRoundsP" |) |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Poseidon_not_under_constrained (nInputs : F.t) inputs : Prop :=
  exists! out,
  let signals := PoseidonSignals.Build_t inputs out in
  True (* NotUnderConstrained Poseidon nInputs signals *).
