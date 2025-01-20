(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module EscalarMulWindowSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Input *)
    sel : list F.t;
    (* Output *)
    out : list F.t;
  }.
End EscalarMulWindowSignals.

(* Template body *)
Definition EscalarMulWindow (base k : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("base", base); ("k", k)] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ 2 ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "sel" [[ [ 4 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 2 ] ]] in
    (* Var *)
    do~ M.declare_var "table" [[ [ 16; 2 ] ]] in
    do~ M.substitute_var "table" [[ array_with_repeat (array_with_repeat (0) (2)) (16) ]] in
    (* Component *)
    do~ M.declare_component "mux" in
    (* Component *)
    do~ M.declare_component "adder" in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.substitute_var "table" [[ M.call_function ~(| "EscalarMulW4Table", [ M.var (| "base" |); M.var (| "k" |) ] |) ]] in
    do~ M.substitute_var "mux" [[ M.call_function ~(| "MultiMux4", [ 2 ] |) ]] in
    do~ M.substitute_var "adder" [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 4 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "sel", [Access.Array (M.var (| "i" |))] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 16 |) ]] (
      do~ M.substitute_var "mux" [[ M.var_access (| "table", [Access.Array (M.var (| "i" |)); Access.Array (0)] |) ]] in
      do~ M.substitute_var "mux" [[ M.var_access (| "table", [Access.Array (M.var (| "i" |)); Access.Array (1)] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "adder" [[ M.var_access (| "in", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "adder" [[ M.var_access (| "in", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "adder" [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "adder" [[ M.var_access (| "mux", [Access.Component "out"; Access.Array (1)] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "adder", [Access.Component "xout"] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "adder", [Access.Component "yout"] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition EscalarMulWindow_not_under_constrained (base k : F.t) in_ sel : Prop :=
  exists! out,
  let signals := EscalarMulWindowSignals.Build_t in_ sel out in
  True (* NotUnderConstrained EscalarMulWindow base k signals *).

(* Template signals *)
Module EscalarMulSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Input *)
    inp : list F.t;
    (* Output *)
    out : list F.t;
  }.
End EscalarMulSignals.

(* Template body *)
Definition EscalarMul (n base : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n); ("base", base)] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Input *)
    do~ M.declare_signal "inp" [[ [ 2 ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 2 ] ]] in
    (* Var *)
    do~ M.declare_var "nBlocks" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nBlocks" [[ InfixOp.add ~(| InfixOp.shiftR ~(| InfixOp.sub ~(| M.var (| "n" |), 1 |), 2 |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [[ 0 ]] in
    (* Component *)
    do~ M.declare_component "windows" in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nBlocks" |) |) ]] (
      do~ M.substitute_var "windows" [[ M.call_function ~(| "EscalarMulWindow", [ M.var (| "base" |); M.var (| "i" |) ] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nBlocks" |) |) ]] (
      do~ M.substitute_var "j" [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), 4 |) ]] (
        do~ M.if_ [[ InfixOp.greaterEq ~(| InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 4 |), M.var (| "j" |) |), M.var (| "n" |) |) ]] (* then *) (
          do~ M.substitute_var "windows" [[ 0 ]] in
          M.pure BlockUnit.Tt
        ) (* else *) (
          do~ M.substitute_var "windows" [[ M.var_access (| "in", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 4 |), M.var (| "j" |) |))] |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "windows" [[ M.var_access (| "inp", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "windows" [[ M.var_access (| "inp", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), InfixOp.sub ~(| M.var (| "nBlocks" |), 1 |) |) ]] (
      do~ M.substitute_var "windows" [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "windows" [[ M.var_access (| "windows", [Access.Array (M.var (| "i" |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "nBlocks" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "windows", [Access.Array (InfixOp.sub ~(| M.var (| "nBlocks" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition EscalarMul_not_under_constrained (n base : F.t) in_ inp : Prop :=
  exists! out,
  let signals := EscalarMulSignals.Build_t in_ inp out in
  True (* NotUnderConstrained EscalarMul n base signals *).
