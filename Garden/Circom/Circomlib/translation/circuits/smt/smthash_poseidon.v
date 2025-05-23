(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SMTHash1Signals.
  Record t : Set := {
    (* Input *)
    key : F.t;
    (* Input *)
    value : F.t;
    (* Output *)
    out : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | key : P _ key "key"
    | value : P _ value "value"
    | out : P _ out "out".
  End IsNamed.
End SMTHash1Signals.

(* Template body *)
Definition SMTHash1 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "key" in
    (* Signal Input *)
    do~ M.declare_signal "value" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Component *)
    do~ M.declare_component "h" in
    do~ M.substitute_var "h" [] [[ M.call_function ~(| "Poseidon", [ 3 ] |) ]] in
    do~ M.substitute_var "h" [Access.Component "inputs"; Access.Array (0)] [[ M.var (| "key" |) ]] in
    do~ M.substitute_var "h" [Access.Component "inputs"; Access.Array (1)] [[ M.var (| "value" |) ]] in
    do~ M.substitute_var "h" [Access.Component "inputs"; Access.Array (2)] [[ 1 ]] in
    do~ M.substitute_var "out" [] [[ M.var_access (| "h", [Access.Component "out"] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SMTHash1_not_under_constrained key value : Prop :=
  exists! out,
  let signals := SMTHash1Signals.Build_t key value out in
  True (* NotUnderConstrained SMTHash1 signals *).

(* Template signals *)
Module SMTHash2Signals.
  Record t : Set := {
    (* Input *)
    L : F.t;
    (* Input *)
    R : F.t;
    (* Output *)
    out : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | L : P _ L "L"
    | R : P _ R "R"
    | out : P _ out "out".
  End IsNamed.
End SMTHash2Signals.

(* Template body *)
Definition SMTHash2 : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "L" in
    (* Signal Input *)
    do~ M.declare_signal "R" in
    (* Signal Output *)
    do~ M.declare_signal "out" in
    (* Component *)
    do~ M.declare_component "h" in
    do~ M.substitute_var "h" [] [[ M.call_function ~(| "Poseidon", [ 2 ] |) ]] in
    do~ M.substitute_var "h" [Access.Component "inputs"; Access.Array (0)] [[ M.var (| "L" |) ]] in
    do~ M.substitute_var "h" [Access.Component "inputs"; Access.Array (1)] [[ M.var (| "R" |) ]] in
    do~ M.substitute_var "out" [] [[ M.var_access (| "h", [Access.Component "out"] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SMTHash2_not_under_constrained L R : Prop :=
  exists! out,
  let signals := SMTHash2Signals.Build_t L R out in
  True (* NotUnderConstrained SMTHash2 signals *).
