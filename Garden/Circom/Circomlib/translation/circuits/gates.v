(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module XORSignals.
  Record t : Set := {
    (* Input *)
    a : F.t;
    (* Input *)
    b : F.t;
    (* Output *)
    out : F.t;
  }.
End XORSignals.

(* Template body *)
Definition XOR : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.add ~(| M.var (| "a" |), M.var (| "b" |) |), InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var (| "a" |) |), M.var (| "b" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition XOR_not_under_constrained a b : Prop :=
  exists! out,
  let signals := XORSignals.Build_t a b out in
  True (* NotUnderConstrained XOR signals *).

(* Template signals *)
Module ANDSignals.
  Record t : Set := {
    (* Input *)
    a : F.t;
    (* Input *)
    b : F.t;
    (* Output *)
    out : F.t;
  }.
End ANDSignals.

(* Template body *)
Definition AND : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.mul ~(| M.var (| "a" |), M.var (| "b" |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition AND_not_under_constrained a b : Prop :=
  exists! out,
  let signals := ANDSignals.Build_t a b out in
  True (* NotUnderConstrained AND signals *).

(* Template signals *)
Module ORSignals.
  Record t : Set := {
    (* Input *)
    a : F.t;
    (* Input *)
    b : F.t;
    (* Output *)
    out : F.t;
  }.
End ORSignals.

(* Template body *)
Definition OR : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.add ~(| M.var (| "a" |), M.var (| "b" |) |), InfixOp.mul ~(| M.var (| "a" |), M.var (| "b" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition OR_not_under_constrained a b : Prop :=
  exists! out,
  let signals := ORSignals.Build_t a b out in
  True (* NotUnderConstrained OR signals *).

(* Template signals *)
Module NOTSignals.
  Record t : Set := {
    (* Input *)
    in_ : F.t;
    (* Output *)
    out : F.t;
  }.
End NOTSignals.

(* Template body *)
Definition NOT : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.add ~(| 1, M.var (| "in" |) |), InfixOp.mul ~(| 2, M.var (| "in" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition NOT_not_under_constrained in_ : Prop :=
  exists! out,
  let signals := NOTSignals.Build_t in_ out in
  True (* NotUnderConstrained NOT signals *).

(* Template signals *)
Module NANDSignals.
  Record t : Set := {
    (* Input *)
    a : F.t;
    (* Input *)
    b : F.t;
    (* Output *)
    out : F.t;
  }.
End NANDSignals.

(* Template body *)
Definition NAND : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.sub ~(| 1, InfixOp.mul ~(| M.var (| "a" |), M.var (| "b" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition NAND_not_under_constrained a b : Prop :=
  exists! out,
  let signals := NANDSignals.Build_t a b out in
  True (* NotUnderConstrained NAND signals *).

(* Template signals *)
Module NORSignals.
  Record t : Set := {
    (* Input *)
    a : F.t;
    (* Input *)
    b : F.t;
    (* Output *)
    out : F.t;
  }.
End NORSignals.

(* Template body *)
Definition NOR : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "out" [[ InfixOp.sub ~(| InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| M.var (| "a" |), M.var (| "b" |) |), 1 |), M.var (| "a" |) |), M.var (| "b" |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition NOR_not_under_constrained a b : Prop :=
  exists! out,
  let signals := NORSignals.Build_t a b out in
  True (* NotUnderConstrained NOR signals *).

(* Template signals *)
Module MultiANDSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : F.t;
  }.
End MultiANDSignals.

(* Template body *)
Definition MultiAND (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
    (* Component *)
    do~ M.declare_component "and1" in
    (* Component *)
    do~ M.declare_component "and2" in
    (* Component *)
    do~ M.declare_component "ands" in
    do~ M.if_ [[ InfixOp.eq ~(| M.var (| "n" |), 1 |) ]] (* then *) (
      do~ M.substitute_var "out" [[ M.var_access (| "in", [Access.Array (0)] |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "n" |), 2 |) ]] (* then *) (
        do~ M.substitute_var "and1" [[ M.call_function ~(| "AND", ([] : list F.t) |) ]] in
        do~ M.substitute_var "and1" [[ M.var_access (| "in", [Access.Array (0)] |) ]] in
        do~ M.substitute_var "and1" [[ M.var_access (| "in", [Access.Array (1)] |) ]] in
        do~ M.substitute_var "out" [[ M.var_access (| "and1", [Access.Component "out"] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "and2" [[ M.call_function ~(| "AND", ([] : list F.t) |) ]] in
        (* Var *)
        do~ M.declare_var "n1" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "n1" [[ InfixOp.intDiv ~(| M.var (| "n" |), 2 |) ]] in
        (* Var *)
        do~ M.declare_var "n2" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "n2" [[ InfixOp.sub ~(| M.var (| "n" |), InfixOp.intDiv ~(| M.var (| "n" |), 2 |) |) ]] in
        do~ M.substitute_var "ands" [[ M.call_function ~(| "MultiAND", [ M.var (| "n1" |) ] |) ]] in
        do~ M.substitute_var "ands" [[ M.call_function ~(| "MultiAND", [ M.var (| "n2" |) ] |) ]] in
        (* Var *)
        do~ M.declare_var "i" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "i" [[ 0 ]] in
        do~ M.substitute_var "i" [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n1" |) |) ]] (
          do~ M.substitute_var "ands" [[ M.var_access (| "in", [Access.Array (M.var (| "i" |))] |) ]] in
          do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "i" [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "n2" |) |) ]] (
          do~ M.substitute_var "ands" [[ M.var_access (| "in", [Access.Array (InfixOp.add ~(| M.var (| "n1" |), M.var (| "i" |) |))] |) ]] in
          do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        do~ M.substitute_var "and2" [[ M.var_access (| "ands", [Access.Array (0); Access.Component "out"] |) ]] in
        do~ M.substitute_var "and2" [[ M.var_access (| "ands", [Access.Array (1); Access.Component "out"] |) ]] in
        do~ M.substitute_var "out" [[ M.var_access (| "and2", [Access.Component "out"] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      M.pure BlockUnit.Tt
    ) in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition MultiAND_not_under_constrained (n : F.t) in_ : Prop :=
  exists! out,
  let signals := MultiANDSignals.Build_t in_ out in
  True (* NotUnderConstrained MultiAND n signals *).
