(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SMTProcessorLevelSignals.
  Record t : Set := {
    (* Input *)
    st_top : F.t;
    (* Input *)
    st_old0 : F.t;
    (* Input *)
    st_bot : F.t;
    (* Input *)
    st_new1 : F.t;
    (* Input *)
    st_na : F.t;
    (* Input *)
    st_upd : F.t;
    (* Output *)
    oldRoot : F.t;
    (* Output *)
    newRoot : F.t;
    (* Input *)
    sibling : F.t;
    (* Input *)
    old1leaf : F.t;
    (* Input *)
    new1leaf : F.t;
    (* Input *)
    newlrbit : F.t;
    (* Input *)
    oldChild : F.t;
    (* Input *)
    newChild : F.t;
    (* Intermediate *)
    aux : list F.t;
  }.
End SMTProcessorLevelSignals.

(* Template body *)
Definition SMTProcessorLevel : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "st_top" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "st_old0" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "st_bot" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "st_new1" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "st_na" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "st_upd" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "oldRoot" [[ ([] : list F.t) ]] in
    (* Signal Output *)
    do~ M.declare_signal "newRoot" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "sibling" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "old1leaf" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "new1leaf" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "newlrbit" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "oldChild" [[ ([] : list F.t) ]] in
    (* Signal Input *)
    do~ M.declare_signal "newChild" [[ ([] : list F.t) ]] in
    (* Signal Intermediate *)
    do~ M.declare_signal "aux" [[ [ 4 ] ]] in
    (* Component *)
    do~ M.declare_component "oldProofHash" in
    do~ M.substitute_var "oldProofHash" [[ M.call_function ~(| "SMTHash2", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "newProofHash" in
    do~ M.substitute_var "newProofHash" [[ M.call_function ~(| "SMTHash2", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "oldSwitcher" in
    do~ M.substitute_var "oldSwitcher" [[ M.call_function ~(| "Switcher", ([] : list F.t) |) ]] in
    (* Component *)
    do~ M.declare_component "newSwitcher" in
    do~ M.substitute_var "newSwitcher" [[ M.call_function ~(| "Switcher", ([] : list F.t) |) ]] in
    do~ M.substitute_var "oldSwitcher" [[ M.var (| "oldChild" |) ]] in
    do~ M.substitute_var "oldSwitcher" [[ M.var (| "sibling" |) ]] in
    do~ M.substitute_var "oldSwitcher" [[ M.var (| "newlrbit" |) ]] in
    do~ M.substitute_var "oldProofHash" [[ M.var_access (| "oldSwitcher", [Access.Component "outL"] |) ]] in
    do~ M.substitute_var "oldProofHash" [[ M.var_access (| "oldSwitcher", [Access.Component "outR"] |) ]] in
    do~ M.substitute_var "aux" [[ InfixOp.mul ~(| M.var (| "old1leaf" |), InfixOp.add ~(| InfixOp.add ~(| M.var (| "st_bot" |), M.var (| "st_new1" |) |), M.var (| "st_upd" |) |) |) ]] in
    do~ M.substitute_var "oldRoot" [[ InfixOp.add ~(| M.var_access (| "aux", [Access.Array (0)] |), InfixOp.mul ~(| M.var_access (| "oldProofHash", [Access.Component "out"] |), M.var (| "st_top" |) |) |) ]] in
    do~ M.substitute_var "aux" [[ InfixOp.mul ~(| M.var (| "newChild" |), InfixOp.add ~(| M.var (| "st_top" |), M.var (| "st_bot" |) |) |) ]] in
    do~ M.substitute_var "newSwitcher" [[ InfixOp.add ~(| M.var_access (| "aux", [Access.Array (1)] |), InfixOp.mul ~(| M.var (| "new1leaf" |), M.var (| "st_new1" |) |) |) ]] in
    do~ M.substitute_var "aux" [[ InfixOp.mul ~(| M.var (| "sibling" |), M.var (| "st_top" |) |) ]] in
    do~ M.substitute_var "newSwitcher" [[ InfixOp.add ~(| M.var_access (| "aux", [Access.Array (2)] |), InfixOp.mul ~(| M.var (| "old1leaf" |), M.var (| "st_new1" |) |) |) ]] in
    do~ M.substitute_var "newSwitcher" [[ M.var (| "newlrbit" |) ]] in
    do~ M.substitute_var "newProofHash" [[ M.var_access (| "newSwitcher", [Access.Component "outL"] |) ]] in
    do~ M.substitute_var "newProofHash" [[ M.var_access (| "newSwitcher", [Access.Component "outR"] |) ]] in
    do~ M.substitute_var "aux" [[ InfixOp.mul ~(| M.var_access (| "newProofHash", [Access.Component "out"] |), InfixOp.add ~(| InfixOp.add ~(| M.var (| "st_top" |), M.var (| "st_bot" |) |), M.var (| "st_new1" |) |) |) ]] in
    do~ M.substitute_var "newRoot" [[ InfixOp.add ~(| M.var_access (| "aux", [Access.Array (3)] |), InfixOp.mul ~(| M.var (| "new1leaf" |), InfixOp.add ~(| M.var (| "st_old0" |), M.var (| "st_upd" |) |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SMTProcessorLevel_not_under_constrained st_top st_old0 st_bot st_new1 st_na st_upd sibling old1leaf new1leaf newlrbit oldChild newChild : Prop :=
  exists! oldRoot newRoot,
  exists aux,
  let signals := SMTProcessorLevelSignals.Build_t st_top st_old0 st_bot st_new1 st_na st_upd oldRoot newRoot sibling old1leaf new1leaf newlrbit oldChild newChild aux in
  True (* NotUnderConstrained SMTProcessorLevel signals *).
