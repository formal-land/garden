(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module SMTVerifierSMSignals.
  Record t : Set := {
    (* Input *)
    is0 : F.t;
    (* Input *)
    levIns : F.t;
    (* Input *)
    fnc : F.t;
    (* Input *)
    prev_top : F.t;
    (* Input *)
    prev_i0 : F.t;
    (* Input *)
    prev_iold : F.t;
    (* Input *)
    prev_inew : F.t;
    (* Input *)
    prev_na : F.t;
    (* Output *)
    st_top : F.t;
    (* Output *)
    st_i0 : F.t;
    (* Output *)
    st_iold : F.t;
    (* Output *)
    st_inew : F.t;
    (* Output *)
    st_na : F.t;
    (* Intermediate *)
    prev_top_lev_ins : F.t;
    (* Intermediate *)
    prev_top_lev_ins_fnc : F.t;
  }.

  Module IsNamed.
    Inductive P : forall (A : Set), (t -> A) -> string -> Prop :=
    | is0 : P _ is0 "is0"
    | levIns : P _ levIns "levIns"
    | fnc : P _ fnc "fnc"
    | prev_top : P _ prev_top "prev_top"
    | prev_i0 : P _ prev_i0 "prev_i0"
    | prev_iold : P _ prev_iold "prev_iold"
    | prev_inew : P _ prev_inew "prev_inew"
    | prev_na : P _ prev_na "prev_na"
    | st_top : P _ st_top "st_top"
    | st_i0 : P _ st_i0 "st_i0"
    | st_iold : P _ st_iold "st_iold"
    | st_inew : P _ st_inew "st_inew"
    | st_na : P _ st_na "st_na"
    | prev_top_lev_ins : P _ prev_top_lev_ins "prev_top_lev_ins"
    | prev_top_lev_ins_fnc : P _ prev_top_lev_ins_fnc "prev_top_lev_ins_fnc".
  End IsNamed.
End SMTVerifierSMSignals.

(* Template body *)
Definition SMTVerifierSM : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    (* Signal Input *)
    do~ M.declare_signal "is0" in
    (* Signal Input *)
    do~ M.declare_signal "levIns" in
    (* Signal Input *)
    do~ M.declare_signal "fnc" in
    (* Signal Input *)
    do~ M.declare_signal "prev_top" in
    (* Signal Input *)
    do~ M.declare_signal "prev_i0" in
    (* Signal Input *)
    do~ M.declare_signal "prev_iold" in
    (* Signal Input *)
    do~ M.declare_signal "prev_inew" in
    (* Signal Input *)
    do~ M.declare_signal "prev_na" in
    (* Signal Output *)
    do~ M.declare_signal "st_top" in
    (* Signal Output *)
    do~ M.declare_signal "st_i0" in
    (* Signal Output *)
    do~ M.declare_signal "st_iold" in
    (* Signal Output *)
    do~ M.declare_signal "st_inew" in
    (* Signal Output *)
    do~ M.declare_signal "st_na" in
    (* Signal Intermediate *)
    do~ M.declare_signal "prev_top_lev_ins" in
    (* Signal Intermediate *)
    do~ M.declare_signal "prev_top_lev_ins_fnc" in
    do~ M.substitute_var "prev_top_lev_ins" [] [[ InfixOp.mul ~(| M.var (| "prev_top" |), M.var (| "levIns" |) |) ]] in
    do~ M.substitute_var "prev_top_lev_ins_fnc" [] [[ InfixOp.mul ~(| M.var (| "prev_top_lev_ins" |), M.var (| "fnc" |) |) ]] in
    do~ M.substitute_var "st_top" [] [[ InfixOp.sub ~(| M.var (| "prev_top" |), M.var (| "prev_top_lev_ins" |) |) ]] in
    do~ M.substitute_var "st_inew" [] [[ InfixOp.sub ~(| M.var (| "prev_top_lev_ins" |), M.var (| "prev_top_lev_ins_fnc" |) |) ]] in
    do~ M.substitute_var "st_iold" [] [[ InfixOp.mul ~(| M.var (| "prev_top_lev_ins_fnc" |), InfixOp.sub ~(| 1, M.var (| "is0" |) |) |) ]] in
    do~ M.substitute_var "st_i0" [] [[ InfixOp.mul ~(| M.var (| "prev_top_lev_ins" |), M.var (| "is0" |) |) ]] in
    do~ M.substitute_var "st_na" [] [[ InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var (| "prev_na" |), M.var (| "prev_inew" |) |), M.var (| "prev_iold" |) |), M.var (| "prev_i0" |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition SMTVerifierSM_not_under_constrained is0 levIns fnc prev_top prev_i0 prev_iold prev_inew prev_na : Prop :=
  exists! st_top st_i0 st_iold st_inew st_na,
  exists prev_top_lev_ins prev_top_lev_ins_fnc,
  let signals := SMTVerifierSMSignals.Build_t is0 levIns fnc prev_top prev_i0 prev_iold prev_inew prev_na st_top st_i0 st_iold st_inew st_na prev_top_lev_ins prev_top_lev_ins_fnc in
  True (* NotUnderConstrained SMTVerifierSM signals *).
