(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module MainSignals.
  Record t : Set := {
    a : F.t;
    b : F.t;
    out : F.t;
  }.
End MainSignals.

(* Template body *)
Definition Main : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "a" [[ ([] : list F.t) ]] in
  (* Signal Input *)
  do~ M.declare_signal "b" [[ ([] : list F.t) ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ ([] : list F.t) ]] in
  (* Component *)
  do~ M.declare_component "sha256_2" in
  do~ M.substitute_var "sha256_2" [[ M.call_function ~(| "Sha256_2", ([] : list F.t) |) ]] in
  do~ M.substitute_var "sha256_2" [[ M.var (| "a" |) ]] in
  do~ M.substitute_var "sha256_2" [[ M.var (| "b" |) ]] in
  do~ M.substitute_var "out" [[ M.var_access (| "sha256_2", [Access.Component "out"] |) ]] in
  M.pure BlockUnit.Tt.
