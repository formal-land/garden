Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import ListNotations.

Module Sponges.
  Parameter t : Set.
End Sponges.

Class Mul (A : Type) := {
  mul : A -> A -> A
}.

Class Add (A : Type) := {
  add : A -> A -> A
}.

Class Sub (A : Type) := {
  sub : A -> A -> A
}.

Class Clone (A : Type) := {
  clone : A -> A
}.

Class Debug (A : Type) := {
  debug : A -> string (* Assuming Debug generates a string representation *)
}.

Class One (A : Type) := {
  one : A
}.

Class Zero (A : Type) := {
  zero : A
}.


Class Interpreter_Variable (A : Type) `{Mul A, Add A, Sub A, Clone A, Debug A, One A, Zero A} := {}.


Inductive Steps :=
| Round : nat -> Steps
| Sponge : Sponges.t -> Steps.

(* Define Keccak Module *)
Module Keccak.
  Definition constrain_theta {T : Type} `{Interpreter_Variable T}
    (self : Type) (step : Steps) : list (list (list T)). Admitted.
End Keccak.