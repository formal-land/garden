Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope char_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
(* Global Open Scope Z_scope. *)
Global Open Scope bool_scope.

Export List.ListNotations.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Class Prime (p : Z) : Prop := {
  is_prime : IsPrime p;
}.

Module Felt.
  Definition t : Set :=
    Z.
End Felt.

Module Index.
  Definition t : Set :=
    nat.
End Index.

Module Array.
  Parameter t : Set -> list nat -> Set.

  Module MultiIndex.
    Fixpoint t (N : list nat) : Set :=
      match N with
      | nil => unit
      | _ :: N => Index.t * t N
      end.
  End MultiIndex.

  Parameter new : forall {A : Set} {N : list nat}, list A -> t A N.

  Parameter read : forall {A : Set} {N : list nat}, t A N -> MultiIndex.t N -> A.

  Parameter extract : forall {A : Set} {N M : list nat}, t A N -> list nat -> t A M.
End Array.

Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.

  Definition from {p} `{Prime p} (x : Z) : Z := 
    x mod p.
End UnOp.

Module BinOp.
  Definition add {p} `{Prime p} (x y : Z) : Z :=
    (x + y) mod p.

  Definition sub {p} `{Prime p} (x y : Z) : Z :=
    (x - y) mod p.

  Definition mul {p} `{Prime p} (x y : Z) : Z :=
    (x * y) mod p.

  Definition div {p} `{Prime p} (x y : Z) : Z :=
    (x / y) mod p.

  Definition mod_ {p} `{Prime p} (x y : Z) : Z :=
    (x mod y) mod p.
End BinOp.

Module M.
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | AssertEqual {A : Set} (x1 x2 : A) : t unit
  | AssertIn {A : Set} {N : nat} (x : A) (array : Array.t A [N]) : t unit
  | CreateStruct {A : Set} : t A
  | FieldWrite {A : Set} (field : A) (value : A) : t unit
  | Let {A B : Set} (e : t A) (k : A -> t B) : t B
  .

  Parameter For : nat -> nat -> nat -> (nat -> t unit) -> t unit.

  Definition Yield := @Pure.
  Arguments Yield {_}.
End M.

Notation "'let*' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).
