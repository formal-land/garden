Require Export Coq.Strings.Ascii.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
From Ltac2 Require Ltac2.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope char_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.
Arguments existS {_ _}.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module F.
  Definition t := Z.
End F.

Module BlockUnit.
  (** The return value of a code block. *)
  Inductive t : Set :=
  (** The default value *)
  | Tt
  (** The instruction `return` was called *)
  | Return (value : F.t).
End BlockUnit.

Module Primitive.
  (** We group together primitives that share being impure functions operating over the state. *)
  Inductive t : Set -> Set :=
  | OpenScope : t unit
  | CloseScope : t unit
  | DeclareVar (names : list string) (values : list F.t) : t unit
  | AssignVar (names : list string) (values : list F.t) : t unit
  | GetVar (name : string) : t F.t.
End Primitive.

Module M.
  Inductive t (A : Set) : Set :=
  | Pure
      (output : A)
  | Primitive {B : Set}
      (primitive : Primitive.t B)
      (k : B -> t A)
  | Loop {In Out : Set}
      (init : In)
      (body : In -> t Out)
      (** The final value to return if we decide to break of the loop, otherwise what to continue
          with. *)
      (break_with : Out -> In + Out)
      (k : Out -> t A)
  (** Explicit cut in the monadic expressions, to provide better composition for the proofs. *)
  | Let {B : Set} (e1 : t B) (k : B -> t A)
  (** Similar to [Let], a marker to help for the proofs. *)
  | Call {B : Set} (e : t B) (k : B -> t A)
  | Impossible (message : string).
  Arguments Pure {_}.
  Arguments Primitive {_ _}.
  Arguments Loop {_ _ _}.
  Arguments Let {_ _}.
  Arguments Call {_ _}.
  Arguments Impossible {_}.

  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure (output) =>
      e2 output
    | Primitive primitive k =>
      Primitive primitive (fun result => let_ (k result) e2)
    | Loop input body break_with k =>
      Loop input body break_with (fun result => let_ (k result) e2)
    | Let e1 k =>
      Let e1 (fun result => let_ (k result) e2)
    | Call e k =>
      Call e (fun result => let_ (k result) e2)
    | Impossible message => Impossible message
    end.

  Definition do (block1 block2 : t BlockUnit.t) : t BlockUnit.t :=
    Let block1 (fun (result : BlockUnit.t) =>
    match result with
    | BlockUnit.Tt => block2
    | BlockUnit.Return _ => block1
    end).

  Definition function_body (block : t BlockUnit.t) : t F.t :=
    Primitive Primitive.OpenScope (fun _ =>
    Let block (fun (result : BlockUnit.t) =>
    Primitive Primitive.CloseScope (fun _ =>
    match result with
    | BlockUnit.Tt => Impossible "Expected a return in the function body"
    | BlockUnit.Return value => Pure value
    end))).
End M.
