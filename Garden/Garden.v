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
  (** This is only an alias to the [Z] type, to represent field elements *)
  Definition t := Z.
End F.

Module BlockUnit.
  (** The return value of a code block. *)
  Inductive t {R : Set} : Set :=
  (** The default value *)
  | Tt
  (** The instruction `return` was called *)
  | Return (value : R).
  Arguments t : clear implicits.
End BlockUnit.

Module Access.
  Inductive t : Set :=
  | Component (name : string)
  | Array (index : F.t).
End Access.

Module Primitive.
  (** We group together primitives that share being impure functions operating over the state. *)
  Inductive t : Set -> Set :=
  | OpenScope : t unit
  | CloseScope : t unit
  | DeclareVar (name : string) (value : F.t) : t unit
  | DeclareSignal (name : string) (dimensions : list F.t) : t unit
  | DeclareComponent (name : string) : t unit
  | SubstituteVar {A : Set} (name : string) (value : A) : t unit
  | GetVarAccess (name : string) (access : list Access.t) : t F.t
  | GetPrime : t F.t
  | EqualityConstraint (value1 value2 : F.t) : t unit
  | CallFunction (name : string) (parameters : list F.t) : t F.t.
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

  Definition pure {A : Set} (output : A) : t A :=
    Pure output.

  (** A soft version of the [Let], where we unfold definitions *)
  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure output =>
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

  Definition do {R : Set} (block1 block2 : t (BlockUnit.t R)) : t (BlockUnit.t R) :=
    Let block1 (fun (result : BlockUnit.t R) =>
    match result with
    | BlockUnit.Tt => block2
    | BlockUnit.Return _ => block1
    end).

  Definition call {A : Set} (e : t A) : t A :=
    Call e Pure.

  (** This axiom is only used as a marker, we eliminate it later. *)
  Parameter run : forall {A : Set}, t A -> A.

  Definition function_body {R : Set} (block : t (BlockUnit.t R)) : t R :=
    Primitive Primitive.OpenScope (fun _ =>
    Let block (fun (result : BlockUnit.t R) =>
    Primitive Primitive.CloseScope (fun _ =>
    match result with
    | BlockUnit.Tt => Impossible "Expected a return in the function body"
    | BlockUnit.Return value => Pure value
    end))).

  (* TODO: use the dimensions *)
  Definition declare_var {R : Set} (name : string) (dimensions : t (list F.t)) :
      t (BlockUnit.t R) :=
    let_ dimensions (fun dimensions =>
    Primitive (Primitive.DeclareVar name 0) (fun _ =>
    Pure BlockUnit.Tt)).

  Definition declare_signal {R : Set} (name : string) (dimensions : t (list F.t)) :
      t (BlockUnit.t R) :=
    let_ dimensions (fun dimensions =>
    Primitive (Primitive.DeclareSignal name dimensions) (fun _ =>
    Pure BlockUnit.Tt)).

  Definition declare_component {R : Set} (name : string) : t (BlockUnit.t R) :=
    Primitive (Primitive.DeclareComponent name) (fun _ =>
    Pure BlockUnit.Tt).

  Definition substitute_var {R A : Set} (name : string) (value : t A) : t (BlockUnit.t R) :=
    let_ value (fun value =>
    Primitive (Primitive.SubstituteVar name value) (fun _ =>
    Pure BlockUnit.Tt)).

  Definition var (name : string) : t F.t :=
    Primitive (Primitive.GetVarAccess name []) Pure.

  Definition var_access (name : string) (access : list Access.t) : t F.t :=
    Primitive (Primitive.GetVarAccess name access) Pure.

  Definition if_ {R : Set} (condition : t F.t) (then_ else_ : t (BlockUnit.t R)) :
      t (BlockUnit.t R) :=
    let_ condition (fun condition =>
    if condition =? 0 then
      else_
    else
      then_).

  Parameter while : forall {R : Set}, t F.t -> t (BlockUnit.t R) -> t (BlockUnit.t R).

  Definition return_ {R : Set} (result : t R) : t (BlockUnit.t R) :=
    let_ result (fun result =>
    Pure (BlockUnit.Return result)).

  Definition get_prime : t F.t :=
    Primitive Primitive.GetPrime Pure.

  Definition equality_constraint {R : Set} (value1 value2 : t F.t) : t (BlockUnit.t R) :=
    let_ value1 (fun value1 =>
    let_ value2 (fun value2 =>
    Primitive (Primitive.EqualityConstraint value1 value2) (fun _ =>
    Pure BlockUnit.Tt))).

  Definition call_function (name : string) (parameters : list F.t) : t F.t :=
    Primitive (Primitive.CallFunction name parameters) Pure.

  Definition assert {R : Set} (condition : t F.t) : t (BlockUnit.t R) :=
    let_ condition (fun condition =>
    if condition =? 0 then
      Impossible "assert failure"
    else
      Pure BlockUnit.Tt).

  (** A tactic that replaces all [run] markers with a bind operation.
    This allows to represent programs without introducing
    explicit names for all intermediate computation results. *)
  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (let_ _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (let_ _ _);
              [ monadic y
              | let w := fresh "v" in
                intro w;
                let z := context ctxt [w] in
                monadic z
              ]
          end
        ]
    | context ctxt [run ?x] =>
      lazymatch context ctxt [run x] with
      | run x => monadic x
      | _ =>
        refine (let_ _ _);
          [ monadic x
          | let v := fresh "v" in
            intro v;
            let y := context ctxt [v] in
            monadic y
          ]
      end
    | _ =>
      lazymatch type of e with
      | t _ => exact e
      | _ => exact (pure e)
      end
    end.
End M.

Module Notations.
  Notation "'let*' x ':=' e 'in' k" :=
    (M.let_ e (fun x => k))
    (at level 200, x ident, e at level 200, k at level 200).

  Notation "'let~' x ':=' e 'in' k" :=
    (M.Let e (fun x => k))
    (at level 200, x ident, e at level 200, k at level 200).

  Notation "'do~' a 'in' b" :=
    (M.do a b)
    (at level 200).

  Notation "e ~(| e1 , .. , en |)" :=
    (M.run (M.call ((.. (e e1) ..) en)))
    (at level 100).

  Notation "e ~(||)" :=
    (M.run (M.call e))
    (at level 100).

  Notation "[[ e ]]" :=
    (M.Pure e)
    (* (ltac:(M.monadic e)) *)
    (only parsing).
End Notations.

Export Notations.

Definition ternary_expression (condition true_value false_value : F.t) : F.t :=
  if condition =? 0 then
    false_value
  else
    true_value.

Definition array_with_repeat {A : Set} (value : A) (size : F.t) : list A :=
  List.repeat value (Z.to_nat size).

(*
pub enum ExpressionPrefixOpcode {
    Sub,
    BoolNot,
    Complement,
}
*)
Module PrefixOp.
  Definition sub (a : F.t) : M.t F.t :=
    M.pure (- a).

  Definition boolNot (a : F.t) : M.t F.t :=
    M.pure (Z.lnot a).

  Parameter complement : F.t -> M.t F.t.
End PrefixOp.

(*
pub enum ExpressionInfixOpcode {
    Mul,
    Div,
    Add,
    Sub,
    Pow,
    IntDiv,
    Mod,
    ShiftL,
    ShiftR,
    LesserEq,
    GreaterEq,
    Lesser,
    Greater,
    Eq,
    NotEq,
    BoolOr,
    BoolAnd,
    BitOr,
    BitAnd,
    BitXor,
}
*)
Module InfixOp.
  Definition mul (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((a * b) mod p).

  Parameter div : F.t -> F.t -> M.t F.t.

  Definition add (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((a + b) mod p).

  Definition sub (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((a - b) mod p).

  Definition pow (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((a ^ b) mod p).

  Parameter intDiv : F.t -> F.t -> M.t F.t.

  Parameter mod_ : F.t -> F.t -> M.t F.t.

  Definition shiftL (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((Z.shiftl a b) mod p).

  Definition shiftR (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((Z.shiftr a b) mod p).

  Definition lesserEq (a b : F.t) : M.t F.t :=
    if a <=? b then
      M.pure 1
    else
      M.pure 0.

  Definition greaterEq (a b : F.t) : M.t F.t :=
    if a >=? b then
      M.pure 1
    else
      M.pure 0.

  Definition lesser (a b : F.t) : M.t F.t :=
    if a <? b then
      M.pure 1
    else
      M.pure 0.

  Definition greater (a b : F.t) : M.t F.t :=
    if a >? b then
      M.pure 1
    else
      M.pure 0.

  Definition eq (a b : F.t) : M.t F.t :=
    if a =? b then
      M.pure 1
    else
      M.pure 0.

  Definition notEq (a b : F.t) : M.t F.t :=
    if a =? b then
      M.pure 0
    else
      M.pure 1.

  Parameter boolOr : F.t -> F.t -> M.t F.t.

  Parameter boolAnd : F.t -> F.t -> M.t F.t.

  Definition bitAnd (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((Z.land a b) mod p).

  Definition bitOr (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((Z.lor a b) mod p).

  Definition bitXor (a b : F.t) : M.t F.t :=
    let* p := M.get_prime in
    M.pure ((Z.lxor a b) mod p).
End InfixOp.
