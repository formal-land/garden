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
  | DeclareVar {A : Set} (name : string) (value : A) : t unit
  | DeclareSignal (name : string) (dimensions : list F.t) : t unit
  | DeclareComponent (name : string) : t unit
  | SubstituteVar {A : Set} (name : string) (value : A) : t unit
  | GetVarAccess {A : Set} (name : string) (accesses : list Access.t) : t A
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
  | Loop {Out : Set}
      (body : t (option Out))
      (k : Out -> t A)
  (** Explicit cut in the monadic expressions, to provide better composition for the proofs. *)
  | Let {B : Set} (e1 : t B) (k : B -> t A)
  (** Similar to [Let], a marker to help for the proofs. *)
  | Call {B : Set} (e : t B) (k : B -> t A)
  | Impossible (message : string).
  Arguments Pure {_}.
  Arguments Primitive {_ _}.
  Arguments Loop {_ _}.
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
    | Loop body k =>
      Loop body (fun result => let_ (k result) e2)
    | Let e1 k =>
      Let e1 (fun result => let_ (k result) e2)
    | Call e k =>
      Call e (fun result => let_ (k result) e2)
    | Impossible message => Impossible message
    end.

  Definition Do {R : Set} (block1 block2 : t (BlockUnit.t R)) : t (BlockUnit.t R) :=
    Let block1 (fun (result : BlockUnit.t R) =>
    match result with
    | BlockUnit.Tt => block2
    | BlockUnit.Return _ => block1
    end).

  Definition call {A : Set} (e : t A) : t A :=
    Call e Pure.

  (** This axiom is only used as a marker, we eliminate it later. *)
  Parameter run : forall {A : Set}, t A -> A.

  Definition wrap_in_scope {R : Set} (block : t R) : t R :=
    Primitive Primitive.OpenScope (fun _ =>
    let_ block (fun result =>
    Primitive Primitive.CloseScope (fun _ =>
    Pure result))).

  Fixpoint function_init_args (args : list (string * F.t)) : t unit :=
    match args with
    | [] => Pure tt
    | (name, value) :: args =>
      Primitive (Primitive.DeclareVar name value) (fun _ =>
      function_init_args args)
    end.

  Definition function_body {R : Set} (args : list (string * F.t)) (block : t (BlockUnit.t R)) :
      t R :=
    wrap_in_scope (
      let_ (function_init_args args) (fun _ =>
      Let block (fun (result : BlockUnit.t R) =>
      match result with
      | BlockUnit.Tt => Impossible "Expected a return in the function body"
      | BlockUnit.Return value => Pure value
      end))
    ).

  Fixpoint init_Set_from_dimensions (dimensions : list F.t) : Set :=
    match dimensions with
    | [] => F.t
    | _ :: dimensions => list (init_Set_from_dimensions dimensions)
    end.

  Fixpoint init_value_dimensions (dimensions : list F.t) : init_Set_from_dimensions dimensions :=
    match dimensions with
    | [] => 0
    | dimension :: dimensions =>
      List.repeat (init_value_dimensions dimensions) (Z.to_nat dimension)
    end.

  Definition declare_var {R : Set} (name : string) (dimensions : t (list F.t)) :
      t (BlockUnit.t R) :=
    let_ dimensions (fun dimensions =>
    Primitive (Primitive.DeclareVar name (init_value_dimensions dimensions)) (fun _ =>
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

  Definition var_access (name : string) (accesses : list Access.t) : t F.t :=
    Primitive (Primitive.GetVarAccess name accesses) Pure.

  Definition if_ {R : Set} (condition : t F.t) (then_ else_ : t (BlockUnit.t R)) :
      t (BlockUnit.t R) :=
    Let condition (fun condition =>
    if condition =? 0 then
      wrap_in_scope else_
    else
      wrap_in_scope then_).

  Definition while {R : Set} (condition : t F.t) (body : t (BlockUnit.t R)) : t (BlockUnit.t R) :=
    Loop
      (
        Let condition (fun condition =>
        if condition =? 0 then
          Pure (Some BlockUnit.Tt)
        else
          let_ (wrap_in_scope body) (fun result =>
          match result with
          | BlockUnit.Tt => Pure None
          | BlockUnit.Return _ => Pure (Some result)
          end))
      )
      Pure.

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
    (M.Do a b)
    (at level 200).

  Notation "e ~(| e1 , .. , en |)" :=
    (M.run (M.call ((.. (e e1) ..) en)))
    (at level 100).

  Notation "e ~(||)" :=
    (M.run (M.call e))
    (at level 100).

  Notation "e (| e1 , .. , en |)" :=
    (M.run ((.. (e e1) ..) en))
    (at level 100).

  Notation "e (||)" :=
    (M.run e)
    (at level 100).

  Notation "[[ e ]]" :=
    (* (M.Pure e) *)
    (ltac:(M.monadic e))
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

(** ** Semantics *)

Module Scope.
  (** We will use the scope only for symbolic computations, so that we do not need to prove any
      properties about its operations. *)
  Definition t : Set :=
    list (string * {A : Set @ A}).

  Definition empty : t :=
    [].
  Arguments empty /.

  Fixpoint get (scope : t) (name : string) : option {A : Set @ A} :=
    match scope with
    | [] => None
    | (name', value) :: scope' =>
      if String.eqb name name' then
        Some value
      else
        get scope' name
    end.

  Definition declare {A : Set} (scope : t) (name : string) (value : A) : t :=
    (name, existS _ value) :: scope.
  Arguments declare /.

  Fixpoint set {A : Set} (scope : t) (name : string) (value : A) : option t :=
    match scope with
    | [] => None
    | (name', value') :: scope' =>
      if String.eqb name name' then
        Some ((name, existS _ value) :: scope')
      else
        match set scope' name value with
        | Some scope' => Some ((name', value') :: scope')
        | None => None
        end
    end.
End Scope.

Module Scopes.
  (** We have a stack of scopes because there might be shadowing in sub-blocks. *)
  Definition t : Set :=
    list Scope.t.

  Definition empty : t :=
    [].
  Arguments empty /.

  Fixpoint get (scopes : t) (name : string) : option {A : Set @ A} :=
    match scopes with
    | [] => None
    | scope :: scopes' =>
      match Scope.get scope name with
      | Some value => Some value
      | None => get scopes' name
      end
    end.

  Fixpoint set {A : Set} (scopes : t) (name : string) (value : A) : option t :=
    match scopes with
    | [] => None
    | scope :: scopes' =>
      match Scope.set scope name value with
      | Some scope => Some (scope :: scopes')
      | None =>
        match set scopes' name value with
        | Some scopes' => Some (scope :: scopes')
        | None => None
        end
      end
    end.
End Scopes.

Module GetVarAccessArrays.
  Inductive t {Element : Set} :
      forall {Container : Set}, Container -> list Access.t -> Element -> Prop :=
  | Nil (element : Element) :
    t element [] element
  | Cons {SubContainer : Set}
      (index : F.t)
      (container : list SubContainer)
      (sub_container : SubContainer)
      (accesses : list Access.t)
      (element : Element) :
    t sub_container accesses element ->
    List.nth_error container (Z.to_nat index) = Some sub_container ->
    t container (Access.Array index :: accesses) element.
End GetVarAccessArrays.

Module Run.
  Reserved Notation "{{ p , state_in ⏩ e 🔽 output ⏩ state_out }}".

  Inductive t {A : Set} (p : Z) (output : A) (scopes_out : Scopes.t) :
      Scopes.t -> M.t A -> Prop :=
  | Pure :
    (* This should be the only case where the input and output states are the same. *)
    {{ p, scopes_out ⏩ M.Pure output 🔽 output ⏩ scopes_out }}
  | PrimitiveOpenScope
      (k : unit -> M.t A)
      (scopes_in : Scopes.t) :
    {{ p, Scope.empty :: scopes_in ⏩ k tt 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩
      M.Primitive Primitive.OpenScope k 🔽 output
    ⏩ scopes_out }}
  | PrimitiveCloseScope
      (k : unit -> M.t A)
      (scope_in : Scope.t)
      (scopes_in : Scopes.t) :
    {{ p, scopes_in ⏩ k tt 🔽 output ⏩ scopes_out }} ->
    {{ p, scope_in :: scopes_in ⏩
      M.Primitive Primitive.CloseScope k 🔽 output
    ⏩ scopes_out }}
  | PrimitiveGetPrime
      (k : Z -> M.t A)
      (scopes_in : Scopes.t) :
    {{ p, scopes_in ⏩ k p 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩
      M.Primitive Primitive.GetPrime k 🔽 output
    ⏩ scopes_out }}
  | PrimitiveDeclareVar {B : Set}
      (name : string)
      (value : B)
      (k : unit -> M.t A)
      (scope_in : Scope.t)
      (scopes_in : Scopes.t) :
    {{ p, Scope.declare scope_in name value :: scopes_in ⏩
      k tt 🔽 output
    ⏩ scopes_out }} ->
    {{ p, scope_in :: scopes_in ⏩
      M.Primitive (Primitive.DeclareVar name value) k 🔽 output
    ⏩ scopes_out }}
  | PrimitiveSubstituteVar {B : Set}
      (name : string)
      (value : B)
      (k : unit -> M.t A)
      (scopes_in scopes_inter : Scopes.t) :
    Scopes.set scopes_in name value = Some scopes_inter ->
    {{ p, scopes_inter ⏩
      k tt 🔽 output
    ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩
      M.Primitive (Primitive.SubstituteVar name value) k 🔽 output
    ⏩ scopes_out }}
  | PrimitiveGetVarAccess {Container Element : Set}
      (name : string)
      (accesses : list Access.t)
      (k : Element -> M.t A)
      (container : Container) (element : Element)
      (scopes_in : Scopes.t) :
    Scopes.get scopes_in name = Some (existS Container container) ->
    GetVarAccessArrays.t container accesses element ->
    {{ p, scopes_in ⏩ k element 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩
      M.Primitive (Primitive.GetVarAccess name accesses) k 🔽 output
    ⏩ scopes_out }}
  | LoopNext {Out : Set}
      (body : M.t (option Out))
      (k : Out -> M.t A)
      (scopes_in scopes_inter : Scopes.t) :
    {{ p, scopes_in ⏩ body 🔽 None ⏩ scopes_inter }} ->
    {{ p, scopes_inter ⏩ M.Loop body k 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.Loop body k 🔽 output ⏩ scopes_out }}
  | LoopStop {Out : Set}
      (body : M.t (option Out))
      (k : Out -> M.t A)
      (output_inter : Out)
      (scopes_in scopes_inter : Scopes.t) :
    {{ p, scopes_in ⏩ body 🔽 Some output_inter ⏩ scopes_inter }} ->
    {{ p, scopes_inter ⏩ k output_inter 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.Loop body k 🔽 output ⏩ scopes_out }}
  | Let {B : Set}
      (e : M.t B)
      (k : B -> M.t A)
      (output_inter : B)
      (scopes_in scopes_inter : Scopes.t) :
    {{ p, scopes_in ⏩ e 🔽 output_inter ⏩ scopes_inter }} ->
    {{ p, scopes_inter ⏩ k output_inter 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.Let e k 🔽 output ⏩ scopes_out }}
  | LetUnfold {B : Set}
      (e : M.t B)
      (k : B -> M.t A)
      (scopes_in : Scopes.t) :
    {{ p, scopes_in ⏩ M.let_ e k 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.Let e k 🔽 output ⏩ scopes_out }}
  | LetUnUnfold {B : Set}
      (e : M.t B)
      (k : B -> M.t A)
      (scopes_in : Scopes.t) :
    {{ p, scopes_in ⏩ M.Let e k 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.let_ e k 🔽 output ⏩ scopes_out }}
  | Call {B : Set}
      (e : M.t B)
      (k : B -> M.t A)
      (output_inter : B)
      (scopes_in : Scopes.t) :
    {{ p, Scopes.empty ⏩ e 🔽 output_inter ⏩ Scopes.empty }} ->
    {{ p, scopes_in ⏩ k output_inter 🔽 output ⏩ scopes_out }} ->
    {{ p, scopes_in ⏩ M.Call e k 🔽 output ⏩ scopes_out }}

  where "{{ p , scopes_in ⏩ e 🔽 output ⏩ scopes_out }}" :=
    (t p output scopes_out scopes_in e).

  Lemma Loop {A Out : Set} (p : Z)
      (body : M.t (option Out))
      (k : Out -> M.t A)
      (output : A)
      (output_inter : option Out)
      (scopes_in scopes_inter scopes_out : Scopes.t) :
    {{ p, scopes_in ⏩ body 🔽 output_inter ⏩ scopes_inter }} ->
    match output_inter with
    | None =>
      {{ p, scopes_inter ⏩ M.Loop body k 🔽 output ⏩ scopes_out }}
    | Some output_inter =>
      {{ p, scopes_inter ⏩ k output_inter 🔽 output ⏩ scopes_out }}
    end ->
    {{ p, scopes_in ⏩ M.Loop body k 🔽 output ⏩ scopes_out }}.
  Proof.
    intros H_body H_next.
    destruct output_inter as [output_inter|].
    { eapply LoopStop; eauto. }
    { eapply LoopNext; eauto. }
  Qed.
End Run.

Ltac run_deterministic :=
  repeat (
    cbn ||
    apply Run.PrimitiveOpenScope ||
    apply Run.PrimitiveCloseScope ||
    apply Run.PrimitiveDeclareVar ||
    (eapply Run.PrimitiveSubstituteVar; try reflexivity) ||
    (eapply Run.PrimitiveGetVarAccess; try now repeat constructor) ||
    eapply Run.PrimitiveGetPrime ||
    eapply Run.Loop ||
    eapply Run.Let ||
    eapply Run.Call ||
    apply Run.Pure
  ).
