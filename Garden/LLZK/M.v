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
Global Open Scope Z_scope.
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

Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.

  Axiom inv : forall {p} `{Prime p} (x : Z), Z.

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

Module BoolCmp.
  Inductive t : Set :=
  | Eq : t
  | Neq : t
  | Lt : t
  | Gt : t
  | Leq : t
  | Geq : t.
End BoolCmp.

Module Bool.
  Axiom cmp : forall {p} `{Prime p} (cmp : BoolCmp.t) (x y : Z), bool.

  Axiom and : forall (x y : bool), bool.
  Axiom or : forall (x y : bool), bool.
  Axiom xor : forall (x y : bool), bool.
  Axiom not : forall (x : bool), bool.
End Bool.

Module Array.
  Module MultiIndex.
    Fixpoint t (Ns : list nat) : Set :=
      match Ns with
      | nil => unit
      | _ :: Ns => Index.t * t Ns
      end.

    Module Valid.
      Fixpoint t {Ns : list nat} (indexes : MultiIndex.t Ns) : Prop :=
        match Ns, indexes with
        | nil, _ => True
        | N :: Ns, (index, indexes) =>
          (index < N)%nat /\ t indexes
        end.
    End Valid.

    Fixpoint concat {Ns Ms : list nat}
        (indexes : MultiIndex.t Ns)
        (indexes' : MultiIndex.t Ms) :
        MultiIndex.t (Ns ++ Ms) :=
      match Ns, indexes with
      | nil, _ => indexes'
      | _ :: Ns, (index, indexes) => (index, concat indexes indexes')
      end.
  End MultiIndex.

  Record t {A : Set} {Ns : list nat} := {
    get : MultiIndex.t Ns -> A;
  }.
  Arguments t : clear implicits.

  (** A special dimension that can be used to represent any dimension. This is only used in special
      functions like logging. *)
  Parameter dimension_any : nat.

  (* TODO: remove *)
  Parameter affine_map : nat.

  (** How to get an index into the flat list of values *)
  Fixpoint new_aux (Ns : list nat) (indexes : MultiIndex.t Ns) : nat :=
    match Ns, indexes with
    | nil, _ => 0
    | N :: Ns, (index, indexes) => index + N * new_aux Ns indexes
    end.

  Definition new {p} `{Prime p} {Ns : list nat} (l : list Felt.t) : t Felt.t Ns :=
    {|
      get indexes := List.nth (new_aux Ns indexes) l (UnOp.from 0);
    |}.

  Definition len {A : Set} {Ns : list nat} (array : t A Ns) (index : Index.t) : Index.t :=
    List.nth index Ns 0%nat.

  Definition read {A : Set} {Ns : list nat} (array : t A Ns) : MultiIndex.t Ns -> A :=
    array.(get).

  Definition extract {A : Set} {Ns Ms : list nat}
      (array : t A (Ns ++ Ms))
      (indexes : MultiIndex.t Ns) :
      t A Ms :=
    {|
      get indexes' := array.(get) (MultiIndex.concat indexes indexes');
    |}.

  Module IsIn.
    Definition t {A : Set} {Ns : list nat} (x : A) (array : t A Ns) : Prop :=
      exists indexes,
        Array.MultiIndex.Valid.t indexes /\
        Array.read array indexes = x.
  End IsIn.
End Array.

Module M.
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | AssertEqual {A : Set} (x1 x2 : A) : t unit
  | AssertIn {A : Set} {Ns : list nat} (x : A) (array : Array.t A Ns) : t unit
  | AssertBool (value : bool) : t unit
  | CreateStruct {A : Set} : t A
  | ArrayWrite {A : Set} {Ns : list nat}
      (array : Array.t A Ns)
      (indexes : Array.MultiIndex.t Ns)
      (value : A) :
      t unit
  | FieldWrite {A : Set} (field : A) (value : A) : t unit
  | Let {A B : Set} (e : t A) (k : A -> t B) : t B
  .
End M.

Notation "'let*' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Definition yield := @M.Pure.
Arguments yield {_}.

Fixpoint iter (actions : list (M.t unit)) : M.t unit :=
  match actions with
  | nil => M.Pure tt
  | action :: actions =>
    let* _ := action in
    iter actions
  end.

Parameter for_ : nat -> nat -> nat -> (nat -> M.t unit) -> M.t unit.

(** To start with, we will only reason on for loops with step 1. *)
Definition for_step_one (start end_ : nat) (body : nat -> M.t unit) : M.t unit :=
  let indexes : list nat := List.seq start end_ in
  iter (List.map body indexes).

Axiom for_step_one_eq : forall (start end_ : nat) (body : nat -> M.t unit),
  for_ start end_ 1 body = for_step_one start end_ body.

Module RunCompute.
  Reserved Notation "{{ e 🔽 output }}".

  Inductive t : forall {A : Set}, M.t A -> A -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ M.Pure value 🔽 value }}
  | CreateStruct {A : Set} (value : A) :
    {{ M.CreateStruct 🔽 value }}
  | ArrayWrite {A : Set} {Ns : list nat} (array : Array.t A Ns) (indexes : Array.MultiIndex.t Ns) (value : A) :
    Array.read array indexes = value ->
    {{ M.ArrayWrite array indexes value 🔽 tt }}
  | FieldWrite {A : Set} (field : A) :
    {{ M.FieldWrite field field 🔽 tt }}
  | Let {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) :
    {{ e 🔽 value }} ->
    {{ k value 🔽 output }} ->
    {{ M.Let e k 🔽 output }}

  where "{{ e 🔽 output }}" := (t e output).
End RunCompute.
Export RunCompute.

Module RunConstrain.
  Reserved Notation "{{ e 🔽 output , P }}".

  Inductive t : forall {A : Set}, M.t A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ M.Pure value 🔽 value, True }}
  | AssertEqual {A : Set} (x1 x2 : A) :
    {{ M.AssertEqual x1 x2 🔽 tt, x1 = x2 }}
  | AssertIn {A : Set} {Ns : list nat} (x : A) (array : Array.t A Ns) :
    {{ M.AssertIn x array 🔽
      tt, exists indexes, Array.MultiIndex.Valid.t indexes /\ Array.read array indexes = x
    }}
  | Compute {A : Set} (e : M.t A) (value : A) :
    {{ e 🔽 value }} ->
    {{ e 🔽 value, True }}
  | Let {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 -> {{ k value 🔽 output, P2 }}) ->
    {{ M.Let e k 🔽 output, P1 /\ P2 }}
  | Implies {A : Set} (e : M.t A) (value : A) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 -> P2) ->
    {{ e 🔽 value, P2 }}
  | Replace {A : Set} (e : M.t A) (value1 value2 : A) (P : Prop) :
    {{ e 🔽 value1, P }} ->
    value1 = value2 ->
    {{ e 🔽 value2, P }}

  where "{{ e 🔽 output , P }}" := (t e output P).
End RunConstrain.
Export RunConstrain.

Class MapMod {p : Z} `{Prime p} (A : Set) : Set := {
  map_mod : A -> A;
}.

Global Instance MapMod_Felt {p} `{Prime p} : MapMod Felt.t := {
  map_mod := UnOp.from;
}.

Global Instance MapMod_Array {p} `{Prime p} (A : Set) `{MapMod p A} (Ns : list nat) :
    MapMod (Array.t A Ns) := {
  map_mod x := {|
    Array.get indexes := map_mod (x.(Array.get) indexes);
  |};
}.

Class CanCastToFelt {p : Z} `{Prime p} (A : Set) : Set := {
  cast_to_felt : A -> Felt.t;
}.

Global Instance CanCastToFelt_Felt {p} `{Prime p} : CanCastToFelt Felt.t := {
  cast_to_felt := id;
}.

Global Instance CanCastToFelt_Index {p} `{Prime p} : CanCastToFelt Index.t := {
  cast_to_felt x := Z.of_nat x mod p;
}.

Global Instance CanCastToFelt_Bool {p} `{Prime p} : CanCastToFelt bool := {
  cast_to_felt := Z.b2z;
}.

Class CanCastToIndex {p : Z} `{Prime p} (A : Set) : Set := {
  cast_to_index : A -> Index.t;
}.

Global Instance CanCastToIndex_Felt {p} `{Prime p} : CanCastToIndex Felt.t := {
  cast_to_index x := Z.to_nat (x mod p);
}.

Global Instance CanCastToIndex_Index {p} `{Prime p} : CanCastToIndex Index.t := {
  cast_to_index := id;
}.

Global Instance CanCastToIndex_Bool {p} `{Prime p} : CanCastToIndex bool := {
  cast_to_index b := if b then 1%nat else 0%nat;
}.
