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

Module Array.
  Record t {A : Set} {N : Z} : Set := {
    get : Z -> A;
  }.
  Arguments t : clear implicits.

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {|
      get index := x.(get) (start + index)
    |}.

  Definition slice_first {A : Set} {N : Z} (x : t A N) (count : Z) : t A count := 
    {|
      get := x.(get)
    |}.

  Definition get_mod {p} `{Prime p} {N : Z} (x : t Z N) (i : Z) : Z :=
    x.(get) i mod p.

  Definition placeholder {A : Set} {N : Z} (x : A) : t A N :=
    {|
      get index := x
    |}.

  Definition map {A B : Set} {N : Z} (x : t A N) (f : A -> B) : t B N := 
    {|
      get index := f (x.(get) index)
    |}.
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
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | Equal (x1 x2 : Z) : t unit
  | AssertBool (x : Z) : t unit
  | AssertZeros {N : Z} (array : Array.t Z N) : t unit
  | ForInZeroToN (N : Z) (f : Z -> t unit) : t unit
  | SumForInZeroToN (N : Z) (f : Z -> Z) : t Z
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call {A : Set} (e : t A) : t A
  | Let {A B : Set} (e : t A) (k : A -> t B) : t B
  | Impossible {A : Set} (message : string) : t A
  .

  (** This is a marker that we remove with the following tactic. *)
  Axiom run : forall {A : Set}, t A -> A.

  (** A tactic that replaces all [run] markers with a bind operation.
    This allows to represent programs without introducing
    explicit names for all intermediate computation results. *)
  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (Let _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (Let _ _);
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
        refine (Let _ _);
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
      | _ => exact (Pure e)
      end
    end.

  Definition pure {A : Set} (x : A) : t A :=
    Pure x.

  Definition equal (x y : Z) : t unit :=
    Equal x y.

  Definition assert_zeros {N : Z} (array : Array.t Z N) : t unit :=
    AssertZeros array.

  Definition for_in_zero_to_n (N : Z) (f : Z -> t unit) : t unit :=
    ForInZeroToN N f.

  (* helper: acting on all elements in an array *)
  Definition for_each {A : Set} {N : Z} (f : A -> t unit) (x : Array.t A N) : t unit :=
    for_in_zero_to_n N (fun i => f (Array.get x i)).

  (* helper: acting on all elements in an array, but returning a sum *)    

  Fixpoint sum_for_in_zero_to_n_aux {p} `{Prime p} (N : nat) (f : Z -> Z) : Z :=
    match N with
    | O => 0
    | S N => BinOp.add (sum_for_in_zero_to_n_aux N f) (f (Z.of_nat N))
    end.

  Definition sum_for_in_zero_to_n {p} `{Prime p} (N : Z) (f : Z -> Z) : Z :=
    sum_for_in_zero_to_n_aux (Z.to_nat N) f.

  Definition call {A : Set} (e : t A) : t A :=
    Call e.

  Definition collapsing_let {A B : Set} (e : t A) (k : A -> t B) : t B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end.
End M.

Notation "'let*' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Notation "e (| e1 , .. , en |)" :=
  (M.run ((.. (e e1) ..) en))
  (at level 100).

Notation "e (||)" :=
  (M.run e)
  (at level 100).

Notation "[[ e ]]" :=
  (ltac:(M.monadic e))
  (* Use the version below for debugging and show errors that are made obscure by the tactic *)
  (* (M.Pure e) *)
  (only parsing).

(** Rules to check if the contraints are what we expect, typically a unique possible value. *)
Module Run.
  Reserved Notation "{{ e 🔽 output , P }}".

  Inductive t : forall {A : Set}, M.t A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ M.Pure value 🔽 value, True }}
  | Equal (x1 x2 : Z) :
    {{ M.Equal x1 x2 🔽 tt, x1 = x2 }}
  | AssertBool (x : Z) :
    {{ M.AssertBool x 🔽 tt, exists (b : bool), x = Z.b2z b }}
  | AssertZerosFromFnSub {p} `{Prime p} {N : Z} (f g : Z -> Z) :
    {{ M.AssertZeros (N := N) {| Array.get i := BinOp.sub (f i) (g i) |} 🔽
      tt, forall i, 0 <= i < N -> f i = g i
    }}
  | AssertZeros {N : Z} (array : Array.t Z N) :
    {{ M.AssertZeros array 🔽 tt, forall i, 0 <= i < N -> array.(Array.get) i = 0 }}
  | ForInZeroToN (N : Z) (f : Z -> M.t unit) (P : Z -> Prop) :
    (forall i, 0 <= i < N ->
      {{ f i 🔽 tt, P i }}
    ) ->
    {{ M.ForInZeroToN N f 🔽 tt, forall i, 0 <= i < N -> P i }}
  | Call {A : Set} (e : M.t A) (value : A) (P : Prop) :
    {{ e 🔽 value, P }} ->
    {{ M.Call e 🔽 value, P }}
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
End Run.
Export Run.

(** ** Primitives we also have in the library *)

Module Pair.
  Record t {A B : Set} : Set := {
    x : A;
    xs : B;
  }.
  Arguments t : clear implicits.
End Pair.

(* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_zero (x : Z) : M.t unit :=
  M.equal x 0.

(* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_one {p} `{Prime p} (x : Z) : M.t unit :=
  M.equal x (1 mod p).

(* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_bool {p} `{Prime p} (x : Z) : M.t unit :=
  M.AssertBool x.

(* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
Definition assert_bools {p} `{Prime p} {N : Z} (l : Array.t Z N) : M.t unit :=
  M.for_in_zero_to_n N (fun i =>
    M.assert_bool (l.(Array.get) i)
  ).

Definition when (condition : Z) (e : M.t unit) : M.t unit :=
  if condition =? 0 then
    M.pure tt
  else
    e.

Definition when_bool (condition : bool) (e : M.t unit) : M.t unit :=
  if condition then
    e
  else
    M.pure tt.

Definition not {p} `{Prime p} (x : Z) : Z :=
  BinOp.sub 1 x.

Parameter xor : forall {p} `{Prime p}, Z -> Z -> Z.

Parameter xor3 : forall {p} `{Prime p}, Z -> Z -> Z -> Z.

Definition double {p} `{Prime p} (x : Z) : Z :=
  BinOp.mul x 2.

Parameter andn : forall {p} `{Prime p}, Z -> Z -> Z.

Module List.
  Fixpoint fold_left {A B : Set} (f : A -> B -> M.t A) (acc : A) (l : list B) : M.t A :=
    match l with
    | nil => M.pure acc
    | cons x xs =>
      let* acc := f acc x in
      fold_left f acc xs
    end.

  Fixpoint fold_right {A B : Set} (f : B -> A -> M.t A) (l : list B) (acc : A) : M.t A :=
    match l with
    | nil => M.pure acc
    | cons x xs =>
      let* acc := fold_right f xs acc in
      f x acc
    end.
End List.

Class MapMod {p : Z} `{Prime p} (A : Set) : Set := {
  map_mod : A -> A;
}.

Global Instance MapMod_Felt {p} `{Prime p} : MapMod Z := {
  map_mod := UnOp.from;
}.

Global Instance IsMapMod_Array {p} `{Prime p} (A : Set) (N : Z) `{MapMod p A} :
    MapMod (Array.t A N) :=
{
  map_mod x := Array.map x map_mod;
}.

Module Limbs.
  Definition of_bools {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (a : Array.t Z (NB_LIMBS * BITS_PER_LIMB)) :
      Array.t Z NB_LIMBS :=
    {|
      Array.get limb :=
        let l : list nat :=
          List.rev (
            List.seq
              (Z.to_nat (limb * BITS_PER_LIMB))%Z
              (Z.to_nat (limb * BITS_PER_LIMB + BITS_PER_LIMB))%Z
          ) in
        Lists.List.fold_left (fun acc (z : nat) =>
          let z : Z := Z.of_nat z in
          BinOp.add (BinOp.mul 2 acc) (a.(Array.get) z)
        ) l 0
    |}.
End Limbs.
