Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
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

Module Array.
  Record t {A : Set} {N : Z} : Set := {
    get : Z -> A;
  }.
  Arguments t : clear implicits.

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {|
      get index := x.(get) (start + index)
    |}.
End Array.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Class Prime (p : Z) : Prop := {
  is_prime : IsPrime p;
}.

Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.
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

(* TODO: 
- integrate the builder into the monad, maybe as a state? 
- write a function to create a sub builder *)
Module Builder.
  (* Parameters
  1. constraints being stored from using `when` (should we even use this?)
  2. assertions being stored from all assert zeros being invoked so far
  *)
  Definition t : Type := (list Prop) * (list Prop).

  Definition add_assert (b : t) (p : Prop) : t :=
    let (c, a) := b in
    (c, (a ++ [p])).
End Builder.

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t {b : Builder.t} : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | AssertZero {A : Set} (x : Z) : t A
  | When {A : Set} (x : Z) : t A
  | EndWhen {A : Set} (x : Z) : t A
  (* | Zeros {N : Z} (array : Array.t Z N) : t unit *)
  (* | ForInZeroToN (N : Z) (f : Z -> t unit) : t unit *)
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call {A : Set} (e : t A) : t A
  | Let {A B : Set} (e : t A) (k : A -> t B) : t B
  | Impossible {A : Set} (message : string) : t A
  .

  (** This is a marker that we remove with the following tactic. *)
  Axiom run : forall {A : Set} {b : Builder.t}, @t b A -> A.

  (** A tactic that replaces all [run] markers with a bind operation.
    This allows to represent programs without introducing
    explicit names for all intermediate computation results. *)

  (* Ltac monadic e :=
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
    end. *)

  Definition pure {A : Set} {b : Builder.t} (x : A) : @t b A :=
    Pure x.

  (* TODO: we might be able to remove this equal function along with its primitives
  Definition equal {b : Builder.t} (x y : Z) : @t b unit :=
    Equal x y.

  Definition zeros {N : Z} {b : Builder.t} (array : Array.t Z N) : @t b unit :=
    Zeros array.

  Definition for_in_zero_to_n {b : Builder.t} (N : Z) (f : Z -> t unit) : @t b unit :=
    ForInZeroToN N f.

  Definition call {A : Set} {b : Builder.t} (e : t A) : @t b A :=
    Call e.

  Definition collapsing_let {A B : Set} {b : Builder.t} (e : t A) (k : A -> t B) : @t b B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end. *)
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

(* Notation "[[ e ]]" :=
  (ltac:(M.monadic e))
  (* Use the version below for debugging and show errors that are made obscure by the tactic *)
  (* (M.Pure e) *)
  (only parsing). *)

(** Rules to check if the contraints are what we expect, typically a unique possible value. *)
Module Run.
  Reserved Notation "{{ e , B1 🔽 output , P , B2 }}".

  Inductive t : forall (builder : Builder.t) {A : Set}, (@M.t builder A) -> A -> (Prop * Builder.t) -> Prop :=
  | Pure {b : Builder.t} {A : Set} (value : A) :
    {{ (M.Pure value), b 🔽 value, True, b }}
  | AssertZero {b : Builder.t} (z : Z) : {{ M.AssertZero z, b 🔽 tt, 
  (* TODO: compute the assert with the `when` constraint *)
    0 = z, Builder.add_assert b (0 = z) }}
  | When {b : Builder.t} (z : Z) : {{ M.When z, b 🔽 tt, True, b }} (* stub *)
  | EndWhen {b : Builder.t} (z : Z) : {{ M.EndWhen z, b 🔽 tt, True, b }} (* stub *)
  (* | Zeros {N : Z} (array : Array.t Z N) :
    {{ M.Zeros array 🔽 tt, forall i, 0 <= i < N -> array.(Array.get) i = 0 }} *)
  (* | ForInZeroToN (N : Z) (f : Z -> M.t unit) (P : Z -> Prop) :
    (forall i, 0 <= i < N ->
      {{ f i 🔽 tt, P i }}
    ) ->
    {{ M.ForInZeroToN N f 🔽 tt, forall i, 0 <= i < N -> P i }} *)

  | Call {b : Builder.t} {A : Set} (e : M.t A) (value : A) (P : Prop) :
    {{ e, b 🔽 value, P, b }} ->
    {{ M.Call e, b 🔽 value, P, b }}
  | Let {b : Builder.t} {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e, b 🔽 value, P1, b }} ->
    {{ k value, b 🔽 output, P2, b }} ->
    {{ M.Let e k, b🔽 output, P1 /\ P2, b }}
  | Implies {b : Builder.t} {A : Set} (e : M.t A) (value : A) (P1 P2 : Prop) :
    {{ e, b 🔽 value, P1, b }} ->
    (P1 -> P2) ->
    {{ e, b 🔽 value, P2, b }}
  | Replace {b : Builder.t} {A : Set} (e : M.t A) (value1 value2 : A) (P : Prop) :
    {{ e, b 🔽 value1, P, b }} ->
    value1 = value2 ->
    {{ e, b 🔽 value2, P, b }}

    where "{{ e , B1 🔽 output , P , B2 }}" := (t B1 e output (P, B2)).

  (* Lemma AssertZerosFromFnSub {p} `{Prime p} (N : Z) (f g : Z -> Z) :
    {{ M.Zeros (N := N) {| Array.get i := BinOp.sub (f i) (g i) |} 🔽
      tt, forall i, 0 <= i < N -> f i = g i
    }}.
  Proof.
  Admitted. *)
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
Definition assert_one (x : Z) : M.t unit :=
  assert_zero (Z.sub 1 x).

(* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_bool {p} `{Prime p} (x : Z) : M.t unit :=
  assert_zero (Z.mul x (Z.sub 1 x)).

(* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
Definition assert_bools {p} `{Prime p} {N : Z} (l : Array.t Z N) : M.t unit :=
  M.zeros (N := N) {|
    Array.get i :=
      let x := l.(Array.get) i in
      BinOp.sub (BinOp.mul x x) x
  |}.

Definition when (condition : bool) (e : M.t unit) : M.t unit :=
  if condition then
    e
  else
    M.pure tt.

Parameter xor : forall {p} `{Prime p}, Z -> Z -> Z.

Parameter xor3 : forall {p} `{Prime p}, Z -> Z -> Z -> Z.

Definition double {p} `{Prime p} (x : Z) : Z :=
  BinOp.mul x 2.

Parameter andn : forall {p} `{Prime p}, Z -> Z -> Z.
