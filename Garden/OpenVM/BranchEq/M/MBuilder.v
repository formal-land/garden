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

(* NOTE: 
- The monad currently designed is unfinished.
- Proposition as an output has been removed
- Instead, we save necessary information inside a state machine being called builder
- I don't know yet how should I update the builder with the `Run`
*)
Module Builder.
  (* Here we use record for easier access *)
  Record t : Type := 
  {
  (* Parameters
  1. when_context being stored from using `when`
  2. assertions as a proposition of all assert zeros being invoked so far.
     Whenever a new assertions is being added, it is supposed to be appended by
     all constraints stored in `when_context` before appending to the tail of 
     `assertions`
  *)
    when_context : list Z;
    assertions : list Z;
  }.
End Builder.

Definition pop_list (l : list Z) : list Z :=
  match l with
  | _ :: l => l
  | [] => []
  end.

Definition add_assert (x : Z) (b : Builder.t) : Builder.t :=
  {|
    Builder.when_context := b.(Builder.when_context);
    Builder.assertions := x :: b.(Builder.assertions);
  |}.

Definition push_context (x : Z) (b : Builder.t) : Builder.t :=
  {|
    Builder.when_context := x :: b.(Builder.when_context);
    Builder.assertions := b.(Builder.assertions);
  |}.

Definition pop_context (b : Builder.t) : Builder.t :=
  {|
    Builder.when_context := pop_list b.(Builder.when_context);
    Builder.assertions := b.(Builder.assertions);
  |}.

Fixpoint all_ones_or_empty (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => if Z.eqb x 1 then all_ones_or_empty xs else 0
  end.

Definition compute_context (b : Builder.t) : Z := 
  let '(Builder.Build_t c _) := b in all_ones_or_empty c.

Definition compute_assert (x : Z) (b : Builder.t) : bool :=
  if Z.eqb 1 (compute_context b) then (Z.eqb x 0%Z) else false.

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | AssertZero {A : Set} (x : Z) : t A
  | When {A : Set} (x : Z) : t A
  | EndWhen {A : Set} : t A
  (* | Zeros {N : Z} (array : Array.t Z N) : t unit *)
  (* | ForInZeroToN (N : Z) (f : Z -> t unit) : t unit *)
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

  Definition call {A : Set} (e : t A) : t A :=
    Call e.

  Definition collapsing_let {A B : Set} (e : t A) (k : A -> t B) : t B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end.

  Definition pure {A : Set} (x : A) : t A :=
    Pure x.

  (* TODO: we might be able to remove this equal function along with its primitives
  Definition equal {b : Builder.t} (x y : Z) : @t b unit :=
    Equal x y.

  Definition zeros {N : Z} {b : Builder.t} (array : Array.t Z N) : @t b unit :=
    Zeros array.

  Definition for_in_zero_to_n {b : Builder.t} (N : Z) (f : Z -> t unit) : @t b unit :=
    ForInZeroToN N f.
  *)
  Definition mul {p} `{Prime p} (x y : Z) : t Z :=
    pure (BinOp.mul x y).
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

(* NOTE: Ideas I'm thinking of
Issue with builder: 
- assertions are supposed to be calculated as quick as possible, while
when_context is a lazy-style stack
- We are not supposed to perform calculations in propositions so we would better leave the 
  computation somewhere(where?) else

Example predicates(?), for `P_Builder` below:
- fun builder' => builder'.(when_context) = c :: builder.(when_context)
- let a := (compute_with_when c (eqb 0%z a)) in 
    fun builder' => builder'.(assertions) = builder.(assertions) /\ a
*)
Module Run.
  (* TEST SECTION BELOW *)
  Inductive test_primitives :=
  | TEq0 (_ : Z)
  | TWhen (_ : Z)
  | TEndWhen
  .
  
  Reserved Notation "{{{ e | L }}}".
  Inductive test_design_proposition : 
  (* monad instance -> builder instance -> prop *)
    test_primitives -> Builder.t -> Prop :=
  | PEq (b : Builder.t) (x : Z) : 
    {{{ TEq0 x | if (compute_assert x b) then add_assert 1 b else add_assert 0 b }}}
  where "{{{ e | L }}}" := (test_design_proposition e L).

  Definition default_builder : Builder.t := Builder.Build_t [] [].

  Compute (PEq default_builder 0%Z).
  Compute (PEq (add_assert 1 default_builder) 0%Z).

  Theorem eq0_appends_1 : forall (b : Builder.t),
    compute_context b = 1 ->
    {{{ TEq0 0%Z | add_assert 1 b }}}.
  Proof.
    intros b valid.
    (* NOTE: is there a better way to perform the proof than posing 
    this statement during the proof? *)
    pose (PEq b 0) as PEq0.
    unfold compute_assert in PEq0.
    rewrite -> valid in PEq0.
    exact PEq0.
  Qed.

  Theorem eq1_appends_0 : forall (b : Builder.t),
    compute_context b = 1 ->
    {{{ TEq0 1%Z | add_assert 0 b }}}.
  Proof.
    intros b valid.
    pose (PEq b 1) as PEq1.
    unfold compute_assert in PEq1.
    rewrite -> valid in PEq1.
    exact PEq1.
  Qed.
  (* TEST SECTION END *)

  Reserved Notation "{{ e 🔽 output | B }}".
  
  Inductive t : forall {A : Set}, M.t A -> A -> Builder.t -> Prop :=
  | Pure (b : Builder.t) {A : Set} (value : A): {{ M.Pure value 🔽 value | b }}
  | AssertZero (b : Builder.t) (x : Z) : 
    {{ M.AssertZero x 🔽 tt | 
      if (compute_assert x b) then add_assert 1 b else add_assert 0 b }}
  | When (b : Builder.t) (x : Z)  : {{ M.When x 🔽 tt | push_context x b }}
  | EndWhen (b : Builder.t) : {{ M.EndWhen 🔽 tt | pop_context b }}
  | Call (b : Builder.t) {A : Set} (e : M.t A) (value : A) :
    {{ e 🔽 value | b }} ->
    {{ M.Call e 🔽 value | b }}
  | Let (b : Builder.t) {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) :
    {{ e 🔽 value | b }} ->
    {{ k value 🔽 output | b }} ->
    {{ M.Let e k 🔽 output | b }}
  | Replace (b : Builder.t) {A : Set} (e : M.t A) (value1 value2 : A) :
    {{ e 🔽 value1 | b }} ->
    value1 = value2 ->
    {{ e 🔽 value2 | b }}

  where "{{ e 🔽 output | B }}" := (t e output B).
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
Definition assert_zero {b : Builder.t} (x : Z) : @M.t b unit :=
  M.AssertZero x.

(* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_one {b : Builder.t} (x : Z) : @M.t b unit :=
  assert_zero (Z.sub 1 x).

(* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_bool {b : Builder.t} (x : Z) : @M.t b unit :=
  assert_zero (Z.mul x (Z.sub 1 x)).

(* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
(* Definition assert_bools {p} `{Prime p} {N : Z} (l : Array.t Z N) : M.t unit :=
  M.zeros (N := N) {|
    Array.get i :=
      let x := l.(Array.get) i in
      BinOp.sub (BinOp.mul x x) x
  |}. *)

(* Definition when (condition : bool) (e : M.t unit) : M.t unit :=
  if condition then
    e
  else
    M.pure tt. *)

Parameter xor : forall {p} `{Prime p}, Z -> Z -> Z.

Parameter xor3 : forall {p} `{Prime p}, Z -> Z -> Z -> Z.

Definition double {p} `{Prime p} (x : Z) : Z :=
  BinOp.mul x 2.

Parameter andn : forall {p} `{Prime p}, Z -> Z -> Z.

(* TODO: use some examples to test our notations... *)
Module Examples.

  Definition zero_or_one {b : Builder.t} (x : Z) : @M.t b unit := 
    assert_bool x.
  
  (* NOTE: is there a way to make the implicit builder much more convenient? *)
  Definition zero_or_absolute_one {b : Builder.t} {p} `{Prime p} (x : Z) : @M.t b unit :=
    let* square_x := [[ BinOp.mul x x ]] in
    assert_bool square_x.
  Opaque zero_or_one.

  Lemma assert_zero_correct {builder : Builder.t} :
  {{ (M.AssertZero 0%Z) 
  | 
  builder 
  🔽 
  tt 
  | 
  (fun b : Builder.t => builder.(Builder.assertions) = 0 :: b.(Builder.assertions)) }}.
  
  

  Lemma zero_abs_one_correct {b : Builder.t} {p} `{Prime p} (x : Z) :
  {{ zero_or_one x 🔽 tt
    (fun builder' => 1 :: builder'.(assertions) = b.(assertions) ) }} -> 
  (x = 0 \/ x = 1).
  Proof.
  Admitted.

  (** A function with an arbitrary number of constraints. *)
  Fixpoint all_zero_or_one (l : list Z) : M.t unit :=
    match l with
    | [] => M.Pure tt
    | x :: l' =>
      let* _ := M.call (zero_or_one x) in
      all_zero_or_one l'
    end.
  Opaque all_zero_or_one.
End Examples.