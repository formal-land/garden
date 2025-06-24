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

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t {b : Builder.t} : Set -> Set :=
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
  Axiom run : forall {A : Set} {b : Builder.t}, @t b A -> A.

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

  Definition call {b : Builder.t} {A : Set} (e : t A) : @t b A :=
    Call e.

  Definition collapsing_let {b : Builder.t} {A B : Set} (e : t A) (k : A -> t B) : @t b B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end.

  Definition pure {b : Builder.t} {A : Set} (x : A) : @t b A :=
    Pure x.

  (* TODO: we might be able to remove this equal function along with its primitives
  Definition equal {b : Builder.t} (x y : Z) : @t b unit :=
    Equal x y.

  Definition zeros {N : Z} {b : Builder.t} (array : Array.t Z N) : @t b unit :=
    Zeros array.

  Definition for_in_zero_to_n {b : Builder.t} (N : Z) (f : Z -> t unit) : @t b unit :=
    ForInZeroToN N f.
  *)
  Definition mul {b : Builder.t} {p} `{Prime p} (x y : Z) : @t b Z :=
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
  (* UNUSED. Maybe just a marker. Parameters:
  - The builder instance
  - The proposition to assert 
  *)
  Parameter P_Assert : Builder.t -> Prop -> Prop. 
  (* UNUSED. Maybe just a marker. Parameters:
  - The builder instance
  - The proposition to add into conatraint?
  *)
  Parameter P_When : Builder.t -> Prop -> Prop.

  Reserved Notation "{{ e | B 🔽 output | P_B }}".

  Inductive test_primitives :=
  | Eq0 (_ : Z)
  | P2
  .

  Reserved Notation "{{{ e | L }}}".

  (* TODO: 
  - add a more complicated computation to similar `when`
  *)
  Inductive test_design_proposition : 
    test_primitives -> list Z -> Prop :=
  | PEq (l : list Z) (x : Z) : 
    {{{ Eq0 x | 
      if Z.eqb x 0%Z then 1 :: l else 0 :: l }}}

  where "{{{ e | L }}}" := (test_design_proposition e L).

  Compute (PEq [] 0%Z).

  Compute (PEq [0] 0%Z).

  Theorem test_item (l : list Z):
  {{{ Eq0 0%Z | 1 :: l }}}.
  Proof.
    apply (PEq l).
  Qed.

(* 
(* 
Inductive t `{Heap.Trait} {A B : Set}
      (stack : Stack.t) (heap : Heap)
      (to_value : A -> B) (P_stack : Stack.t -> Prop) (P_heap : Heap -> Prop) :
      LowM.t B -> Set :=
  | Pure
    (result : A)
    (result' : B) :
    result' = to_value result ->
    P_stack stack ->
    P_heap heap ->
    {{ stack, heap |
      LowM.Pure result' ⇓
      to_value
    | P_stack, P_heap }}
*)

Definition run_pop (stack : Stack.t) (heap : Heap.t) :
  {{ stack, heap |
    stack.pop (make_list [Evm.stack_to_value]) (make_dict []) ⇓
    (fun (result : unit + builtins.Exception.t) =>
      match result with
      | inl tt => inl Constant.None_
      | inr exn => inr (Exception.Raise (Some (builtins.Exception.to_value exn)))
      end)
  |
    fun stack' => exists fresh_stack, stack' = stack ++ fresh_stack,
    fun heap' => True
  }}.
*)

(* 
P_Builder for AssertZero : 
fun builder' => 
  (* TODO: perform calculations on constraints....? or find a better way to design it? *)
  if eqb x 0 then
    builder' = 1 :: builder
    else
    builder' = 0 :: builder 
  *)
  Inductive t (builder : Builder.t) (P_Builder : Builder.t -> Prop) : forall {A : Set}, 
    (@M.t builder A) -> A -> Prop :=
  | Pure {A : Set} (value : A) :
    (* TODO: define separate notations in the future to enforce P_Builder *)
    P_Builder builder ->
    {{ M.Pure value | builder 🔽 value | P_Builder }} (* Usually: fun b => builder = b *)
  | AssertZero (z : Z) : {{ M.AssertZero z | builder 🔽 tt | P_Builder }}
  | When (z : Z) : {{ M.When z | builder 🔽 tt | P_Builder }}
  | EndWhen : {{ M.EndWhen | builder 🔽 tt | P_Builder }}
  | Call {A : Set} (e : M.t A) (value : A) :
    {{ e | builder 🔽 value | P_Builder }} ->
    {{ M.Call e | builder 🔽 value | P_Builder }}
  | Let {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) :
    {{ e | builder 🔽 value| P_Builder }} ->
    {{ k value | builder 🔽 output| P_Builder }} ->
    {{ M.Let e k | builder 🔽 output| P_Builder }}
  (* NOTE: since we should do the computations asap, we might be able to remove this? *)
  | Replace {A : Set} (e : M.t A) (value1 value2 : A) :
    (* Note: the P_Builder here looks unsatisfying *)
    {{ e | builder 🔽 value1 | P_Builder }} ->
    value1 = value2 ->
    {{ e | builder 🔽 value2 | P_Builder }}
  where "{{ e | builder 🔽 output | P_Builder }}" := (t builder P_Builder e output).
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