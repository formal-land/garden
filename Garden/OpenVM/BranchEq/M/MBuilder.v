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

Require Import Eqdep. (* ??? *)
Require Import Coq.Program.Equality.

Export List.ListNotations.

(* NOTE: Currently there are 2 major issues in the monad.
1. I have attempted to define a notation for `when`, and it didn't work out well. 
  Search `the keyword `when` and see related parts.
2. Since the monad involves `forall` in its type, it turns out that Coq will have
  some difficulty to perform `inversion` on the types. Currently the only problem is,
  I have changed the type of monad from `Set` to `Type` 
*)
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

Module Builder.
  (* NOTE: Here we use record for easier access. Parameters
  1. when_context being stored from using `when`
  2. assertions as a proposition of all assert zeros being invoked so far.
     Whenever a new assertions is being added, it is supposed to be appended by
     all constraints stored in `when_context` before appending to the tail of 
     `assertions`
  *)
  Record t : Type := 
  {
    when_context : list Z;
    assertions : list Z;
  }.
End Builder.

Definition pop_list (l : list Z) : list Z :=
  match l with
  | _ :: l => l
  | [] => []
  end.

Definition add_assert (x : Z) (b : Builder.t)
  : Builder.t :=
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
  andb (Z.eqb 1 (compute_context b)) (Z.eqb x 0%Z).

Module M.
  (* NOTE: eventually monad is a `Type` or otherwise `discriminate` will not work.
  Is there a better way to handle this? *)
  Inductive t : Set -> Type :=
  | Pure {A : Set} (value : A) : t A
  | AssertZero {A : Set} (x : Z) : t A
  | When {A : Set} (x : Z) : t A
  | EndWhen : t unit
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call {A : Set} (e : t A) : t A
  | Let {A B : Set} (e : t A) (k : A -> t B) : t B
  | Impossible {A : Set} (message : string) : t A
  .

  (* NOTE: test on inversion on constructors *)
  Lemma pure_assert_zero_neq :
    forall value x, @M.Pure unit value = @M.AssertZero unit x -> False.
  Proof.
    intros value x H.
    inversion H.
  Qed.

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
  Definition equal (x y : Z) : @t b unit :=
    Equal x y.

  Definition zeros {N : Z} (array : Array.t Z N) : @t b unit :=
    Zeros array.

  Definition for_in_zero_to_n (N : Z) (f : Z -> t unit) : @t b unit :=
    ForInZeroToN N f.
  *)
  Definition mul {p} `{Prime p} (x y : Z) : t Z :=
    pure (BinOp.mul x y).
End M.

Notation "'let*B' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

(* NOTE: BROKEN. Don't know why it doesn't work out *)
Notation "'when*' A x k1 'in' k2" := (
  let*B _ := @M.When A x in 
  let*B _ := k1 in
  let*B _ := M.EndWhen in
  k2
) (at level 200, format "'when*' A x k1 'in' k2").

Notation "e (| e1 , .. , en |)" :=
  (M.run ((.. (e e1) ..) en))
  (at level 100).

Notation "e (||)*" :=
  (M.run e)
  (at level 100).

Notation "[[ e ]]*" :=
  (ltac:(M.monadic e))
  (* Use the version below for debugging and show errors that are made obscure by the tactic *)
  (* (M.Pure e) *)
  (only parsing).


(* NOTE: unfinished draft *)
Ltac m_3_trace e :=
  match e with
  (* | context ctxt [M.Pure ?x] =>
    let x := context ctxt [M.Pure "OUT_OF_CONTEXT"] in
    constr:(("match M.Pure", x)) *)
  | context ctxt [let v := ?x in @?f v] =>
    refine (M.Let _ _);
    let x := context ctxt [M.Pure "OUT_OF_CONTEXT"] in
    constr:(("match let context", x))
  | context ctxt [M.run ?x] =>
    let x := context ctxt [M.Pure "OUT_OF_CONTEXT"] in
    constr:(("match run context", x))
  | _ => 
    constr:(("match default", e))
  end. 

(* Definition test_term := let y := Nat.add 1%nat 1%nat in Nat.mul y y. *)
Definition test_term := let x := 1 in M.Pure x.

(* Goal let x := 1 + 1 in True. *)
(* refine (M.Let _ _). *)

(* Goal True.
  let x := eval cbv delta in test_term in
  (* pose x as x. *)
  let t := m_3_trace x in
  pose t as extracted_ctxt.
  pose (let* _ := [[ (3 * 3) ]] in M.Pure tt) as xxx.
  [pose constr:(M.monadic xxx) 1 as sss | idtac "1"].
  exact I.
Qed. *)

(* Definition testtest : True.
Proof.
  pose test2 as t2. 
  let x := m_3_trace t2 in pose x as t3_trace.
Admitted.

Print test2.

Compute (ltac:(M.monadic (1 + 1))). *)

(* Definition test := [[ 
    let* x := [[ 1 + 1 ]] in
    [[ x ]]
]].
Print test. Compute test. *)

(* NOTE: tests for `when` notation *)
(* Definition test1 : M.t unit := M.Pure tt.
Definition test2 : M.t unit := M.EndWhen.
Definition test3 := 
  let* _ := @M.When unit 0%Z in 
  let* _ := M.Pure tt in
  let* _ := M.EndWhen in
  M.Pure tt.
Print test3.
Definition test4 := when* unit 1%Z ( M.Pure tt ) in (M.Pure tt). *)

(* A smaller example than monad to tackle around and prepare to prove 
  properties on the monad 
  From which some ideas on developing the proofs are also being written 
  down
*)
Module TestSection.
  Inductive test_primitives :=
  | TEq0 (_ : Z)
  | TWhen (_ : Z)
  | TEndWhen
  .

  (* NOTE: ideas:
  - necessary universal parameters should be collected at lhs of colon so 
    that they're accessible to constructors of inductive types
  - types at rhs of the colon are supposed to be tags for the type being 
    presented altogether as a proposition
  - rhs tags can depend only from lhs parameters
  - parameters under the constructors are supposed to be as few and necessary
    as possible
  - reason for above: if we put same parameters under constructors plus rhs
    we will have a problem unifying these copies
    for rhs and constructors sharing the same copy we should put what they 
    share in the left
  - when designing the propositions, take it carefully for the tags to hold
    necessary informations without being computed, for example an extra 
    uncalculated builder. this helps the prover to set up less necessary
    equations to reason between unlinked variables
  - TODO: write more clearly what are necessary informations and when will 
    we need them
  - TODO: figure out more clearly when will Coq prove false
  *)
  Reserved Notation "{{{ e , b | L }}}".
  Inductive test_design_proposition (b : Builder.t) : 
    test_primitives -> Builder.t -> Prop :=
  | PEq (x : Z) : 
    {{{ TEq0 x, b | 
      if (compute_assert x b) 
      then add_assert 1 b
      else add_assert 0 b }}}
  where "{{{ e , b | L }}}" := (test_design_proposition b e L).

  Theorem eqx0_to_eq0 : forall (b : Builder.t) (x : Z),
    compute_context b = 1 ->
    x = 0 ->
    {{{ TEq0 x, b | 
    add_assert 1 b
    }}}.
  Proof.
    intros b x valid eqx.
    pose (PEq b x) as PEq0.
    unfold compute_assert in PEq0.
    rewrite -> valid in PEq0.
    rewrite -> eqx in PEq0.
    simpl in PEq0.
    rewrite <- eqx in PEq0.
    exact PEq0.
  Qed.
  
  (* NOTE: 
  When designing this theorem, one previous attempt is stating the
  proposition like this:
  {{{ TEq0 0, b | add_assert 1 b }}}
  and we can see that 0 is not dependent on x
  the experience we get here is that we want to carry as much information(?)
  as possible in the type, and know that x doesn't automatically change into
  0 without an equation 
  *)
  Theorem eq0_to_eqx0 : forall (b : Builder.t) (x : Z),
    compute_context b = 1 ->
    {{{ TEq0 x, b | add_assert 1 b }}} ->
    x = 0.
  Proof.
    intros b x valid e.
    inversion e.
    simpl in H.
    symmetry in valid.
    unfold compute_assert in H.
    rewrite <- valid in H.
    simpl in H.
    destruct (x =? 0) eqn:Eqx0 in H.
    - apply Z.eqb_eq in Eqx0. exact Eqx0.
    - inversion H.
  Qed.
End TestSection.

Module Run.
  Reserved Notation "{{ e | b1 🔽 output | b2 }}*".
  Inductive t (b : Builder.t) : 
    forall {A : Set}, M.t A -> A -> Builder.t -> Prop :=
  | Pure {A : Set} (value : A) : {{ M.Pure value | b 🔽 value | b }}*
  | AssertZero (x : Z) : 
    {{ M.AssertZero x | b 🔽 tt | 
      if (compute_assert x b) then add_assert 1 b else add_assert 0 b }}*
  | When (x : Z) : {{ M.When x | b 🔽 tt | push_context x b }}*
  | EndWhen : {{ M.EndWhen | b 🔽 tt | pop_context b }}*
  | Call {A : Set} (e : M.t A) (value : A) :
    {{ e | b 🔽 value | b }}* ->
    {{ M.Call e | b 🔽 value | b }}*
  | Let {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) :
    {{ e | b 🔽 value | b }}* ->
    {{ k value | b 🔽 output | b }}* ->
    {{ M.Let e k | b 🔽 output | b }}*
  | Replace {A : Set} (e : M.t A) (value1 value2 : A) :
    {{ e | b 🔽 value1 | b }}* ->
    value1 = value2 ->
    {{ e | b 🔽 value2 | b }}*
    where "{{ e | b1 🔽 output | b2 }}*" := (t b1 e output b2).
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
  M.AssertZero x.

(* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_one (x : Z) : M.t unit :=
  assert_zero (Z.sub 1 x).

(* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_bool (x : Z) : M.t unit :=
  assert_zero (Z.mul x (Z.sub 1 x)).

(* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)

Definition when (condition : Z) : M.t unit :=
  @M.When unit condition.

Definition end_when : (M.t unit) := M.EndWhen.

Parameter xor : forall {p} `{Prime p}, Z -> Z -> Z.

Parameter xor3 : forall {p} `{Prime p}, Z -> Z -> Z -> Z.

Definition double {p} `{Prime p} (x : Z) : Z :=
  BinOp.mul x 2.

Definition andn {p} `{Prime p} (x1 x2 : Z) : Z :=
  BinOp.sub 1 (BinOp.mul x1 x2).

Module Theorems.
  Example zero_or_one (x : Z) : M.t unit := assert_bool x.
  
  Example zero_or_absolute_one {p} `{Prime p} (x : Z) : M.t unit :=
    let*B square_x := [[ BinOp.mul x x ]]* in
    assert_bool square_x.
  Opaque zero_or_absolute_one.

  Theorem eq_builder_assertions : forall (b1 b2 : Builder.t),
    b1 = b2 -> b1.(Builder.assertions) = b2.(Builder.assertions).
  Proof. intros. subst. reflexivity. Qed.

  Theorem neq_list_append : forall (x : Z) (l : list Z), l <> x :: l.
  Proof.
    intros x l H.
    induction l as [| h t IH].
    - simpl in H.
      discriminate H.
    - simpl in H.
      inversion H.
      apply IH in H2.
      contradiction.
  Qed.

  Lemma eq_to_assert_zero : forall (x : Z) (b : Builder.t), 
    compute_context b = 1 ->
    x = 0 -> {{ M.AssertZero x | b 🔽 tt | add_assert 1 b }}*.
  Proof.
    intros x b valid eqx.
    pose (AssertZero b x) as AEqx.
    unfold compute_assert in AEqx.
    symmetry in valid. rewrite <- valid in AEqx.
    rewrite -> eqx in AEqx.
    rewrite -> eqx.
    exact AEqx.
  Qed.

  Lemma assert_zero_to_eq : forall (x : Z) (b : Builder.t), 
    compute_context b = 1 ->
    {{ M.AssertZero x | b 🔽 tt | add_assert 1 b }}* -> x = 0.
  Proof.
    intros x b valid run.
    symmetry in valid.
    inversion run. (* We only generate 2 of 7 cases *)
    (* Can we ensure the construct `add_assert 1 b` from original primitive 
      with arbitary x? *)
    - unfold compute_assert in H0.
      rewrite <- valid in H0.
      destruct (x =? 0) eqn:Eqx0 in H.
      (* For arbitary x, is (x = 0) = true or false? *)
      + apply Z.eqb_eq in Eqx0. exact Eqx0. (* If true, we can get exactly a proof of x=0 *)
      + rewrite -> Eqx0 in H0. inversion H0. (* Otherwise, we can get a proof of exfalso *)
    (* Could it be that we're generating the proposition from `Replace` primitive? *)
    - apply eq_builder_assertions in H4.
      apply neq_list_append in H4. 
      contradiction.
  Qed.
End Theorems.