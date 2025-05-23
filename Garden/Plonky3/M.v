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

Module UnOp.
  Inductive t : Set -> Set -> Set :=
  | Opp    : t Z Z
  .

  Definition eval (p : Z) {A B : Set} (op : t A B) : A -> B :=
    match op in t A B return A -> B with
    | Opp => fun x => (-x) mod p
    end.
End UnOp.

Module BinOp.
  Inductive t : Set -> Set -> Set -> Set :=
  | Add : t Z Z Z
  | Sub : t Z Z Z
  | Mul : t Z Z Z
  | Div : t Z Z Z
  | Mod : t Z Z Z
  .

  Definition eval (p : Z) {A B C : Set} (op : t A B C) : A -> B -> C :=
    match op in t A B C return A -> B -> C with
    | Add => fun x y => (x + y) mod p
    | Sub => fun x y => (x - y) mod p
    | Mul => fun x y => (x * y) mod p
    | Div => fun x y => (x / y) mod p
    | Mod => fun x y => (x mod y) mod p
    end.
End BinOp.

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | UnOp {A B : Set} (op : UnOp.t A B) (x : A) : t B
  | BinOp {A B C : Set} (op : BinOp.t A B C) (x1 : A) (x2 : B) : t C
  | Equal (x1 x2 : Z) : t unit
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

  Definition opp (x : Z) : t Z :=
    UnOp UnOp.Opp x.

  Definition add (x y : Z) : t Z :=
    BinOp BinOp.Add x y.

  Definition sub (x y : Z) : t Z :=
    BinOp BinOp.Sub x y.

  Definition mul (x y : Z) : t Z :=
    BinOp BinOp.Mul x y.

  Definition div (x y : Z) : t Z :=
    BinOp BinOp.Div x y.

  Definition mod_ (x y : Z) : t Z :=
    BinOp BinOp.Mod x y.

  Definition equal (x y : Z) : t unit :=
    Equal x y.

  Definition call {A : Set} (e : t A) : t A :=
    Call e.

  Definition collapsing_let {A B : Set} (e : t A) (k : A -> t B) : t B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end.

  (** Evaluate only the primitive operations and keep everything else. *)
  Fixpoint eval (p : Z) {A : Set} (e : t A) : t A :=
    match e in t A return t A with
    | Pure x => Pure x
    | UnOp op x => Pure (UnOp.eval p op x)
    | BinOp op x y => Pure (BinOp.eval p op x y)
    | Equal x y => Equal x y
    | Call e => Call (eval p e)
    | Let e k => collapsing_let (eval p e) (fun x => eval p (k x))
    | Impossible message => Impossible message
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
  | Call {A : Set} (e : M.t A) (value : A) (P : Prop) :
    {{ e 🔽 value, P }} ->
    {{ M.Call e 🔽 value, P }}
  | Let {A B : Set} (e : M.t A) (k : A -> M.t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    {{ k value 🔽 output, P2 }} ->
    {{ M.Let e k 🔽 output, P1 /\ P2 }}
  | Equiv {A : Set} (e : M.t A) (value : A) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 <-> P2) ->
    {{ e 🔽 value, P2 }}
  | Replace {A : Set} (e : M.t A) (value1 value2 : A) (P : Prop) :
    {{ e 🔽 value1, P }} ->
    value1 = value2 ->
    {{ e 🔽 value2, P }}
  where "{{ e 🔽 output , P }}" := (t e output P).
End Run.
Export Run.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Module Examples.
  (** Here we see the use of the monadic notations defined above. *)
  Definition zero_or_one (x : Z) : M.t unit :=
    let* square_x := [[
      M.mul (| x, x |)
    ]] in
    M.equal x square_x.
  Opaque zero_or_one.

  Lemma zero_or_one_correct (p : Z) (x : Z) :
    IsPrime p ->
    {{ M.eval p (zero_or_one x) 🔽 tt, x = 0 \/ x = 1 }}.
  Proof.
    intros.
    with_strategy transparent [zero_or_one] unfold zero_or_one.
    cbn.
    eapply Run.Equiv. {
      apply Run.Equal.
    }
    (* This property should be handled automatically by some field reasoning tactic. *)
    admit.
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

  Lemma all_zero_or_one_correct (p : Z) (l : list Z) :
    IsPrime p ->
    {{ M.eval p (all_zero_or_one l) 🔽 tt, List.Forall (fun x => x = 0 \/ x = 1) l }}.
  Proof.
    intros.
    with_strategy transparent [all_zero_or_one] unfold all_zero_or_one.
    induction l; cbn.
    { eapply Run.Equiv. {
        apply Run.Pure.
      }
      easy.
    }
    { eapply Run.Equiv. {
        eapply Run.Let. {
          apply Run.Call.
          now apply zero_or_one_correct.
        }
        apply IHl.
      }
      sauto lq: on.
    }
  Qed.

  (** One more example to show the use of the monadic notations without naming intermediate results. *)
  Definition cube (x : Z) : M.t Z :=
    [[
      M.mul (|M.mul (| x, x |), x |)
    ]].
  Opaque cube.

  Ltac show_equality_modulo :=
    repeat (
      (
        (
          apply Zplus_eqm ||
          apply Zmult_eqm ||
          apply Zopp_eqm
        );
        unfold eqm
      ) ||
      rewrite Zmod_eqm ||
      reflexivity
    ).

  Lemma cube_correct (p : Z) (x : Z) :
    IsPrime p ->
    {{ M.eval p (cube x) 🔽 (x * x * x) mod p, True }}.
  Proof.
    intros.
    with_strategy transparent [cube] unfold cube.
    cbn.
    eapply Run.Equiv. {
      eapply Run.Replace. {
        apply Run.Pure.
      }
      show_equality_modulo.
    }
    tauto.
  Qed.
End Examples.

(** ** Primitives we also have in the library *)

Module Array.
  Record t {A : Set} {N : Z} : Set := {
    value : list A;
  }.
  Arguments t : clear implicits.

  Module Valid.
    Record t {A : Set} {N : Z} (P : A -> Prop) (x : t A N) : Prop := {
      length : Z.of_nat (List.length x.(value)) = N;
      elements : List.Forall P x.(value);
    }.
  End Valid.

  Definition get {A : Set} {N : Z} (x : t A N) (index : Z) : M.t A :=
    match List.nth_error x.(value) (Z.to_nat index) with
    | Some value => M.Pure value
    | None => M.Impossible "Index out of bounds"
    end.

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {| Array.value := List.skipn (Z.to_nat start) x.(value) |}.

  Definition from_fn {A : Set} {N : Z} (f : Z -> M.t A) : M.t (t A N) :=
    let fix aux (index : nat) : M.t (list A) :=
      match index with
      | O => M.Pure []
      | S index' =>
        let* xs := aux index' in
        let* x := f (Z.of_nat index') in
        M.Pure (x :: xs)
      end in
    let* xs := aux (Z.to_nat N) in
    M.Pure {| Array.value := List.rev xs |}.

  Definition from_fn_pure {A : Set} {N : Z} (f : Z -> A) : t A N :=
    {| Array.value := List.map (fun n => f (Z.of_nat n)) (List.seq 0 (Z.to_nat N)) |}.
End Array.

Module Pair.
  Record t {A B : Set} : Set := {
    x : A;
    xs : B;
  }.
  Arguments t : clear implicits.
End Pair.

Module WithDefault.
  Class C (A : Set) : Set := {
    default : A;
  }.
End WithDefault.

Module ExplicitArray.
  Fixpoint t_aux (A : Set) (length : nat) : Set :=
    match length with
    | O => unit
    | S length' => Pair.t A (t_aux A length')
    end.

  Definition t (A : Set) (length : Z) : Set :=
    t_aux A (Z.to_nat length).

  Fixpoint get_aux {A : Set} `{WithDefault.C A} {length : nat}
      (array : t_aux A length) (index : nat) :
      A :=
    match length, array, index with
    | O, _, _ => WithDefault.default
    | S length', {| Pair.x := x |}, O => x
    | S length', {| Pair.xs := xs |}, S index' => get_aux xs index'
    end.

  Definition get {A : Set} `{WithDefault.C A} {length : Z}
      (array : t A length) (index : Z) :
      A :=
    get_aux array (Z.to_nat index).

  Fixpoint from_fn_aux {A : Set} {length : nat} (f : nat -> A) (index : nat) : t_aux A length :=
    match length return t_aux A length with
    | O => tt
    | S length' =>
      let x := f index in
      let xs := from_fn_aux f (S index) in
      {| Pair.x := x; Pair.xs := xs |}
    end.

  Definition from_fn {A : Set} {length : Z} (f : Z -> A) : t A length :=
    from_fn_aux (fun n => f (Z.of_nat n)) O.

  Fixpoint default_aux {A : Set} `{WithDefault.C A} (length : nat) :
      t_aux A length :=
    match length return t_aux A length with
    | O => tt
    | S length' => {| Pair.x := WithDefault.default; Pair.xs := default_aux length' |}
    end.

  Definition default {A : Set} `{WithDefault.C A} {length : Z} : t A length :=
    default_aux (Z.to_nat length).

  Fixpoint to_array_aux {A : Set} {length : nat} (array : t_aux A length) : list A :=
    match length, array with
    | O, _ => []
    | S length', {| Pair.x := x; Pair.xs := xs |} => x :: to_array_aux xs
    end.

  Definition to_array {A : Set} {length : Z} (array : t A length) : Array.t A length :=
    {| Array.value := to_array_aux array |}.
End ExplicitArray.

Global Instance Impl_WithDefault_for_Z : WithDefault.C Z := {
  default := 0;
}.

Global Instance Impl_WithDefault_for_ExplicitArray (A : Set) `{WithDefault.C A} (length : Z) :
    WithDefault.C (ExplicitArray.t A length) := {
  default := ExplicitArray.default;
}.

(* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_zero (x : Z) : M.t unit :=
  M.equal x 0.

(* fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
Definition assert_zeros {N : Z} (l : Array.t Z N) : M.t unit :=
  let fix aux (l : list Z) : M.t unit :=
    match l with
    | [] => M.Pure tt
    | x :: l' =>
      let* _ := assert_zero x in
      aux l'
    end in
  aux l.(Array.value).

(* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_one (x : Z) : M.t unit :=
  M.equal x 1.

(* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_bool (x : Z) : M.t unit :=
  [[ M.equal (| x, M.mul (| x, x |) |) ]].

(* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
Definition assert_bools {N : Z} (l : Array.t Z N) : M.t unit :=
  let fix aux (l : list Z) : M.t unit :=
    match l with
    | [] => M.Pure tt
    | x :: l' =>
      let* _ := assert_bool x in
      aux l'
    end in
  aux l.(Array.value).

Definition when (condition : bool) (e : M.t unit) : M.t unit :=
  if condition then e else M.Pure tt.

Fixpoint for_in {A : Set} (l : list A) (f : A -> M.t unit) : M.t unit :=
  match l with
  | [] => M.Pure tt
  | x :: l' =>
    let* _ := f x in
    for_in l' f
  end.

Definition for_in_zero_to_n (n : Z) (f : Z -> M.t unit) : M.t unit :=
  for_in (List.map Z.of_nat (List.seq 0 (Z.to_nat n))) f.

Fixpoint fold {Acc Element : Set} (acc : Acc) (l : list Element) (f : Acc -> Element -> M.t Acc) :
    M.t Acc :=
  match l with
  | [] => M.Pure acc
  | x :: l' =>
    let* acc' := f acc x in
    fold acc' l' f
  end.

Definition double (x : Z) : M.t Z :=
  [[ M.mul (| 2, x |) ]].

Parameter xor  : Z -> Z -> M.t Z.
Parameter xor3 : Z -> Z -> Z -> M.t Z.

Definition double (x : Z) : M.t Z :=
  [[ M.mul (| 2, x |) ]].
