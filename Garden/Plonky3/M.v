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
  | Opp : t Z Z
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
  .

  Definition eval (p : Z) {A B C : Set} (op : t A B C) : A -> B -> C :=
    match op in t A B C return A -> B -> C with
    | Add => fun x y => (x + y) mod p
    | Sub => fun x y => (x - y) mod p
    | Mul => fun x y => (x * y) mod p
    | Div => fun x y => (x / y) mod p
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
  .

  (** This is a marker that we remove with the following tactic. *)
  Axiom run : forall {A : Set}, t A -> A.

  (** A tactic that replaces all [run] markers with a bind operation.
    This allows to represent programs without introducing
    explicit names for all intermediate computation results. *)
  Ltac expr e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (Let _ _);
        [ expr x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => expr y
          | _ =>
            refine (Let _ _);
              [ expr y
              | let w := fresh "v" in
                intro w;
                let z := context ctxt [w] in
                expr z
              ]
          end
        ]
    | context ctxt [run ?x] =>
      lazymatch context ctxt [run x] with
      | run x => expr x
      | _ =>
        refine (Let _ _);
          [ expr x
          | let v := fresh "v" in
            intro v;
            let y := context ctxt [v] in
            expr y
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

  Definition equal (x y : Z) : t unit :=
    Equal x y.

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

(** Rules to check if the contraints are what we expect, typically a unique possible value. *)
Module Run.
  Reserved Notation "{{ e 🔽 output , P }}".

  Inductive t : forall {A : Set}, M.t A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ M.Pure value 🔽 value, True }}
  | Equal (x1 x2 : Z) :
    {{ M.Equal x1 x2 🔽 tt, x1 = x2 }}
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

(** Here we see the use of the monadic notations defined above. *)
Definition zero_or_one (x : Z) : M.t unit :=
  let* square_x := ltac:(M.expr (
    M.mul (| x, x |)
  )) in
  M.equal x square_x.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Lemma zero_or_one_correct (p : Z) (x : Z) :
  IsPrime p ->
  {{ M.eval p (zero_or_one x) 🔽 tt, x = 0 \/ x = 1 }}.
Proof.
  intros.
  unfold zero_or_one; cbn.
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
    let* _ := zero_or_one x in
    all_zero_or_one l'
  end.

Lemma all_zero_or_one_correct (p : Z) (l : list Z) :
  IsPrime p ->
  {{ M.eval p (all_zero_or_one l) 🔽 tt, List.Forall (fun x => x = 0 \/ x = 1) l }}.
Proof.
  intros.
  induction l; cbn.
  { eapply Run.Equiv. {
      apply Run.Pure.
    }
    easy.
  }
  { eapply Run.Equiv. {
      eapply Run.Let. {
        now apply zero_or_one_correct.
      }
      apply IHl.
    }
    best.
  }
Qed.

(** One more example to show the use of the monadic notations without naming intermediate results. *)
Definition cube (x : Z) : M.t Z :=
  ltac:(M.expr (
    M.mul (|M.mul (| x, x |), x |)
  )).

Lemma cube_correct (p : Z) (x : Z) :
  IsPrime p ->
  {{ M.eval p (cube x) 🔽 (x * x * x) mod p, True }}.
Proof.
  intros.
  unfold cube; cbn.
  eapply Run.Equiv. {
    eapply Run.Replace. {
      apply Run.Pure.
    }
    (* This property should be handled automatically by some field reasoning tactic. *)
    admit.
  }
  tauto.
Admitted.
