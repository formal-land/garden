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
  Inductive t (F : Set) : Set -> Set -> Set :=
  | Opp : t F F F
  .
  Arguments Opp {_}.

  Definition eval (p : Z) {A B : Set} (op : t Z A B) : A -> B :=
    match op in t _ A B return A -> B with
    | Opp => fun x => (-x) mod p
    end.
End UnOp.

Module BinOp.
  Inductive t (F : Set) : Set -> Set -> Set -> Set :=
  | Add : t F F F F
  | Sub : t F F F F
  | Mul : t F F F F
  | Div : t F F F F
  .
  Arguments Add {_}.
  Arguments Sub {_}.
  Arguments Mul {_}.
  Arguments Div {_}.

  Definition eval (p : Z) {A B C : Set} (op : t Z A B C) : A -> B -> C :=
    match op in t _ A B C return A -> B -> C with
    | Add => fun x y => (x + y) mod p
    | Sub => fun x y => (x - y) mod p
    | Mul => fun x y => (x * y) mod p
    | Div => fun x y => (x / y) mod p
    end.
End BinOp.

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t (F : Set) : Set -> Set :=
  | Pure {A : Set} (value : A) : t F A
  | UnOp {A B : Set} (op : UnOp.t F A B) (x : A) : t F B
  | BinOp {A B C : Set} (op : BinOp.t F A B C) (x1 : A) (x2 : B) : t F C
  | Equal (x1 x2 : F) : t F unit
  | Let {A B : Set} (e : t F A) (k : A -> t F B) : t F B
  .
  Arguments Pure {_ _}.
  Arguments UnOp {_ _ _}.
  Arguments BinOp {_ _ _ _}.
  Arguments Equal {_}.
  Arguments Let {_ _ _}.

  (** This is a marker that we remove with the following tactic. *)
  Axiom run : forall {F A : Set}, t F A -> A.

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
      | t _ _ => exact e
      | _ => exact (Pure e)
      end
    end.

  Definition opp {F : Set} (x : F) : t F F :=
    UnOp UnOp.Opp x.

  Definition add {F : Set} (x y : F) : t F F :=
    BinOp BinOp.Add x y.

  Definition sub {F : Set} (x y : F) : t F F :=
    BinOp BinOp.Sub x y.

  Definition mul {F : Set} (x y : F) : t F F :=
    BinOp BinOp.Mul x y.

  Definition div {F : Set} (x y : F) : t F F :=
    BinOp BinOp.Div x y.

  Definition equal {F : Set} (x y : F) : t F unit :=
    Equal x y.
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
  Reserved Notation "{{ p , e 🔽 output , P }}".

  Inductive t (p : Z) : forall {A : Set}, M.t Z A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ p, M.Pure value 🔽 value, True }}
  | UnOp {A B : Set} (op : UnOp.t Z A B) (x : A) :
    {{ p, M.UnOp op x 🔽 UnOp.eval p op x, True }}
  | BinOp {A B C : Set} (op : BinOp.t Z A B C) (x1 : A) (x2 : B) :
    {{ p, M.BinOp op x1 x2 🔽 BinOp.eval p op x1 x2, True }}
  | Equal (x1 x2 : Z) :
    {{ p, M.Equal x1 x2 🔽 tt, x1 = x2 }}
  | Let {A B : Set} (e : M.t Z A) (k : A -> M.t Z B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ p, e 🔽 value, P1 }} ->
    {{ p, k value 🔽 output, P2 }} ->
    {{ p, M.Let e k 🔽 output, P1 /\ P2 }}
  | Equiv {A : Set} (e : M.t Z A) (value : A) (P1 P2 : Prop) :
    {{ p, e 🔽 value, P1 }} ->
    (P1 <-> P2) ->
    {{ p, e 🔽 value, P2 }}
  | Replace {A : Set} (e : M.t Z A) (value1 value2 : A) (P : Prop) :
    {{ p, e 🔽 value1, P }} ->
    value1 = value2 ->
    {{ p, e 🔽 value2, P }}
  where "{{ p , e 🔽 output , P }}" := (t p e output P).
End Run.
Export Run.

(** Here we see the use of the monadic notations defined above. *)
Definition zero_or_one {F : Set} (x : F) : M.t F unit :=
  let* square_x := ltac:(M.expr (
    M.mul (| x, x |)
  )) in
  M.equal x square_x.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Lemma zero_or_one_correct (p : Z) (x : Z) :
  IsPrime p ->
  {{ p, zero_or_one x 🔽 tt, x = 0 \/ x = 1 }}.
Proof.
  intros.
  unfold zero_or_one.
  eapply Run.Equiv. {
    eapply Run.Let. {
      apply Run.BinOp.
    }
    apply Run.Equal.
  }
  cbn.
  (* This property should be handled automatically by some field reasoning tactic. *)
  admit.
Admitted.

(** A function with an arbitrary number of constraints. *)
Fixpoint all_zero_or_one {F : Set} (l : list F) : M.t F unit :=
  match l with
  | [] => M.Pure tt
  | x :: l' =>
    let* _ := zero_or_one x in
    all_zero_or_one l'
  end.

Lemma all_zero_or_one_correct (p : Z) (l : list Z) :
  IsPrime p ->
  {{ p, all_zero_or_one l 🔽 tt, List.Forall (fun x => x = 0 \/ x = 1) l }}.
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
Definition cube {F : Set} (x : F) : M.t F F :=
  ltac:(M.expr (
    M.mul (|M.mul (| x, x |), x |)
  )).

Lemma cube_correct (p : Z) (x : Z) :
  IsPrime p ->
  {{ p, cube x 🔽 (x * x * x) mod p, True }}.
Proof.
  intros.
  unfold cube.
  eapply Run.Equiv. {
    eapply Run.Replace. {
      eapply Run.Let. {
        apply Run.BinOp.
      }
      apply Run.BinOp.
    }
    cbn.
    (* This property should be handled automatically by some field reasoning tactic. *)
    admit.
  }
  tauto.
Admitted.
