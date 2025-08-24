Require Import Garden.Plonky3.M.
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Export Coq.Strings.PrimString.

Export PStringNotations.
Global Open Scope pstring_scope.

Module Field.
  Record t : Set := {
    value : Z;
  }.

  Definition eval {p} `{Prime p} (self : t) : Z :=
    UnOp.from self.(value).
  Arguments eval {p} {_} _ /.
End Field.

Module Var.
  Record t : Set := {
    index : Z;
  }.

  Definition make := Build_t.

  Module Env.
    Definition t : Set :=
      Z -> Z.
  End Env.

  Definition eval {p} `{Prime p} (env : Env.t) (self : t) : Z :=
    UnOp.from (env self.(index)).
  Arguments eval {p} {_} _ _ /.
End Var.

Module Expr.
  Inductive t : Set :=
  | Var (var : Var.t)
  | IsFirstRow
  | IsLastRow
  | IsTransition
  | Constant (value : Field.t)
  | Add (x y : t)
  | Sub (x y : t)
  | Neg (x : t)
  | Mul (x y : t).

  Module Env.
    Record t : Set := {
      is_first_row : bool;
      is_last_row : bool;
      is_transition : bool;
    }.
  End Env.

  Fixpoint eval {p} `{Prime p} (expr_env : Env.t) (var_env : Var.Env.t) (self : t) : Z :=
    match self with
    | Var var => Var.eval var_env var
    | IsFirstRow => Z.b2z expr_env.(Env.is_first_row)
    | IsLastRow => Z.b2z expr_env.(Env.is_last_row)
    | IsTransition => Z.b2z expr_env.(Env.is_transition)
    | Constant value => Field.eval value
    | Add x y => BinOp.add (eval expr_env var_env x) (eval expr_env var_env y)
    | Sub x y => BinOp.sub (eval expr_env var_env x) (eval expr_env var_env y)
    | Neg x => UnOp.opp (eval expr_env var_env x)
    | Mul x y => BinOp.mul (eval expr_env var_env x) (eval expr_env var_env y)
    end.

  Definition var (index : Z) : t :=
    Var {| Var.index := index |}.

  Definition constant (value : Z) : t :=
    Constant {| Field.value := value |}.

  Definition ZERO : t := constant 0.

  Definition ONE : t := constant 1.

  Definition not (e : t) : t :=
    Sub ONE e.
End Expr.

Module ToRocq.
  Class C (T : Set) : Set := {
    to_rocq (value : T) (indent : Z) : string;
  }.

  Fixpoint indent_aux (indent : nat) : string :=
    match indent with
    | O => ""
    | S n => PrimString.cat (PrimString.make 1%int63 32%int63) (indent_aux n)
    end.

  Definition indent (indent : Z) : string :=
    indent_aux (Z.to_nat indent).

  Fixpoint cats (l : list string) : string :=
    match l with
    | [] => ""
    | x :: xs => PrimString.cat x (cats xs)
    end.

  Fixpoint separate (separator : string) (l : list string) : string :=
    match l with
    | [] => ""
    | [x] => x
    | x :: xs => cats [x; separator; separate separator xs]
    end.

  Definition endl : string :=
    "
".

  Fixpoint pstring_of_uint (n : Decimal.uint) : PrimString.string :=
    match n with
    | Decimal.Nil => ""%pstring
    | Decimal.D0 n =>
        PrimString.cat (PrimString.make 1 48%int63) (pstring_of_uint n)
    | Decimal.D1 n =>
        PrimString.cat (PrimString.make 1 49%int63) (pstring_of_uint n)
    | Decimal.D2 n =>
        PrimString.cat (PrimString.make 1 50%int63) (pstring_of_uint n)
    | Decimal.D3 n =>
        PrimString.cat (PrimString.make 1 51%int63) (pstring_of_uint n)
    | Decimal.D4 n =>
        PrimString.cat (PrimString.make 1 52%int63) (pstring_of_uint n)
    | Decimal.D5 n =>
        PrimString.cat (PrimString.make 1 53%int63) (pstring_of_uint n)
    | Decimal.D6 n =>
        PrimString.cat (PrimString.make 1 54%int63) (pstring_of_uint n)
    | Decimal.D7 n =>
        PrimString.cat (PrimString.make 1 55%int63) (pstring_of_uint n)
    | Decimal.D8 n =>
        PrimString.cat (PrimString.make 1 56%int63) (pstring_of_uint n)
    | Decimal.D9 n =>
        PrimString.cat (PrimString.make 1 57%int63) (pstring_of_uint n)
    end.

  Definition of_Z (z : Z) : PrimString.string :=
    pstring_of_uint (Nat.to_uint (Z.to_nat z)).
End ToRocq.

Fixpoint string_of_expr (expr : Expr.t) (indent : Z) : string :=
  match expr with
  | Expr.Var var =>
    ToRocq.cats [ToRocq.indent indent; "Variable: "; ToRocq.of_Z var.(Var.index)]
  | Expr.IsFirstRow =>
    ToRocq.cats [ToRocq.indent indent; "IsFirstRow"]
  | Expr.IsLastRow =>
    ToRocq.cats [ToRocq.indent indent; "IsLastRow"]
  | Expr.IsTransition =>
    ToRocq.cats [ToRocq.indent indent; "IsTransition"]
  | Expr.Constant value =>
    ToRocq.cats [ToRocq.indent indent; "Constant: "; ToRocq.of_Z value.(Field.value)]
  | Expr.Add x y =>
    ToRocq.cats [ToRocq.indent indent; "Add:"; ToRocq.endl;
      string_of_expr x (indent + 2);
      ToRocq.endl;
      string_of_expr y (indent + 2)
    ]
  | Expr.Sub x y =>
    ToRocq.cats [ToRocq.indent indent; "Sub:"; ToRocq.endl;
      string_of_expr x (indent + 2);
      ToRocq.endl;
      string_of_expr y (indent + 2)
    ]
  | Expr.Neg x =>
    ToRocq.cats [ToRocq.indent indent; "Neg:"; ToRocq.endl;
      string_of_expr x (indent + 2)
    ]
  | Expr.Mul x y =>
    ToRocq.cats [ToRocq.indent indent; "Mul:"; ToRocq.endl;
      string_of_expr x (indent + 2);
      ToRocq.endl;
      string_of_expr y (indent + 2)
    ]
  end.

Global Instance ExprIsToRocq : ToRocq.C Expr.t := {
  to_rocq := string_of_expr;
}.

Global Instance OptionIsToRocq {T : Set} {C : ToRocq.C T} : ToRocq.C (option T) := {
  to_rocq self indent :=
    match self with
    | Some x =>
      ToRocq.cats [ToRocq.indent indent; "Some:"; ToRocq.endl;
        ToRocq.to_rocq x (indent + 2)
      ]
    | None => ToRocq.cats [ToRocq.indent indent; "None"]
    end;
}.

Global Instance ListIsToRocq {T : Set} {C : ToRocq.C T} : ToRocq.C (list T) := {
  to_rocq self indent :=
    ToRocq.cats (
      [ToRocq.indent indent; "Array:"] ++
      List.map (fun item => ToRocq.cats [ToRocq.endl; ToRocq.to_rocq item (indent + 2)]) self
    );
}.

Global Instance ArrayIsToRocq {T : Set} {C : ToRocq.C T} {N : Z} : ToRocq.C (Array.t T N) := {
  to_rocq self indent :=
    ToRocq.to_rocq (Array.to_list self) indent
}.

Module Env.
  Record t : Set := {
    expr : Expr.Env.t;
    var : Var.Env.t;
  }.
End Env.

Module Eval.
  Class C (T1 T2 : Set) : Set := {
    eval {p} `{Prime p} (env : Env.t) (self : T1) : T2;
  }.
End Eval.

Global Instance IdAsEval {T : Set} : Eval.C T T := {
  eval p _ env self := self;
}.

Global Instance VarIsEval : Eval.C Var.t Z := {
  eval p _ env self := Var.eval env.(Env.var) self;
}.

Global Instance ExprIsEval : Eval.C Expr.t Z := {
  eval p _ env self := Expr.eval env.(Env.expr) env.(Env.var) self;
}.

Global Instance ArrayIsEval {T : Set} `{Eval.C T Z} {N : Z} :
    Eval.C (Array.t T N) (Array.t Z N) := {
  eval p _ env self := Array.map (Eval.eval env) self;
}.

(** What we are pretty-printing at the end *)
Module Trace.
  Inductive t : Set :=
  | Pure
  | AssertZero (expr : Expr.t) (rest : t)
  | When (condition : Expr.t) (body : t) (rest : t).

  Fixpoint concat (self : t) (next : t) : t :=
    match self with
    | Pure => next
    | AssertZero expr rest => AssertZero expr (concat rest next)
    | When condition body rest => When condition body (concat rest next)
    end.

  (** We flatten the [When] operator, as while it is useful on its own, it is hard to make it appear
      explicitly on the Rust side without modifying Plonky3 itself. *)
  Fixpoint flatten (self : t) : list Expr.t :=
    match self with
    | Pure => []
    | AssertZero expr rest => expr :: flatten rest
    | When condition body rest =>
      let body := flatten body in
      let rest := flatten rest in
      (List.map (Expr.Mul condition) body) ++ rest
    end.

  Fixpoint to_rocq (self : t) (indent : Z) : string :=
    match self with
    | Pure => ToRocq.cats [ToRocq.indent indent; "Pure"]
    | AssertZero expr rest =>
      ToRocq.cats [
        ToRocq.indent indent; "AssertZero:"; ToRocq.endl;
        ToRocq.to_rocq expr (indent + 2);
        ToRocq.endl;
        to_rocq rest indent 
      ]
    | When condition body rest =>
      ToRocq.cats [ToRocq.indent indent; "When:"; ToRocq.endl;
        ToRocq.cats [ToRocq.indent (indent + 2); "Condition:"; ToRocq.endl;
          ToRocq.to_rocq condition (indent + 4)
        ];
        ToRocq.endl;
        ToRocq.cats [ToRocq.indent (indent + 2); "Body:"; ToRocq.endl;
          to_rocq body (indent + 4)
        ];
        ToRocq.endl;
        to_rocq rest indent
      ]
  end.

  Global Instance IsToRocq : ToRocq.C t := {
    to_rocq self indent :=
      let asserts := flatten self in
      ToRocq.separate ToRocq.endl (
        List.map (fun assert =>
          ToRocq.cats [ToRocq.indent indent; "AssertZero:"; ToRocq.endl;
            ToRocq.to_rocq assert (indent + 2)
          ]
        ) asserts
      );
  }.
End Trace.

Module MExpr.
  Inductive t (A : Set) : Set :=
  | Pure (value : A) : t A
  | AssertZero (expr : Expr.t) (value : A) : t A
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call (e : t A) : t A
  | Let {B : Set} (e : t B) (k : B -> t A) : t A
  (** We add this condition here as it helps to have a clear pretty-printing *)
  | When (condition : Expr.t) (body : t A) : t A
  .
  Arguments Pure {_}.
  Arguments AssertZero {_}.
  Arguments Call {_}.
  Arguments Let {_ _}.
  Arguments When {_}.

  Fixpoint flatten {A : Set} (self : t A) : A * Trace.t :=
    match self with
    | Pure value => (value, Trace.Pure)
    | AssertZero expr value => (value, Trace.AssertZero expr Trace.Pure)
    | Call e => flatten e
    | Let e k =>
      let '(value_e, constraints_e) := flatten e in
      let '(value_k, constraints_k) := flatten (k value_e) in
      (value_k, Trace.concat constraints_e constraints_k)
    | When condition body =>
      let '(value_body, constraints_body) := flatten body in
      (value_body, Trace.When condition constraints_body Trace.Pure)
    end.

  Module Eq.
    (** Equality with the [M.t] monad. *)
    Inductive t {A1 A2 : Set} `{Eval.C A1 A2} {p} `{Prime p} (env : Env.t) :
      MExpr.t A1 -> M.t A2 -> Prop :=
    | Pure (value : A1) value' :
      Eval.eval env value = value' ->
      t env (Pure value) (M.Pure value')
    | AssertZero (expr : Expr.t) expr' (value : A1) value' :
      Eval.eval env expr = expr' ->
      Eval.eval env value = value' ->
      t env (AssertZero expr value) (M.AssertZero expr' value')
    | Call (e : MExpr.t A1) (e' : M.t A2) :
      t env e e' ->
      t env (MExpr.Call e) (M.Call e')
    | Let {B1 B2 : Set} `{Eval.C B1 B2}
        (e : MExpr.t B1) (k : B1 -> MExpr.t A1)
        (e' : M.t B2) (k' : B2 -> M.t A2) :
      t env e e' ->
      (forall (value : B1),
        t env (k value) (k' (Eval.eval env value))
      ) ->
      t env (MExpr.Let e k) (M.Let e' k')
    | When (condition : Expr.t) condition' (body : MExpr.t A1) (body' : M.t A2) :
      Eval.eval env condition = condition' ->
      t env body body' ->
      t env (MExpr.When condition body) (M.When condition' body')
    .
  End Eq.

  Fixpoint eval {A : Set} {p} `{Prime p}
      (env : Env.t)
      (self : t A) :
      M.t A :=
    match self with
    | Pure value => M.pure value
    | AssertZero expr value => M.AssertZero (Eval.eval env expr) value
    | Call e => M.Call (eval env e)
    | Let e k =>
      let* value_e := eval env e in
      eval env (k value_e)
    | When condition body =>
      M.when (Eval.eval env condition) (eval env body)
    end.

  Fixpoint map {A B : Set} (f : A -> B) (self : t A) : t B :=
    match self with
    | Pure value => Pure (f value)
    | AssertZero expr value => AssertZero expr (f value)
    | Call e => Call (map f e)
    | Let e k => Let e (fun x => map f (k x))
    | When condition body => When condition (map f body)
    end.
End MExpr.

Notation "'let!' x ':=' e 'in' k" :=
  (MExpr.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Global Instance MExprIsToRocq {A : Set} {C : ToRocq.C A} : ToRocq.C (MExpr.t A) := {
  to_rocq self indent :=
    let '(result, trace) := MExpr.flatten self in
    ToRocq.cats (
      [ToRocq.indent indent; "Trace 🐾"; ToRocq.endl;
        ToRocq.to_rocq trace (indent + 2)
      ] ++
      [ToRocq.endl] ++
      [ToRocq.indent indent; "Result 🛍️"; ToRocq.endl;
        ToRocq.to_rocq result (indent + 2)
      ]
    );
}.

Definition pure {A : Set} (value : A) : MExpr.t A :=
  MExpr.Pure value.

Definition when {A : Set} (condition : Expr.t) (body : MExpr.t A) : MExpr.t A :=
  MExpr.When condition body.

Definition assert_zero (e : Expr.t) : MExpr.t unit :=
  MExpr.AssertZero e tt.

Definition assert_one (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Sub e Expr.ONE).

Definition assert_bool (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Mul e (Expr.Sub e Expr.ONE)).

Fixpoint for_in_zero_to_n_aux (N : nat) (f : Z -> MExpr.t unit) : MExpr.t unit :=
  match N with
  | O => pure tt
  | S N =>
    let! _ := for_in_zero_to_n_aux N f in
    f (Z.of_nat N)
  end.

Definition for_in_zero_to_n (N : Z) (f : Z -> MExpr.t unit) : MExpr.t unit :=
  for_in_zero_to_n_aux (Z.to_nat N) f.

Lemma for_in_zero_to_n_eq {N : Z} {p} `{Prime p}
    (env : Env.t)
    (f : Z -> MExpr.t unit) (f' : Z -> M.t unit)
    (H_f : forall (i : Z),
      MExpr.Eq.t env (f i) (f' i)
    ) :
  MExpr.Eq.t env (MExpr.for_in_zero_to_n N f) (M.for_in_zero_to_n N f').
Proof.
  with_strategy transparent [M.for_in_zero_to_n]
    unfold MExpr.for_in_zero_to_n, M.for_in_zero_to_n.
  set (n := Z.to_nat N); clearbody n.
  induction n; cbn; intros.
  { now constructor. }
  { econstructor. {
      apply IHn.
    }
    intros.
    apply H_f.
  }
Qed.

Module List.
  Fixpoint fold_left {A B : Set} (f : A -> B -> MExpr.t A) (acc : A) (l : list B) : MExpr.t A :=
    match l with
    | [] => pure acc
    | x :: xs =>
      let! acc := f acc x in
      fold_left f acc xs
    end.

  Module Eq.
    Lemma fold_left_eq {A1 A2 B1 B2 : Set} `{Eval.C A1 A2} `{Eval.C B1 B2} {p} `{Prime p}
        (env : Env.t)
        (f : A1 -> B1 -> MExpr.t A1) (f' : A2 -> B2 -> M.t A2)
        (acc : A1) acc' (l : list B1) l'
        (H_f : forall (acc : A1) (a : B1),
          MExpr.Eq.t env (f acc a) (f' (Eval.eval env acc) (Eval.eval env a))
        )
        (H_acc : Eval.eval env acc = acc')
        (H_l : List.map (Eval.eval env) l = l') :
      MExpr.Eq.t env
        (MExpr.List.fold_left f acc l)
        (M.List.fold_left f' acc' l').
    Proof.
      rewrite <- H_l, <- H_acc.
      clear H_l H_acc.
      revert acc.
      induction l; cbn; intros.
      { now constructor. }
      { econstructor. {
          apply H_f.
        }
        apply IHl.
      }
    Qed.
  End Eq.
End List.
