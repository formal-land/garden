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
    ToRocq.cats [ToRocq.indent indent; "Variable: "; ToRocq.of_Z var.(Var.index); ToRocq.endl]
  | Expr.IsFirstRow =>
    ToRocq.cats [ToRocq.indent indent; "IsFirstRow"]
  | Expr.IsLastRow =>
    ToRocq.cats [ToRocq.indent indent; "IsLastRow"]
  | Expr.IsTransition =>
    ToRocq.cats [ToRocq.indent indent; "IsTransition"]
  | Expr.Constant value =>
    ToRocq.cats [ToRocq.indent indent; "Constant: "; ToRocq.of_Z value.(Field.value); ToRocq.endl]
  | Expr.Add x y =>
    ToRocq.cats [ToRocq.indent indent; "Add:"; ToRocq.endl;
      string_of_expr x (indent + 2);
      string_of_expr y (indent + 2)
    ]
  | Expr.Sub x y =>
    ToRocq.cats [ToRocq.indent indent; "Sub:"; ToRocq.endl;
      string_of_expr x (indent + 2);
      string_of_expr y (indent + 2)
    ]
  | Expr.Neg x =>
    ToRocq.cats [ToRocq.indent indent; "Neg:"; ToRocq.endl;
      string_of_expr x (indent + 2)
    ]
  | Expr.Mul x y =>
    ToRocq.cats [ToRocq.indent indent; "Mul:"; ToRocq.endl;
      string_of_expr x (indent + 2);
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
      [ToRocq.indent indent; "Array:"; ToRocq.endl] ++
      List.map (fun item => ToRocq.to_rocq item (indent + 2)) self
    );
}.

Global Instance ArrayIsToRocq {T : Set} {C : ToRocq.C T} {N : Z} : ToRocq.C (Array.t T N) := {
  to_rocq self indent :=
    ToRocq.to_rocq (Array.to_list self) indent
}.

Module MExpr.
  Inductive t (A : Set) : Set :=
  | Pure (value : A) : t A
  | AssertZero (expr : Expr.t) (value : A) : t A
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call (e : t A) : t A
  | Let {B : Set} (e : t B) (k : B -> t A) : t A
  .
  Arguments Pure {_}.
  Arguments AssertZero {_}.
  Arguments Call {_}.
  Arguments Let {_ _}.

  Fixpoint flatten {A : Set} (self : t A) : A * list Expr.t :=
    match self with
    | Pure value => (value, [])
    | AssertZero expr value => (value, [expr])
    | Call e => flatten e
    | Let e k =>
      let '(value_e, constraints_e) := flatten e in
      let '(value_k, constraints_k) := flatten (k value_e) in
      (value_k, constraints_k ++ constraints_e)
    end.

  Fixpoint eval {A : Set} {p} `{Prime p}
      (expr_env : Expr.Env.t)
      (var_env : Var.Env.t)
      (self : t A) :
      M.t A :=
    match self with
    | Pure value => M.pure value
    | AssertZero expr value => M.Equal (Expr.eval expr_env var_env expr) 0 value
    | Call e => M.Call (eval expr_env var_env e)
    | Let e k =>
      let* value_e := eval expr_env var_env e in
      eval expr_env var_env (k value_e)
    end.

  Fixpoint map {A B : Set} (f : A -> B) (self : t A) : t B :=
    match self with
    | Pure value => Pure (f value)
    | AssertZero expr value => AssertZero expr (f value)
    | Call e => Call (map f e)
    | Let e k => Let e (fun x => map f (k x))
    end.
End MExpr.

Notation "'let!' x ':=' e 'in' k" :=
  (MExpr.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Global Instance MExprIsToRocq {A : Set} {C : ToRocq.C A} : ToRocq.C (MExpr.t A) := {
  to_rocq self indent :=
    let '(result, constraints) := MExpr.flatten self in
    ToRocq.cats (
      [ToRocq.indent indent; "Builder:"; ToRocq.endl] ++
      List.map (fun item =>
        ToRocq.cats [ToRocq.indent (indent + 2); "AssertZero:"; ToRocq.endl;
          ToRocq.to_rocq item (indent + 4)
        ]
      ) (List.rev constraints) ++
      [ToRocq.to_rocq result indent]
    );
}.

Definition pure {A : Set} (value : A) : MExpr.t A :=
  MExpr.Pure value.

Fixpoint when {A : Set} (condition : Expr.t) (body : MExpr.t A) : MExpr.t A :=
  match body with
  | MExpr.Pure value => MExpr.Pure value
  | MExpr.AssertZero expr value => MExpr.AssertZero (Expr.Mul condition expr) value
  | MExpr.Call e => MExpr.Call (when condition e)
  | MExpr.Let e k => MExpr.Let (when condition e) (fun x => when condition (k x))
  end.

Definition assert_zero (e : Expr.t) : MExpr.t unit :=
  MExpr.AssertZero e tt.

Definition assert_one (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Sub e Expr.ONE).

Definition assert_bool (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Mul e (Expr.Sub e Expr.ONE)).

Module List.
  Fixpoint fold_left {A B : Set} (f : A -> B -> MExpr.t A) (acc : A) (l : list B) : MExpr.t A :=
    match l with
    | [] => pure acc
    | x :: xs =>
      let! acc := f acc x in
      fold_left f acc xs
    end.
End List.
