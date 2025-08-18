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

Module Builder.
  Record t : Set := {
    constraints : list Expr.t;
  }.

  Definition eval {p} `{Prime p} (expr_env : Expr.Env.t) (var_env : Var.Env.t) (self : t) : Prop :=
    Lists.List.fold_left (fun acc e => acc /\ Expr.eval expr_env var_env e = 0) self.(constraints) True.

  Definition new : t :=
    {| constraints := [] |}.

  Definition assert_zero (builder : t) (e : Expr.t) : t :=
    {| constraints := e :: builder.(constraints) |}.

  Definition assert_one (builder : t) (e : Expr.t) : t :=
    assert_zero builder (Expr.Sub e Expr.ONE).

  Definition assert_bool (builder : t) (e : Expr.t) : t :=
    assert_zero builder (Expr.Mul e (Expr.Sub e Expr.ONE)).

  Definition when (builder : t) (condition : Expr.t) (body : Builder.t -> Builder.t) : t :=
    let new_builder := body new in
    {|
      constraints :=
        List.map (fun e => Expr.Mul condition e) new_builder.(constraints) ++
        builder.(constraints)
    |}.
End Builder.

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

Global Instance BuilderIsToRocq : ToRocq.C Builder.t := {
  to_rocq builder indent :=
    ToRocq.cats (
      [ToRocq.indent indent; "Builder:"; ToRocq.endl] ++
      List.map (fun item =>
        ToRocq.cats [ToRocq.indent (indent + 2); "AssertZero:"; ToRocq.endl;
          ToRocq.to_rocq item (indent + 4)
        ]
      ) (List.rev builder.(Builder.constraints))
    );
}.
