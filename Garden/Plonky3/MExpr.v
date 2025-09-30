Require Import Garden.Plonky3.M.
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Export Coq.Strings.PrimString.

Export PStringNotations.
Global Open Scope pstring_scope.

Module Field.
  Record t : Set := {
    value : Z;
  }.

  Definition make := Build_t.

  Definition eval {p} `{Prime p} (self : t) : Z :=
    UnOp.from self.(value).
  Arguments eval {p} {_} _ /.

  Definition from_canonical_u32 (value : Z) : t :=
    make (value mod (2 ^ 32)).

  Definition from_canonical_usize (value : Z) : t :=
    make (value mod (2 ^ 64)).

  (* TODO: compute the actual value *)
  Definition inverse (self : t) : t :=
    make self.(value).
    (* make (self.(value) * 123456789). *)
    (* if self.(value) =? 65536 then
      make 18446462594437939201
    else
      make 123456789. *)
End Field.

Module Var.
  Record t : Set := {
    index : Z;
  }.

  Definition make := Build_t.

  Global Instance VarIsDefault : Default.C t := {
    default := {| index := 0 |};
  }.

  Module Env.
    Definition t : Set :=
      Z -> Z.
  End Env.

  Definition eval {p} `{Prime p} (env : Env.t) (self : t) : Z :=
    UnOp.from (env self.(index)).
  Arguments eval {p} {_} _ _ /.
End Var.

Global Instance VarIsGenerate : MGenerate.C Var.t := {
  generate := fun n => (Var.make n, n + 1);
}.

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

  Definition NEG_ONE : t := constant (-1).

  Definition TWO : t := constant 2.

  Definition not (e : t) : t :=
    Sub ONE e.

  Definition from_canonical_u32 (value : Z) : t :=
    constant (value mod (2 ^ 32)).

  Definition from_canonical_usize (value : Z) : t :=
    constant (value mod (2 ^ 64)).

  (** We group additions and multiplications together, to operate on a list instead of on a couple
      of values. The main idea is to simplify the pretty-printing. *)
  Module Flat.
    Inductive t : Set :=
    | Var (var : Var.t)
    | IsFirstRow
    | IsLastRow
    | IsTransition
    | Constant (value : Field.t)
    | Add (xs : list t)
    | Sub (x y : t)
    | Neg (x : t)
    | Mul (xs : list t).

    Fixpoint flatten (expr : Expr.t) : t :=
      match expr with
      | Expr.Var var => Var var
      | Expr.IsFirstRow => IsFirstRow
      | Expr.IsLastRow => IsLastRow
      | Expr.IsTransition => IsTransition
      | Expr.Constant value => Constant value
      | Expr.Add x y =>
        let x := flatten x in
        let y := flatten y in
        match x, y with
        | Add xs, Add ys => Add (xs ++ ys)
        | Add xs, y => Add (xs ++ [y])
        | x, Add ys => Add (x :: ys)
        | x, y => Add [x; y]
        end
      | Expr.Sub x y => Sub (flatten x) (flatten y)
      | Expr.Neg x => Neg (flatten x)
      | Expr.Mul x y =>
        let x := flatten x in
        let y := flatten y in
        match x, y with
        | Mul xs, Mul ys => Mul (xs ++ ys)
        | Mul xs, y => Mul (xs ++ [y])
        | x, Mul ys => Mul (x :: ys)
        | x, y => Mul [x; y]
        end
      end.
  End Flat.
End Expr.

(* Notations *)
Notation "x +E y" := (Expr.Add x y) (at level 50, left associativity).
Notation "x -E y" := (Expr.Sub x y) (at level 50, left associativity).
Notation "-E x" := (Expr.Neg x) (at level 35, right associativity).
Notation "x *E y" := (Expr.Mul x y) (at level 40, left associativity).

(* Coercion from Var.t to Expr.t *)
Global Coercion Expr.Var : Var.t >-> Expr.t.

Module PrettyPrint.
  Class C (T : Set) : Set := {
    to_string (value : T) (indent : Z) : string;
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
    pstring_of_uint (N.to_uint (Z.to_N z)).
End PrettyPrint.

Fixpoint string_of_flat_expr (expr : Expr.Flat.t) (indent : Z) : string :=
  match expr with
  | Expr.Flat.Var var =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Variable: "; PrettyPrint.of_Z var.(Var.index)]
  | Expr.Flat.IsFirstRow =>
    PrettyPrint.cats [PrettyPrint.indent indent; "IsFirstRow"]
  | Expr.Flat.IsLastRow =>
    PrettyPrint.cats [PrettyPrint.indent indent; "IsLastRow"]
  | Expr.Flat.IsTransition =>
    PrettyPrint.cats [PrettyPrint.indent indent; "IsTransition"]
  | Expr.Flat.Constant value =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Constant: "; PrettyPrint.of_Z value.(Field.value)]
  | Expr.Flat.Add xs =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Add:"; PrettyPrint.endl;
      PrettyPrint.separate PrettyPrint.endl (List.map (fun x => string_of_flat_expr x (indent + 2)) xs)
    ]
  | Expr.Flat.Sub x y =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Sub:"; PrettyPrint.endl;
      string_of_flat_expr x (indent + 2);
      PrettyPrint.endl;
      string_of_flat_expr y (indent + 2)
    ]
  | Expr.Flat.Neg x =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Neg:"; PrettyPrint.endl;
      string_of_flat_expr x (indent + 2)
    ]
  | Expr.Flat.Mul xs =>
    PrettyPrint.cats [PrettyPrint.indent indent; "Mul:"; PrettyPrint.endl;
      PrettyPrint.separate PrettyPrint.endl (List.map (fun x => string_of_flat_expr x (indent + 2)) xs)
    ]
  end.

Global Instance ExprIsPrettyPrint : PrettyPrint.C Expr.t := {
  to_string self indent :=
    let flat := Expr.Flat.flatten self in
    string_of_flat_expr flat indent;
}.

Global Instance UnitIsPrettyPrint : PrettyPrint.C unit := {
  to_string self indent :=
    PrettyPrint.cats [PrettyPrint.indent indent; "tt"];
}.

Global Instance StringIsPrettyPrint : PrettyPrint.C string := {
  to_string self indent :=
    PrettyPrint.cats [PrettyPrint.indent indent; self];
}.

Global Instance ZIsPrettyPrint : PrettyPrint.C Z := {
  to_string self indent :=
    PrettyPrint.cats [PrettyPrint.indent indent; PrettyPrint.of_Z self];
}.

Global Instance OptionIsPrettyPrint {T : Set} {C : PrettyPrint.C T} : PrettyPrint.C (option T) := {
  to_string self indent :=
    match self with
    | Some x =>
      PrettyPrint.cats [PrettyPrint.indent indent; "Some:"; PrettyPrint.endl;
        PrettyPrint.to_string x (indent + 2)
      ]
    | None => PrettyPrint.cats [PrettyPrint.indent indent; "None"]
    end;
}.

Global Instance ListIsPrettyPrint {T : Set} {C : PrettyPrint.C T} : PrettyPrint.C (list T) := {
  to_string self indent :=
    PrettyPrint.cats (
      [PrettyPrint.indent indent; "Array:"] ++
      List.map (fun item => PrettyPrint.cats [PrettyPrint.endl; PrettyPrint.to_string item (indent + 2)]) self
    );
}.

Global Instance ArrayIsPrettyPrint {T : Set} {C : PrettyPrint.C T} {N : Z} : PrettyPrint.C (Array.t T N) := {
  to_string self indent :=
    PrettyPrint.to_string (Array.to_list self) indent
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

(** For interactions with buses *)
Module Interaction.
  (*
  pub struct Interaction<Expr> {
      pub message: Vec<Expr>,
      pub count: Expr,
      pub bus_index: u16,
      pub count_weight: u32,
  }
  *)
  Record t : Set := {
    message : list Expr.t;
    count : Expr.t;
    bus_index : Z;
    count_weight : Z;
  }.

  Global Instance IsPrettyPrint : PrettyPrint.C t := {
    to_string self indent :=
      PrettyPrint.cats [PrettyPrint.indent indent; "Interaction:"; PrettyPrint.endl;
        PrettyPrint.indent (indent + 2); "message:"; PrettyPrint.endl;
        PrettyPrint.separate PrettyPrint.endl (
          List.map (fun expr => PrettyPrint.to_string expr (indent + 4)) self.(message)
        );
        PrettyPrint.endl;
        PrettyPrint.indent (indent + 2); "count:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(count) (indent + 4);
        PrettyPrint.endl;
        PrettyPrint.indent (indent + 2); "bus_index:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(bus_index) (indent + 4);
        PrettyPrint.endl;
        PrettyPrint.indent (indent + 2); "count_weight:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(count_weight) (indent + 4)
      ];
  }.
End Interaction.

(** What we are pretty-printing at the end *)
Module Trace.
  Module Event.
    Inductive t : Set :=
    | AssertZero (expr : Expr.t)
    | Message (message : string)
    | Interaction (interaction : Interaction.t).

    Global Instance IsPrettyPrint : PrettyPrint.C t := {
      to_string self indent :=
        match self with
        | AssertZero expr =>
          PrettyPrint.cats [PrettyPrint.indent indent; "AssertZero:"; PrettyPrint.endl;
            PrettyPrint.to_string expr (indent + 2)
          ]
        | Message message =>
          PrettyPrint.cats [PrettyPrint.indent indent; "Message 🦜"; PrettyPrint.endl;
            PrettyPrint.to_string message (indent + 2)
          ]
        | Interaction interaction =>
          PrettyPrint.to_string interaction indent
        end;
    }.
  End Event.

  Definition t : Set := list Event.t.

  Global Instance IsPrettyPrint : PrettyPrint.C t := {
    to_string self indent :=
      let asserts := self in
      PrettyPrint.separate PrettyPrint.endl (
        List.map (fun event => PrettyPrint.to_string event indent) asserts
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
  | Message (message : string) (k : t A) : t A
  | Interaction (interaction : Interaction.t) (value : A) : t A
  .
  Arguments Pure {_}.
  Arguments AssertZero {_}.
  Arguments Call {_}.
  Arguments Let {_ _}.
  Arguments When {_}.
  Arguments Message {_}.
  Arguments Interaction {_}.

  Fixpoint to_trace {A : Set} (self : t A) : A * Trace.t :=
    match self with
    | Pure value => (value, [])
    | AssertZero expr value => (value, [Trace.Event.AssertZero expr])
    | Call e => to_trace e
    | Let e k =>
      let '(value_e, constraints_e) := to_trace e in
      let '(value_k, constraints_k) := to_trace (k value_e) in
      (value_k, constraints_e ++ constraints_k)
    | When condition body =>
      let '(value_body, constraints_body) := to_trace body in
      (
        value_body,
        List.map (fun event =>
          match event with
          | Trace.Event.AssertZero expr => Trace.Event.AssertZero (Expr.Mul condition expr)
          | Trace.Event.Message _ | Trace.Event.Interaction _ => event
          end
        ) constraints_body
      )
    | Message message k =>
      let '(value_k, constraints_k) := to_trace k in
      (value_k, [Trace.Event.Message message] ++ constraints_k)
    | Interaction interaction value =>
      (value, [Trace.Event.Interaction interaction])
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
    | Message (message : string) (k : MExpr.t A1) (k' : M.t A2) :
      t env k k' ->
      t env (MExpr.Message message k) k'
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
    | Message _ k =>
      eval env k
    | Interaction interaction value =>
      (* TODO *)
      M.pure value
    end.

  Fixpoint map {A B : Set} (f : A -> B) (self : t A) : t B :=
    match self with
    | Pure value => Pure (f value)
    | AssertZero expr value => AssertZero expr (f value)
    | Call e => Call (map f e)
    | Let e k => Let e (fun x => map f (k x))
    | When condition body => When condition (map f body)
    | Message message k => Message message (map f k)
    | Interaction interaction value => Interaction interaction (f value)
    end.
End MExpr.

Notation "'let!' x ':=' e 'in' k" :=
  (MExpr.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Notation "'msg!' message 'in' k" :=
  (MExpr.Message message k)
  (at level 200, message at level 200, k at level 200).

Global Instance MExprIsPrettyPrint {A : Set} {C : PrettyPrint.C A} : PrettyPrint.C (MExpr.t A) := {
  to_string self indent :=
    let '(result, trace) := MExpr.to_trace self in
    PrettyPrint.cats (
      [PrettyPrint.indent indent; "Trace 🐾"; PrettyPrint.endl;
        PrettyPrint.to_string trace (indent + 2)
      ] ++
      [PrettyPrint.endl] ++
      [PrettyPrint.indent indent; "Result 🛍️"; PrettyPrint.endl;
        PrettyPrint.to_string result (indent + 2)
      ]
    );
}.

Definition pure {A : Set} (value : A) : MExpr.t A :=
  MExpr.Pure value.

Definition when {A : Set} (condition : Expr.t) (body : MExpr.t A) : MExpr.t A :=
  MExpr.When condition body.

Definition interaction (interaction : Interaction.t) : MExpr.t unit :=
  MExpr.Interaction interaction tt.

(*
pub struct LookupBus {
    pub index: BusIndex,
}
*)
Module LookupBus.
  Record t : Set := {
    index : Z;
  }.
End LookupBus.

(* impl LookupBus { *)
Module Impl_LookupBus.
  (*
    pub fn lookup_key<AB, E>(
        &self,
        builder: &mut AB,
        query: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        builder.push_interaction(self.index, query, enabled, 1);
    }
  *)
  Definition lookup_key
    (self : LookupBus.t)
    (query : list Expr.t)
    (enabled : Expr.t) :
    MExpr.t unit :=
  interaction {|
    Interaction.message := query;
    Interaction.count := enabled;
    Interaction.bus_index := self.(LookupBus.index);
    Interaction.count_weight := 1;
  |}.

  (*
    pub fn add_key_with_lookups<AB, E>(
        &self,
        builder: &mut AB,
        key: impl IntoIterator<Item = E>,
        num_lookups: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        builder.push_interaction(self.index, key, -num_lookups.into(), 0);
    }
  *)
  Definition add_key_with_lookups
    (self : LookupBus.t)
    (key : list Expr.t)
    (num_lookups : Expr.t) :
    MExpr.t unit :=
  interaction {|
    Interaction.message := key;
    Interaction.count := num_lookups;
    Interaction.bus_index := self.(LookupBus.index);
    Interaction.count_weight := 0;
  |}.
End Impl_LookupBus.

Definition assert_zero (e : Expr.t) : MExpr.t unit :=
  MExpr.AssertZero e tt.

Definition assert_one (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Sub e Expr.ONE).

Definition assert_bool (e : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Mul e (Expr.Sub e Expr.ONE)).

Definition assert_eq (e1 e2 : Expr.t) : MExpr.t unit :=
  assert_zero (Expr.Sub e1 e2).

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

  Fixpoint iter {A : Set} (f : A -> MExpr.t unit) (l : list A) : MExpr.t unit :=
    match l with
    | [] => pure tt
    | x :: xs =>
      let! _ := f x in
      iter f xs
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

(** Utilities to convert the shallow representation of circuits into this deep representation. *)
Module OfShallow.
  Ltac to_expr e :=
    lazymatch e with
    | MGenerate.Var ?index => constr:(Expr.var index)
    | UnOp.opp ?x =>
      let x := to_expr x in
      constr:(Expr.Neg x)
    | BinOp.add ?x ?y =>
      let x := to_expr x in
      let y := to_expr y in
      constr:(Expr.Add x y)
    | BinOp.sub ?x ?y =>
      let x := to_expr x in
      let y := to_expr y in
      constr:(Expr.Sub x y)
    | BinOp.mul ?x ?y =>
      let x := to_expr x in
      let y := to_expr y in
      constr:(Expr.Mul x y)
    | ?z => constr:(Expr.constant z)
    end.

  Ltac to_mexpr_trace_aux trace :=
    lazymatch trace with
    | List.nil => constr:(List.nil (A := MExpr.Trace.Event.t))
    | List.cons ?event ?trace =>
      let event :=
        lazymatch event with
        | M.Trace.Event.AssertZero ?expr =>
          let expr := to_expr expr in
          constr:(MExpr.Trace.Event.AssertZero expr)
        | M.Trace.Event.Message ?message =>
          constr:(MExpr.Trace.Event.Message message)
        end in
      let trace := to_mexpr_trace_aux trace in
      constr:(List.cons event trace)
    end.

  Ltac to_mexpr_trace e :=
    let v := fresh "v" in
    pose e as v;
    (
      with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
      with_strategy transparent [M.for_in_zero_to_n]
        cbv in v
    );
    lazymatch eval unfold v in v with
    | ?e =>
      let result := to_mexpr_trace_aux e in
      exact result
    end.
End OfShallow.
