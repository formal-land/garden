Require Export Coq.PArith.BinPosDef.
Require Export Coq.Strings.PrimString.
Require Export Coq.ZArith.ZArith.

Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.
Require Export Coq.Strings.PrimString.
Class Prime (p : Z) : Prop := {
  is_prime : IsPrime p;
}.

Axiom prime_range : forall {p} `{Prime p}, 1 < p.

Module Default.
  Class C (A : Set) : Set := {
    default : A;
  }.

  Global Instance ZIsDefault : C Z := {
    default := 0;
  }.

  Global Instance BoolIsDefault : C bool := {
    default := false;
  }.
End Default.

Module Equal.
  Class C (A : Set) : Type := {
    t : A -> A -> Prop;
  }.
End Equal.

Notation "x =F y" := (Equal.t x y) (at level 70, no associativity).

Global Instance ZIsEqual : Equal.C Z := {
  Equal.t := eq;
}.

Class MapMod {p : Z} `{Prime p} (A : Set) : Set := {
  map_mod : A -> A;
}.

Module Mappable.
  Class C (Self : Set -> Set) (A B : Set) : Set := {
    map : (A -> B) -> Self A -> Self B;
  }.

  Global Instance IdIsMappable (A : Set) : C (fun (X : Set) => X) A A := {
    map f x := f x;
  }.
End Mappable.

Module IsBool.
  Class C (A : Set) : Type := {
    t : A -> Prop;
  }.

  Global Instance ZIsBool : C Z := {
    t x := x = Z.b2z (Z.odd x);
  }.
End IsBool.

Module InField.
  Class C {p} `{Prime p} (z : Z) : Prop := {
    make : z = z mod p;
  }.

  Global Instance mod_is_in_field {p} `{Prime p} (z : Z) : InField.C (z mod p).
  Admitted.
End InField.

Module Array.
  Record t {A : Set} {N : Z} : Set := {
    get : Z -> A;
  }.
  Arguments t : clear implicits.

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {|
      get index := x.(get) (start + index)
    |}.

  Definition slice_first {A : Set} {N : Z} (x : t A N) (count : Z) : t A count := 
    {|
      get := x.(get)
    |}.

  Definition slice_range {A : Set} {N : Z} (x : t A N) (start end_ : Z) : t A (end_ - start) :=
    {|
      get index := x.(get) (start + index)
    |}.

  Definition get_mod {p} `{Prime p} {N : Z} (x : t Z N) (i : Z) : Z :=
    x.(get) i mod p.

  Definition placeholder {A : Set} {N : Z} (x : A) : t A N :=
    {|
      get index := x
    |}.

  Definition map {A B : Set} {N : Z} (f : A -> B) (x : t A N) : t B N := 
    {|
      get index := f (x.(get) index)
    |}.

  Definition concat {A : Set} {N1 N2 : Z} (x1 : t A N1) (x2 : t A N2) : t A (N1 + N2) :=
    {|
      get index :=
        if index <? N1 then
          x1.(get) index
        else
          x2.(get) (index - N1)
    |}.

  Definition to_list {A : Set} {N : Z} (x : t A N) : list A :=
    List.map (fun i => x.(get) (Z.of_nat i)) (Lists.List.seq 0 (Z.to_nat N)).

  Definition of_list {A : Set} {N : Z} `{Default.C A} (l : list A): t A N :=
    {|
      get index := List.nth (Z.to_nat index) l Default.default
    |}.

  Global Instance IsDefault (A : Set) (N : Z) `{Default.C A} : Default.C (t A N) := {
    default :=
      {|
        get index := Default.default
      |}
  }.

  Module Eq.
    Global Instance IsEqual (A : Set) (N : Z) `{Equal.C A} : Equal.C (t A N) := {
      Equal.t (x y : t A N) :=
        forall (i : Z),
        0 <= i < N ->
        Equal.t (x.(get) i) (y.(get) i);
    }.

    Axiom dec : forall {N : Z} (x y : Array.t Z N), {Equal.t x y} + {~ Equal.t x y}.
  End Eq.

  Global Instance IsMapMod  {p} `{Prime p} (A : Set) (N : Z) `{MapMod p A} : MapMod (t A N) := {
    map_mod := map map_mod;
  }.

  Global Instance IsMappable (N : Z) (T : Set -> Set) (A B : Set)
      `{Mappable.C T A B} :
      Mappable.C (fun (X : Set) => t (T X) N) A B :=
  {
    Mappable.map f x := map (Mappable.map f) x;
  }.

  Global Instance IsIsBool (A : Set) (N : Z) `{IsBool.C A} : IsBool.C (t A N) := {
    t array :=
      forall (i : Z),
      0 <= i < N ->
      IsBool.t (array.(get) i);
  }.
End Array.

Notation "x .[ i ]" := (Array.get x i) (at level 9).

Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.

  Definition from {p} `{Prime p} (x : Z) : Z := 
    x mod p.
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

(* Notations *)
Notation "x +F y" := (BinOp.add x y) (at level 50, left associativity).
Notation "x -F y" := (BinOp.sub x y) (at level 50, left associativity).
Notation "-F x" := (UnOp.opp x) (at level 35, right associativity).
Notation "x *F y" := (BinOp.mul x y) (at level 40, left associativity).

Global Instance ZIsMapMod {p} `{Prime p} : MapMod Z := {
  map_mod := UnOp.from;
}.

Module IsInField.
  Global Instance from_is_in_field {p} `{Prime p} (x : Z) : InField.C (UnOp.from x).
  Proof. typeclasses eauto. Qed.

  Global Instance opp_is_in_field {p} `{Prime p} (x : Z) : InField.C (UnOp.opp x).
  Proof. typeclasses eauto. Qed.

  Global Instance add_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.add x y).
  Proof. typeclasses eauto. Qed.

  Global Instance sub_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.sub x y).
  Proof. typeclasses eauto. Qed.

  Global Instance mul_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.mul x y).
  Proof. typeclasses eauto. Qed.

  Global Instance div_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.div x y).
  Proof. typeclasses eauto. Qed.

  Global Instance mod_is_in_field {p} `{Prime p} (x y : Z) : InField.C (BinOp.mod_ x y).
  Proof. typeclasses eauto. Qed.
End IsInField.

Module Trace.
  Module Event.
    Inductive t : Set :=
    | AssertZero (expr : Z)
    | Message (message : string).

    Definition map_condition {p} `{Prime p} (condition : Z) (event : t) : t :=
      match event with
      | AssertZero expr => AssertZero (condition *F expr)
      | Message _ => event
      end.
  End Event.

  Definition t : Set := list Event.t.
End Trace.

Module M.
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t (A : Set) : Set :=
  | Pure (value : A) : t A
  | AssertZero (x : Z) (value : A) : t A
  (** This constructor does nothing, but helps to delimit what is inside the current the current
      function and what is being called, to better compose reasoning. *)
  | Call (e : t A) : t A
  | Let {B : Set} (e : t B) (k : B -> t A) : t A
  | When (condition : Z) (e : t A) : t A
  | Message (message : string) (k : t A) : t A
  .
  Arguments Pure {_}.
  Arguments AssertZero {_}.
  Arguments Call {_}.
  Arguments Let {_ _}.
  Arguments When {_}.
  Arguments Message {_}.

  Fixpoint map {A B : Set} (f : A -> B) (e : M.t A) : M.t B :=
    match e with
    | M.Pure value => M.Pure (f value)
    | M.AssertZero x value => M.AssertZero x (f value)
    | M.Call e => M.Call (map f e)
    | M.Let e k => M.Let e (fun x => map f (k x))
    | M.When condition e => M.When condition (map f e)
    | M.Message message k => M.Message message (map f k)
    end.

  Fixpoint to_trace {p} `{Prime p} {A : Set} (e : M.t A) : A * Trace.t :=
    match e with
    | M.Pure value => (value, [])
    | M.AssertZero expr value => (value, [Trace.Event.AssertZero expr])
    | M.Call e => to_trace e
    | M.Let e k =>
      let '(value_e, trace_e) := to_trace e in
      let '(value_k, trace_k) := to_trace (k value_e) in
      (value_k, trace_e ++ trace_k)
    | M.When condition e =>
      let '(value_e, trace_e) := to_trace e in
      (value_e, List.map (Trace.Event.map_condition condition) trace_e)
    | M.Message message k =>
      let '(value_k, trace_k) := to_trace k in
      (value_k, [Trace.Event.Message message] ++ trace_k)
    end.
End M.

Notation "'let*' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Notation "'msg*' message 'in' k" :=
  (M.Message message k)
  (at level 200, message at level 200, k at level 200).

Definition pure {A : Set} (x : A) : M.t A :=
  M.Pure x.

(* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_zero (x : Z) : M.t unit :=
  M.AssertZero x tt.

Definition assert_bool {p} `{Prime p} (x : Z) : M.t unit :=
  M.AssertZero (BinOp.mul (BinOp.sub 1 x) x) tt.

Fixpoint for_in_zero_to_n_aux (N : nat) (f : Z -> M.t unit) : M.t unit :=
  match N with
  | O => pure tt
  | S N =>
    let* _ := for_in_zero_to_n_aux N f in
    f (Z.of_nat N)
  end.

Definition for_in_zero_to_n (N : Z) (f : Z -> M.t unit) : M.t unit :=
  for_in_zero_to_n_aux (Z.to_nat N) f.

Definition assert_zeros {N : Z} (array : Array.t Z N) : M.t unit :=
  for_in_zero_to_n N (fun i => assert_zero (array.(Array.get) i)).

(* helper: acting on all elements in an array *)
Definition for_each {A : Set} {N : Z} (f : A -> M.t unit) (x : Array.t A N) : M.t unit :=
  for_in_zero_to_n N (fun i => f (Array.get x i)).

(* helper: acting on all elements in an array, but returning a sum *)

Fixpoint sum_for_in_zero_to_n_aux {p} `{Prime p} (N : nat) (f : Z -> Z) : Z :=
  match N with
  | O => 0
  | S N => BinOp.add (sum_for_in_zero_to_n_aux N f) (f (Z.of_nat N))
  end.

Definition sum_for_in_zero_to_n {p} `{Prime p} (N : Z) (f : Z -> Z) : Z :=
  sum_for_in_zero_to_n_aux (Z.to_nat N) f.

Definition call {A : Set} (e : M.t A) : M.t A :=
  M.Call e.

Definition collapsing_let {A B : Set} (e : M.t A) (k : A -> M.t B) : M.t B :=
  match e, k with
  | M.Pure x, k => k x
  | e, k => M.Let e k
  end.

Lemma odd_b2z_eq (b : bool) :
  Z.odd (Z.b2z b) = b.
Proof.
  destruct b; cbn; reflexivity.
Qed.

(** ** Primitives we also have in the library *)

Module Pair.
  Record t {A B : Set} : Set := {
    x : A;
    xs : B;
  }.
  Arguments t : clear implicits.
End Pair.

(* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_one {p} `{Prime p} (x : Z) : M.t unit :=
  M.AssertZero (BinOp.sub x 1) tt.

Definition assert_eq {p} `{Prime p} (x y : Z) : M.t unit :=
  M.AssertZero (BinOp.sub x y) tt.

  (* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
Definition assert_bools {p} `{Prime p} {N : Z} (l : Array.t Z N) : M.t unit :=
  M.for_in_zero_to_n N (fun i =>
    M.assert_bool (l.(Array.get) i)
  ).

Definition when {p} `{Prime p} {A : Set} (condition : Z) (e : M.t A) : M.t A :=
  M.When condition e.

Definition when_bool (condition : bool) (e : M.t unit) : M.t unit :=
  if condition then
    e
  else
    M.pure tt.

Definition not {p} `{Prime p} (x : Z) : Z :=
  BinOp.sub 1 x.

Definition xor {p} `{Prime p} (x y : Z) : Z :=
  (x +F y) -F (x *F (2 *F y)).

Axiom from_xor_eq : forall {p} `{Prime p} (x y : Z),
  UnOp.from (xor x y) = xor x y.

Axiom xor_eq : forall {p} `{Prime p} (x y : bool),
  xor (Z.b2z x) (Z.b2z y) = Z.b2z (xorb x y).

Lemma xor_is_bool {p} `{Prime p} (x y : Z) :
  IsBool.t x ->
  IsBool.t y ->
  IsBool.t (xor x y).
Proof.
  intros -> ->.
  rewrite xor_eq.
  cbn.
  now rewrite odd_b2z_eq.
Qed.

Definition xor3 {p} `{Prime p} (x y z : Z) : Z :=
  xor (xor x y) z.

Lemma xor3_eq : forall {p} `{Prime p} (x y z : bool),
  xor3 (Z.b2z x) (Z.b2z y) (Z.b2z z) = Z.b2z (xorb (xorb x y) z).
Proof.
  intros.
  unfold xor3.
  now repeat rewrite xor_eq.
Qed.

Lemma xor3_is_bool {p} `{Prime p} (x y z : Z) :
  IsBool.t x ->
  IsBool.t y ->
  IsBool.t z ->
  IsBool.t (xor3 x y z).
Proof.
  intros.
  now repeat apply xor_is_bool.
Qed.

Definition double {p} `{Prime p} (x : Z) : Z :=
  BinOp.mul x 2.

Module List.
  Fixpoint fold_left {A B : Set} (f : A -> B -> M.t A) (acc : A) (l : list B) : M.t A :=
    match l with
    | nil => M.pure acc
    | cons x xs =>
      let* acc := f acc x in
      fold_left f acc xs
    end.

  Fixpoint fold_right {A B : Set} (f : B -> A -> M.t A) (l : list B) (acc : A) : M.t A :=
    match l with
    | nil => M.pure acc
    | cons x xs =>
      let* acc := fold_right f xs acc in
      f x acc
    end.
End List.

Ltac show_equality_modulo :=
  unfold
    UnOp.from,
    BinOp.add,
    BinOp.sub,
    BinOp.mul,
    BinOp.div,
    BinOp.mod_;
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

Axiom mul_zero_implies_zero : forall {p} `{Prime p} (x y : Z),
  BinOp.mul x y = 0 <->
  UnOp.from x = 0 \/ UnOp.from y = 0.

Lemma mul_zero_implies_zero_3 {p} `{Prime p} (x y z : Z) :
  BinOp.mul (BinOp.mul x y) z = 0 <->
  UnOp.from x = 0 \/ UnOp.from y = 0 \/ UnOp.from z = 0.
Proof.
  rewrite mul_zero_implies_zero.
  replace (UnOp.from _) with (BinOp.mul x y) by show_equality_modulo.
  rewrite mul_zero_implies_zero.
  tauto.
Qed.

(** This lemma is often useful when the value we are comparing to zero is small and known. *)
Lemma is_zero_small {p} `{Prime p} (x : Z) :
  -p < x < p ->
  UnOp.from x = 0 <->
  x = 0.
Proof.
  intros.
  unfold UnOp.from.
  split; intros; [|now subst].
  assert (-p < x < 0 \/ 0 <= x < p) as [] by lia.
  { rewrite <- (Z.mod_unique x p (-1) (p + x)) in *; lia. }
  { rewrite <- (Z.mod_unique x p 0 x) in *; lia. }
Qed.

(* TODO: prove with Coqtail *)
Lemma sub_zero_equiv {p} `{Prime p} (x y : Z) :
  BinOp.sub x y = 0 <->
  UnOp.from x = UnOp.from y.
Proof.
Admitted.

Lemma sum_for_in_zero_to_n_zeros_eq {p} `{Prime p} (N : Z) (f : Z -> Z)
    (H_body : forall (i : Z), 0 <= i < N -> f i = 0) :
  M.sum_for_in_zero_to_n N f = 0.
Proof.
Admitted.

(** Rewrite rules for field operations. *)
Module FieldRewrite.
  Lemma from_zero {p} `{Prime p} : UnOp.from 0 = 0.
  Proof.
    reflexivity.
  Qed.
  Global Hint Rewrite @from_zero : field_rewrite.

  Lemma from_one {p} `{Prime p} : UnOp.from 1 = 1.
  Proof.
  Admitted.
  Global Hint Rewrite @from_one : field_rewrite.

  Lemma from_bool {p} `{Prime p} (x : bool) :
    UnOp.from (Z.b2z x) = Z.b2z x.
  Proof.
    unfold UnOp.from.
    destruct x; [apply from_one | apply from_zero].
  Qed.
  Global Hint Rewrite @from_bool : field_rewrite.

  Lemma from_from {p} `{Prime p} (x : Z) :
    UnOp.from (UnOp.from x) = UnOp.from x.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @from_from : field_rewrite.

  Lemma from_add {p} `{Prime p} (x y : Z) :
    UnOp.from (BinOp.add x y) = BinOp.add x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @from_add : field_rewrite.

  Lemma add_from_left {p} `{Prime p} (x y : Z) :
    BinOp.add (UnOp.from x) y = BinOp.add x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @add_from_left : field_rewrite.

  Lemma add_from_right {p} `{Prime p} (x y : Z) :
    BinOp.add x (UnOp.from y) = BinOp.add x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @add_from_right : field_rewrite.

  Lemma sub_from_left {p} `{Prime p} (x y : Z) :
    BinOp.sub (UnOp.from x) y = BinOp.sub x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @sub_from_left : field_rewrite.

  Lemma sub_from_right {p} `{Prime p} (x y : Z) :
    BinOp.sub x (UnOp.from y) = BinOp.sub x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @sub_from_right : field_rewrite.

  Lemma mul_from_left {p} `{Prime p} (x y : Z) :
    BinOp.mul (UnOp.from x) y = BinOp.mul x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @mul_from_left : field_rewrite.

  Lemma mul_from_right {p} `{Prime p} (x y : Z) :
    BinOp.mul x (UnOp.from y) = BinOp.mul x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @mul_from_right : field_rewrite.

  Lemma from_sub {p} `{Prime p} (x y : Z) :
    UnOp.from (BinOp.sub x y) = BinOp.sub x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @from_sub : field_rewrite.

  Lemma from_mul {p} `{Prime p} (x y : Z) :
    UnOp.from (BinOp.mul x y) = BinOp.mul x y.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @from_mul : field_rewrite.

  Lemma add_zero_left {p} `{Prime p} (x : Z) :
    BinOp.add 0 x = UnOp.from x.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @add_zero_left : field_rewrite.

  Lemma add_zero_right {p} `{Prime p} (x : Z) :
    BinOp.add x 0 = UnOp.from x.
  Proof.
    show_equality_modulo.
    f_equal; lia.
  Qed.
  Global Hint Rewrite @add_zero_right : field_rewrite.

  Lemma sub_zero_left {p} `{Prime p} (x : Z) :
    BinOp.sub 0 x = UnOp.from (-x).
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @sub_zero_left : field_rewrite.

  Lemma sub_zero_right {p} `{Prime p} (x : Z) :
    BinOp.sub x 0 = UnOp.from x.
  Proof.
    show_equality_modulo.
    f_equal; lia.
  Qed.
  Global Hint Rewrite @sub_zero_right : field_rewrite.

  Lemma mul_zero_left {p} `{Prime p} (x : Z) :
    BinOp.mul 0 x = 0.
  Proof.
    show_equality_modulo.
  Qed.
  Global Hint Rewrite @mul_zero_left : field_rewrite.

  Lemma mul_zero_right {p} `{Prime p} (x : Z) :
    BinOp.mul x 0 = 0.
  Proof.
    show_equality_modulo.
    now replace (x * 0) with 0 by lia.
  Qed.
  Global Hint Rewrite @mul_zero_right : field_rewrite.

  Lemma mul_one_left {p} `{Prime p} (x : Z) :
    BinOp.mul 1 x = UnOp.from x.
  Proof.
    show_equality_modulo.
    now replace (1 * x) with x by lia.
  Qed.
  Global Hint Rewrite @mul_one_left : field_rewrite.

  Lemma mul_one_right {p} `{Prime p} (x : Z) :
    BinOp.mul x 1 = UnOp.from x.
  Proof.
    show_equality_modulo.
    now replace (x * 1) with x by lia.
  Qed.
  Global Hint Rewrite @mul_one_right : field_rewrite.

  (** It applies the rewrite even under binders, for the goal and all the hypothesis. *)
  Ltac run :=
    try rewrite_db field_rewrite;
    repeat match goal with
    | H : _ |- _ => rewrite_db field_rewrite in H
    end.
End FieldRewrite.

Definition andn {p} `{Prime p} (x y : Z) : Z :=
  (1 -F x) *F y.

Lemma andn_eq {p} `{Prime p} (x y : bool) :
  andn (Z.b2z x) (Z.b2z y) = Z.b2z (andb (negb x) y).
Proof.
  intros.
  unfold andn.
  now destruct x, y; cbn; FieldRewrite.run.
Qed.

Lemma andn_is_bool {p} `{Prime p} (x y : Z) :
  IsBool.t x ->
  IsBool.t y ->
  IsBool.t (andn x y).
Proof.
  intros -> ->.
  rewrite andn_eq.
  cbn.
  now rewrite odd_b2z_eq.
Qed.

(** Utilities around the manipulation of limbs *)
Module Limbs.
  (** Sometimes we do not know yet that we are adding booleans, so we go through this step. *)
  Definition of_Z_bools {p} `{Prime p} (BITS_PER_LIMB : Z)
      (f : Z -> Z)
      (limb : Z) :
      Z :=
    let l : list nat :=
      List.rev (
        List.seq
          (Z.to_nat (limb * BITS_PER_LIMB))
          (Z.to_nat BITS_PER_LIMB)
        ) in
    Lists.List.fold_left (fun acc (z : nat) =>
      let z : Z := Z.of_nat z in
      (2 *F acc) +F f z
    ) l 0.

  (** We have already taken the modulo of the result. *)
  Lemma unop_from_of_Z_bools_eq {p} `{Prime p} (BITS_PER_LIMB : Z)
      (f : Z -> Z)
      (limb : Z) :
    UnOp.from (of_Z_bools BITS_PER_LIMB f limb) =
    of_Z_bools BITS_PER_LIMB f limb.
  Proof.
    unfold of_Z_bools.
    set (l := List.rev _); clearbody l.
    assert (H_acc : UnOp.from 0 = 0) by trivial; revert H_acc.
    generalize 0 as acc.
    induction l; cbn; trivial; intros.
    apply IHl.
    now FieldRewrite.run.
  Qed.

  Lemma of_Z_bools_eq {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (f1 f2 : Z -> Z)
      (H_f1_f2_eq :
        forall (z : Z),
        0 <= z < NB_LIMBS * BITS_PER_LIMB ->
        f1 z = f2 z
      )
      (limb : Z)
      (H_limb : 0 <= limb < NB_LIMBS) :
    of_Z_bools BITS_PER_LIMB f1 limb =
    of_Z_bools BITS_PER_LIMB f2 limb.
  Proof.
  Admitted.

  (** Convert an array of bools to an array of limbs. *)
  Definition of_bools (BITS_PER_LIMB : Z)
      (f : Z -> bool)
      (limb : Z) :
      Z :=
    let l : list nat :=
      List.rev (
        List.seq
          (Z.to_nat (limb * BITS_PER_LIMB))
          (Z.to_nat BITS_PER_LIMB)
        ) in
    Lists.List.fold_left (fun acc (z : nat) =>
      let z : Z := Z.of_nat z in
      (2 * acc) + Z.b2z (f z)
    ) l 0.

  Lemma of_bools_eq_of_Z_bools {p} `{Prime p} (BITS_PER_LIMB : Z)
      (H_p : 2 ^ BITS_PER_LIMB < p)
      (f : Z -> bool)
      (limb : Z) :
    of_bools BITS_PER_LIMB f limb =
    of_Z_bools BITS_PER_LIMB (fun z => Z.b2z (f z)) limb.
  Proof.
  Admitted.

  Lemma of_bools_eq (NB_LIMBS BITS_PER_LIMB : Z)
      (f1 f2 : Z -> bool)
      (H_f1_f2_eq :
        forall (z : Z),
        0 <= z < NB_LIMBS * BITS_PER_LIMB ->
        f1 z = f2 z
      )
      (limb : Z) :
    of_bools BITS_PER_LIMB f1 limb =
    of_bools BITS_PER_LIMB f2 limb.
  Admitted.

  Lemma limbs_eq_implies_bools_eq (NB_LIMBS BITS_PER_LIMB : Z)
      (f1 f2 : Z -> bool)
      (H_limbs :
        forall (limb : Z),
        0 <= limb < NB_LIMBS ->
        of_bools BITS_PER_LIMB f1 limb =
        of_bools BITS_PER_LIMB f2 limb
      ) :
    forall (z : Z),
    0 <= z < NB_LIMBS * BITS_PER_LIMB ->
    f1 z = f2 z.
  Admitted.
End Limbs.

(** Rules to check if the contraints are what we expect, typically a unique possible value. *)
Module Run.
  Reserved Notation "{{ e 🔽 output , P }}".

  Inductive t {A : Set} : M.t A -> A -> Prop -> Prop :=
  | Pure (value : A) :
    {{ M.Pure value 🔽 value, True }}
  | AssertZero (x : Z) (value : A) :
    {{ M.AssertZero x value 🔽 value, x = 0 }}
  | Call (e : M.t A) (value : A) (P : Prop) :
    {{ e 🔽 value, P }} ->
    {{ M.Call e 🔽 value, P }}
  | Let {B : Set} (e : M.t B) (k : B -> M.t A) (value : B) (output : A) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 -> {{ k value 🔽 output, P2 }}) ->
    {{ M.Let e k 🔽 output, P1 /\ P2 }}
  | When (condition : Z) (e : M.t A) (value : A) (P : Prop) :
    (condition <> 0 -> {{ e 🔽 value, P }}) ->
    {{ M.When condition e 🔽 value, condition <> 0 -> P }}
  | Message (message : string) (e : M.t A) (value : A) (P : Prop) :
    {{ e 🔽 value, P }} ->
    {{ M.Message message e 🔽 value, P }}
  | Implies (e : M.t A) (value : A) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 -> P2) ->
    {{ e 🔽 value, P2 }}
  | Replace (e : M.t A) (value1 value2 : A) (P : Prop) :
    {{ e 🔽 value1, P }} ->
    value1 = value2 ->
    {{ e 🔽 value2, P }}

  where "{{ e 🔽 output , P }}" := (t e output P).

  Lemma AssertBool {p} `{Prime p} (x' : Z) :
    let x := UnOp.from x' in
    {{ M.assert_bool x 🔽 tt, IsBool.t x }}.
  Proof.
    eapply Run.Implies. {
      constructor.
    }
    intros H_mul.
    rewrite mul_zero_implies_zero in H_mul; destruct H_mul as [H_mul|H_mul].
    { autorewrite with field_rewrite in H_mul.
      rewrite sub_zero_equiv in H_mul.
      rewrite <- H_mul.
      now autorewrite with field_rewrite.
    }
    { autorewrite with field_rewrite in H_mul.
      hauto lq: on.
    }
  Qed.

  Lemma ForInZeroToN_nat {N : nat} (f : Z -> M.t unit) (P : Z -> Prop) :
    (forall i, 0 <= i < Z.of_nat N ->
      {{ f i 🔽 tt, P i }}
    ) ->
    {{ M.for_in_zero_to_n (Z.of_nat N) f 🔽 tt, forall i, 0 <= i < Z.of_nat N -> P i }}.
  Proof.
    intros H_body.
    unfold M.for_in_zero_to_n.
    replace (Z.to_nat (Z.of_nat N)) with N by lia.
    induction N; cbn in *.
    { eapply Run.Implies. {
        apply Run.Pure.
      }
      lia.
    }
    { eapply Run.Implies. {
        eapply Run.Let. {
          apply IHN.
          intros i H_i.
          apply H_body.
          lia.
        }
        intros _.
        apply H_body.
        lia.
      }
      intros.
      assert (i < Z.of_nat N \/ i = Z.of_nat N) as [H_i | H_i] by lia;
        hauto lq: on.
    }
  Qed.

  Lemma ForInZeroToN {N : Z} (f : Z -> M.t unit) (P : Z -> Prop) :
    (forall i, 0 <= i < N ->
      {{ f i 🔽 tt, P i }}
    ) ->
    {{ M.for_in_zero_to_n N f 🔽 tt, forall i, 0 <= i < N -> P i }}.
  Proof.
    intros H_body.
    assert (N < 0 \/ N = Z.of_nat (Z.to_nat N)) as [H_N | H_N] by lia.
    { unfold M.for_in_zero_to_n.
      replace (Z.to_nat N) with 0%nat by lia.
      cbn.
      eapply Run.Implies. {
        apply Run.Pure.
      }
      lia.
    }
    { rewrite H_N.
      apply ForInZeroToN_nat.
      hauto q: on.
    }
  Qed.

  (** To avoid unrolling this definition, as you should better go through the lemma above. *)
  Global Opaque M.for_in_zero_to_n.

  Lemma AssertZeros {N : Z} (array : Array.t Z N) :
    {{ M.assert_zeros array 🔽 tt, forall i, 0 <= i < N -> array.[i] = 0 }}.
  Proof.
    eapply Run.Implies. {
      unfold M.assert_zeros.
      apply ForInZeroToN.
      intros.
      apply AssertZero.
    }
    trivial.
  Qed.

  Lemma AssertZerosFromFnSub {p} `{Prime p} {N : Z} (f g : Z -> Z) 
      (H_f : forall (i : Z), 0 <= i < N -> InField.C (f i))
      (H_g : forall (i : Z), 0 <= i < N -> InField.C (g i)) :
    {{ M.assert_zeros (N := N) {| Array.get i := BinOp.sub (f i) (g i) |} 🔽
      tt,
      forall (i : Z),
      0 <= i < N ->
      f i = g i
    }}.
  Proof.
    intros.
    eapply Run.Implies. {
      eapply Run.AssertZeros.
    }
    cbn; intros H_zeros i H_i.
    rewrite (H_f i H_i).(InField.make).
    rewrite (H_g i H_i).(InField.make).
    apply sub_zero_equiv.
    now apply H_zeros.
  Qed.

  Lemma LetAccumulate {A B : Set}
      (e : M.t A) (k : A -> M.t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 -> {{ k value 🔽 output, P2 }}) ->
    {{ M.Let e k 🔽 output, P2 }}.
  Proof.
    intros.
    eapply Run.Implies. {
      eapply Run.Let; eassumption.
    }
    tauto.
  Qed.

  (** Here we will automatically apply the most appropriate [Run.t] lemma, as some operators are
      better handled as whole primitives. *)
  Ltac run_step :=
    (apply AssertBool) ||
    (apply AssertZerosFromFnSub; try typeclasses eauto) ||
    (apply AssertZeros) ||
    (eapply Run.ForInZeroToN) ||
    (apply Run.Pure) ||
    (apply Run.AssertZero) ||
    (apply Run.Call) ||
    (eapply Run.Let) ||
    (apply Run.When) ||
    (apply Run.Message) ||
    match goal with
    | |- True -> _ => intros _
    | _ => intros
    end.

  Ltac run :=
    repeat run_step.
End Run.
Export Run.

(** Evaluation rule to show the completeness of a circuit. *)
Module Complete.
  Reserved Notation "{{ e ✅ value }}".

  Inductive t {A : Set} : M.t A -> A -> Prop :=
  | Pure (value : A) :
    {{ M.Pure value ✅ value }}
  | AssertZero (x : Z) (value : A) :
    x = 0 ->
    {{ M.AssertZero x value ✅ value }}
  | Call (e : M.t A) (value : A) :
    {{ e ✅ value }} ->
    {{ M.Call e ✅ value }}
  | Let {B : Set} (e : M.t B) (value : B) (k : B -> M.t A) (value_k : A) :
    {{ e ✅ value }} ->
    {{ k value ✅ value_k }} ->
    {{ M.Let e k ✅ value_k }}
  | When (condition : Z) (e : M.t A) (value : A) :
    (condition <> 0 -> {{ e ✅ value }}) ->
    {{ M.When condition e ✅ value }}

  where "{{ e ✅ value }}" := (t e value).

  Lemma ForInZeroToN_nat {N : nat} (f : Z -> M.t unit) :
    (forall i, 0 <= i < Z.of_nat N ->
      {{ f i ✅ tt }}
    ) ->
    {{ M.for_in_zero_to_n (Z.of_nat N) f ✅ tt }}.
  Proof.
    intros H_body.
    with_strategy transparent [M.for_in_zero_to_n] unfold M.for_in_zero_to_n.
    replace (Z.to_nat (Z.of_nat N)) with N by lia.
    induction N; cbn in *.
    { apply Complete.Pure. }
    { eapply Complete.Let. {
        apply IHN.
        intros i H_i.
        apply H_body.
        lia.
      }
      apply H_body.
      lia.
    }
  Qed.

  Lemma ForInZeroToN {N : Z} (f : Z -> M.t unit) :
    (forall i, 0 <= i < N ->
      {{ f i ✅ tt }}
    ) ->
    {{ M.for_in_zero_to_n N f ✅ tt }}.
  Proof.
    intros H_body.
    assert (N < 0 \/ N = Z.of_nat (Z.to_nat N)) as [H_N | H_N] by lia.
    { with_strategy transparent [M.for_in_zero_to_n] unfold M.for_in_zero_to_n.
      replace (Z.to_nat N) with 0%nat by lia.
      cbn.
      apply Complete.Pure.
    }
    { rewrite H_N.
      apply ForInZeroToN_nat.
      hauto q: on.
    }
  Qed.
End Complete.
Export Complete.

(* could be later moved together to a single module doing modulo arithmetics. *)

(* Utilities used for modulo arithmetics *)
Lemma mod_when_smaller {p : Z} (x : Z) (Hx : 0 <= x < p) :
  x mod p = x.
Proof.
  apply Zmod_small; auto.
Qed.

(* possible referencehttps://math.stackexchange.com/questions/2542245/how-to-prove-chinese-remainder-theorem-by-coq *)
Lemma chinese_remainder_simpler: forall n p a b : Z,
    n <> 0 ->
    p <> 0 ->
    Znumtheory.rel_prime n p ->
    exists x:Z, (x mod n = a mod n) /\ (x mod p = b mod p). 
Proof.
  intros n p a b npos ppos coprime. 
  destruct (Znumtheory.rel_prime_bezout _ _ coprime) as [u v H0].
  exists (a * v * p + b * u * n). split.
  - rewrite Z.mod_add. 2: exact npos.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod n = 1 mod n) as H.
    rewrite H0. reflexivity.
    rewrite Z.add_comm, Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    reflexivity. exact npos.
  - rewrite Z.add_comm, Z.mod_add. 2: exact ppos.
    rewrite <- Z.mul_assoc, <- Zdiv.Zmult_mod_idemp_r.
    assert ((u * n + v * p) mod p = 1 mod p) as H.
    rewrite H0. reflexivity.
    rewrite Z.mod_add in H. rewrite H.
    rewrite Zdiv.Zmult_mod_idemp_r, Z.mul_1_r.
    reflexivity. exact ppos.  
Qed.

(** Binary Chinese Remainder Theorem: if p, q are coprime, then the equation system 
    "x mod p = a /\ x mod q = b" has a unique solution modulo p * q *)
Axiom binary_chinese_remainder_alt : forall (p q x t : Z),
  p <> 0 ->
  q <> 0 ->
  Znumtheory.rel_prime p q ->
  x mod p = t mod p ->
  x mod q = t mod q ->
  x mod (p * q) = t mod (p * q).

Lemma mod_0_range (k : Z) (x : Z) :
    k > 0 -> 
    -k < x < k ->
    x mod k = 0 ->
    x = 0.
Proof.
Admitted.


Fixpoint fast_pow_modulo_positive (acc base modulus : Z) (exponent : positive) : Z :=
  match exponent with
  | xH => (acc * base) mod modulus
  | xO p =>
    fast_pow_modulo_positive acc ((base * base) mod modulus) modulus p
  | xI p =>
    let acc := (acc * base) mod modulus in
    fast_pow_modulo_positive acc ((base * base) mod modulus) modulus p
  end.

Definition mod_inverse (a p : Z) : Z :=
  match p with
  | Zpos p' => fast_pow_modulo_positive 1 a p (Pos.pred (Pos.pred p'))
  | _ => 0 (* We will always have 1 <= p *)
  end.


Module Test_mod_inverse.
  Definition test1 : Z := mod_inverse 3 7.
  Goal test1 = 5.
  Proof.
    reflexivity.
  Qed.

  Definition test2 : Z := mod_inverse 2 11. 
  Goal test2 = 6.
  Proof.
    reflexivity.
  Qed.

  Definition test3 : Z := mod_inverse 5 17.
  Goal test3 = 7.
  Proof.
    reflexivity.
  Qed.

  Definition test4 : Z := mod_inverse 5 (2 ^ 31 - 1).
  Goal test4 = 858993459.
  Proof.
    reflexivity.
  Qed.
End Test_mod_inverse.

(** A monad to simplify the generation of data structures with fresh variables. This is useful to
    validate that our models have the same constraints as the original implementations. *)
Module MGenerate.
  Definition t (A : Set) : Set :=
    Z -> A * Z.

  Definition pure {A : Set} (value : A) : t A :=
    fun n => (value, n).

  Definition bind {A B : Set} (e : t A) (k : A -> t B) : t B :=
    fun n =>
      let '(value, n') := e n in
      k value n'.

  (** Fake constructor used for the pretty-printing. *)
  Definition Var (z : Z) : Z :=
    z.
  Global Opaque Var.

  Definition generate_var : t Z :=
    fun n => (Var n, n + 1).

  Definition eval {A : Set} (x : t A) : A :=
    fst (x 0).

  Class C (A : Set) : Set := {
    generate : t A;
  }.

  Fixpoint generate_list {A : Set} `{C A} (n : nat) : t (list A) :=
    match n with
    | O => pure []
    | S n =>
      bind generate (fun x =>
        bind (generate_list n) (fun xs =>
          pure (x :: xs)
        )
      )
    end.

  (** This is a marker that we remove with the following tactic. *)
  Axiom run : forall {A : Set}, t A -> A.

  (** A tactic that replaces all [run] markers with a bind operation.
    This allows to represent programs without introducing
    explicit names for all intermediate computation results. *)
  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (bind _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (bind _ _);
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
        refine (bind _ _);
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
      | _ => exact (pure e)
      end
    end.
End MGenerate.

Notation "e (| e1 , .. , en |)" :=
  (MGenerate.run ((.. (e e1) ..) en))
  (at level 100).

Notation "e (||)" :=
  (MGenerate.run e)
  (at level 100).

Notation "[[ e ]]" :=
  (ltac:(MGenerate.monadic e))
  (* Use the version below for debugging and show errors that are made obscure by the tactic *)
  (* (MGenerate.pure e) *)
  (only parsing).

Notation "'let*g' x ':=' e 'in' k" :=
  (MGenerate.bind e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Global Instance VarIsGenerate : MGenerate.C Z := {
  generate := MGenerate.generate_var;
}.

Global Instance ArrayIsGenerate {T : Set} `{MGenerate.C T} `{Default.C T} {N : Z} :
    MGenerate.C (Array.t T N) := {
  generate :=
    MGenerate.bind (MGenerate.generate_list (Z.to_nat N)) (fun l =>
      MGenerate.pure (Array.of_list l)
    );
}.

Global Instance CoupleIsGenerate {T1 T2 : Set} `{MGenerate.C T1} `{MGenerate.C T2} :
    MGenerate.C (T1 * T2) := {
  generate :=
    MGenerate.bind MGenerate.generate (fun v1 =>
    MGenerate.bind MGenerate.generate (fun v2 =>
      MGenerate.pure (v1, v2)
    ));
}.

Module GenerateExample.
  Definition five_items : MGenerate.t (list Z) :=
    [[
      [
        MGenerate.generate (||);
        MGenerate.generate (||);
        MGenerate.generate (||);
        MGenerate.generate (||);
        MGenerate.generate (||)
      ]
    ]].

  Goal MGenerate.eval five_items = [
    MGenerate.Var 0;
    MGenerate.Var 1;
    MGenerate.Var 2;
    MGenerate.Var 3;
    MGenerate.Var 4
  ].
  Proof. reflexivity. Qed.

  Definition pair_items : MGenerate.t (list Z * list Z) :=
    [[
      (
        five_items (||),
        five_items (||)
      )
    ]].

  Goal MGenerate.eval pair_items = (
    [
      MGenerate.Var 0;
      MGenerate.Var 1;
      MGenerate.Var 2;
      MGenerate.Var 3;
      MGenerate.Var 4
    ],
    [
      MGenerate.Var 5;
      MGenerate.Var 6;
      MGenerate.Var 7;
      MGenerate.Var 8;
      MGenerate.Var 9
    ]
  ).
  Proof. reflexivity. Qed.
End GenerateExample.
