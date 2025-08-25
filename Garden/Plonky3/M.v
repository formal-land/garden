Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.

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

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

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
End Default.

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
    Definition t {A : Set} {N : Z} (x y : t A N) : Prop :=
      forall (i : Z), 0 <= i < N -> x.(get) i = y.(get) i.

    Axiom dec : forall {A : Set} {N : Z} (x y : Array.t A N), {t x y} + {~ t x y}.
  End Eq.
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
  .
  Arguments Pure {_}.
  Arguments AssertZero {_}.
  Arguments Call {_}.
  Arguments Let {_ _}.
  Arguments When {_}.

  Fixpoint map {A B : Set} (f : A -> B) (e : M.t A) : M.t B :=
    match e with
    | M.Pure value => M.Pure (f value)
    | M.AssertZero x value => M.AssertZero x (f value)
    | M.Call e => M.Call (map f e)
    | M.Let e k => M.Let e (fun x => map f (k x))
    | M.When condition e => M.When condition (map f e)
    end.
End M.

Notation "'let*' x ':=' e 'in' k" :=
  (M.Let e (fun x => k))
  (at level 200, x pattern, e at level 200, k at level 200).

Definition pure {A : Set} (x : A) : M.t A :=
  M.Pure x.

(* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) *)
Definition assert_zero (x : Z) : M.t unit :=
  M.AssertZero x tt.

Definition assert_bool {p} `{Prime p} (x : Z) : M.t unit :=
  M.AssertZero (BinOp.mul x (BinOp.sub x 1)) tt.

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

Module IsBool.
  Definition t (x : Z) : Prop :=
    x = Z.b2z (Z.odd x).
End IsBool.

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

Parameter xor : forall {p} `{Prime p}, Z -> Z -> Z.

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
  unfold IsBool.t.
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

Parameter andn : forall {p} `{Prime p}, Z -> Z -> Z.

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

Class MapMod {p : Z} `{Prime p} (A : Set) : Set := {
  map_mod : A -> A;
}.

Global Instance MapMod_Felt {p} `{Prime p} : MapMod Z := {
  map_mod := UnOp.from;
}.

Global Instance IsMapMod_Array {p} `{Prime p} (A : Set) (N : Z) `{MapMod p A} :
    MapMod (Array.t A N) :=
{
  map_mod := Array.map map_mod;
}.

Module Limbs.
  Definition of_bools {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (a : Array.t Z (NB_LIMBS * BITS_PER_LIMB)) :
      Array.t Z NB_LIMBS :=
    {|
      Array.get limb :=
        let l : list nat :=
          List.rev (
            List.seq
              (Z.to_nat (limb * BITS_PER_LIMB))%Z
              (Z.to_nat (limb * BITS_PER_LIMB + BITS_PER_LIMB))%Z
          ) in
        Lists.List.fold_left (fun acc (z : nat) =>
          let z : Z := Z.of_nat z in
          BinOp.add (BinOp.mul 2 acc) (a.(Array.get) z)
        ) l 0
    |}.

  Lemma from_of_bools_eq {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (a : Array.t Z (NB_LIMBS * BITS_PER_LIMB))
      (H_bools :
        forall (z : Z),
        0 <= z < NB_LIMBS * BITS_PER_LIMB ->
        IsBool.t (a.(Array.get) z)
      )
      (limb : Z) :
    0 <= limb < NB_LIMBS ->
    UnOp.from ((of_bools NB_LIMBS BITS_PER_LIMB a).(Array.get) limb) =
    (of_bools NB_LIMBS BITS_PER_LIMB a).(Array.get) limb.
  Admitted.

  Definition get_bit {NB_LIMBS : Z} (BITS_PER_LIMB : Z)
      (a : Array.t Z NB_LIMBS)
      (bit : Z) :
      bool :=
    let limb := bit / BITS_PER_LIMB in
    let bit_in_limb := bit mod BITS_PER_LIMB in
    let limb_value := a.(Array.get) limb in
    Z.testbit limb_value bit_in_limb.

  Lemma get_bit_of_bools_eq {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (a : Array.t Z (NB_LIMBS * BITS_PER_LIMB))
      (bit : Z)
      (H_bools :
        forall (z : Z),
        0 <= z < NB_LIMBS * BITS_PER_LIMB ->
        IsBool.t (a.(Array.get) z)
      ) :
    get_bit BITS_PER_LIMB (of_bools NB_LIMBS BITS_PER_LIMB a) bit =
    Z.odd (a.(Array.get) bit).
  Admitted.

  Lemma get_bit_of_bools_eqs {p} `{Prime p} (NB_LIMBS BITS_PER_LIMB : Z)
      (a_limbs : Array.t Z NB_LIMBS)
      (a_bools : Array.t Z (NB_LIMBS * BITS_PER_LIMB))
      (H_bools :
        forall (z : Z),
        0 <= z < NB_LIMBS * BITS_PER_LIMB ->
        IsBool.t (a_bools.(Array.get) z)
      )
      (H_limbs :
        forall (limb : Z),
        0 <= limb < NB_LIMBS ->
        a_limbs.(Array.get) limb =
        UnOp.from ((of_bools NB_LIMBS BITS_PER_LIMB a_bools).(Array.get) limb)
      ) :
    0 <= NB_LIMBS ->
    forall (bit : Z),
    0 <= bit < NB_LIMBS * BITS_PER_LIMB ->
    get_bit BITS_PER_LIMB a_limbs bit =
    Z.odd (a_bools.(Array.get) bit).
  Proof.
    intros.
    unfold get_bit.
    rewrite H_limbs by nia.
    rewrite <- get_bit_of_bools_eq by assumption.
    rewrite from_of_bools_eq; trivial.
    nia.
  Qed.
End Limbs.

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
      hauto lq: on.
    }
    { autorewrite with field_rewrite in H_mul.
      rewrite sub_zero_equiv in H_mul.
      rewrite H_mul.
      now autorewrite with field_rewrite.
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
    {{ M.assert_zeros array 🔽 tt, forall i, 0 <= i < N -> array.(Array.get) i = 0 }}.
  Proof.
    eapply Run.Implies. {
      unfold M.assert_zeros.
      apply ForInZeroToN.
      intros.
      apply AssertZero.
    }
    trivial.
  Qed.

  Lemma AssertZerosFromFnSub {p} `{Prime p} {N : Z} (f g : Z -> Z) :
    {{ M.assert_zeros (N := N) {| Array.get i := BinOp.sub (f i) (g i) |} 🔽
      tt,
      forall (i : Z),
      0 <= i < N ->
      UnOp.from (f i) = UnOp.from (g i)
    }}.
  Proof.
    intros.
    eapply Run.Implies. {
      eapply Run.AssertZeros.
    }
    cbn; intros H_zeros i H_i.
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
    (apply AssertZerosFromFnSub) ||
    (apply AssertZeros) ||
    (eapply Run.ForInZeroToN) ||
    (apply Run.Pure) ||
    (apply Run.AssertZero) ||
    (apply Run.Call) ||
    (eapply Run.Let) ||
    (apply Run.When) ||
    match goal with
    | |- True -> _ => intros _
    | _ => intros
    end.

  Ltac run :=
    repeat run_step.
End Run.
Export Run.

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
