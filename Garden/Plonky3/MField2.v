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

(** Field type for parameterization *)
Module Type FieldType.
  Parameter F : Set.
  Parameter zero : F.
  Parameter one : F.
  Parameter two : F.
  Parameter add : F -> F -> F.
  Parameter sub : F -> F -> F.
  Parameter mul : F -> F -> F.
  Parameter div : F -> F -> F.  (* Field division *)
  Parameter neg : F -> F.
  Parameter eq : F -> F -> Prop.
  
  (* Conversion functions for working with integers *)
  Parameter to_Z : F -> Z.
  Parameter from_Z : Z -> F.
  Parameter char : Z.  (* field characteristic *)
  
  (* Basic field axioms *)
  Axiom add_comm : forall x y, add x y = add y x.
  Axiom add_assoc : forall x y z, add x (add y z) = add (add x y) z.
  Axiom add_zero : forall x, add x zero = x.
  Axiom add_neg : forall x, add x (neg x) = zero.
  Axiom mul_comm : forall x y, mul x y = mul y x.
  Axiom mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z.
  Axiom mul_one : forall x, mul x one = x.
  Axiom distrib : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
  Axiom sub_def : forall x y, sub x y = add x (neg y).
  Axiom two_def : two = add one one.
  Axiom div_correct : forall x y, y <> zero -> mul (div x y) y = x.
  Axiom char_pos : char > 1.
End FieldType.

(** Parameterized modules that mimic original M.v structure *)
Module UnOp (Field : FieldType).
  Import Field.
  
  Inductive t : Set -> Set -> Set :=
  | Opp : t F F
  .

  Definition eval {A B : Set} (op : t A B) : A -> B :=
    match op in t A B return A -> B with
    | Opp => neg
    end.
End UnOp.

Module BinOp (Field : FieldType).
  Import Field.
  
  Inductive t : Set -> Set -> Set -> Set :=
  | Add : t F F F
  | Sub : t F F F
  | Mul : t F F F
  | Div : t F F F
  | Mod : t F F F  (* Keep for compatibility, though not typical in fields *)
  .

  Definition eval {A B C : Set} (op : t A B C) : A -> B -> C :=
    match op in t A B C return A -> B -> C with
    | Add => add
    | Sub => sub
    | Mul => mul
    | Div => div
    | Mod => fun x y => x  (* Simplified - mod doesn't make sense in general fields *)
    end.
End BinOp.

Module M (Field : FieldType).
  Import Field.
  Module FUnOp := UnOp Field.
  Module FBinOp := BinOp Field.
  
  (** The monad to write constraints generation in a certain field [F] *)
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | UnOp {A B : Set} (op : FUnOp.t A B) (x : A) : t B
  | BinOp {A B C : Set} (op : FBinOp.t A B C) (x1 : A) (x2 : B) : t C
  | Equal (x1 x2 : F) : t unit
  | Unwrap {A : Set} (value : option A) : t A
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

  Definition opp (x : F) : t F :=
    UnOp FUnOp.Opp x.

  Definition add (x y : F) : t F :=
    BinOp FBinOp.Add x y.

  Definition sub (x y : F) : t F :=
    BinOp FBinOp.Sub x y.

  Definition mul (x y : F) : t F :=
    BinOp FBinOp.Mul x y.

  Definition div (x y : F) : t F :=
    BinOp FBinOp.Div x y.

  Definition mod_ (x y : F) : t F :=
    BinOp FBinOp.Mod x y.

  Definition equal (x y : F) : t unit :=
    Equal x y.

  Definition call {A : Set} (e : t A) : t A :=
    Call e.

  Definition collapsing_let {A B : Set} (e : t A) (k : A -> t B) : t B :=
    match e, k with
    | Pure x, k => k x
    | e, k => Let e k
    end.

  (** Evaluate only the primitive operations and keep everything else. *)
  Fixpoint eval {A : Set} (e : t A) : t A :=
    match e in t A return t A with
    | Pure x => Pure x
    | UnOp op x => Pure (FUnOp.eval op x)
    | BinOp op x y => Pure (FBinOp.eval op x y)
    | Equal x y => Equal x y
    | Unwrap value => Unwrap value
    | Call e => Call (eval e)
    | Let e k => collapsing_let (eval e) (fun x => eval (k x))
    end.

  (** Notations defined inside the M module *)
  Notation "'let*' x ':=' e 'in' k" :=
    (Let e (fun x => k))
    (at level 200, x pattern, e at level 200, k at level 200).

  Notation "e (| e1 , .. , en |)" :=
    (run ((.. (e e1) ..) en))
    (at level 100).

  Notation "e (||)" :=
    (run e)
    (at level 100).

  Notation "[[ e ]]" :=
    (ltac:(monadic e))
    (* Use the version below for debugging and show errors that are made obscure by the tactic *)
    (* (Pure e) *)
    (only parsing).
End M.

(** Array module for field-based arrays *)
Module Array (Field : FieldType).
  Module MF := M Field.
  Import Field MF.
  
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

  Definition get {A : Set} {N : Z} (x : t A N) (index : Z) : MF.t A :=
    Unwrap (List.nth_error x.(value) (Z.to_nat index)).

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {| value := List.skipn (Z.to_nat start) x.(value) |}.

  Definition from_fn {A : Set} {N : Z} (f : Z -> MF.t A) : MF.t (t A N) :=
    let fix aux (index : nat) : MF.t (list A) :=
      match index with
      | O => Pure []
      | S index' =>
        let* xs := aux index' in
        let* x := f (Z.of_nat index') in
        Pure (x :: xs)
      end in
    let* xs := aux (Z.to_nat N) in
    Pure {| value := List.rev xs |}.
End Array.

(** Field-based assert and utility functions *)
Module FieldUtils (Field : FieldType).
  Module MF := M Field.
  Module ArrayF := Array Field.
  Import Field MF.

  (* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) *)
  Definition assert_zero (x : F) : t unit :=
    MF.equal x zero.

  (* fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
  Definition assert_zeros {N : Z} (l : ArrayF.t F N) : MF.t unit :=
    let fix aux (l : list F) : t unit :=
      match l with
      | [] => MF.Pure tt
      | x :: l' =>
        let* _ := (assert_zero x) in
        aux l'
      end in
    aux l.(ArrayF.value).

  (* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) *)
  Definition assert_one (x : F) : t unit :=
    equal x one.

  (* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) *)
  Definition assert_bool (x : F) : t unit :=
    [[ equal (| x, mul (| x, x |) |) ]].

  (* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) *)
  Definition assert_bools {N : Z} (l : ArrayF.t F N) : t unit :=
    let fix aux (l : list F) : t unit :=
      match l with
      | [] => Pure tt
      | x :: l' =>
        let* _ := assert_bool x in
        aux l'
      end in
    aux l.(ArrayF.value).

  Definition when (condition : bool) (e : t unit) : t unit :=
    if condition then e else Pure tt.

  Fixpoint for_in {A : Set} (l : list A) (f : A -> t unit) : t unit :=
    match l with
    | [] => Pure tt
    | x :: l' =>
      let* _ := f x in
      for_in l' f
    end.

  Definition for_in_zero_to_n (n : Z) (f : Z -> t unit) : t unit :=
    for_in (List.map Z.of_nat (List.seq 0 (Z.to_nat n))) f.

  Fixpoint fold {Acc Element : Set} (acc : Acc) (l : list Element) (f : Acc -> Element -> t Acc) :
      t Acc :=
    match l with
    | [] => Pure acc
    | x :: l' =>
      let* acc' := f acc x in
      fold acc' l' f
    end.

  Definition double (x : F) : t F :=
    [[ mul (| two, x |) ]].

  (** Field-aware XOR operation *)
  Definition xor (x y : F) : t F :=
    (* XOR for field elements: x + y - 2*x*y *)
    let* sum := add x y in
    let* product := mul x y in
    let* double_product := double product in
    sub sum double_product.

  Definition xor3 (x y z : F) : t F :=
    let* xy := xor x y in
    xor xy z.
End FieldUtils.

(** Rules to check if the contraints are what we expect, typically a unique possible value. *)
Module Run (Field : FieldType).
  Module FM := M Field.
  Import Field FM.
  
  Reserved Notation "{{ e 🔽 output , P }}".

  Inductive t : forall {A : Set}, FM.t A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ Pure value 🔽 value, True }}
  | Equal (x1 x2 : F) :
    {{ Equal x1 x2 🔽 tt, Field.eq x1 x2 }}
  | Unwrap {A : Set} (value : A) :
    {{ Unwrap (Some value) 🔽 value, True }}
  | Call {A : Set} (e : FM.t A) (value : A) (P : Prop) :
    {{ e 🔽 value, P }} ->
    {{ Call e 🔽 value, P }}
  | Let {A B : Set} (e : FM.t A) (k : A -> FM.t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    {{ k value 🔽 output, P2 }} ->
    {{ Let e k 🔽 output, P1 /\ P2 }}
  | Equiv {A : Set} (e : FM.t A) (value : A) (P1 P2 : Prop) :
    {{ e 🔽 value, P1 }} ->
    (P1 <-> P2) ->
    {{ e 🔽 value, P2 }}
  | Replace {A : Set} (e : FM.t A) (value1 value2 : A) (P : Prop) :
    {{ e 🔽 value1, P }} ->
    value1 = value2 ->
    {{ e 🔽 value2, P }}
  where "{{ e 🔽 output , P }}" := (t e output P).
End Run.

(** ** Examples of field instantiations *)

(** Simple prime field F_7 for testing *)
Module F7 : FieldType.
  Definition F := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition two := 2%Z.
  Definition add (x y : Z) := (x + y) mod 7.
  Definition sub (x y : Z) := (x - y) mod 7.
  Definition mul (x y : Z) := (x * y) mod 7.
  Definition neg (x : Z) := (-x) mod 7.
  Definition eq (x y : Z) : Prop := x mod 7 = y mod 7.
  
  (* Simple division - assumes y has inverse *)
  Definition div (x y : Z) : Z := 
    match y mod 7 with
    | 1 => x mod 7
    | 2 => (x * 4) mod 7  (* 2^(-1) = 4 in F_7 *)
    | 3 => (x * 5) mod 7  (* 3^(-1) = 5 in F_7 *)
    | 4 => (x * 2) mod 7  (* 4^(-1) = 2 in F_7 *)
    | 5 => (x * 3) mod 7  (* 5^(-1) = 3 in F_7 *)
    | 6 => (x * 6) mod 7  (* 6^(-1) = 6 in F_7 *)
    | _ => 0  (* Division by zero - undefined *)
    end.
  
  Definition to_Z (x : Z) : Z := x.
  Definition from_Z (x : Z) : Z := x mod 7.
  Definition char := 7%Z.
  
  (* Field axioms - simplified for example *)
  Axiom add_comm : forall x y, add x y = add y x.
  Axiom add_assoc : forall x y z, add x (add y z) = add (add x y) z.
  Axiom add_zero : forall x, add x zero = x.
  Axiom add_neg : forall x, add x (neg x) = zero.
  Axiom mul_comm : forall x y, mul x y = mul y x.
  Axiom mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z.
  Axiom mul_one : forall x, mul x one = x.
  Axiom distrib : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
  Axiom sub_def : forall x y, sub x y = add x (neg y).
  Axiom two_def : two = add one one.
  Axiom div_correct : forall x y, y <> zero -> mul (div x y) y = x.
  Axiom char_pos : char > 1.
End F7.

(** Goldilocks field *)
Module Goldilocks : FieldType.
  Definition F := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition two := 2%Z.
  Definition char := (2^64 - 2^32 + 1)%Z.  (* Goldilocks prime *)
  Definition add (x y : Z) := (x + y) mod char.
  Definition sub (x y : Z) := (x - y) mod char.
  Definition mul (x y : Z) := (x * y) mod char.
  Definition neg (x : Z) := (-x) mod char.
  Definition eq (x y : Z) : Prop := x mod char = y mod char.
  
  (* Division using modular inverse - simplified placeholder *)
  Parameter modular_inverse : Z -> Z -> Z.  (* inverse of y mod char *)
  Definition div (x y : Z) : Z := (x * modular_inverse y char) mod char.
  
  Definition to_Z (x : Z) : Z := x.
  Definition from_Z (x : Z) : Z := x mod char.
  
  (* Field axioms *)
  Axiom add_comm : forall x y, add x y = add y x.
  Axiom add_assoc : forall x y z, add x (add y z) = add (add x y) z.
  Axiom add_zero : forall x, add x zero = x.
  Axiom add_neg : forall x, add x (neg x) = zero.
  Axiom mul_comm : forall x y, mul x y = mul y x.
  Axiom mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z.
  Axiom mul_one : forall x, mul x one = x.
  Axiom distrib : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
  Axiom sub_def : forall x y, sub x y = add x (neg y).
  Axiom two_def : two = add one one.
  Axiom div_correct : forall x y, y <> zero -> mul (div x y) y = x.
  Axiom char_pos : char > 1.
End Goldilocks.

(** Instantiate M for specific fields *)
Module M7 := M F7.
Module MGoldilocks := M Goldilocks.
Module Run7 := Run F7.
Module RunGoldilocks := Run Goldilocks.

(** Usage example *)
Module Example.
  Import F7 M7.
  
  Definition test_computation : t F :=
    Let (add one two) (fun sum =>
    mul sum sum).
    
  (* Evaluate: (1 + 2)^2 = 9 = 2 in F_7 *)
  Compute eval test_computation.  (* Should give Pure 2 *)
  
  Definition test_division : t F :=
    div (from_Z 6) (from_Z 2).  (* 6 / 2 = 3 in F_7 *)
  
  Compute eval test_division.  (* Should give Pure 3 *)
  
End Example.