Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope char_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

(** Field-based monad for a specific field type F *)
Module Type FieldType.
  Parameter F : Set.
  Parameter zero : F.
  Parameter one : F.
  Parameter add : F -> F -> F.
  Parameter sub : F -> F -> F.
  Parameter mul : F -> F -> F.
  Parameter neg : F -> F.
  Parameter eq : F -> F -> Prop.
  
  (* Conversion functions *)
  Parameter to_Z : F -> Z.
  Parameter from_Z : Z -> F.
  Parameter char : Z.  (* field characteristic *)
  
  (* Axioms ensuring proper field behavior *)
  Axiom to_from_Z : forall x, to_Z (from_Z x) = x mod char.
  Axiom from_to_Z : forall x, from_Z (to_Z x) = x.
  Axiom char_pos : char > 1.
End FieldType.

Module FieldUnOp (Field : FieldType).
  Import Field.
  
  Inductive t : Set -> Set -> Set :=
  | Neg : t F F
  .

  Definition eval {A B : Set} (op : t A B) : A -> B :=
    match op in t A B return A -> B with
    | Neg => neg
    end.
End FieldUnOp.

Module FieldBinOp (Field : FieldType).
  Import Field.
  
  Inductive t : Set -> Set -> Set -> Set :=
  | Add : t F F F
  | Sub : t F F F
  | Mul : t F F F
  .

  Definition eval {A B C : Set} (op : t A B C) : A -> B -> C :=
    match op in t A B C return A -> B -> C with
    | Add => add
    | Sub => sub
    | Mul => mul
    end.
End FieldBinOp.

Module FieldM (Field : FieldType).
  Import Field.
  Module FUnOp := FieldUnOp Field.
  Module FBinOp := FieldBinOp Field.
  
  (** Field monad mimicking M.v structure *)
  Inductive t : Set -> Set :=
  | Pure {A : Set} (value : A) : t A
  | UnOp {A B : Set} (op : FUnOp.t A B) (x : A) : t B
  | BinOp {A B C : Set} (op : FBinOp.t A B C) (x1 : A) (x2 : B) : t C
  | Equal (x1 x2 : F) : t unit
  | Unwrap {A : Set} (value : option A) : t A
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

  Definition neg_op (x : F) : t F :=
    UnOp FUnOp.Neg x.

  Definition add_op (x y : F) : t F :=
    BinOp FBinOp.Add x y.

  Definition sub_op (x y : F) : t F :=
    BinOp FBinOp.Sub x y.

  Definition mul_op (x y : F) : t F :=
    BinOp FBinOp.Mul x y.

  Definition equal_op (x y : F) : t unit :=
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
  
  (** Field-based array *)
  Record FieldArray (n : nat) := {
    field_value : list F;
    field_length : List.length field_value = n;
  }.
  Arguments FieldArray : clear implicits.
  
  Definition field_get {n : nat} (arr : FieldArray n) (i : nat) : t F :=
    Unwrap (List.nth_error (field_value n arr) i).
  
  (** Constants *)
  Definition two : F := add one one.
  
  (** Power function *)
  Fixpoint power (x : F) (n : nat) : F :=
    match n with
    | O => one
    | S n' => mul x (power x n')
    end.
  
  Definition pow2 (n : nat) : F := power two n.
  
  (** Assert operations *)
  Definition assert_zero (x : F) : t unit := Equal x zero.
  
  Fixpoint assert_zeros (l : list F) : t unit :=
    match l with
    | [] => Pure tt
    | x :: l' => Let (assert_zero x) (fun _ => assert_zeros l')
    end.
  
  Definition assert_bool (x : F) : t unit := 
    Let (mul_op x x) (fun square_x => equal_op x square_x).
      
  Fixpoint assert_bools (l : list F) : t unit :=
    match l with
    | [] => Pure tt
    | x :: l' => Let (assert_bool x) (fun _ => assert_bools l')
    end.
      
  (** Field-based add2 circuit *)
  Definition field_add2 (a b c : FieldArray 2) : t unit :=
    let two_16 := pow2 16 in
    let two_32 := pow2 32 in
    
    Let (field_get a 0) (fun a0 =>
    Let (field_get a 1) (fun a1 =>
    Let (field_get b 0) (fun b0 =>
    Let (field_get b 1) (fun b1 =>
    Let (field_get c 0) (fun c0 =>
    Let (field_get c 1) (fun c1 =>
    
    (* acc_16 = a[0] - b[0] - c[0] *)
    Let (sub_op a0 b0) (fun temp1 =>
    Let (sub_op temp1 c0) (fun acc_16 =>
    
    (* acc_32 = a[1] - b[1] - c[1] *)  
    Let (sub_op a1 b1) (fun temp2 =>
    Let (sub_op temp2 c1) (fun acc_32 =>
    
    (* acc = acc_16 + acc_32 * 2^16 *)
    Let (mul_op acc_32 two_16) (fun acc_32_shifted =>
    Let (add_op acc_16 acc_32_shifted) (fun acc =>
    
    (* First constraint: acc * (acc + 2^32) = 0 *)
    Let (add_op acc two_32) (fun acc_plus_two32 =>
    Let (mul_op acc acc_plus_two32) (fun constraint1 =>
    
    (* Second constraint: acc_16 * (acc_16 + 2^16) = 0 *)
    Let (add_op acc_16 two_16) (fun acc16_plus_two16 =>
    Let (mul_op acc_16 acc16_plus_two16) (fun constraint2 =>
    
    assert_zeros [constraint1; constraint2]
    )))))))))))))))).
End FieldM.

(** Notations need to be defined within each field instance since FieldM is a functor *)
(** Example usage:
    Module F7M := FieldM F7.
    Import F7M.
    Notation "'let*' x ':=' e 'in' k" := (Let e (fun x => k)) (at level 200).
*)

Module FieldRun (Field : FieldType).
  Module FM := FieldM Field.
  Import Field FM.
  
  Reserved Notation "{{ e ==> output , P }}".
  
  Inductive run : forall {A : Set}, FM.t A -> A -> Prop -> Prop :=
  | Pure {A : Set} (value : A) :
    {{ Pure value ==> value, True }}
  | Equal (x1 x2 : F) :
    {{ Equal x1 x2 ==> tt, eq x1 x2 }}
  | Unwrap {A : Set} (value : A) :
    {{ Unwrap (Some value) ==> value, True }}
  | Call {A : Set} (e : t A) (value : A) (P : Prop) :
    {{ e ==> value, P }} ->
    {{ Call e ==> value, P }}
  | Let {A B : Set} (e : t A) (k : A -> t B) (value : A) (output : B) (P1 P2 : Prop) :
    {{ e ==> value, P1 }} ->
    {{ k value ==> output, P2 }} ->
    {{ Let e k ==> output, P1 /\ P2 }}
  | Equiv {A : Set} (e : t A) (value : A) (P1 P2 : Prop) :
    {{ e ==> value, P1 }} ->
    (P1 <-> P2) ->
    {{ e ==> value, P2 }}
  | Replace {A : Set} (e : t A) (value1 value2 : A) (P : Prop) :
    {{ e ==> value1, P }} ->
    value1 = value2 ->
    {{ e ==> value2, P }}
  where "{{ e ==> output , P }}" := (run e output P).
End FieldRun.

Module FieldCompleteness (Field : FieldType).
  Module FR := FieldRun Field.
  Module FM := FieldM Field.
  Import Field FM FR.
  
  (** Range predicates using built-in conversion *)
  Definition is_16_bit (x : F) : Prop := 0 <= to_Z x < 2^16.
  Definition is_32_bit (x : F) : Prop := 0 <= to_Z x < 2^32.
  
  (** Field-based completeness for add2 *)
  Definition field_add2_completeness : Prop :=
    forall (a0 a1 b0 b1 c0 c1 : F),
      is_16_bit a0 -> is_16_bit a1 ->
      is_16_bit b0 -> is_16_bit b1 ->
      is_16_bit c0 -> is_16_bit c1 ->
      (* Field arithmetic relation *)
      let a_val := to_Z a0 + 2^16 * to_Z a1 in
      let b_val := to_Z b0 + 2^16 * to_Z b1 in
      let c_val := to_Z c0 + 2^16 * to_Z c1 in
      a_val = (b_val + c_val) mod 2^32 ->
      (* Circuit evaluation succeeds *)
      {{ FM.eval (FM.field_add2 
          {| FM.field_value := [a0; a1]; FM.field_length := eq_refl |}
          {| FM.field_value := [b0; b1]; FM.field_length := eq_refl |}  
          {| FM.field_value := [c0; c1]; FM.field_length := eq_refl |}) ==> tt, True }}.
  
  (** General template *)
  Definition circuit_completeness_template 
    {InputType : Type}
    (circuit : InputType -> FM.t unit)
    (input_valid : InputType -> Prop)
    (arithmetic_relation : InputType -> Prop) : Prop :=
    forall (input : InputType),
      input_valid input ->
      arithmetic_relation input ->
      {{ FM.eval (circuit input) ==> tt, True }}.
End FieldCompleteness.

(** ** Examples of Concrete Fields *)

(** Small prime field F_7 *)
Module F7 : FieldType.
  Definition F := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add (x y : Z) := (x + y) mod 7.
  Definition sub (x y : Z) := (x - y) mod 7.
  Definition mul (x y : Z) := (x * y) mod 7.
  Definition neg (x : Z) := (-x) mod 7.
  Definition eq (x y : Z) : Prop := x mod 7 = y mod 7.
  
  (* Conversion functions *)
  Definition to_Z (x : Z) : Z := x.
  Definition from_Z (x : Z) : Z := x mod 7.
  Definition char := 7%Z.
  
  (* Axioms *)
  Axiom to_from_Z : forall x, to_Z (from_Z x) = x mod char.
  Axiom from_to_Z : forall x, from_Z (to_Z x) = x.
  Axiom char_pos : char > 1.
End F7.

(** Generic prime field F_p *)
Module Type PrimeSpec.
  Parameter p : Z.
  Axiom p_prime : forall n : Z, 1 < n < p -> ~(n | p).  (* simple primality *)
  Axiom p_pos : p > 1.
End PrimeSpec.

Module FP (P : PrimeSpec) : FieldType.
  Import P.
  Definition F := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add (x y : Z) := (x + y) mod p.
  Definition sub (x y : Z) := (x - y) mod p.
  Definition mul (x y : Z) := (x * y) mod p.
  Definition neg (x : Z) := (-x) mod p.
  Definition eq (x y : Z) : Prop := x mod p = y mod p.
  
  (* Conversion functions *)
  Definition to_Z (x : Z) : Z := x.
  Definition from_Z (x : Z) : Z := x mod p.
  Definition char := p.
  
  (* Axioms *)
  Axiom to_from_Z : forall x, to_Z (from_Z x) = x mod char.
  Axiom from_to_Z : forall x, from_Z (to_Z x) = x.
  Axiom char_pos : char > 1.
End FP.

(** Large prime for Plonky3 (example: Goldilocks field) *)
Module Goldilocks : PrimeSpec.
  Definition p := (2^64 - 2^32 + 1)%Z.  (* 0xFFFFFFFF00000001 *)
  Axiom p_prime : forall n : Z, 1 < n < p -> ~(n | p).
  Axiom p_pos : p > 1.
End Goldilocks.

Module GoldilocksField := FP Goldilocks.

(** Baby Bear field (another common choice) *)
Module BabyBear : PrimeSpec.
  Definition p := (15 * 2^27 + 1)%Z.  (* 2013265921 *)
  Axiom p_prime : forall n : Z, 1 < n < p -> ~(n | p).
  Axiom p_pos : p > 1.
End BabyBear.

Module BabyBearField := FP BabyBear.

(** Usage Examples *)

(** Instantiate field monad for F_7 *)
Module F7M := FieldM F7.
Module F7R := FieldRun F7.
Module F7C := FieldCompleteness F7.

(** Instantiate for Goldilocks *)
Module GoldilocksM := FieldM GoldilocksField.
Module GoldilocksR := FieldRun GoldilocksField.
Module GoldilocksC := FieldCompleteness GoldilocksField.

(** The generic completeness template works directly with the built-in to_Z conversion *)

(** Extensible to other field representations *)

(** Alternative: Use a record type for better encapsulation *)
Module Type FieldTypeAlt.
  Parameter F : Set.
  Record FieldOps := {
    zero : F;
    one : F;
    add : F -> F -> F;
    sub : F -> F -> F;
    mul : F -> F -> F;
    neg : F -> F;
    eq : F -> F -> Prop;
    (* Additional operations for verification *)
    to_Z : F -> Z;
    from_Z : Z -> F;
    char : Z;  (* characteristic *)
  }.
  Parameter ops : FieldOps.
End FieldTypeAlt.