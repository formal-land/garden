(** * Rust primitive types, copied from rocq-of-rust

    Data-only transcription of the integer, array, result, vector, and
    lens types used by [rocq-of-rust] simulations. The [Link]/[φ]/[Value]
    layer of that project is omitted: this file is the single local copy
    of those primitives, not a vendor of the whole development.

    Provenance (rocq-of-rust [main]):
    - [IntegerKind], wrapping width: [RocqOfRust/M.v]
    - [Integer.t] and the [u8]/[usize]/… aliases: [RocqOfRust/links/M.v]
    - [ArrayEmpty]/[ArrayPair]/[ArrayPairs]/[Array.t]: [RocqOfRust/core/links/array.v]
    - [Result.t]: [RocqOfRust/core/links/result.v] ([Ok]/[Err] constructors)

    [usize]/[isize] are 64-bit, matching that model's pointer width. *)

Require Export Stdlib.ZArith.ZArith.
Require Export Stdlib.Lists.List.
Require Export Stdlib.Bool.Bool.

Import List.ListNotations.
Global Set Primitive Projections.
Global Open Scope Z_scope.
Global Open Scope list_scope.

Module Default.
  Class C (A : Set) : Set := {
    default : A;
  }.

  Global Instance Z_default : C Z := { default := 0 }.
  Global Instance Bool_default : C bool := { default := false }.
  Global Instance List_default (A : Set) : C (list A) := { default := [] }.
  Global Instance Option_default (A : Set) : C (option A) := { default := None }.
End Default.

(** ** Integer kinds and wrapping machine integers *)

Module IntegerKind.
  Inductive t : Set :=
  | I8 | I16 | I32 | I64 | I128 | Isize
  | U8 | U16 | U32 | U64 | U128 | Usize.

  Definition eqb (k1 k2 : t) : bool :=
    match k1, k2 with
    | I8, I8 | I16, I16 | I32, I32 | I64, I64 | I128, I128 | Isize, Isize
    | U8, U8 | U16, U16 | U32, U32 | U64, U64 | U128, U128 | Usize, Usize => true
    | _, _ => false
    end.

  Definition bit_size (kind : t) : Z :=
    match kind with
    | I8 | U8 => 8
    | I16 | U16 => 16
    | I32 | U32 => 32
    | I64 | U64 | Isize | Usize => 64
    | I128 | U128 => 128
    end.

  Definition is_signed (kind : t) : bool :=
    match kind with
    | I8 | I16 | I32 | I64 | I128 | Isize => true
    | U8 | U16 | U32 | U64 | U128 | Usize => false
    end.

  Definition modulus (kind : t) : Z := 2 ^ bit_size kind.

  Definition min (kind : t) : Z :=
    if is_signed kind then - (2 ^ (bit_size kind - 1)) else 0.

  Definition max (kind : t) : Z :=
    if is_signed kind then 2 ^ (bit_size kind - 1) - 1 else modulus kind - 1.

  (** Two's-complement wrap of [z] into the range of [kind]. *)
  Definition normalize_wrap (kind : t) (z : Z) : Z :=
    let m := modulus kind in
    let r := z mod m in
    if is_signed kind then
      if r >=? 2 ^ (bit_size kind - 1) then r - m else r
    else r.
End IntegerKind.

Module Integer.
  Record t {kind : IntegerKind.t} : Set := {
    value : Z;
  }.
  Arguments t : clear implicits.

  Definition make (kind : IntegerKind.t) (z : Z) : t kind :=
    {| value := IntegerKind.normalize_wrap kind z |}.

  Definition wrap {kind : IntegerKind.t} (x : t kind) : t kind :=
    make kind x.(value).

  Definition add {kind : IntegerKind.t} (x y : t kind) : t kind :=
    make kind (x.(value) + y.(value)).

  Definition sub {kind : IntegerKind.t} (x y : t kind) : t kind :=
    make kind (x.(value) - y.(value)).

  Definition mul {kind : IntegerKind.t} (x y : t kind) : t kind :=
    make kind (x.(value) * y.(value)).

  Definition eqb {kind : IntegerKind.t} (x y : t kind) : bool :=
    x.(value) =? y.(value).

  Definition ltb {kind : IntegerKind.t} (x y : t kind) : bool :=
    x.(value) <? y.(value).

  Definition leb {kind : IntegerKind.t} (x y : t kind) : bool :=
    x.(value) <=? y.(value).

  Definition to_Z {kind : IntegerKind.t} (x : t kind) : Z := x.(value).

  Definition of_nat (kind : IntegerKind.t) (n : nat) : t kind :=
    make kind (Z.of_nat n).

  Definition to_nat {kind : IntegerKind.t} (x : t kind) : nat :=
    Z.to_nat x.(value).

  Global Instance default {kind : IntegerKind.t} : Default.C (t kind) := {
    default := make kind 0;
  }.
End Integer.

Definition u8 : Set := Integer.t IntegerKind.U8.
Definition u16 : Set := Integer.t IntegerKind.U16.
Definition u32 : Set := Integer.t IntegerKind.U32.
Definition u64 : Set := Integer.t IntegerKind.U64.
Definition u128 : Set := Integer.t IntegerKind.U128.
Definition usize : Set := Integer.t IntegerKind.Usize.
Definition i8 : Set := Integer.t IntegerKind.I8.
Definition i16 : Set := Integer.t IntegerKind.I16.
Definition i32 : Set := Integer.t IntegerKind.I32.
Definition i64 : Set := Integer.t IntegerKind.I64.
Definition i128 : Set := Integer.t IntegerKind.I128.
Definition isize : Set := Integer.t IntegerKind.Isize.

Definition u8_of (z : Z) : u8 := Integer.make IntegerKind.U8 z.
Definition u32_of (z : Z) : u32 := Integer.make IntegerKind.U32 z.
Definition u64_of (z : Z) : u64 := Integer.make IntegerKind.U64 z.
Definition usize_of (z : Z) : usize := Integer.make IntegerKind.Usize z.
Definition i32_of (z : Z) : i32 := Integer.make IntegerKind.I32 z.

(** ** [Result<T, E>] *)

Module Result.
  Inductive t (T E : Set) : Set :=
  | Ok : T -> t T E
  | Err : E -> t T E.
  Arguments Ok {_ _}.
  Arguments Err {_ _}.

  Definition map {T U E : Set} (f : T -> U) (r : t T E) : t U E :=
    match r with
    | Ok x => Ok (f x)
    | Err e => Err e
    end.

  Definition map_err {T E F : Set} (f : E -> F) (r : t T E) : t T F :=
    match r with
    | Ok x => Ok x
    | Err e => Err (f e)
    end.

  Definition and_then {T U E : Set} (f : T -> t U E) (r : t T E) : t U E :=
    match r with
    | Ok x => f x
    | Err e => Err e
    end.

  Definition is_ok {T E : Set} (r : t T E) : bool :=
    match r with
    | Ok _ => true
    | Err _ => false
    end.

  Definition unwrap_or {T E : Set} (r : t T E) (default : T) : T :=
    match r with
    | Ok x => x
    | Err _ => default
    end.
End Result.

Notation "'ok" := Result.Ok (at level 0).
Notation "'err" := Result.Err (at level 0).

(** ** Nested-pair arrays [[T; N]] *)

Module ArrayEmpty.
  Inductive t : Set := Make.
End ArrayEmpty.

Module ArrayPair.
  Record t {A B : Set} : Set := {
    x : A;
    xs : B;
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_ _}.
End ArrayPair.

Module ArrayPairs.
  Fixpoint t (A : Set) (length : nat) : Set :=
    match length with
    | O => ArrayEmpty.t
    | S n => ArrayPair.t A (t A n)
    end.

  Fixpoint of_list {A : Set} (xs : list A) : t A (List.length xs) :=
    match xs with
    | [] => ArrayEmpty.Make
    | x :: xs => {| ArrayPair.x := x; ArrayPair.xs := of_list xs |}
    end.

  Fixpoint to_list {A : Set} {length : nat} (xs : t A length) : list A :=
    match length, xs with
    | O, _ => []
    | S length, p => p.(ArrayPair.x) :: to_list p.(ArrayPair.xs)
    end.

  Fixpoint repeat {A : Set} (value : A) (length : nat) : t A length :=
    match length with
    | O => ArrayEmpty.Make
    | S n => {| ArrayPair.x := value; ArrayPair.xs := repeat value n |}
    end.

  Fixpoint nth_error {A : Set} {length : nat} (xs : t A length) (index : nat) : option A :=
    match index, length, xs with
    | _, O, _ => None
    | O, S _, p => Some p.(ArrayPair.x)
    | S index, S _, p => nth_error p.(ArrayPair.xs) index
    end.

  Fixpoint replace_at {A : Set} {length : nat} (xs : t A length) (index : nat) (value : A) :
      option (t A length) :=
    match index, length, xs with
    | _, O, _ => None
    | O, S _, p => Some {| ArrayPair.x := value; ArrayPair.xs := p.(ArrayPair.xs) |}
    | S index, S _, p =>
      match replace_at p.(ArrayPair.xs) index value with
      | Some xs' => Some {| ArrayPair.x := p.(ArrayPair.x); ArrayPair.xs := xs' |}
      | None => None
      end
    end.
End ArrayPairs.

Module Array.
  Record t {A : Set} {length : usize} : Set := {
    value : ArrayPairs.t A (Z.to_nat length.(Integer.value));
  }.
  Arguments t : clear implicits.

  Definition of_pairs {A : Set} (length : usize) (value : ArrayPairs.t A (Z.to_nat length.(Integer.value))) :
      t A length :=
    {| value := value |}.

  Definition repeat {A : Set} (length : usize) (x : A) : t A length :=
    {| value := ArrayPairs.repeat x (Z.to_nat length.(Integer.value)) |}.

  Definition nth {A : Set} {length : usize} (xs : t A length) (index : usize) : option A :=
    ArrayPairs.nth_error xs.(value) (Integer.to_nat index).

  Definition replace_at {A : Set} {length : usize} (xs : t A length) (index : usize) (v : A) :
      option (t A length) :=
    match ArrayPairs.replace_at xs.(value) (Integer.to_nat index) v with
    | Some value => Some {| value := value |}
    | None => None
    end.

  Definition to_list {A : Set} {length : usize} (xs : t A length) : list A :=
    ArrayPairs.to_list xs.(value).

  Global Instance default (A : Set) (length : usize) `{Default.C A} : Default.C (t A length) := {
    default := repeat length Default.default;
  }.
End Array.

(** ** [Vec<T>] as a Coq list *)

Module Vec.
  Definition t (A : Set) : Set := list A.

  Definition new {A : Set} : t A := [].

  Definition len {A : Set} (v : t A) : usize :=
    usize_of (Z.of_nat (List.length v)).

  Definition push {A : Set} (v : t A) (x : A) : t A :=
    v ++ [x].

  Definition nth {A : Set} `{Default.C A} (v : t A) (index : usize) : A :=
    List.nth (Integer.to_nat index) v Default.default.

  Definition nth_error {A : Set} (v : t A) (index : usize) : option A :=
    List.nth_error v (Integer.to_nat index).

  Definition replace_at {A : Set} (v : t A) (index : usize) (x : A) : t A :=
    List.firstn (Integer.to_nat index) v ++ x :: List.skipn (S (Integer.to_nat index)) v.

  Definition of_list {A : Set} (l : list A) : t A := l.

  Definition to_list {A : Set} (v : t A) : list A := v.

  Definition repeat {A : Set} (n : usize) (x : A) : t A :=
    List.repeat x (Integer.to_nat n).

  Definition is_empty {A : Set} (v : t A) : bool :=
    match v with
    | [] => true
    | _ => false
    end.
End Vec.

(** ** Lenses for [ &mut ] focuses *)

Module Lens.
  Record t (A B : Set) : Set := {
    get : A -> B;
    set : B -> A -> A;
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_ _}.
  Arguments get {_ _}.
  Arguments set {_ _}.

  Definition id (A : Set) : t A A := {|
    get := fun a => a;
    set := fun b _ => b;
  |}.

  Definition compose {A B C : Set} (outer : t A B) (inner : t B C) : t A C := {|
    get := fun a => inner.(get) (outer.(get) a);
    set := fun c a => outer.(set) (inner.(set) c (outer.(get) a)) a;
  |}.

  Definition modify {A B : Set} (l : t A B) (f : B -> B) (a : A) : A :=
    l.(set) (f (l.(get) a)) a.

  Definition vec_nth {A : Set} `{Default.C A} (index : usize) : t (Vec.t A) A := {|
    get := fun v => Vec.nth v index;
    set := fun x v => Vec.replace_at v index x;
  |}.
End Lens.

Module PrimitiveTests.
  Lemma u8_wrapping_add : Integer.add (u8_of 255) (u8_of 1) = u8_of 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma u8_wrapping_sub : Integer.sub (u8_of 0) (u8_of 1) = u8_of 255.
  Proof. vm_compute. reflexivity. Qed.

  Lemma i8_wrapping_add : Integer.add (Integer.make IntegerKind.I8 127) (Integer.make IntegerKind.I8 1)
    = Integer.make IntegerKind.I8 (-128).
  Proof. vm_compute. reflexivity. Qed.

  Lemma result_and_then_ok :
    Result.and_then (E := unit) (fun x : Z => Result.Ok (x + 1)) (Result.Ok 3)
      = Result.Ok 4.
  Proof. reflexivity. Qed.

  Lemma array_nth_replace :
    let a := Array.of_pairs (usize_of 3)
      (ArrayPairs.of_list [u8_of 1; u8_of 2; u8_of 3]) in
    match Array.replace_at a (usize_of 1) (u8_of 9) with
    | Some a' => Array.nth a' (usize_of 1)
    | None => None
    end = Some (u8_of 9).
  Proof. vm_compute. reflexivity. Qed.

  Lemma vec_push_nth :
    Vec.nth (A := Z) (Vec.push (Vec.push Vec.new 10) 20) (usize_of 1) = 20.
  Proof. vm_compute. reflexivity. Qed.

  Lemma lens_vec_nth :
    let l := Lens.vec_nth (A := Z) (usize_of 0) in
    l.(Lens.get) (l.(Lens.set) 7 [1; 2; 3]) = 7.
  Proof. vm_compute. reflexivity. Qed.
End PrimitiveTests.
