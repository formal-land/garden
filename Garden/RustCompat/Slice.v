(** * Executable Rust slice compatibility

    Rocq-of-rust represents a Rust slice by a Rocq list.  This module retains
    that representation and exposes bounds-aware operations.  Every operation
    taking a Rust [usize] rejects an invalid raw integer, and out-of-bounds
    reads or writes return [None] rather than acquiring a default value. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.ZArith.
Require Import Garden.RustCompat.Integer.

Import ListNotations.
Local Open Scope Z_scope.

Module UInt := Garden.RustCompat.Integer.

Definition t (A : Type) : Type := list A.

Definition length_Z {A : Type} (xs : t A) : Z :=
  Z.of_nat (List.length xs).

Definition length_fits_usize {A : Type} (xs : t A) : Prop :=
  UInt.valid_Z UInt.Kind.Usize (length_Z xs).

Definition len_checked {A : Type} (xs : t A) : option UInt.usize_t :=
  UInt.usize_of_nat (List.length xs).

Definition get {A : Type} (xs : t A) (index : UInt.usize_t) : option A :=
  if UInt.validb index then
    List.nth_error xs (Z.to_nat (UInt.value index))
  else
    None.

Fixpoint replace_at_nat {A : Type} (xs : list A) (index : nat) (x : A) :
    option (list A) :=
  match xs, index with
  | [], _ => None
  | _ :: xs, O => Some (x :: xs)
  | y :: xs, S index =>
      match replace_at_nat xs index x with
      | Some xs => Some (y :: xs)
      | None => None
      end
  end.

Definition set {A : Type} (xs : t A) (index : UInt.usize_t) (x : A) :
    option (t A) :=
  if UInt.validb index then
    replace_at_nat xs (Z.to_nat (UInt.value index)) x
  else
    None.

Definition split_at {A : Type} (xs : t A) (index : UInt.usize_t) :
    option (t A * t A) :=
  if UInt.validb index then
    let n := Z.to_nat (UInt.value index) in
    if Nat.leb n (List.length xs) then
      Some (List.firstn n xs, List.skipn n xs)
    else
      None
  else
    None.

Definition exact_length {A : Type} (expected : UInt.usize_t) (xs : list A) :
    option (t A) :=
  if UInt.validb expected && Z.eqb (UInt.value expected) (length_Z xs) then
    Some xs
  else
    None.

Lemma replace_at_nat_length {A : Type} (xs ys : list A) (index : nat) (x : A) :
  replace_at_nat xs index x = Some ys ->
  List.length ys = List.length xs.
Proof.
  revert ys index.
  induction xs as [|y xs IH]; intros ys [|index] H; cbn in H;
    try discriminate.
  - inversion H; reflexivity.
  - destruct (replace_at_nat xs index x) as [updated|] eqn:Hupdated;
      try discriminate.
    inversion H; subst ys; cbn.
    f_equal.
    eapply IH; eassumption.
Qed.

Lemma set_length {A : Type} (xs ys : t A) (index : UInt.usize_t) (x : A) :
  set xs index x = Some ys ->
  List.length ys = List.length xs.
Proof.
  unfold set.
  destruct (UInt.validb index); [apply replace_at_nat_length | discriminate].
Qed.

Goal get [10; 20; 30]%Z (UInt.usize_of_Z_wrapping 1) = Some 20%Z.
Proof. vm_compute. reflexivity. Qed.

Goal get [10; 20; 30]%Z (UInt.usize_of_Z_wrapping 3) = None.
Proof. vm_compute. reflexivity. Qed.

Goal get [10; 20; 30]%Z
    (UInt.of_Z_unchecked UInt.Kind.Usize (-1)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal set [10; 20; 30]%Z (UInt.usize_of_Z_wrapping 1) 99%Z =
  Some [10; 99; 30]%Z.
Proof. vm_compute. reflexivity. Qed.

Goal split_at [10; 20; 30]%Z (UInt.usize_of_Z_wrapping 2) =
  Some ([10; 20]%Z, [30]%Z).
Proof. vm_compute. reflexivity. Qed.
