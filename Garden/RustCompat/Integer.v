(** * Fixed-width Rust integer operations

    Rocq-of-rust represents every Rust integer kind by a tagged record whose
    payload is [Z].  The record constructor does not enforce the range of its
    tag.  This module supplies the boundary checks and the named arithmetic
    operations used by hand-written, executable translations.

    The [usize] and [isize] tags denote the 64-bit target used by the Orchard
    implementation snapshots.  Callers use [of_Z_checked] for parsed or
    externally supplied values.  Wrapping operations normalize their result;
    checked operations return [None] for overflow. *)

From Stdlib Require Import Bool.Bool ZArith.ZArith.
Require Import RocqOfRust.lib.lib.
Require Import RocqOfRust.links.M.

Local Open Scope Z_scope.

Module Kind := RocqOfRust.M.IntegerKind.

(** Forward the raw carrier definitions instead of aliasing rocq-of-rust's
    complete linked-integer module.  Such an alias would make OCaml extraction
    retain simulation-only [Link]/[Ty] instances, including abstract Rust type
    paths that the verifier never evaluates. *)
Module Raw.
  Definition t (kind : Kind.t) : Set :=
    RocqOfRust.links.M.Integer.t kind.

  Definition value {kind : Kind.t} (x : t kind) : Z :=
    RocqOfRust.links.M.Integer.value x.
End Raw.

Module Semantics := RocqOfRust.lib.lib.Integer.

Definition t (kind : Kind.t) : Set := Raw.t kind.

Definition value {kind : Kind.t} (x : t kind) : Z := Raw.value x.

Definition of_Z_unchecked (kind : Kind.t) (z : Z) : t kind :=
  RocqOfRust.links.M.Integer.Build_t kind z.

Definition valid_Z (kind : Kind.t) (z : Z) : Prop :=
  Semantics.min kind <= z <= Semantics.max kind.

Definition valid {kind : Kind.t} (x : t kind) : Prop :=
  valid_Z kind (value x).

Definition validb_Z (kind : Kind.t) (z : Z) : bool :=
  Z.leb (Semantics.min kind) z && Z.leb z (Semantics.max kind).

Definition validb {kind : Kind.t} (x : t kind) : bool :=
  validb_Z kind (value x).

Definition of_Z_checked (kind : Kind.t) (z : Z) : option (t kind) :=
  match Semantics.normalize_option kind z with
  | Some z => Some (of_Z_unchecked kind z)
  | None => None
  end.

Definition of_Z_wrapping (kind : Kind.t) (z : Z) : t kind :=
  of_Z_unchecked kind (Semantics.normalize_wrap kind z).

Definition of_Z_saturating (kind : Kind.t) (z : Z) : t kind :=
  of_Z_unchecked kind (Semantics.normalize_saturating kind z).

Lemma validb_Z_spec (kind : Kind.t) (z : Z) :
  validb_Z kind z = true <-> valid_Z kind z.
Proof.
  unfold validb_Z, valid_Z.
  rewrite Bool.andb_true_iff, !Z.leb_le.
  reflexivity.
Qed.

Lemma of_Z_checked_some (kind : Kind.t) (z : Z) (x : t kind) :
  of_Z_checked kind z = Some x -> value x = z /\ valid x.
Proof.
  unfold of_Z_checked, Semantics.normalize_option.
  destruct (z <? Semantics.min kind) eqn:Hmin; [discriminate |].
  destruct (Semantics.max kind <? z) eqn:Hmax; [discriminate |].
  intro H.
  inversion H; subst x; clear H.
  split; [reflexivity |].
  unfold valid, valid_Z, value; cbn.
  apply Z.ltb_ge in Hmin.
  apply Z.ltb_ge in Hmax.
  lia.
Qed.

Lemma of_Z_wrapping_valid (kind : Kind.t) (z : Z) :
  valid (of_Z_wrapping kind z).
Proof.
  destruct kind;
    unfold valid, valid_Z, value, of_Z_wrapping, of_Z_unchecked;
    unfold Semantics.min, Semantics.max, Semantics.normalize_wrap;
    cbn.
  all:
    match goal with
    | |- context [Z.modulo ?dividend ?modulus] =>
        assert (Hmodulus : 0 < modulus) by (vm_compute; reflexivity);
        pose proof (Z.mod_pos_bound dividend modulus Hmodulus) as Hmod;
        lia
    end.
Qed.

Lemma kind_bounds_ordered (kind : Kind.t) :
  Semantics.min kind <= Semantics.max kind.
Proof.
  destruct kind; unfold Semantics.min, Semantics.max; cbn; lia.
Qed.

Lemma of_Z_saturating_valid (kind : Kind.t) (z : Z) :
  valid (of_Z_saturating kind z).
Proof.
  unfold valid, valid_Z, value, of_Z_saturating, of_Z_unchecked.
  cbn.
  unfold Semantics.normalize_saturating.
  destruct (z <? Semantics.min kind) eqn:Hmin.
  - split; [reflexivity | apply kind_bounds_ordered].
  - apply Z.ltb_ge in Hmin.
    destruct (Semantics.max kind <? z) eqn:Hmax.
    + split; [apply kind_bounds_ordered | reflexivity].
    + apply Z.ltb_ge in Hmax.
      lia.
Qed.

Definition wrapping_unary {kind : Kind.t} (op : Z -> Z) (x : t kind) :
    t kind :=
  of_Z_wrapping kind (op (value x)).

Definition checked_unary {kind : Kind.t} (op : Z -> Z) (x : t kind) :
    option (t kind) :=
  of_Z_checked kind (op (value x)).

Definition saturating_unary {kind : Kind.t} (op : Z -> Z) (x : t kind) :
    t kind :=
  of_Z_saturating kind (op (value x)).

Definition wrapping_binary {kind : Kind.t} (op : Z -> Z -> Z)
    (left right : t kind) : t kind :=
  of_Z_wrapping kind (op (value left) (value right)).

Definition checked_binary {kind : Kind.t} (op : Z -> Z -> Z)
    (left right : t kind) : option (t kind) :=
  of_Z_checked kind (op (value left) (value right)).

Definition saturating_binary {kind : Kind.t} (op : Z -> Z -> Z)
    (left right : t kind) : t kind :=
  of_Z_saturating kind (op (value left) (value right)).

Definition wrapping_neg {kind : Kind.t} : t kind -> t kind :=
  wrapping_unary Z.opp.
Definition checked_neg {kind : Kind.t} : t kind -> option (t kind) :=
  checked_unary Z.opp.
Definition saturating_neg {kind : Kind.t} : t kind -> t kind :=
  saturating_unary Z.opp.

Definition wrapping_add {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.add.
Definition wrapping_sub {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.sub.
Definition wrapping_mul {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.mul.

Definition checked_add {kind : Kind.t} : t kind -> t kind -> option (t kind) :=
  checked_binary Z.add.
Definition checked_sub {kind : Kind.t} : t kind -> t kind -> option (t kind) :=
  checked_binary Z.sub.
Definition checked_mul {kind : Kind.t} : t kind -> t kind -> option (t kind) :=
  checked_binary Z.mul.

Definition saturating_add {kind : Kind.t} : t kind -> t kind -> t kind :=
  saturating_binary Z.add.
Definition saturating_sub {kind : Kind.t} : t kind -> t kind -> t kind :=
  saturating_binary Z.sub.
Definition saturating_mul {kind : Kind.t} : t kind -> t kind -> t kind :=
  saturating_binary Z.mul.

(** [Z.quot] truncates toward zero, matching Rust signed division.  This is
    distinct from [Z.div], which is the operation used by rocq-of-rust's
    generic release-mode binary operator. *)
Definition checked_div {kind : Kind.t} (left right : t kind) :
    option (t kind) :=
  if Z.eqb (value right) 0 then
    None
  else
    of_Z_checked kind (Z.quot (value left) (value right)).

Definition checked_rem {kind : Kind.t} (left right : t kind) :
    option (t kind) :=
  if Z.eqb (value right) 0 then
    None
  else
    match of_Z_checked kind (Z.quot (value left) (value right)) with
    | None => None
    | Some _ => of_Z_checked kind (Z.rem (value left) (value right))
    end.

(** Rust's named wrapping division and remainder still reject a zero divisor,
    so their executable result carries an [option]. *)
Definition wrapping_div {kind : Kind.t} (left right : t kind) :
    option (t kind) :=
  if Z.eqb (value right) 0 then
    None
  else
    Some (of_Z_wrapping kind (Z.quot (value left) (value right))).

Definition wrapping_rem {kind : Kind.t} (left right : t kind) :
    option (t kind) :=
  if Z.eqb (value right) 0 then
    None
  else
    Some (of_Z_wrapping kind (Z.rem (value left) (value right))).

Definition bit_width (kind : Kind.t) : Z :=
  match kind with
  | Kind.I8 | Kind.U8 => 8
  | Kind.I16 | Kind.U16 => 16
  | Kind.I32 | Kind.U32 => 32
  | Kind.I64 | Kind.U64 | Kind.Isize | Kind.Usize => 64
  | Kind.I128 | Kind.U128 => 128
  end.

Definition checked_shl {kind : Kind.t} (x : t kind) (amount : Z) :
    option (t kind) :=
  if (amount <? 0) || (bit_width kind <=? amount) then
    None
  else
    Some (of_Z_wrapping kind (Z.shiftl (value x) amount)).

Definition checked_shr {kind : Kind.t} (x : t kind) (amount : Z) :
    option (t kind) :=
  if (amount <? 0) || (bit_width kind <=? amount) then
    None
  else
    Some (of_Z_wrapping kind (Z.shiftr (value x) amount)).

Definition wrapping_shl {kind : Kind.t} (x : t kind) (amount : Z) : t kind :=
  of_Z_wrapping kind
    (Z.shiftl (value x) (Z.modulo amount (bit_width kind))).

Definition wrapping_shr {kind : Kind.t} (x : t kind) (amount : Z) : t kind :=
  of_Z_wrapping kind
    (Z.shiftr (value x) (Z.modulo amount (bit_width kind))).

Definition wrapping_bitand {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.land.
Definition wrapping_bitor {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.lor.
Definition wrapping_bitxor {kind : Kind.t} : t kind -> t kind -> t kind :=
  wrapping_binary Z.lxor.
Definition wrapping_not {kind : Kind.t} : t kind -> t kind :=
  wrapping_unary Z.lnot.

Definition cast_wrapping {source target : Kind.t} (x : t source) : t target :=
  of_Z_wrapping target (value x).

Definition eqb {kind : Kind.t} (left right : t kind) : bool :=
  Z.eqb (value left) (value right).
Definition ltb {kind : Kind.t} (left right : t kind) : bool :=
  Z.ltb (value left) (value right).
Definition leb {kind : Kind.t} (left right : t kind) : bool :=
  Z.leb (value left) (value right).

Definition usize_t : Set := t Kind.Usize.
Definition usize_bits : Z := 64.
Definition usize_max : Z := 2 ^ usize_bits - 1.
Definition usize_of_Z : Z -> option usize_t := of_Z_checked Kind.Usize.
Definition usize_of_Z_wrapping : Z -> usize_t := of_Z_wrapping Kind.Usize.
Definition usize_of_nat (n : nat) : option usize_t :=
  usize_of_Z (Z.of_nat n).

Lemma usize_bounds :
  Semantics.min Kind.Usize = 0 /\
  Semantics.max Kind.Usize = usize_max.
Proof. split; reflexivity. Qed.

Goal value (wrapping_add
    (of_Z_wrapping Kind.U8 255) (of_Z_wrapping Kind.U8 1)) = 0.
Proof. vm_compute. reflexivity. Qed.

Goal checked_add
    (of_Z_wrapping Kind.U8 255) (of_Z_wrapping Kind.U8 1) = None.
Proof. vm_compute. reflexivity. Qed.

Goal option_map value (checked_div
    (of_Z_wrapping Kind.I32 (-5)) (of_Z_wrapping Kind.I32 2)) = Some (-2).
Proof. vm_compute. reflexivity. Qed.

Goal checked_div
    (of_Z_wrapping Kind.I8 (-128)) (of_Z_wrapping Kind.I8 (-1)) = None.
Proof. vm_compute. reflexivity. Qed.

Goal option_map value (wrapping_div
    (of_Z_wrapping Kind.I8 (-128)) (of_Z_wrapping Kind.I8 (-1))) =
  Some (-128).
Proof. vm_compute. reflexivity. Qed.

Goal option_map value (usize_of_Z (2 ^ 64 - 1)) = Some (2 ^ 64 - 1).
Proof. vm_compute. reflexivity. Qed.

Goal usize_of_Z (2 ^ 64) = None.
Proof. vm_compute. reflexivity. Qed.

Goal value (wrapping_shl (of_Z_wrapping Kind.U8 1) 8) = 1.
Proof. vm_compute. reflexivity. Qed.
