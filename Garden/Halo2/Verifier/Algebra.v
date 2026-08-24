(** * Executable scalar algebra used by the Halo2 verifier model

    Halo2's Orchard verifier uses the Vesta scalar field, whose modulus is
    [Primes.pallas_p].  Values in this module are plain [Z]s, but every public
    arithmetic operation returns a canonical residue.  Keeping the modulus
    explicit here is important: Rust's integer counters are modelled elsewhere;
    these operations are field operations and therefore never use machine-word
    wraparound. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Field.Field.

Import ListNotations.
Local Open Scope Z_scope.

Module VerifierField.

Definition t : Type := Z.
Definition modulus : Z := Primes.pallas_p.

Definition canon (x : Z) : t := x mod modulus.
Definition zero : t := 0.
Definition one : t := 1.
Definition add (x y : t) : t := canon (x + y).
Definition sub (x y : t) : t := canon (x - y).
Definition mul (x y : t) : t := canon (x * y).
Definition opp (x : t) : t := canon (-x).
Definition square (x : t) : t := mul x x.
Definition eqb (x y : t) : bool := Z.eqb (canon x) (canon y).
Definition is_zero (x : t) : bool := eqb x zero.

Fixpoint pow_nat (x : t) (n : nat) : t :=
  match n with
  | O => one
  | S n' => mul x (pow_nat x n')
  end.

(** Extended Euclid is the same executable inverse already certified by
    [Garden.Field.Div].  [None] records the two Rust [unwrap] panic sites that
    attempt to invert zero. *)
Definition invert (x : t) : option t :=
  if is_zero x then None else Some (mod_inverse (canon x) modulus).

Definition div (x y : t) : option t :=
  match invert y with
  | Some y_inv => Some (mul x y_inv)
  | None => None
  end.

Fixpoint powers_from (x current : t) (fuel : nat) : list t :=
  match fuel with
  | O => []
  | S fuel' => current :: powers_from x (mul current x) fuel'
  end.

Definition powers (x : t) (fuel : nat) : list t :=
  powers_from x one fuel.

Definition sum (xs : list t) : t := fold_left add xs zero.
Definition product (xs : list t) : t := fold_left mul xs one.

(** Halo2 folds gate, permutation, and lookup expressions from left to right:
    [acc <- acc * challenge + value]. *)
Definition compress (challenge : t) (xs : list t) : t :=
  fold_left (fun acc x => add (mul acc challenge) x) xs zero.

Definition eval_polynomial (coefficients : list t) (x : t) : t :=
  fold_right (fun coefficient acc => add coefficient (mul x acc)) zero
    coefficients.

Fixpoint replace_nth {A : Type} (index : nat) (value : A) (xs : list A) :
    option (list A) :=
  match index, xs with
  | O, _ :: tail => Some (value :: tail)
  | S index', head :: tail =>
      match replace_nth index' value tail with
      | Some tail' => Some (head :: tail')
      | None => None
      end
  | _, _ => None
  end.

Fixpoint repeat_scalar (x : t) (n : nat) : list t :=
  match n with O => [] | S n' => x :: repeat_scalar x n' end.

Lemma canon_zero : canon 0 = zero.
Proof. vm_compute. reflexivity. Qed.

Lemma powers_length (x : t) (n : nat) : List.length (powers x n) = n.
Proof.
  unfold powers. generalize one. induction n; intros; cbn; auto.
Qed.

End VerifierField.
