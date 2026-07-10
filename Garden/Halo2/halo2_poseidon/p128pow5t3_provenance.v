(** * P128Pow5T3 constants provenance

    In-kernel derivation checks for the trusted Poseidon literals of
    [p128pow5t3.v] and the [inv_two_pow_*] field constants of
    [ecc/chip/constants.v]:

    - the 64 x 3 [round_constants] equal the rejection-sampled output of
      the Grain LFSR seeded at [(SboxType::Pow, t = 3, R_F = 8, R_P = 56)]
      over the Pallas base field ([grain.rs] / [lib.rs]
      [generate_constants]);
    - [mds] equals the Cauchy matrix [1/(x_i + y_j)] built from the next
      six non-rejection samples of the same Grain state at secure-MDS
      index 0, and [mds_inv] its Lagrange-polynomial inverse ([mds.rs]
      [generate_mds]);
    - [mds * mds_inv] is the identity matrix over the field;
    - each [inv_two_pow_n] equals [2^{-n} mod pallas_p].

    Every checker is a raw [forallb]/[Z.eqb] boolean term closed by a
    single [vm_compute]; the derivation runs entirely inside the kernel
    (the [derived] pipeline is recomputed by each checker).  The fuel
    values cover the concrete run with slack: the run's longest
    self-shrinking gap is 18 discarded pairs, its worst rejection chain is
    8 attempts, and the MDS sampling loop exits on its first iteration. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.halo2_poseidon.grain.
Require Import Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.constants.

Import ListNotations.

Global Open Scope Z_scope.

(** [F::NUM_BITS] of the Pallas base field. *)
Definition pallas_num_bits : Z := 255.

(** Fuel bounds for the three unbounded loops (see the header note). *)
Definition bit_fuel : nat := 64.
Definition attempt_fuel : nat := 32.
Definition loop_fuel : nat := 4.

(** The full generation pipeline at the P128Pow5T3 parameters, taken from
    [p128pow5t3.v]'s own [width]/[full_rounds]/[partial_rounds], with
    secure-MDS index 0 (the [P128Pow5T3Gen::<F, 0>] instantiation that
    [p128pow5t3.rs] verifies the literals against). *)
Definition derived :
    option (list (list Z) * (list (list Z) * list (list Z))) :=
  Generation.generate_constants loop_fuel attempt_fuel bit_fuel 0
    (Z.of_nat width) (Z.of_nat full_rounds) (Z.of_nat partial_rounds)
    pallas_num_bits Primes.pallas_p.

(** Projections out of [derived] go through [option_get]/[option_map] so
    that no [match] takes the concrete [derived] as its syntactic
    scrutinee: elaborating such a [match] sends the whole generation
    pipeline to the lazy conversion machine (a multi-minute stall), while
    these applications stay unreduced until the checkers' [vm_compute]. *)
Definition option_get {A : Type} (default : A) (o : option A) : A :=
  match o with
  | Some x => x
  | None => default
  end.

Definition derived_round_constants : list (list Z) :=
  option_get [] (option_map fst derived).

Definition derived_mds : list (list Z) :=
  option_get [] (option_map (fun r => fst (snd r)) derived).

Definition derived_mds_inv : list (list Z) :=
  option_get [] (option_map (fun r => snd (snd r)) derived).

(** (a) The Grain-derived round constants equal the [round_constants]
    literal, entry by entry, and the derived matrix has the literal's
    64 x 3 shape (so the derivation did not run out of fuel). *)
Lemma round_constants_check :
  Nat.eqb (List.length derived_round_constants)
    (full_rounds + partial_rounds)
  && List.forallb
       (fun r =>
         Nat.eqb (List.length (nth r derived_round_constants [])) width
         && List.forallb
              (fun c =>
                Z.eqb (get derived_round_constants r c) (round_constant r c))
              (List.seq 0 width))
       (List.seq 0 (full_rounds + partial_rounds)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** (b) The derived Cauchy matrix equals the [mds] literal. *)
Lemma mds_check :
  Nat.eqb (List.length derived_mds) width
  && List.forallb
       (fun i =>
         Nat.eqb (List.length (nth i derived_mds [])) width
         && List.forallb
              (fun j => Z.eqb (get derived_mds i j) (mds_coeff i j))
              (List.seq 0 width))
       (List.seq 0 width) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** (b') The derived Lagrange inverse equals the [mds_inv] literal. *)
Lemma mds_inv_check :
  Nat.eqb (List.length derived_mds_inv) width
  && List.forallb
       (fun i =>
         Nat.eqb (List.length (nth i derived_mds_inv [])) width
         && List.forallb
              (fun j => Z.eqb (get derived_mds_inv i j) (mds_inv_coeff i j))
              (List.seq 0 width))
       (List.seq 0 width) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** (c) The two literals are mutually inverse over the field:
    [mds * mds_inv = I]. *)
Lemma mds_times_mds_inv_check :
  List.forallb
    (fun i =>
      List.forallb
        (fun j =>
          Z.eqb
            (List.fold_left
              (fun acc k =>
                (acc + mds_coeff i k * mds_inv_coeff k j)
                  mod Primes.pallas_p)
              (List.seq 0 width)
              0)
            (if Nat.eqb i j then 1 else 0))
        (List.seq 0 width))
    (List.seq 0 width) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** (d) Each [inv_two_pow_n] literal of [ecc/chip/constants.v] is the
    reduced inverse of [2^n] modulo [pallas_p]. *)
Lemma inv_two_pow_check :
  List.forallb
    (fun '(n, c) => Z.eqb c (mod_inverse (2 ^ n) Primes.pallas_p))
    [(4, inv_two_pow_4); (5, inv_two_pow_5); (6, inv_two_pow_6);
     (8, inv_two_pow_8); (9, inv_two_pow_9)] = true.
Proof.
  vm_compute; reflexivity.
Qed.
