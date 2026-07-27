Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Poseidon hash specification

    This module folds the per-round arithmetic proved deterministic in
    [pow5_proof.v] ([FullRound.output], [PartialRound.output],
    [PadAndAdd.output]) into the full P128Pow5T3 permutation and a
    fixed-length-2 sponge hash [poseidon_hash2 : Z -> Z -> Z].

    The fold mirrors the circuit's [permutation_rows]
    ([p128pow5t3_synthesis.v]): four full rounds (0..3), twenty-eight
    partial-round *pairs* (rounds 4..59), four full rounds (60..63).  The
    definition tracks the circuit's own computation structure (the
    "internal soundness" reading); the circuit-to-math bridge
    (composing [FullRound.deterministic] / [PartialRound.deterministic] /
    [PadAndAdd.deterministic] along the permute region rows) is the
    soundness obligation discharged at the [Orchard/circuit_proof/main.v] level,
    where the Poseidon synthesis region is in scope.

    Protocol reference: §5.4.1.10 'PoseidonHash Function' of the Zcash
    protocol specification — the Poseidon permutation
    over [F_qP³] with S-box [x ↦ x⁵], [R_F = 8] full rounds and [R_P = 56]
    partial rounds, used as a sponge with rate 2 / capacity 1 in
    Constant-Input-Length mode.  The MDS matrix and round constants
    ([p128pow5t3.v]) are the Grain-generated parameters of the Poseidon
    reference implementation, transcribed from the vendored Rust crate. *)

Module Poseidon.
  Definition rc (round column : nat) : Z :=
    p128pow5t3.round_constant round column.

  (** One full round: substitution box on all three lanes, then MDS mix. *)
  Definition apply_full (round : nat) (s : State.t) : State.t :=
    FullRound.output
      s.(State.x0) s.(State.x1) s.(State.x2)
      (rc round 0) (rc round 1) (rc round 2).

  (** One pair of partial rounds (the circuit packs two per row): substitution
      box on lane 0 only, MDS mix, twice. *)
  Definition apply_partial (round_a round_b : nat) (s : State.t) : State.t :=
    PartialRound.output
      s.(State.x0) s.(State.x1) s.(State.x2)
      (rc round_a 0) (rc round_a 1) (rc round_a 2)
      (rc round_b 0) (rc round_b 1) (rc round_b 2).

  (** The full P128Pow5T3 permutation: 8 full rounds split around 56 partial
      rounds, exactly the schedule of [p128pow5t3_synthesis.permutation_rows]. *)
  Definition permute (s : State.t) : State.t :=
    let s := apply_full 0 s in
    let s := apply_full 1 s in
    let s := apply_full 2 s in
    let s := apply_full 3 s in
    let s := apply_partial 4 5 s in
    let s := apply_partial 6 7 s in
    let s := apply_partial 8 9 s in
    let s := apply_partial 10 11 s in
    let s := apply_partial 12 13 s in
    let s := apply_partial 14 15 s in
    let s := apply_partial 16 17 s in
    let s := apply_partial 18 19 s in
    let s := apply_partial 20 21 s in
    let s := apply_partial 22 23 s in
    let s := apply_partial 24 25 s in
    let s := apply_partial 26 27 s in
    let s := apply_partial 28 29 s in
    let s := apply_partial 30 31 s in
    let s := apply_partial 32 33 s in
    let s := apply_partial 34 35 s in
    let s := apply_partial 36 37 s in
    let s := apply_partial 38 39 s in
    let s := apply_partial 40 41 s in
    let s := apply_partial 42 43 s in
    let s := apply_partial 44 45 s in
    let s := apply_partial 46 47 s in
    let s := apply_partial 48 49 s in
    let s := apply_partial 50 51 s in
    let s := apply_partial 52 53 s in
    let s := apply_partial 54 55 s in
    let s := apply_partial 56 57 s in
    let s := apply_partial 58 59 s in
    let s := apply_full 60 s in
    let s := apply_full 61 s in
    let s := apply_full 62 s in
    let s := apply_full 63 s in
    s.

  (** Domain initial-capacity element for [ConstantLength<2>]: the rate-position
      lane is seeded with [(L as u128) << 64] = [2 * 2^64] before absorbing.
      Protocol: §5.4.1.10 — "for a 2-element input, the initial value of the
      capacity element is 2⁶⁵". *)
  Definition domain_iv_constant_length_2 : Z :=
    2 * 2 ^ 64.

  (** The two-input fixed-length Poseidon hash used by the Orchard nullifier PRF:
      absorb [x], [y] into the rate lanes of the freshly-seeded state, run the
      permutation, squeeze the first rate lane.

      Protocol: §5.4.1.10, [PoseidonHash(x, y) = f([x, y, 2⁶⁵])₁]; §5.4.2
      instantiates the nullifier PRF as
      [PRF^nfOrchard_nk(ρ) = PoseidonHash(nk, ρ)]. *)
  Definition poseidon_hash2 (x y : Z) : Z :=
    (permute {|
      State.x0 := x;
      State.x1 := y;
      State.x2 := domain_iv_constant_length_2;
    |}).(State.x0).

  (** Sanity: the hash is exactly the squeezed lane of the permuted seeded
      state — definitional, kept as a regression guard on the absorb wiring. *)
  Lemma poseidon_hash2_unfold (x y : Z) :
    poseidon_hash2 x y =
      (permute {|
        State.x0 := x;
        State.x1 := y;
        State.x2 := domain_iv_constant_length_2;
      |}).(State.x0).
  Proof. reflexivity. Qed.
End Poseidon.
