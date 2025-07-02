(*
  https://github.com/formal-land/garden/issues/29

  Time-stamp: <2025-07-02 15:30:26 adhithsanjay>

  The goal of this .v file is to prove that the verifier
  is not overconstrained.
 *)

Require Import Nat ZArith Bool Lia.
Require Import Garden.Plonky3.MLessEffects.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.
Require Import Garden.Plonky3.keccak.round_flags.

(* Restricted column type. *)
Print KeccakCols.t.
(*
  Record t : Set := Build_t
  { step_flags : Array.t Z NUM_ROUNDS;
    export : Z;
    preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    c : Array.t (Array.t Z 64) 5;
    c_prime : Array.t (Array.t Z 64) 5;
    a_prime : Array.t (Array.t (Array.t Z 64) 5) 5;
    a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a_prime_prime_0_0_bits : Array.t Z 64;
    a_prime_prime_prime_0_0_limbs : Array.t Z U64_LIMBS }.
 *)

Print NUM_ROUNDS.
(* NUM_ROUNDS = 24 *)
Print U64_LIMBS.
(* U64_LIMBS = 64 / BITS_PER_LIMB *)

(* No invalid states. *)
Module PreKeccakCols.
  Record t := {
    step_flags : Array.t bool NUM_ROUNDS;
    export : bool;
    preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    c : Array.t (Array.t bool 64) 5;
    c_prime : Array.t (Array.t bool 64) 5;
    a_prime : Array.t (Array.t (Array.t bool 64) 5) 5;
    a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    a_prime_prime_0_0_bits : Array.t bool 64;
    a_prime_prime_prime_0_0_limbs : Array.t Z U64_LIMBS
    }.
(*
  TODO: Conversion function from PreKeccakCols.t -> KeccakCols.t
*)
End PreKeccakCols.  
  
  















