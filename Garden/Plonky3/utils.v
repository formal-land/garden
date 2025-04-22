From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From Coq Require Import Uint63 ZArith.
From mathcomp Require Import fintype.
From mathcomp Require Import fingroup.
From mathcomp Require Import ssrint.
From mathcomp Require Import ssrnum.



Definition TWO_TO_16 : N := 2 ^ 16.
Definition TWO_TO_32 : N := 2 ^ 32.

(* Define the field type using mathcomp's finite field 'F_p *)
Module Add2.

  (* Let p denote the characteristic of the finite field *)
  Parameter p : nat.
  Axiom p_prime : prime p. 
  Axiom p_large : (p > 2^17) % nat.

  (* Define the field type using mathcomp's finite field 'F_p *)
  Definition F := 'F_p.

  (* Helper functions and definitions - casting integers to field elements *)
  Definition two_16 : F := inord (TWO_TO_16).
  Definition two_32 : F := inord (TWO_TO_32).

  (* Define what it means for a value to be within 16 bits *)
  Definition in_range_16 (x : F) := (0 <= val x < TWO_TO_16) % nat.

  (* Verification function for a = b + c mod 2^32 *)
  Definition verify_add2 (a b : (F * F)) (c : (F * F)) : Prop :=
    let (a0, a1) := a in
    let (b0, b1) := b in
    let (c0, c1) := c in
    
    (* Range checks for inputs *)
    in_range_16 a0 /\ in_range_16 a1 /\
    in_range_16 b0 /\ in_range_16 b1 /\
    in_range_16 c0 /\ in_range_16 c1 /\
    
    (* Compute acc and acc_16 *)
    let acc_16 := a0 - b0 - c0 in
    let acc := acc_16 + (a1 - b1 - c1) * two_16 in
    
    (* Check conditions *)
    (acc * (acc + two_32) == 0) /\
    (acc_16 * (acc_16 + two_16) == 0).

  (* Theorem: our verification implies a = b + c mod 2^32 *)
  Theorem verify_add2_sound a b c :
    verify_add2 a b c ->
    let (a0, a1) := a in
    let (b0, b1) := b in
    let (c0, c1) := c in
    let a_val := a0 + val a1 * (TWO_TO_16) % nat in
    let b_val := val b0 + val b1 * (TWO_TO_16) % nat in
    let c_val := val c0 + val c1 * (TWO_TO_16) % nat in
    (a_val = (b_val + c_val) %% (TWO_TO_32)) % nat.
  Proof.
    admit.
  Admitted. 

  (* Theorem: if a = b + c mod 2^32, then our verification holds *)
  Theorem verify_add2_complete (a b c : F * F) : 
    (let (a0, a1) := a in
    let (b0, b1) := b in
    let (c0, c1) := c in
    let a_val := a0 + val a1 * (TWO_TO_16) % nat in
    let b_val := val b0 + val b1 * (TWO_TO_16) % nat in
    let c_val := val c0 + val c1 * (TWO_TO_16) % nat in
    (a_val = (b_val + c_val) %% (TWO_TO_32)) % nat) ->
    verify_add2 a b c.
  Proof.
    admit.
  Admitted.

End Add2.