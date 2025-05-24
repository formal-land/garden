Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Uint63 ZArith.
From mathcomp Require Import ssrint.
From mathcomp Require Import ssrnum.


Require Export Lia.

Definition TWO_TO_16 : nat := 2 ^ 16.
Definition TWO_TO_32 : nat := 2 ^ 32.

Module UtilGadgets.

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
  Definition in_range_16 (x : F) := (0 <= x < TWO_TO_16) % nat.

  Module PackBitsLe.
  
  End PackBitsLe.

  (* Define the field type using mathcomp's finite field 'F_p *)
  Module Add2.

    (* Verification function for a = b + c mod 2^32 *)
    Definition verify_add2 (a b c : (F * F)): Prop :=
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
      (acc * (acc + two_32) % nat == 0) % nat /\
      (acc_16 * (acc_16 + two_16) % nat == 0) % nat.

    (* Theorem: our verification implies a = b + c mod 2^32 *)
    Theorem verify_add2_sound a b c :
      verify_add2 a b c ->
      let (a0, a1) := a in
      let (b0, b1) := b in
      let (c0, c1) := c in
      let b_val := b0 + b1 * (TWO_TO_16) % nat in
      let a_val := a0 + a1 * (TWO_TO_16) % nat in
      let c_val := c0 + c1 * (TWO_TO_16) % nat in
      (a_val = (b_val + c_val) %% (TWO_TO_32)) % nat.
    Proof.
      unfold verify_add2.
      intros H.
      destruct a as [a0 a1].
      destruct b as [b0 b1].
      destruct c as [c0 c1].
      destruct H as [Ha0 [Ha1 [Hb0 [Hb1 [Hc0 [Hc1 [Hacc Hacc16]]]]]]].

      (* 16-bit range constraints on individual parts *)
      assert (Ha0_bound: (a0 < TWO_TO_16) % nat) by apply Ha0.
      assert (Ha1_bound: (a1 < TWO_TO_16) % nat) by apply Ha1.
      assert (Hb0_bound: (b0 < TWO_TO_16) % nat) by apply Hb0.
      assert (Hb1_bound: (b1 < TWO_TO_16) % nat) by apply Hb1.
      assert (Hc0_bound: (c0 < TWO_TO_16) % nat) by apply Hc0.
      assert (Hc1_bound: (c1 < TWO_TO_16) % nat) by apply Hc1.

      (* auxiliary lemma for the 32-bit constraints *)
      assert (H32_bound : forall (x y : F), (x < TWO_TO_16) % nat /\ (y < TWO_TO_16) % nat -> (x + y * TWO_TO_16 < TWO_TO_32)  % nat ).
        intros x y.
      {
        intros [Hx Hy].
        have H32 : (TWO_TO_32 % nat = (TWO_TO_16 % nat) * (TWO_TO_16 % nat)) % nat.
        {
          unfold TWO_TO_32, TWO_TO_16.
          rewrite -(expnD 2 16 16).
          assert (H32_16 : (32 = 16 + 16)%nat) by reflexivity.
          rewrite -H32_16.
          admit.
        }
        admit.
      }

      (* 32-bit range constraints *)
      assert (Ha_bound : (a0 + a1 * TWO_TO_16 < TWO_TO_32) % nat).
      {
        apply H32_bound.
        split.
        - apply Ha0_bound.
        - apply Ha1_bound.
      }
      assert (Hb_bound : (b0 + b1 * TWO_TO_16 < TWO_TO_32) % nat).
      {
        apply H32_bound.
        split.
        - apply Hb0_bound.
        - apply Hb1_bound.
      }
      assert (Hc_bound : (c0 + c1 * TWO_TO_16 < TWO_TO_32) % nat).
      {
        apply H32_bound.
        split.
        - apply Hc0_bound.
        - apply Hc1_bound.
      }

      (* Compute the values *)
      admit.
    Admitted. 

    (* Theorem: if a = b + c mod 2^32, then our verification holds *)
    Theorem verify_add2_complete (a b c : F * F) : 
      (let (a0, a1) := a in
      let (b0, b1) := b in
      let (c0, c1) := c in
      let a_val := a0 + a1 * (TWO_TO_16) % nat in
      let b_val := b0 + b1 * (TWO_TO_16) % nat in
      let c_val := c0 + c1 * (TWO_TO_16) % nat in
      (a_val = (b_val + c_val) %% (TWO_TO_32)) % nat) ->
      verify_add2 a b c.
    Proof.
      admit.
    Admitted.

  End Add2.

  Module Add3.
    (* Verification function for `a = b + c + d mod 2^32` *)
    Definition verify_add3 (a b c d : (F * F)): Prop := 
      let (a0, a1) := a in
      let (b0, b1) := b in
      let (c0, c1) := c in
      let (d0, d1) := d in
      
      (* Range checks for inputs *)
      in_range_16 a0 /\ in_range_16 a1 /\
      in_range_16 b0 /\ in_range_16 b1 /\
      in_range_16 c0 /\ in_range_16 c1 /\
      in_range_16 d0 /\ in_range_16 d1 /\

      (* Compute acc and acc_16 *)
      let acc_16 := a0 - b0 - c0 - d0 in
      let acc := acc_16 + (a1 - b1 - c1 - d1) * two_16 in
      
      (* Check conditions *)
      (* acc*(acc + 2^32)*(acc + 2*2^32) = 0. *)
      (acc * (acc + two_32) * (acc + two_32 * 2) % nat == 0) % nat /\
      (* acc_16*(acc_16 + 2^16)*(acc_16 + 2*2^16) = 0. *)
      (acc_16 * (acc_16 + two_16) * (acc_16 + 2 * two_16) % nat == 0) % nat.
    
    Theorem verify_add3_sound a b c d :
      verify_add3 a b c d ->
      let (a0, a1) := a in
      let (b0, b1) := b in
      let (c0, c1) := c in
      let (d0, d1) := d in
      let b_val := b0 + b1 * (TWO_TO_16) % nat in
      let a_val := a0 + a1 * (TWO_TO_16) % nat in
      let c_val := c0 + c1 * (TWO_TO_16) % nat in
      let d_val := d0 + d1 * (TWO_TO_16) % nat in
      (a_val = (b_val + c_val + d_val) %% (TWO_TO_32)) % nat.
    Proof.
    Admitted.

    Theorem verify_add3_complete (a b c d : F * F):
      (let (a0, a1) := a in
      let (b0, b1) := b in
      let (c0, c1) := c in
      let (d0, d1) := d in
      let a_val := a0 + a1 * (TWO_TO_16) % nat in
      let b_val := b0 + b1 * (TWO_TO_16) % nat in
      let c_val := c0 + c1 * (TWO_TO_16) % nat in
      let d_val := d0 + d1 * (TWO_TO_16) % nat in
      (a_val = (b_val + c_val + d_val) %% (TWO_TO_32)) % nat) ->
      verify_add3 a b c d.
    Proof.
    Admitted.
  End Add3.

  (* 
  Pack a collection of bits into a number 
  Given `vec = [v_0, v_1, ..., v_n]` returns `v_0 + 2v_1 + ... + 2^n v_n`
  *)


  Module Xor_32_shift.
  End Xor_32_shift.


End UtilGadgets.