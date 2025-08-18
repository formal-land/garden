Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.Util.
Require Import Coq.omega.PreOmega.

(* TODO: these are to be declared as shared constants / methods, copied from blake3/constants.v *)
Definition BITS_PER_LIMB : Z := 16.
Definition U32_LIMBS : Z := 32 / BITS_PER_LIMB.

Definition double_val (val1 val2 : Z) : Array.t Z 2 :=
  {| Array.get i := 
        match i with
        | 0 => val1
        | 1 => val2
        | _ => 0 (* Default case, should not happen *)
        end
  |}.

Definition pack_16_limbs (bits : Array.t Z U32_LIMBS) : Z :=
    bits.(Array.get) 0 + bits.(Array.get) 1 * (2 ^ BITS_PER_LIMB).

Definition unpack_16_limbs (value : Z) : Array.t Z U32_LIMBS :=
  {| Array.get i := 
        match i with
        | 0 => value mod (2 ^ BITS_PER_LIMB)
        | 1 => value / (2 ^ BITS_PER_LIMB)
        | _ => 0 (* Default case, should not happen *)
        end
  |}.


Module Add2Proof.
    Definition eval_add2 {p} `{Prime p} (a b : Array.t Z U32_LIMBS) : Array.t Z U32_LIMBS :=
        unpack_16_limbs (BinOp.add (pack_16_limbs a) (pack_16_limbs b)).
    
    Lemma implies {p} `{Prime p} (result a b : Array.t Z U32_LIMBS) :
      (* let result := M.map_mod result in
      let a := M.map_mod a in
      let b := M.map_mod b in *)
      p > 2 ^ 17 ->
      {{ add2 result a b 🔽
        tt,
        Array.Eq.t (eval_add2 a b) result
      }}.
    Proof.
      cbn.
      intros Hp.
      cbn.
      eapply Run.LetAccumulate. {
        constructor.
      }
      intros H1.
      simpl in H1.
      set (a0 := a.(Array.get) 0) in H1.
      set (a1 := a.(Array.get) 1) in H1.
      set (b0 := b.(Array.get) 0) in H1.
      set (b1 := b.(Array.get) 1) in H1.
      set (res0 := result.(Array.get) 0) in H1.
      set (res1 := result.(Array.get) 1) in H1.

      eapply Run.LetAccumulate. {
        constructor.
      }
      intros H2.
      fold a0 a1 b0 b1 res0 res1 in H2.

      
      (* d1 *)
      set (acc_16 := BinOp.sub (BinOp.sub res0 a0) b0) in H1, H2.
      (* d2 *)
      set (acc_32 := BinOp.sub (BinOp.sub res1 a1) b1) in H1.
      (* d3 *)
      set (acc := BinOp.add acc_16 (BinOp.mul acc_32 (Z.pow_pos 2 16))) in H1.
      set (two_32 := BinOp.mul (UnOp.from (Z.pow_pos 2 16)) (UnOp.from (Z.pow_pos 2 16))) in H1.

      set (two_16 := UnOp.from (2 ^ 16)) in H2.

      assert (H_two_16 : two_16 = 2 ^ 16). {
        unfold two_16.
        unfold UnOp.from.
        (* given Hp, this should be obvious. *)
        (* try to use the newly defined `mod_when_smaller` in M.v *)
        rewrite mod_when_smaller; [reflexivity | lia].
      }

      rewrite H_two_16 in H2.

      assert (Hacc_16 : 0 <= acc_16 < 2 ^ 16). {
        admit.
      }

      assert (Hacc_32 : 0 <= acc_32 < 2 ^ 16). {
        admit.
      }

      (* Now we have acc_16 and acc_32 in the range [0, 2^16) *)
      (* We can now rewrite H1 and H2 to use these definitions *)

      rewrite mul_zero_implies_zero in H1, H2.

      (* now we want to remove the UnOp.from in H1. *)
      
      unfold UnOp.from in H1.

      (* given p > 131072 = 2 ^17, and acc_16 < 2 ^ 16, this should be obvious. *)

      (* 1. `acc_16 = 0 \/ acc_16 = -2 ^ 16` from (A), `hp`, and (0). *)

      assert (H1' : acc_16 = 0 \/ (acc_16 + 2 ^ 16) = 0).
      {
        destruct H2 as [H2a | H2b].
        (* case 1: acc_16 = 0  (mod p) *)
        {
          left.
          unfold UnOp.from in H2a.
          rewrite mod_when_smaller in H2a; [|lia].
          auto.
        }
        (* case 2 : acc_16 + 2 ^ 16 = 0 (mod p) *)
        {
          right.
          rewrite FieldRewrite.from_add in H2b.
          unfold BinOp.add in H2b.
          rewrite mod_when_smaller in H2b; [|lia].
          auto.
        }
      }

      (* 2. `acc_16 = 0 (mod 2 ^ 16)` from (1) *)
      assert (H2' : acc_16 mod (2 ^ 16) = 0).
      {
        lia.
      }

      (* 3. `acc = 0 (mod 2 ^ 16)` from (d3), (2), and `hp` *)
      assert (H3' : acc mod (2 ^ 16) = 0).
      {
        unfold acc.
        unfold BinOp.add.
        unfold BinOp.mul.
        admit.
      }


      (* 4. `acc = 0 (mod P) \/ acc = -2^32 (mod P)` from (B) *)
      assert (H4' : acc mod p = 0 \/ (acc + two_32) mod p = 0).
      {
        admit.
      }

      (* 5. `acc = 0 (mod 2 ^ 16 * P) \/ acc = -2^32 (mod 2 ^ 16 * P)` by `p` and 2 are coprime, Chinese Remainder Theorem, case analysis on (4), and arithmetics (for finding the remainder solution), for detailed method of finding the solution see (here)[https://crypto.stanford.edu/pbc/notes/numbertheory/crt.html] *)
      assert (H5' : acc mod (2 ^ 16 * p) = 0 \/ (acc + two_32) mod (2 ^ 16 * p) = 0).
      { 
        unfold acc.
        admit.
      }

      (* 6. `acc = result - a - b` (definition) *)

      (* 7. No overflow can occur on `acc mod 2^16 P` as `2^16 P > 2^33` and `result, a, b < 2^32`, by (5) and (6) *)

      (* 8. Hence `acc = 0 \/ acc = -2^32` from (5) and (7) *)
      assert (H8' : acc = 0 \/ (acc + 2 ^ 32) = 0).
      {
        unfold acc.
        admit.
      }

      (* 9. `acc = 0 (mod 2 ^ 32)` from (8) and definition of `mod` *)
      assert (H9' : acc mod (2 ^ 32) = 0).
      {
        admit.
      }

      (* 10. `result - a - b = 0 (mod 2 ^ 32)` from definition of `acc` *)

      (* helper *)
      assert (Htmp : Array.Eq.t (eval_add2 a b) result).
      {
        unfold eval_add2.
        unfold Array.Eq.t.
        intros i.
        unfold U32_LIMBS.
        unfold BITS_PER_LIMB.
        intros Hi.
        assert (i = 0 \/ i = 1) as [Hi0 | Hi1].
        {
          (* should be lia *)
          admit.
        }
        unfold pack_16_limbs;
        fold a0 a1 b0 b1;
        unfold unpack_16_limbs.
        (* i = 0*)
        {
          rewrite Hi0.
          fold res0.
          simpl.
          admit.
        }
        (* i = 1 *)
        {
          rewrite Hi1.
          fold res1.
          simpl.
          admit.
        }
      }


      eapply Run.Implies. {
        repeat constructor.
      }

      easy.
      
    Admitted.
End Add2Proof.



(*
# Proof Sketches for `add2`

We will begin with one of the most fundamental ideas: `add2`.

## Inputs and Preconditions

- `p`: the prime characteristic of our finite field, such that
	- `IsPrime p` (referred to as `hp`)
    - `p > 2 ^ 17` (otherwise `panic`)
- `a b c`: our inputs given as `2, 16` bit limbs (e.g. `a = a[0] + 2^16 a[1]`)
	- each `16` bit limb has been range checked to ensure it contains a value in `[0, 2^16)`.

## In-House Definitions
- `acc_16 = a[0] - b[0] - c[0] (mod p)`.   (d1)
- `acc' = acc_16 + 2 ^ 16 * acc_32`.            (d2)
- `acc  = acc_16 + 2 ^ 16 * acc_32 (mod p) = acc' mod p` (d3)

## Desired Output

The desired property `a = b + c (mod 2 ^ 32)`, which is to say, `a[0] + 2 ^ 16 a[1] = (b[0] + c[0] + 2 ^ 16 b[1] + 2 ^ 16 c[1]) mod (2 ^ 32)`

Will hold if and only if the following conditions are satisfied: (they are the constraints that will be generated and checked by Plonky3)
- A. `acc_16 * (acc_16 + 2 ^ 16) = 0 (mod p)`.
- B. `acc * (acc + 2 ^ 32) = 0 (mod p)`.        

## The proof:
0. `acc_16 = 0 (mod p) \/ acc_16 = -2 ^ 16 (mod p)` from (A)
1. `acc_16 = 0 \/ acc_16 = -2 ^ 16` from `hp`, and (0).
2. `acc_16 = 0 (mod 2 ^ 16)` from (1)
3. `acc'  = 0 (mod 2 ^ 16)` from (d3), (2), and `hp`
4. `acc'  = 0 (mod P) \/ acc' = -2^32 (mod P)` from (B)
5. `acc' = 0 (mod 2 ^ 16 * P) \/ acc' = -2^32 (mod 2 ^ 16 * P)` by `p` and 2 are coprime, Chinese Remainder Theorem, case analysis on (4), and arithmetics (for finding the remainder solution), for detailed method of finding the solution see (here)[https://crypto.stanford.edu/pbc/notes/numbertheory/crt.html]
6. `acc' = a - b - c` (definition)
7. No overflow can occur on `acc' mod 2^16 P` as `2^16 P > 2^33` and `a, b, c < 2^32`, by (5) and (6)
8. Hence `acc' = 0 \/ acc' = -2^32` from (5) and (7)
9. `acc' = 0 (mod 2 ^ 32)` from (8) and definition of `mod`
10. `a - b - c = 0 (mod 2 ^ 32)` from definition of `acc'`.
*)

