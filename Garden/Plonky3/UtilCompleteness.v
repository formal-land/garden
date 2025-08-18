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

      assert (H_two_32 : two_32 = UnOp.from (2 ^ 32)). {
        unfold two_32.
        unfold UnOp.from.
        (* given Hp, this should be obvious. *)
        (* try to use the newly defined `mod_when_smaller` in M.v *)
        rewrite mod_when_smaller; [reflexivity | lia].
      }

      (* Now we have acc_16, acc_32, and acc in terms of a0, a1, b0, b1, res0, res1 *)

      (* We will now prove the properties of acc_16 and acc_32 *)

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

      set (acc_raw := acc_16 + 2 ^ 16 * acc_32).

      assert (Hacc : acc = UnOp.from acc_raw).
      {
        unfold acc.
        unfold acc_raw.
        unfold BinOp.add.
        unfold BinOp.mul.
        unfold UnOp.from.
        replace (Z.pow_pos 2 16) with (2 ^ 16) by reflexivity.

        rewrite Zplus_mod_idemp_r.
        rewrite Z.mul_comm.
        reflexivity.
      }

      

      (* 3. `acc = 0 (mod 2 ^ 16)` from (d3), (2), and `hp` *)
      assert (H3' : acc_raw mod (2 ^ 16) = 0).
      {
        unfold acc_raw.
        lia.
      }


      (* 4. `acc = 0 (mod P) \/ acc = -2^32 (mod P)` from (B) *)
      assert (H4' : acc mod p = 0 \/ (acc + two_32) mod p = 0).
      {
        rewrite <- (Zmod_mod (acc + two_32)).
        unfold BinOp.add in H1.
        auto.
      }

      assert (H4'' : acc_raw mod p = 0 \/ (acc_raw + 2 ^ 32) mod p = 0).
      {
        rewrite Hacc in H4'.
        unfold UnOp.from in H4'.
        rewrite Zmod_mod in H4'.
        rewrite Zplus_mod_idemp_l in H4'.
        destruct H4' as [H4a | H4b].
        (* case 1: acc mod p = 0 *)
        {
          left.
          auto.
        }
        (* case 2: acc + two_32 mod p = 0 *)
        {
          right.
          rewrite H_two_32 in H4b.
          unfold UnOp.from in H4b.
          rewrite Zplus_mod_idemp_r in H4b.
          auto.
        }
      }

      assert (Hp_coprime : Znumtheory.rel_prime (2 ^ 16) p).
      {
        (* Consider integrating some definitions from Znumtheory. *)
        (* Idea: Prime p, and p > 2 : p and any exponential of 2 should be coprime. *)
        admit.
      }

      (* 5. `acc = 0 (mod 2 ^ 16 * P) \/ acc = -2^32 (mod 2 ^ 16 * P)` by `p` and 2 are coprime, Chinese Remainder Theorem, case analysis on (4), and arithmetics (for finding the remainder solution), for detailed method of finding the solution see (here)[https://crypto.stanford.edu/pbc/notes/numbertheory/crt.html] *)
      assert (H5'' : acc_raw mod (2 ^ 16 * p) = 0 \/ (acc_raw + two_32) mod (2 ^ 16 * p) = 0).
      { 
        assert (Hp0 : p <> 0).
        {
          lia.
        }
        assert (H216 : 2 ^ 16 <> 0).
        {
          lia.
        }
        destruct H4' as [H4a | H4b].
        (* case 1: acc_raw mod p = 0 *)
        {
          left.
          assert (H4a' : acc_raw mod p = 0).
          {
            rewrite Hacc in H4a.
            unfold UnOp.from in H4a.
            rewrite Zmod_mod in H4a.
            auto.
          }
          assert (Hcrt := binary_chinese_remainder_alt (2 ^ 16) p acc_raw 0 H216 Hp0 Hp_coprime H3' H4a').
          auto.     
        }
        (* case 2: acc_raw + two_32 mod p = 0 *)
        {
          right.
          assert (Hacc_raw_2_32 : (acc_raw + 2 ^ 32) mod 2 ^ 16 = 0).
          {
            admit.
          }
          assert (H4b' : (acc_raw + two_32) mod p = 0).
          {
            rewrite Hacc in H4b.
            unfold UnOp.from in H4b.
            rewrite Zplus_mod_idemp_l in H4b.
            auto.
          }
          (* 
          Idea: 
          (acc_raw + two_32) mod (2 ^ 16 * p)
          = acc_raw mod (2 ^ 16 * p) + two_32 mod (2 ^ 16 * p)
          Given p > 2 ^ 17, 2 ^ 16 p > 2^32
          so two_32 mod (2 ^ 16 * p) = two_32
          *)
          (* assert (Hcrt := binary_chinese_remainder_alt (2 ^ 16) p (acc_raw + 2 ^ 32) 0 H216 Hp0 Hp_coprime Hacc_raw_2_32 H4b).
          rewrite <- Hcrt. *)
          admit.
        }
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
Updated New Proof:


Given the definitions:
```
- (d1) acc_16 = a[0] - b[0] - c[0] (mod p)
- (d2) acc_32 = a[1] - b[1] - c[1] (mod p)
- (d3) acc    = acc_16 + acc_32 * 2 ^ 16 (mod p)
```
The prover generates the following two constraints:
(A) acc_16 * (acc_16 + 2 ^ 16) = 0 (mod p)
(B) acc * (acc + (2 ^ 32) mod p) = 0 (mod p)

precondition:
(Hp)    p > 2 ^ 17
(Hlimb) 0 <= a_i, b_i < 2 ^ 16

following the guides in the comments:

let 
(d4) acc_16_r = a[0] - b[0] - c[0] (without mod)
(d5) acc_32_r = a[1] - b[1] - c[1]
(d6) acc_r    = a    - b    - c    (without mod)
              = acc_16_r + 2 ^ 16 * acc_32_r

(r1) - 2 ^ 17 + 2 < acc_16_r <= 2 ^ 16 - 1
(r2) - 2 ^ 33 + 2 < acc_r    <= 2 ^ 32 - 1

(0) acc_16 = 0 (mod p) \/ (acc_16 + 2 ^ 16) = 0 (mod p) from (A)
(1) acc_16_r = 0 \/ acc_16_r = - 2 ^ 16 from (0) and (Hp)
(2) acc_16_r = 0 (mod 2 ^ 16) from (1)
(3) acc = 0 (mod p) \/ (acc + (2 ^ 32) mod p) = 0 (mod p) from (B)
(4) acc = 0 (mod p) \/ acc = - 2 ^ 32 (mod p) from (3)
(5) acc_r = 0 (mod 2 ^ 16) from (2), (d6) and arithmetics
(6) acc = acc_r mod p
(7) acc_r = 0 (mod p) \/ acc_r = - 2 ^ 32 (mod p) from (4) and (7)
(8) acc_r = 0 (mod 2 ^ 16 * p) \/ acc_r = - 2 ^ 32 (mod 2 ^ 16 * p) from (crt), (5), (7)
(9) acc_r = 0 \/ acc_r = - 2 ^ 32 from (8), (hp) and (r2).
(10) a = b + c (mod 2 ^ 32)

*)