Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.Util.
Require Import Coq.omega.PreOmega.
Require Import Coqtail.Arith.Zeqm.

(* TODO: these are to be declared as shared constants / methods, copied from blake3/constants.v *)
Definition BITS_PER_LIMB : Z := 16.
Definition U32_LIMBS : Z := 32 / BITS_PER_LIMB.

Definition double_val (val1 val2 : Z) : Array.t Z 2 :=
  {| Array.get i := 
       if i =? 0 then val1
       else if i =? 1 then val2
       else 0 (* Default case, should not happen *)
  |}.

Definition pack_16_limbs (bits : Array.t Z U32_LIMBS) : Z :=
    bits.(Array.get) 0 + bits.(Array.get) 1 * (2 ^ BITS_PER_LIMB).

Definition unpack_16_limbs (value : Z) : Array.t Z U32_LIMBS := 
  double_val (value mod (2 ^ BITS_PER_LIMB)) (value / (2 ^ BITS_PER_LIMB)).

Lemma large_prime_coprime_exp_of_2 {p} `{Prime p} : 2 < p -> Znumtheory.rel_prime (2 ^ 16) p.
Proof.
Admitted.

Module RangeCheck32.
  Record t (x : Array.t Z U32_LIMBS) : Prop := {
    first : 0 <= x.(Array.get) 0 < 2 ^ 16;
    second : 0 <= x.(Array.get) 1 < 2 ^ 16;
  }.
End RangeCheck32.


Lemma int_upper (x y : Z) : x < y <-> x <= y - 1.
Proof.
  lia.
Qed.  

(* helper for add2 and add3 *)
Module AddProofUtil.
  Lemma array_index_range_U32 (i : Z) : 0 <= i < U32_LIMBS -> i = 0 \/ i = 1.
  Proof.
    cbn; lia.
  Qed.

  Lemma p_times_2_exp_16 {x : Z} (p : Z) (Hx : x > 0) (Hp : x < p) : 2 ^ 16 * p > 2 ^ 16 * x.
  Proof.
    nia.
  Qed.

  Lemma constant_unwrap {p} `{Prime p} (x : Z) : x > 0 -> p > x -> UnOp.from x = x.
  Proof.
    intros Hx Hp.
    unfold UnOp.from.
    apply Zmod_small.
    lia.
  Qed.

  Lemma compound_range_check (x y a b c d p q : Z)
    (Hx : a <= x <= b)
    (Hy : c <= y <= d)
    (Hp : p > 0)
    (Hq : q > 0) :
    p * a + q * c <= p * x + q * y <= p * b + q * d.
  Proof.
    nia.
  Qed.
End AddProofUtil.

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
(10) a - b - c = 0 \/ a - b - c = - 2 ^ 32
(11) a = b + c \/ a = b + c + 2 ^ 32
(12) a = b + c (mod 2 ^ 32)
*)  

Module Add2Proof.
    Definition eval_add2 {p} `{Prime p} (a b : Array.t Z U32_LIMBS) : Array.t Z U32_LIMBS :=
        unpack_16_limbs (((pack_16_limbs a) + (pack_16_limbs b)) mod 2 ^ 32).
    
    Lemma implies {p} `{Prime p} (result a b : Array.t Z U32_LIMBS) :
      (* let result := M.map_mod result in
      let a := M.map_mod a in
      let b := M.map_mod b in *)
      2 ^ 17 < p ->
      RangeCheck32.t result ->
      RangeCheck32.t a ->
      RangeCheck32.t b ->
      {{ add2 result a b 🔽
        tt,
        Array.Eq.t (eval_add2 a b) result
      }}.
    Proof.
      cbn.
      intros Hp.
      intros Hrc_res Hrc_a Hrc_b.
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

      destruct Hrc_res as [Hrc_res_first Hrc_res_second].
      destruct Hrc_a as [Hrc_a_first Hrc_a_second].
      destruct Hrc_b as [Hrc_b_first Hrc_b_second].
      fold a0 a1 b0 b1 res0 res1 in Hrc_res_first, Hrc_res_second, Hrc_a_first, Hrc_a_second, Hrc_b_first, Hrc_b_second.

      eapply Run.LetAccumulate. {
        constructor.
      }
      intros H2.
      fold a0 a1 b0 b1 res0 res1 in H2.

      (* precondition gives: p and 2 ^ 16 are relatively coprime. *)
      
      assert (Hp_coprime : Znumtheory.rel_prime (2 ^ 16) p).
      {
        apply large_prime_coprime_exp_of_2.
        lia.
      }
      
      (* d1 *)
      set (acc_16 := BinOp.sub (BinOp.sub res0 a0) b0) in H1, H2.
      (* d2 *)
      set (acc_32 := BinOp.sub (BinOp.sub res1 a1) b1) in H1.
      (* d3 *)
      set (acc := BinOp.add acc_16 (BinOp.mul acc_32 (Z.pow_pos 2 16))) in H1.
      set (two_32 := BinOp.mul (UnOp.from (Z.pow_pos 2 16)) (UnOp.from (Z.pow_pos 2 16))) in H1.

      set (two_16 := UnOp.from (2 ^ 16)) in H2.

      assert (H_two_16 : two_16 = 2 ^ 16). {
        apply (AddProofUtil.constant_unwrap (2 ^ 16)); lia.
      }

      assert (H_two_32 : two_32 = UnOp.from (2 ^ 32)). {
        unfold two_32.
        replace (Z.pow_pos 2 16) with (2 ^ 16) by lia.
        unfold two_16 in H_two_16.
        rewrite H_two_16.
        unfold BinOp.mul.
        replace (2 ^ 16 * 2 ^ 16) with (2 ^ 32) by lia.
        unfold UnOp.from.
        auto.
      }

      (* Now we have acc_16, acc_32, and acc in terms of a0, a1, b0, b1, res0, res1 *)

      (* We will now prove the properties of acc_16 and acc_32 *)

      rewrite H_two_16 in H2.

      (* We will now define acc_16_r, acc_32_r, and acc_r *)

      (* (d4) acc_16_r = a[0] - b[0] - c[0] (without mod) *)
      set (acc_16_r := res0 - a0 - b0).

      (* (d5) acc_32_r = a[1] - b[1] - c[1] *)
      set (acc_32_r := res1 - a1 - b1).

      (* (d6) acc_r    = a - b - c    (without mod) = acc_16_r + 2 ^ 16 * acc_32_r *)
      set (acc_r := acc_16_r + 2 ^ 16 * acc_32_r).      

      assert (Hacc_16_r : - 2 ^ 17 + 2 <= acc_16_r <= 2 ^ 16 - 1). 
      {
        unfold acc_16_r.
        lia.
      }

      assert (Hacc_32_r : - 2 ^ 17 + 2 <= acc_32_r <= 2 ^ 16 - 1). {
        unfold acc_32_r.
        lia.
      }

      assert (Hacc_r : - 2 ^ 33 + 2 <= acc_r <= 2 ^ 32 - 1).
      {
        unfold acc_r.
        lia.
      }

      (* Now we have acc_16_r, acc_32_r, and acc_r in the range [-2^16 + 2, 2^16 - 1] and [-2^32 + 2, 2^32 - 1] respectively *)

      (* We will now define acc_16 and acc_32 in terms of acc_16_r and acc_32_r *)

      assert (Hacc_16 : acc_16 = UnOp.from acc_16_r).
      {
        unfold acc_16.
        unfold acc_16_r.
        show_equality_modulo.
      }

      assert (Hacc_32 : acc_32 = UnOp.from acc_32_r).
      {
        unfold acc_32.
        unfold acc_32_r.
        show_equality_modulo.
      }

      (* Now we have acc_16 and acc_32 in the range [0, 2^16) *)

      (* We will now rewrite the constraints H1 and H2 to use these definitions *)

      (* (A) acc_16 * (acc_16 + 2 ^ 16) = 0 (mod p) *)
      (* (B) acc * (acc + (2 ^ 32) mod p) = 0 (mod p) *)


      (* Now we have acc_16 and acc_32 in the range [0, 2^16) *)
      (* We can now rewrite H1 and H2 to use these definitions *)

      rewrite mul_zero_implies_zero in H1, H2.

      (* (0) acc_16 = 0 (mod p) \/ (acc_16 + 2 ^ 16) = 0 (mod p) from (A) *)
      assert (H0' : UnOp.from acc_16 = 0 \/ BinOp.add acc_16 (2 ^ 16) = 0).
      {
        rewrite FieldRewrite.from_add in H2.
        assumption.
      }
      (* (1) acc_16_r = 0 \/ acc_16_r = - 2 ^ 16 from (0) and (Hp) *)
      assert (H1' : acc_16_r = 0 \/ acc_16_r + 2 ^ 16 = 0).
      {
        rewrite Hacc_16 in H0'.
        rewrite FieldRewrite.from_from in H0'.
        rewrite FieldRewrite.add_from_left in H0'.
        unfold UnOp.from in H0'.
        unfold BinOp.add in H0'.
        destruct H0' as [H0a | H0b].
        (* acc_16_r mod p = 0. *)
        {
          left.
          apply (mod_0_range p acc_16_r).
          (* p > 0 *)
          {
            lia.
          }
          (* - p < acc_16_r < p *)
          {
            lia.
          }
          auto.
        }
        (* (acc_16_r + 2 ^ 16) mod p = 0 *)
        {
          right.
          apply (mod_0_range p (acc_16_r + 2 ^ 16)).
          (* p > 0 *)
          {
            lia.
          }
          (* - p < acc_16_r < p *)
          {
            lia.
          }
          auto.
        }
      }
      (* (2) acc_16_r = 0 (mod 2 ^ 16) from (1) *)
      assert (H2' : acc_16_r mod (2 ^ 16) = 0).
      {
        lia.
      }

      (* Now we have acc_16_r = 0 (mod 2 ^ 16) *)

      (* We will now prove the properties of acc *)
      (* (3) acc = 0 (mod p) \/ (acc + (2 ^ 32) mod p) = 0 (mod p) from (B) *)
      (* (4) acc = 0 (mod p) \/ acc = - 2 ^ 32 (mod p) from (3) *)
      assert (H4' : UnOp.from acc = 0 \/ BinOp.add acc (2 ^ 32) = 0).
      {
        rewrite FieldRewrite.from_add in H1.
        rewrite H_two_32 in H1.
        rewrite FieldRewrite.add_from_right in H1.
        assumption.
      }
      
      (* (5) acc_r = 0 (mod 2 ^ 16) from (2), (d6) and arithmetics *)
      assert (H5' : acc_r mod (2 ^ 16) = 0).
      {
        unfold acc_r.
        lia.
      }
      (* (6) acc = acc_r mod p *)
      assert (H6' : acc = UnOp.from acc_r).
      {
        unfold acc.
        unfold acc_r.
        rewrite Hacc_32.
        rewrite FieldRewrite.mul_from_left.
        rewrite Hacc_16.
        rewrite FieldRewrite.add_from_left.
        unfold BinOp.add.
        replace (Z.pow_pos 2  16) with (2 ^ 16) by lia.
        unfold UnOp.from.
        unfold BinOp.mul.
        rewrite Z.mul_comm.
        show_equality_modulo.
      }
      (* (7) acc_r = 0 (mod p) \/ acc_r = - 2 ^ 32 (mod p) from (4) and (B) *)
      assert (H7' : UnOp.from acc_r = 0 \/ BinOp.add acc_r (2 ^ 32) = 0).
      {
        rewrite H6' in H4'.
        rewrite FieldRewrite.from_from in H4'.
        rewrite FieldRewrite.add_from_left in H4'.
        assumption.
      }
      (* (8) acc_r = 0 (mod 2 ^ 16 * p) \/ acc_r = - 2 ^ 32 (mod 2 ^ 16 * p) from (crt), (5), (7) *)
      assert (H8' : acc_r mod (2 ^ 16 * p) = 0 \/ (acc_r + 2 ^ 32) mod (2 ^ 16 * p) = 0).
      {
        assert (Hp0 : p <> 0) by lia.
        assert (H216 : 2 ^ 16 <> 0) by lia.
        destruct H7' as [H7a | H7b].
        (* acc_r mod p = 0. *)
        {
          left.
          unfold UnOp.from in H7a.
          apply (binary_chinese_remainder_alt (2 ^ 16) p acc_r 0 H216 Hp0 Hp_coprime H5' H7a).
        }
        (* (acc_r + 2 ^ 32) mod p = 0. *)
        {
          right.
          unfold BinOp.add in H7b.
          assert (H5'' : (acc_r + 2 ^ 32) mod (2 ^ 16) = 0).
          {
            rewrite <-Zplus_mod_idemp_r.
            replace ((2 ^ 32) mod (2 ^ 16)) with 0 by lia.
            rewrite Z.add_0_r.
            assumption.
          }
          apply (binary_chinese_remainder_alt (2 ^ 16) p (acc_r + 2 ^ 32) 0 H216 Hp0 Hp_coprime H5'' H7b).
        }
      }
      
      (* (9) acc_r = 0 \/ acc_r = - 2 ^ 32 from (8), (hp) and (r2). *)
      assert (H9' : acc_r = 0 \/ (acc_r + 2 ^ 32) = 0).
      {
        (*
        2 ^ 16 p > 2 ^ 33
        -k < arg_min < arg_max < k
        then given k > 0, arg mod k = 0
        arg = 0.
        *)
        assert (H2_16_p : 2 ^ 16 * p > 2 ^ 33).
        {
          replace (2 ^ 33) with ((2 ^ 16) * (2 ^ 17)) by lia.
          apply AddProofUtil.p_times_2_exp_16; lia.
        }

        destruct H8' as [H8a | H8b].
        (* acc_r mod 2 ^ 16  * p = 0. *)
        {
          left.
          apply (mod_0_range (2 ^ 16 * p)); [lia | lia | auto].
        }
        
        (* (acc_r + 2 ^ 32) mod 2 ^ 16  * p = 0. *)
        {
          right.
          apply (mod_0_range (2 ^ 16 * p)); [lia | lia | auto].
        }

      } 
      (* Now we have acc_r = 0 \/ acc_r = - 2 ^ 32 *)

      (* We can now conclude the proof *)

      (* (10) a = b + c \/ a = b + c + 2 ^ 32 *)
      (* (11) a = b + c (mod 2 ^ 32) *)
      set (res_val := pack_16_limbs result).
      set (a_val := pack_16_limbs a).
      set (b_val := pack_16_limbs b).

      unfold acc_r in H9'.
      unfold acc_16_r, acc_32_r in H9'.

      assert (H10' : res_val = a_val + b_val \/ res_val = a_val + b_val - 2 ^ 32).
      {
        unfold res_val, a_val, b_val.
        unfold pack_16_limbs.
        fold res0 res1 a0 a1 b0 b1.
        unfold BITS_PER_LIMB.
        destruct H9' as [H9a | H9b].
        {
          left.
          lia.
        }
        {
          right.
          lia.
        }
      }

      (* (11) res0 = a0 + b0 (mod 2 ^ 16) *)
      assert (H11' : res0 mod (2 ^ 16) = (a0 + b0) mod (2 ^ 16)).
      {
        destruct H9' as [H9a | H9b].
        {
          apply (f_equal (fun x => x mod (2 ^ 16))) in H9a.
          rewrite Z.mul_comm in H9a.
          rewrite Z_mod_plus_full in H9a.
          rewrite Zmod_0_l in H9a.
          replace (res0 - a0 - b0) with (res0 - (a0 + b0)) in H9a by lia.
          apply eqm_minus_0.
          assumption.
        }
        {
          apply (f_equal (fun x => x mod (2 ^ 16))) in H9b.
          replace (2 ^ 32) with ((2 ^ 16) * 2 ^ 16) in H9b by lia.
          rewrite Z.mul_comm in H9b.
          rewrite Z_mod_plus_full in H9b.
          rewrite Z_mod_plus_full in H9b.
          rewrite Zmod_0_l in H9b.
          replace (res0 - a0 - b0) with (res0 - (a0 + b0)) in H9b by lia.
          apply eqm_minus_0.
          assumption.
        }
      }

      assert (Hres : res_val = (a_val + b_val) mod (2 ^ 32)).
      {
        assert (Hres_val_range : 0 <= res_val < 2 ^ 32).
        {
          unfold res_val.
          unfold pack_16_limbs.
          unfold BITS_PER_LIMB.
          fold res0 res1 in Hrc_res_first, Hrc_res_second.
          fold res0 res1.
          split.
          (* >= 0 *)
          {
            apply Z.add_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; lia].
          }
          (* < 2 ^ 32 *)
          {
            (*
            res0 + res1 * 2 ^ 16 
            <= 2 ^ 16 - 1 + (2 ^ 16 - 1) * 2 ^ 16
            <= 2 ^ 16 * 2 ^ 16 - 1
            <= 2 ^ 32 - 1
            < 2 ^ 32
            *)
            apply int_upper.
            assert (res0 <= Z.pow_pos 2 16 - 1).
            { 
              apply int_upper. 
              exact (proj2 Hrc_res_first). 
            }
            assert (res1 <= Z.pow_pos 2 16 - 1).
            { 
              apply int_upper. 
              exact (proj2 Hrc_res_second). 
            }
            assert (res0 + res1 * Z.pow_pos 2 16 <= 
              (Z.pow_pos 2 16 - 1) + (Z.pow_pos 2 16 - 1) * Z.pow_pos 2 16).
            {
              apply Z.add_le_mono.
              {
                exact H0.
              }
              {
                apply Z.mul_le_mono_nonneg_r.
                {
                  lia.
                }
                {
                  exact H3.
                }
              }
            }
            assert ((Z.pow_pos 2 16 - 1) + (Z.pow_pos 2 16 - 1) * Z.pow_pos 2 16 = 
              Z.pow_pos 2 16 * Z.pow_pos 2 16 - 1).
            {
              ring_simplify.
              reflexivity.
            }
            rewrite H5 in H4.
            exact H4.
          }
        }
        destruct H10' as [H10a | H10b].
        (* case 1: res_val = a_val + b_val *)
        {
          rewrite <-H10a.
          rewrite Zmod_small; auto.
        }
        (* case 2: res_val = a_val + b_val - 2 ^ 32 *)
        {
          assert (H10b' : res_val + 2 ^ 32 = a_val + b_val).
          {
            rewrite H10b.
            ring.
          }
          rewrite <-H10b'.
          replace (res_val + 2 ^ 32) with (res_val + 1 * 2 ^ 32) by ring.
          rewrite Z_mod_plus; [|lia].
          rewrite Zmod_small; auto.
        }
      }
      (* helper *)
      assert (Htmp : Array.Eq.t (eval_add2 a b) result).
      {
        unfold eval_add2.
        unfold Array.Eq.t.
        intros i.
        unfold U32_LIMBS.
        unfold BITS_PER_LIMB.
        intros Hi.
        unfold unpack_16_limbs; unfold double_val.
        apply (AddProofUtil.array_index_range_U32 i) in Hi.
        destruct Hi as [Hi0 | Hi1].
        (* i = 0 *)
        {
          rewrite Hi0.
          fold res0.
          simpl.
          fold a_val b_val.
          replace (Z.pow_pos 2 16) with (2 ^ 16) by lia.
          replace (a0 + a1 * 2 ^ 16 + (b0 + b1 * 2 ^ 16)) with ((a0 + b0) + (a1 + b1) * (2 ^ 16)) by lia.
          replace (Z.pow_pos 2 32) with (2 ^ 32) by lia.
          rewrite <- Hres.
          unfold res_val.
          unfold pack_16_limbs.
          unfold BITS_PER_LIMB.
          rewrite Z_mod_plus_full.
          unfold res0.
          apply Zmod_small.
          apply Hrc_res_first.
        }
        (* i = 1 *)
        {
          rewrite Hi1.
          fold res1.
          simpl.
          replace (Z.pow_pos 2 16) with (2 ^ 16) by lia.
          fold a_val b_val.
          replace (Z.pow_pos 2 32) with (2 ^ 32) by lia.
          rewrite <-Hres.
          unfold res_val.
          unfold res1.
          unfold pack_16_limbs.
          unfold BITS_PER_LIMB.
          rewrite Z_div_plus_full; [|lia].
          cut (result.(Array.get) 0 / 2 ^ 16 = 0); [intros Hr; rewrite Hr; reflexivity |].
          apply Zdiv_small.
          apply Hrc_res_first.
        }
      }
      eapply Run.Implies. {
        repeat constructor.
      }
      easy.
    Qed.
End Add2Proof.

Module Add3Proof.
    Definition eval_add3 {p} `{Prime p} (a b c : Array.t Z U32_LIMBS) : Array.t Z U32_LIMBS :=
      unpack_16_limbs (((pack_16_limbs a) + (pack_16_limbs b) + (pack_16_limbs c)) mod 2 ^ 32).

    Lemma implies {p} `{Prime p} (result a b c : Array.t Z U32_LIMBS) :
      (* let result := M.map_mod result in
      let a := M.map_mod a in
      let b := M.map_mod b in *)
      p > 3 * 2 ^ 17 ->
      RangeCheck32.t result ->
      RangeCheck32.t a ->
      RangeCheck32.t b ->
      RangeCheck32.t c ->
      {{ add3 result a b c 🔽
        tt,
        Array.Eq.t (eval_add3 a b c) result
      }}.
    Proof.
      intros Hp Hrc_res Hrc_a Hrc_b Hrc_c.
      eapply Run.LetAccumulate. {
        constructor.
      }
      intros HA.
      
      eapply Run.LetAccumulate. {
        constructor.
      }
      intros HB.
      set (a0 := a.(Array.get) 0) in HA, HB.
      set (a1 := a.(Array.get) 1) in HA, HB.
      set (b0 := b.(Array.get) 0) in HA, HB.
      set (b1 := b.(Array.get) 1) in HA, HB.
      set (c0 := c.(Array.get) 0) in HA, HB.
      set (c1 := c.(Array.get) 1) in HA, HB.
      set (res0 := result.(Array.get) 0) in HA, HB.
      set (res1 := result.(Array.get) 1) in HA, HB.
      set (acc_16 := BinOp.sub (BinOp.sub (BinOp.sub res0 a0) b0) c0) in HA, HB.
      set (acc_32 := BinOp.sub (BinOp.sub (BinOp.sub res1 a1) b1) c1) in HA, HB.
      set (acc := BinOp.add acc_16 (BinOp.mul acc_32 (2 ^ 16))) in HA.
      (* apply definitions *)
      destruct Hrc_res as [Hrc_res_first Hrc_res_second].
      destruct Hrc_a as [Hrc_a_first Hrc_a_second].
      destruct Hrc_b as [Hrc_b_first Hrc_b_second].
      destruct Hrc_c as [Hrc_c_first Hrc_c_second].
      (* shorthand substitutions*)
      fold res0 res1 in Hrc_res_first, Hrc_res_second.
      fold a0 a1 in Hrc_a_first, Hrc_a_second.
      fold b0 b1 in Hrc_b_first, Hrc_b_second.
      fold c0 c1 in Hrc_c_first, Hrc_c_second.

      (* HA : acc * (acc + two_32) * (acc + 2 * two_32) = 0 *)
      (* HB : acc_16 * (acc_16 + two_16) * (acc_16 + 2 * two_16) = 0 *)
      set (acc_16_r := res0 - a0 - b0 - c0).
      set (acc_32_r := res1 - a1 - b1 - c1).
      set (acc_r := acc_16_r + 2 ^ 16 * acc_32_r).
      
      rewrite mul_zero_implies_zero_3 in HA, HB.
      rewrite FieldRewrite.from_add in HA, HB.
      rewrite FieldRewrite.from_add in HA, HB.
      rewrite FieldRewrite.mul_from_left in HA.
      rewrite FieldRewrite.mul_from_right in HA.
      rewrite FieldRewrite.add_from_right in HB.
      unfold BinOp.mul in HA.
      unfold double in HA, HB.
      replace (2 ^ 16 * 2 ^ 16) with (2 ^ 32) in HA by lia.
      fold (UnOp.from (2 ^ 32)) in HA.
      rewrite FieldRewrite.add_from_right in HA.
      rewrite FieldRewrite.mul_from_left in HA, HB.
      unfold BinOp.mul in HA, HB.
      fold (UnOp.from (2 ^ 16 * 2)) in HB.
      fold (UnOp.from (2 ^ 32 * 2)) in HA.
      rewrite FieldRewrite.add_from_right in HA, HB.

      assert (Hacc_16 : acc_16 = UnOp.from acc_16_r).
      {
        unfold acc_16.
        unfold acc_16_r.
        show_equality_modulo.
      }

      assert (Hacc_32 : acc_32 = UnOp.from acc_32_r).
      {
        unfold acc_32.
        unfold acc_32_r.
        show_equality_modulo.
      }

      assert (Hacc : acc = UnOp.from acc_r).
      {
        unfold acc.
        unfold acc_r.
        rewrite Hacc_32.
        rewrite FieldRewrite.mul_from_left.
        rewrite Hacc_16.
        rewrite FieldRewrite.add_from_left.
        unfold BinOp.add.
        replace (Z.pow_pos 2 16) with (2 ^ 16) by lia.
        unfold UnOp.from.
        unfold BinOp.mul.
        rewrite Z.mul_comm.
        show_equality_modulo.
      }

      (* HA : acc mod p = 0 \/ (acc + 2 ^ 32) mod p = 0 \/ (acc + 2 * 2 ^ 32) mod p = 0 *)
      (* HB : acc_16 mod p = 0 \/ (acc_16 + 2 ^ 16) mod p = 0 \/ (acc_16 + 2 * 2 ^ 16) mod p = 0 *)

      (* H1' : acc_r = 0 \/ acc_r + 2 ^ 32 = 0 \/ acc_r + 2 * 2 ^ 32 = 0 (mod p). *)
      assert (H1' : UnOp.from acc_r = 0 \/ BinOp.add acc_r (2 ^ 32) = 0 \/ BinOp.add acc_r (2 * 2 ^ 32) = 0).
      {
        rewrite Hacc in HA.
        rewrite FieldRewrite.from_from in HA.
        rewrite FieldRewrite.add_from_left in HA.
        rewrite FieldRewrite.add_from_left in HA.
        auto.
      }

      (* range check on `_r`s *)
      assert (Hacc_16_r : - 3 * 2 ^ 17 + 3 <= acc_16_r <= 2 ^ 16 - 1). 
      {
        unfold acc_16_r.
        lia.
      }

      assert (Hacc_32_r : - 3 * 2 ^ 17 + 3 <= acc_32_r <= 2 ^ 16 - 1). {
        unfold acc_32_r.
        lia.
      }

      assert (Hacc_r : - 3 * 2 ^ 33 + 3 <= acc_r <= 2 ^ 32 - 1).
      {
        unfold acc_r.
        lia.
      }

      (* H2' : acc_16_r = 0 \/ acc_16_r = - 2 ^ 16 \/ acc_16_r = - 2 * 2 ^ 16 from (0) and (Hp) *)


      (* H2' : acc_16_r = 0 \/ acc_16_r + 2 ^ 16 = 0 \/ acc_16_r + 2 * 2 ^ 16 = 0. *)
      assert (H2' : acc_16_r = 0 \/ acc_16_r + 2 ^ 16 = 0 \/ acc_16_r + 2 * 2 ^ 16 = 0).
      {
        rewrite Hacc_16 in HB.
        rewrite FieldRewrite.from_from in HB.
        rewrite! FieldRewrite.add_from_left in HB.
        replace (BinOp.add acc_16_r (2 ^ 16)) with (UnOp.from (acc_16_r + 2 ^ 16)) in HB by reflexivity.
        replace (BinOp.add acc_16_r (2 ^ 16 * 2)) with (UnOp.from (acc_16_r + 2 ^ 16 * 2)) in HB by reflexivity.
        destruct HB as [HBa | HB'].
        {
          left.
          unfold UnOp.from in HBa.
          apply mod_0_range with (k := p).
          - lia.
          - lia.
          - auto.
        }
        {
          destruct HB' as [HBb | HBc].
          {
            right. left.
            unfold UnOp.from in HBb.
            apply mod_0_range with (k := p).
            - lia.
            - lia.
            - auto.
          }
          {
            right. right.
            unfold UnOp.from in HBc.
            apply mod_0_range with (k := p).
            - lia.
            - lia.
            - auto.
          }
        }
      }

      (* H3' : acc_r = 0 (mod 2 ^ 16) *)
      assert (H3' : acc_r mod (2 ^ 16) = 0).
      {
        unfold acc_r.
        lia.
      }

      (* H4' : acc_r = 0 \/ acc_r + 2 ^ 32 = 0 \/ acc_r + 2 * 2 ^ 32 = 0 (mod 2 ^ 16 p) *)
      assert (H4 : acc_r mod (2 ^ 16 * p) = 0 \/ (acc_r + 2 ^ 32) mod (2 ^ 16 * p) = 0 \/ (acc_r + 2 * 2 ^ 32) mod (2 ^ 16 * p) = 0).
      {
        assert (Hp_coprime : Znumtheory.rel_prime (2 ^ 16) p).
        {
          apply large_prime_coprime_exp_of_2.
          lia.
        }
        assert (H216 : 2 ^ 16 <> 0) by lia.
        assert (Hp_gt_0 : p <> 0) by lia.
        destruct HA as [HAa | HA'].
        {
          left.
          assert (Hcrt := binary_chinese_remainder_alt (2 ^ 16) p acc_r ).
          apply (Hcrt 0 H216 Hp_gt_0 Hp_coprime H3').
          rewrite Hacc in HAa.
          rewrite FieldRewrite.from_from in HAa.
          apply HAa.
        }
        {
          destruct HA' as [HAb | HAc].
          {
            right. left.
            assert (Hcrt := binary_chinese_remainder_alt (2 ^ 16) p (acc_r + 2 ^ 32)).
            rewrite Hacc in HAb.
            rewrite FieldRewrite.add_from_left in HAb.
            replace (acc_r mod 2 ^ 16) with ((acc_r + 2 ^ 32) mod 2 ^ 16) in H3' by lia.
            apply (Hcrt 0 H216 Hp_gt_0 Hp_coprime H3').
            apply HAb.
          }
          {
            right. right.
            assert (Hcrt := binary_chinese_remainder_alt (2 ^ 16) p (acc_r + 2 * 2 ^ 32)).
            rewrite Z.mul_comm in HAc.
            replace (acc_r mod 2 ^ 16) with ((acc_r + 2 * 2 ^ 32) mod 2 ^ 16) in H3' by lia.
            apply (Hcrt 0 H216 Hp_gt_0 Hp_coprime H3').
            rewrite Hacc in HAc.
            rewrite FieldRewrite.add_from_left in HAc.
            apply HAc.
          }
        }
      }

      (* H5' : acc_r = 0 \/ acc_r + 2 ^ 32 = 0 \/ acc_r + 2 * 2 ^ 32 = 0. *)
      assert (H5' : acc_r = 0 \/ acc_r + 2 ^ 32 = 0 \/ acc_r + 2 * 2 ^ 32 = 0).
      {
        assert (H2_16_p : 2 ^ 16 * p > 3 * 2 ^ 33).
        {
          replace (3 * 2 ^ 33) with ((2 ^ 16) * (3 * 2 ^ 17)) by lia.
          apply AddProofUtil.p_times_2_exp_16; lia.
        }
        destruct H4 as [H4a | H4''].
        {
          left.
          apply (mod_0_range (2 ^ 16 * p)); [lia | lia | auto].
        }
        {
          destruct H4'' as [H4b | H4c].
          {
            right. left.
            apply (mod_0_range (2 ^ 16 * p)); [lia | lia | auto].
          }
          {
            right. right.
            apply (mod_0_range (2 ^ 16 * p)); [lia | lia | auto].
          }
        }
      }

      assert (Hsum_mod_32 : acc_r mod (2 ^ 32) = 0).
      {
        destruct H5' as [H5_1 | H5_res].
        {
          rewrite H5_1.
          show_equality_modulo.
        }
        {
          destruct H5_res as [H5_2 | H5_3].
          {
            replace (acc_r mod 2 ^ 32) with ((acc_r + 1 * 2 ^ 32) mod 2 ^ 32) by (apply Z_mod_plus_full).
            replace (acc_r + 1 * 2 ^ 32) with (acc_r + 2 ^ 32) by lia.
            rewrite H5_2.
            show_equality_modulo.
          }
          {
            replace (acc_r mod 2 ^ 32) with ((acc_r + 2 * 2 ^ 32) mod 2 ^ 32) by (apply Z_mod_plus_full).
            rewrite H5_3.
            show_equality_modulo.
          }
        }
      }



      (* desired properties *)
      set (sum_abc := (a0 + a1 * Z.pow_pos 2 16 + (b0 + b1 * Z.pow_pos 2 16) + (c0 + c1 * Z.pow_pos 2 16)) mod Z.pow_pos 2 32).

      assert (Hsum_eq_res : sum_abc = res0 + res1 * Z.pow_pos 2 16).
      {
        unfold acc_r in Hsum_mod_32.
        unfold sum_abc.
        replace (a0 + a1 * Z.pow_pos 2 16 + (b0 + b1 * Z.pow_pos 2 16) + (c0 + c1 * Z.pow_pos 2 16)) with ((a0 + b0 + c0) + (a1 + b1 + c1) * (Z.pow_pos 2 16)) by lia.
        unfold acc_16_r, acc_32_r in Hsum_mod_32.
        replace (res0 - a0 - b0 - c0 + 2 ^ 16 * (res1 - a1 - b1 - c1)) with (res0 - (a0 + b0 + c0) + 2 ^ 16 * (res1 - (a1 + b1 + c1))) in Hsum_mod_32 by lia.
        set (sum_0 := a0 + b0 + c0).
        set (sum_1 := a1 + b1 + c1).
        fold sum_0 sum_1 in Hsum_mod_32.
        replace (res0 - sum_0 + 2 ^ 16 * (res1 - sum_1)) with (res0 + 2 ^ 16 * res1 - (sum_0 + 2 ^ 16 * sum_1)) in Hsum_mod_32 by lia.
        replace (2 ^ 16) with (Z.pow_pos 2 16) in Hsum_mod_32 by lia.
        replace (Z.pow_pos 2 16 * sum_1) with (sum_1 * Z.pow_pos 2 16) in Hsum_mod_32 by lia.
        replace (Z.pow_pos 2 16 * res1) with (res1 * Z.pow_pos 2 16) in Hsum_mod_32 by apply Z.mul_comm.
        set (sum_val := sum_0 + sum_1 * (Z.pow_pos 2 16)).
        set (res_val := res0 + res1 * Z.pow_pos 2 16).
        fold sum_val in Hsum_mod_32.
        fold res_val in Hsum_mod_32.
        assert (Hrc_res_val : 0 <= res_val <= 2 ^ 32 - 1).
        {
          unfold res_val.
          replace res0 with (1 * res0) by lia.
          replace (res1 * Z.pow_pos 2 16) with (Z.pow_pos 2 16 * res1) by apply Z.mul_comm.
          replace 0 with (1 * 0 + (Z.pow_pos 2 16) * 0) by lia.
          replace (2 ^ 32 - 1) with (Z.pow_pos 2 32 - 1) by lia.
          replace (Z.pow_pos 2 32 - 1) with (1 * (Z.pow_pos 2 16 - 1) + (Z.pow_pos 2 16) * (Z.pow_pos 2 16 - 1)) by lia.
          apply (AddProofUtil.compound_range_check res0 res1 0 (Z.pow_pos 2 16 - 1) 0 (Z.pow_pos 2 16 - 1) 1 (Z.pow_pos 2 16)).
          {
            split; [|apply int_upper]; apply Hrc_res_first.
          }
          {
            split; [| apply int_upper]; apply Hrc_res_second.
          }
          {
            lia.
          }
          {
            lia.
          }
        }

        rewrite <-(Zmod_small res_val (Z.pow_pos 2 32)).
        {
          apply eqm_minus_0 in Hsum_mod_32.
          auto.
        }

        {
          replace (Z.pow_pos 2 32) with (2 ^ 32) by lia.
          rewrite int_upper.
          auto.
        }
      }

      assert (Htmp : Array.Eq.t (eval_add3 a b c) result).
      {
        unfold Array.Eq.t.
        unfold U32_LIMBS.
        intros i Hi.
        apply (AddProofUtil.array_index_range_U32 i) in Hi.
        destruct Hi as [Hi0 | Hi1].
        (* i = 0 *)
        {
          rewrite Hi0.
          unfold eval_add3.
          unfold unpack_16_limbs.
          unfold pack_16_limbs.
          fold res0 res1 a0 a1 b0 b1 c0 c1.
          simpl.
          unfold sum_abc in Hsum_eq_res.
          rewrite Hsum_eq_res.
          rewrite Z_mod_plus_full.
          apply Zmod_small.
          apply Hrc_res_first.
        }
        (* i = 1 *)
        {
          rewrite Hi1.
          unfold eval_add3.
          unfold unpack_16_limbs.
          unfold pack_16_limbs.
          fold res0 res1 a0 a1 b0 b1 c0 c1.
          simpl.
          unfold sum_abc in Hsum_eq_res.
          rewrite Hsum_eq_res.
          rewrite Z_div_plus_full; [|lia].
          assert (Hres0 : res0 / Z.pow_pos 2 16 = 0). {
            apply Zdiv_small.
            apply Hrc_res_first.
          }
          rewrite Hres0.
          auto.
        }
      }

      eapply Run.Implies. {
        repeat constructor.
      }

      easy.
    Qed.  

End Add3Proof.
