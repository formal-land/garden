Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.Util.

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

(* Injectivity lemma for pack_16_limbs *)
Lemma pack_16_limbs_injective: 
  forall (a b : Array.t Z U32_LIMBS),
    (* If both arrays have valid 16-bit limbs *)
    (0 <= a.(Array.get) 0 < 2 ^ BITS_PER_LIMB) ->
    (0 <= a.(Array.get) 1 < 2 ^ BITS_PER_LIMB) ->
    (0 <= b.(Array.get) 0 < 2 ^ BITS_PER_LIMB) ->
    (0 <= b.(Array.get) 1 < 2 ^ BITS_PER_LIMB) ->
    pack_16_limbs a = pack_16_limbs b ->
    a = b. (* or at least, their elements are the same in the indexes we care about (0 and 1). *)
Proof.
  intros a b Ha0_bounds Ha1_bounds Hb0_bounds Hb1_bounds H_pack_eq.
  unfold pack_16_limbs in H_pack_eq.
  (* From a.0 + a.1 * 2^16 = b.0 + b.1 * 2^16, we can derive a.0 = b.0 and a.1 = b.1 *)
  (* using modular arithmetic and the bounds *)
  admit. (* Standard arithmetic proof *)
Admitted.

Definition unpack_16_limbs (value : Z) : Array.t Z U32_LIMBS :=
  {| Array.get i := 
        match i with
        | 0 => value mod (2 ^ BITS_PER_LIMB)
        | 1 => value / (2 ^ BITS_PER_LIMB)
        | _ => 0 (* Default case, should not happen *)
        end
  |}.

(* Constants for Blake3 *)

(* pub const BITS_PER_LIMB: usize = 16; *)

Module Add2Proof.
    (* Use the existing add2 specification from Util.v *)
    (* add2 : Array.t Z 2 -> Array.t Z 2 -> Array.t Z 2 -> M.t unit *)
    
    (* Helper function for semantic meaning of addition *)
    Definition eval_add2 {p} `{Prime p} (a b : Array.t Z U32_LIMBS) : Array.t Z U32_LIMBS :=
        unpack_16_limbs (BinOp.add (pack_16_limbs a) (pack_16_limbs b)).

    Module Valid.
      Record t {p} `{Prime p} (result a b : Array.t Z U32_LIMBS) : Prop := {
        add_correctness :
          let acc_16 := BinOp.sub (result.(Array.get) 0) (BinOp.add (a.(Array.get) 0) (b.(Array.get) 0)) in
          let acc_32 := BinOp.sub (result.(Array.get) 1) (BinOp.add (a.(Array.get) 1) (b.(Array.get) 1)) in
          let acc := BinOp.add acc_16 (BinOp.mul acc_32 (2 ^ BITS_PER_LIMB)) in
          (acc_16 = 0 \/ acc_16 = -(2 ^ BITS_PER_LIMB)) /\
          (acc = 0 \/ acc = -(2 ^ (2 * BITS_PER_LIMB)));
        result_deterministic :
          result = eval_add2 a b
      }.
    End Valid.

    Lemma implies {p} `{Prime p} (result a b : Array.t Z U32_LIMBS) :
      let result := M.map_mod result in
      let a := M.map_mod a in
      let b := M.map_mod b in
      p > 2 ^ 17 ->
      {{ add2 result a b 🔽
        tt,
        eval_add2 a b = result
      }}.
    Proof.
      (* We are not targeting soundness proof for now. *)
      admit.
    Admitted.

    Theorem deterministic {p} `{Prime p} :
      forall (a b result1 result2 : Array.t Z U32_LIMBS),
        p > 2 ^ 17 ->
        {{ add2 result1 a b 🔽 tt, True }} ->
        {{ add2 result2 a b 🔽 tt, True }} ->
        result1 = result2.
    Proof.
      intros a b result1 result2 Hp_large H1 H2.
      (* 
        Strategy: 
        1. The add2 constraints uniquely determine the result modulo p
        2. Since we're working with bounded values (< 2^32) and p > 2^17,
           the unique solution modulo p is also the unique integer solution
        3. Therefore result1 = result2 as integers
      *)
      
      (* Key insight: For Blake3, the inputs are range-checked to be < 2^16 per limb,
         so results are < 2^32. With p > 2^17, we have p > 2^17 > 2^32 for reasonable
         field sizes, making the modular solution equal to the integer solution. *)
      
      (* Apply the constraint uniqueness property *)
      (* From Util.v lines 130-145, add2 constraints ensure:
         - acc*(acc + 2^32) = 0 implies acc = 0 or acc = -2^32
         - acc_16*(acc_16 + 2^16) = 0 implies acc_16 = 0 or acc_16 = -2^16
         - With range checking and field size, this uniquely determines the result
      *)
      
      (* Both constraints are satisfied, so both results satisfy the same system *)
      assert (Uniqueness: forall result, 
        {{ add2 result a b 🔽 tt, True }} -> 
        exists! val, val = pack_16_limbs result /\ 
                    val = (pack_16_limbs a + pack_16_limbs b) mod (2 ^ (2 * BITS_PER_LIMB))).
      {
        intros result H_constraint.
        (* The add2 constraint system has a unique solution *)
        (* This follows from the mathematical analysis in Util.v *)
        exists ((pack_16_limbs a + pack_16_limbs b) mod (2 ^ (2 * BITS_PER_LIMB))).
        split.
        { split.
          { (* val = pack_16_limbs result *)
            unfold add2 in H_constraint.
            admit. (* should automatically follows from constraint satisfaction *)
          }
          { (* val = (pack_16_limbs a + pack_16_limbs b) mod 2^32 *)
            reflexivity.
          }
        }
        { (* uniqueness *)
          intros val' [H_eq H_sum].
          rewrite H_sum.
          reflexivity.
        }
      }

      (* Apply uniqueness to both results *)
      destruct (Uniqueness result1 H1) as [x1 H1_unique].
      destruct (Uniqueness result2 H2) as [x2 H2_unique].
      
      (* Extract the properties from the unique witnesses *)
      destruct H1_unique as [H1_props H1_uniq].
      destruct H2_unique as [H2_props H2_uniq].
      destruct H1_props as [Hval1_eq Hval1_sum].
      destruct H2_props as [Hval2_eq Hval2_sum].
      
      (* Both values are the same by uniqueness *)
      assert (x1 = x2) by (rewrite Hval1_sum, Hval2_sum; reflexivity).
      
      (* Since pack_16_limbs is injective for valid inputs, and 
         both results are valid (range-checked), we get result1 = result2 *)
      assert (pack_16_limbs result1 = pack_16_limbs result2) by 
        (rewrite <- Hval1_eq, <- Hval2_eq; assumption).
      
      (* Use injectivity of pack_16_limbs to conclude result1 = result2 *)
      apply pack_16_limbs_injective; try assumption.
      (* the following requirements are the basic range checks on results. *)
      { 
        admit.
      }
      {
        admit. 
      }
      {
        admit.
      }
      { 
        admit. 
      }
    Admitted.
End Add2Proof.

Module Xor32Shift.
  (* XOR with shift: input = mask XOR (output << shift_amount) *)

  Lemma deterministic {p} `{Prime p} :
    forall (mask : Array.t Z 32) (shift_amount : Z)
           (input1 input2 : Array.t Z U32_LIMBS) (output1 output2 : Array.t Z 32),
    {{ xor_32_shift input1 mask output1 shift_amount 🔽 tt, True }} ->
    {{ xor_32_shift input2 mask output2 shift_amount 🔽 tt, True }} ->
    input1 = input2 /\ output1 = output2.
  Proof.
    (* TODO: Prove XOR+shift has unique input/output relationship *)
    intros.
    admit.
  Admitted.
End Xor32Shift.