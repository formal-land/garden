Require Import Garden.Plonky3.MLessEffects.
Require Import Garden.OpenVM.EqualityCheck.example.

(*
pub struct ImmInstruction<T> {
    pub is_valid: T,
    pub opcode: T,
    pub immediate: T,
}
*)
Module ImmInstruction.
  Record t : Set := {
    is_valid : Z;
    opcode : Z;
    immediate : Z;
  }.
End ImmInstruction.

(*
pub struct AdapterAirContext<T, I: VmAdapterInterface<T>> {
  pub to_pc: Option<T>,
  pub reads: I::Reads,
  pub writes: I::Writes,
  pub instruction: I::ProcessedInstruction,
}
*)
(* TODO: move it to another file, as this is actually related to `integration_api.rs` *)
Module AdapterAirContext.
  Record t {NUM_LIMBS : Z}: Set := {
    to_pc : option Z;
    (* I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>, *)
    reads : Array.t Z NUM_LIMBS * Array.t Z NUM_LIMBS;
    (* I::Writes: Default, *)
    writes : unit;
    (* I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>, *)
    instruction : ImmInstruction.t;
  }.
  Arguments t : clear implicits.
End AdapterAirContext.

(* TODO: from `instructions.rs`, move there *)
(*
pub enum BranchEqualOpcode {
    BEQ,
    BNE,
}
*)
Module BranchEqualOpcode.
  Inductive t : Set :=
    | BEQ
    | BNE.
End BranchEqualOpcode.

(*
pub struct BranchEqualCoreCols<T, const NUM_LIMBS: usize> {
  pub a: [T; NUM_LIMBS],
  pub b: [T; NUM_LIMBS],

  pub cmp_result: T,
  pub imm: T,

  pub opcode_beq_flag: T,
  pub opcode_bne_flag: T,

  pub diff_inv_marker: [T; NUM_LIMBS],
}
*)
Module BranchEqualCoreCols.
  Record t {NUM_LIMBS : Z} : Set := {
    a : Array.t Z NUM_LIMBS;
    b : Array.t Z NUM_LIMBS;
    cmp_result : Z;
    imm : Z;
    opcode_beq_flag : Z;
    opcode_bne_flag : Z;
    diff_inv_marker : Array.t Z NUM_LIMBS;
  }.
  Arguments t : clear implicits.
End BranchEqualCoreCols.

(*
pub struct BranchEqualCoreAir<const NUM_LIMBS: usize> {
  offset: usize,
  pc_step: u32,
}
*)
Module BranchEqualCoreAir.
  Record t : Set := {
    offset : Z;
    pc_step : Z;
  }.
End BranchEqualCoreAir.

Definition eval {p} `{Prime p} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t)
    (local : BranchEqualCoreCols.t NUM_LIMBS)
    (from_pc : Z) :
    M.t (AdapterAirContext.t NUM_LIMBS) :=
  let flags : list Z := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let* is_valid : Z :=
    List.fold_left
      (fun acc flag =>
        let* _ := assert_bool flag in
        M.pure (BinOp.add acc flag)
      )
      Z.zero
      flags in
  let* _ := assert_bool is_valid in
  let* _ := assert_bool local.(BranchEqualCoreCols.cmp_result) in

  let a : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.a) in
  let b : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.b) in
  let inv_marker : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.diff_inv_marker) in

  let* cmp_eq : Z :=
    M.pure (
      BinOp.add
        (BinOp.mul local.(BranchEqualCoreCols.cmp_result) local.(BranchEqualCoreCols.opcode_beq_flag))
        (BinOp.mul (MLessEffects.not local.(BranchEqualCoreCols.cmp_result)) local.(BranchEqualCoreCols.opcode_bne_flag))
    ) in

  let* _ := M.for_in_zero_to_n NUM_LIMBS (fun i =>
    assert_zero (BinOp.mul cmp_eq (BinOp.sub (Array.get a i) (Array.get b i)))
  ) in
  let sum : Z := M.sum_for_in_zero_to_n NUM_LIMBS (fun i =>
    BinOp.mul (Array.get inv_marker i) (BinOp.sub (Array.get a i) (Array.get b i))
  ) in
  let sum := BinOp.add sum cmp_eq in
  let* _ := when is_valid (assert_one sum) in

  let flags_with_opcode_integer : list (Z * Z) :=
    [
      (local.(BranchEqualCoreCols.opcode_beq_flag), 0);
      (local.(BranchEqualCoreCols.opcode_bne_flag), 1)
    ] in
  let expected_opcode : Z :=
    Lists.List.fold_left
      (fun acc '(flag, opcode) =>
        BinOp.add acc (BinOp.mul flag opcode)
      )
      flags_with_opcode_integer
      0 in
  let expected_opcode : Z :=
    BinOp.add expected_opcode self.(BranchEqualCoreAir.offset) in

  let to_pc : Z :=
    BinOp.add
      (BinOp.add
        from_pc
        (BinOp.mul local.(BranchEqualCoreCols.cmp_result) local.(BranchEqualCoreCols.imm))
      )
      (BinOp.mul (MLessEffects.not local.(BranchEqualCoreCols.cmp_result)) self.(BranchEqualCoreAir.pc_step))
    in

  M.pure {|
    AdapterAirContext.to_pc := Some to_pc;
    AdapterAirContext.reads := (a, b);
    AdapterAirContext.writes := tt;
    AdapterAirContext.instruction := {|
      ImmInstruction.is_valid := is_valid;
      ImmInstruction.opcode := expected_opcode;
      ImmInstruction.immediate := local.(BranchEqualCoreCols.imm);
    |};
  |}.

Module Array.
  Parameter to_limbs : forall (NUM_LIMBS value : Z), Array.t Z NUM_LIMBS.
End Array.

Module Input.
  Record t : Set := {
    a : Z;
    b : Z;
    opcode : BranchEqualOpcode.t;
    imm : Z;
    (* to_pc : Z; *)
  }.

  Module Extra.
    Record t : Set := {
      cmp_result : Z;
      diff_inv_marker : Z;
    }.
  End Extra.

  Definition to_cols {NUM_LIMBS : Z} (input : t) (extra : Extra.t):
    BranchEqualCoreCols.t NUM_LIMBS :=
  {|
    BranchEqualCoreCols.a := Array.to_limbs NUM_LIMBS input.(a);
    BranchEqualCoreCols.b := Array.to_limbs NUM_LIMBS input.(b);
    BranchEqualCoreCols.cmp_result := extra.(Extra.cmp_result);
    BranchEqualCoreCols.imm := input.(imm);
    BranchEqualCoreCols.opcode_beq_flag :=
      match input.(opcode) with
      | BranchEqualOpcode.BEQ => 1
      | BranchEqualOpcode.BNE => 0
      end;
    BranchEqualCoreCols.opcode_bne_flag :=
      match input.(opcode) with
      | BranchEqualOpcode.BEQ => 0
      | BranchEqualOpcode.BNE => 1
      end;
    BranchEqualCoreCols.diff_inv_marker :=
      Array.to_limbs NUM_LIMBS extra.(Extra.diff_inv_marker);
  |}.
End Input.

Module Output.
  Record t : Set := {
    to_pc : Z;
    reads : Z * Z;
    writes : unit;
    instruction : ImmInstruction.t;
  }.

  Definition to_adapter_air_context {NUM_LIMBS : Z} (output : t) :
    AdapterAirContext.t NUM_LIMBS :=
  {|
    AdapterAirContext.to_pc := Some output.(to_pc);
    AdapterAirContext.reads :=
      let '(a, b) := output.(reads) in
      (Array.to_limbs NUM_LIMBS a, Array.to_limbs NUM_LIMBS b);
    AdapterAirContext.writes := output.(writes);
    AdapterAirContext.instruction := output.(instruction);
  |}.

  Definition of_input 
    (* TODO: change to arbitary prime in the future *)
    (* {p} `{Prime p}  *)
    `{Prime 23}
    (core_air : BranchEqualCoreAir.t) (input : Input.t) 
    (extra : Input.Extra.t) (from_pc : Z) : t := {|
    to_pc :=
      let cmp_result := extra.(Input.Extra.cmp_result) in
      ((from_pc + (cmp_result * input.(Input.imm)) mod 23
       + (not cmp_result) * core_air.(BranchEqualCoreAir.pc_step)
       ) mod 23);
      (* match input.(Input.opcode) with
      | BranchEqualOpcode.BEQ =>
        if input.(Input.a) =? input.(Input.b) then
          from_pc + input.(Input.imm)
        else
        from_pc + core_air.(BranchEqualCoreAir.pc_step)
      | BranchEqualOpcode.BNE =>
        if negb (input.(Input.a) =? input.(Input.b)) then
          from_pc + input.(Input.imm)
        else
          from_pc + 4
      end; *)
    reads := (input.(Input.a), input.(Input.b));
    writes := tt;
    instruction := {|
      ImmInstruction.is_valid := 1;
      ImmInstruction.opcode :=
        ((match input.(Input.opcode) with
        | BranchEqualOpcode.BEQ => 0
        | BranchEqualOpcode.BNE => 1
        end) mod 23
        + core_air.(BranchEqualCoreAir.offset)) mod 23;
      ImmInstruction.immediate := input.(Input.imm);
    |};
  |}.
End Output.

Smpl Create run_auto.

Axiom assert_bool_zero :
  {{ M.AssertBool 0 🔽 tt, True }}.
Smpl Add apply assert_bool_zero : run_auto.

Axiom assert_bool_one :
  {{ M.AssertBool 1 🔽 tt, True }}.
Smpl Add apply assert_bool_one : run_auto.

Lemma eval_is_valid `{Prime 23} {NUM_LIMBS : Z}
    (core_air : BranchEqualCoreAir.t)
    (input : Input.t)
    (extra : Input.Extra.t)
    (from_pc : Z) :
  let cols : BranchEqualCoreCols.t NUM_LIMBS := Input.to_cols input extra in
  let output : AdapterAirContext.t NUM_LIMBS :=
    Output.to_adapter_air_context (Output.of_input core_air input extra from_pc) in
  {{ eval core_air cols from_pc 🔽 output, True }}.
Proof.
  cbn.
  eapply Run.Implies. {
    unfold eval; cbn.
    eapply Run.Let with (value := 1) (P1 := True). {
      destruct input.(Input.opcode); cbn.
      { eapply Run.Implies. {
          repeat (
            (eapply Run.Let; [|intro]) ||
            smpl run_auto ||
            apply Run.Pure
          ).
        }
        tauto.
      }
      { eapply Run.Implies. {
          repeat (
            (eapply Run.Let; [|intro]) ||
            smpl run_auto ||
            apply Run.Pure
          ).
        }
        tauto.
      }
    }
    intros [].
    eapply Run.Let. { smpl run_auto. }
    intros [].
    eapply Run.Let. { apply Run.AssertBool. }
    intros [cmp_result H_cmp_result_eq].
    rewrite H_cmp_result_eq.
    set (cmp_eq :=
      match input.(Input.opcode) with
      | BranchEqualOpcode.BEQ => cmp_result
      | BranchEqualOpcode.BNE => negb cmp_result
      end
    ).
    (* match goal with
    | |- context[M.pure ?e] =>
      set (cmp_eq := e)
    end. *)
    eapply Run.Let with (value := Z.b2z cmp_eq). {
      destruct input.(Input.opcode), cmp_result; apply Run.Pure.
    }
    intros [].
    eapply Run.Implies. 
    {
      (* NOTE: here we specify a property to prove for the `Let` clause *)
      eapply Run.Let with
        (P1 :=
          if cmp_eq then
            forall i, 0 <= i < NUM_LIMBS ->
              Array.get_mod (Array.to_limbs NUM_LIMBS input.(Input.a)) i =
              Array.get_mod (Array.to_limbs NUM_LIMBS input.(Input.b)) i
          else
            True
        ). 
      { 
        destruct cmp_eq; cbn.
        { 
          apply Run.ForInZeroToN; intros.
          unfold assert_zero.
          repeat destruct Array.to_limbs. 
          eapply Run.Implies with (P1 := 
            (BinOp.mul 1 (BinOp.sub (get i) (get0 i))) = 0
          ).
          { apply Run.Equal. }
          { unfold BinOp.mul, BinOp.sub.
            rewrite -> Z.mul_1_l.
            rewrite -> foo_mod_mod.
            rewrite <- foo_sub.
            apply foo_eq_sub. }
        }
        (* NOTE: `else` case for `cmp_eq`. We don't want to prove anything here,
          so we want to stub the proof with a `True`. This `True` should be obtained
          by constructing a combination of trivial cases for all constructors appeared
          in the part of the program. 
          Applying `Run.Implies` allows the constructors being used to automatically
          generate such a case.
        *)
        { 
          eapply Run.Implies.
          (* Using the constructors *)
          { apply Run.ForInZeroToN; intros.
            apply Run.Equal. }
          (* The generated case *)
          { trivial. } 
        }
      }
      intros H_a_b_eq.
      (* Enforced by our current definition on Input *)
      set (is_valid := true).
      set (sum := M.sum_for_in_zero_to_n NUM_LIMBS (fun i =>
        BinOp.mul 
          (Array.get ((Array.to_limbs NUM_LIMBS extra.(Input.Extra.diff_inv_marker))) i) 
          (BinOp.sub 
            (Array.get (Array.to_limbs NUM_LIMBS input.(Input.a)) i)
            (Array.get (Array.to_limbs NUM_LIMBS input.(Input.b)) i))
      )).
      eapply Run.Let with (P1 :=
        if is_valid then BinOp.add sum (Z.b2z cmp_eq) = 1 else True
      ).
      { unfold assert_one, when, sum.
        unfold BinOp.add, BinOp.sub, BinOp.mul.
        repeat destruct Array.to_limbs.
        eapply Run.Implies.
        simpl.
        { apply Run.Equal. }
        { trivial. }
      }
      intros H_valid_sum_1.
      {
        unfold BinOp.add, BinOp.sub, BinOp.mul.
        unfold Output.to_adapter_air_context, Output.of_input.
        rewrite -> foo_add, H_cmp_result_eq.
        rewrite -> foo_mul_0.
        rewrite -> Z.mul_1_r.
        simpl.
        rewrite -> foo_mod_mod.
        apply Run.Pure.
      }
    }
    intros.
      }
      { admit.
      }
      
Admitted.
(*
        apply Run.Equal.
        eapply Run.Let. {
          smpl run_auto.
        }
      }
      { admit. }
    }

    eapply Run.Implies. {
    eapply Run.Let with
        (value := if cmp_eq then 1 else 0)
        (P1 :=
          if cmp_eq then
            forall (i : nat),
              (0 <= i < NUM_LIMBS)%nat ->
              (Array.to_limbs (Z.of_nat NUM_LIMBS) input.(Input.a)).(Array.get) (Z.of_nat i) =
              (Array.to_limbs (Z.of_nat NUM_LIMBS) input.(Input.b)).(Array.get) (Z.of_nat i)
          else
            False
        ). {
      destruct cmp_eq; cbn.
      { rewrite Nat2Z.id.
        induction NUM_LIMBS; cbn.
        { admit. }
        { eapply Run.Implies. {
          eapply Run.Let. {
            apply IHNUM_LIMBS.
        }
      admit. }
      { admit. }
    }
    intros [].
    eapply Run.Let. {
      smpl run_auto.
    }
    intros [].
    eapply Run.Let. {
      smpl run_auto.
    }
    intros [].
    eapply Run.Let. {
        { repeat (
            eapply Run.Let ||
            eapply Run.AssertBool ||
            apply Run.Pure
          ).
          unfold BinOp.add, BinOp.mul; cbn.
          assert (H_1_eq : 1 mod p = 1) by admit.
          repeat (rewrite H_1_eq; cbn).
          apply Run.Pure.
        }
        reflexivity.
        eapply Run.Replace; [apply Run.Pure |].
        unfold BinOp.add, BinOp.mul.
        cbn.
        assert (H_1_eq : 1 mod p = 1) by admit.
        repeat (rewrite H_1_eq; cbn).
        reflexivity.
      }
      { repeat (
          eapply Run.Let ||
          eapply Run.Equal ||
          apply Run.Pure
        ).
        eapply Run.Replace; [apply Run.Pure |].
        unfold BinOp.add, BinOp.mul.
        cbn.
        assert (H_1_eq : 1 mod p = 1) by admit.
        repeat (rewrite H_1_eq; cbn).
        reflexivity.
      }
      unfold assert_bool.
  }
Qed.
*)
