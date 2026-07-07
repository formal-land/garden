(** Determinism of the Poseidon hash chip as used by the Orchard nullifier
    derivation ([synthesize_hash nk rho_old], [Halo2.halo2_gadgets.poseidon
    .pow5]).  Seed/absorb: pin the initial state to the
    [ConstantLength<2>] domain constants ({0, 0, 2^65}, a
    [CellIsConstant] descent from the synthesis [ConstrainConstant] facts)
    and apply [PadAndAdd.deterministic] once to
    read off the absorbed state — [nk], [rho_old] and the capacity constant —
    at offset 0 of the [PermuteState] region, before any round is run.
    Per-row facts and round chain: fold the 36 schedule rows of
    [permutation_rows] into [Poseidon.permute] by symbolic induction.
    Assembly: the hash output cell — advice A6 at [PermuteState] row
    36 — equals [poseidon_hash2 nk rho_old]
    ([poseidon_hash_cell_correct] / [poseidon_hash_value_correct]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Garden.Halo2.halo2_gadgets.poseidon.pow5.
Require Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.
Global Open Scope Z_scope.

Module OrchardPoseidon.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The three Poseidon regions touched by the seed/absorb steps: the
      constant initial state, the add-input (pad-and-add) region, and the
      permutation region (only its copy-in row 0 is used here — the round
      chain is handled separately below). *)
  Definition init_region : RegionId.t :=
    RegionId.Poseidon RegionId.Poseidon.InitialState.
  Definition add_input_region : RegionId.t :=
    RegionId.Poseidon RegionId.Poseidon.AddInput.
  Definition permute_region : RegionId.t :=
    RegionId.Poseidon RegionId.Poseidon.PermuteState.

  (** The two Poseidon input cells for the nullifier's
      [synthesize_hash nk rho_old]: definitionally
      [Cell.advice (RegionId.WitnessInput Nk/RhoOld) Advice.A0 0], matching
      the free-witness cells threaded through [circuit.synthesize_nullifier]. *)
  Definition nk_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    layouter_value
      (Garden.Orchard.circuit.assign_free_advice
        (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.Nk)
        "witness nk" Advice.A0 0).

  Definition rho_old_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    layouter_value
      (Garden.Orchard.circuit.assign_free_advice
        (Garden.Orchard.circuit.witness_input_region
          RegionId.WitnessInput.RhoOld)
        "witness rho_old" Advice.A0 0).

  (** The three state lanes at [row] of [region], as reduced expression
      evaluations (advice A6/A7/A8, [pow5.v] layout). *)
  Definition state_at_row
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) : State.t := {|
    State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row);
    State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row);
    State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row);
  |}.

  (** Row-arithmetic twins of [eval_advice_cur_cell] for the [next]/[prev]
      rotations, used to normalize [PadAndAdd.deterministic]'s rotated
      lookups to concrete row offsets. *)
  Lemma eval_advice_next_add_1
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.next ⟧ (region, row) =
    Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row + 1).
  Proof.
    change (eval_expression Γ (region, row)
        (Expression.Advice column Rotation.next) =
      eval_expression Γ (region, row + 1)
        (Expression.Advice column Rotation.cur)).
    unfold eval_expression, rotated_row, Rotation.next, Rotation.cur.
    cbn.
    do 2 f_equal.
    lia.
  Qed.

  Lemma eval_advice_prev_sub_1
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.prev ⟧ (region, row) =
    Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row - 1).
  Proof.
    change (eval_expression Γ (region, row)
        (Expression.Advice column Rotation.prev) =
      eval_expression Γ (region, row - 1)
        (Expression.Advice column Rotation.cur)).
    unfold eval_expression, rotated_row, Rotation.prev, Rotation.cur.
    cbn.
    do 2 f_equal.
    lia.
  Qed.

  (** A [read]-value (already [UnOp.from]-wrapped) is idempotent under a
      further [UnOp.from]. *)
  Lemma from_read
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) :
    UnOp.from (read Γ region) = read Γ region.
  Proof.
    unfold read, read_advice.
    change (UnOp.from
        (eval_expression Γ (region, 0)
          (Expression.Advice Advice.A0 Rotation.cur)) =
      eval_expression Γ (region, 0)
        (Expression.Advice Advice.A0 Rotation.cur)).
    cbn [eval_expression].
    apply FieldRewrite.from_from.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Facts descent: from [Holds Γ] down to the three Poseidon regions.  *)
  (* ------------------------------------------------------------------ *)

  (** Descend from the whole-circuit facts to the facts established by
      [pow5.synthesize_hash nk_cell rho_old_cell] — the Poseidon hash call
      inside [circuit.synthesize_nullifier].  Mirrors [nullifier_facts]
      ([circuit_proof/facts.v]), continued two more binds into
      [synthesize_nullifier]'s body. *)
  Lemma poseidon_hash_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
          nk_cell rho_old_cell)).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_nullifier in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** The seed constants: the [InitialState] region's three [ConstrainConstant]
      facts for the [ConstantLength<2>] domain — rate words 0, capacity word
      [2^65]. *)
  Lemma poseidon_init_state_constants
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A6 0)
      = 0 /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A7 0)
      = 0 /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A8 0) =
      Garden.Halo2.halo2_gadgets.poseidon.pow5.initial_capacity_element.
  Proof.
    pose proof (poseidon_hash_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold
      Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_initial_state
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    cbn in Hfacts.
    tauto.
  Qed.

  (** The add-input (pad-and-add) region's facts: the enabled selector at
      offset 1, the three copies-in from the initial state at offset 0, and
      the two copies-in of [nk]/[rho_old] at offset 1. *)
  Lemma poseidon_add_input_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QPoseidonPadAndAdd add_input_region 1
      = 1 /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A6 0) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A6 0)
      /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A7 0) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A7 0)
      /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A8 0) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice init_region Advice.A8 0)
      /\
    eval_cell Γ nk_cell =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A6 1) /\
    eval_cell Γ rho_old_cell =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A7 1).
  Proof.
    pose proof (poseidon_hash_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_sponge
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold
      Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_add_input_region
      in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    cbn in Hfacts.
    tauto.
  Qed.

  (** The permutation region's copy-in at offset 0: it holds the add-input
      region's threaded output state (offset 2). *)
  Lemma poseidon_permute_copy_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice permute_region Advice.A6 0) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A6 2) /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice permute_region Advice.A7 0) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A7 2) /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice permute_region Advice.A8 0) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice add_input_region Advice.A8 2).
  Proof.
    pose proof (poseidon_hash_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_sponge
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_permute_state
      in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn in Hfacts.
    tauto.
  Qed.

  (** [pad_and_add_gate] is one of the three Poseidon gates configured on the
      Orchard circuit ([circuit.configure] calls [pow5.configure], which
      creates exactly [full_round_gate]/[partial_rounds_gate]/
      [pad_and_add_gate], in that order). *)
  Lemma pad_and_add_gate_in_orchard_gates :
    List.In Garden.Halo2.halo2_gadgets.poseidon.pow5.pad_and_add_gate
      (𝓒.run_unit Garden.Orchard.circuit.configure
        ConstraintSystem.empty).(ConstraintSystem.gates).
  Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

  (* ------------------------------------------------------------------ *)
  (* Seed and absorb.                                                   *)
  (* ------------------------------------------------------------------ *)

  (** The absorbed state read off [PermuteState] row 0, before any round is
      run: lane 0 is [nk], lane 1 is [rho_old], lane 2 is the capacity
      constant — derived from the [ConstrainConstant] seed pinning plus
      exactly one application of [PadAndAdd.deterministic] at offset 1 of the
      [AddInput] region. *)
  Theorem poseidon_absorb_state
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    state_at_row Γ permute_region 0 = {|
      State.x0 := read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk);
      State.x1 :=
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld);
      State.x2 :=
        UnOp.from
          Garden.Halo2.halo2_gadgets.poseidon.pow5.initial_capacity_element;
    |}.
  Proof.
    destruct (poseidon_init_state_constants Γ Hcircuit) as (Hi0 & Hi1 & Hi2).
    destruct (poseidon_add_input_facts Γ Hcircuit)
      as (Hpad_sel & Hcp0 & Hcp1 & Hcp2 & Hin0 & Hin1).
    destruct (poseidon_permute_copy_facts Γ Hcircuit) as (Hpc0 & Hpc1 & Hpc2).
    assert (Htransport :
        state_at_row Γ permute_region 0 = state_at_row Γ add_input_region 2).
    {
      unfold state_at_row.
      rewrite (eval_advice_cur_cell Γ permute_region Advice.A6 0), Hpc0,
        <- (eval_advice_cur_cell Γ add_input_region Advice.A6 2).
      rewrite (eval_advice_cur_cell Γ permute_region Advice.A7 0), Hpc1,
        <- (eval_advice_cur_cell Γ add_input_region Advice.A7 2).
      rewrite (eval_advice_cur_cell Γ permute_region Advice.A8 0), Hpc2,
        <- (eval_advice_cur_cell Γ add_input_region Advice.A8 2).
      reflexivity.
    }
    rewrite Htransport.
    pose proof
      (PadAndAdd.deterministic Γ add_input_region 1
        (enabled_nonzero Γ Selector.QPoseidonPadAndAdd add_input_region 1
          Hpad_sel)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.poseidon.pow5.pad_and_add_gate
          add_input_region 1
          pad_and_add_gate_in_orchard_gates
          (holds_gates Γ Hcircuit)))
      as Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A6 add_input_region 1) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A7 add_input_region 1) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A8 add_input_region 1) in Hdet.
    rewrite (eval_advice_prev_sub_1 Γ Advice.A6 add_input_region 1) in Hdet.
    rewrite (eval_advice_prev_sub_1 Γ Advice.A7 add_input_region 1) in Hdet.
    rewrite (eval_advice_prev_sub_1 Γ Advice.A8 add_input_region 1) in Hdet.
    replace (1 + 1) with 2 in Hdet by lia.
    replace (1 - 1) with 0 in Hdet by lia.
    unfold PadAndAdd.output in Hdet.
    rewrite (eval_advice_cur_cell Γ add_input_region Advice.A6 0) in Hdet.
    rewrite (eval_advice_cur_cell Γ add_input_region Advice.A7 0) in Hdet.
    rewrite (eval_advice_cur_cell Γ add_input_region Advice.A8 0) in Hdet.
    rewrite (eval_advice_cur_cell Γ add_input_region Advice.A6 1) in Hdet.
    rewrite (eval_advice_cur_cell Γ add_input_region Advice.A7 1) in Hdet.
    rewrite Hcp0, Hi0 in Hdet.
    rewrite Hcp1, Hi1 in Hdet.
    rewrite Hcp2, Hi2 in Hdet.
    rewrite <- Hin0 in Hdet.
    rewrite <- Hin1 in Hdet.
    rewrite FieldRewrite.from_zero in Hdet.
    rewrite !FieldRewrite.add_zero_left in Hdet.
    rewrite !FieldRewrite.from_from in Hdet.
    unfold state_at_row.
    rewrite Hdet.
    unfold read, read_advice, nk_cell, rho_old_cell.
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Per-row facts: the selector-on and fixed-cell values that each     *)
  (* row of [permutation_rows] assigns, extracted by plain symbolic     *)
  (* induction over the row list (no [vm_compute], no unfolding of the  *)
  (* concrete 36-row schedule). *)
  (* ------------------------------------------------------------------ *)

  (** The permutation region's facts for the whole round-constant
      schedule ([assign_permutation_rows] at offset 0): the second half
      of the [PermuteState] region's program, after the copy-in facts
      already extracted by [poseidon_permute_copy_facts]. *)
  Lemma poseidon_permute_rows_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (region_facts permute_region
        (Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_permutation_rows
          permute_region 0
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .permutation_rows)).
  Proof.
    pose proof (poseidon_hash_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_sponge
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_permute_state
      in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    exact Hfacts.
  Qed.

  (** Interpreting the four facts a full-round row assigns: the selector
      is on, and the three fixed cells hold the round's constants. *)
  Lemma full_round_row_facts_interp
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (r : nat) (n0 n1 n2 : string)
      (Hfacts :
        interpret_facts Γ
          (region_facts region
            (Garden.Halo2.halo2_gadgets.poseidon.pow5
              .assign_round_constant_row offset
              (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
                .full_round_row r n0 n1 n2)))) :
    Γ.(Assignment.selector) Selector.QPoseidonFull region offset = 1 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs2 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 0 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs3 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 1 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs4 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 2.
  Proof.
    cbn
      [Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_round_constant_row
       Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_round_constant_entries
       Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis.full_round_row
       region_facts interpret_facts interpret_fact List.app
       Monad.bind Monad.ret Garden.Halo2.Synthesis.RegionIsMonad]
      in Hfacts.
    tauto.
  Qed.

  (** Interpreting the seven facts a partial-round row assigns: the
      selector is on, and the six fixed cells hold the two packed
      rounds' constants. *)
  Lemma partial_round_row_facts_interp
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (ra rb : nat)
      (na0 na1 na2 nb0 nb1 nb2 : string)
      (Hfacts :
        interpret_facts Γ
          (region_facts region
            (Garden.Halo2.halo2_gadgets.poseidon.pow5
              .assign_round_constant_row offset
              (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
                .partial_round_row ra rb na0 na1 na2 nb0 nb1 nb2)))) :
    Γ.(Assignment.selector) Selector.QPoseidonPartial region offset = 1 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs2 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 0 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs3 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 1 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs4 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 2 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs5 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 0 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs6 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 1 /\
    Γ.(Assignment.fixed) Fixed.LagrangeCoeffs7 region offset =
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 2.
  Proof.
    cbn
      [Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_round_constant_row
       Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_round_constant_entries
       Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
         .partial_round_row
       region_facts interpret_facts interpret_fact List.app
       Monad.bind Monad.ret Garden.Halo2.Synthesis.RegionIsMonad]
      in Hfacts.
    tauto.
  Qed.

  (** The per-row fact interpretation lifts along the whole schedule by
      plain symbolic induction on the row list: no [vm_compute], no
      unfolding of the concrete 36-row literal — just [List.nth_error]
      indexing into an arbitrary [rows]/[offset] pair, so the same proof
      covers every row uniformly. *)
  Lemma assign_permutation_rows_facts_chain
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (rows :
        list
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .round_constant_row) :
    forall (offset : Z),
      interpret_facts Γ
        (region_facts region
          (Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_permutation_rows
            region offset rows)) ->
      forall (n : nat)
        (row :
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .round_constant_row),
        List.nth_error rows n = Some row ->
        interpret_facts Γ
          (region_facts region
            (Garden.Halo2.halo2_gadgets.poseidon.pow5
              .assign_round_constant_row (offset + Z.of_nat n) row)).
  Proof.
    induction rows as [| row' rows IH]; intros offset Hfacts n row Hnth.
    - destruct n; cbn in Hnth; discriminate.
    - cbn
        [Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_permutation_rows]
        in Hfacts.
      pose proof Hfacts as Htail.
      apply interpret_region_facts_bind_left in Hfacts.
      apply interpret_region_facts_bind_right in Htail.
      destruct n as [| n].
      + cbn [List.nth_error] in Hnth.
        injection Hnth as Hnth.
        subst row.
        replace (offset + Z.of_nat 0) with offset by lia.
        exact Hfacts.
      + cbn [List.nth_error] in Hnth.
        specialize (IH (offset + 1) Htail n row Hnth).
        replace (offset + Z.of_nat (S n)) with (offset + 1 + Z.of_nat n)
          by lia.
        exact IH.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The round chain: fold the 36 schedule rows (8 FullRound + 28       *)
  (* PartialRound deterministic steps) along the [PermuteState] region,  *)
  (* keeping every intermediate state as a nested [FullRound.output]/    *)
  (* [PartialRound.output] application (the S-box is never unfolded).    *)
  (* ------------------------------------------------------------------ *)

  Import ListNotations.

  (** [full_round_gate] and [partial_rounds_gate] are among the gates
      configured on the Orchard circuit (the other two of the three
      Poseidon gates besides [pad_and_add_gate]). *)
  Lemma full_round_gate_in_orchard_gates :
    List.In Garden.Halo2.halo2_gadgets.poseidon.pow5.full_round_gate
      (𝓒.run_unit Garden.Orchard.circuit.configure
        ConstraintSystem.empty).(ConstraintSystem.gates).
  Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

  Lemma partial_rounds_gate_in_orchard_gates :
    List.In Garden.Halo2.halo2_gadgets.poseidon.pow5.partial_rounds_gate
      (𝓒.run_unit Garden.Orchard.circuit.configure
        ConstraintSystem.empty).(ConstraintSystem.gates).
  Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

  (** [from]-absorption on the round-constant arguments of the round
      outputs: the gate lemmas deliver constants as [UnOp.from]-wrapped
      fixed-cell evaluations, while the spec fold uses the raw constants.
      Only the [+F] spines exposed by unfolding [output] (and the [let]
      in the partial case) are touched — [pow5]/[mds_mul]/[sbox_partial]
      stay folded. *)
  Lemma full_round_output_from (s0 s1 s2 c0 c1 c2 : Z) :
    FullRound.output s0 s1 s2 (UnOp.from c0) (UnOp.from c1) (UnOp.from c2) =
    FullRound.output s0 s1 s2 c0 c1 c2.
  Proof.
    unfold FullRound.output, FullRound.output_coordinate.
    cbv zeta.
    now rewrite !FieldRewrite.add_from_right.
  Qed.

  Lemma partial_round_output_from (s0 s1 s2 a0 a1 a2 b0 b1 b2 : Z) :
    PartialRound.output s0 s1 s2
      (UnOp.from a0) (UnOp.from a1) (UnOp.from a2)
      (UnOp.from b0) (UnOp.from b1) (UnOp.from b2) =
    PartialRound.output s0 s1 s2 a0 a1 a2 b0 b1 b2.
  Proof.
    unfold PartialRound.output.
    cbv zeta.
    now rewrite !FieldRewrite.add_from_right.
  Qed.

  (** One schedule row as a state transition, read off the row's stored
      constants.  On [full_round_row r _ _ _] this is definitionally
      [Poseidon.apply_full r]; on [partial_round_row ra rb …] it is
      [Poseidon.apply_partial ra rb]. *)
  Definition row_transition
      (row :
        Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
          .round_constant_row)
      (s : State.t) : State.t :=
    match row with
    | (Selector.QPoseidonFull, [(_, _, c0); (_, _, c1); (_, _, c2)]) =>
        FullRound.output s.(State.x0) s.(State.x1) s.(State.x2) c0 c1 c2
    | (Selector.QPoseidonPartial,
       [(_, _, a0); (_, _, a1); (_, _, a2);
        (_, _, b0); (_, _, b1); (_, _, b2)]) =>
        PartialRound.output s.(State.x0) s.(State.x1) s.(State.x2)
          a0 a1 a2 b0 b1 b2
    | _ => s
    end.

  Definition fold_rows
      (rows :
        list
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .round_constant_row)
      (s : State.t) : State.t :=
    Lists.List.fold_left (fun s row => row_transition row s) rows s.

  Lemma fold_rows_cons
      (row :
        Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
          .round_constant_row)
      (rows :
        list
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .round_constant_row)
      (s : State.t) :
    fold_rows (row :: rows) s = fold_rows rows (row_transition row s).
  Proof. reflexivity. Qed.

  Lemma fold_rows_nil (s : State.t) : fold_rows [] s = s.
  Proof. reflexivity. Qed.

  Lemma row_transition_full
      (r : nat) (n0 n1 n2 : string) (s : State.t) :
    row_transition
      (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .full_round_row r n0 n1 n2) s =
    Poseidon.apply_full r s.
  Proof. reflexivity. Qed.

  Lemma row_transition_partial
      (ra rb : nat) (na0 na1 na2 nb0 nb1 nb2 : string) (s : State.t) :
    row_transition
      (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .partial_round_row ra rb na0 na1 na2 nb0 nb1 nb2) s =
    Poseidon.apply_partial ra rb s.
  Proof. reflexivity. Qed.

  (** Every row of the schedule is a full-round or a partial-round row —
      the shape hypothesis that drives the chain induction. *)
  Inductive RowShape :
      Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .round_constant_row -> Prop :=
  | RowShapeFull (r : nat) (n0 n1 n2 : string) :
      RowShape
        (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
          .full_round_row r n0 n1 n2)
  | RowShapePartial (ra rb : nat) (na0 na1 na2 nb0 nb1 nb2 : string) :
      RowShape
        (Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
          .partial_round_row ra rb na0 na1 na2 nb0 nb1 nb2).

  Lemma permutation_rows_shape :
    List.Forall RowShape
      Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .permutation_rows.
  Proof. repeat constructor. Qed.

  (** Folding the whole 36-row schedule is the P128Pow5T3 permutation:
      the fold is peeled one row at a time, keeping every intermediate
      state as a folded [Poseidon.apply_full]/[Poseidon.apply_partial]
      application (each of which consumes its state argument exactly
      once), so both sides align as the same linear-size 36-deep
      application chain — [apply_full]/[apply_partial]/[output] are
      never unfolded, and the S-box never appears.  (Normalizing with
      [cbv] instead would unfold [output] into three projections of the
      previous state per level — a term of size [3^36].) *)
  Lemma fold_rows_permutation_eq (s : State.t) :
    fold_rows
      Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .permutation_rows s =
    Poseidon.permute s.
  Proof.
    unfold
      Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
        .permutation_rows.
    rewrite !fold_rows_cons.
    rewrite !row_transition_full, !row_transition_partial.
    rewrite fold_rows_nil.
    unfold Poseidon.permute.
    reflexivity.
  Qed.

  (** One full-round circuit step at an arbitrary [(region, row)]: the
      next-row state is [Poseidon.apply_full r] of the current-row state,
      given the row's selector-on and round-constant facts. *)
  Lemma full_round_step
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (r : nat)
      (Hgates : satisfies_gates Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hselector :
        Γ.(Assignment.selector) Selector.QPoseidonFull region row = 1)
      (Hc0 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs2 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 0)
      (Hc1 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs3 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 1)
      (Hc2 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs4 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant r 2) :
    state_at_row Γ region (row + 1) =
      Poseidon.apply_full r (state_at_row Γ region row).
  Proof.
    pose proof
      (FullRound.deterministic Γ region row
        (enabled_nonzero Γ Selector.QPoseidonFull region row Hselector)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.poseidon.pow5.full_round_gate
          region row
          full_round_gate_in_orchard_gates
          Hgates))
      as Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs2 region row _ Hc0)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs3 region row _ Hc1)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs4 region row _ Hc2)
      in Hdet.
    rewrite full_round_output_from in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A6 region row) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A7 region row) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A8 region row) in Hdet.
    unfold Poseidon.apply_full, Poseidon.rc, state_at_row.
    cbn [State.x0 State.x1 State.x2].
    exact Hdet.
  Qed.

  (** One partial-round circuit step (a packed pair of partial rounds) at
      an arbitrary [(region, row)]. *)
  Lemma partial_round_step
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (ra rb : nat)
      (Hgates : satisfies_gates Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hselector :
        Γ.(Assignment.selector) Selector.QPoseidonPartial region row = 1)
      (Ha0 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs2 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 0)
      (Ha1 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs3 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 1)
      (Ha2 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs4 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant ra 2)
      (Hb0 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs5 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 0)
      (Hb1 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs6 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 1)
      (Hb2 : Γ.(Assignment.fixed) Fixed.LagrangeCoeffs7 region row =
        Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant rb 2) :
    state_at_row Γ region (row + 1) =
      Poseidon.apply_partial ra rb (state_at_row Γ region row).
  Proof.
    pose proof
      (PartialRound.deterministic Γ region row
        (enabled_nonzero Γ Selector.QPoseidonPartial region row Hselector)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.poseidon.pow5.partial_rounds_gate
          region row
          partial_rounds_gate_in_orchard_gates
          Hgates))
      as Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs2 region row _ Ha0)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs3 region row _ Ha1)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs4 region row _ Ha2)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs5 region row _ Hb0)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs6 region row _ Hb1)
      in Hdet.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs7 region row _ Hb2)
      in Hdet.
    rewrite partial_round_output_from in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A6 region row) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A7 region row) in Hdet.
    rewrite (eval_advice_next_add_1 Γ Advice.A8 region row) in Hdet.
    unfold Poseidon.apply_partial, Poseidon.rc, state_at_row.
    cbn [State.x0 State.x1 State.x2].
    exact Hdet.
  Qed.

  (** The round chain (the P3 invariant): for every suffix [rows] of the
      schedule laid down starting at [offset], the circuit state read at
      [offset + length rows] is [fold_rows rows] of the state read at
      [offset] — symbolic induction over the shape hypothesis, one
      deterministic step per row, no [vm_compute]. *)
  Lemma assign_permutation_rows_chain
      (Γ : Assignment.t columns RegionId.t)
      (Hgates : satisfies_gates Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (rows :
        list
          Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
            .round_constant_row)
      (Hshape : List.Forall RowShape rows) :
    forall (offset : Z),
      interpret_facts Γ
        (region_facts permute_region
          (Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_permutation_rows
            permute_region offset rows)) ->
      state_at_row Γ permute_region (offset + Z.of_nat (List.length rows)) =
        fold_rows rows (state_at_row Γ permute_region offset).
  Proof.
    induction Hshape as [| row rows Hrow Hrows IH]; intros offset Hfacts.
    - cbn [List.length].
      replace (offset + Z.of_nat 0) with offset by lia.
      reflexivity.
    - cbn
        [Garden.Halo2.halo2_gadgets.poseidon.pow5.assign_permutation_rows]
        in Hfacts.
      pose proof Hfacts as Htail.
      apply interpret_region_facts_bind_left in Hfacts.
      apply interpret_region_facts_bind_right in Htail.
      specialize (IH (offset + 1) Htail).
      cbn [List.length].
      replace (offset + Z.of_nat (S (List.length rows)))
        with (offset + 1 + Z.of_nat (List.length rows)) by lia.
      destruct Hrow as [r n0 n1 n2 | ra rb na0 na1 na2 nb0 nb1 nb2].
      + destruct
          (full_round_row_facts_interp Γ permute_region offset r n0 n1 n2
            Hfacts)
          as (Hsel & Hc0 & Hc1 & Hc2).
        pose proof
          (full_round_step Γ permute_region offset r Hgates
            Hsel Hc0 Hc1 Hc2)
          as Hstep.
        rewrite fold_rows_cons, row_transition_full, <- Hstep.
        exact IH.
      + destruct
          (partial_round_row_facts_interp Γ permute_region offset ra rb
            na0 na1 na2 nb0 nb1 nb2 Hfacts)
          as (Hsel & Ha0 & Ha1 & Ha2 & Hb0 & Hb1 & Hb2).
        pose proof
          (partial_round_step Γ permute_region offset ra rb Hgates
            Hsel Ha0 Ha1 Ha2 Hb0 Hb1 Hb2)
          as Hstep.
        rewrite fold_rows_cons, row_transition_partial, <- Hstep.
        exact IH.
  Qed.

  (** The chain specialized to the whole schedule at offset 0: the state
      at row 36 of the permutation region is [Poseidon.permute] of the
      state at row 0 — ready for the assembly with
      [poseidon_absorb_state]. *)
  Lemma permute_state_row36
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    state_at_row Γ permute_region 36 =
      Poseidon.permute (state_at_row Γ permute_region 0).
  Proof.
    pose proof
      (assign_permutation_rows_chain Γ (holds_gates Γ Hcircuit)
        Garden.Halo2.halo2_gadgets.poseidon.p128pow5t3_synthesis
          .permutation_rows
        permutation_rows_shape 0
        (poseidon_permute_rows_facts Γ Hcircuit))
      as Hchain.
    rewrite fold_rows_permutation_eq in Hchain.
    exact Hchain.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Assembly: identify the A6 output cell at [PermuteState] row 36      *)
  (* with the spec-level [poseidon_hash2] of the two witness inputs.     *)
  (* ------------------------------------------------------------------ *)

  (** The circuit's capacity seed is the [ConstantLength<2>] domain
      constant of the spec ([2 ^ 65 = 2 * 2 ^ 64]). *)
  Lemma initial_capacity_element_eq :
    Garden.Halo2.halo2_gadgets.poseidon.pow5.initial_capacity_element =
    Poseidon.domain_iv_constant_length_2.
  Proof. reflexivity. Qed.

  (** [from]-absorption on the seed state: only the first full round sees
      the seed record, and its lanes enter as the left operands of the
      round-constant additions. *)
  Lemma apply_full_from (r : nat) (x0 x1 x2 : Z) :
    Poseidon.apply_full r
      {| State.x0 := UnOp.from x0; State.x1 := UnOp.from x1;
         State.x2 := UnOp.from x2 |} =
    Poseidon.apply_full r {| State.x0 := x0; State.x1 := x1; State.x2 := x2 |}.
  Proof.
    unfold Poseidon.apply_full.
    cbn [State.x0 State.x1 State.x2].
    unfold FullRound.output, FullRound.output_coordinate.
    cbv zeta.
    now rewrite !FieldRewrite.add_from_left.
  Qed.

  (** Seed-reduction glue: the [UnOp.from]-wrapped seed state and the raw
      seed state permute to the same value — the single [apply_full_from]
      rewrite fires on the innermost round, after which both chains are
      syntactically equal. *)
  Lemma permute_seed_from (x y : Z) :
    Poseidon.permute {|
      State.x0 := UnOp.from x;
      State.x1 := UnOp.from y;
      State.x2 := UnOp.from Poseidon.domain_iv_constant_length_2;
    |} =
    Poseidon.permute {|
      State.x0 := x;
      State.x1 := y;
      State.x2 := Poseidon.domain_iv_constant_length_2;
    |}.
  Proof.
    unfold Poseidon.permute.
    cbv zeta.
    now rewrite apply_full_from.
  Qed.

  (** The capstone: the hash output cell — advice A6 at row 36 of the
      [PermuteState] region — carries [poseidon_hash2 nk rho_old], for any
      assignment satisfying the Orchard circuit. *)
  Theorem poseidon_hash_cell_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (permute_region, 36) =
      Poseidon.poseidon_hash2
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)).
  Proof.
    pose proof (permute_state_row36 Γ Hcircuit) as Hchain.
    rewrite (poseidon_absorb_state Γ Hcircuit) in Hchain.
    rewrite <- (from_read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.Nk)) in Hchain.
    rewrite <- (from_read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)) in Hchain.
    rewrite initial_capacity_element_eq in Hchain.
    rewrite permute_seed_from in Hchain.
    unfold Poseidon.poseidon_hash2.
    rewrite <- Hchain.
    reflexivity.
  Qed.

  (** The output cell of [synthesize_hash] is A6 at [PermuteState] offset
      36, for any input cells (the layouter value is input-independent) —
      the hook that lets clients holding
      [layouter_value (synthesize_hash …)] land on the capstone cell. *)
  Lemma poseidon_hash_output_cell
      (input_0 input_1 : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    layouter_value
      (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
        input_0 input_1) =
    Garden.Halo2.Synthesis.Cell.advice permute_region Advice.A6 36.
  Proof. reflexivity. Qed.

  (** Client-facing form: the [UnOp.from]-wrapped evaluation of the
      [synthesize_hash] output cell is [poseidon_hash2 nk rho_old]. *)
  Lemma poseidon_hash_value_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (input_0 input_1 : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
            input_0 input_1))) =
    Poseidon.poseidon_hash2
      (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
      (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)).
  Proof.
    rewrite poseidon_hash_output_cell.
    rewrite <- (eval_advice_cur_cell Γ permute_region Advice.A6 36).
    exact (poseidon_hash_cell_correct Γ Hcircuit).
  Qed.

End OrchardPoseidon.
