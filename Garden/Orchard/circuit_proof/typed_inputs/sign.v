(** * Typed inputs: the witnessed sign is [1] or [pallas_p - 1] under [Holds]

    The sign input of the value commitment ([OrchardSpec.in_sign], read from
    advice [A9] of the [SignRangeCheck] region) satisfies the sign conjunct of
    [OrchardProtocolEquiv.ProtocolTypedInputs] on any satisfying assignment.

    Route.  [ValueCommitVOut.value_commit_v_short_mul_facts]
    ([circuit_proof/value_commit_v/out.v]) exposes the facts of the whole
    short-mul program; its MSB region copies the [SignRangeCheck] [A9] cell
    onto [A4] of the sign row and enables [QMulFixedShort] there, so
    [ShortFixedBaseStructure.short_fixed_base_mul_sign_square]
    ([circuit_proof/fixed_base/short.v]) yields [s *F s = 1] for the copied
    sign value.  The cell is an expression evaluation, hence reduced mod
    [pallas_p]; the field case split [sqrt_one_val] ([Field/Sqrt.v], prime
    zero-product on [(s - 1) * (s + 1)]) then pins [s] to [1] or
    [pallas_p - 1]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.fixed_base.short.
Require Import Garden.Orchard.circuit_proof.value_commit_v.out.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module TypedInputsSign.
  Import OrchardActionFixedBase.

  (* The consumed short-mul lemmas sit in files whose types mention
     [is_square]/[field_sqrt]/[fixed_window_point_canonical]; keep the chain
     opaque to the conversion oracle ([docs/compile-performance.md]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** [-1] mod the Pallas modulus, as the concrete representative. *)
  Lemma from_neg_one : UnOp.from (-1) = Primes.pallas_p - 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The "sign_check" constraint, landed on the [SignRangeCheck] cell: the
      MSB region of the short fixed-base multiplication copies the sign cell
      onto [A4] of the [QMulFixedShort] row, where the gate squares it to
      one. *)
  Lemma sign_read9_square
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read9 Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck) *F
    read9 Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck) = 1.
  Proof.
    pose proof
      (ValueCommitVOut.value_commit_v_short_mul_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_short_fixed_base_mul in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    unfold Garden.Orchard.circuit
      .synthesize_short_fixed_base_mul_msb_region in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    (* The sign copy: A4 at row 1 of the MSB region holds the
       [SignRangeCheck] cell's value. *)
    pose proof Hfacts as Hcopy_sign.
    apply interpret_region_facts_bind_right in Hcopy_sign.
    apply interpret_region_facts_bind_left in Hcopy_sign.
    cbn [region_facts interpret_facts interpret_fact] in Hcopy_sign.
    destruct Hcopy_sign as [Hcopy_sign _].
    (* The [QMulFixedShort] selector is enabled at row 1. *)
    pose proof Hfacts as Hsel.
    do 3 apply interpret_region_facts_bind_right in Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    cbn [region_facts interpret_facts interpret_fact] in Hsel.
    destruct Hsel as [Hsel _].
    pose proof (enabled_nonzero Γ Selector.QMulFixedShort
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb) 1 Hsel) as Hselector.
    pose proof (satisfies_gates_at Γ
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
        .short_fixed_base_mul_gate
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb) 1
      ltac:(cbn; repeat (first [left; reflexivity | right]))
      (holds_gates Γ Hcircuit)) as Hgate.
    pose proof
      (ShortFixedBaseStructure.short_fixed_base_mul_sign_square Γ
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.ValueCommitVMsb) 1 Hselector Hgate) as Hsq.
    rewrite (eval_advice_cur_cell Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb) Advice.A4 1) in Hsq.
    rewrite Hcopy_sign in Hsq.
    rewrite (assigned_free_advice_value Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.SignRangeCheck)
      "v_net sign" Advice.A9) in Hsq.
    exact Hsq.
  Qed.

  (** The sign cell, as an expression evaluation, is reduced. *)
  Lemma sign_read9_reduced
      (Γ : Assignment.t columns RegionId.t) :
    UnOp.from
      (read9 Γ
        (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck)) =
    read9 Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck).
  Proof.
    unfold read9, read_advice.
    rewrite (eval_advice_cur_cell Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck)
      Advice.A9 0).
    apply from_idem.
  Qed.

  (** The sign case split on the [SignRangeCheck] cell. *)
  Lemma sign_read9_typed
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read9 Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck) = 1 \/
    read9 Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck) =
      Primes.pallas_p - 1.
  Proof.
    pose proof (sqrt_one_val _ (sign_read9_square Γ Hcircuit)) as Hcase.
    rewrite sign_read9_reduced in Hcase.
    rewrite from_neg_one in Hcase.
    exact Hcase.
  Qed.

  (** The sign conjunct of [OrchardProtocolEquiv.ProtocolTypedInputs], from
      [Holds] alone. *)
  Lemma in_sign_typed
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardSpec.in_sign (read_action_inputs Γ) = 1 \/
    OrchardSpec.in_sign (read_action_inputs Γ) = Primes.pallas_p - 1.
  Proof.
    exact (sign_read9_typed Γ Hcircuit).
  Qed.

End TypedInputsSign.
