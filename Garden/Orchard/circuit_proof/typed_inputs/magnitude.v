(** * Typed input: the value_commit_v magnitude range, from [Holds] alone

    The magnitude conjunct of [OrchardProtocolEquiv.ProtocolTypedInputs]:
    [in_magnitude] — [read9] of the [MagnitudeRangeCheck] free-witness cell —
    lies in [0, 8^22).

    Route: the short-mul running sum of [ValueCommitVIncomplete].  The
    region's [Copy] pins [A4[0]] to the magnitude cell
    ([value_commit_v_initial_z]), the strict-tail [ConstrainConstant] pins
    [A4[22]] to zero ([value_commit_v_z_boundary_of_holds]), and the
    running-sum gate bounds each word [z_i - 8·z_{i+1}] in [0, 8)
    ([short_incomplete_region_word_range]).  The integer reconstruction
    [running_sum_zero_tail_reconstruct] ([circuit_proof/fixed_base/main.v])
    telescopes the 22 words below the modulus (8^22 = 2^66 < p): the reduced
    head entry equals the word sum exactly, and the bound follows. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module TypedInputsMagnitude.
  Import OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The magnitude cell — [read9] of [MagnitudeRangeCheck], the source of
      [in_magnitude] — lies in [0, 8^22). *)
  Lemma magnitude_range_check_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <=
      read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck) <
      8 ^ 22.
  Proof.
    rewrite <- (value_commit_v_initial_z Γ Hcircuit).
    pose proof (value_commit_v_incomplete_facts Γ Hcircuit) as Hfacts.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    assert (Hwords :
      forall i : nat,
        (i < 22)%nat ->
        0 <=
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete,
              Z.of_nat i)) -F
            (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.ValueCommitVIncomplete,
                Z.of_nat (S i))) *F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
          8).
    { intros i Hi.
      pose proof
        (short_incomplete_region_word_range Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.value_commitment_region
              RegionId.ValueCommitment.MagnitudeRangeCheck)
            Advice.A9 0)
          i Hfacts Hgates Hi) as Hword.
      rewrite (eval_advice_next_succ Γ Advice.A4
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) i) in Hword.
      exact Hword. }
    assert (Hfit : 8 ^ Z.of_nat 22 < Primes.pallas_p).
    { assert (Hpow : 8 ^ Z.of_nat 22 = 73786976294838206464)
        by reflexivity.
      rewrite Hpow.
      unfold Primes.pallas_p, Primes.t_p.
      lia. }
    destruct
      (running_sum_zero_tail_reconstruct
        (fun n : nat =>
          Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete,
              Z.of_nat n))
        22%nat
        (fun (i : nat) (_ : (i <= 22)%nat) =>
          eval_advice_cur_bounds Γ Advice.A4
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete)
            (Z.of_nat i))
        Hwords
        (value_commit_v_z_boundary_of_holds Γ Hcircuit)
        Hfit
        22%nat 0%nat eq_refl) as [_ Hbound].
    exact Hbound.
  Qed.

  (** The magnitude conjunct of [ProtocolTypedInputs], at the
      [read_action_inputs] spelling consumed by the theorem surface
      ([circuit_proof/main.v]). *)
  Lemma in_magnitude_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <=
      OrchardSpec.in_magnitude (OrchardActionInputs.read_action_inputs Γ) <
      8 ^ 22.
  Proof.
    exact (magnitude_range_check_range Γ Hcircuit).
  Qed.

End TypedInputsMagnitude.
