(** * Full-width scalar range conjuncts of [ProtocolTypedInputs].

    Under [Holds Γ], each of the three full-width fixed-base scalars read by
    [read_action_inputs] — [in_alpha], [in_rcv], [in_rcm_new] — lies in the
    85-window domain [0, 8^85).  Each scalar is [read_scalar_from_windows]
    over its incomplete region: the per-window range [0 <= w < 8] is the
    full-width fixed-base gate's window constraint at that region's facts
    ([OrchardActionFixedBase.full_width_incomplete_region_windows_range] with
    the region's facts extractor from [circuit_proof/us_free/main.v] and
    [holds_gates]), and the base-8 reconstruction of 85 in-range windows is
    bounded by [8^85] ([scalar_from_windows_range]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module TypedInputsFullWidth.
  Import OrchardActionInputs.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The base-8 window reconstruction of pointwise in-range windows is
      bounded by the window count's power of 8. *)
  Lemma scalar_from_windows_range (windows : list Z) :
    List.Forall (fun w => 0 <= w < 8) windows ->
    0 <= scalar_from_windows windows < 8 ^ Z.of_nat (List.length windows).
  Proof.
    induction windows as [| w windows IH]; intros Hbounded.
    - unfold scalar_from_windows.
      cbn [scalar_from_windows_aux List.length].
      change (8 ^ Z.of_nat 0) with 1.
      lia.
    - inversion Hbounded as [| ? ? Hw Htail]; subst.
      specialize (IH Htail).
      rewrite scalar_from_windows_cons.
      cbn [List.length].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      clear -Hw IH.
      lia.
  Qed.

  Lemma read_windows_length
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (count : nat) :
    List.length (read_windows Γ region count) = count.
  Proof.
    unfold read_windows.
    rewrite List.length_map, List.length_seq.
    reflexivity.
  Qed.

  (** The windowed-scalar reader over an 85-window region with in-range
      windows lands in the full-width scalar domain. *)
  Lemma read_scalar_from_windows_85_range
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (Hwindows :
        List.Forall (fun w => 0 <= w < 8) (read_windows Γ region 85)) :
    0 <= read_scalar_from_windows Γ region 85 < 8 ^ 85.
  Proof.
    pose proof (scalar_from_windows_range _ Hwindows) as Hrange.
    rewrite read_windows_length in Hrange.
    change (Z.of_nat 85) with 85 in Hrange.
    unfold read_scalar_from_windows.
    exact Hrange.
  Qed.

  (** ** Per-region window ranges, from [Holds]

      Per base: the region's facts extractor peels the incomplete region's
      fact list out of the synthesized circuit, and the full-width gate's
      window constraint bounds every [A4] window cell. *)

  Lemma alpha_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    List.Forall (fun w => 0 <= w < 8)
      (read_windows Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        85).
  Proof.
    exact (OrchardActionFixedBase.full_width_incomplete_region_windows_range
      Γ
      (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
      _
      (OrchardActionUsFree.spend_auth_g_incomplete_facts Γ Hcircuit)
      (OrchardActionFixedBase.holds_gates Γ Hcircuit)).
  Qed.

  Lemma rcv_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    List.Forall (fun w => 0 <= w < 8)
      (read_windows Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete)
        85).
  Proof.
    exact (OrchardActionFixedBase.full_width_incomplete_region_windows_range
      Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete)
      _
      (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
      (OrchardActionFixedBase.holds_gates Γ Hcircuit)).
  Qed.

  Lemma rcm_new_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    List.Forall (fun w => 0 <= w < 8)
      (read_windows Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        85).
  Proof.
    exact (OrchardActionFixedBase.full_width_incomplete_region_windows_range
      Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete)
      _
      (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
      (OrchardActionFixedBase.holds_gates Γ Hcircuit)).
  Qed.

  (** ** The three full-width conjuncts of [ProtocolTypedInputs] *)

  Theorem in_alpha_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <= OrchardSpec.in_alpha (read_action_inputs Γ) < 8 ^ 85.
  Proof.
    unfold read_action_inputs, read_action_inputs_with_anchor.
    cbn [OrchardSpec.in_alpha].
    apply read_scalar_from_windows_85_range.
    exact (alpha_windows_range Γ Hcircuit).
  Qed.

  Theorem in_rcv_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <= OrchardSpec.in_rcv (read_action_inputs Γ) < 8 ^ 85.
  Proof.
    unfold read_action_inputs, read_action_inputs_with_anchor.
    cbn [OrchardSpec.in_rcv].
    apply read_scalar_from_windows_85_range.
    exact (rcv_windows_range Γ Hcircuit).
  Qed.

  Theorem in_rcm_new_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <= OrchardSpec.in_rcm_new (read_action_inputs Γ) < 8 ^ 85.
  Proof.
    unfold read_action_inputs, read_action_inputs_with_anchor.
    cbn [OrchardSpec.in_rcm_new].
    apply read_scalar_from_windows_85_range.
    exact (rcm_new_windows_range Γ Hcircuit).
  Qed.
End TypedInputsFullWidth.
