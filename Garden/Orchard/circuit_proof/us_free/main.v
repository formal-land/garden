(** * Downstream assembly of the per-table witness-elimination legs.

    [OrchardActionInputs.action_spec_us_free_of_table_eqs] reduces the
    witness-elimination lemma [action_spec_us_free] to five per-table
    [fixed_scalar_mul] equalities [Ek]/[Ev]/[Er]/[Ea]/[Ercm] — witnessed
    [u]-list versus canonical [u]-list.  Each equality is an instance of
    [table_us_free_of_oncurve], whose [Hfacts] needs, per window:
    - the on-curve fact for the spec window point at the spec digit, extracted
      from the circuit by the on-curve extraction lemmas of
      [Orchard/circuit_proof/fixed_base/main.v]; and
    - the non-residue discriminant certificates
      [window_disc_qr_*_all_Z].
    Those extraction lemmas live downstream of [circuit_proof/inputs.v] (which is
    a build dependency of [circuit_proof/facts.v] and hence of
    [circuit_proof/fixed_base/main.v]), so the assembly lives here, downstream of
    the fixed-base layer.

    This file discharges four of the five legs:
    - [spend_auth_g_table_eq] ([Ea], scalar [in_alpha]),
    - [value_commit_r_table_eq] ([Er], scalar [in_rcv]),
    - [note_commit_r_table_eq] ([Ercm], scalar [in_rcm_new]),
    - [value_commit_v_table_eq] ([Ev], scalar [in_magnitude]; the
      running-sum final boundary [value_commit_v_z_boundary] ([A4[22] = 0])
      is discharged from [Holds] by [value_commit_v_z_boundary_of_holds] —
      see [circuit_proof/fixed_base/main.v]).

    [action_spec_us_free_of_nullifier_k] then pins the remaining content of
    [action_spec_us_free] to exactly the [Ek] (nullifier_k) leg, whose scalar
    is [poseidon_hash2 nk rho_old +F psi_old] (the base-field sum): [Ek] is
    discharged in [Orchard/circuit_proof/us_free/nullifier_k.v] from Poseidon
    full-permutation soundness plus the base-field running-sum digit match. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.constants.fixed_bases.spend_auth_g.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.disc_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.disc_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.disc_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.disc_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.disc_cert.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module OrchardActionUsFree.
  Import OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* Keep the square-root / QR chain opaque to the conversion oracle: the
     statements below mention [canonical_us_for] (hence [field_sqrt] and
     [fixed_window_point_canonical]) and [is_square] over the concrete Pasta
     modulus, and unfolding [modpow] at the concrete [(p-1)/2] exponent blows
     the term up. *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** [read_us] returns one square-root witness per window. *)
  Lemma read_us_length
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (count : nat) :
    List.length (read_us Γ region count) = count.
  Proof.
    unfold read_us.
    rewrite List.length_map, List.length_seq.
    reflexivity.
  Qed.

  (** Concrete lengths of the three full-width spec tables ([value_commit_v]'s
      is [value_commit_v_table_length] in [circuit_proof/fixed_base/main.v]). *)
  Lemma spend_auth_g_table_length :
    List.length (OrchardCircuitSpec.spend_auth_g orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  Lemma value_commit_r_table_length :
    List.length (OrchardCircuitSpec.value_commit_r orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  Lemma note_commit_r_table_length :
    List.length (OrchardCircuitSpec.note_commit_r orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  (** ** Generic full-width per-window correctness over a whole rows table

      [full_width_incomplete_window_correct] takes the row as
      an explicit nine-entry literal.  The boolean shape check below lets a
      single [vm_compute] certificate per table replace a per-index case
      analysis: every row of the three full-width tables is a standard
      [LagrangeCoeffs0..7; FixedZ] row. *)
  Definition standard_row_shape
      (row : Garden.Orchard.circuit.fixed_base_row) : bool :=
    match row with
    | [(Fixed.LagrangeCoeffs0, _, _); (Fixed.LagrangeCoeffs1, _, _);
       (Fixed.LagrangeCoeffs2, _, _); (Fixed.LagrangeCoeffs3, _, _);
       (Fixed.LagrangeCoeffs4, _, _); (Fixed.LagrangeCoeffs5, _, _);
       (Fixed.LagrangeCoeffs6, _, _); (Fixed.LagrangeCoeffs7, _, _);
       (Fixed.FixedZ, _, _)] => true
    | _ => false
    end%list.

  Lemma spend_auth_g_rows_standard :
    List.forallb standard_row_shape
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_commit_r_rows_standard :
    List.forallb standard_row_shape
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma note_commit_r_rows_standard :
    List.forallb standard_row_shape
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma spend_auth_g_rows_length :
    List.length
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows = 85%nat.
  Proof. reflexivity. Qed.

  Lemma value_commit_r_rows_length :
    List.length
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows = 85%nat.
  Proof. reflexivity. Qed.

  Lemma note_commit_r_rows_length :
    List.length
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows = 85%nat.
  Proof. reflexivity. Qed.

  (** [nth] through [fixed_table_of_rows]: the empty row projects to the empty
      window, so [List.map_nth] applies with default row [nil]. *)
  Lemma fixed_table_of_rows_nth
      (rows : list Garden.Orchard.circuit.fixed_base_row) (i : nat) :
    List.nth i (EccSpec.fixed_table_of_rows rows) fixed_window_default =
    EccSpec.fixed_window_of_row (List.nth i rows nil).
  Proof.
    unfold EccSpec.fixed_table_of_rows.
    exact (List.map_nth EccSpec.fixed_window_of_row rows nil i).
  Qed.

  (** Window correctness at a row known only through its shape bit: the shape
      check pins the row to the nine-entry literal form, exposing the
      annotation/value components [full_width_incomplete_window_correct]
      expects. *)
  Lemma standard_row_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (Hrow : List.nth_error rows i = Some row)
      (Hshape : standard_row_shape row = true)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    incomplete_additions_window_point Γ region (Z.of_nat i) =
    EccSpec.fixed_window_point (EccSpec.fixed_window_of_row row)
      (EccSpec.window_digit (read_scalar_from_windows Γ region 85) i)
      (List.nth i (read_us Γ region 85) 0).
  Proof.
    destruct row as [| ((col0, a0), c0) row]; [discriminate Hshape |].
    destruct col0; try discriminate Hshape.
    destruct row as [| ((col1, a1), c1) row]; [discriminate Hshape |].
    destruct col1; try discriminate Hshape.
    destruct row as [| ((col2, a2), c2) row]; [discriminate Hshape |].
    destruct col2; try discriminate Hshape.
    destruct row as [| ((col3, a3), c3) row]; [discriminate Hshape |].
    destruct col3; try discriminate Hshape.
    destruct row as [| ((col4, a4), c4) row]; [discriminate Hshape |].
    destruct col4; try discriminate Hshape.
    destruct row as [| ((col5, a5), c5) row]; [discriminate Hshape |].
    destruct col5; try discriminate Hshape.
    destruct row as [| ((col6, a6), c6) row]; [discriminate Hshape |].
    destruct col6; try discriminate Hshape.
    destruct row as [| ((col7, a7), c7) row]; [discriminate Hshape |].
    destruct col7; try discriminate Hshape.
    destruct row as [| ((colz, az), z) row]; [discriminate Hshape |].
    destruct colz; try discriminate Hshape.
    destruct row as [| e row]; [| discriminate Hshape].
    rewrite <- incomplete_additions_window_point_map_mod.
    unfold incomplete_additions_window_point.
    exact (full_width_incomplete_window_correct Γ region rows i
      a0 a1 a2 a3 a4 a5 a6 a7 az c0 c1 c2 c3 c4 c5 c6 c7 z
      Hrow Hfacts Hgates Hi).
  Qed.

  (** Per-window correctness against the whole spec table: window [i] of a
      full-width incomplete region equals the spec window point of table entry
      [i] at the region's read-out digit and square-root witness. *)
  Lemma full_width_table_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hshape : List.forallb standard_row_shape rows = true)
      (Hrows_len : List.length rows = 85%nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (i : nat) (Hi : (i < 85)%nat) :
    incomplete_additions_window_point Γ region (Z.of_nat i) =
    EccSpec.fixed_window_point
      (List.nth i (EccSpec.fixed_table_of_rows rows) fixed_window_default)
      (EccSpec.window_digit (read_scalar_from_windows Γ region 85) i)
      (List.nth i (read_us Γ region 85) 0).
  Proof.
    rewrite fixed_table_of_rows_nth.
    apply (standard_row_window_correct Γ region rows i (List.nth i rows nil)).
    - apply List.nth_error_nth'. lia.
    - eapply List.forallb_forall; [exact Hshape |].
      apply List.nth_In. lia.
    - exact Hfacts.
    - exact Hgates.
    - exact Hi.
  Qed.

  (** On-curve fact at the spec digit, in the [Hfacts] shape consumed by
      [table_us_free_of_oncurve], for any standard full-width table. *)
  Lemma full_width_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hshape : List.forallb standard_row_shape rows = true)
      (Hrows_len : List.length rows = 85%nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i (EccSpec.fixed_table_of_rows rows) fixed_window_default)
        (EccSpec.window_digit (read_scalar_from_windows Γ region 85) i)
        (List.nth i (read_us Γ region 85) 0)).
  Proof.
    pose proof
      (full_width_incomplete_region_window_on_curve Γ region rows i
        Hfacts Hgates Hi) as Honc.
    rewrite (full_width_table_window_correct Γ region rows Hshape Hrows_len
      Hfacts Hgates i Hi) in Honc.
    exact Honc.
  Qed.

  (** ** Facts of the three full-width incomplete regions, peeled from [Holds] *)

  Lemma spend_auth_g_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
          Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows)).
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma value_commit_r_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitRIncomplete)
          Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows)).
  Proof.
    pose proof (value_commitment_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.synth_value_commit_r_mul
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** The new-note commitment's blind region, in [note_commit.v]'s own
      synthesizer form. *)
  Lemma note_commit_r_incomplete_facts_raw
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.note_commit
          .synth_note_commit_r_mul_incomplete
          (Garden.Orchard.circuit.note_commit.note_commit_region
            RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete))).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_new in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.note_commit
      .synthesize_full_fixed_base_mul_note_commit_r in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** [note_commit.v]'s region synthesizer is a verbatim copy of [circuit.v]'s
      [synth_full_mul_incomplete_with_rows] over its own
      helper constants (only the [FullFixedResult] return type differs, which
      the fact list does not mention), so the two emitted fact lists are
      computationally equal. *)
  Lemma note_commit_r_incomplete_facts_eq :
    layouter_facts
      (Garden.Orchard.circuit.note_commit
        .synth_note_commit_r_mul_incomplete
        (Garden.Orchard.circuit.note_commit.note_commit_region
          RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)) =
    layouter_facts
      (Garden.Orchard.circuit
        .synth_full_mul_incomplete_with_rows
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows).
  Proof. reflexivity. Qed.

  Lemma note_commit_r_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete)
          Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows)).
  Proof.
    pose proof (note_commit_r_incomplete_facts_raw Γ Hcircuit) as Hfacts.
    rewrite note_commit_r_incomplete_facts_eq in Hfacts.
    exact Hfacts.
  Qed.

  (** ** On-curve facts at the spec digit, per table *)

  Lemma spend_auth_g_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
          fixed_window_default)
        (EccSpec.window_digit
          (read_scalar_from_windows Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete)
            85)
          i)
        (List.nth i
          (read_us Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete)
            85)
          0)).
  Proof.
    exact (full_width_spec_window_on_curve Γ
      (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
      spend_auth_g_rows_standard
      spend_auth_g_rows_length
      (spend_auth_g_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      i Hi).
  Qed.

  Lemma value_commit_r_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i (OrchardCircuitSpec.value_commit_r orchard_internal_params)
          fixed_window_default)
        (EccSpec.window_digit
          (read_scalar_from_windows Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete)
            85)
          i)
        (List.nth i
          (read_us Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete)
            85)
          0)).
  Proof.
    exact (full_width_spec_window_on_curve Γ
      (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete)
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
      value_commit_r_rows_standard
      value_commit_r_rows_length
      (value_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      i Hi).
  Qed.

  Lemma note_commit_r_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i (OrchardCircuitSpec.note_commit_r orchard_internal_params)
          fixed_window_default)
        (EccSpec.window_digit
          (read_scalar_from_windows Γ
            (RegionId.NoteCommit RegionId.NoteCommit.Which.New
              RegionId.NoteCommit.FixedBaseIncomplete)
            85)
          i)
        (List.nth i
          (read_us Γ
            (RegionId.NoteCommit RegionId.NoteCommit.Which.New
              RegionId.NoteCommit.FixedBaseIncomplete)
            85)
          0)).
  Proof.
    exact (full_width_spec_window_on_curve Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete)
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
      note_commit_r_rows_standard
      note_commit_r_rows_length
      (note_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      i Hi).
  Qed.

  (** ** The four table-equality legs

      Each is the [Ea]/[Er]/[Ercm]/[Ev] hypothesis of
      [action_spec_us_free_of_table_eqs], verbatim: [table_us_free_of_oncurve]
      applied with the region's read-out [u]-list, the spec scalar, and the
      per-window on-curve + non-residue facts.  The digit bound of the
      non-residue certificate is free:
      [window_digit k i = (k / 8^i) mod 8 ∈ [0, 8)]. *)

  Lemma spend_auth_g_table_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (OrchardSpec.in_alpha (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_alpha (read_action_witness Γ)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (OrchardSpec.in_alpha (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_alpha (canonical_witness (read_action_inputs Γ))).
  Proof.
    unfold read_action_witness, canonical_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardCircuitSpec.w_us_alpha OrchardSpec.in_alpha].
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        85)
      (read_us Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        85)
      fixed_window_default).
    - rewrite read_us_length, spend_auth_g_table_length. reflexivity.
    - intros i Hi.
      rewrite spend_auth_g_table_length in Hi.
      split.
      + cbv zeta.
        exact (spend_auth_g_spec_window_on_curve Γ Hcircuit i Hi).
      + apply (window_disc_qr_spend_auth_g_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  Lemma value_commit_r_table_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      (OrchardSpec.in_rcv (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_rcv (read_action_witness Γ)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      (OrchardSpec.in_rcv (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_rcv (canonical_witness (read_action_inputs Γ))).
  Proof.
    unfold read_action_witness, canonical_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardCircuitSpec.w_us_rcv OrchardSpec.in_rcv].
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
      (read_us Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
      fixed_window_default).
    - rewrite read_us_length, value_commit_r_table_length. reflexivity.
    - intros i Hi.
      rewrite value_commit_r_table_length in Hi.
      split.
      + cbv zeta.
        exact (value_commit_r_spec_window_on_curve Γ Hcircuit i Hi).
      + apply (window_disc_qr_value_commit_r_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  Lemma note_commit_r_table_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (OrchardSpec.in_rcm_new (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_rcm (read_action_witness Γ)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (OrchardSpec.in_rcm_new (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_rcm (canonical_witness (read_action_inputs Γ))).
  Proof.
    unfold read_action_witness, canonical_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardCircuitSpec.w_us_rcm OrchardSpec.in_rcm_new].
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85)
      (read_us Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85)
      fixed_window_default).
    - rewrite read_us_length, note_commit_r_table_length. reflexivity.
    - intros i Hi.
      rewrite note_commit_r_table_length in Hi.
      split.
      + cbv zeta.
        exact (note_commit_r_spec_window_on_curve Γ Hcircuit i Hi).
      + apply (window_disc_qr_note_commit_r_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (** The short (running-sum) leg.  The [A4[22] = 0] final boundary of the
      running sum is enforced by the synthesized region's
      [𝓡.ConstrainConstant] (mirroring upstream's strict
      [decompose_running_sum]) and discharged from [Holds] by
      [value_commit_v_z_boundary_of_holds]. *)
  Lemma value_commit_v_table_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      (OrchardSpec.in_magnitude (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_v (read_action_witness Γ)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      (OrchardSpec.in_magnitude (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_v (canonical_witness (read_action_inputs Γ))).
  Proof.
    unfold read_action_witness, canonical_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardCircuitSpec.w_us_v OrchardSpec.in_magnitude].
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      (read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck))
      (read_us Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) 22)
      fixed_window_default).
    - rewrite read_us_length, value_commit_v_table_length. reflexivity.
    - intros i Hi.
      rewrite value_commit_v_table_length in Hi.
      split.
      + cbv zeta.
        exact (value_commit_v_spec_window_on_curve Γ Hcircuit i Hi).
      + apply (window_disc_qr_value_commit_v_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (** ** The reduction: [action_spec_us_free] modulo the nullifier_k leg

      With the four legs above discharged under [Holds Γ] (plus the
      value_commit_v boundary side condition), the witness elimination follows
      from the single remaining table equality [Ek] — the nullifier_k
      fixed-base mul at the scalar [poseidon_hash2 nk rho_old +F psi_old].
      [Ek] is discharged in [Orchard/circuit_proof/us_free/nullifier_k.v]:
      Poseidon full-permutation soundness (the circuit's 64-round
      [synthesize_hash] output equals [poseidon_hash2]) composed through the
      [ScalarAdd] [QAdd]/[Copy] chain, together with the base-field
      running-sum digit match of [circuit_proof/base_field_canonicity.v]. *)
  Lemma action_spec_us_free_of_nullifier_k
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Ek : EccSpec.fixed_scalar_mul
              (OrchardCircuitSpec.nullifier_k orchard_internal_params)
              (Poseidon.poseidon_hash2
                 (OrchardSpec.in_nk (read_action_inputs Γ))
                 (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
                 OrchardSpec.in_psi_old (read_action_inputs Γ))
              (OrchardCircuitSpec.w_us_k (read_action_witness Γ)) =
            EccSpec.fixed_scalar_mul
              (OrchardCircuitSpec.nullifier_k orchard_internal_params)
              (Poseidon.poseidon_hash2
                 (OrchardSpec.in_nk (read_action_inputs Γ))
                 (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
                 OrchardSpec.in_psi_old (read_action_inputs Γ))
              (OrchardCircuitSpec.w_us_k (canonical_witness (read_action_inputs Γ)))) :
    action_spec_of Γ = output (read_action_inputs Γ).
  Proof.
    exact (action_spec_us_free_of_table_eqs Γ Ek
      (value_commit_v_table_eq Γ Hcircuit)
      (value_commit_r_table_eq Γ Hcircuit)
      (spend_auth_g_table_eq Γ Hcircuit)
      (note_commit_r_table_eq Γ Hcircuit)).
  Qed.

End OrchardActionUsFree.
