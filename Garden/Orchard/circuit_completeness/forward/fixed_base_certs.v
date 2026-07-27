(** * Certificates for the fixed-base forward lemmas

    The concrete [vm_compute] facts consumed by [forward/fixed_base.v] — the
    symbolic per-gate forward lemmas for the fixed-base window gates.  All
    inputs are independent of the honest input [w], so each fact is a single
    Boolean check over the synthesis program's facts, the configured system,
    or the circuit's window tables:

    - [fb_shape_ok]: every enabled point of the four fixed-base selectors
      ([QMulFixedRunningSum], [QMulFixedFull], [QMulFixedShort],
      [QMulFixedBaseField]) lies in one of the nine (region, row-range)
      groups the forward lemmas cover;
    - [<region>_fixed_ok]: at each window row of a fixed-base leg region, the
      honest fixed plane carries exactly the window's eight Lagrange
      coefficients and its [z] offset, and the window has eight coefficients;
    - [<base>_oncurve_ok]: for every (window, digit) of a leg's table, the
      window point recovered from the pasted square-root witness satisfies
      the Pallas curve equation — the forward image of the gate's on-curve
      constraint;
    - [<base>_len]: the window counts of the leg tables;
    - [fb_lookups_unmentioned_ok]: no configured lookup argument mentions a
      fixed-base selector, so the lookup obligations at these points are
      vacuous.

    This file is a leaf: nothing under proof iteration depends on it, so its
    [vm_compute] costs are paid only when it changes. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardFixedBaseCerts.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessTables.

  (** ** The nine enabled-point groups *)

  Definition R_sa : RegionId.t :=
    RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete.
  Definition R_vcr : RegionId.t :=
    RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete.
  Definition R_vcv : RegionId.t :=
    RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete.
  Definition R_msb : RegionId.t :=
    RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb.
  Definition R_civk : RegionId.t :=
    RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete.
  Definition R_nco : RegionId.t :=
    RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.FixedBaseIncomplete.
  Definition R_ncn : RegionId.t :=
    RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.FixedBaseIncomplete.
  Definition R_nk : RegionId.t :=
    RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete.
  Definition R_canon : RegionId.t :=
    RegionId.Nullifier RegionId.Nullifier.CanonicityChecks.

  Definition zin (lo hi row : Z) : bool := (lo <=? row) && (row <? hi).

  (** The admissible (selector, region, row) shape of a fixed-base enabled
      point; [true] on every other selector. *)
  Definition fb_shape (pt : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, row) := pt in
    match sel, region with
    | Selector.QMulFixedRunningSum,
      RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete => zin 0 22 row
    | Selector.QMulFixedRunningSum,
      RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete =>
        zin 0 85 row
    | Selector.QMulFixedRunningSum, _ => false
    | Selector.QMulFixedFull,
      RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitRIncomplete => zin 0 85 row
    | Selector.QMulFixedFull,
      RegionId.SpendAuthority
        RegionId.SpendAuthority.FullFixedIncomplete => zin 0 85 row
    | Selector.QMulFixedFull,
      RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete =>
        zin 0 85 row
    | Selector.QMulFixedFull,
      RegionId.NoteCommit _ RegionId.NoteCommit.FixedBaseIncomplete =>
        zin 0 85 row
    | Selector.QMulFixedFull, _ => false
    | Selector.QMulFixedShort,
      RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb =>
        row =? 1
    | Selector.QMulFixedShort, _ => false
    | Selector.QMulFixedBaseField,
      RegionId.Nullifier RegionId.Nullifier.CanonicityChecks => row =? 1
    | Selector.QMulFixedBaseField, _ => false
    | _, _ => true
    end.

  Lemma fb_shape_ok : List.forallb fb_shape enabled = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** The honest fixed plane at the window rows *)

  (** The honest fixed plane of [honest_assignment] (input-independent). *)
  Definition fixed_at (c : Fixed.t) (region : RegionId.t) (row : Z) : Z :=
    Complete.fixed_write_or_zero
      OrchardHonestAssignment.fixed_eqb OrchardHonestAssignment.region_eqb
      OrchardHonestAssignment.facts c region row.

  Definition wdw (tbl : EccSpec.fixed_table) (i : nat) : EccSpec.fixed_window :=
    List.nth i tbl OrchardAdviceEccMuls.dummy_window.

  (** Window row [i] of [region] reads the eight Lagrange coefficients and
      the [z] offset of window [i] of [tbl] from the fixed plane, and the
      window has exactly eight coefficients. *)
  Definition window_row_check
      (tbl : EccSpec.fixed_table) (region : RegionId.t) (i : nat) : bool :=
    let W := wdw tbl i in
    let cs := W.(EccSpec.fw_coeffs) in
    let r := Z.of_nat i in
    (List.length cs =? 8)%nat &&
    (fixed_at Fixed.LagrangeCoeffs0 region r =? List.nth 0 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs1 region r =? List.nth 1 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs2 region r =? List.nth 2 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs3 region r =? List.nth 3 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs4 region r =? List.nth 4 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs5 region r =? List.nth 5 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs6 region r =? List.nth 6 cs 0) &&
    (fixed_at Fixed.LagrangeCoeffs7 region r =? List.nth 7 cs 0) &&
    (fixed_at Fixed.FixedZ region r =? W.(EccSpec.fw_z)).

  Lemma sa_fixed_ok :
    List.forallb
      (window_row_check OrchardAdviceEccMuls.tbl_spend_auth R_sa)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma vcr_fixed_ok :
    List.forallb
      (window_row_check OrchardAdviceEccMuls.tbl_value_commit_r R_vcr)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma vcv_fixed_ok :
    List.forallb
      (window_row_check OrchardAdviceEccMuls.tbl_value_commit_v R_vcv)
      (List.seq 0 22) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma civk_fixed_ok :
    List.forallb
      (window_row_check
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) R_civk)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nco_fixed_ok :
    List.forallb
      (window_row_check OrchardAdviceEccMuls.tbl_note_commit_r R_nco)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma ncn_fixed_ok :
    List.forallb
      (window_row_check OrchardAdviceEccMuls.tbl_note_commit_r R_ncn)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nk_fixed_ok :
    List.forallb
      (window_row_check OrchardAdvicePoseidonNullifier.nk_table R_nk)
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** The window points are on the curve

      For each (window, digit), the point read back from the table's Lagrange
      interpolation and the pasted square-root witness satisfies
      [y² = x³ + 5]. *)
  Definition oncurve_entry_check
      (tbl : EccSpec.fixed_table) (roots : list (list Z)) (i d : nat) : bool :=
    let W := wdw tbl i in
    let u := List.nth d (List.nth i roots []) 0 in
    let P := EccSpec.fixed_window_point W (Z.of_nat d) u in
    let x := Point.x P in
    let y := Point.y P in
    (y *F y -F (x *F x *F x +F 5)) =? 0.

  Lemma sa_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check OrchardAdviceEccMuls.tbl_spend_auth
            SpendAuthGWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma vcr_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check OrchardAdviceEccMuls.tbl_value_commit_r
            ValueCommitRWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma vcv_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check OrchardAdviceEccMuls.tbl_value_commit_v
            ValueCommitVWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 22) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma civkr_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check
            (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
            CommitIvkRWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma ncr_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check OrchardAdviceEccMuls.tbl_note_commit_r
            NoteCommitRWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nk_oncurve_ok :
    List.forallb
      (fun i =>
        List.forallb
          (oncurve_entry_check OrchardAdvicePoseidonNullifier.nk_table
            NullifierKWindowSignCert.root_table i)
          (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Window counts *)

  Lemma sa_len : List.length OrchardAdviceEccMuls.tbl_spend_auth = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma vcr_len : List.length OrchardAdviceEccMuls.tbl_value_commit_r = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma vcv_len : List.length OrchardAdviceEccMuls.tbl_value_commit_v = 22%nat.
  Proof. vm_cast_no_check (@eq_refl nat 22%nat). Qed.

  Lemma civkr_len :
    List.length (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) =
    85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma ncr_len : List.length OrchardAdviceEccMuls.tbl_note_commit_r = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma nk_len : List.length OrchardAdvicePoseidonNullifier.nk_table = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  (** ** No lookup argument mentions a fixed-base selector *)

  Definition fb_selectors : list Selector.t :=
    [Selector.QMulFixedRunningSum; Selector.QMulFixedFull;
     Selector.QMulFixedShort; Selector.QMulFixedBaseField].

  Lemma fb_lookups_unmentioned_ok :
    List.forallb
      (fun arg =>
        List.forallb
          (fun sel =>
            negb
              (Complete.arg_mentions_selector
                OrchardDecidableEq.selector_eqb sel arg))
          fb_selectors)
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardForwardFixedBaseCerts.
