(** * ValueCommitR fixed-base ladder: full window correctness and distinctness

    The per-base instance, for ValueCommitR (the CV_NET blind base, a
    full-width 85-window table exactly like SpendAuthG), of the parameterized
    window-table-to-distinctness chain of [circuit_proof/ladder/main.v]
    ([full_table_entry_eq_mul_gen], [fixed_window_point_x_eq_mul_gen],
    [full_window_correct_gen], [ladder_distinct_precondition_holds_gen]).
    The ValueCommitR certificate ingredients are proved in their own files:
    [circuit_proof/value_commit_r/table.v] (the octupling-chain-computed
    window table [ValueCommitRFullTable.full_table] and its materialised
    literal), [circuit_proof/value_commit_r/x_cert.v] (the
    Lagrange x-coordinate agreement), [circuit_proof/value_commit_r/sign_cert.v]
    (the positive-QR witness), and
    [circuit_proof/value_commit_r/disc_cert.v] (the
    discriminant non-residue certificate).  The per-window circuit fact
    against the whole spec table is proved generically over any
    standard full-width table:
    [OrchardActionUsFree.full_width_table_window_correct] /
    [full_width_spec_window_on_curve] ([circuit_proof/us_free/main.v]), fed by the
    ValueCommitR-specific shape/length facts [value_commit_r_rows_standard] /
    [value_commit_r_rows_length] and the region facts
    [value_commit_r_incomplete_facts] (same file).

    This file instantiates the shared chain at
    [G := value_commit_r_G] / [n := 85]:
    - [value_commit_r_full_table_entry_eq_mul] (the certificate table entry
      is the Weierstrass multiple) and
      [value_commit_r_fixed_window_point_x_eq_mul] (the spec window point's
      x equals the multiple's x);
    - [value_commit_r_full_window_correct]: every one of the 85
      ValueCommitR incomplete-region window points equals the [repr] of its
      Weierstrass multiple [window_scalar 85 j digit_j · value_commit_r_G];
    - [value_commit_r_distinct_holds]: the full
      83-edge (rows 1..83) [incomplete_additions_distinct_precondition]. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.value_commit_r.table.
Require Import Garden.Orchard.circuit_proof.value_commit_r.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import OrchardActionInputs.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the [Holds] hypotheses below are at [pallas_p] (every other EC
   and Orchard file sets this; see [circuit_proof/ladder/main.v]). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module ValueCommitRLadder.
  Import FixedBaseLadder.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The ValueCommitR incomplete-additions region, spelled out (not aliased)
     in every statement below so downstream consumers match syntactically. *)
  Local Notation VCR :=
    (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete).

  (** Make scalar multiplication opaque to conversion for the x-coordinate
      instances:
      window points are closed multiples of a concrete 254-bit generator, so
      any [reflexivity]/[rewrite]/[f_equal] that would reduce one to
      weak-head normal form runs the full double-and-add ladder.  Restored to
      transparent right after the x-coordinate bridge (the same opaque
      window as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** ** Table-entry bridge — the certificate table entry is the Weierstrass
      multiple: window [w], digit [d]'s entry of
      [ValueCommitRFullTable.full_table] is exactly the abstract multiple
      [window_scalar 85 w d * value_commit_r_G].  Consumed to transport the
      positive QR certificate [ValueCommitRWindowSignCert.y_check_entry] onto
      [repr (mul (window_scalar ..) G)]. *)
  Lemma value_commit_r_full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w ValueCommitRFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 85 w d) PallasGenerators.value_commit_r_G.
  Proof.
    unfold ValueCommitRFullTable.full_table, ValueCommitRFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.value_commit_r_G
             PallasGenerators.value_commit_r_on_curve
             PallasGenerators.value_commit_r_reduced 84 w d Hw Hd).
  Qed.

  (** ** Window-point x-coordinate agreement — the unconditional half, from
      the Lagrange
      x-coordinate [vm_compute] certificate
      [ValueCommitRFixedWindowCert.x_check_entry]. *)
  Lemma value_commit_r_fixed_window_point_x_eq_mul (w : nat) (d u : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.value_commit_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 w d) PallasGenerators.value_commit_r_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.value_commit_r_G
              PallasGenerators.value_commit_r_on_curve
              PallasGenerators.value_commit_r_reduced 84
              (OrchardCircuitSpec.value_commit_r orchard_internal_params)
              _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (ValueCommitRFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold ValueCommitRFixedWindowCert.table, ValueCommitRFixedWindowCert.default
      in Hx.
    unfold ValueCommitRFullTable.full_table, ValueCommitRFullTable.G in Hx.
    exact Hx.
  Qed.

  (** Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (* Keep the square-root / QR chain opaque to the kernel's conversion oracle
     so up-to-conversion matching in [value_commit_r_full_window_correct]
     never evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent
     (as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** ** Per-window full correctness from a satisfying assignment

      [full_window_correct_gen] at the ValueCommitR base: the window equation
      and the on-curve
      fact from the generic [OrchardActionUsFree] lemmas (fed by the
      ValueCommitR shape/length/region facts), the discriminant certificate
      from
      [window_disc_qr_value_commit_r_all_Z], the positive QR certificate from
      [ValueCommitRWindowSignCert.y_check_entry] transported by
      [value_commit_r_full_table_entry_eq_mul], and the x-coordinate agreement
      from
      [value_commit_r_fixed_window_point_x_eq_mul]. *)
  Lemma value_commit_r_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ VCR (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j
          (EccSpec.window_digit
            (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) j))
        PallasGenerators.value_commit_r_G).
  Proof.
    pose proof (OrchardActionUsFree.value_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    pose proof (OrchardActionFixedBase.holds_gates Γ Hcircuit) as Hgates.
    refine (full_window_correct_gen Γ VCR
      PallasGenerators.value_commit_r_G
      PallasGenerators.value_commit_r_on_curve
      PallasGenerators.value_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)
      (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_table_window_correct Γ VCR
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        OrchardActionUsFree.value_commit_r_rows_standard
        OrchardActionUsFree.value_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_on_curve *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ VCR
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows
        OrchardActionUsFree.value_commit_r_rows_standard
        OrchardActionUsFree.value_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_value_commit_r_all_Z i
        (EccSpec.window_digit
          (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)
        Hi
        (window_digit_bound
          (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i) as Hdj.
      set (dj := EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i) in *.
      pose proof (ValueCommitRWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (value_commit_r_full_table_entry_eq_mul i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (value_commit_r_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** ** The FULL ValueCommitR ladder-distinctness predicate

      All 83 incomplete edges (rows 1..83) at once:
      [ladder_distinct_precondition_holds_gen] fed with
      [value_commit_r_full_window_correct] and the ValueCommitR generator's
      on-curve/reduced/non-identity/order facts. *)
  Lemma value_commit_r_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ VCR 1 83
      (OrchardActionFixedBase.incomplete_additions_window_point Γ VCR 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ VCR
      PallasGenerators.value_commit_r_G
      PallasGenerators.value_commit_r_on_curve
      PallasGenerators.value_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ VCR 85) i)
      PallasGenerators.value_commit_r_ne_identity
      PallasGeneratorsOrder.value_commit_r_order
      ltac:(lia)
      (fun j Hj => value_commit_r_full_window_correct Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

End ValueCommitRLadder.
