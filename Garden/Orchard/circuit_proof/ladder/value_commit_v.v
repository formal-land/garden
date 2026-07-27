(** * ValueCommitV fixed-base ladder: full window correctness and distinctness

    The per-base instance, for ValueCommitV (the CV_NET short base, 22
    windows), of the parameterized window-table-to-distinctness chain of
    [circuit_proof/ladder/main.v] ([full_table_entry_eq_mul_gen],
    [fixed_window_point_x_eq_mul_gen], [full_window_correct_gen],
    [ladder_distinct_precondition_holds_gen] — all generic in the window
    count, so the short [n = 22] ladder reuses them with [22]/[21]/[20] in
    place of [85]/[84]/[83]).  The ValueCommitV certificate ingredients are
    proved in their own
    files: [circuit_proof/value_commit_v/table.v] (the
    octupling-chain-computed window table [ValueCommitVFullTable.full_table]
    and its materialised literal),
    [circuit_proof/value_commit_v/x_cert.v] (the Lagrange
    x-coordinate agreement), [circuit_proof/value_commit_v/sign_cert.v]
    (the positive-QR witness), and
    [circuit_proof/value_commit_v/disc_cert.v] (the
    discriminant non-residue certificate).  The digit/window-correct
    match at the spec table is proved in [circuit_proof/fixed_base/main.v]
    ([OrchardActionFixedBase.value_commit_v_window_digit] /
    [value_commit_v_window_correct] / [value_commit_v_spec_window_on_curve]).

    This file instantiates the shared chain at
    [G := value_commit_v_G] / [n := 22]:
    - [value_commit_v_full_table_entry_eq_mul] (the certificate table entry
      is the Weierstrass multiple) and
      [value_commit_v_fixed_window_point_x_eq_mul] (the spec window point's
      x equals the multiple's x);
    - [value_commit_v_full_window_correct]: every one of the 22
      ValueCommitV incomplete-region window points equals the [repr] of its
      Weierstrass multiple [window_scalar 22 j digit_j · value_commit_v_G],
      the digit read from the magnitude cell ([read9] of the magnitude
      range-check region);
    - [value_commit_v_distinct_holds]: the full
      20-edge (rows 1..20) [incomplete_additions_distinct_precondition]. *)

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
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.value_commit_v.table.
Require Import Garden.Orchard.circuit_proof.value_commit_v.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import OrchardActionInputs.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the [Holds] hypotheses below are at [pallas_p] (every other EC
   and Orchard file sets this; see [circuit_proof/ladder/main.v]). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module ValueCommitVLadder.
  Import FixedBaseLadder.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The ValueCommitV incomplete-additions region, spelled out (not aliased)
     in every statement below so downstream consumers match syntactically. *)
  Local Notation VCV :=
    (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete).
  Local Notation VCV_MAG :=
    (RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck).

  (** Make scalar multiplication opaque to conversion for the x-coordinate
      instances
      (the same opaque window as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** ** Table-entry bridge — the certificate table entry is the Weierstrass
      multiple: window [w], digit [d]'s entry of
      [ValueCommitVFullTable.full_table] is exactly the abstract multiple
      [window_scalar 22 w d * value_commit_v_G].  Consumed to transport the
      positive QR certificate [ValueCommitVWindowSignCert.y_check_entry] onto
      [repr (mul (window_scalar ..) G)]. *)
  Lemma value_commit_v_full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 22)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w ValueCommitVFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 22 w d) PallasGenerators.value_commit_v_G.
  Proof.
    unfold ValueCommitVFullTable.full_table, ValueCommitVFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.value_commit_v_G
             PallasGenerators.value_commit_v_on_curve
             PallasGenerators.value_commit_v_reduced 21 w d Hw Hd).
  Qed.

  (** ** Window-point x-coordinate agreement — the unconditional half, from
      the Lagrange
      x-coordinate [vm_compute] certificate
      [ValueCommitVFixedWindowCert.x_check_entry]. *)
  Lemma value_commit_v_fixed_window_point_x_eq_mul (w : nat) (d u : Z)
      (Hw : (w < 22)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.value_commit_v orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 22 w d) PallasGenerators.value_commit_v_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.value_commit_v_G
              PallasGenerators.value_commit_v_on_curve
              PallasGenerators.value_commit_v_reduced 21
              (OrchardCircuitSpec.value_commit_v orchard_internal_params)
              _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (ValueCommitVFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold ValueCommitVFixedWindowCert.table, ValueCommitVFixedWindowCert.default
      in Hx.
    unfold ValueCommitVFullTable.full_table, ValueCommitVFullTable.G in Hx.
    exact Hx.
  Qed.

  (** Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (* Keep the square-root / QR chain opaque to the kernel's conversion oracle
     so up-to-conversion matching in [value_commit_v_full_window_correct]
     never evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent
     (as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** ** Per-window full correctness from a satisfying assignment

      [full_window_correct_gen] at the ValueCommitV base: the window equation
      from
      [OrchardActionFixedBase.value_commit_v_window_correct] (the digit is
      [window_digit] of the magnitude cell [read9]), the on-curve fact from
      [value_commit_v_spec_window_on_curve], the discriminant certificate
      from
      [window_disc_qr_value_commit_v_all_Z], the positive QR certificate from
      [ValueCommitVWindowSignCert.y_check_entry] transported by
      [value_commit_v_full_table_entry_eq_mul], and the x-coordinate
      agreement from
      [value_commit_v_fixed_window_point_x_eq_mul]. *)
  Lemma value_commit_v_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 22)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ VCV (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 22 j
          (EccSpec.window_digit (OrchardActionInputs.read9 Γ VCV_MAG) j))
        PallasGenerators.value_commit_v_G).
  Proof.
    refine (full_window_correct_gen Γ VCV
      PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_on_curve
      PallasGenerators.value_commit_v_reduced
      22
      (fun i => EccSpec.window_digit (OrchardActionInputs.read9 Γ VCV_MAG) i)
      (fun i _ => window_digit_bound (OrchardActionInputs.read9 Γ VCV_MAG) i)
      (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      assert (Hnth : List.nth_error
          (OrchardCircuitSpec.value_commit_v orchard_internal_params) i
        = Some (List.nth i (OrchardCircuitSpec.value_commit_v orchard_internal_params)
                  OrchardActionFixedBase.fixed_window_default)).
      { apply List.nth_error_nth'.
        rewrite OrchardActionFixedBase.value_commit_v_table_length. exact Hi. }
      exact (OrchardActionFixedBase.value_commit_v_window_correct Γ Hcircuit i
        _ Hnth).
    - (* Hwindow_on_curve *)
      intros i Hi.
      exact (OrchardActionFixedBase.value_commit_v_spec_window_on_curve Γ
        Hcircuit i Hi).
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_value_commit_v_all_Z i
        (EccSpec.window_digit (OrchardActionInputs.read9 Γ VCV_MAG) i)
        Hi
        (window_digit_bound (OrchardActionInputs.read9 Γ VCV_MAG) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound (OrchardActionInputs.read9 Γ VCV_MAG) i)
        as Hdj.
      set (dj := EccSpec.window_digit (OrchardActionInputs.read9 Γ VCV_MAG) i)
        in *.
      pose proof (ValueCommitVWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (value_commit_v_full_table_entry_eq_mul i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (value_commit_v_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** ** The FULL ValueCommitV ladder-distinctness predicate

      All 20 incomplete edges (rows 1..20) at once:
      [ladder_distinct_precondition_holds_gen] fed with
      [value_commit_v_full_window_correct] and the ValueCommitV generator's
      on-curve/reduced/non-identity/order facts. *)
  Lemma value_commit_v_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ VCV 1 20
      (OrchardActionFixedBase.incomplete_additions_window_point Γ VCV 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ VCV
      PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_on_curve
      PallasGenerators.value_commit_v_reduced
      22
      (fun i => EccSpec.window_digit (OrchardActionInputs.read9 Γ VCV_MAG) i)
      (fun i _ => window_digit_bound (OrchardActionInputs.read9 Γ VCV_MAG) i)
      PallasGenerators.value_commit_v_ne_identity
      PallasGeneratorsOrder.value_commit_v_order
      ltac:(lia)
      (fun j Hj => value_commit_v_full_window_correct Γ Hcircuit j Hj)
      20 eq_refl).
  Qed.

End ValueCommitVLadder.
