(** * NoteCommitR fixed-base ladder: full window correctness and distinctness

    The per-base instance, for NoteCommitR (the CMX blinding base of the
    new-note commitment, a full-width 85-window table exactly like SpendAuthG
    and ValueCommitR), of the parameterized window-table-to-distinctness
    chain of
    [circuit_proof/ladder/main.v] ([full_table_entry_eq_mul_gen],
    [fixed_window_point_x_eq_mul_gen], [full_window_correct_gen],
    [ladder_distinct_precondition_holds_gen]).  The NoteCommitR certificate
    ingredients are proved in their own files:
    [circuit_proof/note_commit_r/table.v] (the octupling-chain-computed
    window table [NoteCommitRFullTable.full_table] and its materialised
    literal), [circuit_proof/note_commit_r/x_cert.v] (the
    Lagrange x-coordinate agreement),
    [circuit_proof/note_commit_r/sign_cert.v] (the positive-QR
    witness), and [circuit_proof/note_commit_r/disc_cert.v] (the
    discriminant non-residue certificate).  The per-window circuit
    fact against the whole spec table is proved generically over
    any standard full-width table:
    [OrchardActionUsFree.full_width_table_window_correct] /
    [full_width_spec_window_on_curve] ([circuit_proof/us_free/main.v]), fed by the
    NoteCommitR-specific shape/length facts [note_commit_r_rows_standard] /
    [note_commit_r_rows_length] and the region facts
    [note_commit_r_incomplete_facts] (same file) — the latter carrying
    the bridge from [note_commit.v]'s LOCAL ladder combinators
    ([synth_note_commit_r_mul_incomplete]) to
    [circuit.v]'s generic
    [synth_full_mul_incomplete_with_rows]
    ([note_commit_r_incomplete_facts_eq], a [reflexivity]: the local region
    synthesizer is a verbatim copy whose fact list never mentions the local
    record types).

    This file instantiates the shared chain at
    [G := note_commit_r_G] / [n := 85]:
    - [note_commit_r_full_table_entry_eq_mul] (the certificate table entry
      is the Weierstrass multiple) and
      [note_commit_r_fixed_window_point_x_eq_mul] (the spec window point's
      x equals the multiple's x);
    - [note_commit_r_full_window_correct]: every one of the 85
      NoteCommitR incomplete-region window points equals the [repr] of its
      Weierstrass multiple [window_scalar 85 j digit_j · note_commit_r_G];
    - [note_commit_r_distinct_holds]: the full
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
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.note_commit_r.table.
Require Import Garden.Orchard.circuit_proof.note_commit_r.x_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import OrchardActionInputs.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the [Holds] hypotheses below are at [pallas_p] (every other EC
   and Orchard file sets this; see [circuit_proof/ladder/main.v]). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NoteCommitRLadder.
  Import FixedBaseLadder.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The NoteCommitR (new-note) incomplete-additions region, spelled out (not
     aliased) in every statement below so downstream consumers match
     syntactically. *)
  Local Notation NCR :=
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.FixedBaseIncomplete).

  (** Make scalar multiplication opaque to conversion for the x-coordinate
      instances
      (the same opaque window as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** ** Table-entry bridge — the certificate table entry is the Weierstrass
      multiple: window [w], digit [d]'s entry of
      [NoteCommitRFullTable.full_table] is exactly the abstract multiple
      [window_scalar 85 w d * note_commit_r_G].  Consumed to transport the
      positive QR certificate [NoteCommitRWindowSignCert.y_check_entry] onto
      [repr (mul (window_scalar ..) G)]. *)
  Lemma note_commit_r_full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w NoteCommitRFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 85 w d) PallasGenerators.note_commit_r_G.
  Proof.
    unfold NoteCommitRFullTable.full_table, NoteCommitRFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.note_commit_r_G
             PallasGenerators.note_commit_r_on_curve
             PallasGenerators.note_commit_r_reduced 84 w d Hw Hd).
  Qed.

  (** ** Window-point x-coordinate agreement — the unconditional half, from
      the Lagrange
      x-coordinate [vm_compute] certificate
      [NoteCommitRFixedWindowCert.x_check_entry]. *)
  Lemma note_commit_r_fixed_window_point_x_eq_mul (w : nat) (d u : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.note_commit_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 w d) PallasGenerators.note_commit_r_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.note_commit_r_G
              PallasGenerators.note_commit_r_on_curve
              PallasGenerators.note_commit_r_reduced 84
              (OrchardCircuitSpec.note_commit_r orchard_internal_params)
              _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (NoteCommitRFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold NoteCommitRFixedWindowCert.table, NoteCommitRFixedWindowCert.default
      in Hx.
    unfold NoteCommitRFullTable.full_table, NoteCommitRFullTable.G in Hx.
    exact Hx.
  Qed.

  (** Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (* Keep the square-root / QR chain opaque to the kernel's conversion oracle
     so up-to-conversion matching in [note_commit_r_full_window_correct]
     never evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent
     (as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** ** Per-window full correctness from a satisfying assignment

      [full_window_correct_gen] at the NoteCommitR base: the window equation
      and the on-curve
      fact from the generic [OrchardActionUsFree] lemmas (fed by the
      NoteCommitR shape/length/region facts), the discriminant certificate
      from
      [window_disc_qr_note_commit_r_all_Z], the positive QR certificate from
      [NoteCommitRWindowSignCert.y_check_entry] transported by
      [note_commit_r_full_table_entry_eq_mul], and the x-coordinate agreement
      from
      [note_commit_r_fixed_window_point_x_eq_mul]. *)
  Lemma note_commit_r_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ NCR (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j
          (EccSpec.window_digit
            (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) j))
        PallasGenerators.note_commit_r_G).
  Proof.
    pose proof (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    pose proof (OrchardActionFixedBase.holds_gates Γ Hcircuit) as Hgates.
    refine (full_window_correct_gen Γ NCR
      PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_table_window_correct Γ NCR
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_on_curve *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ NCR
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_note_commit_r_all_Z i
        (EccSpec.window_digit
          (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)
        Hi
        (window_digit_bound
          (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i) as Hdj.
      set (dj := EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i) in *.
      pose proof (NoteCommitRWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (note_commit_r_full_table_entry_eq_mul i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (note_commit_r_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** ** The FULL NoteCommitR ladder-distinctness predicate

      All 83 incomplete edges (rows 1..83) at once:
      [ladder_distinct_precondition_holds_gen] fed with
      [note_commit_r_full_window_correct] and the NoteCommitR generator's
      on-curve/reduced/non-identity/order facts. *)
  Lemma note_commit_r_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ NCR 1 83
      (OrchardActionFixedBase.incomplete_additions_window_point Γ NCR 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ NCR
      PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ NCR 85) i)
      PallasGenerators.note_commit_r_ne_identity
      PallasGeneratorsOrder.note_commit_r_order
      ltac:(lia)
      (fun j Hj => note_commit_r_full_window_correct Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

End NoteCommitRLadder.
