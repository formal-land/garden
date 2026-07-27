(** * commit_ivk_r fixed-base window-point computational certificate

    The [vm_compute] half of the commit_ivk_r x-coordinate agreement: for
    every window [w] (0..84) and digit [i] (0..7), the circuit fixed-base
    table's Lagrange-interpolated x-coordinate equals the x-coordinate of the
    computed Weierstrass multiple of the commit_ivk_r generator [G].

    The window points come from the shared materialised table
    ([circuit_proof/commit_ivk_r/table.v]): [x_check_true] compares all
    85*8 entries against the circuit table by [Z.eqb], reading the multiples
    from the pasted literal [CommitIvkRFullTable.full_table_reduced], so its
    [vm_compute] costs seconds — the octupling chain is paid once, in the
    table leaf's [full_table_reduced_eq].  The per-entry extraction
    [x_check_entry] (consumed by the per-base bridge
    [circuit_proof/protocol_mul/commit_ivk_r.v]) is stated against the
    builder-form [CommitIvkRFullTable.full_table] and rewrites through
    [full_table_reduced_eq]. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.cert_defs.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.table.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** Keep the table constants opaque to unification/conversion in this file
    ([Opaque] is file-local; [vm_compute] ignores it, and the literal is
    already a value). *)
Opaque CommitIvkRFullTable.full_table.
Opaque CommitIvkRFullTable.full_table_reduced.

Module CommitIvkRFixedWindowCert.
  (** Alias for the circuit table / default window. *)
  Definition table : EccSpec.fixed_table :=
    OrchardCircuitSpec.commit_ivk_r OrchardActionFixedBase.orchard_internal_params.
  Definition default : EccSpec.fixed_window :=
    OrchardActionFixedBase.fixed_window_default.

  (** The whole-table certificate: every window/digit's Lagrange-interpolated
      x-coordinate equals the multiple's x-coordinate, in the shared checker's
      raw [forallb] shape ([FixedBaseXCert.check_fn]), reading the multiples
      from the table leaf's [full_table_reduced] literal. *)
  Lemma x_check_true :
    List.forallb
      (fun w : nat =>
         List.forallb
           (FixedBaseXCert.check_fn table default
              CommitIvkRFullTable.full_table_reduced w)
           (List.seq 0 8))
      (List.seq 0 85) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Per-entry extraction of the x-coordinate agreement. *)
  Lemma x_check_entry (w i : nat) (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    Point.x (EccSpec.fixed_window_point (List.nth w table default) (Z.of_nat i) 0)
    = Point.x (PallasModel.repr
         (List.nth i (List.nth w CommitIvkRFullTable.full_table [])
            Pallas.identity)).
  Proof.
    exact (FixedBaseXCert.x_check_entry table default
             CommitIvkRFullTable.full_table CommitIvkRFullTable.full_table_reduced 85
             CommitIvkRFullTable.full_table_reduced_eq x_check_true w i Hw Hi).
  Qed.
End CommitIvkRFixedWindowCert.
