(** * CommitIvkR: the canonical-witness table fold is the group multiple

    The CommitIvkR instance of the Γ-free generic composition
    [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([circuit_proof/protocol_mul/core.v]): for [0 <= k < 8^85], the
    [EccSpec.fixed_scalar_mul] fold over the circuit's CommitIvkR table
    ([OrchardCircuitSpec.commit_ivk_r orchard_internal_params], the blinding
    base of the CommitIvk commitment — the [rivk] leg) with the canonical
    square-root witnesses equals [OrchardProtocolSpec.mul_commit_ivk_r k] —
    the [Pallas.mul] multiple of the affine generator
    [PallasGenerators.commit_ivk_r_G].

    The generic wrapper is instantiated at the last window index [m = 84]
    (window count 85) with:
    - the generator facts [commit_ivk_r_on_curve] / [commit_ivk_r_reduced] /
      [commit_ivk_r_ne_identity] ([Orchard/Pallas/Generators.v]) and the
      prime-order fact [commit_ivk_r_order]
      ([Orchard/Pallas/GeneratorsOrder.v]);
    - the three per-base [vm_compute] certificate hooks
      ([circuit_proof/commit_ivk_r/{x_cert,sign_cert,disc_cert}.v]),
      restated over the spec-table spelling — the cert files' [table] /
      [default] aliases and the table leaf's builder form
      ([CommitIvkRFullTable.full_table]) unfold to it, the same bridge as
      [circuit_proof/protocol_mul/note_commit_r.v];
    - the table length, a one-[reflexivity] read-off of the pasted rows
      ([commit_ivk_r_spec_table_length], proved locally below — the
      [OrchardActionUsFree] plumbing carries no commit_ivk_r entry). *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.table.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.x_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so [is_square]/[field_sqrt]/[fixed_window_point] below are at
   [pallas_p] (every other EC and Orchard file sets this). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   up-to-conversion matching against the [ProtocolMulCore] hook shapes never
   evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent (see
   [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module CommitIvkRMulProtocol.
  Import OrchardActionInputs.

  (** The spec table has the full 85 windows (a one-iota read-off of the
      pasted rows, the same shape as [OrchardActionUsFree]'s table-length
      plumbing for the other full-width bases). *)
  Lemma commit_ivk_r_spec_table_length :
    List.length (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  (** Make scalar multiplication opaque to conversion while restating the
      certificate hooks over the spec-table spelling: the bridges below match
      terms containing [Pallas.mul] purely syntactically (the same opaque
      window as in [circuit_proof/protocol_mul/note_commit_r.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** The Lagrange x-coordinate certificate hook
      ([CommitIvkRFixedWindowCert.x_check_entry]), in the [Hx_cert] shape of
      [ProtocolMulCore.ProtocolMulGen]: the cert file's [table]/[default]
      aliases and the table leaf's builder form unfold to the spec-table
      spelling. *)
  Lemma commit_ivk_r_x_cert_hook (w i : nat)
      (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        (Z.of_nat i) 0) =
    Point.x
      (PallasModel.repr
        (List.nth i
          (List.nth w
            (FixedBaseTableDefs.nonlast_points 84
               PallasGenerators.commit_ivk_r_G ++
             [FixedBaseTableDefs.last_row
                (FixedBaseTableDefs.base_pow8 84
                  PallasGenerators.commit_ivk_r_G)
                (Pallas.mul
                  (FixedBaseTableDefs.window_offset_sum 84)
                  PallasGenerators.commit_ivk_r_G)]) [])
          Pallas.identity)).
  Proof.
    pose proof (CommitIvkRFixedWindowCert.x_check_entry w i Hw Hi) as Hx.
    unfold CommitIvkRFixedWindowCert.table, CommitIvkRFixedWindowCert.default
      in Hx.
    unfold CommitIvkRFullTable.full_table, CommitIvkRFullTable.G in Hx.
    exact Hx.
  Qed.

  (** The positive QR window-sign certificate hook
      ([CommitIvkRWindowSignCert.y_check_entry]), in the [Hsign_cert]
      shape. *)
  Lemma commit_ivk_r_sign_cert_hook (w i : nat)
      (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    is_square
      (UnOp.from
        (EccSpec.fw_z
          (List.nth w (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
            OrchardActionFixedBase.fixed_window_default)
         +F Point.y
              (PallasModel.repr
                (List.nth i
                  (List.nth w
                    (FixedBaseTableDefs.nonlast_points 84
                       PallasGenerators.commit_ivk_r_G ++
                     [FixedBaseTableDefs.last_row
                        (FixedBaseTableDefs.base_pow8 84
                          PallasGenerators.commit_ivk_r_G)
                        (Pallas.mul
                          (FixedBaseTableDefs.window_offset_sum 84)
                          PallasGenerators.commit_ivk_r_G)]) [])
                  Pallas.identity)))) = true.
  Proof.
    pose proof (CommitIvkRWindowSignCert.y_check_entry w i Hw Hi) as Hqr.
    unfold CommitIvkRWindowSignCert.table, CommitIvkRWindowSignCert.default
      in Hqr.
    unfold CommitIvkRFullTable.full_table, CommitIvkRFullTable.G in Hqr.
    exact Hqr.
  Qed.

  (** Restore [mul] transparency for the composition below. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (** The non-residue window-discriminant certificate hook
      ([window_disc_qr_commit_ivk_r_all_Z]), in the [Hdisc_cert] shape (the
      cert's inlined [fixed_table_of_rows] spelling converts to the
      spec-table one). *)
  Lemma commit_ivk_r_disc_cert_hook (w : nat) (digit : Z)
      (Hw : (w < 85)%nat) (Hdig : 0 <= digit < 8) :
    is_square
      (window_disc
        (List.nth w (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        digit) = false.
  Proof.
    exact (window_disc_qr_commit_ivk_r_all_Z w digit Hw Hdig).
  Qed.

  (** ** The CommitIvkR table-fold = group-multiple bridge

      [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul] at [m = 84],
      [G = commit_ivk_r_G], [spec_table = OrchardCircuitSpec.commit_ivk_r
      orchard_internal_params], fed with the three certificate hooks and the
      generator's on-curve/reduced/non-identity/order facts. *)
  Theorem commit_ivk_r_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) k) =
    OrchardProtocolSpec.mul_commit_ivk_r k.
  Proof.
    unfold OrchardProtocolSpec.mul_commit_ivk_r.
    exact (ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul
      PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced
      84
      ltac:(lia) ltac:(lia)
      PallasGenerators.commit_ivk_r_ne_identity
      PallasGeneratorsOrder.commit_ivk_r_order
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      commit_ivk_r_spec_table_length
      commit_ivk_r_x_cert_hook
      commit_ivk_r_sign_cert_hook
      commit_ivk_r_disc_cert_hook
      k Hk).
  Qed.
End CommitIvkRMulProtocol.
