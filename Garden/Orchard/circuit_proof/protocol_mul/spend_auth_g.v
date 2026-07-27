(** * SpendAuthG: the canonical-witness table fold is the group multiple

    The SpendAuthG instance of the Γ-free protocol bridge
    ([OrchardProtocolEquiv.spend_auth_g_mul_protocol] in
    [Garden/Orchard/circuit_proof/protocol_equiv.v]): for [0 <= k < 8^85],
    the [EccSpec.fixed_scalar_mul] fold over the concrete circuit table
    [OrchardCircuitSpec.spend_auth_g orchard_internal_params] with the canonical
    square-root witnesses equals
    [OrchardProtocolSpec.mul_spend_auth_g k = repr ([k] spend_auth_g_G)].

    Instantiates [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([circuit_proof/protocol_mul/core.v]) at [m = 84] (85 windows), the
    generator [PallasGenerators.spend_auth_g_G] with its on-curve / reduced /
    non-identity / order facts, and the three SpendAuthG certificate hooks:
    the Lagrange x-coordinate certificate
    ([SpendAuthGFixedWindowCert.x_check_entry]), the positive QR window-sign
    certificate ([SpendAuthGWindowSignCert.y_check_entry]) and the
    non-residue window-discriminant certificate
    ([window_disc_qr_spend_auth_g_all_Z]).  The hook lemmas below only
    re-spell each certificate's table constant to the spec table
    ([OrchardCircuitSpec.spend_auth_g orchard_internal_params], one delta step from
    [OrchardActionFixedBase.spend_auth_g_fixed_table] and from the disc
    cert's [sag_table]) and the cert table to its octupling-chain builder
    form ([SpendAuthGFullTable.full_table]). *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.table.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.x_cert.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.disc_cert.
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   composing the certificate hooks never evaluates [modpow] over the concrete
   Pallas [(p-1)/2] exponent (see [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

(* Window points at the concrete generator are closed 254-bit multiples; keep
   scalar multiplication opaque so conversion compares scalar arguments
   instead of running the double-and-add ladder (same window as the per-base
   instances of [circuit_proof/ladder/main.v]). *)
Strategy opaque [Pallas.mul Weierstrass.mul].

Module SpendAuthGMulProtocol.
  Import OrchardActionInputs.

  (** The spec table's concrete length (85 windows). *)
  Lemma spec_table_length :
    List.length (OrchardCircuitSpec.spend_auth_g orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  (** The Lagrange x-coordinate certificate hook, re-spelled onto the spec
      table and the builder-form window table
      ([ProtocolMulCore]'s [Hx_cert] shape at [m = 84],
      [G = spend_auth_g_G]). *)
  Lemma x_cert_hook (w i : nat) (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        (Z.of_nat i) 0) =
    Point.x
      (PallasModel.repr
        (List.nth i
          (List.nth w
            (FixedBaseTableDefs.nonlast_points 84
               PallasGenerators.spend_auth_g_G ++
             [FixedBaseTableDefs.last_row
                (FixedBaseTableDefs.base_pow8 84
                   PallasGenerators.spend_auth_g_G)
                (Pallas.mul (FixedBaseTableDefs.window_offset_sum 84)
                   PallasGenerators.spend_auth_g_G)]) [])
          Pallas.identity)).
  Proof.
    pose proof (SpendAuthGFixedWindowCert.x_check_entry w i Hw Hi) as Hx.
    unfold SpendAuthGFixedWindowCert.table, SpendAuthGFixedWindowCert.default,
      OrchardActionFixedBase.spend_auth_g_fixed_table in Hx.
    unfold SpendAuthGFullTable.full_table, SpendAuthGFullTable.G in Hx.
    exact Hx.
  Qed.

  (** The positive QR window-sign certificate hook ([Hsign_cert] shape). *)
  Lemma sign_cert_hook (w i : nat) (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    is_square
      (UnOp.from
        (EccSpec.fw_z
          (List.nth w (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
            OrchardActionFixedBase.fixed_window_default)
         +F Point.y
              (PallasModel.repr
                (List.nth i
                  (List.nth w
                    (FixedBaseTableDefs.nonlast_points 84
                       PallasGenerators.spend_auth_g_G ++
                     [FixedBaseTableDefs.last_row
                        (FixedBaseTableDefs.base_pow8 84
                           PallasGenerators.spend_auth_g_G)
                        (Pallas.mul (FixedBaseTableDefs.window_offset_sum 84)
                           PallasGenerators.spend_auth_g_G)]) [])
                  Pallas.identity)))) = true.
  Proof.
    pose proof (SpendAuthGWindowSignCert.y_check_entry w i Hw Hi) as Hqr.
    unfold SpendAuthGWindowSignCert.table, SpendAuthGWindowSignCert.default,
      OrchardActionFixedBase.spend_auth_g_fixed_table in Hqr.
    unfold SpendAuthGFullTable.full_table, SpendAuthGFullTable.G in Hqr.
    exact Hqr.
  Qed.

  (** The non-residue window-discriminant certificate hook
      ([Hdisc_cert] shape; the disc cert's [sag_table]/[sag_default] are
      definitionally the spec table / default). *)
  Lemma disc_cert_hook (w : nat) (digit : Z)
      (Hw : (w < 85)%nat) (Hdig : 0 <= digit < 8) :
    is_square
      (window_disc
        (List.nth w (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        digit) = false.
  Proof.
    pose proof (window_disc_qr_spend_auth_g_all_Z w digit Hw Hdig) as Hd.
    unfold sag_table, sag_default in Hd.
    exact Hd.
  Qed.

  (** The statement of [OrchardProtocolEquiv.spend_auth_g_mul_protocol]
      ([circuit_proof/protocol_equiv.v]), proved standalone. *)
  Theorem spend_auth_g_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.spend_auth_g orchard_internal_params) k) =
    OrchardProtocolSpec.mul_spend_auth_g k.
  Proof.
    unfold OrchardProtocolSpec.mul_spend_auth_g.
    assert (Hk' : 0 <= k < 8 ^ Z.of_nat (S 84)) by exact Hk.
    exact (ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul
      PallasGenerators.spend_auth_g_G
      PallasGenerators.spend_auth_g_on_curve
      PallasGenerators.spend_auth_g_reduced
      84 ltac:(lia) ltac:(lia)
      PallasGenerators.spend_auth_g_ne_identity
      PallasGeneratorsOrder.spend_auth_g_order
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      spec_table_length
      x_cert_hook sign_cert_hook disc_cert_hook
      k Hk').
  Qed.
End SpendAuthGMulProtocol.
