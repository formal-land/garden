(** * ValueCommitR: the canonical-witness table fold is the group multiple

    The ValueCommitR (CV_NET blind base, full-width 85 windows) instance of
    the Γ-free generic wrapper
    [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([circuit_proof/protocol_mul/core.v]): for [0 <= k < 8^85], the
    [EccSpec.fixed_scalar_mul] fold over the concrete 85-window circuit table
    [OrchardCircuitSpec.value_commit_r orchard_internal_params] with the canonical
    square-root witnesses equals
    [OrchardProtocolSpec.mul_value_commit_r k = repr ([k] value_commit_r_G)]
    — the [value_commit_r_mul_protocol] statement of
    [circuit_proof/protocol_equiv.v].

    The core wrapper is generic in the last window index [m] (window count
    [S m]); the full-width base instantiates it at [m := 84]
    ([circuit_proof/value_commit_r/table.v] builds the certificate table as
    [nonlast_points 84 G ++ [last_row (base_pow8 84 G)
    ([window_offset_sum 84] G)]], matching the core hooks' shape verbatim).
    The spec table's length fact is
    [OrchardActionUsFree.value_commit_r_table_length]
    ([circuit_proof/us_free/main.v]).

    Certificate hooks (all [Qed], one [vm_compute] each, in their own leaf
    files):
    - x-coordinate: [ValueCommitRFixedWindowCert.x_check_entry]
      ([circuit_proof/value_commit_r/x_cert.v]);
    - window sign (positive QR): [ValueCommitRWindowSignCert.y_check_entry]
      ([circuit_proof/value_commit_r/sign_cert.v]);
    - window discriminant (non-residue): [window_disc_qr_value_commit_r_all_Z]
      ([circuit_proof/value_commit_r/disc_cert.v]).
    Generator facts: [PallasGenerators.value_commit_r_{on_curve,reduced,
    ne_identity}] and [PallasGeneratorsOrder.value_commit_r_order]. *)

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
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Garden.Orchard.circuit_proof.value_commit_r.table.
Require Import Garden.Orchard.circuit_proof.value_commit_r.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Import OrchardActionInputs.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so [is_square]/[field_sqrt]/[fixed_window_point] below are at
   [pallas_p] (every other EC and Orchard file sets this). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   up-to-conversion matching in the hook composition below never evaluates
   [modpow] over the concrete Pallas [(p-1)/2] exponent (see
   [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module ValueCommitRMulProtocol.

  (** ** The three certificate hooks, in the core wrapper's exact shapes

      Each is the per-base certificate lemma with the file-local aliases
      ([ValueCommitRFixedWindowCert.table]/[default],
      [ValueCommitRFullTable.full_table]/[G]) unfolded to the spellings the
      core hooks use: the spec table
      [OrchardCircuitSpec.value_commit_r orchard_internal_params], the default window
      [OrchardActionFixedBase.fixed_window_default], and the builder-form
      multiple table over [PallasGenerators.value_commit_r_G] at [m := 84]. *)

  (** The Lagrange x-coordinate hook ([Hx_cert] of [ProtocolMulGen]). *)
  Lemma value_commit_r_x_cert_hook (w i : nat)
      (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.value_commit_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        (Z.of_nat i) 0) =
    Point.x
      (PallasModel.repr
        (List.nth i
          (List.nth w
            (FixedBaseTableDefs.nonlast_points 84
               PallasGenerators.value_commit_r_G ++
             [FixedBaseTableDefs.last_row
                (FixedBaseTableDefs.base_pow8 84
                  PallasGenerators.value_commit_r_G)
                (Pallas.mul (FixedBaseTableDefs.window_offset_sum 84)
                  PallasGenerators.value_commit_r_G)]) [])
          Pallas.identity)).
  Proof.
    pose proof (ValueCommitRFixedWindowCert.x_check_entry w i Hw Hi) as Hx.
    unfold ValueCommitRFixedWindowCert.table,
      ValueCommitRFixedWindowCert.default in Hx.
    unfold ValueCommitRFullTable.full_table, ValueCommitRFullTable.G in Hx.
    exact Hx.
  Qed.

  (** The positive QR window-sign hook ([Hsign_cert] of [ProtocolMulGen]). *)
  Lemma value_commit_r_sign_cert_hook (w i : nat)
      (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    is_square
      (UnOp.from
        (EccSpec.fw_z
          (List.nth w (OrchardCircuitSpec.value_commit_r orchard_internal_params)
            OrchardActionFixedBase.fixed_window_default)
         +F Point.y
              (PallasModel.repr
                (List.nth i
                  (List.nth w
                    (FixedBaseTableDefs.nonlast_points 84
                       PallasGenerators.value_commit_r_G ++
                     [FixedBaseTableDefs.last_row
                        (FixedBaseTableDefs.base_pow8 84
                          PallasGenerators.value_commit_r_G)
                        (Pallas.mul (FixedBaseTableDefs.window_offset_sum 84)
                          PallasGenerators.value_commit_r_G)]) [])
                  Pallas.identity)))) = true.
  Proof.
    pose proof (ValueCommitRWindowSignCert.y_check_entry w i Hw Hi) as Hy.
    unfold ValueCommitRWindowSignCert.table,
      ValueCommitRWindowSignCert.default in Hy.
    unfold ValueCommitRFullTable.full_table, ValueCommitRFullTable.G in Hy.
    exact Hy.
  Qed.

  (** The non-residue window-discriminant hook ([Hdisc_cert] of
      [ProtocolMulGen]).  The certificate is stated over the definitionally
      equal table spelling [EccSpec.fixed_table_of_rows
      value_commit_r.full_fixed_rows] (and the same default-window record);
      [exact] crosses the spelling by conversion — [is_square] stays opaque,
      so only the small window data is compared. *)
  Lemma value_commit_r_disc_cert_hook (w : nat) (digit : Z)
      (Hw : (w < 85)%nat) (Hdig : 0 <= digit < 8) :
    is_square
      (window_disc
        (List.nth w (OrchardCircuitSpec.value_commit_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        digit) = false.
  Proof.
    exact (window_disc_qr_value_commit_r_all_Z w digit Hw Hdig).
  Qed.

  (** ** The ValueCommitR protocol bridge

      The exact [value_commit_r_mul_protocol] statement of
      [circuit_proof/protocol_equiv.v]: the core wrapper at
      [G := value_commit_r_G], [m := 84] (85 windows), the spec table, and
      the three hooks above; [8^85 = 8^(Z.of_nat (S 84))] by conversion. *)
  Theorem value_commit_r_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_r orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.value_commit_r orchard_internal_params) k) =
    OrchardProtocolSpec.mul_value_commit_r k.
  Proof.
    unfold OrchardProtocolSpec.mul_value_commit_r.
    assert (Hk' : 0 <= k < 8 ^ Z.of_nat 85) by exact Hk.
    exact (ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul
      PallasGenerators.value_commit_r_G
      PallasGenerators.value_commit_r_on_curve
      PallasGenerators.value_commit_r_reduced
      84 ltac:(lia) ltac:(lia)
      PallasGenerators.value_commit_r_ne_identity
      PallasGeneratorsOrder.value_commit_r_order
      (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      OrchardActionUsFree.value_commit_r_table_length
      value_commit_r_x_cert_hook
      value_commit_r_sign_cert_hook
      value_commit_r_disc_cert_hook
      k Hk').
  Qed.

End ValueCommitRMulProtocol.
