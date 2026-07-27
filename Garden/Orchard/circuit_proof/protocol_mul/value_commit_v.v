(** * ValueCommitV: the canonical-witness table fold is the group multiple

    The ValueCommitV (CV_NET short base, 22 windows) instance of the Γ-free
    generic wrapper [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([circuit_proof/protocol_mul/core.v]): for [0 <= k < 8^22], the
    [EccSpec.fixed_scalar_mul] fold over the concrete 22-window circuit table
    [OrchardCircuitSpec.value_commit_v orchard_internal_params] with the canonical
    square-root witnesses equals
    [OrchardProtocolSpec.mul_value_commit_v k = repr ([k] value_commit_v_G)]
    — the [value_commit_v_mul_protocol] statement of
    [circuit_proof/protocol_equiv.v].

    The core wrapper is generic in the last window index [m] (window count
    [S m]); the short base instantiates it at [m := 21], the same
    [(d + 2)·8^w] non-last / offset-correcting last window convention as the
    full-width [m := 84] bases ([circuit_proof/value_commit_v/table.v] builds
    the certificate table as [nonlast_points 21 G ++ [last_row (base_pow8 21 G)
    ([window_offset_sum 21] G)]], matching the core hooks' shape verbatim).

    Certificate hooks (all [Qed], one [vm_compute] each, in their own leaf
    files):
    - x-coordinate: [ValueCommitVFixedWindowCert.x_check_entry]
      ([circuit_proof/value_commit_v/x_cert.v]);
    - window sign (positive QR): [ValueCommitVWindowSignCert.y_check_entry]
      ([circuit_proof/value_commit_v/sign_cert.v]);
    - window discriminant (non-residue): [window_disc_qr_value_commit_v_all_Z]
      ([circuit_proof/value_commit_v/disc_cert.v]).
    Generator facts: [PallasGenerators.value_commit_v_{on_curve,reduced,
    ne_identity}] and [PallasGeneratorsOrder.value_commit_v_order]. *)

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
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Garden.Orchard.circuit_proof.value_commit_v.table.
Require Import Garden.Orchard.circuit_proof.value_commit_v.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.disc_cert.
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

Module ValueCommitVMulProtocol.

  (** ** The three certificate hooks, in the core wrapper's exact shapes

      Each is the per-base certificate lemma with the file-local aliases
      ([ValueCommitVFixedWindowCert.table]/[default],
      [ValueCommitVFullTable.full_table]/[G]) unfolded to the spellings the
      core hooks use: the spec table
      [OrchardCircuitSpec.value_commit_v orchard_internal_params], the default window
      [OrchardActionFixedBase.fixed_window_default], and the builder-form
      multiple table over [PallasGenerators.value_commit_v_G] at [m := 21]. *)

  (** The Lagrange x-coordinate hook ([Hx_cert] of [ProtocolMulGen]). *)
  Lemma value_commit_v_x_cert_hook (w i : nat)
      (Hw : (w < 22)%nat) (Hi : (i < 8)%nat) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.value_commit_v orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        (Z.of_nat i) 0) =
    Point.x
      (PallasModel.repr
        (List.nth i
          (List.nth w
            (FixedBaseTableDefs.nonlast_points 21
               PallasGenerators.value_commit_v_G ++
             [FixedBaseTableDefs.last_row
                (FixedBaseTableDefs.base_pow8 21
                  PallasGenerators.value_commit_v_G)
                (Pallas.mul (FixedBaseTableDefs.window_offset_sum 21)
                  PallasGenerators.value_commit_v_G)]) [])
          Pallas.identity)).
  Proof.
    pose proof (ValueCommitVFixedWindowCert.x_check_entry w i Hw Hi) as Hx.
    unfold ValueCommitVFixedWindowCert.table,
      ValueCommitVFixedWindowCert.default in Hx.
    unfold ValueCommitVFullTable.full_table, ValueCommitVFullTable.G in Hx.
    exact Hx.
  Qed.

  (** The positive QR window-sign hook ([Hsign_cert] of [ProtocolMulGen]). *)
  Lemma value_commit_v_sign_cert_hook (w i : nat)
      (Hw : (w < 22)%nat) (Hi : (i < 8)%nat) :
    is_square
      (UnOp.from
        (EccSpec.fw_z
          (List.nth w (OrchardCircuitSpec.value_commit_v orchard_internal_params)
            OrchardActionFixedBase.fixed_window_default)
         +F Point.y
              (PallasModel.repr
                (List.nth i
                  (List.nth w
                    (FixedBaseTableDefs.nonlast_points 21
                       PallasGenerators.value_commit_v_G ++
                     [FixedBaseTableDefs.last_row
                        (FixedBaseTableDefs.base_pow8 21
                          PallasGenerators.value_commit_v_G)
                        (Pallas.mul (FixedBaseTableDefs.window_offset_sum 21)
                          PallasGenerators.value_commit_v_G)]) [])
                  Pallas.identity)))) = true.
  Proof.
    pose proof (ValueCommitVWindowSignCert.y_check_entry w i Hw Hi) as Hy.
    unfold ValueCommitVWindowSignCert.table,
      ValueCommitVWindowSignCert.default in Hy.
    unfold ValueCommitVFullTable.full_table, ValueCommitVFullTable.G in Hy.
    exact Hy.
  Qed.

  (** The non-residue window-discriminant hook ([Hdisc_cert] of
      [ProtocolMulGen]).  The certificate is stated over the definitionally
      equal table spelling [EccSpec.fixed_table_of_rows
      value_commit_v.short_fixed_rows] (and the same default-window record);
      [exact] crosses the spelling by conversion — [is_square] stays opaque,
      so only the small window data is compared. *)
  Lemma value_commit_v_disc_cert_hook (w : nat) (digit : Z)
      (Hw : (w < 22)%nat) (Hdig : 0 <= digit < 8) :
    is_square
      (window_disc
        (List.nth w (OrchardCircuitSpec.value_commit_v orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        digit) = false.
  Proof.
    exact (window_disc_qr_value_commit_v_all_Z w digit Hw Hdig).
  Qed.

  (** ** The ValueCommitV protocol bridge

      The exact [value_commit_v_mul_protocol] statement of
      [circuit_proof/protocol_equiv.v]: the core wrapper at
      [G := value_commit_v_G], [m := 21] (22 windows), the spec table, and
      the three hooks above; [8^22 = 8^(Z.of_nat (S 21))] by conversion. *)
  Theorem value_commit_v_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 22) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_v orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.value_commit_v orchard_internal_params) k) =
    OrchardProtocolSpec.mul_value_commit_v k.
  Proof.
    unfold OrchardProtocolSpec.mul_value_commit_v.
    assert (Hk' : 0 <= k < 8 ^ Z.of_nat 22) by exact Hk.
    exact (ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul
      PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_on_curve
      PallasGenerators.value_commit_v_reduced
      21 ltac:(lia) ltac:(lia)
      PallasGenerators.value_commit_v_ne_identity
      PallasGeneratorsOrder.value_commit_v_order
      (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      OrchardActionFixedBase.value_commit_v_table_length
      value_commit_v_x_cert_hook
      value_commit_v_sign_cert_hook
      value_commit_v_disc_cert_hook
      k Hk').
  Qed.

End ValueCommitVMulProtocol.
