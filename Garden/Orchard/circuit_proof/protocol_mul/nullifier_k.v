(** * NullifierK: table fold = group multiple

    The NullifierK (𝒦^Orchard, §4.16) instance of the Γ-free generic bridge
    [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([Garden/Orchard/circuit_proof/protocol_mul/core.v]): the [EccSpec]
    windowed Lagrange-table fold over the concrete circuit table
    [OrchardCircuitSpec.nullifier_k orchard_internal_params] with the canonical
    square-root witnesses equals the group multiple
    [OrchardProtocolSpec.mul_nullifier_k k = repr ([k] nullifier_k_G)], for
    the full 85-window scalar domain [0 <= k < 8^85].

    The generic wrapper is fed with:

    - the [PallasGenerators.nullifier_k_G] generator facts (on-curve,
      reduced, non-identity) and its prime order
      ([PallasGeneratorsOrder.nullifier_k_order]);
    - the Lagrange x-coordinate certificate
      [NullifierKFixedWindowCert.x_check_entry]
      ([circuit_proof/nullifier_k/x_cert.v]);
    - the positive QR window-sign certificate
      [NullifierKWindowSignCert.y_check_entry]
      ([circuit_proof/nullifier_k/sign_cert.v]);
    - the non-residue window-discriminant certificate
      [window_disc_qr_nullifier_k_all_Z]
      ([circuit_proof/nullifier_k/disc_cert.v]).

    The three hook lemmas below only cross the table-constant spellings
    ([NullifierKFixedWindowCert.table]/[NullifierKFullTable.full_table] and
    the disc certificate's [nk_table] are the circuit table by unfolding),
    so the wrapper instantiation is syntactic. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
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
Require Import Garden.Orchard.circuit_proof.cert_defs.
Require Import Garden.Orchard.circuit_proof.nullifier_k.table.
Require Import Garden.Orchard.circuit_proof.nullifier_k.x_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.disc_cert.
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   up-to-conversion matching against the certificate hooks below never
   evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent (see
   [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

(* Make scalar multiplication opaque to conversion as well: the hook
   statements contain closed multiples of the concrete 254-bit NullifierK
   generator ([base_pow8 84 G], [mul (window_offset_sum 84) G]), so any
   conversion fallback that reduced one to weak-head normal form would run
   the full double-and-add ladder (the same opaque window as in
   [circuit_proof/ladder/nullifier_k.v]). *)
Strategy opaque [Pallas.mul Weierstrass.mul].

Module NullifierKMulProtocol.
  Import OrchardActionInputs.

  (** The circuit table has the full 85 windows ([S 84]). *)
  Lemma nullifier_k_spec_table_length :
    List.length (OrchardCircuitSpec.nullifier_k orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  (** The Lagrange x-coordinate certificate, restated on the circuit table
      and the builder-form full table (the certificate's [table] and
      [NullifierKFullTable.full_table] aliases, unfolded). *)
  Lemma nullifier_k_x_hook (w i : nat) (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.nullifier_k orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        (Z.of_nat i) 0) =
    Point.x
      (PallasModel.repr
        (List.nth i
          (List.nth w
            (FixedBaseTableDefs.nonlast_points 84 PallasGenerators.nullifier_k_G
             ++ [FixedBaseTableDefs.last_row
                   (FixedBaseTableDefs.base_pow8 84
                     PallasGenerators.nullifier_k_G)
                   (Pallas.mul (FixedBaseTableDefs.window_offset_sum 84)
                     PallasGenerators.nullifier_k_G)]) [])
          Pallas.identity)).
  Proof.
    pose proof (NullifierKFixedWindowCert.x_check_entry w i Hw Hi) as Hx.
    unfold NullifierKFixedWindowCert.table, NullifierKFixedWindowCert.default,
      NullifierKFullTable.full_table, NullifierKFullTable.G in Hx.
    exact Hx.
  Qed.

  (** The positive QR window-sign certificate, restated the same way. *)
  Lemma nullifier_k_sign_hook (w i : nat)
      (Hw : (w < 85)%nat) (Hi : (i < 8)%nat) :
    is_square
      (UnOp.from
        (EccSpec.fw_z
          (List.nth w (OrchardCircuitSpec.nullifier_k orchard_internal_params)
            OrchardActionFixedBase.fixed_window_default)
         +F Point.y
              (PallasModel.repr
                (List.nth i
                  (List.nth w
                    (FixedBaseTableDefs.nonlast_points 84
                       PallasGenerators.nullifier_k_G
                     ++ [FixedBaseTableDefs.last_row
                           (FixedBaseTableDefs.base_pow8 84
                             PallasGenerators.nullifier_k_G)
                           (Pallas.mul
                             (FixedBaseTableDefs.window_offset_sum 84)
                             PallasGenerators.nullifier_k_G)]) [])
                  Pallas.identity)))) = true.
  Proof.
    pose proof (NullifierKWindowSignCert.y_check_entry w i Hw Hi) as Hy.
    unfold NullifierKWindowSignCert.table, NullifierKWindowSignCert.default,
      NullifierKFullTable.full_table, NullifierKFullTable.G in Hy.
    exact Hy.
  Qed.

  (** The non-residue window-discriminant certificate on the circuit table
      (the certificate's [nk_table]/[nk_default] are the circuit table and
      default window by conversion). *)
  Lemma nullifier_k_disc_hook (w : nat) (digit : Z)
      (Hw : (w < 85)%nat) (Hdig : 0 <= digit < 8) :
    is_square
      (window_disc
        (List.nth w (OrchardCircuitSpec.nullifier_k orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default)
        digit) = false.
  Proof.
    exact (window_disc_qr_nullifier_k_all_Z w digit Hw Hdig).
  Qed.

  (** The NullifierK table-fold = group-multiple bridge: the statement of
      [OrchardProtocolEquiv.nullifier_k_mul_protocol]
      ([circuit_proof/protocol_equiv.v]). *)
  Theorem nullifier_k_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.nullifier_k orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.nullifier_k orchard_internal_params) k) =
    OrchardProtocolSpec.mul_nullifier_k k.
  Proof.
    unfold OrchardProtocolSpec.mul_nullifier_k.
    exact (ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul
      PallasGenerators.nullifier_k_G
      PallasGenerators.nullifier_k_on_curve
      PallasGenerators.nullifier_k_reduced
      84 ltac:(lia) ltac:(lia)
      PallasGenerators.nullifier_k_ne_identity
      PallasGeneratorsOrder.nullifier_k_order
      (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      nullifier_k_spec_table_length
      nullifier_k_x_hook
      nullifier_k_sign_hook
      nullifier_k_disc_hook
      k Hk).
  Qed.
End NullifierKMulProtocol.
