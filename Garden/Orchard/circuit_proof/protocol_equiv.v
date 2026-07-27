Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.protocol_mul.spend_auth_g.
Require Import Garden.Orchard.circuit_proof.protocol_mul.value_commit_v.
Require Import Garden.Orchard.circuit_proof.protocol_mul.value_commit_r.
Require Import Garden.Orchard.circuit_proof.protocol_mul.nullifier_k.
Require Import Garden.Orchard.circuit_proof.protocol_mul.note_commit_r.
Require Import Garden.Orchard.circuit_proof.protocol_mul.signed.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   composing the per-base bridge theorems never evaluates [modpow] over the
   concrete Pallas [(p-1)/2] exponent (see [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

(** * Circuit-structured spec ↔ protocol-aligned spec

    The equivalence surface between [OrchardCircuitSpec] at the concrete
    circuit parameters ([orchard_internal_params]) and the protocol-aligned
    [OrchardProtocolSpec] ([Garden/Orchard/protocol_spec.v]): per fixed base,
    the windowed Lagrange-table fold with canonical square-root witnesses
    equals the group multiple [Pallas.mul] of the base's affine generator;
    per output, [OrchardActionInputs.output] equals the protocol form on
    protocol-typed inputs.

    Proof material.  Each per-base bridge delegates to its instance of the
    Γ-free core theorem
    [ProtocolMulCore.fixed_scalar_mul_canonical_eq_mul]
    ([circuit_proof/protocol_mul/core.v], instantiated per base in
    [circuit_proof/protocol_mul/<base>.v]): the per-window certificates
    identify each canonical window point with [repr ([window_scalar w d] G)],
    the fold composes those multiples by the group law, and the window
    scalars telescope to the scalar itself over the canonical base-8 digits.
    [output_protocol_eq] assembles the five bridges output by output, with
    the signed-value algebra of [circuit_proof/protocol_mul/signed.v] on the
    CV_NET leg.

    The [ValidActionInputs] track — the input-side conditions of
    §4.18.4 of the Zcash protocol specification ([docs/protocol.pdf]) —
    lives in [circuit_proof/valid_action_inputs.v]; this file keeps only the
    spec-coincidence domain [ProtocolTypedInputs] that
    [output_protocol_eq] quantifies over. *)

Module OrchardProtocolEquiv.
  Import OrchardActionInputs.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Per-base bridges: table fold = group multiple

      For each Orchard fixed base: the [EccSpec.fixed_scalar_mul] fold over
      the concrete circuit table, with the canonical square-root witnesses,
      is the [Pallas.mul] group multiple of the base's affine generator.
      The scalar ranges are the folds' full window domains — [8⁸⁵ = 2²⁵⁵]
      for the 85-window bases, [8²² = 2⁶⁶] for the 22-window short base. *)

  Theorem spend_auth_g_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.spend_auth_g orchard_internal_params) k) =
    OrchardProtocolSpec.mul_spend_auth_g k.
  Proof.
    exact (SpendAuthGMulProtocol.spend_auth_g_mul_protocol k Hk).
  Qed.

  Theorem value_commit_v_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 22) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_v orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.value_commit_v orchard_internal_params) k) =
    OrchardProtocolSpec.mul_value_commit_v k.
  Proof.
    exact (ValueCommitVMulProtocol.value_commit_v_mul_protocol k Hk).
  Qed.

  Theorem value_commit_r_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.value_commit_r orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.value_commit_r orchard_internal_params) k) =
    OrchardProtocolSpec.mul_value_commit_r k.
  Proof.
    exact (ValueCommitRMulProtocol.value_commit_r_mul_protocol k Hk).
  Qed.

  Theorem nullifier_k_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.nullifier_k orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.nullifier_k orchard_internal_params) k) =
    OrchardProtocolSpec.mul_nullifier_k k.
  Proof.
    exact (NullifierKMulProtocol.nullifier_k_mul_protocol k Hk).
  Qed.

  Theorem note_commit_r_mul_protocol (k : Z) (Hk : 0 <= k < 8 ^ 85) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params) k
      (canonical_us_for (OrchardCircuitSpec.note_commit_r orchard_internal_params) k) =
    OrchardProtocolSpec.mul_note_commit_r k.
  Proof.
    exact (NoteCommitRMulProtocol.note_commit_r_mul_protocol k Hk).
  Qed.

  (** ** Protocol-typed inputs

      The input ranges under which the circuit-structured and protocol
      output functions coincide.  Every conjunct is enforced by the circuit
      on a satisfying assignment (window range checks for the three
      full-width scalars, the 64 < 66-bit magnitude range check, the sign
      gate), so [read_action_inputs Γ] satisfies this predicate under
      [Holds Γ] — [OrchardValidActionInputs.protocol_typed_inputs_of_holds]
      ([circuit_proof/valid_action_inputs.v]). *)
  Definition ProtocolTypedInputs (inp : OrchardSpec.ActionInputs) : Prop :=
    0 <= OrchardSpec.in_alpha inp < 8 ^ 85 /\
    0 <= OrchardSpec.in_rcv inp < 8 ^ 85 /\
    0 <= OrchardSpec.in_rcm_new inp < 8 ^ 85 /\
    0 <= OrchardSpec.in_magnitude inp < 8 ^ 22 /\
    (OrchardSpec.in_sign inp = 1 \/
     OrchardSpec.in_sign inp = Primes.pallas_p - 1).

  (** ** The action-level equivalence

      The witness-free circuit-structured output record
      ([OrchardActionInputs.output], the right-hand side of
      [OrchardAction.satisfies_specification]'s circuit-structured
      composition point) equals the protocol-aligned
      action spec on protocol-typed inputs.  Composed with the per-output
      bridges, this yields the functional-correctness theorem
      [OrchardAction.satisfies_specification] and its determinism corollary
      [OrchardAction.deterministic]
      ([circuit_proof/main.v]). *)

  (** Projection read-offs of the canonical witness: each [w_us_*] field of
      [canonical_witness inp] is its [canonical_us_for] application
      (record-literal projections, named so the assembly proof rewrites them
      into the bridge spellings without reducing the spec term). *)
  Lemma w_us_alpha_canonical (inp : OrchardSpec.ActionInputs) :
    OrchardCircuitSpec.w_us_alpha (canonical_witness inp) =
    canonical_us_for (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (OrchardSpec.in_alpha inp).
  Proof. reflexivity. Qed.

  Lemma w_us_v_canonical (inp : OrchardSpec.ActionInputs) :
    OrchardCircuitSpec.w_us_v (canonical_witness inp) =
    canonical_us_for (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      (OrchardSpec.in_magnitude inp).
  Proof. reflexivity. Qed.

  Lemma w_us_rcv_canonical (inp : OrchardSpec.ActionInputs) :
    OrchardCircuitSpec.w_us_rcv (canonical_witness inp) =
    canonical_us_for (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      (OrchardSpec.in_rcv inp).
  Proof. reflexivity. Qed.

  Lemma w_us_k_canonical (inp : OrchardSpec.ActionInputs) :
    OrchardCircuitSpec.w_us_k (canonical_witness inp) =
    canonical_us_for (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      (Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp)
         (OrchardSpec.in_rho_old inp) +F OrchardSpec.in_psi_old inp).
  Proof. reflexivity. Qed.

  Lemma w_us_rcm_canonical (inp : OrchardSpec.ActionInputs) :
    OrchardCircuitSpec.w_us_rcm (canonical_witness inp) =
    canonical_us_for (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (OrchardSpec.in_rcm_new inp).
  Proof. reflexivity. Qed.

  (** The nullifier scalar is a reduced field element, hence inside the
      85-window domain: [0 <= x mod p < p < 8^85]. *)
  Lemma nullifier_scalar_range (inp : OrchardSpec.ActionInputs) :
    0 <= Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp)
           (OrchardSpec.in_rho_old inp) +F OrchardSpec.in_psi_old inp
      < 8 ^ 85.
  Proof.
    assert (Hp85 : Primes.pallas_p < 8 ^ 85)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    unfold BinOp.add.
    pose proof (Z.mod_pos_bound
      (Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp)
         (OrchardSpec.in_rho_old inp) + OrchardSpec.in_psi_old inp)
      Primes.pallas_p
      ltac:(unfold Primes.pallas_p, Primes.t_p; lia)) as Hb.
    clear -Hp85 Hb.
    lia.
  Qed.

  (** Per output: [anchor] is shared verbatim; [rk] and [nf_old] rewrite one
      bridge each (the [nf] scalar is in range by [nullifier_scalar_range]);
      [cv_net] rewrites the two value-commit bridges and closes with the
      signed-value algebra ([SignedValueAlgebra.value_commit_signed_eq]);
      [cmx] rewrites the [note_commit_r] bridge, with the rewritten [nf_old]
      threading into [rho_new] on both sides.  Assembled in the congruence
      style of [orchard_action_spec_us_congr] ([circuit_proof/inputs.v]):
      unfold both action specs, rewrite the five bridges syntactically, and
      finish with a [reflexivity] on literally identical records — no
      unification ever compares differing terms under [fixed_scalar_mul] or
      the Sinsemilla hash fold, and no record eta touches the spec term. *)
  Theorem output_protocol_eq
      (inp : OrchardSpec.ActionInputs)
      (Htyped : ProtocolTypedInputs inp) :
    output inp =
    OrchardProtocolSpec.orchard_action_spec orchard_circuit_params inp.
  Proof.
    destruct Htyped as (Halpha & Hrcv & Hrcm & Hmag & Hsign).
    unfold output, output_with_witness,
      OrchardCircuitSpec.orchard_action_spec, OrchardProtocolSpec.orchard_action_spec.
    cbv zeta.
    rewrite w_us_alpha_canonical, w_us_v_canonical, w_us_rcv_canonical,
      w_us_k_canonical, w_us_rcm_canonical.
    unfold OrchardCircuitSpec.value_commit, OrchardCircuitSpec.nullifier,
      OrchardCircuitSpec.spend_auth_randomize, OrchardCircuitSpec.OrchardCmx,
      OrchardCircuitSpec.note_commit,
      OrchardProtocolSpec.nullifier, OrchardProtocolSpec.spend_auth_randomize,
      OrchardProtocolSpec.OrchardCmx, OrchardProtocolSpec.note_commit.
    cbv zeta.
    rewrite (SpendAuthGMulProtocol.spend_auth_g_mul_protocol
      (OrchardSpec.in_alpha inp) Halpha).
    rewrite (ValueCommitVMulProtocol.value_commit_v_mul_protocol
      (OrchardSpec.in_magnitude inp) Hmag).
    rewrite (ValueCommitRMulProtocol.value_commit_r_mul_protocol
      (OrchardSpec.in_rcv inp) Hrcv).
    rewrite (NullifierKMulProtocol.nullifier_k_mul_protocol
      _ (nullifier_scalar_range inp)).
    rewrite (NoteCommitRMulProtocol.note_commit_r_mul_protocol
      (OrchardSpec.in_rcm_new inp) Hrcm).
    rewrite (SignedValueAlgebra.value_commit_signed_eq
      (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp)
      (OrchardSpec.in_rcv inp) (proj1 Hmag) Hsign).
    reflexivity.
  Qed.

End OrchardProtocolEquiv.
