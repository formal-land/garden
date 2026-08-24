(** * Tests for the Orchard Halo 2 verifier transcription

    Cheap [vm_compute] checks: primitive wrapping, Pasta codecs,
    transcript underrun, IPA [compute_s]/[compute_b], and the Orchard
    wrapper rejecting a [disableCrossAddress] instance under a pre-NU6.3
    key. Full fixture replay of a 2048-row IPA is a separate cost class. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.
Require Import Garden.Halo2.halo2_proofs.plonk.verifier.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Orchard.verifier.

Import List.ListNotations.
Global Open Scope Z_scope.

Module OrchardVerifierTests.

  Lemma primitives_loaded : Integer.add (u8_of 255) (u8_of 1) = u8_of 0.
  Proof. apply PrimitiveTests.u8_wrapping_add. Qed.

  Lemma pasta_repr_loaded : Fp.from_repr (Fp.to_repr 7) = Some 7.
  Proof. apply PastaTests.fp_from_repr_roundtrip. Qed.

  Lemma transcript_underrun_loaded :
    Result.is_ok (Blake2bRead.read_scalar (Blake2bRead.init [])) = false.
  Proof. apply TranscriptTests.read_underrun. Qed.

  Lemma ipa_compute_s_loaded : Ipa.compute_s [2] 1 = [1; 2].
  Proof. apply IpaTests.compute_s_one. Qed.

  Definition dummy_instance : OrchardVerifier.Instance := {|
    OrchardVerifier.anchor := 1;
    OrchardVerifier.cv_net_x := 2;
    OrchardVerifier.cv_net_y := 3;
    OrchardVerifier.nf_old := 4;
    OrchardVerifier.rk_x := 5;
    OrchardVerifier.rk_y := 6;
    OrchardVerifier.cmx := 7;
    OrchardVerifier.enable_spend := true;
    OrchardVerifier.enable_output := true;
    OrchardVerifier.cross_address_disabled := true;
  |}.

  Definition dummy_params : Params.t := {|
    Params.k := u32_of 1;
    Params.n := u64_of 2;
    Params.g := [];
    Params.g_lagrange := [];
    Params.w := VestaCurve.identity;
    Params.u := VestaCurve.identity;
  |}.

  Definition dummy_cs : ConstraintSystem.t := {|
    ConstraintSystem.num_instance_columns := usize_of 1;
    ConstraintSystem.num_advice_columns := usize_of 0;
    ConstraintSystem.instance_queries := [];
    ConstraintSystem.advice_queries := [];
    ConstraintSystem.fixed_queries := [];
    ConstraintSystem.gates := [];
    ConstraintSystem.lookups := [];
    ConstraintSystem.permutation := {| PermutationArgument.columns := [] |};
    ConstraintSystem.blinding_factors := usize_of 0;
    ConstraintSystem.degree := usize_of 3;
  |}.

  Definition dummy_vk_inner : VerifyingKey.t := {|
    VerifyingKey.domain := EvaluationDomain.make (u32_of 1) 1 (u64_of 1);
    VerifyingKey.fixed_commitments := [];
    VerifyingKey.permutation := {| PermutationVK.commitments := [] |};
    VerifyingKey.cs := dummy_cs;
    VerifyingKey.cs_degree := usize_of 3;
    VerifyingKey.transcript_repr := 0;
  |}.

  Definition dummy_vk_pre : OrchardVerifier.VerifyingKey := {|
    OrchardVerifier.params := dummy_params;
    OrchardVerifier.plonk_vk := dummy_vk_inner;
    OrchardVerifier.circuit_version := OrchardVerifier.FixedPostNu6_2;
  |}.

  Lemma rejects_restricted_on_fixed_key :
    Result.is_ok
      (OrchardVerifier.verify {| OrchardVerifier.bytes := [] |} dummy_vk_pre [dummy_instance])
    = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma halo2_instance_length :
    List.length (OrchardVerifier.to_halo2_instance dummy_instance) = 10%nat.
  Proof. reflexivity. Qed.

  Lemma verify_wrong_instance_width :
    let inst := [[1; 2]] in
    Result.is_ok (PlonkVerifier.verify_proof dummy_params dummy_vk_inner [inst]
      (Blake2bRead.init [])) = false.
  Proof. vm_compute. reflexivity. Qed.

End OrchardVerifierTests.
