(** * Orchard [Proof::verify] wrapper

    Transcription of [orchard/src/circuit.rs] verify-time surface:
    circuit-version gating of [disableCrossAddress], public-input
    encoding ([Instance::to_halo2_instance]), and the call to
    [plonk::verify_proof] with [Blake2bRead] and [SingleVerifier]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.plonk.
Require Import Garden.Halo2.halo2_proofs.plonk.verifier.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.

Import List.ListNotations.
Global Open Scope Z_scope.

Module OrchardVerifier.
  Inductive CircuitVersion : Set :=
  | InsecurePreNu6_2
  | FixedPostNu6_2
  | PostNu6_3.

  Definition supports_cross_address_restriction (v : CircuitVersion) : bool :=
    match v with
    | PostNu6_3 => true
    | InsecurePreNu6_2 | FixedPostNu6_2 => false
    end.

  Record Instance : Set := {
    anchor : Z;
    cv_net_x : Z;
    cv_net_y : Z;
    nf_old : Z;
    rk_x : Z;
    rk_y : Z;
    cmx : Z;
    enable_spend : bool;
    enable_output : bool;
    cross_address_disabled : bool;
  }.

  Definition bool_to_scalar (b : bool) : Z :=
    if b then 1 else 0.

  Definition to_halo2_instance (i : Instance) : list Z :=
    [ i.(anchor);
      i.(cv_net_x);
      i.(cv_net_y);
      i.(nf_old);
      i.(rk_x);
      i.(rk_y);
      i.(cmx);
      bool_to_scalar i.(enable_spend);
      bool_to_scalar i.(enable_output);
      bool_to_scalar i.(cross_address_disabled)
    ].

  Record Proof : Set := {
    bytes : list Z;
  }.

  Record VerifyingKey : Set := {
    params : Params.t;
    plonk_vk : Garden.Halo2.halo2_proofs.plonk.VerifyingKey.t;
    circuit_version : CircuitVersion;
  }.

  Definition verify (proof : Proof) (ovk : VerifyingKey) (instances : list Instance) :
      Result.t unit Error.t :=
    if List.existsb (fun i => i.(cross_address_disabled)) instances
         && negb (supports_cross_address_restriction ovk.(circuit_version))
    then Result.Err Error.InvalidInstances
    else
      let halo2_instances :=
        List.map (fun i => [to_halo2_instance i]) instances in
      let tr := Blake2bRead.init proof.(bytes) in
      PlonkVerifier.verify_proof ovk.(params) ovk.(plonk_vk) halo2_instances tr.
End OrchardVerifier.
