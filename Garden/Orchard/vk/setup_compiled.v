(** * Compiled-system bridge for Orchard verifying-key setup provenance *)

Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.vk.setup.

Module OrchardVkSetupCompiled.

(** The degree consumed by the lightweight domain computation is exactly the
    degree of Garden's compiled Orchard constraint system. *)
Lemma circuit_degree_refined :
  OrchardVkSetup.circuit_degree =
    Plonkish.system_degree_with_minimum
      orchard_indexed_system
      OrchardConfigure.minimum_degree.
Proof.
  rewrite OrchardConfigure.minimum_degree_eq.
  change
    (OrchardVkSetup.circuit_degree =
      Plonkish.system_degree orchard_indexed_system).
  rewrite OrchardCompiledAlgebraic.orchard_degree.
  reflexivity.
Qed.

Record certificate : Prop := {
  setup_certified : OrchardVkSetup.certificate;
  compiled_degree_refined :
    OrchardVkSetup.circuit_degree =
      Plonkish.system_degree_with_minimum
        orchard_indexed_system
        OrchardConfigure.minimum_degree;
}.

Theorem certified : certificate.
Proof.
  constructor.
  - exact OrchardVkSetup.certified.
  - exact circuit_degree_refined.
Qed.

End OrchardVkSetupCompiled.
