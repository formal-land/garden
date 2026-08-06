(** * Public end-to-end provenance statement for the deployed Orchard VK

    The deployed literals and byte dump remain useful as right-hand-side
    regression targets.  This statement separates those targets from the
    values derived by Garden: setup and evaluation-domain data come from the
    curve and [k = 11], the constraint-system fields come from the explicit
    formal configure-metadata trace and selector compression, and the 44
    points come from mathematical [commit_lagrange]. *)

From Stdlib Require Import ZArith Lists.List Strings.PrimString
  Numbers.Cyclic.Int63.Uint63.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Field.Field.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.Halo2.plonkish.evaluation_domain.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.certificate.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.vk.bytes.
Require Import Garden.Orchard.vk.data.
Require Import Garden.Orchard.vk.print.
Require Import Garden.Orchard.vk.setup.
Require Import Garden.Orchard.vk.setup_compiled.
Require Import Garden.Orchard.vk.parity.
Require Import Garden.Orchard.vk.transcript_repr.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Abstract.
Require Import Garden.Orchard.vk.provenance.ModelColumnsCorrect.
Require Import Garden.Orchard.vk.provenance.PinnedSpec.

Import Plonkish.

Module OrchardVkFullAbstract.

Local Open Scope Z_scope.

(** The optimized commitment semantics uses checked inverse-root and
    inverse-size witnesses.  Tie both witnesses explicitly to the domain
    derived by [OrchardVkSetup], rather than leaving that transport implicit
    through the cached [PolyDomain] constants. *)
Lemma commitment_omega_inverse_from_setup :
  (OrchardVkSetup.omega_from_pasta_root * VkMsm.omega_inv)
    mod Primes.pallas_p = 1.
Proof.
  rewrite OrchardVkSetup.omega_from_pasta_root_matches.
  exact VkMsm.omega_inv_spec.
Qed.

Lemma commitment_domain_size_inverse_from_setup :
  (Z.of_nat
      (EvaluationDomainSetup.domain_size OrchardVkSetup.k) * VkMsm.n_inv)
    mod Primes.pallas_p = 1.
Proof.
  change ((2048 * VkMsm.n_inv) mod Primes.pallas_p = 1).
  exact VkMsm.n_inv_spec.
Qed.

(** The permutation-label coset generator is likewise a checked Pasta-field
    schedule, not a value copied from the deployed commitment list. *)
Lemma permutation_delta_from_generator :
  fast_pow_modulo_positive 1 5 Primes.pallas_p
      (Z.to_pos (2 ^ Z.of_nat OrchardVkSetup.scalar_two_adicity)) =
    OrchardCompiledAlgebraic.delta.
Proof.
  change
    (fast_pow_modulo_positive 1 5 Primes.pallas_p 4294967296 =
      OrchardCompiledAlgebraic.delta).
  exact OrchardCompiledAlgebraic.delta_generator.
Qed.

(** Turn a printer coordinate pair into the corresponding abstract affine
    Vesta point. *)
Definition point_of_coordinates (coordinates : Z * Z) : Vesta.point :=
  Vesta.affine (fst coordinates) (snd coordinates).

(** A coordinate view is not accepted merely because it prints the deployed
    bytes.  It must also denote every mathematical [commit_lagrange] result.
    The first field records the structural substitution equality used by T1
    and T2: the explicit generated coordinate view equals the deployed
    right-hand side.  Independent recomputation of that view is a
    generator/oracle property outside the kernel. *)
Record coordinate_certificate
    (coordinates : VkPinnedPrint.commitment_coordinates) : Prop := {
  coordinates_match_deployed :
    coordinates = VkPinnedPrint.pinned_commitment_coordinates;
  fixed_coordinates_refined :
    forall index, (index < 29)%nat ->
      OrchardVkAbstract.fixed_commitment index =
        point_of_coordinates
          (List.nth index
            coordinates.(VkPinnedPrint.fixed_commitment_coordinates) (0, 0));
  permutation_coordinates_refined :
    forall index, (index < 15)%nat ->
      OrchardVkAbstract.permutation_commitment index =
        point_of_coordinates
          (List.nth index
            coordinates.(VkPinnedPrint.permutation_commitment_coordinates)
            (0, 0));
}.

Theorem coordinates_certified
    (coordinates : VkPinnedPrint.commitment_coordinates)
    (commitments : OrchardVkAbstract.certificate)
    (Hcoordinates :
      coordinates = VkPinnedPrint.pinned_commitment_coordinates) :
  coordinate_certificate coordinates.
Proof.
  constructor.
  - exact Hcoordinates.
  - intros index Hindex.
    rewrite Hcoordinates.
    rewrite (OrchardVkAbstract.fixed_commitments_refined
      commitments index Hindex).
    change
      (VkPinnedSpec.fixed_point index =
        point_of_coordinates
          (List.nth index VkPinnedData.fixed_commitments (0, 0))).
    unfold point_of_coordinates, VkPinnedSpec.fixed_point,
      VkPinnedSpec.point, VkPinnedSpec.pair.
    destruct (List.nth index VkPinnedData.fixed_commitments (0, 0)).
    reflexivity.
  - intros index Hindex.
    rewrite Hcoordinates.
    rewrite (OrchardVkAbstract.permutation_commitments_refined
      commitments index Hindex).
    change
      (VkPinnedSpec.permutation_point index =
        point_of_coordinates
          (List.nth index VkPinnedData.permutation_commitments (0, 0))).
    unfold point_of_coordinates, VkPinnedSpec.permutation_point,
      VkPinnedSpec.point, VkPinnedSpec.pair.
    destruct (List.nth index VkPinnedData.permutation_commitments (0, 0)).
    reflexivity.
Qed.

(** T1 and T2 are stated for an explicit commitment-coordinate input.  Thus
    the final generated theorem talks about the printer instantiated with
    emitter-produced MSM coordinates, rather than a printer whose commitment
    fields are definitionally [VkPinnedData].  The independent Python
    recomputation is outside the kernel. *)
Record non_commitment_certificate
    (coordinates : VkPinnedPrint.commitment_coordinates) : Prop := {
  setup_and_domain : OrchardVkSetupCompiled.certificate;
  constraint_system : OrchardCompiledCertificate.certificate;
  deployed_rendering :
    VkPinnedPrint.vk_pretty_with coordinates = VkPinnedBytes.dump;
  compact_rendering_length :
    PrimString.length (VkPinnedPrint.vk_compact_with coordinates) =
      285134%uint63;
  transcript_representation :
    Blake2b.word_of_le_bytes
      (Blake2b.blake2b 64 Blake2b.zero16 VkTranscriptRepr.personal
        (VkTranscriptRepr.transcript_input
          (VkPinnedPrint.vk_compact_with coordinates)))
      mod Primes.pallas_p = VkTranscriptRepr.transcript_repr;
}.

Theorem non_commitments_certified
    (coordinates : VkPinnedPrint.commitment_coordinates)
    (Hcoordinates :
      coordinates = VkPinnedPrint.pinned_commitment_coordinates) :
  non_commitment_certificate coordinates.
Proof.
  rewrite Hcoordinates.
  constructor.
  - exact OrchardVkSetupCompiled.certified.
  - exact OrchardCompiledCertificate.certified.
  - exact VkPinnedParity.vk_pinned_dump_parity.
  - exact VkPinnedParity.vk_pinned_compact_length.
  - exact VkTranscriptRepr.transcript_repr_spec.
Qed.

(** The generated commitment leaves instantiate the final field.  The public
    result has no premises: generated numbers are witnesses checked by Rocq,
    never axioms or hypotheses. *)
Record certificate_for
    (coordinates : VkPinnedPrint.commitment_coordinates) : Prop := {
  fixed_column_model : VkModelColumnsCorrect.certificate;
  synthesis_usable_rows :
    Garden.Orchard.circuit.orchard_usable_rows =
      Domain.usable_rows OrchardCompiled.orchard_domain;
  commitment_omega_inverse :
    (OrchardVkSetup.omega_from_pasta_root * VkMsm.omega_inv)
      mod Primes.pallas_p = 1;
  commitment_domain_size_inverse :
    (Z.of_nat
        (EvaluationDomainSetup.domain_size OrchardVkSetup.k) * VkMsm.n_inv)
      mod Primes.pallas_p = 1;
  permutation_delta_schedule :
    fast_pow_modulo_positive 1 5 Primes.pallas_p
        (Z.to_pos (2 ^ Z.of_nat OrchardVkSetup.scalar_two_adicity)) =
      OrchardCompiledAlgebraic.delta;
  coordinate_fields : coordinate_certificate coordinates;
  non_commitment_fields : non_commitment_certificate coordinates;
  commitment_fields : OrchardVkAbstract.certificate;
}.

(** Keep the public statement propositional while carrying the explicit
    generated coordinate view as an existential witness. *)
Definition certificate : Prop :=
  exists coordinates, certificate_for coordinates.

Definition assemble
    (model_columns : VkModelColumnsCorrect.certificate)
    (usable_rows :
      Garden.Orchard.circuit.orchard_usable_rows =
        Domain.usable_rows OrchardCompiled.orchard_domain)
    (coordinates : VkPinnedPrint.commitment_coordinates)
    (Hcoordinates :
      coordinates = VkPinnedPrint.pinned_commitment_coordinates)
    (commitments : OrchardVkAbstract.certificate) : certificate.
Proof.
  exists coordinates.
  exact {|
    fixed_column_model := model_columns;
    synthesis_usable_rows := usable_rows;
    commitment_omega_inverse := commitment_omega_inverse_from_setup;
    commitment_domain_size_inverse :=
      commitment_domain_size_inverse_from_setup;
    permutation_delta_schedule := permutation_delta_from_generator;
    coordinate_fields :=
      coordinates_certified coordinates commitments Hcoordinates;
    non_commitment_fields :=
      non_commitments_certified coordinates Hcoordinates;
    commitment_fields := commitments;
  |}.
Defined.

End OrchardVkFullAbstract.
