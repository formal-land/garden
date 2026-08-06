(** * Provenance of the Orchard verifying-key setup and domain literals

    The curve and [Params::new(11)] exponent are deployment inputs.  From
    those inputs and the proved degree of Garden's compiled Orchard system,
    this module executes the sizing and root schedules of Halo 2
    [EvaluationDomain::new].  The literals in [VkPinnedData] and
    [PolyDomain] are efficient cached witnesses on the right-hand side of
    closed equalities, not inputs to these derivations. *)

From Stdlib Require Import ZArith Strings.PrimString.
Require Import Garden.Field.Field.
Require Import Garden.Field.Hex.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.sswu.
Require Import Garden.Halo2.plonkish.evaluation_domain.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Orchard.vk.data.
Require Import Garden.Orchard.vk.parameters.

Local Open Scope Z_scope.

Module OrchardVkSetup.

Definition k : nat := OrchardVkParameters.k.
Definition scalar_two_adicity : nat :=
  OrchardVkParameters.scalar_two_adicity.

(** The small setup model receives the constraint-system degree computed by
    the plonkish compiler.  [Orchard/vk/setup_compiled.v] identifies this
    witness with [system_degree orchard_indexed_system] without making
    field/domain normalization depend on the full compiled-circuit import
    closure. *)
Definition circuit_degree : nat := 9%nat.

Definition extended_k_result : option nat :=
  EvaluationDomainSetup.extended_k
    scalar_two_adicity circuit_degree k.

Definition extended_k : nat :=
  match extended_k_result with
  | Some value => value
  | None => O
  end.

Definition omega_from_pasta_root : Z :=
  EvaluationDomainSetup.root_for_domain
    Primes.pallas_p IsoPallas.lambda
    scalar_two_adicity extended_k k.

Definition base_modulus : PrimString.string :=
  FieldHex.hex64 Vesta.vesta_p.

Definition scalar_modulus : PrimString.string :=
  FieldHex.hex64 Vesta.vesta_q.

Lemma k_is_11 : k = 11%nat.
Proof. reflexivity. Qed.

Lemma k_matches_domain : k = PolyDomain.k.
Proof. reflexivity. Qed.

Lemma circuit_degree_is_9 : circuit_degree = 9%nat.
Proof. reflexivity. Qed.

(** The Rust sizing loop starts at [11] and tests
    [2^e >= 2^11 * (9 - 1)].  Its first successful exponent is [14]. *)
Lemma extended_k_result_is_14 : extended_k_result = Some 14%nat.
Proof.
  unfold extended_k_result.
  rewrite circuit_degree_is_9.
  reflexivity.
Qed.

Lemma extended_k_is_14 : extended_k = 14%nat.
Proof.
  unfold extended_k.
  rewrite extended_k_result_is_14.
  reflexivity.
Qed.

Lemma extended_k_matches_pinned :
  Z.of_nat extended_k = VkPinnedData.extended_k.
Proof.
  rewrite extended_k_is_14.
  reflexivity.
Qed.

Lemma extended_domain_fits :
  (EvaluationDomainSetup.required_extended_size circuit_degree k <=
    EvaluationDomainSetup.domain_size extended_k)%nat.
Proof. vm_compute. lia. Qed.

Lemma preceding_domain_does_not_fit :
  (EvaluationDomainSetup.domain_size (Nat.pred extended_k) <
    EvaluationDomainSetup.required_extended_size circuit_degree k)%nat.
Proof. vm_compute. lia. Qed.

(** This is the exact pair of repeated-squaring loops in
    [EvaluationDomain::new], starting from [Fp::ROOT_OF_UNITY]. *)
Lemma omega_from_pasta_root_matches :
  omega_from_pasta_root = PolyDomain.omega.
Proof.
  vm_cast_no_check (@eq_refl Z PolyDomain.omega).
Qed.

(** The schedule can equivalently start from the defining Pasta generator
    expression because [IsoPallas.lambda_provenance] certifies that expression
    as [Fp::ROOT_OF_UNITY]. *)
Lemma omega_from_generator_schedule :
  EvaluationDomainSetup.root_for_domain
    Primes.pallas_p
    (modpow (p := Primes.pallas_p) 5
      ((Primes.pallas_p - 1) / 2 ^ 32))
    scalar_two_adicity extended_k k = PolyDomain.omega.
Proof.
  rewrite IsoPallas.lambda_provenance.
  exact omega_from_pasta_root_matches.
Qed.

Lemma base_modulus_matches_pinned :
  base_modulus = VkPinnedData.base_modulus.
Proof.
  vm_cast_no_check
    (@eq_refl PrimString.string VkPinnedData.base_modulus).
Qed.

Lemma scalar_modulus_matches_pinned :
  scalar_modulus = VkPinnedData.scalar_modulus.
Proof.
  vm_cast_no_check
    (@eq_refl PrimString.string VkPinnedData.scalar_modulus).
Qed.

Record certificate : Prop := {
  certificate_k : k = 11%nat;
  certificate_k_domain : k = PolyDomain.k;
  certificate_degree : circuit_degree = 9%nat;
  certificate_scalar_two_adicity :
    (Primes.pallas_p - 1) mod
      (2 ^ Z.of_nat scalar_two_adicity) = 0 /\
    ((Primes.pallas_p - 1) /
      (2 ^ Z.of_nat scalar_two_adicity)) mod 2 = 1;
  certificate_extended_k : extended_k_result = Some 14%nat;
  certificate_extended_k_pinned :
    Z.of_nat extended_k = VkPinnedData.extended_k;
  certificate_extended_domain_fits :
    (EvaluationDomainSetup.required_extended_size circuit_degree k <=
      EvaluationDomainSetup.domain_size extended_k)%nat;
  certificate_preceding_domain_does_not_fit :
    (EvaluationDomainSetup.domain_size (Nat.pred extended_k) <
      EvaluationDomainSetup.required_extended_size circuit_degree k)%nat;
  certificate_omega : omega_from_pasta_root = PolyDomain.omega;
  certificate_omega_generator :
    EvaluationDomainSetup.root_for_domain
      Primes.pallas_p
      (modpow (p := Primes.pallas_p) 5
        ((Primes.pallas_p - 1) / 2 ^ 32))
      scalar_two_adicity extended_k k = PolyDomain.omega;
  certificate_base_modulus : base_modulus = VkPinnedData.base_modulus;
  certificate_scalar_modulus : scalar_modulus = VkPinnedData.scalar_modulus;
}.

Theorem certified : certificate.
Proof.
  constructor.
  - exact k_is_11.
  - exact k_matches_domain.
  - exact circuit_degree_is_9.
  - exact OrchardVkParameters.scalar_two_adicity_exact.
  - exact extended_k_result_is_14.
  - exact extended_k_matches_pinned.
  - exact extended_domain_fits.
  - exact preceding_domain_does_not_fit.
  - exact omega_from_pasta_root_matches.
  - exact omega_from_generator_schedule.
  - exact base_modulus_matches_pinned.
  - exact scalar_modulus_matches_pinned.
Qed.

End OrchardVkSetup.
