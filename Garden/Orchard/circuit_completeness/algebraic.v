(** * Honest witnesses are accepted by the algebraic (L1) reading.

    The composition that carries the operational completeness headline
    ([OrchardOperationalAgreement.orchard_operational_complete]: an honest,
    valid, nondegenerate witness is accepted by the ideal checker mirroring
    Rust Halo2's [MockProver]) down the refinement ladder to
    [OrchardCompiledAlgebraic.orchard_algebraic_accepts_regular] — the
    polynomial-identity reading of the compiled pinned system over the
    cyclic domain.

    Every rung below [mock_prover_accepts] is an equivalence or has a
    proved completeness direction, so nothing here is new theory:

    - [OrchardCompiled.orchard_compiled_complete] takes acceptance by the
      ideal checker to the compiled satisfaction triple, through
      [PlonkishMock.plonkish_of_mock_prover] (the domain-row restriction),
      [PlonkishCompile.compile_correct_domain] (selector compression) and
      [sigma_correct] (the copy obligations closing into σ invariance);
    - [OrchardCompiledAlgebraic.orchard_algebraic_complete] takes that
      triple to the three identity families, through
      [Vanishing.vanishing_sound_horner] (the vanishing quotient),
      [PermutationPoly.permutation_complete_grid_invariant] (the running
      products, exhibited division-free) and
      [PlonkishLookupPoly.lookup_arguments_complete] (the permuted columns
      and the product column).

    This is the mirror of
    [OrchardCompiledAlgebraic.orchard_algebraic_action_statement], which
    runs the same ladder in the soundness direction, and it upgrades the
    completeness surface from the ideal row-by-row checker to the
    identity-level reading a deployed verifier checks.

    Two readings are delivered: the [Es]-generic one, where the prover's
    gate polynomials are any that agree with the honest grid on [H] (as the
    real committed ones do), and the unconditional one, where the witness
    is supplied by [PlonkishAlgebraic.zero_gate_polys] — the L1 non-vacuity
    certificate, since it exhibits an inhabitant of
    [orchard_algebraic_accepts_regular] outright.

    The acceptance predicate is the *regular-challenge* one: the
    permutation conjunct is asked only at the [(β, γ)] where no
    identity-side factor vanishes on a usable cell.  At the excluded
    challenges the running-product recurrence divides by zero, so no honest
    prover has a product column there either; the lookup conjunct carries
    the same restriction internally
    ([PlonkishLookupPoly.lookup_challenge_regular]).  Soundness reads the
    same predicate ([PlonkishAlgebraic.algebraic_sound_regular]), so the
    two directions meet exactly. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Halo2.plonkish.algebraic.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.main.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.operational.main.

Import ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardAlgebraicCompleteness.
  Import OrchardWitnessInput.
  Import OrchardOperationalAgreement.

  (** ** The compiled rung *)

  (** The honest grid satisfies the compiled plonkish system: the compiled
      gates vanish on every domain row of the installed grid, every lookup
      argument of the indexed system holds, and the grid is invariant under
      the σ closed from the Orchard copy obligations. *)
  Theorem orchard_honest_compiled_accepts (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    OrchardCompiled.orchard_compiled_accepts g.
  Proof.
    exact (OrchardCompiled.orchard_compiled_complete (orchard_advice w)
      (orchard_instance w) g Hreplay
      (orchard_operational_complete w g Hvalid Hnondeg Hreplay)).
  Qed.

  (** ** The algebraic rung — the E2 headline *)

  (** An honest, valid, nondegenerate witness satisfies the three identity
      families of the compiled pinned system, for any gate polynomials
      agreeing with its grid on the evaluation domain [H]. *)
  Theorem orchard_honest_algebraic_accepts (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g)
      (Es : list Poly.t)
      (Hagree :
        PlonkishAlgebraic.gates_agree (p := Primes.pallas_p) PolyDomain.omega
          PolyDomain.k OrchardCompiledCheck.compiled g Es) :
    OrchardCompiledAlgebraic.orchard_algebraic_accepts_regular g Es.
  Proof.
    exact (OrchardCompiledAlgebraic.orchard_algebraic_complete
      (orchard_advice w) (orchard_instance w) g Es Hreplay Hagree
      (orchard_honest_compiled_accepts w g Hvalid Hnondeg Hreplay)).
  Qed.

  (** The unconditional form: the replay always succeeds and the
      gate-polynomial witness is always available, so an honest witness is
      accepted at L1 outright.  This is the non-vacuity certificate for
      [algebraic_accepts_regular] — the soundness surface at this layer is
      not vacuously true. *)
  Theorem orchard_honest_algebraic_accepts_ex (w : HonestInput)
      (Hvalid : valid w) (Hnondeg : nondegenerate w) :
    exists (g : RawGrid.t) (Es : list Poly.t),
      apply_events orchard_events
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some g /\
      mock_prover_accepts orchard_indexed_system orchard_events g
        orchard_table_rows /\
      OrchardCompiledAlgebraic.orchard_algebraic_accepts_regular g Es.
  Proof.
    destruct (orchard_replay_planes w) as (g & Hreplay).
    destruct
      (OrchardCompiledAlgebraic.orchard_algebraic_complete_ex
        (orchard_advice w) (orchard_instance w) g Hreplay
        (orchard_honest_compiled_accepts w g Hvalid Hnondeg Hreplay))
      as (Es & Haccepts).
    exists g, Es.
    split; [exact Hreplay |].
    split; [| exact Haccepts].
    exact (orchard_operational_complete w g Hvalid Hnondeg Hreplay).
  Qed.

End OrchardAlgebraicCompleteness.
