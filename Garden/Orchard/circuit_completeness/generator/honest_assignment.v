(** * The Orchard completeness witness generator

    The whole-circuit honest assignment: given a §4.18.4 auxiliary input
    ([OrchardWitnessInput.HonestInput]), it assembles the complete
    [Assignment.t] over [circuit.synthesize] whose

    - selector, fixed and lookup planes are the honest planes of
      [Garden.Halo2.complete] read off [layouter_facts circuit.synthesize]
      (the selector plane is the enabled-point indicator, the fixed plane the
      first-write value, the lookup plane the loaded table contents);
    - advice plane dispatches on the [RegionId] constructor to the four
      per-family sub-generators ([advice_witness_io], [advice_merkle_sinsemilla],
      [advice_poseidon_nullifier], [advice_ecc_muls]), each of which is total
      over [RegionId.t] and [0] outside its family;
    - instance plane is the primary-input encoding — the ten-element public
      sequence (anchor, [cv_net], [nf_old], [rk], [cmx], enable flags, and
      [disableCrossAddress]) of post-NU6.3 §4.18.4 — repeated on the single
      [Instance_.Primary] column.

    [honest_planes_ok] establishes the selector/fixed/lookup planes are the
    honest planes by construction (definitionally), so
    [Complete.circuit_holds_intro] applies to [honest_assignment w] with the
    [OrchardDecidableEq] equalities and the certificates of
    [OrchardCompletenessCertificates].  The whole-circuit target proposition
    [completeness_statement] is stated in [OrchardWitnessInput]; the
    instantiation at this generator is named [orchard_completeness_statement]
    below (the C2 proof campaign is follow-up work). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_witness_io.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardHonestAssignment.
  Import OrchardWitnessInput.

  (** The Boolean equalities that instantiate [Garden.Halo2.complete]'s
      completeness section for Orchard — the same functions the
      certificates use. *)
  Definition selector_eqb := OrchardDecidableEq.selector_eqb.
  Definition fixed_eqb := OrchardDecidableEq.fixed_eqb.
  Definition lookup_eqb := OrchardDecidableEq.lookup_eqb.
  Definition region_eqb := OrchardDecidableEq.region_id_eqb.

  (** The reified facts of the whole Orchard synthesis program. *)
  Definition facts : list (Fact.t columns RegionId.t) :=
    layouter_facts Garden.Orchard.circuit.synthesize.

  (** ** The advice plane

      The per-family readers of [OrchardCompletenessTables.advice_t] over the
      hoisted table record [OrchardCompletenessTables.tables_of w]: every
      region-level derivation (Sinsemilla accumulators, fixed-base ladders,
      Poseidon schedule, scalar multiples) is computed once per assignment,
      and each cell read is a lookup.  The readers mirror the per-family
      sub-generators ([advice_witness_io], [advice_merkle_sinsemilla],
      [advice_poseidon_nullifier], [advice_ecc_muls]) cell for cell. *)
  Definition advice_plane (w : HonestInput)
      : Advice.t -> RegionId.t -> Z -> Z :=
    let tb := OrchardCompletenessTables.tables_of w in
    OrchardCompletenessTables.advice_t w tb.

  (** ** The whole assignment

      The selector, fixed and lookup planes are the honest planes read off
      [facts]; the advice and instance planes read the hoisted table record,
      bound once outside the per-cell lambdas so a [vm_compute] run forces
      the region-level derivations exactly once. *)
  Definition honest_assignment (w : HonestInput)
      : Assignment.t columns RegionId.t :=
    let tb := OrchardCompletenessTables.tables_of w in
    {|
      Assignment.selector := fun selector region offset =>
        if Complete.enabled_memb selector_eqb region_eqb facts
             selector region offset
        then 1 else 0;
      Assignment.fixed := fun column region offset =>
        Complete.fixed_write_or_zero fixed_eqb region_eqb facts
          column region offset;
      Assignment.advice := OrchardCompletenessTables.advice_t w tb;
      Assignment.instance_ := fun _ row =>
        OrchardCompletenessTables.instance_t w tb row;
      Assignment.lookup := fun column row =>
        Complete.table_value lookup_eqb facts column row;
    |}.

  (** ** The planes are honest by construction

      Each of the three plane predicates unfolds to the equality between the
      corresponding [honest_assignment] field and its honest-plane builder;
      since the field is defined as that builder over [facts =
      layouter_facts circuit.synthesize], each holds by [reflexivity].  The
      advice and instance planes stay abstract in [honest_planes], so they do
      not enter this proof. *)
  Theorem honest_planes_ok (w : HonestInput) :
    Complete.honest_planes selector_eqb fixed_eqb lookup_eqb region_eqb
      (honest_assignment w) Garden.Orchard.circuit.synthesize.
  Proof.
    unfold Complete.honest_planes.
    split; [| split].
    - intros selector region offset. reflexivity.
    - intros column region offset. reflexivity.
    - intros column row _. reflexivity.
  Qed.

  (** ** The whole-circuit completeness target

      The instantiation of [OrchardWitnessInput.completeness_statement] at
      this generator: for every valid, nondegenerate honest input the
      generated assignment satisfies [circuit_holds] and reads back as the
      input record.  Stated only; the proof is the C2 campaign.  *)
  Definition orchard_completeness_statement : Prop :=
    OrchardWitnessInput.completeness_statement honest_assignment.

End OrchardHonestAssignment.
