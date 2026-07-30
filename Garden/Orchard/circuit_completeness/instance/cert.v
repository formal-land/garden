(** * The concrete Orchard completeness instance

    The first whole-circuit completeness theorem: one concrete honest input,
    built in-model from small secrets, is accepted by the Orchard action
    circuit — [circuit_holds] holds of the generated assignment, and the
    free-witness readers reproduce the input record
    ([orchard_completeness_instance]).  This is the constructive C1 instance
    of the completeness track: a non-vacuity certificate for the [Holds]
    surface (including the satisfiability of the witness-honesty side
    conditions), and an end-to-end machine check of the honest-witness
    generator.

    Structure (see [instance/defs.v] for the shared definitions):

    - [test_input]: the concrete §4.18.4 auxiliary input, certified valid and
      nondegenerate in [instance/domain.v];
    - the gate/lookup obligations of [Complete.circuit_holds_intro] over the
      enabled selector points, the copy/constant witness facts, and the
      reader side of the read-back — all in [instance/certs.v], which shares
      one evaluation of [Γtest] across them;
    - the specification side of the read-back ([instance/read.v]), which
      touches neither [Γtest] nor the table record and so compiles in
      parallel.

    The theorem inherits the model caveats of [docs/chip-model-caveats.md];
    its content is relative to the relational [circuit_holds] semantics. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.instance.domain.
Require Import Garden.Orchard.circuit_completeness.instance.certs.
Require Import Garden.Orchard.circuit_completeness.instance.read.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompletenessInstance.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.
  Import OrchardCompletenessInstanceDefs.

  (** Re-exported domain certificates: the typing/ownership envelope and the
      nondegeneracy assembly from the clause-wise certificates. *)
  Definition test_input := test_input.
  Definition test_input_valid :=
    OrchardCompletenessInstanceDomain.test_input_valid.

  Lemma test_input_nondegenerate : nondegenerate test_input.
  Proof.
    exact (nondegenerate_of_certs test_input
      OrchardCompletenessInstanceDomain.merkle_nondeg_cert
      OrchardCompletenessInstanceDomain.nc_old_nondeg_cert
      OrchardCompletenessInstanceDomain.nc_new_nondeg_cert
      OrchardCompletenessInstanceDomain.civk_nondeg_cert
      OrchardCompletenessInstanceDomain.mul_chain_cert).
  Qed.

  (** ** The join: every enabled point passes the checker *)

  Lemma check_point_enabled (sel : Selector.t) (region : RegionId.t)
      (row : Z) :
    List.In (sel, region, row) enabled ->
    check_point (sel, region, row) = true.
  Proof.
    intros Hin.
    destruct region as
      [wi | layer mr | pr | vr | nr | sr | ar | cr | wh ncr
      | | | | | | | gr].
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - destruct layer;
        exact (check_point_shard_in _ _ _ _
          OrchardCompletenessInstanceShardsMerkle.merkle_shards_ok
          Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.fixed_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.fixed_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.fixed_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsBlocked.shard_37_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsBlocked.shard_38_ok Hin eq_refl).
    - destruct wh.
      + exact (check_point_shard_in _ _ _ _
          OrchardCompletenessInstanceShardsBlocked.shard_39_ok Hin eq_refl).
      + exact (check_point_shard_in _ _ _ _
          OrchardCompletenessInstanceShardsBlocked.shard_40_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
    - exact (check_point_shard_in _ _ _ _
        OrchardCompletenessInstanceShardsMisc.misc_shards_ok Hin eq_refl).
  Qed.

  (** The read-back equation, composed from the two sides that were
      certified independently against the pinned [test_action_inputs].  No
      computation happens here: both sides are already reduced to the same
      literal, so this is a transitivity step on proved equalities. *)
  Lemma read_action_inputs_ok :
    read_action_inputs Γtest = inputs_of test_input.
  Proof.
    exact (eq_trans
      OrchardCompletenessInstanceReadCells.read_action_inputs_lit
      (eq_sym OrchardCompletenessInstanceRead.inputs_of_lit)).
  Qed.

  (** ** The instance theorem

      [Holds (honest_assignment test_input)] together with the free-witness
      read-back: the §4.1.13 in-model completeness residue at one concrete
      valid, nondegenerate input. *)

  Theorem orchard_completeness_instance :
    circuit_holds Γtest Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
    read_action_inputs Γtest = inputs_of test_input.
  Proof.
    split;
      [| exact read_action_inputs_ok].
    apply (Complete.circuit_holds_intro
      OrchardDecidableEq.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardDecidableEq.fixed_eqb OrchardDecidableEq.lookup_eqb
      OrchardDecidableEq.region_id_eqb OrchardDecidableEq.region_id_eqb_eq).
    - exact OrchardCompletenessCertificates.selector_guarded_certificate.
    - exact OrchardCompletenessCertificates.no_conflicting_writes_certificate.
    - exact OrchardCompletenessCertificates.lookup_defaults_certificate.
    - exact (OrchardHonestAssignment.honest_planes_ok test_input).
    - exact (Complete.check_witness_facts_sound Γtest _
        OrchardCompletenessInstanceWitness.witness_facts_ok).
    - (* Gates: one obligation per enabled point of each constraint's own
         selector. *)
      intros sel region row Hin gate Hgate name body Hbody.
      pose proof (check_point_enabled sel region row Hin) as Hpt.
      unfold check_point in Hpt.
      apply Bool.andb_true_iff in Hpt.
      destruct Hpt as [Hgates _].
      rewrite List.forallb_forall in Hgates.
      specialize (Hgates gate Hgate).
      rewrite List.forallb_forall in Hgates.
      specialize (Hgates _ Hbody).
      cbn beta iota in Hgates.
      rewrite OrchardDecidableEq.selector_eqb_refl in Hgates.
      exact (Complete.check_constraint_sound Γtest (region, row) body Hgates).
    - (* Lookups: one obligation per (enabled point, mentioning argument)
         pair. *)
      intros sel region row Hin arg Harg Hmention.
      pose proof (check_point_enabled sel region row Hin) as Hpt.
      unfold check_point in Hpt.
      apply Bool.andb_true_iff in Hpt.
      destruct Hpt as [_ Hlookups].
      rewrite List.forallb_forall in Hlookups.
      specialize (Hlookups arg Harg).
      cbn beta in Hlookups.
      rewrite Hmention in Hlookups.
      rewrite OrchardCompletenessCertificates.layouter_table_rows_eq.
      exact (Complete.check_lookup_argument_sound Γtest (region, row)
        1024 _ arg Hlookups).
  Qed.

End OrchardCompletenessInstance.
