(** * The forward statement API of the universal completeness theorem

    The statement layer for proving
    [OrchardHonestAssignment.orchard_completeness_statement]: the
    [circuit_holds_intro] obligations over [honest_assignment w], split by
    the region-family partition [family_index] of [instance/defs.v] and
    quantified over every valid, nondegenerate input.

    - [family_gates_ok] / [family_lookups_ok]: the per-enabled-point gate and
      lookup obligations restricted to a list of family indices — exactly the
      [Hgates] / [Hlookups] premises of [Complete.circuit_holds_intro] on the
      points whose region family lies in the list ([1024] is the loaded table
      size, [layouter_table_rows_eq]);
    - [witness_facts_forward_ok]: the copy/constant/instance facts of the
      synthesis program ([Hwitness]);
    - [read_back_ok]: the free-witness read-back conjunct of
      [completeness_statement];
    - [covers] / [all_families]: coverage of the family partition — every
      [RegionId.t] has its family index in the list;
    - [completeness_statement_of_families]: the assembly — family-covering
      gate and lookup obligations, the witness facts and the read-back
      compose through [Complete.circuit_holds_intro] (with the three
      [OrchardCompletenessCertificates] checkers and [honest_planes_ok]) into
      the universally quantified completeness statement.

    The per-family obligations are proved in sibling files, one per gate
    family, and joined with [family_gates_ok_app] / [family_lookups_ok_app];
    this file carries no per-family proof. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompletenessForward.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.
  Import OrchardCompletenessInstanceDefs.

  (** ** The per-family symbolic obligations

      [enabled], [system] and [family_index] are the shared definitions of
      [instance/defs.v]: the enabled selector points of
      [layouter_facts circuit.synthesize], the configured constraint system,
      and the region-family shard key. *)

  (** The gate obligation of [Complete.circuit_holds_intro], restricted to
      the enabled points whose region family lies in [fams]: at each such
      point, every constraint guarded by the point's own selector evaluates
      under the honest assignment. *)
  Definition family_gates_ok (fams : list Z) : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        List.In (family_index region) fams ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.

  (** The lookup obligation of [Complete.circuit_holds_intro], restricted the
      same way: at each enabled point of a family in [fams], every lookup
      argument mentioning the point's selector resolves to a row of the
      1024-row loaded table ([layouter_table_rows_eq]). *)
  Definition family_lookups_ok (fams : list Z) : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        List.In (family_index region) fams ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
            sel arg = true ->
          eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
            (region, row) 1024 arg.

  (** The witness-fact obligation of [Complete.circuit_holds_intro]: the
      [CellsEqual] / [InstanceIs] / [CellIsConstant] facts of the synthesis
      program hold of the honest assignment. *)
  Definition witness_facts_forward_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      interpret_facts (OrchardHonestAssignment.honest_assignment w)
        (Complete.witness_facts facts).

  (** The second conjunct of [completeness_statement]: the free-witness
      readers reproduce the input record. *)
  Definition read_back_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      read_action_inputs (OrchardHonestAssignment.honest_assignment w) =
      inputs_of w.

  (** ** Coverage of the family partition *)

  (** A family list covers the circuit when every region's family index is a
      member. *)
  Definition covers (fams : list Z) : Prop :=
    forall region : RegionId.t, List.In (family_index region) fams.

  (** All 43 family indices of the partition: [0] the witness-input loads,
      [1..32] the Merkle layers, [33..41] the per-gadget families, [42] the
      Orchard checks and the note-commitment equality/witness regions. *)
  Definition all_families : list Z := List.map Z.of_nat (List.seq 0 43).

  Lemma family_index_range (region : RegionId.t) :
    0 <= family_index region <= 42.
  Proof.
    destruct region as
      [wi | layer mr | pr | vr | nr | sr | ar | cr | wh ncr
      | | | | | | gr];
      try (cbn; lia).
    - destruct layer; cbn; lia.
    - destruct wh; cbn; lia.
  Qed.

  Lemma all_families_complete (i : Z) :
    0 <= i <= 42 -> List.In i all_families.
  Proof.
    intros Hi.
    unfold all_families.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    apply List.in_map.
    apply List.in_seq.
    lia.
  Qed.

  Lemma all_families_covers : covers all_families.
  Proof.
    intros region.
    apply all_families_complete.
    apply family_index_range.
  Qed.

  (** ** Combinators: the per-family lemmas plug into the join

      Anti-monotonicity in the family list and the union of two certified
      groups, for both obligation kinds. *)

  Lemma family_gates_ok_app (fams1 fams2 : list Z) :
    family_gates_ok fams1 ->
    family_gates_ok fams2 ->
    family_gates_ok (fams1 ++ fams2).
  Proof.
    intros H1 H2 w Hvalid Hnondeg sel region row Hin Hfam.
    apply List.in_app_or in Hfam.
    destruct Hfam as [Hfam | Hfam].
    - exact (H1 w Hvalid Hnondeg sel region row Hin Hfam).
    - exact (H2 w Hvalid Hnondeg sel region row Hin Hfam).
  Qed.

  Lemma family_lookups_ok_app (fams1 fams2 : list Z) :
    family_lookups_ok fams1 ->
    family_lookups_ok fams2 ->
    family_lookups_ok (fams1 ++ fams2).
  Proof.
    intros H1 H2 w Hvalid Hnondeg sel region row Hin Hfam.
    apply List.in_app_or in Hfam.
    destruct Hfam as [Hfam | Hfam].
    - exact (H1 w Hvalid Hnondeg sel region row Hin Hfam).
    - exact (H2 w Hvalid Hnondeg sel region row Hin Hfam).
  Qed.

  (** ** The coverage joins

      A covering family list turns the per-family obligations into the exact
      [Hgates] / [Hlookups] premises of [Complete.circuit_holds_intro] at
      [honest_assignment w], for every input in the completeness domain. *)

  Lemma gates_join (fams : list Z) :
    covers fams ->
    family_gates_ok fams ->
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.
  Proof.
    intros Hcover Hok w Hvalid Hnondeg sel region row Hin.
    exact (Hok w Hvalid Hnondeg sel region row Hin (Hcover region)).
  Qed.

  Lemma lookups_join (fams : list Z) :
    covers fams ->
    family_lookups_ok fams ->
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
            sel arg = true ->
          eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
            (region, row) 1024 arg.
  Proof.
    intros Hcover Hok w Hvalid Hnondeg sel region row Hin.
    exact (Hok w Hvalid Hnondeg sel region row Hin (Hcover region)).
  Qed.

  (** ** The assembly skeleton

      Family-covering gate and lookup obligations, the witness facts and the
      read-back compose into the universally quantified completeness
      statement, through [Complete.circuit_holds_intro] with the three
      program-level certificates and the honest planes.  The concluding C2
      theorem instantiates [gate_fams] / [lookup_fams] with [all_families]
      (via [all_families_covers]) and discharges the four premises with the
      per-family forward lemmas. *)
  Theorem completeness_statement_of_families
      (gate_fams lookup_fams : list Z)
      (Hgate_cover : covers gate_fams)
      (Hlookup_cover : covers lookup_fams)
      (Hgates : family_gates_ok gate_fams)
      (Hlookups : family_lookups_ok lookup_fams)
      (Hwitness : witness_facts_forward_ok)
      (Hread : read_back_ok) :
    OrchardHonestAssignment.orchard_completeness_statement.
  Proof.
    unfold OrchardHonestAssignment.orchard_completeness_statement,
      completeness_statement.
    intros w Hvalid Hnondeg.
    split; [| exact (Hread w Hvalid Hnondeg)].
    apply (Complete.circuit_holds_intro
      OrchardDecidableEq.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardDecidableEq.fixed_eqb OrchardDecidableEq.lookup_eqb
      OrchardDecidableEq.region_id_eqb OrchardDecidableEq.region_id_eqb_eq).
    - exact OrchardCompletenessCertificates.selector_guarded_certificate.
    - exact OrchardCompletenessCertificates.no_conflicting_writes_certificate.
    - exact OrchardCompletenessCertificates.lookup_defaults_certificate.
    - exact (OrchardHonestAssignment.honest_planes_ok w).
    - exact (Hwitness w Hvalid Hnondeg).
    - intros sel region row Hin gate Hgate name body Hbody.
      exact (gates_join gate_fams Hgate_cover Hgates w Hvalid Hnondeg
        sel region row Hin gate Hgate name body Hbody).
    - intros sel region row Hin arg Harg Hmention.
      rewrite OrchardCompletenessCertificates.layouter_table_rows_eq.
      exact (lookups_join lookup_fams Hlookup_cover Hlookups w Hvalid Hnondeg
        sel region row Hin arg Harg Hmention).
  Qed.

End OrchardCompletenessForward.
