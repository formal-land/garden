(** * Forward completeness: the whole-circuit assembly

    The composition of the per-family and per-selector forward obligations
    into the universally quantified completeness statement
    [OrchardHonestAssignment.orchard_completeness_statement], through
    [forward/api.v]'s join [completeness_statement_of_families].

    The gate lane is assembled by case analysis on the guarding selector of
    an enabled point.  Every selector of [Orchard/columns.v] belongs to
    exactly one forward lane:

    - [QOrchard], [QAdd], [QCondSwap1] / [QCondSwap2],
      [QMerkleDecompose1] / [QMerkleDecompose2] — [forward/residual.v];
    - [QLookup], [QRunning], [QBitshift] — [forward/running_sums.v];
    - [QWitnessPoint], [QWitnessPointNonId], [QAddIncomplete], [QEccAdd] —
      [forward/ecc_add.v];
    - the six [QMulIncomplete*] ladder selectors, [QMulDecomposeVar],
      [QMulOverflow], [QMulLsb] — [forward/var_base_ladder.v];
    - [QMulFixedRunningSum], [QMulFixedFull], [QMulFixedShort],
      [QMulFixedBaseField] — [forward/fixed_base.v];
    - the three [QPoseidon*] round selectors — [forward/poseidon.v];
    - the four [QSinsemilla*] round selectors — [forward/sinsemilla.v];
    - [QCommitIvk] and the 22 [QNoteCommit*] decomposition, canonicity and
      y-canonicity selectors — [forward/canonicity.v].

    Three of those lanes are keyed by region family rather than by selector
    ([forward/poseidon.v] at [33], [forward/var_base_ladder.v] at [37],
    [forward/canonicity.v] at [38; 39; 40]).  The side condition they need —
    an enabled point guarded by one of their selectors lies in one of their
    families — is one input-independent [vm_compute] scan of the reified
    enabled points ([point_family_cert]).

    Selector coverage is total, so the assembled gate obligation holds at
    [all_families] and every region family [0..42] is discharged, including
    the vacuous family [41] ([GadgetLocal], no enabled point) and the
    families whose points are spread across several lanes.

    The lookup lane and the witness-fact lane are taken from
    [forward/lookups_witness.v] ([lookups_forward_ok], [witness_facts_ok]),
    the read-back from [forward/read_back.v] ([read_back_forward]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.poseidon.
Require Import Garden.Orchard.circuit_completeness.forward.running_sums.
Require Import Garden.Orchard.circuit_completeness.forward.ecc_add.
Require Import Garden.Orchard.circuit_completeness.forward.fixed_base.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Garden.Orchard.circuit_completeness.forward.var_base_ladder.
Require Import Garden.Orchard.circuit_completeness.forward.canonicity.
Require Import Garden.Orchard.circuit_completeness.forward.residual.
Require Import Garden.Orchard.circuit_completeness.forward.read_back.
Require Import Garden.Orchard.circuit_completeness.forward.lookups_witness.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

Module OrchardCompletenessAssembly.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.

  Module PO := OrchardForwardPoseidon.
  Module RS := OrchardForwardRunningSums.
  Module EA := OrchardCompletenessForwardEccAdd.
  Module FB := OrchardForwardFixedBase.
  Module SI := OrchardForwardSinsemilla.
  Module VB := OrchardVarBaseForward.
  Module CA := OrchardCanonicityForward.
  Module RE := OrchardForwardResidual.
  Module RB := OrchardForwardReadBack.
  Module LW := OrchardForwardLookupsWitness.

  (** ** The family side condition of the family-keyed lanes

      [sel_families sel] is the family list of the lane owning [sel], for the
      three lanes stated as [family_gates_ok], and the empty list for the
      selector-keyed lanes, which need no such fact. *)

  Definition sel_families (sel : Selector.t) : list Z :=
    match sel with
    | Selector.QPoseidonFull
    | Selector.QPoseidonPartial
    | Selector.QPoseidonPadAndAdd => [33]
    | Selector.QMulIncompleteHi1
    | Selector.QMulIncompleteHi2
    | Selector.QMulIncompleteHi3
    | Selector.QMulIncompleteLo1
    | Selector.QMulIncompleteLo2
    | Selector.QMulIncompleteLo3
    | Selector.QMulDecomposeVar
    | Selector.QMulOverflow
    | Selector.QMulLsb => [37]
    | Selector.QCommitIvk
    | Selector.QNoteCommitOldB
    | Selector.QNoteCommitOldD
    | Selector.QNoteCommitOldE
    | Selector.QNoteCommitOldG
    | Selector.QNoteCommitOldH
    | Selector.QNoteCommitOldGd
    | Selector.QNoteCommitOldPkd
    | Selector.QNoteCommitOldValue
    | Selector.QNoteCommitOldRho
    | Selector.QNoteCommitOldPsi
    | Selector.QNoteCommitOldYCanon
    | Selector.QNoteCommitNewB
    | Selector.QNoteCommitNewD
    | Selector.QNoteCommitNewE
    | Selector.QNoteCommitNewG
    | Selector.QNoteCommitNewH
    | Selector.QNoteCommitNewGd
    | Selector.QNoteCommitNewPkd
    | Selector.QNoteCommitNewValue
    | Selector.QNoteCommitNewRho
    | Selector.QNoteCommitNewPsi
    | Selector.QNoteCommitNewYCanon => [38; 39; 40]
    | _ => []
    end.

  Definition point_family_ok (sel : Selector.t) (region : RegionId.t)
      : bool :=
    match sel_families sel with
    | [] => true
    | fams => List.existsb (Z.eqb (family_index region)) fams
    end.

  (** Every enabled point of a family-keyed lane's selectors lies in that
      lane's families.  The scan is input-independent: it mentions only the
      reified synthesis facts. *)
  Lemma point_family_cert :
    List.forallb (fun '(sel, region, _) => point_family_ok sel region)
      enabled = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma in_of_existsb (x : Z) (l : list Z) :
    List.existsb (Z.eqb x) l = true -> List.In x l.
  Proof.
    intros H.
    apply List.existsb_exists in H.
    destruct H as (y & Hy & Heq).
    apply Z.eqb_eq in Heq.
    rewrite Heq.
    exact Hy.
  Qed.

  Lemma fam_in (sel : Selector.t) (region : RegionId.t) (row : Z)
      (f : Z) (fs : list Z) :
    List.In (sel, region, row) enabled ->
    sel_families sel = f :: fs ->
    List.In (family_index region) (f :: fs).
  Proof.
    intros Hin Hsel.
    pose proof (proj1 (List.forallb_forall _ _) point_family_cert _ Hin)
      as Hok.
    cbn beta iota in Hok.
    unfold point_family_ok in Hok.
    rewrite Hsel in Hok.
    apply in_of_existsb.
    exact Hok.
  Qed.

  (** ** The per-lane dispatch

      One tactic per lane, applied to the hypotheses of the gate obligation
      after the selector is fixed.  The selector-keyed lanes take their
      membership side condition by [eq_refl] on the fixed selector; the
      family-keyed lanes take theirs from [fam_in]. *)

  Ltac lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (RE.residual_gates_forward w Hv Hn _ rg rw Hin eq_refl
      g Hg nm bd Hb).

  Ltac lane_ecc w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (EA.ecc_add_gates_forward w Hv Hn _ rg rw Hin eq_refl
      g Hg nm bd Hb).

  Ltac lane_sinsemilla w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (SI.sinsemilla_gates_forward w Hv Hn _ rg rw Hin eq_refl
      g Hg nm bd Hb).

  Ltac lane_poseidon w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (PO.poseidon_gates_ok w Hv Hn _ rg rw Hin
      (fam_in _ rg rw 33 [] Hin eq_refl) g Hg nm bd Hb).

  Ltac lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (VB.var_base_gates_ok w Hv Hn _ rg rw Hin
      (fam_in _ rg rw 37 [] Hin eq_refl) g Hg nm bd Hb).

  Ltac lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (CA.canonicity_gates_ok w Hv Hn _ rg rw Hin
      (fam_in _ rg rw 38 [39; 40] Hin eq_refl) g Hg nm bd Hb).

  (** The lanes whose obligation is keyed by a single selector are applied
      through their theorem, with no membership side condition. *)
  Ltac lane_plain thm w Hv Hn rg rw Hin g Hg nm bd Hb :=
    exact (thm w Hv Hn rg rw Hin g Hg nm bd Hb).

  (** ** The whole-circuit gate obligation

      Case analysis on the guarding selector: each of the 56 selectors is
      routed to the lane that proves its gate bodies.  The family hypothesis
      of [family_gates_ok] is not used — selector coverage is total, so the
      obligation holds at any family list, in particular [all_families]. *)
  Theorem gates_all : family_gates_ok all_families.
  Proof.
    intros w Hv Hn sel rg rw Hin _ g Hg nm bd Hb.
    destruct sel.
    (* [QOrchard]: the whole-circuit checks gate. *)
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QAdd]: the nullifier scalar sum. *)
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QLookup] / [QRunning]: the range-check guards, no gate. *)
    - lane_plain RS.qlookup_gates_ok w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_plain RS.qrunning_gates_ok w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QBitshift]: the short-lookup bitshift gate. *)
    - lane_plain RS.qbitshift_gates_ok w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QWitnessPoint] / [QWitnessPointNonId]: the witnessed points. *)
    - lane_ecc w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_ecc w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QAddIncomplete] / [QEccAdd]: the two point-addition gates. *)
    - lane_ecc w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_ecc w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The six [QMulIncomplete*] ladder halves. *)
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QMulDecomposeVar] / [QMulOverflow] / [QMulLsb]: the ladder's
       complete-bit decomposition, overflow check and LSB check. *)
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_var_base w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The four fixed-base window selectors. *)
    - lane_plain FB.q_mul_fixed_running_sum_gates_ok
        w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_plain FB.q_mul_fixed_full_gates_ok
        w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_plain FB.q_mul_fixed_short_gates_ok
        w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_plain FB.q_mul_fixed_base_field_gates_ok
        w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The three Poseidon round selectors. *)
    - lane_poseidon w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_poseidon w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_poseidon w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The four Sinsemilla round selectors. *)
    - lane_sinsemilla w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_sinsemilla w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_sinsemilla w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_sinsemilla w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The Merkle cond-swap and node-decomposition selectors. *)
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_residual w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* [QCommitIvk]: the [Commit^ivk] canonicity gate. *)
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The eleven [NoteCommit] old-note selectors. *)
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    (* The eleven [NoteCommit] new-note selectors. *)
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
    - lane_canonicity w Hv Hn rg rw Hin g Hg nm bd Hb.
  Qed.

  (** The lookup lane, over the same family partition. *)
  Theorem lookups_all : family_lookups_ok all_families.
  Proof.
    exact LW.lookups_forward_ok.
  Qed.

  (** ** The completeness statement

      The gate lane, the lookup lane and the read-back are unconditional; the
      witness-fact lane is the hypothesis, so each closure of its residue
      removes a hypothesis here.  [all_families_covers] supplies both
      coverage premises of the join; the three checker certificates and
      [honest_planes_ok] are discharged inside it. *)
  Theorem completeness_of_witness_facts
      (Hwitness : witness_facts_forward_ok) :
    OrchardHonestAssignment.orchard_completeness_statement.
  Proof.
    exact (completeness_statement_of_families
      all_families all_families
      all_families_covers all_families_covers
      gates_all lookups_all Hwitness RB.read_back_forward).
  Qed.

  (** The universally quantified completeness theorem.  Its witness-fact
      premise is [OrchardForwardLookupsWitness.witness_facts_ok], whose
      residue of 97 cross-derivation facts is the tracked leaf
      [OrchardForwardLookupsWitness.open_witness_facts]; the assumption audit
      of this theorem reports that leaf alongside the repository baseline. *)
  Theorem orchard_completeness :
    OrchardHonestAssignment.orchard_completeness_statement.
  Proof.
    exact (completeness_of_witness_facts LW.witness_facts_ok).
  Qed.

End OrchardCompletenessAssembly.
