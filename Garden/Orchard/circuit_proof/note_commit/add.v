(** * NoteCommit cm_new complete-add bridge and rcm-leg alignment

    Two results about the new-note commitment inside
    [note_commit.synthesize_new]:

    - [synthesize_new_cm_point_add_correct]: the output point of
      [note_commit.synthesize_new] (the "M + [r] R" complete-add region) is
      [EccSpec.point_add] of the Sinsemilla hash point [new_cm_hash_m] and
      the fixed-base blinding point, from [Holds] alone.  The complete-add
      facts are peeled from [Holds] down to the [CompletePointAdd] region
      (same navigation as [NoteCommitROut.note_commit_r_fixed_base_facts],
      continued two binds past the blinding ladder), then transported to
      [circuit.v]'s generic [synthesize_complete_point_add] — the local
      [note_commit.assign_complete_add] is a verbatim copy whose fact list
      and output cells never mention the local record type — and closed by
      the generic [complete_point_add_correct].

    - the rcm-leg alignment: [OrchardSpec.out_cmx (action_spec_of Γ)]
      receives its scalar and square-root witnesses as
      [read_scalar_from_windows] / [read_us] at
      [RegionId.NoteCommit Which.New FixedBaseIncomplete]
      ([in_rcm_new_read] / [w_us_rcm_read], both [reflexivity]), which are
      exactly the fields of the K-out lemma
      [NoteCommitROut.full_note_commit_r_scalar_mul_correct];
      [note_commit_r_mul_leg_spec] restates that lemma at the spec fields,
      and [synthesize_new_cm_point_add_rcm_correct] combines both results:
      the cm_new point is [point_add] of the hash point and
      [EccSpec.fixed_scalar_mul (note_commit_r prm) (in_rcm_new inp)
      (w_us_rcm wit)] — the exact blinding leg of [OrchardSpec.note_commit]
      in [out_cmx].

    The hash leg is left as the evaluated [HashResult] cells
    [new_cm_hash_m] of [synthesize_hash_to_point_note_commit_2] at the
    [HashToPoint] region; equating it with
    [SinsemillaSpec.sinsemilla_hash_to_point] is the remaining Sinsemilla
    step of the CMX bridge. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.note_commit_r.out.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module NoteCommitNewAdd.
  Import OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** The hash point of the new-note commitment

      The message-piece cells and the [HashResult] of the Sinsemilla
      hash-to-point subprogram of [note_commit.synthesize_new], as
      layouter values of the same subprograms the synthesizer runs (the
      hash program's value does not depend on the piece arguments; passing
      the genuine ones keeps the definition aligned with the source). *)

  Definition new_note_piece
      (region : RegionId.NoteCommit.t) (name : string)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    layouter_value
      (Garden.Orchard.circuit.note_commit.witness_message_piece
        (Garden.Orchard.circuit.note_commit.note_commit_region
          RegionId.NoteCommit.Which.New region)
        Advice.A7
        name).

  Definition new_cm_hash_result
      : Garden.Halo2.halo2_gadgets.sinsemilla.chip.HashResult.t :=
    layouter_value
      (Garden.Halo2.halo2_gadgets.sinsemilla.chip
        .synthesize_hash_to_point_note_commit_2
        (Garden.Orchard.circuit.note_commit.note_commit_region
          RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint)
        Garden.Orchard.circuit.note_commit.q_note_commit_m_x
        Garden.Orchard.circuit.note_commit.q_note_commit_m_y
        (new_note_piece RegionId.NoteCommit.WitnessA "a")
        (new_note_piece RegionId.NoteCommit.WitnessB "b")
        (new_note_piece RegionId.NoteCommit.WitnessC "c")
        (new_note_piece RegionId.NoteCommit.WitnessD "d")
        (new_note_piece RegionId.NoteCommit.WitnessE "e")
        (new_note_piece RegionId.NoteCommit.WitnessF "f")
        (new_note_piece RegionId.NoteCommit.WitnessG "g")
        (new_note_piece RegionId.NoteCommit.WitnessH "h")).

  (** The [m] operand of the "M + [r] R" complete addition: the hash
      point's x/y cells, as [note_commit.v]'s own point record. *)
  Definition new_cm_hash_m : Garden.Orchard.circuit.note_commit.AssignedPoint.t := {|
    Garden.Orchard.circuit.note_commit.AssignedPoint.x :=
      new_cm_hash_result
        .(Garden.Halo2.halo2_gadgets.sinsemilla.chip.HashResult.x);
    Garden.Orchard.circuit.note_commit.AssignedPoint.y :=
      new_cm_hash_result
        .(Garden.Halo2.halo2_gadgets.sinsemilla.chip.HashResult.y);
  |}.

  (** The blinding operand: the output point of the NoteCommitR fixed-base
      ladder at [Which.New] (the subject of the K-out lemma). *)
  Definition new_cm_blind : Garden.Orchard.circuit.note_commit.AssignedPoint.t :=
    layouter_value
      (Garden.Orchard.circuit.note_commit
        .synthesize_full_fixed_base_mul_note_commit_r
        RegionId.NoteCommit.Which.New).

  (** Record conversion into [circuit.v]'s point record (the two records
      are field-for-field identical). *)
  Definition to_circuit_point
      (point : Garden.Orchard.circuit.note_commit.AssignedPoint.t)
      : Garden.Orchard.circuit.AssignedPoint.t := {|
    Garden.Orchard.circuit.AssignedPoint.x :=
      point.(Garden.Orchard.circuit.note_commit.AssignedPoint.x);
    Garden.Orchard.circuit.AssignedPoint.y :=
      point.(Garden.Orchard.circuit.note_commit.AssignedPoint.y);
  |}.

  (** ** Facts of the "M + [r] R" complete-add region, from [Holds]

      Same peel as [NoteCommitROut.note_commit_r_fixed_base_facts] down to
      the "Process NoteCommit inputs" namespace, then two binds further
      (past the blinding ladder and the hash-to-point program) to the
      [cm] bind, transported to the generic [synthesize_complete_point_add]
      by conversion ([note_commit.assign_complete_add] is a verbatim copy of
      [circuit.assign_complete_add]). *)

  Lemma new_cm_complete_add_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_complete_point_add
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.CompletePointAdd)
          "M + [r] R"
          (to_circuit_point new_cm_hash_m)
          (to_circuit_point new_cm_blind))).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_new in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    cbv beta zeta in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** ** The complete-add bridge: cm_new = M + [r] R as spec points

      The output point of [note_commit.synthesize_new] equals the complete
      addition of the hash point and the blinding point.  The seven message
      cells are arbitrary: neither the output cells nor the two operand
      records depend on them. *)

  Lemma synthesize_new_cm_point_add_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.note_commit.synthesize_new
            g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell))) =
    EccSpec.point_add
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ new_cm_hash_m))
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ
          (layouter_value
            (Garden.Orchard.circuit.note_commit
              .synthesize_full_fixed_base_mul_note_commit_r
              RegionId.NoteCommit.Which.New)))).
  Proof.
    pose proof
      (complete_point_add_correct Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.CompletePointAdd)
        "M + [r] R"
        (to_circuit_point new_cm_hash_m)
        (to_circuit_point new_cm_blind)
        (new_cm_complete_add_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)) as Hadd.
    exact Hadd.
  Qed.

  (** ** The rcm-leg alignment (finding: restating suffices)

      [OrchardSpec.out_cmx (action_spec_of Γ)] receives the blinding scalar
      and square-root witnesses as [read_scalar_from_windows] / [read_us]
      at [RegionId.NoteCommit Which.New FixedBaseIncomplete] — exactly the
      fields of the K-out lemma.  Both projections are definitional. *)

  Lemma in_rcm_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_rcm_new (read_action_inputs Γ) =
    read_scalar_from_windows Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete) 85.
  Proof. reflexivity. Qed.

  Lemma w_us_rcm_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.w_us_rcm (read_action_witness Γ) =
    read_us Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete) 85.
  Proof. reflexivity. Qed.

  (** The K-out lemma restated at the spec's own fields: the blinding leg
      of [out_cmx] as the circuit's ladder output point. *)
  Lemma note_commit_r_mul_leg_spec
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.note_commit
            .synthesize_full_fixed_base_mul_note_commit_r
            RegionId.NoteCommit.Which.New))) =
    EccSpec.fixed_scalar_mul
      (OrchardSpec.note_commit_r orchard_circuit_params)
      (OrchardSpec.in_rcm_new (read_action_inputs Γ))
      (OrchardSpec.w_us_rcm (read_action_witness Γ)).
  Proof.
    rewrite
      (NoteCommitROut
        .full_note_commit_r_scalar_mul_correct
        Γ Hcircuit).
    reflexivity.
  Qed.

  (** ** Combined form: cm_new = M + [rcm_new] NoteCommitR

      The complete-add bridge with the blinding leg replaced by the spec's
      [fixed_scalar_mul] at [in_rcm_new]/[w_us_rcm] — the exact second
      operand of [OrchardSpec.note_commit] inside [out_cmx
      (action_spec_of Γ)].  The remaining CMX gap is the hash leg. *)

  Lemma synthesize_new_cm_point_add_rcm_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.note_commit.synthesize_new
            g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell))) =
    EccSpec.point_add
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ new_cm_hash_m))
      (EccSpec.fixed_scalar_mul
        (OrchardSpec.note_commit_r orchard_circuit_params)
        (OrchardSpec.in_rcm_new (read_action_inputs Γ))
        (OrchardSpec.w_us_rcm (read_action_witness Γ))).
  Proof.
    rewrite
      (synthesize_new_cm_point_add_correct Γ Hcircuit
        g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell).
    rewrite (note_commit_r_mul_leg_spec Γ Hcircuit).
    reflexivity.
  Qed.

End NoteCommitNewAdd.
