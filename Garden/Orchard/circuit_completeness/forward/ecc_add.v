(** * Forward lemmas: the complete-addition, incomplete-addition and
    witness-point gates

    The ecc-add slice of the universal completeness campaign: at every
    enabled point of [circuit.synthesize] whose selector is [QEccAdd],
    [QAddIncomplete], [QWitnessPoint] or [QWitnessPointNonId], the gate
    constraints guarded by that selector hold of [honest_assignment w], for
    every valid, nondegenerate input [w].

    Structure:

    - the selector group and its obligation Props ([ecc_selector_gates_ok] /
      [ecc_selector_lookups_ok]), shaped exactly like the per-point
      obligations of [forward/api.v] with the family restriction replaced by
      a selector restriction — a family obligation restricted to these
      selectors follows by [In];
    - a [vm_compute] shape certificate enumerating, per selector, the
      regions and row ranges of its enabled points ([ecc_shape_cert]);
    - a [vm_compute] gate-body inversion: the constraints guarded by each
      selector are exactly the bodies of its defining gate
      ([bodies_of_q_ecc_add] &c.);
    - the field-algebra cores: the twelve complete-addition polynomials
      (reusing [CompleteAdditionCompleteness.witness_polys]), the two
      incomplete-addition polynomials, and the curve equation of the
      witness-point gates;
    - the point-level side conditions: every operand of every
      complete-addition row is a reduced curve-or-sentinel point, every
      incomplete-addition row has a non-vertical chord.  The fixed-base leg
      facts are the Γ-free ladder-distinctness argument
      ([circuit_proof/ladder/main.v], [circuit_proof/protocol_mul/core.v])
      instantiated at the generator's leg tables; the Sinsemilla hash
      outputs use the [nondegenerate] hypothesis; the variable-base rows
      use the [mul_nondegenerate_input] clause. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_complete.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.cert_defs.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.protocol_mul.core.
Require Import Garden.Orchard.circuit_proof.protocol_mul.commit_ivk_r.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.table.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.table.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.x_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.table.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.x_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.table.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.x_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.table.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.x_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.table.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.x_cert.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_r.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_v.
Require Import Garden.Orchard.circuit_proof.ladder.nullifier_k.
Require Import Garden.Orchard.circuit_proof.ladder.note_commit_r.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Orchard.circuit_completeness.advice_witness_io.
Require Import Garden.Orchard.circuit_completeness.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.tables_vb.
Require Import Garden.Orchard.circuit_completeness.tables_nc.
Require Import Garden.Orchard.circuit_completeness.tables.
Require Import Garden.Orchard.circuit_completeness.certificates.
Require Import Garden.Orchard.circuit_completeness.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

(* [Field.Fermat] (through the certificate chain) loads ssreflect, which
   turns bullet discipline off; the proofs below rely on bullets focusing
   subgoals. *)
#[local] Set Bullet Behavior "Strict Subproofs".

(* Keep the square-root / QR chain and scalar multiplication opaque to the
   conversion oracle (docs/compile-performance.md). *)
Strategy opaque
  [Garden.Field.Sqrt.is_square Garden.Field.Sqrt.modpow
   Garden.Field.Sqrt.modpow_pos Garden.Field.Sqrt.field_sqrt].
Strategy opaque [Pallas.mul Weierstrass.mul].

Module OrchardCompletenessForwardEccAdd.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessTables.

  Local Notation A0 := Advice.A0.
  Local Notation A1 := Advice.A1.
  Local Notation A2 := Advice.A2.
  Local Notation A3 := Advice.A3.
  Local Notation A4 := Advice.A4.
  Local Notation A5 := Advice.A5.
  Local Notation A6 := Advice.A6.
  Local Notation A7 := Advice.A7.
  Local Notation A8 := Advice.A8.
  Local Notation A9 := Advice.A9.

  (** ** The selector group and its obligation Props *)

  Definition is_ecc_sel (sel : Selector.t) : bool :=
    match sel with
    | Selector.QEccAdd | Selector.QAddIncomplete
    | Selector.QWitnessPoint | Selector.QWitnessPointNonId => true
    | _ => false
    end.

  (** The gate obligation of [Complete.circuit_holds_intro] restricted to the
      enabled points whose selector is in the ecc-add group — the
      selector-sliced analog of [OrchardCompletenessForward.family_gates_ok].
      A family obligation, restricted to the points of these selectors,
      follows from this Prop directly. *)
  Definition ecc_selector_gates_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        is_ecc_sel sel = true ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.

  (** The lookup obligation for the same points ([forward/api.v]'s
      [family_lookups_ok] shape at the loaded table size 1024).  It is
      vacuous: no configured lookup argument mentions an ecc-add selector
      ([ecc_lookup_mentions_cert]). *)
  Definition ecc_selector_lookups_ok : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (sel : Selector.t) (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        is_ecc_sel sel = true ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
            sel arg = true ->
          eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
            (region, row) 1024 arg.

  (** ** The enabled-point shape certificate

      Per ecc-add selector, the regions and row ranges of its enabled
      points, checked over all enabled points by one [vm_compute]. *)

  Definition ecc_shape_b (sel : Selector.t) (region : RegionId.t) (row : Z)
      : bool :=
    match sel with
    | Selector.QWitnessPoint =>
        match region with
        | RegionId.WitnessInput RegionId.WitnessInput.CmOld => row =? 0
        | _ => false
        end
    | Selector.QWitnessPointNonId =>
        match region with
        | RegionId.WitnessInput RegionId.WitnessInput.GDOld
        | RegionId.WitnessInput RegionId.WitnessInput.AkP
        | RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD
        | RegionId.NoteCommitNewWitnessGD
        | RegionId.NoteCommitNewWitnessPkD => row =? 0
        | _ => false
        end
    | Selector.QAddIncomplete =>
        match region with
        | RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete =>
            (1 <=? row) && (row <=? 20)
        | RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitRIncomplete
        | RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete
        | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete
        | RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete
        | RegionId.NoteCommit _ RegionId.NoteCommit.FixedBaseIncomplete =>
            (1 <=? row) && (row <=? 83)
        | _ => false
        end
    | Selector.QEccAdd =>
        match region with
        | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb
        | RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast
        | RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd
        | RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete
        | RegionId.Nullifier RegionId.Nullifier.CompletePointAdd
        | RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast
        | RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd
        | RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast
        | RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd
        | RegionId.NoteCommit _ RegionId.NoteCommit.FixedBaseLast
        | RegionId.NoteCommit _ RegionId.NoteCommit.CompletePointAdd =>
            row =? 0
        | RegionId.AddressIntegrity
            (RegionId.AddressIntegrity.Mul
              RegionId.AddressIntegrity.Mul.VariableBase) =>
            (row =? 0) || ((129 <=? row) && (row <=? 135))
        | _ => false
        end
    | _ => true
    end.

  Lemma ecc_shape_cert :
    List.forallb (fun '(sel, region, row) => ecc_shape_b sel region row)
      enabled = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma ecc_shape (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    ecc_shape_b sel region row = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ enabled) ecc_shape_cert
      (sel, region, row) Hin).
  Qed.

  (** ** Gate-body inversion

      The constraints guarded by a selector, collected from the configured
      system; each ecc-add selector's list is pinned to its defining gate's
      bodies by one [vm_compute]. *)

  Definition bodies_of (sel : Selector.t) : list (Constraint.t columns) :=
    List.flat_map
      (fun gate =>
        List.flat_map
          (fun '(_, c) =>
            match c with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s sel then [body] else []
            | _ => []
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma in_bodies_of (sel : Selector.t) (gate : Gate.t columns)
      (Hgate : List.In gate system.(ConstraintSystem.gates))
      (name : option PrimString.string) (body : Constraint.t columns)
      (Hbody : List.In (name, Constraint.Select sel body)
        gate.(Gate.constraints)) :
    List.In body (bodies_of sel).
  Proof.
    unfold bodies_of.
    apply List.in_flat_map.
    exists gate.
    split; [exact Hgate |].
    apply List.in_flat_map.
    exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    rewrite (proj2 (OrchardDecidableEq.selector_eqb_eq sel sel) eq_refl).
    left; reflexivity.
  Qed.

  (** The selector-stripped bodies of one gate record. *)
  Definition gate_raw_bodies (g : Gate.t columns) : list (Constraint.t columns) :=
    List.flat_map
      (fun '(_, c) =>
        match c with
        | Constraint.Select _ body => [body]
        | _ => []
        end)
      g.(Gate.constraints).

  Lemma bodies_of_q_ecc_add :
    bodies_of Selector.QEccAdd =
    gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.add
      .complete_addition_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.add
        .complete_addition_gate)).
  Qed.

  Lemma bodies_of_q_add_incomplete :
    bodies_of Selector.QAddIncomplete =
    gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
      .incomplete_addition_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
        .incomplete_addition_gate)).
  Qed.

  Lemma bodies_of_q_witness_point :
    bodies_of Selector.QWitnessPoint =
    gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
      .witness_point_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .witness_point_gate)).
  Qed.

  Lemma bodies_of_q_witness_point_non_id :
    bodies_of Selector.QWitnessPointNonId =
    gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
      .witness_non_identity_point_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .witness_non_identity_point_gate)).
  Qed.

  (** No configured lookup argument mentions an ecc-add selector. *)
  Lemma ecc_lookup_mentions_cert :
    List.forallb
      (fun arg =>
        negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QEccAdd arg) &&
        negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QAddIncomplete arg) &&
        negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QWitnessPoint arg) &&
        negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QWitnessPointNonId arg))
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The lookup obligation is vacuous on the ecc-add selectors. *)
  Theorem ecc_add_lookups_forward : ecc_selector_lookups_ok.
  Proof.
    intros w _ _ sel region row _ Hsel arg Harg Hmention.
    exfalso.
    pose proof (proj1 (List.forallb_forall _ _) ecc_lookup_mentions_cert
      arg Harg) as Hcert.
    apply Bool.andb_true_iff in Hcert; destruct Hcert as [Hcert H4].
    apply Bool.andb_true_iff in Hcert; destruct Hcert as [Hcert H3].
    apply Bool.andb_true_iff in Hcert; destruct Hcert as [H1 H2].
    destruct sel; try discriminate Hsel;
      [ rewrite Hmention in H3; discriminate
      | rewrite Hmention in H4; discriminate
      | rewrite Hmention in H2; discriminate
      | rewrite Hmention in H1; discriminate ].
  Qed.

  (** ** Field-algebra cores

      One evaluation lemma per gate, abstract in the assignment: given the
      cell values of an honest row (the [assign_complete_add] witness
      formulas, an incomplete-addition triple, a witnessed point), every
      constraint body of the gate evaluates. *)

  (** A complete-addition operand: reduced coordinates, on the curve or the
      [(0, 0)] sentinel — [witness_polys]' input domain. *)
  Definition cadd_input_ok (P : Point.t) : Prop :=
    0 <= Point.x P < Primes.pallas_p /\
    0 <= Point.y P < Primes.pallas_p /\
    CompleteAdditionCompleteness.on_curve_or_identity (Point.x P) (Point.y P).

  Lemma from_minus_self (a : Z) : UnOp.from a -F a = 0.
  Proof.
    unfold UnOp.from, BinOp.sub.
    rewrite Zminus_mod_idemp_l, Z.sub_diag.
    apply Zmod_0_l.
  Qed.

  (** The twelve complete-addition constraint bodies, at the honest cells of
      operands [p], [q] and output [EccSpec.point_add p q]. *)
  Lemma cadd_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (p q : Point.t)
      (HA0 : Γ.(Assignment.advice) A0 region row = Point.x p)
      (HA1 : Γ.(Assignment.advice) A1 region row = Point.y p)
      (HA2 : Γ.(Assignment.advice) A2 region row = Point.x q)
      (HA3 : Γ.(Assignment.advice) A3 region row = Point.y q)
      (HA4 : Γ.(Assignment.advice) A4 region row =
        CompleteAdditionCompleteness.lambda_w
          (Point.x p) (Point.y p) (Point.x q) (Point.y q))
      (HA5 : Γ.(Assignment.advice) A5 region row =
        CompleteAdditionCompleteness.alpha_w (Point.x p) (Point.x q))
      (HA6 : Γ.(Assignment.advice) A6 region row =
        CompleteAdditionCompleteness.beta_w (Point.x p))
      (HA7 : Γ.(Assignment.advice) A7 region row =
        CompleteAdditionCompleteness.gamma_w (Point.x q))
      (HA8 : Γ.(Assignment.advice) A8 region row =
        CompleteAdditionCompleteness.delta_w
          (Point.x p) (Point.y p) (Point.x q) (Point.y q))
      (HA2' : Γ.(Assignment.advice) A2 region (row + 1) =
        (CompleteAddition.output
          (Point.x p) (Point.y p) (Point.x q) (Point.y q)).(Point.x))
      (HA3' : Γ.(Assignment.advice) A3 region (row + 1) =
        (CompleteAddition.output
          (Point.x p) (Point.y p) (Point.x q) (Point.y q)).(Point.y))
      (HP : cadd_input_ok p)
      (HQ : cadd_input_ok q)
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate)) :
    eval_constraint Γ (region, row) body.
  Proof.
    destruct HP as (Hpx & Hpy & HP).
    destruct HQ as (Hqx & Hqy & HQ).
    pose proof (CompleteAdditionCompleteness.witness_polys
      (Point.x p) (Point.y p) (Point.x q) (Point.y q)
      Hpx Hpy Hqx Hqy HP HQ) as HW.
    cbv zeta in HW.
    destruct HW as (HG1 & HG2 & HG3a & HG3b & HG3c & HG3d &
      HG4a & HG4b & HG5a & HG5b & HG6a & HG6b).
    cbn in Hbody.
    destruct Hbody as
      [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | Habs
      ] ] ] ] ] ] ] ] ] ] ] ];
      [ | | | | | | | | | | | | destruct Habs ].
    all: subst body.
    all: with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p
       CompleteAdditionCompleteness.lambda_w
       CompleteAdditionCompleteness.alpha_w
       CompleteAdditionCompleteness.beta_w
       CompleteAdditionCompleteness.gamma_w
       CompleteAdditionCompleteness.delta_w
       CompleteAddition.output]
      cbn.
    all: cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    all: rewrite ?Z.add_0_r.
    all: rewrite ?HA0, ?HA1, ?HA2, ?HA3, ?HA4, ?HA5, ?HA6, ?HA7, ?HA8,
      ?HA2', ?HA3'.
    all: autorewrite with field_rewrite.
    { exact HG1. }
    { exact HG2. }
    { exact HG3a. }
    { exact HG3b. }
    { exact HG3c. }
    { exact HG3d. }
    { exact HG4a. }
    { exact HG4b. }
    { exact HG5a. }
    { exact HG5b. }
    { exact HG6a. }
    { exact HG6b. }
  Qed.

  (** The two incomplete-addition constraint bodies, at the honest cells of
      operands [p], [q] (with a non-vertical chord) and output
      [EccSpec.point_add_incomplete p q]. *)
  Lemma incomplete_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (p q : Point.t)
      (HA0 : Γ.(Assignment.advice) A0 region row = Point.x p)
      (HA1 : Γ.(Assignment.advice) A1 region row = Point.y p)
      (HA2 : Γ.(Assignment.advice) A2 region row = Point.x q)
      (HA3 : Γ.(Assignment.advice) A3 region row = Point.y q)
      (HA2' : Γ.(Assignment.advice) A2 region (row + 1) =
        Point.x (EccSpec.point_add_incomplete p q))
      (HA3' : Γ.(Assignment.advice) A3 region (row + 1) =
        Point.y (EccSpec.point_add_incomplete p q))
      (Hd : UnOp.from (Point.x p -F Point.x q) <> 0)
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
            .incomplete_addition_gate)) :
    eval_constraint Γ (region, row) body.
  Proof.
    set (L := BinOp.div (Point.y p -F Point.y q) (Point.x p -F Point.x q)).
    assert (Hlam : L *F (Point.x p -F Point.x q) = Point.y p -F Point.y q).
    { unfold L. rewrite div_mul.
      - apply FieldRewrite.from_sub.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd. }
    assert (Hxr : Point.x (EccSpec.point_add_incomplete p q) =
      L *F L -F Point.x p -F Point.x q) by reflexivity.
    assert (Hyr : Point.y (EccSpec.point_add_incomplete p q) =
      L *F (Point.x p -F (L *F L -F Point.x p -F Point.x q)) -F Point.y p)
      by reflexivity.
    cbn in Hbody.
    destruct Hbody as [H | [H | Habs] ]; [ | | destruct Habs].
    all: subst body.
    all: with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from mod_inverse
       Primes.pallas_p Primes.t_p]
      cbn.
    all: cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    all: rewrite ?Z.add_0_r.
    all: rewrite ?HA0, ?HA1, ?HA2, ?HA3, ?HA2', ?HA3'.
    all: rewrite ?Hxr, ?Hyr.
    all: autorewrite with field_rewrite.
    - (* poly1: (x_r + x_q + x_p)(x_p − x_q)² = (y_p − y_q)². *)
      assert (Hshape :
        (L *F L -F Point.x p -F Point.x q +F Point.x q +F Point.x p) *F
          (Point.x p -F Point.x q) *F (Point.x p -F Point.x q) -F
        (Point.y p -F Point.y q) *F (Point.y p -F Point.y q) =
        (L *F (Point.x p -F Point.x q)) *F (L *F (Point.x p -F Point.x q)) -F
        (Point.y p -F Point.y q) *F (Point.y p -F Point.y q))
        by mod_ring_solve.
      rewrite Hshape, Hlam.
      apply CompleteAdditionCompleteness.sub_self.
    - (* poly2: (y_r + y_q)(x_p − x_q) = (y_p − y_q)(x_q − x_r). *)
      assert (Hshape :
        (L *F (Point.x p -F (L *F L -F Point.x p -F Point.x q)) -F Point.y p
          +F Point.y q) *F (Point.x p -F Point.x q) -F
        (Point.y p -F Point.y q) *F
          (Point.x q -F (L *F L -F Point.x p -F Point.x q)) =
        (L *F (Point.x p -F Point.x q) -F (Point.y p -F Point.y q)) *F
          (Point.x p -F (L *F L -F Point.x p -F Point.x q)))
        by mod_ring_solve.
      rewrite Hshape, Hlam.
      rewrite CompleteAdditionCompleteness.sub_self.
      apply FieldRewrite.mul_zero_left.
  Qed.

  (** The witness-non-identity constraint body: the curve equation at the
      witnessed cells. *)
  Lemma witness_non_id_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (P : Point.t)
      (HA0 : Γ.(Assignment.advice) A0 region row = Point.x P)
      (HA1 : Γ.(Assignment.advice) A1 region row = Point.y P)
      (Hcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_non_identity_point_gate)) :
    eval_constraint Γ (region, row) body.
  Proof.
    cbn in Hbody.
    destruct Hbody as [H | Habs]; [ | destruct Habs].
    subst body.
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from
       Primes.pallas_p Primes.t_p]
      cbn.
    cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    rewrite ?Z.add_0_r.
    rewrite ?HA0, ?HA1.
    autorewrite with field_rewrite.
    exact Hcurve.
  Qed.

  (** The two witness-point constraint bodies: curve-or-sentinel at the
      witnessed cells. *)
  Lemma witness_point_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (P : Point.t)
      (HA0 : Γ.(Assignment.advice) A0 region row = Point.x P)
      (HA1 : Γ.(Assignment.advice) A1 region row = Point.y P)
      (Hok : CompleteAdditionCompleteness.on_curve_or_identity
        (Point.x P) (Point.y P))
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_point_gate)) :
    eval_constraint Γ (region, row) body.
  Proof.
    cbn in Hbody.
    destruct Hbody as [H | [H | Habs] ]; [ | | destruct Habs].
    all: subst body.
    all: with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from
       Primes.pallas_p Primes.t_p]
      cbn.
    all: cbv [rotated_row Rotation.cur Rotation.next Rotation.offset].
    all: rewrite ?Z.add_0_r.
    all: rewrite ?HA0, ?HA1.
    all: autorewrite with field_rewrite.
    - (* x = 0 or on-curve. *)
      destruct Hok as [Hcurve | [Hx0 _] ].
      + right. exact Hcurve.
      + left. rewrite Hx0. reflexivity.
    - (* y = 0 or on-curve. *)
      destruct Hok as [Hcurve | [_ Hy0] ].
      + right. exact Hcurve.
      + left. rewrite Hy0. reflexivity.
  Qed.

  (** ** Point-level facts

      [wgood]: the point is the [repr] of a reduced on-curve Weierstrass
      point — the closure-friendly form of [cadd_input_ok].  [pt_affine_ok]:
      the affine strengthening (the curve polynomial holds of the record, so
      the sentinel is excluded), used through the Sinsemilla fold. *)

  Definition wgood (P : Point.t) : Prop :=
    exists Pw : Pallas.point,
      Pallas.reduced Pw /\ Pallas.on_curve Pw /\ P = PallasModel.repr Pw.

  Definition pt_affine_ok (P : Point.t) : Prop :=
    Point.y P *F Point.y P -F
      (Point.x P *F Point.x P *F Point.x P) -F
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0 /\
    UnOp.from (Point.x P) = Point.x P /\
    UnOp.from (Point.y P) = Point.y P.

  Lemma pallas_p_pos : 0 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p; lia. Qed.

  Lemma reduced_bounds (x : Z) :
    UnOp.from x = x -> 0 <= x < Primes.pallas_p.
  Proof.
    intro H. rewrite <- H. apply Z.mod_pos_bound. exact pallas_p_pos.
  Qed.

  Lemma wgood_cadd_input (P : Point.t) : wgood P -> cadd_input_ok P.
  Proof.
    intros (Pw & Hred & Hoc & ->).
    destruct Pw as [| x y].
    - unfold cadd_input_ok.
      change (PallasModel.repr Weierstrass.Infinity) with
        {| Point.x := 0; Point.y := 0 |}.
      cbn [Point.x Point.y].
      pose proof pallas_p_pos as Hp.
      refine (conj _ (conj _ _)).
      + lia.
      + lia.
      + right. split; reflexivity.
    - cbn [PallasModel.repr].
      unfold cadd_input_ok; cbn [Point.x Point.y].
      destruct Hred as [Hx Hy].
      split; [exact (reduced_bounds x Hx) |].
      split; [exact (reduced_bounds y Hy) |].
      left. exact (PallasModel.on_curve_affine_poly x y Hoc).
  Qed.

  Lemma wgood_repr_mul (G : Pallas.point) (k : Z)
      (HGred : Pallas.reduced G) (HGoc : Pallas.on_curve G) :
    wgood (PallasModel.repr (Pallas.mul k G)).
  Proof.
    exists (Pallas.mul k G).
    split; [exact (FixedBaseLadder.pallas_mul_reduced k G HGred) |].
    split; [exact (FixedBaseLadder.pallas_mul_on_curve k G HGoc) |].
    reflexivity.
  Qed.

  Lemma wgood_point_add (P Q : Point.t) :
    wgood P -> wgood Q -> wgood (EccSpec.point_add P Q).
  Proof.
    intros (Pw & HPr & HPo & ->) (Qw & HQr & HQo & ->).
    exists (Pallas.add Pw Qw).
    refine (conj _ (conj _ _)).
    - apply Weierstrass.add_reduced; [exact HPr | exact HQr].
    - apply Weierstrass.add_on_curve;
        [exact FixedBaseLadder.pallas_3_lt | exact HPo | exact HQo].
    - symmetry.
      exact (FixedBaseLadder.pallas_repr_add Pw Qw HPr HQr HPo HQo).
  Qed.

  Lemma wgood_point_neg (P : Point.t) : wgood P -> wgood (point_neg P).
  Proof.
    intros (Pw & Hred & Hoc & ->).
    exists (Pallas.neg Pw).
    split; [exact (VarBaseDefs.pallas_neg_reduced Pw Hred) |].
    split; [exact (VarBaseDefs.pallas_neg_on_curve Pw Hoc) |].
    destruct Pw as [| x y]; reflexivity.
  Qed.

  Lemma wgood_identity : wgood EccSpec.identity.
  Proof.
    exists Pallas.identity.
    exact (conj I (conj I eq_refl)).
  Qed.

  (** The curve polynomial pins the Weierstrass curve membership. *)
  Lemma poly_on_curve (x y : Z)
      (H : y *F y -F (x *F x *F x) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0) :
    Pallas.on_curve (Weierstrass.Affine x y).
  Proof.
    unfold Pallas.on_curve; cbn [Weierstrass.on_curve].
    unfold Pallas.a, Pallas.b.
    assert (Hz : (0:Z) *F x = 0).
    { unfold BinOp.mul. rewrite Z.mul_0_l. apply Zmod_0_l. }
    rewrite Hz, FieldRewrite.add_zero_right.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b in H.
    set (A := y *F y) in *.
    set (B := x *F x *F x) in *.
    clearbody A B.
    unfold BinOp.add, BinOp.sub, UnOp.from in *.
    pose proof pallas_p_pos as Hp.
    pose proof (Z.mod_pos_bound (A - B) Primes.pallas_p Hp).
    pose proof (Z.mod_pos_bound A Primes.pallas_p Hp).
    pose proof (Z.mod_pos_bound B Primes.pallas_p Hp).
    rewrite Zminus_mod_idemp_l in H.
    rewrite Zplus_mod_idemp_l.
    assert (Hd : (A - B - 5) mod Primes.pallas_p = 0) by exact H.
    apply Z.mod_divide in Hd; [| lia].
    destruct Hd as [t Ht].
    replace A with (B + 5 + t * Primes.pallas_p) by lia.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_mod by lia.
    reflexivity.
  Qed.

  Lemma pt_affine_wgood (P : Point.t) : pt_affine_ok P -> wgood P.
  Proof.
    intros (Hcurve & Hx & Hy).
    exists (Weierstrass.Affine (Point.x P) (Point.y P)).
    split; [exact (conj Hx Hy) |].
    split; [exact (poly_on_curve _ _ Hcurve) |].
    destruct P; reflexivity.
  Qed.

  Lemma pt_affine_cadd_input (P : Point.t) : pt_affine_ok P -> cadd_input_ok P.
  Proof.
    intro H. exact (wgood_cadd_input P (pt_affine_wgood P H)).
  Qed.

  Lemma pt_affine_x_nonzero (P : Point.t) :
    pt_affine_ok P -> UnOp.from (Point.x P) <> 0.
  Proof.
    intros (Hcurve & _ & _).
    exact (EccSpec.pallas_curve_x_nonzero (Point.x P) (Point.y P) Hcurve).
  Qed.

  (** [repr] of a reduced on-curve non-identity multiple is [pt_affine_ok]. *)
  Lemma repr_affine_of_ne (Pw : Pallas.point)
      (Hred : Pallas.reduced Pw) (Hoc : Pallas.on_curve Pw)
      (Hne : Pw <> Pallas.identity) :
    pt_affine_ok (PallasModel.repr Pw).
  Proof.
    destruct Pw as [| x y]; [exact (False_ind _ (Hne eq_refl)) |].
    cbn [PallasModel.repr].
    unfold pt_affine_ok; cbn [Point.x Point.y].
    destruct Hred as [Hx Hy].
    split; [exact (PallasModel.on_curve_affine_poly x y Hoc) |].
    exact (conj Hx Hy).
  Qed.

  (** ** The Sinsemilla layer

      The generator table and the domain points are affine on-curve
      ([vm_compute] certificates); the hash fold preserves [pt_affine_ok]
      under the [SinsemillaHash.nondegenerate] side conditions. *)

  Definition pt_affine_b (P : Point.t) : bool :=
    ((Point.y P *F Point.y P -F
        (Point.x P *F Point.x P *F Point.x P) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b) =? 0) &&
    (UnOp.from (Point.x P) =? Point.x P) &&
    (UnOp.from (Point.y P) =? Point.y P).

  Lemma pt_affine_b_ok (P : Point.t) : pt_affine_b P = true -> pt_affine_ok P.
  Proof.
    unfold pt_affine_b.
    intro H.
    apply Bool.andb_true_iff in H; destruct H as [H Hy].
    apply Bool.andb_true_iff in H; destruct H as [Hc Hx].
    apply Z.eqb_eq in Hc, Hx, Hy.
    exact (conj Hc (conj Hx Hy)).
  Qed.

  Lemma generator_cert :
    List.forallb
      (fun i => pt_affine_b (SinsemillaSpec.generator (Z.of_nat i)))
      (List.seq 0 1024) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma generator_affine (wd : Z) :
    0 <= wd < 1024 -> pt_affine_ok (SinsemillaSpec.generator wd).
  Proof.
    intro Hwd.
    apply pt_affine_b_ok.
    pose proof (forallb_seq_sound
      (fun i => pt_affine_b (SinsemillaSpec.generator (Z.of_nat i)))
      0 1024 generator_cert (Z.to_nat wd) ltac:(lia)) as H.
    cbn beta in H.
    rewrite Z2Nat.id in H by lia.
    exact H.
  Qed.

  Lemma merkle_Q_affine : pt_affine_ok merkle_Q.
  Proof.
    apply pt_affine_b_ok.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma note_commit_q_affine :
    pt_affine_ok (OrchardSpec.note_commit_q orchard_circuit_params).
  Proof.
    apply pt_affine_b_ok.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma commit_ivk_q_affine :
    pt_affine_ok (OrchardSpec.commit_ivk_q orchard_circuit_params).
  Proof.
    apply pt_affine_b_ok.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** One Sinsemilla round preserves the affine invariant, under the round's
      two non-verticality conditions. *)
  Lemma round_affine (acc : Point.t) (wd : Z)
      (Hacc : pt_affine_ok acc) (Hwd : 0 <= wd < 1024)
      (H1 : Point.x acc <> Point.x (SinsemillaSpec.generator wd))
      (H2 : Point.x acc <>
        Point.x (EccSpec.point_add_incomplete acc
          (SinsemillaSpec.generator wd))) :
    pt_affine_ok (SinsemillaSpec.round acc wd).
  Proof.
    pose proof (generator_affine wd Hwd) as Hgen.
    pose proof Hacc as (Hacc_c & Hacc_x & Hacc_y).
    pose proof Hgen as (Hgen_c & Hgen_x & Hgen_y).
    pose proof (pt_affine_x_nonzero acc Hacc) as Hacc_nz.
    pose proof (pt_affine_x_nonzero _ Hgen) as Hgen_nz.
    assert (Hd1 : UnOp.from (Point.x acc) <>
        UnOp.from (Point.x (SinsemillaSpec.generator wd))).
    { rewrite Hacc_x, Hgen_x. exact H1. }
    assert (Hmid_eq : EccSpec.point_add_incomplete acc
        (SinsemillaSpec.generator wd) =
      EccSpec.point_add (SinsemillaSpec.generator wd) acc).
    { exact (OrchardActionFixedBase.point_add_incomplete_eq_point_add_swap
        acc (SinsemillaSpec.generator wd) Hacc_nz Hgen_nz Hd1). }
    set (mid := EccSpec.point_add_incomplete acc
      (SinsemillaSpec.generator wd)) in *.
    assert (Hmid : pt_affine_ok mid).
    { rewrite Hmid_eq.
      unfold pt_affine_ok.
      split.
      { exact (EccSpec.point_add_on_curve_x_distinct
          (SinsemillaSpec.generator wd) acc Hgen_c Hacc_c Hgen_nz Hacc_nz
          (fun Hc => Hd1 (eq_sym Hc))). }
      exact (OrchardActionFixedBase.point_add_reduced
        (SinsemillaSpec.generator wd) acc Hgen_x Hgen_y Hacc_x Hacc_y). }
    pose proof Hmid as (Hmid_c & Hmid_x & Hmid_y).
    pose proof (pt_affine_x_nonzero mid Hmid) as Hmid_nz.
    assert (Hd2 : UnOp.from (Point.x mid) <> UnOp.from (Point.x acc)).
    { rewrite Hmid_x, Hacc_x. intro Hc. exact (H2 (eq_sym Hc)). }
    assert (Hround_eq : SinsemillaSpec.round acc wd =
      EccSpec.point_add acc mid).
    { unfold SinsemillaSpec.round.
      exact (OrchardActionFixedBase.point_add_incomplete_eq_point_add_swap
        mid acc Hmid_nz Hacc_nz Hd2). }
    rewrite Hround_eq.
    unfold pt_affine_ok.
    split.
    { exact (EccSpec.point_add_on_curve_x_distinct acc mid
        Hacc_c Hmid_c Hacc_nz Hmid_nz (fun Hc => Hd2 (eq_sym Hc))). }
    exact (OrchardActionFixedBase.point_add_reduced acc mid
      Hacc_x Hacc_y Hmid_x Hmid_y).
  Qed.

  (** The fold preserves the affine invariant along a nondegenerate
      in-range message. *)
  Lemma hash_affine (words : list Z) :
    forall Q : Point.t,
      pt_affine_ok Q ->
      List.Forall (fun w => 0 <= w < 1024) words ->
      SinsemillaHash.nondegenerate Q words ->
      pt_affine_ok (SinsemillaSpec.sinsemilla_hash_to_point Q words).
  Proof.
    induction words as [| wd ws IH]; intros Q HQ Hrange Hnd.
    - exact HQ.
    - inversion Hrange as [| ? ? Hwd Hws]; subst.
      pose proof (Hnd 0%nat ltac:(cbn [List.length]; lia)) as Hnd0.
      cbn [List.firstn List.nth SinsemillaSpec.sinsemilla_hash_to_point
        Stdlib.Lists.List.fold_left] in Hnd0.
      destruct Hnd0 as [H1 H2].
      assert (Hfold : SinsemillaSpec.sinsemilla_hash_to_point Q (wd :: ws) =
        SinsemillaSpec.sinsemilla_hash_to_point
          (SinsemillaSpec.round Q wd) ws) by reflexivity.
      rewrite Hfold.
      apply IH.
      + exact (round_affine Q wd HQ Hwd H1 H2).
      + exact Hws.
      + intros k Hk.
        pose proof (Hnd (S k) ltac:(cbn [List.length]; lia)) as HndS.
        cbn [List.firstn List.nth] in HndS.
        exact HndS.
  Qed.

  (** The 10-bit little-endian decomposition is in range. *)
  Lemma words_le_range (count : nat) :
    forall n : Z,
      List.Forall (fun w => 0 <= w < 1024)
        (SinsemillaSpec.words_le count n).
  Proof.
    induction count as [| c IH]; intro n.
    - constructor.
    - cbn [SinsemillaSpec.words_le].
      constructor.
      + exact (Z.mod_pos_bound n (2 ^ SinsemillaSpec.sinsemilla_k)
          ltac:(vm_compute; reflexivity)).
      + exact (IH (n / 2 ^ SinsemillaSpec.sinsemilla_k)).
  Qed.

  Lemma words_le_length (count : nat) :
    forall n : Z,
      List.length (SinsemillaSpec.words_le count n) = count.
  Proof.
    induction count as [| c IH]; intro n.
    - reflexivity.
    - cbn [SinsemillaSpec.words_le List.length].
      rewrite IH. reflexivity.
  Qed.

  (** Every point-addition coordinate is a chord over [BinOp.div], and
      [BinOp.div] runs [mod_inverse] (the extended-Euclid loop at the concrete
      [mod_inv_fuel pallas_p ~ 512] fuel) — so any conversion that reaches an
      addition coordinate on symbolic points unfolds that loop into a giant
      term (tens of seconds at the tactic AND again at [Qed]).  From here the
      field division is opaque to the conversion oracle, so the equal chord
      spellings of [hash_go]/[point_add]/[point_add_incomplete] match as stuck
      atoms instead of being reduced (docs/compile-performance.md).  A
      persistent [Strategy] (not [with_strategy]) is required so the kernel
      [Qed] re-check is cheap too; the ring operators [BinOp.add/sub/mul] stay
      transparent so [mod_ring_solve]/[field_solve] still normalize.
      [CompleteAddition.output] (the complete-addition chord, over the same
      [BinOp.div]) is opaque for the same reason — its case split otherwise
      forces the nested leg-point coordinates. *)
  Strategy opaque [BinOp.div mod_inverse CompleteAddition.output].

  (** ** [hash_data_of] against the specification fold *)

  Lemma hash_go_snd (ws : list Z) :
    forall acc : Point.t,
      snd (hash_go acc ws) =
      SinsemillaSpec.sinsemilla_hash_to_point acc ws.
  Proof.
    induction ws as [| wd ws IH]; intro acc.
    - reflexivity.
    - cbn [hash_go].
      cbv zeta.
      rewrite (surjective_pairing (hash_go _ ws)).
      cbn [fst snd].
      rewrite IH.
      reflexivity.
  Qed.

  (** ** Boolean-guard and conversion helpers *)

  Lemma guard_le_lt (lo hi x : Z) :
    lo <= x -> x < hi -> ((lo <=? x) && (x <? hi))%bool = true.
  Proof.
    intros H1 H2.
    rewrite (proj2 (Z.leb_le lo x) H1), (proj2 (Z.ltb_lt x hi) H2).
    reflexivity.
  Qed.

  Lemma guard_le_le (lo hi x : Z) :
    lo <= x -> x <= hi -> ((lo <=? x) && (x <=? hi))%bool = true.
  Proof.
    intros H1 H2.
    rewrite (proj2 (Z.leb_le lo x) H1), (proj2 (Z.leb_le x hi) H2).
    reflexivity.
  Qed.

  Lemma leb_of_le (a b : Z) : a <= b -> (a <=? b) = true.
  Proof. apply Z.leb_le. Qed.

  (** ** [point_ok] plumbing *)

  Lemma wgood_of_point_ok (P : Point.t) : point_ok P -> wgood P.
  Proof.
    intros (Hred & Hoc & _).
    exists (PallasModel.unrepr P).
    exact (conj Hred (conj Hoc (eq_sym (PallasModel.repr_unrepr P)))).
  Qed.

  Lemma pt_affine_of_point_ok (P : Point.t) : point_ok P -> pt_affine_ok P.
  Proof.
    intros (Hred & Hoc & Hne).
    rewrite <- (PallasModel.repr_unrepr P).
    apply repr_affine_of_ne.
    - exact Hred.
    - exact Hoc.
    - intro Hc.
      apply Hne.
      rewrite <- (PallasModel.repr_unrepr P), Hc.
      reflexivity.
  Qed.

  Lemma pt_affine_neg (P : Point.t) :
    pt_affine_ok P -> pt_affine_ok (point_neg P).
  Proof.
    intros (Hc & Hx & Hy).
    unfold pt_affine_ok, point_neg; cbn [Point.x Point.y].
    assert (Hsq : (0 -F Point.y P) *F (0 -F Point.y P) =
      Point.y P *F Point.y P) by mod_ring_solve.
    rewrite Hsq.
    split; [exact Hc |].
    split; [exact Hx | apply from_sub_reduced].
  Qed.

  Lemma wgood_neg_of_point_ok (P : Point.t) :
    point_ok P -> wgood (point_neg P).
  Proof.
    intro H.
    apply wgood_point_neg, wgood_of_point_ok, H.
  Qed.

  (** Coordinates of the [repr] of a reduced Weierstrass point are
      reduced. *)
  Lemma repr_coords_reduced (P : Pallas.point) (HP : Pallas.reduced P) :
    UnOp.from (Point.x (PallasModel.repr P)) = Point.x (PallasModel.repr P) /\
    UnOp.from (Point.y (PallasModel.repr P)) = Point.y (PallasModel.repr P).
  Proof.
    destruct P as [| x y].
    - cbn [PallasModel.repr EccSpec.identity Point.x Point.y].
      split; apply Zmod_0_l.
    - destruct HP as [Hx Hy].
      cbn [PallasModel.repr Point.x Point.y].
      exact (conj Hx Hy).
  Qed.

  (** ** The complete-addition region package

      A region whose advice plane is [cadd_advice p q] satisfies every
      complete-addition constraint at row [0], for operands in the
      [cadd_input_ok] domain.  The [OrchardAdviceEccMuls] witness formulas
      convert to the [CompleteAdditionCompleteness] ones ([square] is the
      only definitional difference), and the row-1 output cells are the
      [EccSpec.point_add] coordinates by definition. *)
  Lemma cadd_region_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (p q : Point.t)
      (Hadv : forall (col : Advice.t) (off : Z),
        Γ.(Assignment.advice) col region off =
        OrchardAdviceEccMuls.cadd_advice p q col off)
      (HP : cadd_input_ok p) (HQ : cadd_input_ok q)
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate)) :
    eval_constraint Γ (region, 0) body.
  Proof.
    apply (cadd_eval Γ region 0 p q); try assumption.
    all: rewrite Hadv; reflexivity.
  Qed.

  (** ** Piece splitting and the hash-region output *)

  Lemma concat_split_pieces (lens : list nat) :
    forall l : list Z,
      (List.length l <= List.list_sum lens)%nat ->
      List.concat (OrchardAdviceMerkleSinsemilla.split_pieces lens l) = l.
  Proof.
    induction lens as [| n lens IH]; intros l Hl;
      cbn [OrchardAdviceMerkleSinsemilla.split_pieces List.concat].
    - destruct l as [| x l]; [reflexivity | cbn in Hl; lia].
    - rewrite IH.
      + apply List.firstn_skipn.
      + rewrite List.length_skipn.
        unfold List.list_sum in Hl |- *.
        cbn [Stdlib.Lists.List.fold_right] in Hl.
        lia.
  Qed.

  Lemma hd_out_hash_data (Q : Point.t) (pieces : list (list Z)) :
    hd_out (hash_data_of Q pieces) =
    SinsemillaSpec.sinsemilla_hash_to_point Q
      (Stdlib.Lists.List.concat pieces).
  Proof.
    unfold hash_data_of.
    rewrite (surjective_pairing
      (hash_go Q (Stdlib.Lists.List.concat pieces))).
    cbn [hd_out].
    apply hash_go_snd.
  Qed.

  (** The three commitment messages are [words_le] packings, so their word
      lists are in range and of pinned length, and the configured piece
      splittings reassemble them. *)

  Lemma note_commit_words_concat (g_d pk_d : Point.t) (v rho psi : Z) :
    Stdlib.Lists.List.concat
      (OrchardAdviceMerkleSinsemilla.split_pieces
        OrchardAdviceMerkleSinsemilla.note_commit_lens
        (OrchardSpec.note_commit_message g_d pk_d v rho psi)) =
    OrchardSpec.note_commit_message g_d pk_d v rho psi.
  Proof.
    apply concat_split_pieces.
    unfold OrchardSpec.note_commit_message.
    rewrite words_le_length.
    cbn. lia.
  Qed.

  Lemma commit_ivk_words_concat (ak nk : Z) :
    Stdlib.Lists.List.concat
      (OrchardAdviceMerkleSinsemilla.split_pieces
        OrchardAdviceMerkleSinsemilla.commit_ivk_lens
        (OrchardSpec.commit_ivk_message ak nk)) =
    OrchardSpec.commit_ivk_message ak nk.
  Proof.
    apply concat_split_pieces.
    unfold OrchardSpec.commit_ivk_message.
    rewrite words_le_length.
    cbn. lia.
  Qed.

  Lemma note_commit_message_range (g_d pk_d : Point.t) (v rho psi : Z) :
    List.Forall (fun wd => 0 <= wd < 1024)
      (OrchardSpec.note_commit_message g_d pk_d v rho psi).
  Proof. apply words_le_range. Qed.

  Lemma commit_ivk_message_range (ak nk : Z) :
    List.Forall (fun wd => 0 <= wd < 1024)
      (OrchardSpec.commit_ivk_message ak nk).
  Proof. apply words_le_range. Qed.

  (** The affine invariant of a note-commitment hash output, from the
      nondegeneracy of its message. *)
  Lemma note_commit_hash_out_affine (g_d pk_d : Point.t) (v rho psi : Z)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.note_commit_q orchard_circuit_params)
        (OrchardSpec.note_commit_message g_d pk_d v rho psi)) :
    pt_affine_ok
      (hd_out
        (hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
          (OrchardAdviceMerkleSinsemilla.split_pieces
            OrchardAdviceMerkleSinsemilla.note_commit_lens
            (OrchardSpec.note_commit_message g_d pk_d v rho psi)))).
  Proof.
    rewrite hd_out_hash_data, note_commit_words_concat.
    apply hash_affine.
    - exact note_commit_q_affine.
    - apply note_commit_message_range.
    - exact Hnd.
  Qed.

  Lemma commit_ivk_hash_out_affine (ak nk : Z)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.commit_ivk_q orchard_circuit_params)
        (OrchardSpec.commit_ivk_message ak nk)) :
    pt_affine_ok
      (hd_out
        (hash_data_of OrchardAdviceMerkleSinsemilla.commit_ivk_Q
          (OrchardAdviceMerkleSinsemilla.split_pieces
            OrchardAdviceMerkleSinsemilla.commit_ivk_lens
            (OrchardSpec.commit_ivk_message ak nk)))).
  Proof.
    rewrite hd_out_hash_data, commit_ivk_words_concat.
    apply hash_affine.
    - exact commit_ivk_q_affine.
    - apply commit_ivk_message_range.
    - exact Hnd.
  Qed.

  (** ** Read-offs of the hoisted table record

      Each projection of [tables_of w] reduces to its builder applied to
      [w]; the equations below are definitional and pin the spellings the
      region branches rewrite with. *)

  Lemma advice_read (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) =
    advice_t w (tables_of w).
  Proof. reflexivity. Qed.

  Lemma t_sa_leg_eq (w : HonestInput) :
    t_sa_leg (tables_of w) =
    leg_of OrchardAdviceEccMuls.tbl_spend_auth
      SpendAuthGWindowSignCert.root_table (hi_alpha w).
  Proof. reflexivity. Qed.

  Lemma t_vcr_leg_eq (w : HonestInput) :
    t_vcr_leg (tables_of w) =
    leg_of OrchardAdviceEccMuls.tbl_value_commit_r
      ValueCommitRWindowSignCert.root_table (hi_rcv w).
  Proof. reflexivity. Qed.

  Lemma t_vcv_leg_eq (w : HonestInput) :
    t_vcv_leg (tables_of w) =
    leg_of OrchardAdviceEccMuls.tbl_value_commit_v
      ValueCommitVWindowSignCert.root_table (magnitude w).
  Proof. reflexivity. Qed.

  Lemma t_nco_leg_eq (w : HonestInput) :
    t_nco_leg (tables_of w) =
    leg_of OrchardAdviceEccMuls.tbl_note_commit_r
      NoteCommitRWindowSignCert.root_table (hi_rcm_old w).
  Proof. reflexivity. Qed.

  Lemma t_ncn_leg_eq (w : HonestInput) :
    t_ncn_leg (tables_of w) =
    leg_of OrchardAdviceEccMuls.tbl_note_commit_r
      NoteCommitRWindowSignCert.root_table (hi_rcm_new w).
  Proof. reflexivity. Qed.

  Lemma t_civkr_leg_eq (w : HonestInput) :
    t_civkr_leg (tables_of w) =
    leg_of (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      CommitIvkRWindowSignCert.root_table (hi_rivk w).
  Proof. reflexivity. Qed.

  (** The nullifier leg's shape.  The right-hand side keeps the deep scalar
      as the [t_nullifier_scalar] projection while the left-hand side inlines
      it; a bare [reflexivity] makes the tactic unifier reduce across that
      mismatch and normalise the Poseidon round chain (the [3^36] trap, see
      [docs/compile-performance.md]).  Reduce only the record builder and its
      two projections — leaving [leg_of], [List.nth] and [pose_states_of]
      folded — so both sides become the identical stuck term. *)
  Lemma t_nk_leg_shape (w : HonestInput) :
    t_nk_leg (tables_of w) =
    leg_of OrchardAdvicePoseidonNullifier.nk_table
      NullifierKWindowSignCert.root_table (t_nullifier_scalar (tables_of w)).
  Proof.
    cbn [tables_of t_nk_leg t_nullifier_scalar].
    reflexivity.
  Qed.

  Lemma t_sa_comm_eq (w : HonestInput) :
    t_sa_comm (tables_of w) =
    EccSpec.point_add (leg_pt (t_sa_leg (tables_of w)) 84%nat)
      (leg_acc (t_sa_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_vcr_pt_eq (w : HonestInput) :
    t_vcr_pt (tables_of w) =
    EccSpec.point_add (leg_pt (t_vcr_leg (tables_of w)) 84%nat)
      (leg_acc (t_vcr_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_vcv_mul_eq (w : HonestInput) :
    t_vcv_mul (tables_of w) =
    EccSpec.point_add (leg_pt (t_vcv_leg (tables_of w)) 21%nat)
      (leg_acc (t_vcv_leg (tables_of w)) 20%nat).
  Proof. reflexivity. Qed.

  Lemma t_nk_prod_eq (w : HonestInput) :
    t_nk_prod (tables_of w) =
    EccSpec.point_add (leg_pt (t_nk_leg (tables_of w)) 84%nat)
      (leg_acc (t_nk_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_civkr_pt_eq (w : HonestInput) :
    t_civkr_pt (tables_of w) =
    EccSpec.point_add (leg_pt (t_civkr_leg (tables_of w)) 84%nat)
      (leg_acc (t_civkr_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_nco_pt_eq (w : HonestInput) :
    t_nco_pt (tables_of w) =
    EccSpec.point_add (leg_pt (t_nco_leg (tables_of w)) 84%nat)
      (leg_acc (t_nco_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_ncn_pt_eq (w : HonestInput) :
    t_ncn_pt (tables_of w) =
    EccSpec.point_add (leg_pt (t_ncn_leg (tables_of w)) 84%nat)
      (leg_acc (t_ncn_leg (tables_of w)) 83%nat).
  Proof. reflexivity. Qed.

  Lemma t_rk_pt_eq (w : HonestInput) :
    t_rk_pt (tables_of w) =
    EccSpec.point_add (t_sa_comm (tables_of w)) (hi_ak w).
  Proof. reflexivity. Qed.

  Lemma t_nc_old_hash_eq (w : HonestInput) :
    t_nc_old_hash (tables_of w) =
    hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
      (OrchardAdviceMerkleSinsemilla.split_pieces
        OrchardAdviceMerkleSinsemilla.note_commit_lens
        (note_commit_old_words w)).
  Proof. reflexivity. Qed.

  (** The right-hand side keeps the old-note hash as the [t_nc_old_hash]
      projection while the left-hand side inlines the Sinsemilla fold; a bare
      [reflexivity] makes the unifier unfold [point_add] over that fold (see
      [docs/compile-performance.md]).  Reduce only the record builder and its
      projections so both sides become the identical stuck term. *)
  Lemma t_cm_old_eq (w : HonestInput) :
    t_cm_old (tables_of w) =
    EccSpec.point_add (hd_out (t_nc_old_hash (tables_of w)))
      (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)).
  Proof.
    cbn [tables_of t_cm_old t_nc_old_hash].
    reflexivity.
  Qed.

  Lemma t_civk_hash_eq (w : HonestInput) :
    t_civk_hash (tables_of w) =
    hash_data_of OrchardAdviceMerkleSinsemilla.commit_ivk_Q
      (OrchardAdviceMerkleSinsemilla.split_pieces
        OrchardAdviceMerkleSinsemilla.commit_ivk_lens
        (commit_ivk_words w)).
  Proof. reflexivity. Qed.

  Lemma t_ivk_eq_ivk (w : HonestInput) : t_ivk (tables_of w) = ivk w.
  Proof.
    assert (Hshape : t_ivk (tables_of w) =
      EccSpec.extract_x
        (EccSpec.point_add (hd_out (t_civk_hash (tables_of w)))
          (OrchardProtocolSpec.mul_commit_ivk_r (hi_rivk w))))
      by (cbn [tables_of t_ivk t_civk_hash]; reflexivity).
    rewrite Hshape, t_civk_hash_eq, hd_out_hash_data.
    unfold commit_ivk_words.
    rewrite commit_ivk_words_concat.
    (* Align the Sinsemilla domain-point spelling on both sides before
       [reflexivity]: comparing two [sinsemilla_hash_to_point] applications
       whose [Q] arguments differ syntactically forces the 109-step fold
       (see [docs/compile-performance.md]).  [commit_ivk_Q] is definitionally
       [commit_ivk_q orchard_circuit_params], the spelling [ivk] uses. *)
    unfold ivk, OrchardProtocolSpec.commit_ivk,
      OrchardAdviceMerkleSinsemilla.commit_ivk_Q.
    reflexivity.
  Qed.

  (** Both variable-base read-offs keep the [Commit^ivk] scalar as the [t_ivk]
      projection over a Sinsemilla-derived value; reduce the record builder
      and its projections so the enclosing [Pallas.mul] / [vb_columns] stays
      folded and both sides coincide syntactically. *)
  Lemma t_vb_result_eq (w : HonestInput) :
    t_vb_result (tables_of w) =
    PallasModel.repr
      (Pallas.mul (t_ivk (tables_of w))
        (PallasModel.unrepr (hi_g_d_old w))).
  Proof.
    cbn [tables_of t_vb_result t_ivk].
    reflexivity.
  Qed.

  Lemma t_vb_eq (w : HonestInput) :
    t_vb (tables_of w) =
    OrchardVarBaseTables.vb_columns (t_ivk (tables_of w)) (hi_g_d_old w).
  Proof.
    cbn [tables_of t_vb t_ivk].
    reflexivity.
  Qed.

  (** ** The fixed-base leg: structure of [leg_of]

      [leg_pts]/[leg_accs] name the window-point and accumulator lists of
      [leg_of] (the field equations are definitional), and the [nth]
      lemmas below read individual entries back as window points and
      incomplete-addition folds. *)

  Import FixedBaseLadder.
  Import ProtocolMulCore.

  Definition leg_pts (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) : list Point.t :=
    List.map
      (fun i =>
        EccSpec.fixed_window_point
          (List.nth i tbl OrchardAdviceEccMuls.dummy_window)
          (EccSpec.window_digit k i)
          (List.nth i (roots_us roots k (List.length tbl)) 0))
      (List.seq 0%nat (List.length tbl)).

  Definition leg_accs (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) : list Point.t :=
    match leg_pts tbl roots k with
    | [] => []
    | p0 :: ps => p0 :: accs_go p0 ps
    end.

  Lemma lg_px_eq (tbl : EccSpec.fixed_table) (roots : list (list Z)) (k : Z) :
    lg_px (leg_of tbl roots k) = List.map Point.x (leg_pts tbl roots k).
  Proof. reflexivity. Qed.

  Lemma lg_py_eq (tbl : EccSpec.fixed_table) (roots : list (list Z)) (k : Z) :
    lg_py (leg_of tbl roots k) = List.map Point.y (leg_pts tbl roots k).
  Proof. reflexivity. Qed.

  Lemma lg_ax_eq (tbl : EccSpec.fixed_table) (roots : list (list Z)) (k : Z) :
    lg_ax (leg_of tbl roots k) = List.map Point.x (leg_accs tbl roots k).
  Proof. reflexivity. Qed.

  Lemma lg_ay_eq (tbl : EccSpec.fixed_table) (roots : list (list Z)) (k : Z) :
    lg_ay (leg_of tbl roots k) = List.map Point.y (leg_accs tbl roots k).
  Proof. reflexivity. Qed.

  Lemma leg_pts_length (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) :
    List.length (leg_pts tbl roots k) = List.length tbl.
  Proof.
    unfold leg_pts.
    rewrite List.length_map, List.length_seq.
    reflexivity.
  Qed.

  Lemma leg_pts_nth (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) (i : nat) (Hi : (i < List.length tbl)%nat) :
    List.nth i (leg_pts tbl roots k) point0 =
    EccSpec.fixed_window_point
      (List.nth i tbl OrchardAdviceEccMuls.dummy_window)
      (EccSpec.window_digit k i)
      (List.nth (Z.to_nat (EccSpec.window_digit k i)) (List.nth i roots []) 0).
  Proof.
    unfold leg_pts.
    rewrite (nth_map_seq _ (List.length tbl) i point0 Hi).
    unfold roots_us.
    rewrite (nth_map_seq _ (List.length tbl) i 0 Hi).
    reflexivity.
  Qed.

  Lemma leg_pt_nth (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) (i : nat) :
    leg_pt (leg_of tbl roots k) i = List.nth i (leg_pts tbl roots k) point0.
  Proof.
    unfold leg_pt.
    apply point_eq; cbn [Point.x Point.y].
    - rewrite lg_px_eq. exact (List.map_nth Point.x _ point0 i).
    - rewrite lg_py_eq. exact (List.map_nth Point.y _ point0 i).
  Qed.

  Lemma leg_acc_nth (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) (j : nat) :
    leg_acc (leg_of tbl roots k) j = List.nth j (leg_accs tbl roots k) point0.
  Proof.
    unfold leg_acc.
    apply point_eq; cbn [Point.x Point.y].
    - rewrite lg_ax_eq. exact (List.map_nth Point.x _ point0 j).
    - rewrite lg_ay_eq. exact (List.map_nth Point.y _ point0 j).
  Qed.

  Lemma accs_go_nth :
    forall (ps : list Point.t) (prev : Point.t) (j : nat),
      (j < List.length ps)%nat ->
      List.nth j (accs_go prev ps) point0 =
      EccSpec.point_add_incomplete (List.nth j ps point0)
        (match j with
         | O => prev
         | S j' => List.nth j' (accs_go prev ps) point0
         end).
  Proof.
    induction ps as [| p ps IH]; intros prev j Hj.
    - cbn [List.length] in Hj. lia.
    - cbn [accs_go].
      destruct j as [| j'].
      + reflexivity.
      + cbn [List.nth].
        rewrite (IH _ j' ltac:(cbn [List.length] in Hj; lia)).
        destruct j' as [| j'']; reflexivity.
  Qed.

  Lemma leg_acc_zero (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) (Hlen : (0 < List.length tbl)%nat) :
    leg_acc (leg_of tbl roots k) 0 = leg_pt (leg_of tbl roots k) 0.
  Proof.
    rewrite leg_acc_nth, leg_pt_nth.
    unfold leg_accs.
    pose proof (leg_pts_length tbl roots k) as Hl.
    destruct (leg_pts tbl roots k) as [| p0 ps].
    - cbn [List.length] in Hl. lia.
    - reflexivity.
  Qed.

  Lemma leg_acc_step (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (k : Z) (j : nat)
      (H0 : (0 < j)%nat) (Hj : (j < List.length tbl)%nat) :
    leg_acc (leg_of tbl roots k) j =
    EccSpec.point_add_incomplete (leg_pt (leg_of tbl roots k) j)
      (leg_acc (leg_of tbl roots k) (Nat.pred j)).
  Proof.
    rewrite !leg_acc_nth, leg_pt_nth.
    unfold leg_accs.
    pose proof (leg_pts_length tbl roots k) as Hl.
    destruct (leg_pts tbl roots k) as [| p0 ps].
    - cbn [List.length] in Hl. lia.
    - cbn [List.length] in Hl.
      destruct j as [| j']; [lia |].
      cbn [List.nth Nat.pred].
      rewrite (accs_go_nth ps p0 j' ltac:(lia)).
      destruct j' as [| j'']; reflexivity.
  Qed.

  (** The bundled per-leg facts the ecc-add rows consume: every window
      point and (non-final) accumulator is a good curve point, and every
      interior accumulator entry is a genuinely non-vertical incomplete
      addition of the previous one with the row's window point. *)
  Definition leg_ok (l : leg_data) (nw : nat) : Prop :=
    (forall i : nat, (i < nw)%nat -> wgood (leg_pt l i)) /\
    (forall j : nat, (S j < nw)%nat -> wgood (leg_acc l j)) /\
    (forall j : nat,
      (0 < j)%nat -> (S j < nw)%nat ->
      leg_acc l j =
        EccSpec.point_add_incomplete (leg_pt l j) (leg_acc l (Nat.pred j)) /\
      UnOp.from
        (Point.x (leg_pt l j) -F Point.x (leg_acc l (Nat.pred j))) <> 0).

  (** ** The generic windowed-ladder argument

      Over an abstract prime-order base [G] and an [n]-window table whose
      Lagrange x-interpolation and pasted square roots are certified
      against the multiples of [G] ([Hx_bridge] / [Hroot_bridge]), every
      [leg_of] window point is the [repr] of its window-scalar multiple,
      the accumulator chain is the [repr] of the cumulative multiples, and
      the interior chords are non-vertical ([FixedBaseLadder]'s signed
      radix-8 range bound plus injectivity of [mul] modulo the prime
      order). *)
  Section LegLadder.
    Variable G : Pallas.point.
    Hypothesis HGoc : Pallas.on_curve G.
    Hypothesis HGred : Pallas.reduced G.
    Hypothesis HGne : G <> Pallas.identity.
    Hypothesis HGord : Pallas.mul Pallas.pallas_q G = Pallas.identity.
    Variable n : nat.
    Hypothesis Hn2 : (2 <= n)%nat.
    Hypothesis Hn85 : (n <= 85)%nat.
    Variable tbl : EccSpec.fixed_table.
    Hypothesis Htlen : List.length tbl = n.
    Variable roots : list (list Z).
    Hypothesis Hx_bridge :
      forall (wi : nat) (d u : Z),
        (wi < n)%nat -> 0 <= d < 8 ->
        Point.x
          (EccSpec.fixed_window_point
            (List.nth wi tbl OrchardActionFixedBase.fixed_window_default) d u) =
        Point.x (PallasModel.repr (Pallas.mul (window_scalar n wi d) G)).
    Hypothesis Hroot_bridge :
      forall (wi : nat) (d : Z),
        (wi < n)%nat -> 0 <= d < 8 ->
        List.nth (Z.to_nat d) (List.nth wi roots []) 0 *F
          List.nth (Z.to_nat d) (List.nth wi roots []) 0 =
        UnOp.from
          (EccSpec.fw_z
            (List.nth wi tbl OrchardActionFixedBase.fixed_window_default) +F
           Point.y (PallasModel.repr (Pallas.mul (window_scalar n wi d) G))).
    Variable k : Z.

    Lemma ladder_window_repr (wi : nat) (Hwi : (wi < n)%nat) :
      leg_pt (leg_of tbl roots k) wi =
      PallasModel.repr
        (Pallas.mul (window_scalar n wi (EccSpec.window_digit k wi)) G).
    Proof using All.
      rewrite leg_pt_nth, (leg_pts_nth tbl roots k wi ltac:(lia)).
      assert (Hnth : List.nth wi tbl OrchardAdviceEccMuls.dummy_window =
        List.nth wi tbl OrchardActionFixedBase.fixed_window_default)
        by (apply List.nth_indep; lia).
      rewrite Hnth.
      pose proof (window_digit_bound k wi) as Hd.
      apply point_eq.
      - apply Hx_bridge; [exact Hwi | exact Hd].
      - cbn [EccSpec.fixed_window_point Point.y].
        rewrite (Hroot_bridge wi (EccSpec.window_digit k wi) Hwi Hd).
        rewrite from_add_comm, from_add_sub_r.
        apply repr_y_reduced.
        apply pallas_mul_reduced; exact HGred.
    Qed.

    Lemma ladder_ks_pos (m : nat) (Hm : (S m < n)%nat) :
      0 < window_scalar n m (EccSpec.window_digit k m) < Pallas.pallas_q.
    Proof using All.
      rewrite (window_scalar_nonlast_gen n m _ ltac:(lia)).
      pose proof (window_digit_bound k m) as Hd.
      pose proof pow8_83_lt_pallas_q as Hq.
      assert (H1 : 1 <= 8 ^ Z.of_nat m)
        by (replace 1 with (8 ^ 0) by reflexivity;
            apply Z.pow_le_mono_r; lia).
      assert (H2 : 8 ^ Z.of_nat m <= 8 ^ 83)
        by (apply Z.pow_le_mono_r; lia).
      nia.
    Qed.

    Lemma ladder_psum_pos (m : nat)
        (Hm1 : (0 < m)%nat) (Hm : (S m < n)%nat) :
      0 < cumulative_scalar n k m < Pallas.pallas_q.
    Proof using All.
      assert (Hpos : forall m0 : nat,
        (0 < m0)%nat -> (m0 < n)%nat -> 0 < cumulative_scalar n k m0).
      { induction m0 as [| m0 IH]; intros Ha Hb; [lia |].
        rewrite cumulative_scalar_succ_gen.
        pose proof (ladder_ks_pos m0 ltac:(lia)) as Hk0.
        destruct m0 as [| m1].
        - cbn [cumulative_scalar partial_sum]. lia.
        - pose proof (IH ltac:(lia) ltac:(lia)). lia. }
      split.
      - apply Hpos; lia.
      - destruct (partial_sum_window_bound n
          (fun wi => EccSpec.window_digit k wi)
          (fun wi _ => window_digit_bound k wi) m ltac:(lia)) as [HS0 HS7].
        cbn beta in HS0, HS7.
        pose proof pow8_83_lt_pallas_q as Hq.
        assert (H2 : 8 ^ Z.of_nat m <= 8 ^ 83)
          by (apply Z.pow_le_mono_r; lia).
        unfold cumulative_scalar.
        lia.
    Qed.

    Lemma ladder_repr_affine (a : Z) (Ha : a mod Pallas.pallas_q <> 0) :
      pt_affine_ok (PallasModel.repr (Pallas.mul a G)).
    Proof using All.
      apply repr_affine_of_ne.
      - apply pallas_mul_reduced; exact HGred.
      - apply pallas_mul_on_curve; exact HGoc.
      - intro He.
        apply Ha.
        assert (Heq : Pallas.mul a G = Pallas.mul Pallas.pallas_q G)
          by (rewrite HGord; exact He).
        pose proof (proj1 (Weierstrass.mul_injective_mod Pallas.a Pallas.b
          G Pallas.pallas_q pallas_11_lt Pallas.nonsingular HGred HGoc HGne
          Pallas.pallas_q_is_prime HGord a Pallas.pallas_q) Heq) as Hm.
        rewrite Z_mod_same_full in Hm.
        exact Hm.
    Qed.

    Lemma ladder_acc_repr :
      forall j : nat,
        (S j < n)%nat ->
        leg_acc (leg_of tbl roots k) j =
        PallasModel.repr (Pallas.mul (cumulative_scalar n k (S j)) G).
    Proof using All.
      induction j as [| j IH]; intro Hj.
      - rewrite (leg_acc_zero tbl roots k ltac:(lia)).
        rewrite (ladder_window_repr 0%nat ltac:(lia)).
        apply (f_equal PallasModel.repr), mul_scalar_eq.
        cbn [cumulative_scalar partial_sum].
        lia.
      - rewrite (leg_acc_step tbl roots k (S j) ltac:(lia) ltac:(lia)).
        cbn [Nat.pred].
        rewrite (ladder_window_repr (S j) ltac:(lia)).
        rewrite (IH ltac:(lia)).
        pose proof (window_scalar_range_bound n
          (fun wi => EccSpec.window_digit k wi)
          (fun wi _ => window_digit_bound k wi) Hn85 (S j)
          ltac:(lia) ltac:(lia)) as [Hr1 Hr2].
        cbn beta in Hr1, Hr2.
        assert (Hij :
          window_scalar n (S j) (EccSpec.window_digit k (S j))
            mod Pallas.pallas_q <>
          cumulative_scalar n k (S j) mod Pallas.pallas_q) by exact Hr1.
        assert (Hijn :
          window_scalar n (S j) (EccSpec.window_digit k (S j))
            mod Pallas.pallas_q <>
          (- cumulative_scalar n k (S j)) mod Pallas.pallas_q) by exact Hr2.
        pose proof (mul_x_neq G _ _ HGoc HGred HGne HGord Hij Hijn) as Hdist.
        pose proof (ladder_repr_affine
          (window_scalar n (S j) (EccSpec.window_digit k (S j)))
          ltac:(pose proof (ladder_ks_pos (S j) ltac:(lia));
                rewrite Z.mod_small by lia; lia)) as HPaff.
        pose proof (ladder_repr_affine (cumulative_scalar n k (S j))
          ltac:(pose proof (ladder_psum_pos (S j) ltac:(lia) ltac:(lia));
                rewrite Z.mod_small by lia; lia)) as HQaff.
        rewrite (OrchardActionFixedBase.point_add_incomplete_eq_point_add_swap
          _ _ (pt_affine_x_nonzero _ HPaff) (pt_affine_x_nonzero _ HQaff)
          Hdist).
        rewrite <- (pallas_repr_add _ _
          (pallas_mul_reduced _ G HGred) (pallas_mul_reduced _ G HGred)
          (pallas_mul_on_curve _ G HGoc) (pallas_mul_on_curve _ G HGoc)).
        rewrite <- (pallas_mul_add _ _ G HGred HGoc).
        apply (f_equal PallasModel.repr), mul_scalar_eq.
        (* Expand the accumulator on the right ([S (S j)]) — the unqualified
           [rewrite] would hit the [S j] occurrence on the left and leave an
           unprovable goal.  The result is [c + w = c + w], closed by [ring]
           (which ignores the [mod Pallas.pallas_q] hypotheses that make [lia]
           diverge here). *)
        rewrite (cumulative_scalar_succ_gen n k (S j)).
        ring.
    Qed.

    Lemma ladder_chord (j : nat)
        (H0 : (0 < j)%nat) (Hj : (S j < n)%nat) :
      UnOp.from
        (Point.x (leg_pt (leg_of tbl roots k) j) -F
         Point.x (leg_acc (leg_of tbl roots k) (Nat.pred j))) <> 0.
    Proof using All.
      destruct j as [| j']; [lia |].
      cbn [Nat.pred].
      rewrite (ladder_window_repr (S j') ltac:(lia)).
      rewrite (ladder_acc_repr j' ltac:(lia)).
      pose proof (window_scalar_range_bound n
        (fun wi => EccSpec.window_digit k wi)
        (fun wi _ => window_digit_bound k wi) Hn85 (S j')
        ltac:(lia) ltac:(lia)) as [Hr1 Hr2].
      cbn beta in Hr1, Hr2.
      pose proof (mul_x_neq G
        (window_scalar n (S j') (EccSpec.window_digit k (S j')))
        (cumulative_scalar n k (S j'))
        HGoc HGred HGne HGord Hr1 Hr2) as Hdist.
      intro Hc.
      rewrite from_sub_reduced in Hc.
      apply (proj1 (sub_zero_equiv _ _)) in Hc.
      exact (Hdist Hc).
    Qed.

    Lemma ladder_leg_ok : leg_ok (leg_of tbl roots k) n.
    Proof using All.
      split; [| split].
      - intros i Hi.
        rewrite (ladder_window_repr i Hi).
        apply wgood_repr_mul; assumption.
      - intros j Hj.
        rewrite (ladder_acc_repr j Hj).
        apply wgood_repr_mul; assumption.
      - intros j H0 Hj.
        split.
        + apply (leg_acc_step tbl roots k j H0 ltac:(lia)).
        + exact (ladder_chord j H0 Hj).
    Qed.
  End LegLadder.

  (** ** Per-base window counts *)

  Lemma sa_tbl_len : List.length OrchardAdviceEccMuls.tbl_spend_auth = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma vcr_tbl_len :
    List.length OrchardAdviceEccMuls.tbl_value_commit_r = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma vcv_tbl_len :
    List.length OrchardAdviceEccMuls.tbl_value_commit_v = 22%nat.
  Proof. vm_cast_no_check (@eq_refl nat 22%nat). Qed.

  Lemma ncr_tbl_len :
    List.length OrchardAdviceEccMuls.tbl_note_commit_r = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma nk_tbl_len :
    List.length OrchardAdvicePoseidonNullifier.nk_table = 85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  Lemma civkr_tbl_len :
    List.length (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) =
    85%nat.
  Proof. vm_cast_no_check (@eq_refl nat 85%nat). Qed.

  (** ** Per-base pasted-root bridges

      Each window-sign certificate's [root_check_true] pins the pasted
      root's square to [fw_z + y] of the certificate table entry; the
      per-base table-entry bridges rewrite that entry as the Weierstrass
      multiple. *)

  Lemma sa_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi SpendAuthGWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi SpendAuthGWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi OrchardAdviceEccMuls.tbl_spend_auth
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 85 wi d)
             PallasGenerators.spend_auth_g_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 85)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn SpendAuthGWindowSignCert.table
        SpendAuthGWindowSignCert.default SpendAuthGFullTable.full_table_reduced
        SpendAuthGWindowSignCert.root_table)
      (List.seq 0 85) (List.seq 0 8) wi (Z.to_nat d)
      SpendAuthGWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- SpendAuthGFullTable.full_table_reduced_eq in Hr.
    rewrite (full_table_entry_eq_mul wi d Hw Hd) in Hr.
    unfold SpendAuthGWindowSignCert.table, SpendAuthGWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  Lemma vcr_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi ValueCommitRWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi ValueCommitRWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi OrchardAdviceEccMuls.tbl_value_commit_r
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 85 wi d)
             PallasGenerators.value_commit_r_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 85)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn ValueCommitRWindowSignCert.table
        ValueCommitRWindowSignCert.default
        ValueCommitRFullTable.full_table_reduced
        ValueCommitRWindowSignCert.root_table)
      (List.seq 0 85) (List.seq 0 8) wi (Z.to_nat d)
      ValueCommitRWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- ValueCommitRFullTable.full_table_reduced_eq in Hr.
    rewrite (ValueCommitRLadder.value_commit_r_full_table_entry_eq_mul
      wi d Hw Hd) in Hr.
    unfold ValueCommitRWindowSignCert.table, ValueCommitRWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  Lemma vcv_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 22)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi ValueCommitVWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi ValueCommitVWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi OrchardAdviceEccMuls.tbl_value_commit_v
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 22 wi d)
             PallasGenerators.value_commit_v_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 22)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn ValueCommitVWindowSignCert.table
        ValueCommitVWindowSignCert.default
        ValueCommitVFullTable.full_table_reduced
        ValueCommitVWindowSignCert.root_table)
      (List.seq 0 22) (List.seq 0 8) wi (Z.to_nat d)
      ValueCommitVWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- ValueCommitVFullTable.full_table_reduced_eq in Hr.
    rewrite (ValueCommitVLadder.value_commit_v_full_table_entry_eq_mul
      wi d Hw Hd) in Hr.
    unfold ValueCommitVWindowSignCert.table, ValueCommitVWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  Lemma nk_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi NullifierKWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi NullifierKWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi OrchardAdvicePoseidonNullifier.nk_table
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 85 wi d)
             PallasGenerators.nullifier_k_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 85)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn NullifierKWindowSignCert.table
        NullifierKWindowSignCert.default
        NullifierKFullTable.full_table_reduced
        NullifierKWindowSignCert.root_table)
      (List.seq 0 85) (List.seq 0 8) wi (Z.to_nat d)
      NullifierKWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- NullifierKFullTable.full_table_reduced_eq in Hr.
    rewrite (NullifierKLadder.nullifier_k_full_table_entry_eq_mul
      wi d Hw Hd) in Hr.
    unfold NullifierKWindowSignCert.table, NullifierKWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  Lemma ncr_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi NoteCommitRWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi NoteCommitRWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi OrchardAdviceEccMuls.tbl_note_commit_r
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 85 wi d)
             PallasGenerators.note_commit_r_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 85)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn NoteCommitRWindowSignCert.table
        NoteCommitRWindowSignCert.default
        NoteCommitRFullTable.full_table_reduced
        NoteCommitRWindowSignCert.root_table)
      (List.seq 0 85) (List.seq 0 8) wi (Z.to_nat d)
      NoteCommitRWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- NoteCommitRFullTable.full_table_reduced_eq in Hr.
    rewrite (NoteCommitRLadder.note_commit_r_full_table_entry_eq_mul
      wi d Hw Hd) in Hr.
    unfold NoteCommitRWindowSignCert.table, NoteCommitRWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  (** The CommitIvkR table-entry bridge (the other bases' analogues live in
      their ladder files). *)
  Lemma civkr_entry_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi CommitIvkRFullTable.full_table []) Pallas.identity =
    Pallas.mul (window_scalar 85 wi d) PallasGenerators.commit_ivk_r_G.
  Proof.
    unfold CommitIvkRFullTable.full_table, CommitIvkRFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced 84 wi d Hw Hd).
  Qed.

  Lemma civkr_root_bridge (wi : nat) (d : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth wi CommitIvkRWindowSignCert.root_table []) 0 *F
      List.nth (Z.to_nat d)
        (List.nth wi CommitIvkRWindowSignCert.root_table []) 0 =
    UnOp.from
      (EccSpec.fw_z
        (List.nth wi (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) +F
       Point.y
         (PallasModel.repr
           (Pallas.mul (window_scalar 85 wi d)
             PallasGenerators.commit_ivk_r_G))).
  Proof.
    assert (Hin_w : List.In wi (List.seq 0 85)) by (apply List.in_seq; lia).
    assert (Hin_i : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (forallb_nested_entry
      (FixedBaseSignCert.root_check_fn CommitIvkRWindowSignCert.table
        CommitIvkRWindowSignCert.default
        CommitIvkRFullTable.full_table_reduced
        CommitIvkRWindowSignCert.root_table)
      (List.seq 0 85) (List.seq 0 8) wi (Z.to_nat d)
      CommitIvkRWindowSignCert.root_check_true Hin_w Hin_i) as Hr.
    unfold FixedBaseSignCert.root_check_fn, FixedBaseSignCert.root in Hr.
    apply Z.eqb_eq in Hr.
    rewrite <- CommitIvkRFullTable.full_table_reduced_eq in Hr.
    rewrite (civkr_entry_bridge wi d Hw Hd) in Hr.
    unfold CommitIvkRWindowSignCert.table, CommitIvkRWindowSignCert.default
      in Hr.
    exact Hr.
  Qed.

  (** The CommitIvkR Lagrange x-coordinate bridge. *)
  Lemma civkr_x_bridge (wi : nat) (d u : Z)
      (Hw : (wi < 85)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth wi (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 wi d) PallasGenerators.commit_ivk_r_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced 84
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      _ wi d u Hw Hd).
    exact CommitIvkRMulProtocol.commit_ivk_r_x_cert_hook.
  Qed.

  (** ** The six per-leg fact bundles *)

  Lemma sa_leg_facts (k : Z) :
    leg_ok
      (leg_of OrchardAdviceEccMuls.tbl_spend_auth
        SpendAuthGWindowSignCert.root_table k) 85%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.spend_auth_g_G
      PallasGenerators.spend_auth_g_on_curve
      PallasGenerators.spend_auth_g_reduced
      PallasGenerators.spend_auth_g_ne_identity
      PallasGeneratorsOrder.spend_auth_g_order
      85%nat ltac:(lia) ltac:(lia)
      OrchardAdviceEccMuls.tbl_spend_auth sa_tbl_len
      SpendAuthGWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (spend_auth_g_fixed_window_point_x_eq_mul wi d u Hwi Hd).
    - exact sa_root_bridge.
  Qed.

  Lemma vcr_leg_facts (k : Z) :
    leg_ok
      (leg_of OrchardAdviceEccMuls.tbl_value_commit_r
        ValueCommitRWindowSignCert.root_table k) 85%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.value_commit_r_G
      PallasGenerators.value_commit_r_on_curve
      PallasGenerators.value_commit_r_reduced
      PallasGenerators.value_commit_r_ne_identity
      PallasGeneratorsOrder.value_commit_r_order
      85%nat ltac:(lia) ltac:(lia)
      OrchardAdviceEccMuls.tbl_value_commit_r vcr_tbl_len
      ValueCommitRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (ValueCommitRLadder.value_commit_r_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact vcr_root_bridge.
  Qed.

  Lemma vcv_leg_facts (k : Z) :
    leg_ok
      (leg_of OrchardAdviceEccMuls.tbl_value_commit_v
        ValueCommitVWindowSignCert.root_table k) 22%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_on_curve
      PallasGenerators.value_commit_v_reduced
      PallasGenerators.value_commit_v_ne_identity
      PallasGeneratorsOrder.value_commit_v_order
      22%nat ltac:(lia) ltac:(lia)
      OrchardAdviceEccMuls.tbl_value_commit_v vcv_tbl_len
      ValueCommitVWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (ValueCommitVLadder.value_commit_v_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact vcv_root_bridge.
  Qed.

  Lemma nk_leg_facts (k : Z) :
    leg_ok
      (leg_of OrchardAdvicePoseidonNullifier.nk_table
        NullifierKWindowSignCert.root_table k) 85%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.nullifier_k_G
      PallasGenerators.nullifier_k_on_curve
      PallasGenerators.nullifier_k_reduced
      PallasGenerators.nullifier_k_ne_identity
      PallasGeneratorsOrder.nullifier_k_order
      85%nat ltac:(lia) ltac:(lia)
      OrchardAdvicePoseidonNullifier.nk_table nk_tbl_len
      NullifierKWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (NullifierKLadder.nullifier_k_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact nk_root_bridge.
  Qed.

  Lemma ncr_leg_facts (k : Z) :
    leg_ok
      (leg_of OrchardAdviceEccMuls.tbl_note_commit_r
        NoteCommitRWindowSignCert.root_table k) 85%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      PallasGenerators.note_commit_r_ne_identity
      PallasGeneratorsOrder.note_commit_r_order
      85%nat ltac:(lia) ltac:(lia)
      OrchardAdviceEccMuls.tbl_note_commit_r ncr_tbl_len
      NoteCommitRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (NoteCommitRLadder.note_commit_r_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact ncr_root_bridge.
  Qed.

  Lemma civkr_leg_facts (k : Z) :
    leg_ok
      (leg_of (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        CommitIvkRWindowSignCert.root_table k) 85%nat.
  Proof.
    apply (ladder_leg_ok PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced
      PallasGenerators.commit_ivk_r_ne_identity
      PallasGeneratorsOrder.commit_ivk_r_order
      85%nat ltac:(lia) ltac:(lia)
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) civkr_tbl_len
      CommitIvkRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (civkr_x_bridge wi d u Hwi Hd).
    - exact civkr_root_bridge.
  Qed.

  (** ** The nullifier scalar and the new note's [ρ]

      The hoisted Poseidon schedule's row-36 lane is the PRF output
      ([poseidon_round_state_hash2] over the [states_go] read-back), so the
      table record's nullifier scalar, old commitment and new-note [ρ] are
      the specification values. *)

  Lemma states_go_last :
    forall (count row : nat) (s : State.t),
      List.nth count (states_go s row count) state0 =
      Stdlib.Lists.List.fold_left (fun t r => poseidon_round r t)
        (List.seq row count) s.
  Proof.
    induction count as [| c IH]; intros row s.
    - reflexivity.
    - cbn [states_go List.nth List.seq Stdlib.Lists.List.fold_left].
      apply IH.
  Qed.

  (** Route the concrete 36-row read-back through [poseidon_state] at an
      ABSTRACT length: the fold over [List.seq 0 n] is stuck, so the two
      spellings align structurally.  Converting the two spellings at the
      concrete count instead normalizes the 36-round chain (the [3^36] trap of
      docs/compile-performance.md). *)
  Lemma states_go_poseidon_state (s : State.t) (n : nat) :
    List.nth n (states_go s 0%nat n) state0 = poseidon_state s n.
  Proof.
    rewrite (states_go_last n 0%nat s).
    unfold poseidon_state.
    reflexivity.
  Qed.

  (** The Poseidon schedule iterate is opaque to the kernel from here on, so a
      conversion between [poseidon_round_state w 36] and
      [poseidon_state (poseidon_input_state w) 36] matches through the single
      [poseidon_round_state] delta rather than reducing either 36-round chain
      (docs/compile-performance.md). *)
  #[local] Opaque poseidon_state.

  Lemma t_hash2_eq (w : HonestInput) :
    t_hash2 (tables_of w) =
    Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w).
  Proof.
    assert (Hshape : t_hash2 (tables_of w) =
      State.x0 (List.nth 36 (pose_states_of w) state0)) by reflexivity.
    rewrite Hshape.
    unfold pose_states_of.
    rewrite (states_go_poseidon_state (poseidon_input_state w) 36%nat).
    exact (poseidon_round_state_hash2 w).
  Qed.

  (** The Poseidon read-back chain is opaque to the conversion oracle from
      here on: every later comparison of a [t_nullifier_scalar]/[t_nk_leg]
      spelling against a hoisted projection would otherwise force
      [List.nth 36 (pose_states_of w) state0] — the 36-round chain — through
      the [State.x0] projection (docs/compile-performance.md).  The lemmas
      above are the only ones that unfold these.  [poseidon_hash2] joins them:
      two identical [poseidon_hash2 (hi_nk w) (hi_rho_old w)] spellings would
      otherwise be compared by normalizing [Poseidon.permute]. *)
  #[local] Opaque pose_states_of states_go Poseidon.poseidon_hash2.

  Lemma t_nullifier_scalar_eq (w : HonestInput) :
    t_nullifier_scalar (tables_of w) = nullifier_scalar w.
  Proof.
    assert (Hshape : t_nullifier_scalar (tables_of w) =
      t_hash2 (tables_of w) +F hi_psi_old w) by reflexivity.
    rewrite Hshape, t_hash2_eq.
    reflexivity.
  Qed.

  Lemma t_cm_old_spec (w : HonestInput) : t_cm_old (tables_of w) = cm_old w.
  Proof.
    rewrite t_cm_old_eq, t_nc_old_hash_eq, hd_out_hash_data.
    unfold note_commit_old_words.
    rewrite note_commit_words_concat.
    (* Align the Sinsemilla domain-point spelling on both sides before
       [reflexivity]: [note_commit_Q] is definitionally
       [note_commit_q orchard_circuit_params], the spelling [cm_old] uses
       (see [docs/compile-performance.md]). *)
    unfold cm_old, OrchardProtocolSpec.note_commit,
      OrchardAdviceMerkleSinsemilla.note_commit_Q.
    reflexivity.
  Qed.

  Lemma t_nf_spec_eq (w : HonestInput) : t_nf_spec (tables_of w) = rho_new w.
  Proof.
    assert (Hshape : t_nf_spec (tables_of w) =
      EccSpec.extract_x
        (EccSpec.point_add
          (OrchardProtocolSpec.mul_nullifier_k
            (t_nullifier_scalar (tables_of w)))
          (t_cm_old (tables_of w))))
      by (cbn [tables_of t_nf_spec t_nullifier_scalar t_cm_old]; reflexivity).
    rewrite Hshape, t_nullifier_scalar_eq, t_cm_old_spec.
    unfold rho_new, nf_old, OrchardProtocolSpec.nullifier, nullifier_scalar.
    reflexivity.
  Qed.

  (** The right-hand side keeps [ρ_new] as the [t_nf_spec] projection while
      the left-hand side inlines the nullifier chain; reduce the record
      builder and its projections so the enclosing [hash_data_of] stays folded
      and both sides coincide syntactically. *)
  Lemma t_nc_new_hash_eq (w : HonestInput) :
    t_nc_new_hash (tables_of w) =
    hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
      (OrchardAdviceMerkleSinsemilla.split_pieces
        OrchardAdviceMerkleSinsemilla.note_commit_lens
        (OrchardSpec.note_commit_message (hi_g_d_new w) (hi_pk_d_new w)
          (hi_v_new w) (t_nf_spec (tables_of w)) (hi_psi_new w))).
  Proof.
    cbn [tables_of t_nc_new_hash t_nf_spec].
    reflexivity.
  Qed.

  (** ** The [ivk] range

      Under the [Commit^ivk] hash nondegeneracy the hash output is affine,
      so the extracted [ivk] is a reduced field element. *)
  Lemma ivk_bound (w : HonestInput)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.commit_ivk_q orchard_circuit_params)
        (commit_ivk_words w)) :
    0 <= ivk w < Primes.pallas_p.
  Proof.
    unfold ivk, OrchardProtocolSpec.commit_ivk.
    unfold commit_ivk_words in Hnd.
    assert (Hh : pt_affine_ok
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.commit_ivk_q orchard_circuit_params)
        (OrchardSpec.commit_ivk_message
          (EccSpec.extract_x (hi_ak w)) (hi_nk w)))).
    { apply hash_affine.
      - exact commit_ivk_q_affine.
      - apply commit_ivk_message_range.
      - exact Hnd. }
    destruct Hh as (_ & Hhx & Hhy).
    unfold OrchardProtocolSpec.mul_commit_ivk_r.
    destruct (repr_coords_reduced
      (Pallas.mul (hi_rivk w) PallasGenerators.commit_ivk_r_G)
      (pallas_mul_reduced _ _ PallasGenerators.commit_ivk_r_reduced))
      as [Hcx Hcy].
    destruct (OrchardActionFixedBase.point_add_reduced _ _
      Hhx Hhy Hcx Hcy) as [Hx _].
    unfold EccSpec.extract_x.
    exact (reduced_bounds _ Hx).
  Qed.

  Lemma mul_scalar_bound (w : HonestInput)
      (Hivk : 0 <= ivk w < Primes.pallas_p) :
    0 <= mul_scalar w < 2 ^ 255.
  Proof.
    unfold mul_scalar.
    assert (Ht : 0 < Primes.t_q) by (vm_compute; reflexivity).
    assert (Hp : Primes.pallas_p + Primes.t_q < 2 ^ 255)
      by (vm_compute; reflexivity).
    lia.
  Qed.

  (** ** The variable-base ladder tracks the specification accumulators

      One [ladder_step] is the double incomplete addition of the signed
      base; on the nondegenerate domain it advances [mul_acc] by one bit
      ([VarBaseDefs.double_add_step_multiple] at the [repr] level), so the
      two [ladder_go] halves land on [mul_acc w 130] and [mul_acc w 4]. *)

  Lemma ladder_step_incomplete (B : Point.t) (bitv : Z) (acc : Point.t) :
    snd (OrchardVarBaseTables.ladder_step B bitv acc) =
    EccSpec.point_add_incomplete acc
      (EccSpec.point_add_incomplete acc
        (OrchardVarBaseTables.signed_pt B bitv)).
  Proof.
    unfold OrchardVarBaseTables.ladder_step, OrchardVarBaseTables.signed_pt,
      point_neg.
    destruct (bitv =? 1); reflexivity.
  Qed.

  Lemma mul_step_point_signed (w : HonestInput) (i : nat) :
    mul_step_point w i =
    OrchardVarBaseTables.signed_pt (hi_g_d_old w)
      (scalar_bit (mul_scalar w) i).
  Proof. reflexivity. Qed.

  Lemma signed_pt_x (B : Point.t) (bitv : Z) :
    Point.x (OrchardVarBaseTables.signed_pt B bitv) = Point.x B.
  Proof.
    unfold OrchardVarBaseTables.signed_pt, point_neg.
    destruct (bitv =? 1); reflexivity.
  Qed.

  Lemma wgood_signed (B : Point.t) (bitv : Z) :
    point_ok B -> wgood (OrchardVarBaseTables.signed_pt B bitv).
  Proof.
    intro H.
    unfold OrchardVarBaseTables.signed_pt.
    destruct (bitv =? 1).
    - exact (wgood_of_point_ok B H).
    - exact (wgood_neg_of_point_ok B H).
  Qed.

  Lemma wgood_lsb (B : Point.t) (bitv : Z) :
    point_ok B -> wgood (OrchardVarBaseTables.lsb_pt B bitv).
  Proof.
    intro H.
    unfold OrchardVarBaseTables.lsb_pt.
    destruct (bitv =? 1).
    - exact wgood_identity.
    - exact (wgood_neg_of_point_ok B H).
  Qed.

  Lemma vb_step_group (w : HonestInput)
      (HB : point_ok (hi_g_d_old w)) (i : nat) (Hi : (i < 255)%nat)
      (Hnd : mul_step_nondegenerate w i) :
    EccSpec.point_add_incomplete (mul_acc w (S i))
      (EccSpec.point_add_incomplete (mul_acc w (S i)) (mul_step_point w i)) =
    mul_acc w i.
  Proof.
    destruct Hnd as (Hx0 & HxB & Hxmid).
    pose proof HB as (HBred & HBoc & HBne).
    set (Bt := PallasModel.unrepr (hi_g_d_old w)) in *.
    assert (HBt : Bt = Weierstrass.Affine (Point.x (hi_g_d_old w))
        (Point.y (hi_g_d_old w))).
    { unfold Bt, PallasModel.unrepr.
      destruct ((Point.x (hi_g_d_old w) =? 0) &&
                (Point.y (hi_g_d_old w) =? 0))%bool eqn:Hb0.
      - exfalso.
        apply Bool.andb_true_iff in Hb0.
        destruct Hb0 as [Hbx Hby].
        apply Z.eqb_eq in Hbx, Hby.
        apply HBne.
        apply point_eq; cbn [EccSpec.identity Point.x Point.y]; assumption.
      - reflexivity. }
    assert (Hbit01 : scalar_bit (mul_scalar w) i = 0 \/
                     scalar_bit (mul_scalar w) i = 1).
    { unfold scalar_bit.
      pose proof (Z.mod_pos_bound (mul_scalar w / 2 ^ Z.of_nat i) 2
        ltac:(lia)) as Hb.
      lia. }
    assert (Hacc : mul_acc w (S i) =
      PallasModel.repr (Pallas.mul (mul_multiple w (S i)) Bt))
      by reflexivity.
    assert (Hacc_ne : Pallas.mul (mul_multiple w (S i)) Bt <>
        Pallas.identity).
    { intro He.
      apply Hx0.
      rewrite Hacc, He.
      reflexivity. }
    assert (Hacc_aff : pt_affine_ok (mul_acc w (S i))).
    { rewrite Hacc.
      apply repr_affine_of_ne.
      - apply pallas_mul_reduced; exact HBred.
      - apply pallas_mul_on_curve; exact HBoc.
      - exact Hacc_ne. }
    assert (Hsp : pt_affine_ok (mul_step_point w i) /\
      mul_step_point w i =
        PallasModel.repr
          (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i)) /\
      Point.x (mul_step_point w i) = Point.x (hi_g_d_old w)).
    { unfold mul_step_point, VarBaseDefs.signed_base.
      destruct Hbit01 as [Hb | Hb]; rewrite Hb; cbn [Z.eqb].
      - split; [| split].
        + apply pt_affine_neg, pt_affine_of_point_ok; exact HB.
        + rewrite HBt. reflexivity.
        + reflexivity.
      - split; [| split].
        + apply pt_affine_of_point_ok; exact HB.
        + symmetry. apply (PallasModel.repr_unrepr (hi_g_d_old w)).
        + reflexivity. }
    destruct Hsp as (Hsp_aff & Hsp_repr & Hsp_x).
    assert (Hsb_red : Pallas.reduced
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))).
    { unfold VarBaseDefs.signed_base.
      destruct (scalar_bit (mul_scalar w) i =? 1).
      - exact HBred.
      - apply VarBaseDefs.pallas_neg_reduced; exact HBred. }
    assert (Hsb_oc : Pallas.on_curve
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))).
    { unfold VarBaseDefs.signed_base.
      destruct (scalar_bit (mul_scalar w) i =? 1).
      - exact HBoc.
      - apply VarBaseDefs.pallas_neg_on_curve; exact HBoc. }
    assert (Hd1 : UnOp.from (Point.x (mul_acc w (S i))) <>
                  UnOp.from (Point.x (mul_step_point w i))).
    { destruct Hacc_aff as (_ & Haccx & _).
      destruct Hsp_aff as (_ & Hspx & _).
      rewrite Haccx, Hspx, Hsp_x.
      exact HxB. }
    assert (Hmid_eq : EccSpec.point_add_incomplete (mul_acc w (S i))
        (mul_step_point w i) =
      EccSpec.point_add (mul_step_point w i) (mul_acc w (S i))).
    { apply OrchardActionFixedBase.point_add_incomplete_eq_point_add_swap.
      - exact (pt_affine_x_nonzero _ Hacc_aff).
      - exact (pt_affine_x_nonzero _ Hsp_aff).
      - exact Hd1. }
    assert (Hmid_aff : pt_affine_ok
      (EccSpec.point_add_incomplete (mul_acc w (S i))
        (mul_step_point w i))).
    { rewrite Hmid_eq.
      pose proof Hacc_aff as (Hacc_c & Hacc_x & Hacc_y).
      pose proof Hsp_aff as (Hsp_c & Hsp_xr & Hsp_y).
      split.
      { exact (EccSpec.point_add_on_curve_x_distinct
          (mul_step_point w i) (mul_acc w (S i)) Hsp_c Hacc_c
          (pt_affine_x_nonzero _ Hsp_aff) (pt_affine_x_nonzero _ Hacc_aff)
          (fun Hc => Hd1 (eq_sym Hc))). }
      exact (OrchardActionFixedBase.point_add_reduced _ _
        Hsp_xr Hsp_y Hacc_x Hacc_y). }
    assert (Hd2 : UnOp.from (Point.x (mul_acc w (S i))) <>
      UnOp.from
        (Point.x (EccSpec.point_add_incomplete (mul_acc w (S i))
          (mul_step_point w i)))).
    { destruct Hmid_aff as (_ & Hmx & _).
      destruct Hacc_aff as (_ & Hax & _).
      rewrite Hmx, Hax.
      intro Hc.
      exact (Hxmid (eq_sym Hc)). }
    rewrite (OrchardActionFixedBase.point_add_incomplete_eq_point_add_swap
      (mul_acc w (S i))
      (EccSpec.point_add_incomplete (mul_acc w (S i)) (mul_step_point w i))
      (pt_affine_x_nonzero _ Hacc_aff) (pt_affine_x_nonzero _ Hmid_aff)
      Hd2).
    rewrite Hmid_eq, Hsp_repr, Hacc.
    rewrite <- (pallas_repr_add _ _ Hsb_red
      (pallas_mul_reduced _ _ HBred) Hsb_oc
      (pallas_mul_on_curve _ _ HBoc)).
    assert (Hadd_red : Pallas.reduced
      (Pallas.add
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))
        (Pallas.mul (mul_multiple w (S i)) Bt))).
    { apply Weierstrass.add_reduced; [exact Hsb_red |].
      apply pallas_mul_reduced; exact HBred. }
    assert (Hadd_oc : Pallas.on_curve
      (Pallas.add
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))
        (Pallas.mul (mul_multiple w (S i)) Bt))).
    { apply Weierstrass.add_on_curve;
        [exact pallas_3_lt | exact Hsb_oc |].
      apply pallas_mul_on_curve; exact HBoc. }
    rewrite <- (pallas_repr_add _ _ Hadd_red
      (pallas_mul_reduced _ _ HBred) Hadd_oc
      (pallas_mul_on_curve _ _ HBoc)).
    assert (Hcomm :
      Pallas.add
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))
        (Pallas.mul (mul_multiple w (S i)) Bt) =
      Pallas.add (Pallas.mul (mul_multiple w (S i)) Bt)
        (VarBaseDefs.signed_base Bt (scalar_bit (mul_scalar w) i))).
    { unfold Pallas.add.
      apply (Weierstrass.add_comm Pallas.a Pallas.b _ _ Hsb_oc
        (pallas_mul_on_curve _ _ HBoc)). }
    rewrite Hcomm.
    rewrite (VarBaseDefs.double_add_step_multiple Bt
      (mul_multiple w (S i)) (scalar_bit (mul_scalar w) i)
      HBred HBoc Hbit01).
    change (mul_acc w i) with
      (PallasModel.repr (Pallas.mul (mul_multiple w i) Bt)).
    apply (f_equal PallasModel.repr), mul_scalar_eq.
    unfold mul_multiple.
    rewrite (bit_running_sum_step (mul_scalar w) i).
    assert (Hpow : 255 - Z.of_nat i = (255 - Z.of_nat (S i)) + 1) by lia.
    rewrite Hpow, Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    lia.
  Qed.

  Lemma ladder_go_snd (w : HonestInput) (HB : point_ok (hi_g_d_old w)) :
    forall (count i : nat),
      (count <= S i)%nat -> (i < 255)%nat -> (4 <= S i - count)%nat ->
      (forall j : nat,
        (S i - count <= j <= i)%nat -> mul_step_nondegenerate w j) ->
      snd (OrchardVarBaseTables.ladder_go (hi_g_d_old w) (mul_scalar w)
        (mul_acc w (S i)) i count) = mul_acc w (S i - count)%nat.
  Proof.
    induction count as [| c IH]; intros i Hci Hi Hlo Hnds.
    - cbn [OrchardVarBaseTables.ladder_go snd].
      (* [S i - 0] is convertible to [S i], so [f_equal] closes the goal on
         its own; keep [lia] chained for the residual [nat] equality if the
         reduction ever leaves one. *)
      f_equal; lia.
    - cbn [OrchardVarBaseTables.ladder_go].
      destruct (OrchardVarBaseTables.ladder_step (hi_g_d_old w)
        (scalar_bit (mul_scalar w) i) (mul_acc w (S i)))
        as [row acc'] eqn:Hstep.
      pose proof (f_equal snd Hstep) as Hsnd.
      cbn [snd] in Hsnd.
      rewrite ladder_step_incomplete in Hsnd.
      rewrite <- mul_step_point_signed in Hsnd.
      rewrite (vb_step_group w HB i Hi (Hnds i ltac:(lia))) in Hsnd.
      assert (Hi1 : (1 <= i)%nat) by lia.
      pose proof (IH (Nat.pred i) ltac:(lia) ltac:(lia) ltac:(lia)
        (fun j Hj => Hnds j ltac:(lia))) as IHi.
      replace (S (Nat.pred i)) with i in IHi by lia.
      rewrite Hsnd in IHi.
      destruct (OrchardVarBaseTables.ladder_go (hi_g_d_old w)
        (mul_scalar w) acc' (Nat.pred i) c) as [rows out] eqn:Hgo.
      cbn [snd] in IHi |- *.
      rewrite IHi.
      (* [f_equal] may discharge the convertible [nat] index directly; chain
         [lia] for the residual equality if one remains. *)
      f_equal; lia.
  Qed.

  Lemma mul_acc_255_eq (w : HonestInput) (HB : point_ok (hi_g_d_old w))
      (Hk : 0 <= mul_scalar w < 2 ^ 255) :
    mul_acc w 255%nat = EccSpec.point_add (hi_g_d_old w) (hi_g_d_old w).
  Proof.
    pose proof HB as (HBred & HBoc & _).
    (* Expose [mul_base w = unrepr (hi_g_d_old w)] up front: [pallas_mul_2]
       instantiates its base from [HBred : reduced (unrepr (hi_g_d_old w))],
       so the [Pallas.mul 2 _] occurrence must already carry that spelling. *)
    unfold mul_acc, mul_base.
    assert (Hm : mul_multiple w 255%nat = 2).
    { unfold mul_multiple, bit_running_sum.
      rewrite Z.div_small by (change (Z.of_nat 255) with 255; lia).
      reflexivity. }
    rewrite Hm.
    rewrite (pallas_mul_2 _ HBred HBoc).
    rewrite (pallas_repr_add _ _ HBred HBred HBoc HBoc).
    rewrite PallasModel.repr_unrepr.
    reflexivity.
  Qed.

  (** The record fields of [vb_columns], read through the two ladder
      folds. *)
  Lemma vb_columns_fields (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_scalar (OrchardVarBaseTables.vb_columns alpha B) =
      alpha + Primes.t_q /\
    OrchardVarBaseTables.vb_d (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add B B /\
    OrchardVarBaseTables.vb_p3 (OrchardVarBaseTables.vb_columns alpha B) =
      OrchardVarBaseTables.signed_pt B
        (scalar_bit (alpha + Primes.t_q) 3%nat) /\
    OrchardVarBaseTables.vb_p2 (OrchardVarBaseTables.vb_columns alpha B) =
      OrchardVarBaseTables.signed_pt B
        (scalar_bit (alpha + Primes.t_q) 2%nat) /\
    OrchardVarBaseTables.vb_p1 (OrchardVarBaseTables.vb_columns alpha B) =
      OrchardVarBaseTables.signed_pt B
        (scalar_bit (alpha + Primes.t_q) 1%nat) /\
    OrchardVarBaseTables.vb_p0 (OrchardVarBaseTables.vb_columns alpha B) =
      OrchardVarBaseTables.lsb_pt B
        (scalar_bit (alpha + Primes.t_q) 0%nat) /\
    OrchardVarBaseTables.vb_mid3 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_p3 (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_acc4
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_acc3 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_acc4
          (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_mid3
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_mid2 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_p2 (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_acc3
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_acc2 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_acc3
          (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_mid2
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_mid1 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_p1 (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_acc2
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_acc1 (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_acc2
          (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_mid1
          (OrchardVarBaseTables.vb_columns alpha B)) /\
    OrchardVarBaseTables.vb_out (OrchardVarBaseTables.vb_columns alpha B) =
      EccSpec.point_add
        (OrchardVarBaseTables.vb_p0 (OrchardVarBaseTables.vb_columns alpha B))
        (OrchardVarBaseTables.vb_acc1
          (OrchardVarBaseTables.vb_columns alpha B)).
  Proof.
    unfold OrchardVarBaseTables.vb_columns.
    cbv zeta.
    destruct (OrchardVarBaseTables.ladder_go B (alpha + Primes.t_q)
      (EccSpec.point_add B B) 254 125) as [hi acc130].
    destruct (OrchardVarBaseTables.ladder_go B (alpha + Primes.t_q)
      acc130 129 126) as [lo acc4].
    repeat split; reflexivity.
  Qed.

  (** The lo-half output of the honest ladder record is the specification
      accumulator at bit boundary 4. *)
  Lemma vb_columns_acc4 (w : HonestInput)
      (HB : point_ok (hi_g_d_old w))
      (Hk : 0 <= mul_scalar w < 2 ^ 255)
      (Hnd : mul_nondegenerate_input w) :
    OrchardVarBaseTables.vb_acc4
      (OrchardVarBaseTables.vb_columns (ivk w) (hi_g_d_old w)) =
    mul_acc w 4%nat.
  Proof.
    assert (Hproj : OrchardVarBaseTables.vb_acc4
        (OrchardVarBaseTables.vb_columns (ivk w) (hi_g_d_old w)) =
      snd (OrchardVarBaseTables.ladder_go (hi_g_d_old w)
        (ivk w + Primes.t_q)
        (snd (OrchardVarBaseTables.ladder_go (hi_g_d_old w)
          (ivk w + Primes.t_q)
          (EccSpec.point_add (hi_g_d_old w) (hi_g_d_old w)) 254 125))
        129 126)).
    { unfold OrchardVarBaseTables.vb_columns.
      cbv zeta.
      destruct (OrchardVarBaseTables.ladder_go (hi_g_d_old w)
        (ivk w + Primes.t_q)
        (EccSpec.point_add (hi_g_d_old w) (hi_g_d_old w)) 254 125)
        as [hi acc130] eqn:H1.
      (* Reduce [snd (hi, acc130)] to [acc130] so the second [destruct]'s
         pattern matches the right-hand occurrence too. *)
      cbn [snd].
      destruct (OrchardVarBaseTables.ladder_go (hi_g_d_old w)
        (ivk w + Primes.t_q) acc130 129 126) as [lo acc4] eqn:H2.
      reflexivity. }
    rewrite Hproj.
    change (ivk w + Primes.t_q) with (mul_scalar w).
    rewrite <- (mul_acc_255_eq w HB Hk).
    rewrite (ladder_go_snd w HB 125%nat 254%nat ltac:(lia) ltac:(lia)
      ltac:(lia) (fun j Hj => Hnd j ltac:(lia))).
    change (S 254 - 125)%nat with 130%nat.
    change 130%nat with (S 129).
    rewrite (ladder_go_snd w HB 126%nat 129%nat ltac:(lia) ltac:(lia)
      ltac:(lia) (fun j Hj => Hnd j ltac:(lia))).
    f_equal.
  Qed.

  (** ** Cell read-offs of the incomplete-region readers *)

  Lemma fb_full_cells (l : leg_data) (scalar count row : Z)
      (H1 : 1 <= row) (H2 : row < count) :
    fb_full_advice_t l scalar count A0 row =
      List.nth (Z.to_nat row) (lg_px l) 0 /\
    fb_full_advice_t l scalar count A1 row =
      List.nth (Z.to_nat row) (lg_py l) 0 /\
    fb_full_advice_t l scalar count A2 row =
      List.nth (Z.to_nat row - 1) (lg_ax l) 0 /\
    fb_full_advice_t l scalar count A3 row =
      List.nth (Z.to_nat row - 1) (lg_ay l) 0.
  Proof.
    unfold fb_full_advice_t.
    rewrite (guard_le_lt 0 count row) by lia.
    rewrite (leb_of_le 1 row) by lia.
    repeat split; reflexivity.
  Qed.

  Lemma fb_short_cells (l : leg_data) (scalar count row : Z)
      (H1 : 1 <= row) (H2 : row < count) :
    fb_short_advice_t l scalar count A0 row =
      List.nth (Z.to_nat row) (lg_px l) 0 /\
    fb_short_advice_t l scalar count A1 row =
      List.nth (Z.to_nat row) (lg_py l) 0 /\
    fb_short_advice_t l scalar count A2 row =
      List.nth (Z.to_nat row - 1) (lg_ax l) 0 /\
    fb_short_advice_t l scalar count A3 row =
      List.nth (Z.to_nat row - 1) (lg_ay l) 0.
  Proof.
    unfold fb_short_advice_t.
    rewrite (guard_le_lt 0 count row) by lia.
    rewrite (leb_of_le 1 row) by lia.
    repeat split; reflexivity.
  Qed.

  Lemma nf_cells (w : HonestInput) (tb : t) (row : Z)
      (H1 : 1 <= row) (H2 : row <= 84) :
    advice_nullifier_t w tb A0 RegionId.Nullifier.BaseFieldIncomplete row =
      List.nth (Z.to_nat row) (lg_px (t_nk_leg tb)) 0 /\
    advice_nullifier_t w tb A1 RegionId.Nullifier.BaseFieldIncomplete row =
      List.nth (Z.to_nat row) (lg_py (t_nk_leg tb)) 0 /\
    advice_nullifier_t w tb A2 RegionId.Nullifier.BaseFieldIncomplete row =
      List.nth (Z.to_nat row - 1) (lg_ax (t_nk_leg tb)) 0 /\
    advice_nullifier_t w tb A3 RegionId.Nullifier.BaseFieldIncomplete row =
      List.nth (Z.to_nat row - 1) (lg_ay (t_nk_leg tb)) 0.
  Proof.
    unfold advice_nullifier_t.
    rewrite (guard_le_le 0 84 row) by lia.
    rewrite (guard_le_le 1 84 row) by lia.
    repeat split; reflexivity.
  Qed.

  (** ** The incomplete-addition row core

      At an interior row of a leg region whose six gate cells read the leg
      lists, both incomplete-addition constraints hold: the next-row
      accumulator is the row's incomplete addition and its chord is
      non-vertical ([leg_ok]). *)
  Lemma leg_incomplete_eval (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (l : leg_data) (nw : nat) (row : Z)
      (Hlok : leg_ok l nw)
      (H1 : 1 <= row) (H2 : row <= Z.of_nat nw - 2)
      (HA0 : Γ.(Assignment.advice) A0 region row =
        List.nth (Z.to_nat row) (lg_px l) 0)
      (HA1 : Γ.(Assignment.advice) A1 region row =
        List.nth (Z.to_nat row) (lg_py l) 0)
      (HA2 : Γ.(Assignment.advice) A2 region row =
        List.nth (Z.to_nat row - 1) (lg_ax l) 0)
      (HA3 : Γ.(Assignment.advice) A3 region row =
        List.nth (Z.to_nat row - 1) (lg_ay l) 0)
      (HA2' : Γ.(Assignment.advice) A2 region (row + 1) =
        List.nth (Z.to_nat (row + 1) - 1) (lg_ax l) 0)
      (HA3' : Γ.(Assignment.advice) A3 region (row + 1) =
        List.nth (Z.to_nat (row + 1) - 1) (lg_ay l) 0)
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
            .incomplete_addition_gate)) :
    eval_constraint Γ (region, row) body.
  Proof.
    destruct Hlok as (Hwin & Hacc & Hstep).
    destruct (Hstep (Z.to_nat row) ltac:(lia) ltac:(lia)) as
      (Hchain & Hchord).
    assert (Hidx : (Z.to_nat (row + 1) - 1)%nat = Z.to_nat row) by lia.
    assert (Hpred : (Z.to_nat row - 1)%nat = Nat.pred (Z.to_nat row)) by lia.
    apply (incomplete_eval Γ region row (leg_pt l (Z.to_nat row))
      (leg_acc l (Nat.pred (Z.to_nat row)))); try assumption.
    (* [try assumption] discharges whichever cell equalities are already
       convertible (the [A0]/[A1] window cells); handle every remaining cell
       uniformly so the proof does not depend on which ones it absorbed. *)
    all: first
      [ rewrite HA0; reflexivity
      | rewrite HA1; reflexivity
      | rewrite HA2, Hpred; reflexivity
      | rewrite HA3, Hpred; reflexivity
      | rewrite HA2', Hidx, <- Hchain; reflexivity
      | rewrite HA3', Hidx, <- Hchain; reflexivity ].
  Qed.

  (** The sign-adjusted value-commitment point stays a good curve point. *)
  Lemma vcv_point_wgood (w : HonestInput) (tb : t) :
    wgood (t_vcv_mul tb) -> wgood (vcv_point_t w tb).
  Proof.
    unfold vcv_point_t, vcv_y_var_t.
    destruct (sign w =? 1).
    - intro H. exact H.
    - intro H. exact (wgood_point_neg _ H).
  Qed.

  (** ** The ecc-add gate obligations *)

  (** The variable-base ladder record is opaque to the conversion oracle in
      the gate proof: the cell-value [reflexivity] obligations compare a
      [vb_acc4]/[vb_p3] projection of [t_vb (tables_of w)] against the same
      projection, and unfolding [vb_columns] to reach it would run the
      130-step ladder fold (docs/compile-performance.md).  The lemmas above
      are the only ones that unfold it. *)
  #[local] Opaque OrchardVarBaseTables.vb_columns.

  Theorem ecc_add_gates_forward : ecc_selector_gates_ok.
  Proof.
    intros w Hvalid Hnd sel region row Hin Hsel gate Hgate name body Hbody.
    pose proof (ecc_shape sel region row Hin) as Hshape.
    destruct Hvalid as (Hty & Hens & Heno & Hpkd).
    destruct Hty as (Hv_old & Hv_new & Halpha & Hrcv & Hrcm_old & Hrcm_new &
      Hrivk & Hnk & Hrho & Hpsi_old & Hpsi_new & Hanchor & Hak & Hgd_old &
      Hpkd_old & Hgd_new & Hpkd_new & Hpath_len & Hpath & Hpos & Hes & Heo).
    destruct Hnd as (Hnd_merkle & Hnd_nc_old & Hnd_nc_new & Hnd_civk &
      Hnd_mul).
    pose proof (in_bodies_of sel gate Hgate name body Hbody) as Hb.
    clear Hbody.
    destruct sel; try discriminate Hsel.
    - (* QWitnessPoint: the cm_old witness *)
      rewrite bodies_of_q_witness_point in Hb.
      cbn [ecc_shape_b] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | glr]; try discriminate Hshape.
      destruct wir; try discriminate Hshape.
      apply Z.eqb_eq in Hshape; subst row.
      assert (Hcm : wgood (t_cm_old (tables_of w))).
      { rewrite t_cm_old_eq.
        apply wgood_point_add.
        - rewrite t_nc_old_hash_eq.
          apply pt_affine_wgood.
          apply note_commit_hash_out_affine.
          exact Hnd_nc_old.
        - unfold OrchardProtocolSpec.mul_note_commit_r.
          apply wgood_repr_mul.
          + exact PallasGenerators.note_commit_r_reduced.
          + exact PallasGenerators.note_commit_r_on_curve. }
      apply (witness_point_eval (OrchardHonestAssignment.honest_assignment w)
        _ 0 (t_cm_old (tables_of w))).
      + reflexivity.
      + reflexivity.
      + destruct (wgood_cadd_input _ Hcm) as (_ & _ & Hoc). exact Hoc.
      + exact Hb.
    - (* QWitnessPointNonId *)
      rewrite bodies_of_q_witness_point_non_id in Hb.
      cbn [ecc_shape_b] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | glr]; try discriminate Hshape.
      + (* WitnessInput: GDOld / AkP *)
        destruct wir; try discriminate Hshape;
          apply Z.eqb_eq in Hshape; subst row.
        * (* GDOld *)
          apply (witness_non_id_eval
            (OrchardHonestAssignment.honest_assignment w) _ 0
            (hi_g_d_old w)).
          -- reflexivity.
          -- reflexivity.
          -- exact (proj1 (pt_affine_of_point_ok _ Hgd_old)).
          -- exact Hb.
        * (* AkP *)
          apply (witness_non_id_eval
            (OrchardHonestAssignment.honest_assignment w) _ 0 (hi_ak w)).
          -- reflexivity.
          -- reflexivity.
          -- exact (proj1 (pt_affine_of_point_ok _ Hak)).
          -- exact Hb.
      + (* AddressIntegrity WitnessPkD *)
        destruct air as [sub | |]; try discriminate Hshape.
        apply Z.eqb_eq in Hshape; subst row.
        assert (Hres : t_vb_result (tables_of w) = hi_pk_d_old w).
        { rewrite t_vb_result_eq, t_ivk_eq_ivk.
          symmetry.
          exact Hpkd. }
        apply (witness_non_id_eval
          (OrchardHonestAssignment.honest_assignment w) _ 0
          (t_vb_result (tables_of w))).
        * reflexivity.
        * reflexivity.
        * rewrite Hres.
          exact (proj1 (pt_affine_of_point_ok _ Hpkd_old)).
        * exact Hb.
      + (* NoteCommitNewWitnessGD *)
        apply Z.eqb_eq in Hshape; subst row.
        apply (witness_non_id_eval
          (OrchardHonestAssignment.honest_assignment w) _ 0 (hi_g_d_new w)).
        * reflexivity.
        * reflexivity.
        * exact (proj1 (pt_affine_of_point_ok _ Hgd_new)).
        * exact Hb.
      + (* NoteCommitNewWitnessPkD *)
        apply Z.eqb_eq in Hshape; subst row.
        apply (witness_non_id_eval
          (OrchardHonestAssignment.honest_assignment w) _ 0
          (hi_pk_d_new w)).
        * reflexivity.
        * reflexivity.
        * exact (proj1 (pt_affine_of_point_ok _ Hpkd_new)).
        * exact Hb.
    - (* QAddIncomplete: the fixed-base leg rows *)
      rewrite bodies_of_q_add_incomplete in Hb.
      cbn [ecc_shape_b] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | glr]; try discriminate Hshape.
      + (* ValueCommitment *)
        destruct vr; try discriminate Hshape.
        * (* ValueCommitVIncomplete, rows 1..20 *)
          apply Bool.andb_true_iff in Hshape.
          destruct Hshape as [Hr1 Hr2].
          apply Z.leb_le in Hr1, Hr2.
          pose proof (fb_short_cells (t_vcv_leg (tables_of w)) (magnitude w)
            22 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
          pose proof (fb_short_cells (t_vcv_leg (tables_of w)) (magnitude w)
            22 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
          apply (leg_incomplete_eval _ _ (t_vcv_leg (tables_of w)) 22%nat
            row).
          -- rewrite t_vcv_leg_eq. apply vcv_leg_facts.
          -- lia.
          -- cbn. lia.
          -- exact HcA0.
          -- exact HcA1.
          -- exact HcA2.
          -- exact HcA3.
          -- exact HcA2'.
          -- exact HcA3'.
          -- exact Hb.
        * (* ValueCommitRIncomplete, rows 1..83 *)
          apply Bool.andb_true_iff in Hshape.
          destruct Hshape as [Hr1 Hr2].
          apply Z.leb_le in Hr1, Hr2.
          pose proof (fb_full_cells (t_vcr_leg (tables_of w)) (hi_rcv w)
            85 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
          pose proof (fb_full_cells (t_vcr_leg (tables_of w)) (hi_rcv w)
            85 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
          apply (leg_incomplete_eval _ _ (t_vcr_leg (tables_of w)) 85%nat
            row).
          -- rewrite t_vcr_leg_eq. apply vcr_leg_facts.
          -- lia.
          -- cbn. lia.
          -- exact HcA0.
          -- exact HcA1.
          -- exact HcA2.
          -- exact HcA3.
          -- exact HcA2'.
          -- exact HcA3'.
          -- exact Hb.
      + (* Nullifier BaseFieldIncomplete, rows 1..83 *)
        destruct nr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape.
        destruct Hshape as [Hr1 Hr2].
        apply Z.leb_le in Hr1, Hr2.
        pose proof (nf_cells w (tables_of w) row ltac:(lia) ltac:(lia))
          as (HcA0 & HcA1 & HcA2 & HcA3).
        pose proof (nf_cells w (tables_of w) (row + 1) ltac:(lia)
          ltac:(lia)) as (_ & _ & HcA2' & HcA3').
        apply (leg_incomplete_eval _ _ (t_nk_leg (tables_of w)) 85%nat row).
        * rewrite t_nk_leg_shape. apply nk_leg_facts.
        * lia.
        * cbn. lia.
        * exact HcA0.
        * exact HcA1.
        * exact HcA2.
        * exact HcA3.
        * exact HcA2'.
        * exact HcA3'.
        * exact Hb.
      + (* SpendAuthority FullFixedIncomplete, rows 1..83 *)
        destruct sr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape.
        destruct Hshape as [Hr1 Hr2].
        apply Z.leb_le in Hr1, Hr2.
        pose proof (fb_full_cells (t_sa_leg (tables_of w)) (hi_alpha w)
          85 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
        pose proof (fb_full_cells (t_sa_leg (tables_of w)) (hi_alpha w)
          85 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
        apply (leg_incomplete_eval _ _ (t_sa_leg (tables_of w)) 85%nat row).
        * rewrite t_sa_leg_eq. apply sa_leg_facts.
        * lia.
        * cbn. lia.
        * exact HcA0.
        * exact HcA1.
        * exact HcA2.
        * exact HcA3.
        * exact HcA2'.
        * exact HcA3'.
        * exact Hb.
      + (* CommitIvk FixedBaseIncomplete, rows 1..83 *)
        destruct cr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape.
        destruct Hshape as [Hr1 Hr2].
        apply Z.leb_le in Hr1, Hr2.
        pose proof (fb_full_cells (t_civkr_leg (tables_of w)) (hi_rivk w)
          85 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
        pose proof (fb_full_cells (t_civkr_leg (tables_of w)) (hi_rivk w)
          85 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
        apply (leg_incomplete_eval _ _ (t_civkr_leg (tables_of w)) 85%nat
          row).
        * rewrite t_civkr_leg_eq. apply civkr_leg_facts.
        * lia.
        * cbn. lia.
        * exact HcA0.
        * exact HcA1.
        * exact HcA2.
        * exact HcA3.
        * exact HcA2'.
        * exact HcA3'.
        * exact Hb.
      + (* NoteCommit FixedBaseIncomplete, rows 1..83 *)
        destruct ncr; try discriminate Hshape.
        apply Bool.andb_true_iff in Hshape.
        destruct Hshape as [Hr1 Hr2].
        apply Z.leb_le in Hr1, Hr2.
        destruct ncw.
        * (* Old: the rcm_old blinding leg *)
          pose proof (fb_full_cells (t_nco_leg (tables_of w)) (hi_rcm_old w)
            85 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
          pose proof (fb_full_cells (t_nco_leg (tables_of w)) (hi_rcm_old w)
            85 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
          apply (leg_incomplete_eval _ _ (t_nco_leg (tables_of w)) 85%nat
            row).
          -- rewrite t_nco_leg_eq. apply ncr_leg_facts.
          -- lia.
          -- cbn. lia.
          -- exact HcA0.
          -- exact HcA1.
          -- exact HcA2.
          -- exact HcA3.
          -- exact HcA2'.
          -- exact HcA3'.
          -- exact Hb.
        * (* New: the rcm_new blinding leg *)
          pose proof (fb_full_cells (t_ncn_leg (tables_of w)) (hi_rcm_new w)
            85 row ltac:(lia) ltac:(lia)) as (HcA0 & HcA1 & HcA2 & HcA3).
          pose proof (fb_full_cells (t_ncn_leg (tables_of w)) (hi_rcm_new w)
            85 (row + 1) ltac:(lia) ltac:(lia)) as (_ & _ & HcA2' & HcA3').
          apply (leg_incomplete_eval _ _ (t_ncn_leg (tables_of w)) 85%nat
            row).
          -- rewrite t_ncn_leg_eq. apply ncr_leg_facts.
          -- lia.
          -- cbn. lia.
          -- exact HcA0.
          -- exact HcA1.
          -- exact HcA2.
          -- exact HcA3.
          -- exact HcA2'.
          -- exact HcA3'.
          -- exact Hb.
    - (* QEccAdd: the complete additions *)
      rewrite bodies_of_q_ecc_add in Hb.
      cbn [ecc_shape_b] in Hshape.
      destruct region as
        [wir | ml mr | pr | vr | nr | sr | air | cr | ncw ncr
         | | | | | | glr]; try discriminate Hshape.
      + (* ValueCommitment *)
        destruct vr; try discriminate Hshape.
        * (* ValueCommitVMsb *)
          apply Z.eqb_eq in Hshape; subst row.
          pose proof (vcv_leg_facts (magnitude w)) as Hlok.
          rewrite <- t_vcv_leg_eq in Hlok.
          destruct Hlok as (Hwin & Hacc & _).
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _ 0
            (leg_pt (t_vcv_leg (tables_of w)) 21%nat)
            (leg_acc (t_vcv_leg (tables_of w)) 20%nat)).
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- transitivity (Point.x (t_vcv_mul (tables_of w)));
               [reflexivity | rewrite t_vcv_mul_eq; reflexivity].
          -- transitivity (Point.y (t_vcv_mul (tables_of w)));
               [reflexivity | rewrite t_vcv_mul_eq; reflexivity].
          -- apply wgood_cadd_input, Hwin. lia.
          -- apply wgood_cadd_input, Hacc. lia.
          -- exact Hb.
        * (* ValueCommitRLast *)
          apply Z.eqb_eq in Hshape; subst row.
          pose proof (vcr_leg_facts (hi_rcv w)) as Hlok.
          rewrite <- t_vcr_leg_eq in Hlok.
          destruct Hlok as (Hwin & Hacc & _).
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (leg_pt (t_vcr_leg (tables_of w)) 84%nat)
            (leg_acc (t_vcr_leg (tables_of w)) 83%nat)).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hwin. lia.
          -- apply wgood_cadd_input, Hacc. lia.
          -- exact Hb.
        * (* ValueCommitment CompletePointAdd *)
          apply Z.eqb_eq in Hshape; subst row.
          assert (Hvm : wgood (t_vcv_mul (tables_of w))).
          { rewrite t_vcv_mul_eq.
            pose proof (vcv_leg_facts (magnitude w)) as Hlok.
            rewrite <- t_vcv_leg_eq in Hlok.
            destruct Hlok as (Hwin & Hacc & _).
            apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
          assert (Hvr : wgood (t_vcr_pt (tables_of w))).
          { rewrite t_vcr_pt_eq.
            pose proof (vcr_leg_facts (hi_rcv w)) as Hlok.
            rewrite <- t_vcr_leg_eq in Hlok.
            destruct Hlok as (Hwin & Hacc & _).
            apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (vcv_point_t w (tables_of w)) (t_vcr_pt (tables_of w))).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, vcv_point_wgood, Hvm.
          -- apply wgood_cadd_input, Hvr.
          -- exact Hb.
      + (* Nullifier *)
        destruct nr; try discriminate Hshape.
        * (* BaseFieldComplete *)
          apply Z.eqb_eq in Hshape; subst row.
          pose proof (nk_leg_facts (t_nullifier_scalar (tables_of w)))
            as Hlok.
          rewrite <- t_nk_leg_shape in Hlok.
          destruct Hlok as (Hwin & Hacc & _).
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (leg_pt (t_nk_leg (tables_of w)) 84%nat)
            (leg_acc (t_nk_leg (tables_of w)) 83%nat)).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hwin. lia.
          -- apply wgood_cadd_input, Hacc. lia.
          -- exact Hb.
        * (* Nullifier CompletePointAdd *)
          apply Z.eqb_eq in Hshape; subst row.
          assert (Hcm : wgood (t_cm_old (tables_of w))).
          { rewrite t_cm_old_eq.
            apply wgood_point_add.
            - rewrite t_nc_old_hash_eq.
              apply pt_affine_wgood.
              apply note_commit_hash_out_affine.
              exact Hnd_nc_old.
            - unfold OrchardProtocolSpec.mul_note_commit_r.
              apply wgood_repr_mul.
              + exact PallasGenerators.note_commit_r_reduced.
              + exact PallasGenerators.note_commit_r_on_curve. }
          assert (Hnkp : wgood (t_nk_prod (tables_of w))).
          { rewrite t_nk_prod_eq.
            pose proof (nk_leg_facts (t_nullifier_scalar (tables_of w)))
              as Hlok.
            rewrite <- t_nk_leg_shape in Hlok.
            destruct Hlok as (Hwin & Hacc & _).
            apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (t_cm_old (tables_of w)) (t_nk_prod (tables_of w))).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hcm.
          -- apply wgood_cadd_input, Hnkp.
          -- exact Hb.
      + (* SpendAuthority *)
        destruct sr; try discriminate Hshape.
        * (* FullFixedLast *)
          apply Z.eqb_eq in Hshape; subst row.
          pose proof (sa_leg_facts (hi_alpha w)) as Hlok.
          rewrite <- t_sa_leg_eq in Hlok.
          destruct Hlok as (Hwin & Hacc & _).
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (leg_pt (t_sa_leg (tables_of w)) 84%nat)
            (leg_acc (t_sa_leg (tables_of w)) 83%nat)).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hwin. lia.
          -- apply wgood_cadd_input, Hacc. lia.
          -- exact Hb.
        * (* SpendAuthority CompletePointAdd *)
          apply Z.eqb_eq in Hshape; subst row.
          assert (Hcomm : wgood (t_sa_comm (tables_of w))).
          { rewrite t_sa_comm_eq.
            pose proof (sa_leg_facts (hi_alpha w)) as Hlok.
            rewrite <- t_sa_leg_eq in Hlok.
            destruct Hlok as (Hwin & Hacc & _).
            apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (t_sa_comm (tables_of w)) (hi_ak w)).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hcomm.
          -- apply wgood_cadd_input, wgood_of_point_ok, Hak.
          -- exact Hb.
      + (* AddressIntegrity: the variable-base QEccAdd rows *)
        destruct air as [sub | |]; try discriminate Hshape.
        destruct sub; try discriminate Hshape.
        assert (Hivkb : 0 <= ivk w < Primes.pallas_p)
          by (apply ivk_bound; exact Hnd_civk).
        pose proof (mul_scalar_bound w Hivkb) as Hkb.
        pose proof (vb_columns_acc4 w Hgd_old Hkb Hnd_mul) as Hacc4.
        pose proof (vb_columns_fields (ivk w) (hi_g_d_old w)) as Hfields.
        rewrite <- t_ivk_eq_ivk in Hacc4, Hfields.
        rewrite <- t_vb_eq in Hacc4, Hfields.
        destruct Hfields as (Hfk & Hfd & Hfp3 & Hfp2 & Hfp1 & Hfp0 & Hfm3 &
          Hfa3 & Hfm2 & Hfa2 & Hfm1 & Hfa1 & Hfout).
        assert (Hwacc4 : wgood
          (OrchardVarBaseTables.vb_acc4 (t_vb (tables_of w)))).
        { rewrite Hacc4.
          exact (wgood_repr_mul (mul_base w) (mul_multiple w 4%nat)
            (proj1 Hgd_old) (proj1 (proj2 Hgd_old))). }
        assert (Hwp3 : wgood
          (OrchardVarBaseTables.vb_p3 (t_vb (tables_of w))))
          by (rewrite Hfp3; apply wgood_signed; exact Hgd_old).
        assert (Hwp2 : wgood
          (OrchardVarBaseTables.vb_p2 (t_vb (tables_of w))))
          by (rewrite Hfp2; apply wgood_signed; exact Hgd_old).
        assert (Hwp1 : wgood
          (OrchardVarBaseTables.vb_p1 (t_vb (tables_of w))))
          by (rewrite Hfp1; apply wgood_signed; exact Hgd_old).
        assert (Hwp0 : wgood
          (OrchardVarBaseTables.vb_p0 (t_vb (tables_of w))))
          by (rewrite Hfp0; apply wgood_lsb; exact Hgd_old).
        assert (Hwm3 : wgood
          (OrchardVarBaseTables.vb_mid3 (t_vb (tables_of w))))
          by (rewrite Hfm3; apply wgood_point_add; assumption).
        assert (Hwa3 : wgood
          (OrchardVarBaseTables.vb_acc3 (t_vb (tables_of w))))
          by (rewrite Hfa3; apply wgood_point_add; assumption).
        assert (Hwm2 : wgood
          (OrchardVarBaseTables.vb_mid2 (t_vb (tables_of w))))
          by (rewrite Hfm2; apply wgood_point_add; assumption).
        assert (Hwa2 : wgood
          (OrchardVarBaseTables.vb_acc2 (t_vb (tables_of w))))
          by (rewrite Hfa2; apply wgood_point_add; assumption).
        assert (Hwm1 : wgood
          (OrchardVarBaseTables.vb_mid1 (t_vb (tables_of w))))
          by (rewrite Hfm1; apply wgood_point_add; assumption).
        assert (Hwa1 : wgood
          (OrchardVarBaseTables.vb_acc1 (t_vb (tables_of w))))
          by (rewrite Hfa1; apply wgood_point_add; assumption).
        assert (HwB : wgood (hi_g_d_old w))
          by (apply wgood_of_point_ok; exact Hgd_old).
        assert (Hrows : row = 0 \/ row = 129 \/ row = 130 \/ row = 131 \/
          row = 132 \/ row = 133 \/ row = 134 \/ row = 135).
        { apply Bool.orb_true_iff in Hshape.
          destruct Hshape as [H | H].
          - apply Z.eqb_eq in H. lia.
          - apply Bool.andb_true_iff in H.
            destruct H as [H1 H2].
            apply Z.leb_le in H1, H2.
            lia. }
        destruct Hrows as
          [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ] ] ].
        * (* row 0: the base doubling *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _ 0
            (hi_g_d_old w) (hi_g_d_old w));
            [reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | | | | | exact Hb].
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_d (t_vb (tables_of w))));
               [reflexivity | rewrite Hfd; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_d (t_vb (tables_of w))));
               [reflexivity | rewrite Hfd; reflexivity].
          -- apply wgood_cadd_input, HwB.
          -- apply wgood_cadd_input, HwB.
        * (* row 129 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            129 (OrchardVarBaseTables.vb_p3 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_acc4 (t_vb (tables_of w))));
            [ | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | | | | | exact Hb].
          -- transitivity (Point.x (hi_g_d_old w)); [reflexivity |].
             rewrite Hfp3, signed_pt_x.
             reflexivity.
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_mid3 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm3; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_mid3 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm3; reflexivity].
          -- apply wgood_cadd_input, Hwp3.
          -- apply wgood_cadd_input, Hwacc4.
        * (* row 130 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            130 (OrchardVarBaseTables.vb_acc4 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_mid3 (t_vb (tables_of w))));
            [reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | | | | | exact Hb].
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_acc3 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa3; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_acc3 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa3; reflexivity].
          -- apply wgood_cadd_input, Hwacc4.
          -- apply wgood_cadd_input, Hwm3.
        * (* row 131 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            131 (OrchardVarBaseTables.vb_p2 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_acc3 (t_vb (tables_of w))));
            [ | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | | | | | exact Hb].
          -- transitivity (Point.x (hi_g_d_old w)); [reflexivity |].
             rewrite Hfp2, signed_pt_x.
             reflexivity.
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_mid2 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm2; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_mid2 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm2; reflexivity].
          -- apply wgood_cadd_input, Hwp2.
          -- apply wgood_cadd_input, Hwa3.
        * (* row 132 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            132 (OrchardVarBaseTables.vb_acc3 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_mid2 (t_vb (tables_of w))));
            [reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | | | | | exact Hb].
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_acc2 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa2; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_acc2 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa2; reflexivity].
          -- apply wgood_cadd_input, Hwa3.
          -- apply wgood_cadd_input, Hwm2.
        * (* row 133 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            133 (OrchardVarBaseTables.vb_p1 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_acc2 (t_vb (tables_of w))));
            [ | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | | | | | exact Hb].
          -- transitivity (Point.x (hi_g_d_old w)); [reflexivity |].
             rewrite Hfp1, signed_pt_x.
             reflexivity.
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_mid1 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm1; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_mid1 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfm1; reflexivity].
          -- apply wgood_cadd_input, Hwp1.
          -- apply wgood_cadd_input, Hwa2.
        * (* row 134 *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            134 (OrchardVarBaseTables.vb_acc2 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_mid1 (t_vb (tables_of w))));
            [reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | | | | | exact Hb].
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_acc1 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa1; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_acc1 (t_vb (tables_of w))));
               [reflexivity | rewrite Hfa1; reflexivity].
          -- apply wgood_cadd_input, Hwa2.
          -- apply wgood_cadd_input, Hwm1.
        * (* row 135: the LSB round *)
          apply (cadd_eval (OrchardHonestAssignment.honest_assignment w) _
            135 (OrchardVarBaseTables.vb_p0 (t_vb (tables_of w)))
            (OrchardVarBaseTables.vb_acc1 (t_vb (tables_of w))));
            [reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | reflexivity | reflexivity | reflexivity
             | reflexivity | | | | | exact Hb].
          -- transitivity
               (Point.x (OrchardVarBaseTables.vb_out (t_vb (tables_of w))));
               [reflexivity | rewrite Hfout; reflexivity].
          -- transitivity
               (Point.y (OrchardVarBaseTables.vb_out (t_vb (tables_of w))));
               [reflexivity | rewrite Hfout; reflexivity].
          -- apply wgood_cadd_input, Hwp0.
          -- apply wgood_cadd_input, Hwa1.
      + (* CommitIvk *)
        destruct cr; try discriminate Hshape.
        * (* FixedBaseLast *)
          apply Z.eqb_eq in Hshape; subst row.
          pose proof (civkr_leg_facts (hi_rivk w)) as Hlok.
          rewrite <- t_civkr_leg_eq in Hlok.
          destruct Hlok as (Hwin & Hacc & _).
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (leg_pt (t_civkr_leg (tables_of w)) 84%nat)
            (leg_acc (t_civkr_leg (tables_of w)) 83%nat)).
          -- intros col off. reflexivity.
          -- apply wgood_cadd_input, Hwin. lia.
          -- apply wgood_cadd_input, Hacc. lia.
          -- exact Hb.
        * (* CommitIvk CompletePointAdd *)
          apply Z.eqb_eq in Hshape; subst row.
          assert (Hh : pt_affine_ok (hd_out (t_civk_hash (tables_of w)))).
          { rewrite t_civk_hash_eq.
            unfold commit_ivk_words.
            apply commit_ivk_hash_out_affine.
            unfold commit_ivk_words in Hnd_civk.
            exact Hnd_civk. }
          assert (Hcp : wgood (t_civkr_pt (tables_of w))).
          { rewrite t_civkr_pt_eq.
            pose proof (civkr_leg_facts (hi_rivk w)) as Hlok.
            rewrite <- t_civkr_leg_eq in Hlok.
            destruct Hlok as (Hwin & Hacc & _).
            apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
          apply (cadd_region_eval
            (OrchardHonestAssignment.honest_assignment w) _
            (hd_out (t_civk_hash (tables_of w))) (t_civkr_pt (tables_of w))).
          -- intros col off. reflexivity.
          -- exact (pt_affine_cadd_input _ Hh).
          -- apply wgood_cadd_input, Hcp.
          -- exact Hb.
      + (* NoteCommit FixedBaseLast / CompletePointAdd *)
        destruct ncr; try discriminate Hshape;
          apply Z.eqb_eq in Hshape; subst row.
        * (* FixedBaseLast *)
          destruct ncw.
          -- pose proof (ncr_leg_facts (hi_rcm_old w)) as Hlok.
             rewrite <- t_nco_leg_eq in Hlok.
             destruct Hlok as (Hwin & Hacc & _).
             apply (cadd_region_eval
               (OrchardHonestAssignment.honest_assignment w) _
               (leg_pt (t_nco_leg (tables_of w)) 84%nat)
               (leg_acc (t_nco_leg (tables_of w)) 83%nat)).
             ++ intros col off. reflexivity.
             ++ apply wgood_cadd_input, Hwin. lia.
             ++ apply wgood_cadd_input, Hacc. lia.
             ++ exact Hb.
          -- pose proof (ncr_leg_facts (hi_rcm_new w)) as Hlok.
             rewrite <- t_ncn_leg_eq in Hlok.
             destruct Hlok as (Hwin & Hacc & _).
             apply (cadd_region_eval
               (OrchardHonestAssignment.honest_assignment w) _
               (leg_pt (t_ncn_leg (tables_of w)) 84%nat)
               (leg_acc (t_ncn_leg (tables_of w)) 83%nat)).
             ++ intros col off. reflexivity.
             ++ apply wgood_cadd_input, Hwin. lia.
             ++ apply wgood_cadd_input, Hacc. lia.
             ++ exact Hb.
        * (* CompletePointAdd *)
          destruct ncw.
          -- (* Old *)
             assert (Hh : pt_affine_ok
               (hd_out (t_nc_old_hash (tables_of w)))).
             { rewrite t_nc_old_hash_eq.
               apply note_commit_hash_out_affine.
               exact Hnd_nc_old. }
             assert (Hcp : wgood (t_nco_pt (tables_of w))).
             { rewrite t_nco_pt_eq.
               pose proof (ncr_leg_facts (hi_rcm_old w)) as Hlok.
               rewrite <- t_nco_leg_eq in Hlok.
               destruct Hlok as (Hwin & Hacc & _).
               apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
             apply (cadd_region_eval
               (OrchardHonestAssignment.honest_assignment w) _
               (hd_out (t_nc_old_hash (tables_of w)))
               (t_nco_pt (tables_of w))).
             ++ intros col off. reflexivity.
             ++ exact (pt_affine_cadd_input _ Hh).
             ++ apply wgood_cadd_input, Hcp.
             ++ exact Hb.
          -- (* New *)
             assert (Hh : pt_affine_ok
               (hd_out (t_nc_new_hash (tables_of w)))).
             { rewrite t_nc_new_hash_eq, t_nf_spec_eq.
               apply note_commit_hash_out_affine.
               exact Hnd_nc_new. }
             assert (Hcp : wgood (t_ncn_pt (tables_of w))).
             { rewrite t_ncn_pt_eq.
               pose proof (ncr_leg_facts (hi_rcm_new w)) as Hlok.
               rewrite <- t_ncn_leg_eq in Hlok.
               destruct Hlok as (Hwin & Hacc & _).
               apply wgood_point_add; [apply Hwin; lia | apply Hacc; lia]. }
             apply (cadd_region_eval
               (OrchardHonestAssignment.honest_assignment w) _
               (hd_out (t_nc_new_hash (tables_of w)))
               (t_ncn_pt (tables_of w))).
             ++ intros col off. reflexivity.
             ++ exact (pt_affine_cadd_input _ Hh).
             ++ apply wgood_cadd_input, Hcp.
             ++ exact Hb.
  Qed.

End OrchardCompletenessForwardEccAdd.
