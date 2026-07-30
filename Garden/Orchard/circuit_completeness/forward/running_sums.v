(** * Forward lemmas: running-sum decomposition and lookup range checks

    Symbolic per-gate forward lemmas of the C2 completeness campaign
    ([forward/api.v]) for the running-sum decomposition gate of
    [decompose_running_sum.v] ([QMulFixedRunningSum], the "range check"
    constraint), the short-lookup bitshift gate of [lookup_range_check.v]
    ([QBitshift]), and the range-check lookup argument
    ([QLookup]/[QRunning]): at every synthesis-enabled point of these
    selectors, the honest assignment satisfies the guarded constraint and
    resolves the looked-up word to a row of the 1024-row table, for every
    input in the completeness domain.

    The obligations are stated per guarding selector
    ([selector_gates_ok]/[selector_lookups_ok] mirror the per-family
    obligations of [forward/api.v] with the point's selector fixed instead
    of its region family; the family joins follow by case analysis on the
    selector).  The proofs are decomposition algebra over the generated
    running sums: each looked-up word is a [z_i − 2^10·z_{i+1} = z_i mod
    2^10] telescoping step (or a bounded bit slice for the short checks),
    and each range-check word is the base-8 digit [z_i − 8·z_{i+1} = z_i
    mod 8], both unconditional integer identities.  The enabled-point
    domain of each selector is pinned by one [vm_compute] certificate over
    the reified synthesis facts.

    Delivered surface: [qbitshift_gates_ok] ([selector_gates_ok
    Selector.QBitshift]), [qmulfixedrs_range_gates_ok] (the range-check
    constraint at every enabled [QMulFixedRunningSum] point; the
    coordinates-check constraints under the same selector belong to the
    fixed-base window family, split off by [qmulfixedrs_body_eq]),
    [qlookup_lookups_ok]/[qrunning_lookups_ok] ([selector_lookups_ok] for
    the range-check lookup argument), and the vacuous complements
    [qlookup_gates_ok]/[qrunning_gates_ok]/[qbitshift_lookups_ok]/
    [qmulfixedrs_lookups_ok]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.
Require Garden.Halo2.halo2_gadgets.utilities.decompose_running_sum.
Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardRunningSums.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.

  Module OCT := OrchardCompletenessTables.

  (** ** The per-selector obligation Props

      The [Hgates]/[Hlookups] premises of [Complete.circuit_holds_intro] at
      [honest_assignment w], restricted to the enabled points of one
      guarding selector — the selector-keyed refinement of
      [OrchardCompletenessForward.family_gates_ok]/[family_lookups_ok]
      ([forward/api.v]): a family obligation follows from the selector
      obligations of the selectors enabled inside that family. *)

  Definition selector_gates_ok (sel : Selector.t) : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        forall gate,
          List.In gate system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint (OrchardHonestAssignment.honest_assignment w)
              (region, row) body.

  Definition selector_lookups_ok (sel : Selector.t) : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (region : RegionId.t) (row : Z),
        List.In (sel, region, row) enabled ->
        forall arg,
          List.In arg system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
            sel arg = true ->
          eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
            (region, row) 1024 arg.

  (** ** Decidable equality on lookup arguments

      Used by the [vm_compute] classification certificates: every lookup
      argument mentioning one of this file's selectors is pinned to its
      literal.  Constraint bodies use [OrchardDecidableEq.constraint_eqb]. *)

  Definition arg_pair_eq_dec (x y : Expression.t columns * Lookup.t)
      : {x = y} + {x <> y}.
  Proof.
    decide equality;
      first
        [ apply OrchardDecidableEq.lookup_eq_dec
        | apply OrchardDecidableEq.expression_eq_dec ].
  Defined.

  Definition arg_eq_dec (x y : LookupArgument.t columns)
      : {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply List.list_eq_dec.
    exact arg_pair_eq_dec.
  Defined.

  Definition arg_eqb : LookupArgument.t columns -> LookupArgument.t columns -> bool :=
    OrchardDecidableEq.dec_to_eqb arg_eq_dec.
  Definition arg_eqb_eq (x y : LookupArgument.t columns) :
      arg_eqb x y = true <-> x = y :=
    OrchardDecidableEq.dec_to_eqb_eq arg_eq_dec x y.

  (** ** The constraint and lookup-argument literals *)

  (** The single constraint of the short-lookup bitshift gate
      ([lookup_range_check.short_lookup_bitshift_gate] at [k = 10],
      column [A9]): [word · 2^10 · inv_two_pow_s = shifted]. *)
  Definition bitshift_body : Constraint.t columns :=
    Constraint.Equal
      (Expression.Product
        (Expression.Scaled (Expression.Advice Advice.A9 Rotation.prev) 1024)
        (Expression.Advice Advice.A9 Rotation.next))
      (Expression.Advice Advice.A9 Rotation.cur).

  (** The single constraint of the running-sum decomposition gate
      ([decompose_running_sum.range_check_gate] at
      [window_num_bits = 3], column [A4]): [z_i − 8·z_{i+1} ∈ [0, 8)]. *)
  Definition range_check_body : Constraint.t columns :=
    Constraint.Range
      (Expression.Sum
        (Expression.Advice Advice.A4 Rotation.cur)
        (Expression.Negated
          (Expression.Scaled (Expression.Advice Advice.A4 Rotation.next) 8)))
      8%nat.

  (** The range-check lookup argument ([lookup_range_check.configure] at
      [k = 10], column [A9], table [TableIdx]): the looked-up word is the
      running-sum step [z_i − 2^10·z_{i+1}] under [q_running], the element
      itself otherwise. *)
  Definition range_arg : LookupArgument.t columns := {|
    LookupArgument.pairs :=
      [(Expression.Product
          (Expression.Selector Selector.QLookup)
          (Expression.Sum
            (Expression.Product
              (Expression.Selector Selector.QRunning)
              (Expression.Sum
                (Expression.Advice Advice.A9 Rotation.cur)
                (Expression.Negated
                  (Expression.Scaled
                    (Expression.Advice Advice.A9 Rotation.next) 1024))))
            (Expression.Product
              (Expression.Sum
                (Expression.Constant 1)
                (Expression.Negated (Expression.Selector Selector.QRunning)))
              (Expression.Advice Advice.A9 Rotation.cur))),
        Lookup.TableIdx)];
  |}.

  (** ** Enabled-point domains

      Boolean characterizations of the [(region, row)] domains of the four
      selectors, certified below by one [vm_compute] scan of the enabled
      points each. *)

  (** The short 's'-bit range-check regions ([synthesize_short]): rows 0/1
      carry [QLookup], row 1 carries [QBitshift], [QRunning] is off. *)
  Definition short_region_b (region : RegionId.t) : bool :=
    match region with
    | RegionId.Merkle _ RegionId.Merkle.Region.RangeB1 => true
    | RegionId.Merkle _ RegionId.Merkle.Region.RangeB2 => true
    | RegionId.CommitIvk RegionId.CommitIvk.RangeB0 => true
    | RegionId.CommitIvk RegionId.CommitIvk.RangeB2 => true
    | RegionId.CommitIvk RegionId.CommitIvk.RangeD0 => true
    | RegionId.NoteCommit _ sub =>
        match sub with
        | RegionId.NoteCommit.RangeB0 | RegionId.NoteCommit.RangeB3
        | RegionId.NoteCommit.RangeD2 | RegionId.NoteCommit.RangeE0
        | RegionId.NoteCommit.RangeE1 | RegionId.NoteCommit.RangeG1
        | RegionId.NoteCommit.RangeH0 => true
        | RegionId.NoteCommit.YCanonicity _
            RegionId.NoteCommit.YCanonicity.RangeK0 => true
        | RegionId.NoteCommit.YCanonicity _
            RegionId.NoteCommit.YCanonicity.RangeK2 => true
        | _ => false
        end
    | _ => false
    end.

  Definition short_dom_b (region : RegionId.t) (row : Z) : bool :=
    ((row =? 0) || (row =? 1)) && short_region_b region.

  (** The strict running-sum lookup regions
      ([synthesize_running_lookup]): rows [0 .. count − 1] carry
      [QLookup] and [QRunning]; the trailing running sum sits at row
      [count]. *)
  Definition running_dom_b (region : RegionId.t) (row : Z) : bool :=
    match region with
    | RegionId.Nullifier RegionId.Nullifier.AlphaLookup =>
        (0 <=? row) && (row <? 13)
    | RegionId.CommitIvk RegionId.CommitIvk.AkLookup =>
        (0 <=? row) && (row <? 13)
    | RegionId.CommitIvk RegionId.CommitIvk.NkLookup =>
        (0 <=? row) && (row <? 14)
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowLookup) =>
        (0 <=? row) && (row <? 13)
    | RegionId.NoteCommit _ sub =>
        match sub with
        | RegionId.NoteCommit.YCanonicity _
            RegionId.NoteCommit.YCanonicity.JLookup =>
            (0 <=? row) && (row <? 25)
        | RegionId.NoteCommit.YCanonicity _
            RegionId.NoteCommit.YCanonicity.JPrimeLookup =>
            (0 <=? row) && (row <? 13)
        | RegionId.NoteCommit.XGDLookup => (0 <=? row) && (row <? 13)
        | RegionId.NoteCommit.XPKDLookup => (0 <=? row) && (row <? 14)
        | RegionId.NoteCommit.RhoLookup => (0 <=? row) && (row <? 14)
        | RegionId.NoteCommit.PsiLookup => (0 <=? row) && (row <? 13)
        | _ => false
        end
    | _ => false
    end.

  (** The base-8 running-sum decomposition regions of the fixed-base
      multiplications with a decomposed scalar. *)
  Definition rs_dom_b (region : RegionId.t) (row : Z) : bool :=
    match region with
    | RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete =>
        (0 <=? row) && (row <? 22)
    | RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete =>
        (0 <=? row) && (row <? 85)
    | _ => false
    end.

  (** Selector membership of the honest selector plane, in the spelling of
      [honest_assignment]'s selector field. *)
  Definition qmemb (sel : Selector.t) (region : RegionId.t) (row : Z)
      : bool :=
    Complete.enabled_memb OrchardHonestAssignment.selector_eqb
      OrchardHonestAssignment.region_eqb OrchardHonestAssignment.facts
      sel region row.

  (** The enabled points of one selector. *)
  Definition sel_pts (sel : Selector.t)
      : list (Selector.t * RegionId.t * Z) :=
    List.filter
      (fun '(sel', _, _) => OrchardDecidableEq.selector_eqb sel' sel)
      enabled.

  Lemma in_sel_pts (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    List.In (sel, region, row) (sel_pts sel).
  Proof.
    intros Hin.
    apply List.filter_In.
    split; [exact Hin | exact (OrchardDecidableEq.selector_eqb_refl sel)].
  Qed.

  (** ** The domain certificates *)

  Lemma qbitshift_dom_cert :
    List.forallb
      (fun '(_, region, row) => (row =? 1) && short_region_b region)
      (sel_pts Selector.QBitshift) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qlookup_dom_cert :
    List.forallb
      (fun '(_, region, row) =>
        (running_dom_b region row && qmemb Selector.QRunning region row)
        || (short_dom_b region row
            && negb (qmemb Selector.QRunning region row)))
      (sel_pts Selector.QLookup) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qrunning_dom_cert :
    List.forallb
      (fun '(_, region, row) =>
        running_dom_b region row && qmemb Selector.QLookup region row)
      (sel_pts Selector.QRunning) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qmulfixedrs_dom_cert :
    List.forallb
      (fun '(_, region, row) => rs_dom_b region row)
      (sel_pts Selector.QMulFixedRunningSum) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** The gate and lookup-argument classification certificates *)

  (** No gate constraint is guarded by [QLookup] or [QRunning] (they only
      appear inside the lookup argument). *)
  Lemma no_ql_qr_gate_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select sel _ =>
                negb (OrchardDecidableEq.selector_eqb sel Selector.QLookup
                      || OrchardDecidableEq.selector_eqb sel
                           Selector.QRunning)
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Every constraint guarded by [QBitshift] is the bitshift identity. *)
  Lemma qbitshift_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select sel body =>
                if OrchardDecidableEq.selector_eqb sel Selector.QBitshift
                then OrchardDecidableEq.constraint_eqb body bitshift_body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Every constraint guarded by [QMulFixedRunningSum] is the range-check
      identity or one of the coordinates-check constraints (whose forward
      lemmas belong to the fixed-base window family). *)
  Lemma qmulfixedrs_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select sel body =>
                if OrchardDecidableEq.selector_eqb sel
                     Selector.QMulFixedRunningSum
                then
                  OrchardDecidableEq.constraint_eqb body range_check_body
                  || List.existsb
                       (fun '(_, constraint') =>
                         OrchardDecidableEq.constraint_eqb
                           (Constraint.Select Selector.QMulFixedRunningSum
                             body)
                           constraint')
                       (Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
                          .running_sum_coordinates_check_gate)
                         .(Gate.constraints)
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Every lookup argument mentioning [QLookup] or [QRunning] is the
      range-check argument, and none mentions [QBitshift] or
      [QMulFixedRunningSum]. *)
  Lemma range_arg_cert :
    List.forallb
      (fun arg =>
        negb
          (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
             Selector.QLookup arg
           || Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QRunning arg)
        || arg_eqb arg range_arg)
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma no_mention_arg_cert :
    List.forallb
      (fun arg =>
        negb
          (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
             Selector.QBitshift arg)
        && negb
             (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                Selector.QMulFixedRunningSum arg))
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The loaded [TableIdx] table holds [i] at row [i] for
      [0 ≤ i < 1024]. *)
  Lemma table_idx_cert :
    List.forallb
      (fun i =>
        Complete.table_value OrchardHonestAssignment.lookup_eqb
          OrchardHonestAssignment.facts Lookup.TableIdx (Z.of_nat i)
        =? Z.of_nat i)
      (List.seq 0 1024) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Plane readers of the honest assignment *)

  Lemma advice_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) =
    OCT.advice_t w (OCT.tables_of w).
  Proof. reflexivity. Qed.

  Lemma selector_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.selector) =
    fun sel region row => if qmemb sel region row then 1 else 0.
  Proof. reflexivity. Qed.

  Lemma lookup_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.lookup) =
    fun column row =>
      Complete.table_value OrchardHonestAssignment.lookup_eqb
        OrchardHonestAssignment.facts column row.
  Proof. reflexivity. Qed.

  Lemma qmemb_of_in (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    qmemb sel region row = true.
  Proof.
    intros Hin.
    exact (Complete.enabled_memb_complete
      OrchardHonestAssignment.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardHonestAssignment.region_eqb OrchardDecidableEq.region_id_eqb_eq
      OrchardHonestAssignment.facts sel region row Hin).
  Qed.

  Lemma table_value_id (v : Z) :
    0 <= v < 1024 ->
    Complete.table_value OrchardHonestAssignment.lookup_eqb
      OrchardHonestAssignment.facts Lookup.TableIdx v = v.
  Proof.
    intros Hv.
    assert (Hin : List.In (Z.to_nat v) (List.seq 0 1024))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) table_idx_cert _ Hin) as Hf.
    cbn beta in Hf.
    rewrite Z2Nat.id in Hf by lia.
    exact (proj1 (Z.eqb_eq _ _) Hf).
  Qed.

  (** ** Domain and classification consumers *)

  Lemma qbitshift_dom (region : RegionId.t) (row : Z) :
    List.In (Selector.QBitshift, region, row) enabled ->
    (row =? 1) && short_region_b region = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ _) qbitshift_dom_cert _
      (in_sel_pts _ _ _ Hin)).
  Qed.

  Lemma qlookup_dom (region : RegionId.t) (row : Z) :
    List.In (Selector.QLookup, region, row) enabled ->
    (running_dom_b region row && qmemb Selector.QRunning region row)
    || (short_dom_b region row
        && negb (qmemb Selector.QRunning region row)) = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ _) qlookup_dom_cert _
      (in_sel_pts _ _ _ Hin)).
  Qed.

  Lemma qrunning_dom (region : RegionId.t) (row : Z) :
    List.In (Selector.QRunning, region, row) enabled ->
    running_dom_b region row && qmemb Selector.QLookup region row = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ _) qrunning_dom_cert _
      (in_sel_pts _ _ _ Hin)).
  Qed.

  Lemma qmulfixedrs_dom (region : RegionId.t) (row : Z) :
    List.In (Selector.QMulFixedRunningSum, region, row) enabled ->
    rs_dom_b region row = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ _) qmulfixedrs_dom_cert _
      (in_sel_pts _ _ _ Hin)).
  Qed.

  Lemma no_ql_qr_gate (sel : Selector.t) (gate : Gate.t columns) :
    sel = Selector.QLookup \/ sel = Selector.QRunning ->
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
      False.
  Proof.
    intros Hsel Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) no_ql_qr_gate_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    destruct Hsel as [-> | ->]; vm_compute in H2; discriminate H2.
  Qed.

  Lemma qbitshift_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QBitshift body)
        gate.(Gate.constraints) ->
      body = bitshift_body.
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qbitshift_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl Selector.QBitshift) in H2.
    exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
  Qed.

  (** Constraint bodies guarded by [QMulFixedRunningSum]: the range check,
      or a coordinates-check constraint (the fixed-base window family). *)
  Lemma qmulfixedrs_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QMulFixedRunningSum body)
        gate.(Gate.constraints) ->
      body = range_check_body \/
      List.In (Constraint.Select Selector.QMulFixedRunningSum body)
        (List.map snd
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
             .running_sum_coordinates_check_gate).(Gate.constraints)).
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qmulfixedrs_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl Selector.QMulFixedRunningSum)
      in H2.
    apply orb_true_iff in H2.
    destruct H2 as [H2 | H2].
    - left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right.
      apply List.existsb_exists in H2.
      destruct H2 as ([name' constraint'] & Hin' & Heq').
      apply OrchardDecidableEq.constraint_eqb_eq in Heq'.
      subst constraint'.
      change (Constraint.Select Selector.QMulFixedRunningSum body) with
        (snd (name', Constraint.Select Selector.QMulFixedRunningSum body)).
      apply List.in_map.
      exact Hin'.
  Qed.

  Lemma range_arg_eq (arg : LookupArgument.t columns) :
    List.In arg system.(ConstraintSystem.lookups) ->
    (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
       Selector.QLookup arg = true \/
     Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
       Selector.QRunning arg = true) ->
    arg = range_arg.
  Proof.
    intros Hin Hm.
    pose proof (proj1 (List.forallb_forall _ _) range_arg_cert _ Hin) as H1.
    cbn beta in H1.
    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
    - exfalso.
      apply negb_true_iff, orb_false_iff in H1.
      destruct H1 as [Hm1 Hm2].
      destruct Hm as [Hm | Hm]; congruence.
    - exact (proj1 (arg_eqb_eq _ _) H1).
  Qed.

  Lemma no_mention_arg (sel : Selector.t) (arg : LookupArgument.t columns) :
    sel = Selector.QBitshift \/ sel = Selector.QMulFixedRunningSum ->
    List.In arg system.(ConstraintSystem.lookups) ->
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel arg =
    true ->
    False.
  Proof.
    intros Hsel Hin Hm.
    pose proof (proj1 (List.forallb_forall _ _) no_mention_arg_cert _ Hin)
      as H1.
    cbn beta in H1.
    apply andb_true_iff in H1.
    destruct H1 as [H1 H2].
    destruct Hsel as [-> | ->];
      [rewrite Hm in H1; discriminate H1 | rewrite Hm in H2; discriminate H2].
  Qed.

  (** ** Arithmetic helpers *)

  Lemma p_big : 1024 < Primes.pallas_p.
  Proof. reflexivity. Qed.

  Lemma rot_cur (row : Z) : rotated_row row Rotation.cur = row.
  Proof. unfold rotated_row. cbn. apply Z.add_0_r. Qed.

  Lemma rot_next (row : Z) : rotated_row row Rotation.next = row + 1.
  Proof. reflexivity. Qed.

  Lemma rot_prev1 : rotated_row 1 Rotation.prev = 0.
  Proof. reflexivity. Qed.

  Lemma rot_cur1 : rotated_row 1 Rotation.cur = 1.
  Proof. reflexivity. Qed.

  Lemma rot_next1 : rotated_row 1 Rotation.next = 2.
  Proof. reflexivity. Qed.

  Lemma if_guard_true (row count x : Z) :
    0 <= row -> row <= count ->
    (if (0 <=? row) && (row <=? count) then x else 0) = x.
  Proof.
    intros H0 H1.
    rewrite (proj2 (Z.leb_le 0 row) H0), (proj2 (Z.leb_le row count) H1).
    reflexivity.
  Qed.

  Lemma div_bound (a b c : Z) :
    0 <= a < b * c -> 0 < b -> 0 < c -> 0 <= a / b < c.
  Proof.
    intros [Ha0 Ha1] Hb Hc.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma mul_bound (v b f : Z) :
    0 <= v < b -> 0 < f -> b * f <= 1024 -> 0 <= v * f < 1024.
  Proof.
    intros [Hv0 Hv1] Hf Hbf.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - apply Z.lt_le_trans with (b * f); [| exact Hbf].
      apply Z.mul_lt_mono_pos_r; lia.
  Qed.

  (** Bounds for the short range-check words: [a mod m] slices, [·/s]
      slices of a bounded value, and their bitshifted row-1 forms. *)

  Lemma bound_mod (a m : Z) :
    0 < m -> m <= 1024 -> 0 <= a mod m < 1024.
  Proof.
    intros Hm Hm'.
    pose proof (Z.mod_pos_bound a m Hm).
    lia.
  Qed.

  Lemma bound_mod_mul (a m f : Z) :
    0 < m -> 0 < f -> m * f <= 1024 -> 0 <= (a mod m) * f < 1024.
  Proof.
    intros Hm Hf Hmf.
    exact (mul_bound _ m _ (Z.mod_pos_bound a m Hm) Hf Hmf).
  Qed.

  Lemma bound_moddiv (a m s : Z) :
    0 < s -> 0 < m -> m <= s * 1024 -> 0 <= (a mod m) / s < 1024.
  Proof.
    intros Hs Hm Hms.
    pose proof (Z.mod_pos_bound a m Hm).
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma bound_moddiv_mul (a m s f : Z) :
    0 < s -> 0 < f -> 0 < m -> m <= s * (1024 / f) ->
    f * (1024 / f) <= 1024 ->
    0 <= ((a mod m) / s) * f < 1024.
  Proof.
    intros Hs Hf Hm Hms Hf'.
    pose proof (Z.mod_pos_bound a m Hm).
    apply (mul_bound _ (1024 / f) _); [| exact Hf | lia].
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma bound_div (b s B : Z) :
    0 <= b < B -> 0 < s -> B <= s * 1024 -> 0 <= b / s < 1024.
  Proof.
    intros [Hb0 Hb1] Hs HB.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma bound_div_mul (b s f B : Z) :
    0 <= b < B -> 0 < s -> 0 < f -> B <= s * (1024 / f) ->
    f * (1024 / f) <= 1024 ->
    0 <= (b / s) * f < 1024.
  Proof.
    intros [Hb0 Hb1] Hs Hf HB Hf'.
    apply (mul_bound _ (1024 / f) _); [| exact Hf | lia].
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  (** The five bitshift constants: [2^10 · 2^{−s} ≡ 2^{10−s}] mod p. *)

  Lemma inv4_eq :
    (1024 * Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4)
      mod Primes.pallas_p = 2 ^ 6 mod Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv5_eq :
    (1024 * Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5)
      mod Primes.pallas_p = 2 ^ 5 mod Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv6_eq :
    (1024 * Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_6)
      mod Primes.pallas_p = 2 ^ 4 mod Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv8_eq :
    (1024 * Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_8)
      mod Primes.pallas_p = 2 ^ 2 mod Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inv9_eq :
    (1024 * Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9)
      mod Primes.pallas_p = 2 mod Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  (** ** The evaluated words

      The three word evaluations, over abstract cell values: the bitshift
      product, the base-8 digit of the range check, and the two branches of
      the range-check lookup word. *)

  (** The bitshift gate at row 1 of a short range-check region. *)
  Lemma bitshift_gate_eval (w : HonestInput) (region : RegionId.t)
      (value factor inv : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region 0 = value ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region 1 = value * factor ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region 2 = inv ->
    (1024 * inv) mod Primes.pallas_p = factor mod Primes.pallas_p ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, 1) bitshift_body.
  Proof.
    intros Hc0 Hc1 Hc2 Hcert.
    cbn [eval_constraint eval_expression eval_selector bitshift_body].
    rewrite rot_prev1, rot_cur1, rot_next1.
    rewrite Hc0, Hc1, Hc2.
    unfold BinOp.mul, UnOp.from.
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    replace (value * 1024 * inv) with (value * (1024 * inv)) by ring.
    apply (Zdiv.Zmult_eqm Primes.pallas_p).
    - unfold Zdiv.eqm. reflexivity.
    - exact Hcert.
  Qed.

  (** The base-8 running-sum digit: [z − 8·(z/8) = z mod 8]. *)
  Lemma word8_eval (a : Z) :
    BinOp.sub (UnOp.from a) (BinOp.mul (UnOp.from (a / 8)) (UnOp.from 8)) =
    a mod 8.
  Proof.
    unfold BinOp.sub, BinOp.mul, UnOp.from.
    transitivity ((a - a / 8 * 8) mod Primes.pallas_p).
    - lazymatch goal with
      | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
      end.
      repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
      unfold Zdiv.eqm. reflexivity.
    - replace (a - a / 8 * 8) with (a mod 8)
        by (rewrite (Z.mod_eq a 8) by lia; ring).
      apply Z.mod_small.
      pose proof p_big.
      pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
      lia.
  Qed.

  (** The range-check gate at a running-sum row. *)
  Lemma range_gate_eval (w : HonestInput) (region : RegionId.t)
      (row a : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region row = a ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region (row + 1) = a / 8 ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_check_body.
  Proof.
    intros Hc Hn.
    cbn [eval_constraint eval_expression eval_selector range_check_body].
    rewrite rot_cur, rot_next.
    rewrite Hc, Hn.
    rewrite word8_eval.
    change (Z.of_nat 8) with 8.
    apply Z.mod_pos_bound.
    lia.
  Qed.

  (** The range-check lookup at a running row ([q_running] on): the word is
      [z − 2^10·(z/2^10) = z mod 2^10], a table row. *)
  Lemma running_lookup_eval (w : HonestInput) (region : RegionId.t)
      (row zc : Z) :
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = true ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region row = zc ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region (row + 1) = zc / 1024 ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hql Hqr Hc Hn.
    pose proof p_big as Hp.
    pose proof (Z.mod_pos_bound zc 1024 ltac:(lia)) as Hw.
    cbn [eval_lookup_argument range_arg LookupArgument.pairs].
    exists (zc mod 1024).
    split; [lia |].
    constructor; [| constructor].
    cbn [eval_expression eval_selector].
    rewrite selector_eq.
    cbn beta.
    rewrite Hql, Hqr.
    cbn iota.
    rewrite lookup_eq.
    cbn beta.
    rewrite table_value_id by lia.
    rewrite rot_cur, rot_next.
    rewrite Hc, Hn.
    unfold BinOp.mul, BinOp.add, BinOp.sub, UnOp.from.
    transitivity ((zc mod 1024) mod Primes.pallas_p);
      [| apply Z.mod_small; lia].
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    rewrite (Z.mod_eq zc 1024) by lia.
    unfold Zdiv.eqm.
    f_equal.
    ring.
  Qed.

  (** The range-check lookup at a short row ([q_running] off): the word is
      the checked element itself, bounded by the table size. *)
  Lemma short_lookup_eval (w : HonestInput) (region : RegionId.t)
      (row v : Z) :
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = false ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region row = v ->
    0 <= v < 1024 ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hql Hqr Hc Hv.
    pose proof p_big as Hp.
    cbn [eval_lookup_argument range_arg LookupArgument.pairs].
    exists v.
    split; [lia |].
    constructor; [| constructor].
    cbn [eval_expression eval_selector].
    rewrite selector_eq.
    cbn beta.
    rewrite Hql, Hqr.
    cbn iota.
    rewrite lookup_eq.
    cbn beta.
    rewrite table_value_id by lia.
    rewrite rot_cur.
    rewrite Hc.
    unfold BinOp.mul, BinOp.add, BinOp.sub, UnOp.from.
    transitivity (v mod Primes.pallas_p); [| apply Z.mod_small; lia].
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    f_equal.
    ring.
  Qed.

  (** ** Region-shaped cores: guarded running-sum cells *)

  Lemma running_cells_lookup (w : HonestInput) (region : RegionId.t)
      (row z0 count : Z) :
    0 <= row -> row < count ->
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = true ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region row =
      (if (0 <=? row) && (row <=? count) then z0 / 2 ^ (10 * row) else 0) ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region (row + 1) =
      (if (0 <=? row + 1) && (row + 1 <=? count)
       then z0 / 2 ^ (10 * (row + 1)) else 0) ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hrow Hcount Hql Hqr Hc Hn.
    rewrite if_guard_true in Hc by lia.
    rewrite if_guard_true in Hn by lia.
    assert (Hpow : 0 < 2 ^ (10 * row))
      by (apply Z.pow_pos_nonneg; lia).
    apply (running_lookup_eval w region row (z0 / 2 ^ (10 * row)));
      try assumption.
    rewrite Hn.
    rewrite Z.div_div by lia.
    f_equal.
    replace (10 * (row + 1)) with (10 * row + 10) by lia.
    rewrite Z.pow_add_r by lia.
    change (2 ^ 10) with 1024.
    reflexivity.
  Qed.

  Lemma rs_core (w : HonestInput) (region : RegionId.t) (row k : Z) :
    0 <= row ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region row = k / 8 ^ row ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region (row + 1) = k / 8 ^ (row + 1) ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_check_body.
  Proof.
    intros Hrow Hc Hn.
    assert (Hpow : 0 < 8 ^ row) by (apply Z.pow_pos_nonneg; lia).
    apply (range_gate_eval w region row (k / 8 ^ row)); [exact Hc |].
    rewrite Hn.
    rewrite Z.div_div by lia.
    f_equal.
    replace (row + 1) with (Z.succ row) by lia.
    rewrite Z.pow_succ_r by lia.
    ring.
  Qed.

  Lemma rs_cells_gate (w : HonestInput) (region : RegionId.t)
      (row k count : Z) :
    0 <= row -> row < count ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region row =
      (if (0 <=? row) && (row <=? count) then k / 8 ^ row else 0) ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region (row + 1) =
      (if (0 <=? row + 1) && (row + 1 <=? count) then k / 8 ^ (row + 1)
       else 0) ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_check_body.
  Proof.
    intros Hrow Hcount Hc Hn.
    rewrite if_guard_true in Hc by lia.
    rewrite if_guard_true in Hn by lia.
    exact (rs_core w region row k Hrow Hc Hn).
  Qed.

  Lemma rs_cells_gate_nat (w : HonestInput) (region : RegionId.t)
      (row k count : Z) :
    0 <= row -> row < count ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region row =
      (if (0 <=? row) && (row <=? count)
       then running_sum_at k (Z.to_nat row) else 0) ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 region (row + 1) =
      (if (0 <=? row + 1) && (row + 1 <=? count)
       then running_sum_at k (Z.to_nat (row + 1)) else 0) ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_check_body.
  Proof.
    intros Hrow Hcount Hc Hn.
    rewrite if_guard_true in Hc by lia.
    rewrite if_guard_true in Hn by lia.
    unfold running_sum_at in Hc, Hn.
    rewrite Z2Nat.id in Hc by lia.
    rewrite Z2Nat.id in Hn by lia.
    exact (rs_core w region row k Hrow Hc Hn).
  Qed.

  (** ** The Merkle [b]-word bound

      The boundary word 26 of every Merkle layer message is a genuine
      10-bit word: the messages are built by [words_le], whose entries are
      [mod 2^10] slices. *)

  Lemma words_le_In_bound (x : Z) (count : nat) (n : Z) :
    List.In x (SinsemillaSpec.words_le count n) -> 0 <= x < 2 ^ 10.
  Proof.
    revert n.
    induction count as [| count IH]; intros n Hin;
      cbn [SinsemillaSpec.words_le] in Hin.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + rewrite <- Heq.
        apply Z.mod_pos_bound.
        reflexivity.
      + exact (IH _ Hin).
  Qed.

  Lemma in_firstn {A : Type} (x : A) (n : nat) (l : list A) :
    List.In x (List.firstn n l) -> List.In x l.
  Proof.
    revert l.
    induction n as [| n IH]; intros l Hin.
    - contradiction.
    - destruct l as [| a l]; [contradiction |].
      destruct Hin as [-> | Hin]; [left; reflexivity |].
      right.
      exact (IH _ Hin).
  Qed.

  Lemma in_skipn {A : Type} (x : A) (n : nat) (l : list A) :
    List.In x (List.skipn n l) -> List.In x l.
  Proof.
    revert l.
    induction n as [| n IH]; intros l Hin.
    - exact Hin.
    - destruct l as [| a l]; [contradiction |].
      right.
      exact (IH _ Hin).
  Qed.

  Lemma split_pieces_incl (lens : list nat) (l : list Z) (x : Z) :
    List.In x
      (List.concat (OrchardAdviceMerkleSinsemilla.split_pieces lens l)) ->
    List.In x l.
  Proof.
    revert l.
    induction lens as [| len lens IH]; intros l Hin;
      cbn [OrchardAdviceMerkleSinsemilla.split_pieces List.concat] in Hin.
    - contradiction.
    - apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (in_firstn _ _ _ Hin).
      + exact (in_skipn _ len _ (IH _ Hin)).
  Qed.

  Lemma hash_data_words (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_words (OCT.hash_data_of Q pieces) = List.concat pieces.
  Proof.
    unfold OCT.hash_data_of.
    destruct (OCT.hash_go Q (List.concat pieces)) as [rows out].
    reflexivity.
  Qed.

  Lemma merkle_words_bound (w : HonestInput) (node : Z) (i : nat) (x : Z) :
    List.In x
      (List.concat
        (OrchardAdviceMerkleSinsemilla.split_pieces
          OrchardAdviceMerkleSinsemilla.merkle_lens
          (OCT.merkle_words_at w node i))) ->
    0 <= x < 2 ^ 10.
  Proof.
    intros Hin.
    apply split_pieces_incl in Hin.
    revert Hin.
    unfold OCT.merkle_words_at.
    destruct (path_bit w i); intros Hin;
      exact (words_le_In_bound _ _ _ Hin).
  Qed.

  Lemma layers_go_word_bound (w : HonestInput) (count : nat) :
    forall (node : Z) (i j : nat),
      0 <=
      List.nth 26
        (OCT.hd_words
          (OCT.lyd_hash (List.nth j (OCT.layers_go w node i count)
            OCT.layer0))) 0 < 2 ^ 10.
  Proof.
    induction count as [| count IH]; intros node i j;
      cbn [OCT.layers_go].
    - destruct j; cbn; lia.
    - destruct j as [| j].
      + cbn [List.nth OCT.lyd_hash].
        rewrite hash_data_words.
        destruct
          (List.nth_in_or_default 26
            (List.concat
              (OrchardAdviceMerkleSinsemilla.split_pieces
                OrchardAdviceMerkleSinsemilla.merkle_lens
                (OCT.merkle_words_at w node i))) 0) as [Hin | Heq].
        * exact (merkle_words_bound w node i _ Hin).
        * rewrite Heq. lia.
      + cbn [List.nth].
        apply IH.
  Qed.

  Lemma merkle_b_word_bound (w : HonestInput)
      (layer : RegionId.Merkle.Layer.t) :
    0 <=
    List.nth 26
      (OCT.hd_words
        (OCT.lyd_hash
          (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
            (OCT.t_layers (OCT.tables_of w)) OCT.layer0))) 0 < 2 ^ 10.
  Proof.
    (* Delta on [tables_of] and the projection only: the layer list surfaces
       as [layers_of w (Point.x …)] with every builder left folded, so the
       [apply] below unifies first-order on the [layers_go] head and never
       unrolls the 32-layer spine. *)
    cbv beta iota zeta delta [OCT.tables_of OCT.t_layers].
    unfold OCT.layers_of.
    apply layers_go_word_bound.
  Qed.

  (** ** The vacuous obligations

      [QLookup]/[QRunning] guard no gate constraint, and no lookup argument
      mentions [QBitshift] or [QMulFixedRunningSum]. *)

  Theorem qlookup_gates_ok : selector_gates_ok Selector.QLookup.
  Proof.
    intros w _ _ region row _ gate Hgate name body Hbody.
    destruct (no_ql_qr_gate Selector.QLookup gate (or_introl eq_refl) Hgate
      name body Hbody).
  Qed.

  Theorem qrunning_gates_ok : selector_gates_ok Selector.QRunning.
  Proof.
    intros w _ _ region row _ gate Hgate name body Hbody.
    destruct (no_ql_qr_gate Selector.QRunning gate (or_intror eq_refl) Hgate
      name body Hbody).
  Qed.

  Theorem qbitshift_lookups_ok : selector_lookups_ok Selector.QBitshift.
  Proof.
    intros w _ _ region row _ arg Harg Hm.
    destruct (no_mention_arg Selector.QBitshift arg (or_introl eq_refl)
      Harg Hm).
  Qed.

  Theorem qmulfixedrs_lookups_ok :
    selector_lookups_ok Selector.QMulFixedRunningSum.
  Proof.
    intros w _ _ region row _ arg Harg Hm.
    destruct (no_mention_arg Selector.QMulFixedRunningSum arg
      (or_intror eq_refl) Harg Hm).
  Qed.

  (** ** The bitshift gate

      At every enabled [QBitshift] point (row 1 of a short range-check
      region), the honest cells are [(value, value·2^{10−s},
      inv_two_pow_s)], and the gate identity is the modular equation
      [1024 · inv_two_pow_s ≡ 2^{10−s}]. *)

  Ltac bitshift_close inv_eq_lemma :=
    eapply bitshift_gate_eval;
      [ reflexivity | reflexivity | reflexivity | exact inv_eq_lemma ].

  Ltac bitshift_branch :=
    first
      [ bitshift_close inv4_eq
      | bitshift_close inv5_eq
      | bitshift_close inv6_eq
      | bitshift_close inv8_eq
      | bitshift_close inv9_eq ].

  Theorem qbitshift_gates_ok : selector_gates_ok Selector.QBitshift.
  Proof.
    intros w _ _ region row Hin gate Hgate name body Hbody.
    pose proof (qbitshift_body_eq gate Hgate name body Hbody) as ->.
    pose proof (qbitshift_dom region row Hin) as Hdom.
    apply andb_true_iff in Hdom; destruct Hdom as [Hrow Hsr].
    apply Z.eqb_eq in Hrow; subst row.
    destruct region as
      [ wr | layer mr | pr | vr | nr | sar | ar | cr | which ncr
      | | | | | | | gr ];
      try discriminate Hsr;
      [ destruct mr; try discriminate Hsr
      | destruct cr; try discriminate Hsr
      | destruct which; destruct ncr; try discriminate Hsr;
        try match goal with
            | s : RegionId.NoteCommit.YSubject.t,
              y : RegionId.NoteCommit.YCanonicity.t |- _ =>
                destruct y; try discriminate Hsr; destruct s
            end ];
      bitshift_branch.
  Qed.

  (** ** The running-sum range-check gate

      At every enabled [QMulFixedRunningSum] point the range-check
      constraint holds: the honest [A4] cells are the base-8 running sums
      [z_i = k / 8^i], so the checked word [z_i − 8·z_{i+1} = z_i mod 8]
      is a genuine base-8 digit.  The coordinates-check constraints under
      the same selector belong to the fixed-base window family
      ([qmulfixedrs_body_eq] separates the two). *)

  Lemma dom_bounds (row n : Z) :
    (0 <=? row) && (row <? n) = true -> 0 <= row /\ row < n.
  Proof.
    intros H; apply andb_true_iff in H; destruct H as [H0 H1].
    split; [ exact (proj1 (Z.leb_le _ _) H0) | exact (proj1 (Z.ltb_lt _ _) H1) ].
  Qed.

  Theorem qmulfixedrs_range_gates_ok :
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      forall (region : RegionId.t) (row : Z),
        List.In (Selector.QMulFixedRunningSum, region, row) enabled ->
        eval_constraint (OrchardHonestAssignment.honest_assignment w)
          (region, row) range_check_body.
  Proof.
    intros w _ _ region row Hin.
    pose proof (qmulfixedrs_dom region row Hin) as Hdom.
    destruct region as
      [ wr | layer mr | pr | vr | nr | sar | ar | cr | which ncr
      | | | | | | | gr ];
      try discriminate Hdom;
      [ destruct vr; try discriminate Hdom
      | destruct nr; try discriminate Hdom ].
    - (* ValueCommitVIncomplete: the 22-window magnitude decomposition. *)
      apply dom_bounds in Hdom.
      eapply (rs_cells_gate w _ row _ 22);
        [ exact (proj1 Hdom) | exact (proj2 Hdom)
        | reflexivity | reflexivity ].
    - (* BaseFieldIncomplete: the 85-window nullifier-scalar decomposition. *)
      apply dom_bounds in Hdom.
      eapply (rs_cells_gate_nat w _ row _ 85);
        [ exact (proj1 Hdom) | exact (proj2 Hdom)
        | reflexivity | reflexivity ].
  Qed.

  (** ** The range-check lookup: running rows

      At a [q_running] row the looked-up word is the telescoping step
      [z_i − 2^10·z_{i+1} = z_i mod 2^10]; the honest [A9] cells are the
      running sums of the region's decomposed value, so every step is a
      10-bit word — one branch per running-lookup region. *)

  Ltac run_site Hdom Hql Hqr cnt :=
    apply dom_bounds in Hdom;
    eapply (running_cells_lookup _ _ _ _ cnt);
      [ exact (proj1 Hdom) | exact (proj2 Hdom) | exact Hql | exact Hqr
      | reflexivity | reflexivity ].

  Lemma running_region_lookup (w : HonestInput) (region : RegionId.t)
      (row : Z) :
    running_dom_b region row = true ->
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = true ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hdom Hql Hqr.
    destruct region as
      [ wr | layer mr | pr | vr | nr | sar | ar | cr | which ncr
      | | | | | | | gr ];
      try discriminate Hdom;
      [ destruct nr; try discriminate Hdom
      | destruct ar as [ msub | | ]; try discriminate Hdom;
        destruct msub; try discriminate Hdom
      | destruct cr; try discriminate Hdom
      | destruct which; destruct ncr; try discriminate Hdom;
        try match goal with
            | s : RegionId.NoteCommit.YSubject.t,
              y : RegionId.NoteCommit.YCanonicity.t |- _ =>
                destruct y; try discriminate Hdom; destruct s
            end ];
      first
        [ run_site Hdom Hql Hqr 13
        | run_site Hdom Hql Hqr 14
        | run_site Hdom Hql Hqr 25 ].
  Qed.

  (** ** The range-check lookup: short rows

      At a short row ([q_running] off) the looked-up word is the checked
      element itself (row 0) or its bitshifted form (row 1); both are
      bounded by the table size because every short-checked value is a
      [mod]/[div] bit slice of bounded width. *)

  Lemma short_cells_lookup (w : HonestInput) (region : RegionId.t)
      (row value factor : Z) :
    (row =? 0) || (row =? 1) = true ->
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = false ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region 0 = value ->
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A9 region 1 = value * factor ->
    0 <= value < 1024 ->
    0 <= value * factor < 1024 ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hrow Hql Hqr Hc0 Hc1 Hb0 Hb1.
    apply orb_true_iff in Hrow.
    destruct Hrow as [Hrow | Hrow]; apply Z.eqb_eq in Hrow; subst row.
    - exact (short_lookup_eval w region 0 value Hql Hqr Hc0 Hb0).
    - exact (short_lookup_eval w region 1 (value * factor) Hql Hqr Hc1 Hb1).
  Qed.

  Ltac short_bound :=
    first
      [ solve [ apply bound_mod; lia ]
      | solve [ apply bound_mod_mul; lia ]
      | solve [ apply bound_moddiv; lia ]
      | solve [ apply bound_moddiv_mul; lia ]
      | solve [ eapply bound_div;
          [ apply merkle_b_word_bound | lia | lia ] ]
      | solve [ eapply bound_div_mul;
          [ apply merkle_b_word_bound | lia | lia | lia | lia ] ] ].

  Lemma short_region_lookup (w : HonestInput) (region : RegionId.t)
      (row : Z) :
    short_dom_b region row = true ->
    qmemb Selector.QLookup region row = true ->
    qmemb Selector.QRunning region row = false ->
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (region, row) 1024 range_arg.
  Proof.
    intros Hdom Hql Hqr.
    unfold short_dom_b in Hdom; apply andb_true_iff in Hdom;
      destruct Hdom as [Hrow Hsr].
    destruct region as
      [ wr | layer mr | pr | vr | nr | sar | ar | cr | which ncr
      | | | | | | | gr ];
      try discriminate Hsr;
      [ destruct mr; try discriminate Hsr
      | destruct cr; try discriminate Hsr
      | destruct which; destruct ncr; try discriminate Hsr;
        try match goal with
            | s : RegionId.NoteCommit.YSubject.t,
              y : RegionId.NoteCommit.YCanonicity.t |- _ =>
                destruct y; try discriminate Hsr; destruct s
            end ];
      (eapply (short_cells_lookup w _ row);
        [ exact Hrow | exact Hql | exact Hqr
        | reflexivity | reflexivity | short_bound | short_bound ]).
  Qed.

  (** ** The range-check lookup theorems *)

  Theorem qlookup_lookups_ok : selector_lookups_ok Selector.QLookup.
  Proof.
    intros w _ _ region row Hin arg Harg Hm.
    rewrite (range_arg_eq arg Harg (or_introl Hm)).
    pose proof (qlookup_dom region row Hin) as Hdom.
    pose proof (qmemb_of_in _ _ _ Hin) as Hql.
    apply orb_true_iff in Hdom.
    destruct Hdom as [Hdom | Hdom]; apply andb_true_iff in Hdom;
      destruct Hdom as [Hdom Hqr].
    - exact (running_region_lookup w region row Hdom Hql Hqr).
    - apply negb_true_iff in Hqr.
      exact (short_region_lookup w region row Hdom Hql Hqr).
  Qed.

  Theorem qrunning_lookups_ok : selector_lookups_ok Selector.QRunning.
  Proof.
    intros w _ _ region row Hin arg Harg Hm.
    rewrite (range_arg_eq arg Harg (or_intror Hm)).
    pose proof (qrunning_dom region row Hin) as Hdom.
    apply andb_true_iff in Hdom; destruct Hdom as [Hdom Hql].
    exact (running_region_lookup w region row Hdom Hql
      (qmemb_of_in _ _ _ Hin)).
  Qed.

End OrchardForwardRunningSums.
