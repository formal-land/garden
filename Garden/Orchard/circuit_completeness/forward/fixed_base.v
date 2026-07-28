(** * Forward gate lemmas: the fixed-base window gates

    The symbolic per-gate forward lemmas of the C2 completeness campaign
    ([forward/api.v]) for the four fixed-base multiplication selectors:

    - [QMulFixedRunningSum] — the coordinates-check gate of [mul_fixed.v]
      (window read as the running-sum step [z_i − 8·z_{i+1}]) together with
      the base-8 digit range check of [decompose_running_sum.v], enabled on
      the [value_commit_v] short leg and the [NullifierK] base-field leg;
    - [QMulFixedFull] — the full-width gate of [mul_fixed/full_width.v]
      (window read directly, plus its window range check), enabled on the
      five 85-window fixed-base legs;
    - [QMulFixedShort] — the magnitude/sign gate of [mul_fixed/short.v] at
      the [value_commit_v] MSB row;
    - [QMulFixedBaseField] — the canonicity gate of
      [mul_fixed/base_field_elem.v] at the nullifier canonicity row.

    The obligations are stated per guarding selector
    ([selector_gates_ok] / [selector_lookups_ok] mirror the per-family
    obligations of [forward/api.v] with the point's selector fixed instead
    of its region family; the family joins follow by case analysis on the
    selector).  The honest cells are the [tables.v] leg records
    ([leg_of]: window points by Lagrange interpolation and the pasted
    square-root witnesses of the window-sign certificates), so each gate
    identity is exact: the x-coordinate is the interpolation polynomial at
    the window digit, [u² − y = z] recovers the witnessed root, the window
    points lie on the curve by the [fixed_base_certs.v] tables, and the
    running-sum and canonicity constraints are integer div/mod identities.
    No configured lookup argument mentions a fixed-base selector, so the
    lookup obligations are vacuous. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem.
Require Garden.Halo2.halo2_gadgets.utilities.decompose_running_sum.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.fixed_base_certs.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardFixedBase.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardForwardFixedBaseCerts.

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

  (** ** The gate bodies

      The constraint bodies of the four fixed-base gates, spelled over the
      shared cell expressions.  The [vm_compute] certificates below pin the
      configured system's guarded constraints to exactly these values. *)

  Definition x_p_e : Expression.t columns :=
    Expression.Advice Advice.A0 Rotation.cur.
  Definition y_p_e : Expression.t columns :=
    Expression.Advice Advice.A1 Rotation.cur.
  Definition u_e : Expression.t columns :=
    Expression.Advice Advice.A5 Rotation.cur.
  Definition zf_e : Expression.t columns :=
    Expression.Fixed Fixed.FixedZ Rotation.cur.

  (** The full-width window: the digit cell itself. *)
  Definition w_full_e : Expression.t columns :=
    Expression.Advice Advice.A4 Rotation.cur.

  (** The running-sum window: [z_cur − 8·z_next]. *)
  Definition w_rs_e : Expression.t columns :=
    Expression.Sum (Expression.Advice Advice.A4 Rotation.cur)
      (Expression.Negated
        (Expression.Scaled (Expression.Advice Advice.A4 Rotation.next) 8)).

  (** The three coordinates-check bodies ([mul_fixed.coords_check]),
      parameterized by the window expression. *)
  Definition check_x_body (win : Expression.t columns)
      : Constraint.t columns :=
    Constraint.Equal
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.interpolated_x win)
      x_p_e.
  Definition check_y_body : Constraint.t columns :=
    Constraint.Equal
      (Expression.Sum (Expression.Product u_e u_e)
        (Expression.Negated y_p_e))
      zf_e.
  Definition on_curve_body : Constraint.t columns :=
    Constraint.EqualZeroToPrecise
      (Expression.Sum
        (Expression.Sum (Expression.Product y_p_e y_p_e)
          (Expression.Negated
            (Expression.Product (Expression.Product x_p_e x_p_e) x_p_e)))
        (Expression.Negated (Expression.Constant 5))).

  (** The window range checks: the full-width gate's own range constraint
      and the [decompose_running_sum] digit range. *)
  Definition range_full_body : Constraint.t columns :=
    Constraint.Range w_full_e 8.
  Definition range_rs_body : Constraint.t columns :=
    Constraint.Range w_rs_e 8.

  (** The short gate's four bodies ([mul_fixed/short.v]). *)
  Definition sgn_e : Expression.t columns :=
    Expression.Advice Advice.A4 Rotation.cur.
  Definition y_a3_e : Expression.t columns :=
    Expression.Advice Advice.A3 Rotation.cur.
  Definition last_window_body : Constraint.t columns :=
    Constraint.Boolean (Expression.Advice Advice.A5 Rotation.cur).
  Definition sign_check_body : Constraint.t columns :=
    Constraint.Equal (Expression.Product sgn_e sgn_e)
      (Expression.Constant 1).
  Definition y_check_body : Constraint.t columns :=
    Constraint.Either (Constraint.Equal y_p_e y_a3_e)
      (Constraint.EqualZeroToPrecise (Expression.Sum y_p_e y_a3_e)).
  Definition negation_check_body : Constraint.t columns :=
    Constraint.Equal (Expression.Product sgn_e y_p_e) y_a3_e.

  (** The base-field canonicity gate's eight bodies
      ([mul_fixed/base_field_elem.v]), read at the canonicity row. *)
  Definition al_e : Expression.t columns :=
    Expression.Advice Advice.A6 Rotation.prev.
  Definition z84_e : Expression.t columns :=
    Expression.Advice Advice.A8 Rotation.prev.
  Definition a1_e : Expression.t columns :=
    Expression.Advice Advice.A7 Rotation.cur.
  Definition a2_e : Expression.t columns :=
    Expression.Advice Advice.A8 Rotation.cur.
  Definition a0p_e : Expression.t columns :=
    Expression.Advice Advice.A6 Rotation.cur.
  Definition z13_e : Expression.t columns :=
    Expression.Advice Advice.A6 Rotation.next.
  Definition z44_e : Expression.t columns :=
    Expression.Advice Advice.A7 Rotation.next.
  Definition z43_e : Expression.t columns :=
    Expression.Advice Advice.A8 Rotation.next.
  Definition alpha0_e : Expression.t columns :=
    Expression.Sum al_e
      (Expression.Negated (Expression.Scaled z84_e (2 ^ 252))).
  Definition hi120_e : Expression.t columns :=
    Expression.Sum z44_e
      (Expression.Negated
        (Expression.Product z84_e (Expression.Constant (2 ^ 120)))).
  Definition a43_e : Expression.t columns :=
    Expression.Sum z43_e
      (Expression.Negated (Expression.Scaled z44_e 8)).

  Definition canon_1_body : Constraint.t columns :=
    Constraint.Either (Constraint.EqualZeroToPrecise a2_e)
      (Constraint.EqualZeroToPrecise a1_e).
  Definition canon_2_body : Constraint.t columns :=
    Constraint.Either (Constraint.EqualZeroToPrecise a2_e)
      (Constraint.EqualZeroToPrecise hi120_e).
  Definition canon_3_body : Constraint.t columns :=
    Constraint.Either (Constraint.EqualZeroToPrecise a2_e)
      (Constraint.Boolean a43_e).
  Definition canon_4_body : Constraint.t columns :=
    Constraint.Either (Constraint.EqualZeroToPrecise a2_e)
      (Constraint.EqualZeroToPrecise z13_e).
  Definition canon_5_body : Constraint.t columns :=
    Constraint.Range a1_e 4.
  Definition canon_6_body : Constraint.t columns :=
    Constraint.Boolean a2_e.
  Definition canon_7_body : Constraint.t columns :=
    Constraint.Equal z84_e
      (Expression.Sum a1_e (Expression.Scaled a2_e 4)).
  Definition canon_8_body : Constraint.t columns :=
    Constraint.Equal a0p_e
      (Expression.Sum
        (Expression.Sum alpha0_e (Expression.Constant (2 ^ 130)))
        (Expression.Negated (Expression.Constant Primes.t_p))).

  (** ** The gate-classification certificates

      Every constraint of the configured system guarded by a fixed-base
      selector is one of that selector's gate bodies. *)

  Lemma qmff_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s Selector.QMulFixedFull
                then
                  OrchardDecidableEq.constraint_eqb body (check_x_body w_full_e)
                  || OrchardDecidableEq.constraint_eqb body check_y_body
                  || OrchardDecidableEq.constraint_eqb body on_curve_body
                  || OrchardDecidableEq.constraint_eqb body range_full_body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qmfrs_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s
                     Selector.QMulFixedRunningSum
                then
                  OrchardDecidableEq.constraint_eqb body (check_x_body w_rs_e)
                  || OrchardDecidableEq.constraint_eqb body check_y_body
                  || OrchardDecidableEq.constraint_eqb body on_curve_body
                  || OrchardDecidableEq.constraint_eqb body range_rs_body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qmfs_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s Selector.QMulFixedShort
                then
                  OrchardDecidableEq.constraint_eqb body last_window_body
                  || OrchardDecidableEq.constraint_eqb body sign_check_body
                  || OrchardDecidableEq.constraint_eqb body y_check_body
                  || OrchardDecidableEq.constraint_eqb body negation_check_body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma qmfbf_body_cert :
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s
                     Selector.QMulFixedBaseField
                then
                  OrchardDecidableEq.constraint_eqb body canon_1_body
                  || OrchardDecidableEq.constraint_eqb body canon_2_body
                  || OrchardDecidableEq.constraint_eqb body canon_3_body
                  || OrchardDecidableEq.constraint_eqb body canon_4_body
                  || OrchardDecidableEq.constraint_eqb body canon_5_body
                  || OrchardDecidableEq.constraint_eqb body canon_6_body
                  || OrchardDecidableEq.constraint_eqb body canon_7_body
                  || OrchardDecidableEq.constraint_eqb body canon_8_body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Classification consumers *)

  Lemma fb_dom (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    fb_shape (sel, region, row) = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall _ _) fb_shape_ok _ Hin).
  Qed.

  Lemma qmff_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QMulFixedFull body)
        gate.(Gate.constraints) ->
      body = check_x_body w_full_e \/ body = check_y_body \/
      body = on_curve_body \/ body = range_full_body.
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qmff_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl Selector.QMulFixedFull)
      in H2.
    apply orb_true_iff in H2; destruct H2 as [H2 | H2];
      [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
        [apply orb_true_iff in H2; destruct H2 as [H2 | H2] |] |].
    - left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; right. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
  Qed.

  Lemma qmfrs_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QMulFixedRunningSum body)
        gate.(Gate.constraints) ->
      body = check_x_body w_rs_e \/ body = check_y_body \/
      body = on_curve_body \/ body = range_rs_body.
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qmfrs_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl
      Selector.QMulFixedRunningSum) in H2.
    apply orb_true_iff in H2; destruct H2 as [H2 | H2];
      [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
        [apply orb_true_iff in H2; destruct H2 as [H2 | H2] |] |].
    - left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; right. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
  Qed.

  Lemma qmfs_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QMulFixedShort body)
        gate.(Gate.constraints) ->
      body = last_window_body \/ body = sign_check_body \/
      body = y_check_body \/ body = negation_check_body.
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qmfs_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl Selector.QMulFixedShort)
      in H2.
    apply orb_true_iff in H2; destruct H2 as [H2 | H2];
      [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
        [apply orb_true_iff in H2; destruct H2 as [H2 | H2] |] |].
    - left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; left. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
    - right; right; right. exact (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _) H2).
  Qed.

  Lemma qmfbf_body_eq (gate : Gate.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    forall (name : option string) (body : Constraint.t columns),
      List.In (name, Constraint.Select Selector.QMulFixedBaseField body)
        gate.(Gate.constraints) ->
      body = canon_1_body \/ body = canon_2_body \/ body = canon_3_body \/
      body = canon_4_body \/ body = canon_5_body \/ body = canon_6_body \/
      body = canon_7_body \/ body = canon_8_body.
  Proof.
    intros Hgate name body Hbody.
    pose proof (proj1 (List.forallb_forall _ _) qmfbf_body_cert _ Hgate)
      as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hbody) as H2.
    cbn beta iota in H2.
    rewrite (OrchardDecidableEq.selector_eqb_refl
      Selector.QMulFixedBaseField) in H2.
    apply orb_true_iff in H2; destruct H2 as [H2 | H2];
      [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
        [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
          [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
            [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
              [apply orb_true_iff in H2; destruct H2 as [H2 | H2];
                [apply orb_true_iff in H2; destruct H2 as [H2 | H2] |]
              |] |] |] |] |];
      apply (proj1 (OrchardDecidableEq.constraint_eqb_eq _ _)) in H2; subst body; tauto.
  Qed.

  (** ** Arithmetic and plane helpers *)

  Lemma p_pos : 0 < Primes.pallas_p.
  Proof. reflexivity. Qed.

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

  Lemma guard2_true (lo hi off : Z) :
    lo <= off -> off < hi -> ((lo <=? off) && (off <? hi))%bool = true.
  Proof.
    intros H0 H1.
    apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; assumption.
  Qed.

  Lemma guard2le_true (lo hi off : Z) :
    lo <= off -> off <= hi -> ((lo <=? off) && (off <=? hi))%bool = true.
  Proof.
    intros H0 H1.
    apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.leb_le]; assumption.
  Qed.

  Lemma from_0 : UnOp.from 0 = 0.
  Proof. unfold UnOp.from. apply Zmod_0_l. Qed.

  Lemma from_small (v : Z) :
    0 <= v < Primes.pallas_p -> UnOp.from v = v.
  Proof. intros Hv. unfold UnOp.from. apply Z.mod_small. exact Hv. Qed.

  Lemma isbool_from (v : Z) :
    v = 0 \/ v = 1 -> IsBool.t (UnOp.from v).
  Proof. intros [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma add_neg_zero (y : Z) :
    BinOp.add (UnOp.from (BinOp.sub 0 y)) (UnOp.from y) = 0.
  Proof.
    transitivity (UnOp.from 0); [| exact from_0].
    mod_ring_solve.
  Qed.

  Lemma neg_one_mul (y : Z) :
    BinOp.mul (UnOp.from (Primes.pallas_p - 1))
      (UnOp.from (BinOp.sub 0 y)) = UnOp.from y.
  Proof.
    unfold BinOp.mul, BinOp.sub, UnOp.from.
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    replace ((Primes.pallas_p - 1) * (0 - y))
      with (y + (- y) * Primes.pallas_p) by ring.
    apply Z_mod_plus_full.
  Qed.

  (** [z = z mod m + (z / m)·m], in the field. *)
  Lemma div_mod_recomb (a m : Z) (Hm : 0 < m) :
    UnOp.from a =
    BinOp.add (UnOp.from (a mod m))
      (BinOp.mul (UnOp.from (a / m)) (UnOp.from m)).
  Proof.
    assert (Ha : a = a mod m + a / m * m)
      by (rewrite Z.mod_eq by lia; ring).
    rewrite Ha at 1.
    mod_ring_solve.
  Qed.

  (** ** Certificate consumers *)

  (** The window rows of a certified region read the eight Lagrange
      coefficients and the [z] offset from the honest fixed plane. *)
  Lemma window_row_facts (w : HonestInput) (tbl : EccSpec.fixed_table)
      (region : RegionId.t) (count i : nat)
      (Hcert : List.forallb (window_row_check tbl region)
        (List.seq 0 count) = true)
      (Hi : (i < count)%nat) :
    (List.length (EccSpec.fw_coeffs (wdw tbl i)) = 8)%nat /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs0 region (Z.of_nat i) =
      List.nth 0 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs1 region (Z.of_nat i) =
      List.nth 1 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs2 region (Z.of_nat i) =
      List.nth 2 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs3 region (Z.of_nat i) =
      List.nth 3 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs4 region (Z.of_nat i) =
      List.nth 4 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs5 region (Z.of_nat i) =
      List.nth 5 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs6 region (Z.of_nat i) =
      List.nth 6 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.LagrangeCoeffs7 region (Z.of_nat i) =
      List.nth 7 (EccSpec.fw_coeffs (wdw tbl i)) 0 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.fixed)
      Fixed.FixedZ region (Z.of_nat i) = EccSpec.fw_z (wdw tbl i).
  Proof.
    assert (Hin : List.In i (List.seq 0 count))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) Hcert _ Hin) as Hf.
    unfold window_row_check in Hf.
    cbv zeta in Hf.
    apply andb_true_iff in Hf; destruct Hf as [Hf Hz].
    apply andb_true_iff in Hf; destruct Hf as [Hf H7].
    apply andb_true_iff in Hf; destruct Hf as [Hf H6].
    apply andb_true_iff in Hf; destruct Hf as [Hf H5].
    apply andb_true_iff in Hf; destruct Hf as [Hf H4].
    apply andb_true_iff in Hf; destruct Hf as [Hf H3].
    apply andb_true_iff in Hf; destruct Hf as [Hf H2].
    apply andb_true_iff in Hf; destruct Hf as [Hf H1].
    apply andb_true_iff in Hf; destruct Hf as [Hlen H0].
    refine (conj (proj1 (Nat.eqb_eq _ _) Hlen) _).
    exact (conj (proj1 (Z.eqb_eq _ _) H0)
      (conj (proj1 (Z.eqb_eq _ _) H1)
      (conj (proj1 (Z.eqb_eq _ _) H2)
      (conj (proj1 (Z.eqb_eq _ _) H3)
      (conj (proj1 (Z.eqb_eq _ _) H4)
      (conj (proj1 (Z.eqb_eq _ _) H5)
      (conj (proj1 (Z.eqb_eq _ _) H6)
      (conj (proj1 (Z.eqb_eq _ _) H7)
        (proj1 (Z.eqb_eq _ _) Hz))))))))).
  Qed.

  (** The certified (window, digit) points satisfy the curve equation. *)
  Lemma oncurve_fact (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (count i : nat) (d : Z)
      (Hcert : List.forallb
        (fun i =>
          List.forallb (oncurve_entry_check tbl roots i) (List.seq 0 8))
        (List.seq 0 count) = true)
      (Hi : (i < count)%nat) (Hd : 0 <= d < 8) :
    let u := List.nth (Z.to_nat d) (List.nth i roots []) 0 in
    let P := EccSpec.fixed_window_point (wdw tbl i) d u in
    Point.y P *F Point.y P -F
      (Point.x P *F Point.x P *F Point.x P +F 5) = 0.
  Proof.
    cbv zeta.
    assert (Hin : List.In i (List.seq 0 count))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) Hcert _ Hin) as Hf.
    cbn beta in Hf.
    assert (Hind : List.In (Z.to_nat d) (List.seq 0 8))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) Hf _ Hind) as Hg.
    unfold oncurve_entry_check in Hg.
    cbv zeta in Hg.
    rewrite Z2Nat.id in Hg by lia.
    exact (proj1 (Z.eqb_eq _ _) Hg).
  Qed.

  (** The leg record's cells at window [i]: the window point recovered from
      the pasted root at the scalar's digit. *)
  Lemma leg_cells (tbl : EccSpec.fixed_table) (roots : list (list Z))
      (scalar : Z) (i : nat) (Hi : (i < List.length tbl)%nat) :
    let d := EccSpec.window_digit scalar i in
    let u := List.nth (Z.to_nat d) (List.nth i roots []) 0 in
    let P := EccSpec.fixed_window_point (wdw tbl i) d u in
    List.nth i (OCT.lg_px (OCT.leg_of tbl roots scalar)) 0 = Point.x P /\
    List.nth i (OCT.lg_py (OCT.leg_of tbl roots scalar)) 0 = Point.y P /\
    List.nth i (OCT.lg_us (OCT.leg_of tbl roots scalar)) 0 = u.
  Proof.
    cbv zeta.
    unfold OCT.leg_of.
    cbv zeta.
    cbn [OCT.lg_px OCT.lg_py OCT.lg_us].
    unfold OCT.roots_us.
    rewrite !List.map_map.
    rewrite !(nth_map_seq _ (List.length tbl)) by exact Hi.
    unfold wdw.
    repeat split; reflexivity.
  Qed.

  (** ** Table projections and plane readers (definitional) *)

  (** The cell-shape discharge for the fixed-base plane readers: reduce the
      advice dispatch and the hoisted-record projections to one spelling on
      both sides, then compare syntactically.  A bare [reflexivity] diverges
      here — with the head constants differing, unification's alternating
      unfolding forces [t_nullifier_scalar (tables_of w)] past the projection
      and normalizes the symbolic Poseidon round chain (see
      [docs/compile-performance.md]).  [cbn] restricted to the region names,
      the advice/table dispatch and the leg/scalar projections leaves the
      Poseidon and leg folds stuck, so both sides become the same term. *)
  Ltac cell_refl :=
    cbn [R_sa R_vcr R_civk R_nco R_ncn R_vcv R_nk R_msb R_canon
         OrchardHonestAssignment.honest_assignment
         OCT.advice_t OCT.advice_ecc_t OCT.advice_nullifier_t OCT.tables_of
         OCT.t_sa_leg OCT.t_vcr_leg OCT.t_civkr_leg OCT.t_nco_leg
         OCT.t_ncn_leg OCT.t_vcv_leg OCT.t_nk_leg OCT.t_nullifier_scalar
         OCT.t_hash2 OCT.t_vcv_mul OCT.vcv_y_var_t];
    reflexivity.

  Lemma nscalar_eq (w : HonestInput) :
    OCT.t_nullifier_scalar (OCT.tables_of w) =
    BinOp.add (OCT.t_hash2 (OCT.tables_of w)) (hi_psi_old w).
  Proof. cell_refl. Qed.

  Lemma nk_leg_eq (w : HonestInput) :
    OCT.t_nk_leg (OCT.tables_of w) =
    OCT.leg_of OrchardAdvicePoseidonNullifier.nk_table
      NullifierKWindowSignCert.root_table
      (OCT.t_nullifier_scalar (OCT.tables_of w)).
  Proof. cell_refl. Qed.

  Lemma sa_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_sa off =
    OCT.fb_full_advice_t
      (OCT.leg_of OrchardAdviceEccMuls.tbl_spend_auth
        SpendAuthGWindowSignCert.root_table (hi_alpha w))
      (hi_alpha w) 85 col off.
  Proof. cell_refl. Qed.

  Lemma vcr_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_vcr off =
    OCT.fb_full_advice_t
      (OCT.leg_of OrchardAdviceEccMuls.tbl_value_commit_r
        ValueCommitRWindowSignCert.root_table (hi_rcv w))
      (hi_rcv w) 85 col off.
  Proof. cell_refl. Qed.

  Lemma civk_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_civk off =
    OCT.fb_full_advice_t
      (OCT.leg_of (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        CommitIvkRWindowSignCert.root_table (hi_rivk w))
      (hi_rivk w) 85 col off.
  Proof. cell_refl. Qed.

  Lemma nco_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_nco off =
    OCT.fb_full_advice_t
      (OCT.leg_of OrchardAdviceEccMuls.tbl_note_commit_r
        NoteCommitRWindowSignCert.root_table (hi_rcm_old w))
      (hi_rcm_old w) 85 col off.
  Proof. cell_refl. Qed.

  Lemma ncn_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_ncn off =
    OCT.fb_full_advice_t
      (OCT.leg_of OrchardAdviceEccMuls.tbl_note_commit_r
        NoteCommitRWindowSignCert.root_table (hi_rcm_new w))
      (hi_rcm_new w) 85 col off.
  Proof. cell_refl. Qed.

  Lemma vcv_adv (w : HonestInput) (col : Advice.t) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      col R_vcv off =
    OCT.fb_short_advice_t
      (OCT.leg_of OrchardAdviceEccMuls.tbl_value_commit_v
        ValueCommitVWindowSignCert.root_table (magnitude w))
      (magnitude w) 22 col off.
  Proof. cell_refl. Qed.

  (** The NullifierK base-field leg cells, in the reader's guarded form. *)
  Lemma nk_cell_A0 (w : HonestInput) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A0 R_nk off =
    (if ((0 <=? off) && (off <=? 84))%bool
     then List.nth (Z.to_nat off)
       (OCT.lg_px (OCT.t_nk_leg (OCT.tables_of w))) 0
     else 0).
  Proof. cell_refl. Qed.

  Lemma nk_cell_A1 (w : HonestInput) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A1 R_nk off =
    (if ((0 <=? off) && (off <=? 84))%bool
     then List.nth (Z.to_nat off)
       (OCT.lg_py (OCT.t_nk_leg (OCT.tables_of w))) 0
     else 0).
  Proof. cell_refl. Qed.

  Lemma nk_cell_A5 (w : HonestInput) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A5 R_nk off =
    (if ((0 <=? off) && (off <=? 84))%bool
     then List.nth (Z.to_nat off)
       (OCT.lg_us (OCT.t_nk_leg (OCT.tables_of w))) 0
     else 0).
  Proof. cell_refl. Qed.

  Lemma nk_cell_A4 (w : HonestInput) (off : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 R_nk off =
    (if ((0 <=? off) && (off <=? 85))%bool
     then running_sum_at (OCT.t_nullifier_scalar (OCT.tables_of w))
       (Z.to_nat off)
     else 0).
  Proof. cell_refl. Qed.

  (** The [value_commit_v] MSB row cells. *)
  Lemma msb_cells (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A1 R_msb 1 =
      (if sign w =? 1
       then Point.y (OCT.t_vcv_mul (OCT.tables_of w))
       else 0 -F Point.y (OCT.t_vcv_mul (OCT.tables_of w))) /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A3 R_msb 1 = Point.y (OCT.t_vcv_mul (OCT.tables_of w)) /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A4 R_msb 1 = sign w /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A5 R_msb 1 = magnitude w / 8 ^ 21.
  Proof. repeat split; cell_refl. Qed.

  (** The nullifier canonicity rows. *)
  Lemma canon_cells (w : HonestInput) :
    let N := OCT.t_nullifier_scalar (OCT.tables_of w) in
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A6 R_canon 0 = N /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A8 R_canon 0 = N / 8 ^ 84 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A7 R_canon 1 = (N / 8 ^ 84) mod 4 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A8 R_canon 1 = N / 8 ^ 84 / 4 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A6 R_canon 1 =
      (N - N / 8 ^ 84 * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
        mod Primes.pallas_p /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A6 R_canon 2 =
      ((N - N / 8 ^ 84 * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
        mod Primes.pallas_p) / 2 ^ 130 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A7 R_canon 2 = N / 8 ^ 44 /\
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
      Advice.A8 R_canon 2 = N / 8 ^ 43.
  Proof. repeat split; cell_refl. Qed.

  (** ** Gate-body evaluation cores *)

  (** The coordinates check-x body at a full-width row: the interpolation
      polynomial at the digit cell is the witnessed x-coordinate. *)
  Lemma check_x_full_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 d : Z)
      (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 region row =
        EccSpec.fixed_interp [c0; c1; c2; c3; c4; c5; c6; c7] d
          (UnOp.from 1))
      (HA4 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region row = d)
      (Hf0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs0 region row = c0)
      (Hf1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs1 region row = c1)
      (Hf2 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs2 region row = c2)
      (Hf3 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs3 region row = c3)
      (Hf4 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs4 region row = c4)
      (Hf5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs5 region row = c5)
      (Hf6 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs6 region row = c6)
      (Hf7 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs7 region row = c7) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) (check_x_body w_full_e).
  Proof.
    unfold check_x_body, w_full_e, x_p_e.
    cbn [eval_constraint].
    (* The interpolation window is a pure [Expression.t] fold over the eight
       Lagrange coefficients; reduce it in isolation ([vm_compute] on the
       symbolic expression, [honest_assignment] never forced) since [cbn] /
       [cbv] leave the tail-recursive [List.fold_left] of [interpolated_x]
       stuck. *)
    match goal with |- eval_expression _ _ ?e = _ => set (E := e) end.
    vm_compute in E.
    subst E.
    cbn [eval_expression].
    rewrite !rot_cur.
    rewrite HA0, HA4, Hf0, Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, Hf7.
    cbn [EccSpec.fixed_interp].
    mod_ring_solve.
  Qed.

  (** The coordinates check-x body at a running-sum row: the window is the
      digit [z_i − 8·z_{i+1}]. *)
  Lemma check_x_rs_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 d zn : Z)
      (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 region row =
        EccSpec.fixed_interp [c0; c1; c2; c3; c4; c5; c6; c7] d
          (UnOp.from 1))
      (HA4c : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region row = d + 8 * zn)
      (HA4n : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region (row + 1) = zn)
      (Hf0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs0 region row = c0)
      (Hf1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs1 region row = c1)
      (Hf2 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs2 region row = c2)
      (Hf3 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs3 region row = c3)
      (Hf4 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs4 region row = c4)
      (Hf5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs5 region row = c5)
      (Hf6 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs6 region row = c6)
      (Hf7 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.LagrangeCoeffs7 region row = c7) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) (check_x_body w_rs_e).
  Proof.
    unfold check_x_body, w_rs_e, x_p_e.
    cbn [eval_constraint].
    (* Reduce the pure interpolation-window fold in isolation; see
       [check_x_full_eval]. *)
    match goal with |- eval_expression _ _ ?e = _ => set (E := e) end.
    vm_compute in E.
    subst E.
    cbn [eval_expression].
    rewrite !rot_cur, !rot_next.
    rewrite HA0, HA4c, HA4n, Hf0, Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, Hf7.
    cbn [EccSpec.fixed_interp].
    mod_ring_solve.
  Qed.

  (** The check-y body: [u² − y = z] recovers the pasted root. *)
  Lemma check_y_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (u fz : Z)
      (HA1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A1 region row = u *F u -F fz)
      (HA5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A5 region row = u)
      (Hfz : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.fixed) Fixed.FixedZ region row = fz) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) check_y_body.
  Proof.
    unfold check_y_body, u_e, y_p_e, zf_e.
    cbn [eval_constraint eval_expression].
    rewrite !rot_cur.
    rewrite HA1, HA5, Hfz.
    mod_ring_solve.
  Qed.

  (** The on-curve body, from the certified curve identity. *)
  Lemma on_curve_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (x y : Z)
      (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 region row = x)
      (HA1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A1 region row = y)
      (Hcurve : y *F y -F (x *F x *F x +F 5) = 0) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) on_curve_body.
  Proof.
    unfold on_curve_body, x_p_e, y_p_e.
    cbn [eval_constraint eval_expression].
    rewrite !rot_cur.
    rewrite HA0, HA1.
    rewrite <- Hcurve.
    mod_ring_solve.
  Qed.

  (** The full-width window range check: the digit is in [0, 8). *)
  Lemma range_full_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (d : Z)
      (HA4 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region row = d)
      (Hd : 0 <= d < 8) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_full_body.
  Proof.
    unfold range_full_body, w_full_e.
    cbn [eval_constraint eval_expression].
    rewrite rot_cur, HA4.
    rewrite from_small by (pose proof p_big; lia).
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    lia.
  Qed.

  (** The running-sum digit range check. *)
  Lemma range_rs_eval (w : HonestInput) (region : RegionId.t) (row : Z)
      (d zn : Z)
      (HA4c : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region row = d + 8 * zn)
      (HA4n : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region (row + 1) = zn)
      (Hd : 0 <= d < 8) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_rs_body.
  Proof.
    unfold range_rs_body, w_rs_e.
    cbn [eval_constraint eval_expression].
    rewrite rot_cur, rot_next, HA4c, HA4n.
    lazymatch goal with
    | |- 0 <= ?t < _ => replace t with (UnOp.from d)
    end.
    2: { mod_ring_solve. }
    rewrite from_small by (pose proof p_big; lia).
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    lia.
  Qed.

  (** ** Region-level assemblies *)

  (** Every full-width leg row satisfies the four [QMulFixedFull] bodies. *)
  Lemma full_region_eval (w : HonestInput) (region : RegionId.t)
      (tbl : EccSpec.fixed_table) (roots : list (list Z)) (scalar : Z)
      (row : Z)
      (Hadv : forall (col : Advice.t) (off : Z),
        (OrchardHonestAssignment.honest_assignment w).(Assignment.advice)
          col region off =
        OCT.fb_full_advice_t (OCT.leg_of tbl roots scalar) scalar 85
          col off)
      (Hlen : List.length tbl = 85%nat)
      (Hfix : List.forallb (window_row_check tbl region)
        (List.seq 0 85) = true)
      (Honc : List.forallb
        (fun i =>
          List.forallb (oncurve_entry_check tbl roots i) (List.seq 0 8))
        (List.seq 0 85) = true)
      (Hrow : 0 <= row < 85) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) (check_x_body w_full_e) /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) check_y_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) on_curve_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_full_body.
  Proof.
    assert (Hiz : Z.of_nat (Z.to_nat row) = row) by (apply Z2Nat.id; lia).
    assert (Hi85 : (Z.to_nat row < 85)%nat) by lia.
    assert (Hitbl : (Z.to_nat row < List.length tbl)%nat)
      by (rewrite Hlen; exact Hi85).
    pose proof (leg_cells tbl roots scalar (Z.to_nat row) Hitbl) as Hlegs.
    cbv zeta in Hlegs.
    destruct Hlegs as (HPx & HPy & HPu).
    set (d := EccSpec.window_digit scalar (Z.to_nat row)) in *.
    assert (Hd : 0 <= d < 8)
      by (unfold d, EccSpec.window_digit; apply Z.mod_pos_bound; lia).
    pose proof (oncurve_fact tbl roots 85 (Z.to_nat row) d Honc Hi85 Hd)
      as Hcurve.
    cbv zeta in Hcurve.
    cbn [EccSpec.fixed_window_point Point.x Point.y] in HPx, HPy, Hcurve.
    (* Advice cells. *)
    assert (HA0 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) Advice.A0 region row =
      List.nth (Z.to_nat row) (OCT.lg_px (OCT.leg_of tbl roots scalar)) 0).
    { rewrite Hadv. unfold OCT.fb_full_advice_t.
      rewrite guard2_true by lia. reflexivity. }
    assert (HA1 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) Advice.A1 region row =
      List.nth (Z.to_nat row) (OCT.lg_py (OCT.leg_of tbl roots scalar)) 0).
    { rewrite Hadv. unfold OCT.fb_full_advice_t.
      rewrite guard2_true by lia. reflexivity. }
    assert (HA5 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) Advice.A5 region row =
      List.nth (Z.to_nat row) (OCT.lg_us (OCT.leg_of tbl roots scalar)) 0).
    { rewrite Hadv. unfold OCT.fb_full_advice_t.
      rewrite guard2_true by lia. reflexivity. }
    assert (HA4 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) Advice.A4 region row = d).
    { rewrite Hadv. unfold OCT.fb_full_advice_t.
      rewrite guard2_true by lia. reflexivity. }
    rewrite HPx in HA0. rewrite HPy in HA1. rewrite HPu in HA5.
    (* Fixed cells. *)
    pose proof (window_row_facts w tbl region 85 (Z.to_nat row) Hfix Hi85)
      as Hwrf.
    rewrite Hiz in Hwrf.
    destruct Hwrf as
      (Hlen8 & Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hfz).
    remember (EccSpec.fw_coeffs (wdw tbl (Z.to_nat row))) as cs eqn:Ecs.
    do 8 (destruct cs as [| ? cs]; [discriminate Hlen8 |]).
    destruct cs as [| ? cs]; [| cbn in Hlen8; lia].
    cbn [List.nth] in Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7.
    refine (conj _ (conj _ (conj _ _))).
    - eapply check_x_full_eval; eassumption.
    - eapply check_y_eval; eassumption.
    - eapply on_curve_eval; eassumption.
    - eapply range_full_eval; eassumption.
  Qed.

  (** Every running-sum leg row satisfies the four [QMulFixedRunningSum]
      bodies. *)
  Lemma rs_region_eval (w : HonestInput) (region : RegionId.t)
      (tbl : EccSpec.fixed_table) (roots : list (list Z)) (scalar : Z)
      (count : nat) (row : Z)
      (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 region row =
        List.nth (Z.to_nat row)
          (OCT.lg_px (OCT.leg_of tbl roots scalar)) 0)
      (HA1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A1 region row =
        List.nth (Z.to_nat row)
          (OCT.lg_py (OCT.leg_of tbl roots scalar)) 0)
      (HA5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A5 region row =
        List.nth (Z.to_nat row)
          (OCT.lg_us (OCT.leg_of tbl roots scalar)) 0)
      (HA4c : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region row = scalar / 8 ^ row)
      (HA4n : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 region (row + 1) =
        scalar / 8 ^ (row + 1))
      (Hlen : List.length tbl = count)
      (Hfix : List.forallb (window_row_check tbl region)
        (List.seq 0 count) = true)
      (Honc : List.forallb
        (fun i =>
          List.forallb (oncurve_entry_check tbl roots i) (List.seq 0 8))
        (List.seq 0 count) = true)
      (Hrow : 0 <= row < Z.of_nat count) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) (check_x_body w_rs_e) /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) check_y_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) on_curve_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) range_rs_body.
  Proof.
    assert (Hiz : Z.of_nat (Z.to_nat row) = row) by (apply Z2Nat.id; lia).
    assert (Hicount : (Z.to_nat row < count)%nat) by lia.
    assert (Hitbl : (Z.to_nat row < List.length tbl)%nat)
      by (rewrite Hlen; exact Hicount).
    pose proof (leg_cells tbl roots scalar (Z.to_nat row) Hitbl) as Hlegs.
    cbv zeta in Hlegs.
    destruct Hlegs as (HPx & HPy & HPu).
    set (d := EccSpec.window_digit scalar (Z.to_nat row)) in *.
    assert (Hd : 0 <= d < 8)
      by (unfold d, EccSpec.window_digit; apply Z.mod_pos_bound; lia).
    pose proof
      (oncurve_fact tbl roots count (Z.to_nat row) d Honc Hicount Hd)
      as Hcurve.
    cbv zeta in Hcurve.
    cbn [EccSpec.fixed_window_point Point.x Point.y] in HPx, HPy, Hcurve.
    rewrite HPx in HA0. rewrite HPy in HA1. rewrite HPu in HA5.
    (* The running-sum step at this row. *)
    assert (Hstep : scalar / 8 ^ row = d + 8 * (scalar / 8 ^ (row + 1))).
    { pose proof (running_sum_step scalar (Z.to_nat row)) as Hs.
      unfold running_sum_at in Hs.
      rewrite Nat2Z.inj_succ, Hiz in Hs.
      rewrite <- Z.add_1_r in Hs.
      exact Hs. }
    rewrite Hstep in HA4c.
    (* Fixed cells. *)
    pose proof
      (window_row_facts w tbl region count (Z.to_nat row) Hfix Hicount)
      as Hwrf.
    rewrite Hiz in Hwrf.
    destruct Hwrf as
      (Hlen8 & Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hfz).
    remember (EccSpec.fw_coeffs (wdw tbl (Z.to_nat row))) as cs eqn:Ecs.
    do 8 (destruct cs as [| ? cs]; [discriminate Hlen8 |]).
    destruct cs as [| ? cs]; [| cbn in Hlen8; lia].
    cbn [List.nth] in Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7.
    refine (conj _ (conj _ (conj _ _))).
    - eapply check_x_rs_eval; eassumption.
    - eapply check_y_eval; eassumption.
    - eapply on_curve_eval; eassumption.
    - eapply range_rs_eval; eassumption.
  Qed.

  (** The MSB row satisfies the four [QMulFixedShort] bodies. *)
  Lemma short_gates_eval (w : HonestInput)
      (Hmag : 0 <= magnitude w < 2 ^ 64) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_msb, 1) last_window_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_msb, 1) sign_check_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_msb, 1) y_check_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_msb, 1) negation_check_body.
  Proof.
    pose proof (msb_cells w) as Hc.
    destruct Hc as (HA1 & HA3 & HA4 & HA5).
    set (Y := Point.y (OCT.t_vcv_mul (OCT.tables_of w))) in *.
    assert (Hsgn : sign w = 1 \/ sign w = Primes.pallas_p - 1)
      by (unfold sign; destruct (hi_v_new w <=? hi_v_old w);
        [left | right]; reflexivity).
    assert (Hlw : magnitude w / 8 ^ 21 = 0 \/ magnitude w / 8 ^ 21 = 1).
    { assert (H21 : 2 * 8 ^ 21 = 2 ^ 64) by reflexivity.
      assert (Hq : 0 <= magnitude w / 8 ^ 21 < 2).
      { split.
        - apply Z.div_pos; lia.
        - apply Z.div_lt_upper_bound; lia. }
      lia. }
    refine (conj _ (conj _ (conj _ _))).
    - (* last_window_check *)
      unfold last_window_body.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA5.
      apply isbool_from. exact Hlw.
    - (* sign_check *)
      unfold sign_check_body, sgn_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA4.
      destruct Hsgn as [-> | ->].
      + mod_ring_solve.
      + vm_compute. reflexivity.
    - (* y_check *)
      unfold y_check_body, y_p_e, y_a3_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA1, HA3.
      destruct Hsgn as [Hs | Hs]; rewrite Hs.
      + left. reflexivity.
      + right.
        assert (Hne : (Primes.pallas_p - 1 =? 1) = false) by reflexivity.
        rewrite Hne.
        apply add_neg_zero.
    - (* negation_check *)
      unfold negation_check_body, sgn_e, y_p_e, y_a3_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA1, HA3, HA4.
      destruct Hsgn as [Hs | Hs]; rewrite Hs.
      + cbn [Z.eqb Pos.eqb]. mod_ring_solve.
      + assert (Hne : (Primes.pallas_p - 1 =? 1) = false) by reflexivity.
        rewrite Hne.
        apply neg_one_mul.
  Qed.

  (** The canonicity row satisfies the eight [QMulFixedBaseField] bodies:
      the decomposition identities unconditionally, and the four
      conditional clauses by cases on the top window of the reduced
      scalar. *)
  Lemma canon_gates_eval (w : HonestInput) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_1_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_2_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_3_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_4_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_5_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_6_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_7_body /\
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (R_canon, 1) canon_8_body.
  Proof.
    pose proof (canon_cells w) as Hc.
    cbv zeta in Hc.
    set (N := OCT.t_nullifier_scalar (OCT.tables_of w)) in *.
    destruct Hc as (HA6_0 & HA8_0 & HA7_1 & HA8_1 & HA6_1 & HA6_2 &
      HA7_2 & HA8_2).
    assert (HN : 0 <= N < Primes.pallas_p).
    { unfold N. rewrite nscalar_eq. unfold BinOp.add.
      apply Z.mod_pos_bound. exact p_pos. }
    set (z := N / 8 ^ 84) in *.
    (* Literal power facts, all by kernel computation. *)
    assert (Hpq : Primes.pallas_p = 2 ^ 254 + Primes.t_p) by reflexivity.
    assert (Htp0 : 0 < Primes.t_p) by reflexivity.
    assert (Htp126 : Primes.t_p < 2 ^ 126) by reflexivity.
    assert (H84 : 8 ^ 84 = 2 ^ 252) by reflexivity.
    assert (Hpow1 : 2 ^ 254 = 4 * 2 ^ 252) by reflexivity.
    assert (Hpow2 : 8 ^ 44 * 2 ^ 122 = 2 ^ 254) by reflexivity.
    assert (Hpow3 : 8 ^ 43 * 2 ^ 125 = 2 ^ 254) by reflexivity.
    assert (Htp44 : Primes.t_p < 8 ^ 44) by reflexivity.
    assert (Htp43 : Primes.t_p < 8 ^ 43) by reflexivity.
    assert (Htp130 : Primes.t_p < 2 ^ 130) by reflexivity.
    assert (Htp252 : Primes.t_p < 2 ^ 252) by reflexivity.
    assert (H84pos : 0 < 8 ^ 84) by reflexivity.
    assert (Hz0 : 0 <= z) by (apply Z.div_pos; lia).
    assert (Hz4 : z <= 4).
    { assert (Hz5 : z < 5); [| lia].
      apply Z.div_lt_upper_bound; lia. }
    (* The unconditional clauses. *)
    assert (E5 : eval_constraint
        (OrchardHonestAssignment.honest_assignment w) (R_canon, 1)
        canon_5_body).
    { unfold canon_5_body, a1_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA7_1.
      rewrite from_small
        by (pose proof (Z.mod_pos_bound z 4 ltac:(lia));
            pose proof p_big; lia).
      pose proof (Z.mod_pos_bound z 4 ltac:(lia)).
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
      lia. }
    assert (E6 : eval_constraint
        (OrchardHonestAssignment.honest_assignment w) (R_canon, 1)
        canon_6_body).
    { unfold canon_6_body, a2_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_cur1, HA8_1.
      apply isbool_from.
      destruct (Z.eq_dec z 4) as [Hz | Hz].
      - right. rewrite Hz. reflexivity.
      - left. apply Z.div_small. lia. }
    assert (E7 : eval_constraint
        (OrchardHonestAssignment.honest_assignment w) (R_canon, 1)
        canon_7_body).
    { unfold canon_7_body, z84_e, a1_e, a2_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_prev1, rot_cur1, HA8_0, HA7_1, HA8_1.
      apply div_mod_recomb. lia. }
    assert (E8 : eval_constraint
        (OrchardHonestAssignment.honest_assignment w) (R_canon, 1)
        canon_8_body).
    { unfold canon_8_body, a0p_e, alpha0_e, al_e, z84_e.
      cbn [eval_constraint eval_expression].
      rewrite rot_prev1, rot_cur1, HA6_0, HA8_0, HA6_1.
      mod_ring_solve. }
    (* The conditional clauses: cases on the top window.  Unfold the four
       [Constraint.Either] bodies so [cbn [eval_constraint]] exposes the
       disjunction; [canon_5..8] stay folded for the [assumption] discharge
       of [E5..E8]. *)
    unfold canon_1_body, canon_2_body, canon_3_body, canon_4_body.
    destruct (Z_lt_ge_dec N (2 ^ 254)) as [Hlt | Hge].
    - (* MSB clear: the guard [alpha_2 = 0] holds. *)
      assert (Hz3 : z < 4) by (apply Z.div_lt_upper_bound; lia).
      assert (Ha2 : z / 4 = 0) by (apply Z.div_small; lia).
      assert (Eguard : eval_constraint
          (OrchardHonestAssignment.honest_assignment w) (R_canon, 1)
          (Constraint.EqualZeroToPrecise a2_e)).
      { unfold a2_e.
        cbn [eval_constraint eval_expression].
        rewrite rot_cur1, HA8_1, Ha2.
        exact from_0. }
      (* Split syntactically ([apply conj] would break [canon_5]'s [Range]
         into its two inequalities up to conversion); the four conditional
         clauses take the guard, [E5..E8] discharge the rest. *)
      refine (conj _ (conj _ (conj _ (conj _
        (conj E5 (conj E6 (conj E7 E8)))))));
        cbn [eval_constraint]; left; exact Eguard.
    - (* MSB set: the reduced scalar pins every clause. *)
      assert (Hr : 0 <= N - 2 ^ 254 < Primes.t_p) by lia.
      assert (Hz : z = 4).
      { symmetry.
        apply (Zdiv.Zdiv_unique N (8 ^ 84) 4 (N - 2 ^ 254)); lia. }
      assert (Hz44 : N / 8 ^ 44 = 2 ^ 122).
      { symmetry.
        apply (Zdiv.Zdiv_unique N (8 ^ 44) (2 ^ 122) (N - 2 ^ 254)); lia. }
      assert (Hz43 : N / 8 ^ 43 = 2 ^ 125).
      { symmetry.
        apply (Zdiv.Zdiv_unique N (8 ^ 43) (2 ^ 125) (N - 2 ^ 254)); lia. }
      assert (HA' : (N - z * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
          mod Primes.pallas_p = N - 2 ^ 254 + 2 ^ 130 - Primes.t_p).
      { rewrite Hz.
        replace (N - 4 * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
          with (N - 2 ^ 254 + 2 ^ 130 - Primes.t_p) by lia.
        apply Z.mod_small. lia. }
      (* Syntactic split (see the MSB-clear branch); the four conditional
         clauses take the second [Either] alternative. *)
      refine (conj _ (conj _ (conj _ (conj _
        (conj E5 (conj E6 (conj E7 E8))))))).
      + (* alpha_1 = 0 *)
        cbn [eval_constraint]. right.
        unfold a1_e.
        cbn [eval_constraint eval_expression].
        rewrite rot_cur1, HA7_1, Hz.
        vm_compute. reflexivity.
      + (* alpha_0_hi_120 = 0 *)
        cbn [eval_constraint]. right.
        unfold hi120_e, z44_e, z84_e.
        cbn [eval_constraint eval_expression].
        rewrite rot_prev1, rot_next1, HA8_0, HA7_2, Hz44.
        fold z. rewrite Hz.
        vm_compute. reflexivity.
      + (* a_43 boolean *)
        cbn [eval_constraint]. right.
        unfold a43_e, z43_e, z44_e.
        cbn [eval_constraint eval_expression].
        rewrite rot_next1, HA7_2, HA8_2, Hz43, Hz44.
        vm_compute. reflexivity.
      + (* z_13_alpha_0_prime = 0 *)
        cbn [eval_constraint]. right.
        unfold z13_e.
        cbn [eval_constraint eval_expression].
        rewrite rot_next1, HA6_2.
        fold z. rewrite HA'.
        rewrite Z.div_small by lia.
        exact from_0.
  Qed.

  (** ** The per-selector obligations *)

  Theorem q_mul_fixed_full_gates_ok :
    selector_gates_ok Selector.QMulFixedFull.
  Proof.
    intros w Hvalid Hnondeg region row Hin gate Hgate name body Hbody.
    pose proof (fb_dom _ _ _ Hin) as Hshape.
    pose proof (qmff_body_eq gate Hgate name body Hbody) as Hbodies.
    destruct region as [wi | layer mr | pr | vr | nr | sr | ar | cr
      | wh ncr | | | | | | | gr];
      cbn in Hshape; try discriminate Hshape.
    - (* ValueCommitment *)
      destruct vr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      destruct (full_region_eval w R_vcr
        OrchardAdviceEccMuls.tbl_value_commit_r
        ValueCommitRWindowSignCert.root_table (hi_rcv w) row
        (vcr_adv w) vcr_len vcr_fixed_ok vcr_oncurve_ok
        (conj Hlo Hhi)) as (E1 & E2 & E3 & E4).
      destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
    - (* SpendAuthority *)
      destruct sr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      destruct (full_region_eval w R_sa
        OrchardAdviceEccMuls.tbl_spend_auth
        SpendAuthGWindowSignCert.root_table (hi_alpha w) row
        (sa_adv w) sa_len sa_fixed_ok sa_oncurve_ok
        (conj Hlo Hhi)) as (E1 & E2 & E3 & E4).
      destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
    - (* CommitIvk *)
      destruct cr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      destruct (full_region_eval w R_civk
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        CommitIvkRWindowSignCert.root_table (hi_rivk w) row
        (civk_adv w) civkr_len civk_fixed_ok civkr_oncurve_ok
        (conj Hlo Hhi)) as (E1 & E2 & E3 & E4).
      destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
    - (* NoteCommit *)
      destruct ncr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      destruct wh.
      + destruct (full_region_eval w R_nco
          OrchardAdviceEccMuls.tbl_note_commit_r
          NoteCommitRWindowSignCert.root_table (hi_rcm_old w) row
          (nco_adv w) ncr_len nco_fixed_ok ncr_oncurve_ok
          (conj Hlo Hhi)) as (E1 & E2 & E3 & E4).
        destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
      + destruct (full_region_eval w R_ncn
          OrchardAdviceEccMuls.tbl_note_commit_r
          NoteCommitRWindowSignCert.root_table (hi_rcm_new w) row
          (ncn_adv w) ncr_len ncn_fixed_ok ncr_oncurve_ok
          (conj Hlo Hhi)) as (E1 & E2 & E3 & E4).
        destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
  Qed.

  Theorem q_mul_fixed_running_sum_gates_ok :
    selector_gates_ok Selector.QMulFixedRunningSum.
  Proof.
    intros w Hvalid Hnondeg region row Hin gate Hgate name body Hbody.
    pose proof (fb_dom _ _ _ Hin) as Hshape.
    pose proof (qmfrs_body_eq gate Hgate name body Hbody) as Hbodies.
    destruct region as [wi | layer mr | pr | vr | nr | sr | ar | cr
      | wh ncr | | | | | | | gr];
      cbn in Hshape; try discriminate Hshape.
    - (* ValueCommitment: the short 22-window leg. *)
      destruct vr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      assert (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 R_vcv row =
        List.nth (Z.to_nat row)
          (OCT.lg_px (OCT.leg_of OrchardAdviceEccMuls.tbl_value_commit_v
            ValueCommitVWindowSignCert.root_table (magnitude w))) 0).
      { rewrite vcv_adv. unfold OCT.fb_short_advice_t.
        rewrite guard2_true by lia. reflexivity. }
      assert (HA1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A1 R_vcv row =
        List.nth (Z.to_nat row)
          (OCT.lg_py (OCT.leg_of OrchardAdviceEccMuls.tbl_value_commit_v
            ValueCommitVWindowSignCert.root_table (magnitude w))) 0).
      { rewrite vcv_adv. unfold OCT.fb_short_advice_t.
        rewrite guard2_true by lia. reflexivity. }
      assert (HA5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A5 R_vcv row =
        List.nth (Z.to_nat row)
          (OCT.lg_us (OCT.leg_of OrchardAdviceEccMuls.tbl_value_commit_v
            ValueCommitVWindowSignCert.root_table (magnitude w))) 0).
      { rewrite vcv_adv. unfold OCT.fb_short_advice_t.
        rewrite guard2_true by lia. reflexivity. }
      assert (HA4c : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 R_vcv row =
        magnitude w / 8 ^ row).
      { rewrite vcv_adv. unfold OCT.fb_short_advice_t.
        rewrite guard2le_true by lia. reflexivity. }
      assert (HA4n : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 R_vcv (row + 1) =
        magnitude w / 8 ^ (row + 1)).
      { rewrite vcv_adv. unfold OCT.fb_short_advice_t.
        rewrite guard2le_true by lia. reflexivity. }
      destruct (rs_region_eval w R_vcv
        OrchardAdviceEccMuls.tbl_value_commit_v
        ValueCommitVWindowSignCert.root_table (magnitude w) 22%nat row
        HA0 HA1 HA5 HA4c HA4n vcv_len vcv_fixed_ok vcv_oncurve_ok
        ltac:(lia)) as (E1 & E2 & E3 & E4).
      destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
    - (* Nullifier: the base-field 85-window leg. *)
      destruct nr; cbn in Hshape; try discriminate Hshape.
      unfold zin in Hshape; apply andb_prop in Hshape;
        destruct Hshape as [Hlo Hhi];
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
      assert (HA0 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A0 R_nk row =
        List.nth (Z.to_nat row)
          (OCT.lg_px (OCT.leg_of OrchardAdvicePoseidonNullifier.nk_table
            NullifierKWindowSignCert.root_table
            (OCT.t_nullifier_scalar (OCT.tables_of w)))) 0).
      { rewrite nk_cell_A0, guard2le_true by lia.
        rewrite nk_leg_eq. reflexivity. }
      assert (HA1 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A1 R_nk row =
        List.nth (Z.to_nat row)
          (OCT.lg_py (OCT.leg_of OrchardAdvicePoseidonNullifier.nk_table
            NullifierKWindowSignCert.root_table
            (OCT.t_nullifier_scalar (OCT.tables_of w)))) 0).
      { rewrite nk_cell_A1, guard2le_true by lia.
        rewrite nk_leg_eq. reflexivity. }
      assert (HA5 : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A5 R_nk row =
        List.nth (Z.to_nat row)
          (OCT.lg_us (OCT.leg_of OrchardAdvicePoseidonNullifier.nk_table
            NullifierKWindowSignCert.root_table
            (OCT.t_nullifier_scalar (OCT.tables_of w)))) 0).
      { rewrite nk_cell_A5, guard2le_true by lia.
        rewrite nk_leg_eq. reflexivity. }
      assert (HA4c : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 R_nk row =
        OCT.t_nullifier_scalar (OCT.tables_of w) / 8 ^ row).
      { rewrite nk_cell_A4, guard2le_true by lia.
        unfold running_sum_at.
        rewrite Z2Nat.id by lia. reflexivity. }
      assert (HA4n : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) Advice.A4 R_nk (row + 1) =
        OCT.t_nullifier_scalar (OCT.tables_of w) / 8 ^ (row + 1)).
      { rewrite nk_cell_A4, guard2le_true by lia.
        unfold running_sum_at.
        rewrite Z2Nat.id by lia. reflexivity. }
      destruct (rs_region_eval w R_nk
        OrchardAdvicePoseidonNullifier.nk_table
        NullifierKWindowSignCert.root_table
        (OCT.t_nullifier_scalar (OCT.tables_of w)) 85%nat row
        HA0 HA1 HA5 HA4c HA4n nk_len nk_fixed_ok nk_oncurve_ok
        ltac:(lia)) as (E1 & E2 & E3 & E4).
      destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
  Qed.

  Theorem q_mul_fixed_short_gates_ok :
    selector_gates_ok Selector.QMulFixedShort.
  Proof.
    intros w Hvalid Hnondeg region row Hin gate Hgate name body Hbody.
    pose proof (fb_dom _ _ _ Hin) as Hshape.
    pose proof (qmfs_body_eq gate Hgate name body Hbody) as Hbodies.
    destruct region as [wi | layer mr | pr | vr | nr | sr | ar | cr
      | wh ncr | | | | | | | gr];
      cbn in Hshape; try discriminate Hshape.
    destruct vr; cbn in Hshape; try discriminate Hshape.
    apply Z.eqb_eq in Hshape. subst row.
    assert (Hmag : 0 <= magnitude w < 2 ^ 64).
    { destruct Hvalid as (Hty & _).
      destruct Hty as (Hvold & Hvnew & _).
      unfold magnitude. lia. }
    destruct (short_gates_eval w Hmag) as (E1 & E2 & E3 & E4).
    destruct Hbodies as [-> | [-> | [-> | ->] ] ]; assumption.
  Qed.

  Theorem q_mul_fixed_base_field_gates_ok :
    selector_gates_ok Selector.QMulFixedBaseField.
  Proof.
    intros w Hvalid Hnondeg region row Hin gate Hgate name body Hbody.
    pose proof (fb_dom _ _ _ Hin) as Hshape.
    pose proof (qmfbf_body_eq gate Hgate name body Hbody) as Hbodies.
    destruct region as [wi | layer mr | pr | vr | nr | sr | ar | cr
      | wh ncr | | | | | | | gr];
      cbn in Hshape; try discriminate Hshape.
    destruct nr; cbn in Hshape; try discriminate Hshape.
    apply Z.eqb_eq in Hshape. subst row.
    destruct (canon_gates_eval w)
      as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct Hbodies
      as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ] ] ];
      assumption.
  Qed.

  (** ** The lookup obligations: vacuous

      No configured lookup argument mentions a fixed-base selector
      ([fb_lookups_unmentioned_ok]). *)

  Lemma fb_lookups_vacuous (sel : Selector.t) :
    List.In sel fb_selectors -> selector_lookups_ok sel.
  Proof.
    intros Hsel w Hvalid Hnondeg region row Hin arg Harg Hmention.
    exfalso.
    pose proof (proj1 (List.forallb_forall _ _)
      fb_lookups_unmentioned_ok _ Harg) as H1.
    pose proof (proj1 (List.forallb_forall _ _) H1 _ Hsel) as H2.
    cbn beta in H2.
    rewrite Hmention in H2.
    discriminate H2.
  Qed.

  Theorem q_mul_fixed_running_sum_lookups_ok :
    selector_lookups_ok Selector.QMulFixedRunningSum.
  Proof. apply fb_lookups_vacuous. cbn. tauto. Qed.

  Theorem q_mul_fixed_full_lookups_ok :
    selector_lookups_ok Selector.QMulFixedFull.
  Proof. apply fb_lookups_vacuous. cbn. tauto. Qed.

  Theorem q_mul_fixed_short_lookups_ok :
    selector_lookups_ok Selector.QMulFixedShort.
  Proof. apply fb_lookups_vacuous. cbn. tauto. Qed.

  Theorem q_mul_fixed_base_field_lookups_ok :
    selector_lookups_ok Selector.QMulFixedBaseField.
  Proof. apply fb_lookups_vacuous. cbn. tauto. Qed.

End OrchardForwardFixedBase.
