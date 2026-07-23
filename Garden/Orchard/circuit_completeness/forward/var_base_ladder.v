(** * Forward gate lemmas: the variable-base multiplication ladder (family 37)

    The symbolic per-gate forward lemmas of the [AddressIntegrity] region
    family — the 137-row double-and-add ladder computing [[ivk] g_d_old]
    (§4.18.4 'Diversified address integrity'), its three overflow-check
    regions and the witnessed [pk_d_old] point — instantiating the
    [forward/api.v] obligations at family index [37]:

    - [var_base_gates_ok] : [family_gates_ok [37]] — at every enabled point
      of the family, every constraint guarded by the point's selector holds
      under [honest_assignment w], for every valid nondegenerate input;
    - [var_base_lookups_ok] : [family_lookups_ok [37]] — the range-check
      lookup rows of the overflow running-sum decomposition land in the
      1024-row table.

    The honest cells of the family are the hoisted ladder record of
    [tables_vb.v] ([vb_columns alpha B] at [alpha = t_ivk (tables_of w)],
    [B = hi_g_d_old w]); the proofs work from the forward formulas of that
    record against the gates of [ecc/chip/mul.v] and
    [ecc/chip/mul/{incomplete,complete,overflow}.v], reusing the field-side
    core of the soundness bridge
    ([circuit_proof/ownership/var_base_{defs,incomplete}.v]) wherever it
    states the same identity.

    Structure:
    - the enabled-point shape certificate ([pt37_ok] / [pt37_cert]): the
      (selector, sub-region, row-range) inventory of the family's 293
      enabled points, one [vm_compute] over [enabled];
    - the guarded-body extraction ([guarded_bodies] +
      [guarded_bodies_complete]): membership of a [Select sel body]
      constraint in the configured system reduces to membership in the
      concrete per-selector body list;
    - the ladder characterization: the [ladder_go] fold states are the
      specification accumulators [macc] ([repr ([2^(255−i) + 2 z_i + 1] B)],
      the invariant of [var_base_incomplete.incomplete_half_generic]) under
      the transported nondegeneracy of [mul_nondegenerate_input];
    - the per-gate case lemmas, one per (selector, sub-region) pair, joined
      into the two family obligations. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_complete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.advice_ecc_muls.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_incomplete.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Orchard.circuit_completeness.certificates.
Require Import Garden.Orchard.circuit_completeness.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Garden.Orchard.circuit_completeness.tables.
Require Import Garden.Orchard.circuit_completeness.tables_vb.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Garden.Orchard.circuit.
(* [Garden.Plonky3.M] is deliberately Require'd but NOT Imported: its
   notations break nested or-intropatterns ([var_base_incomplete.v]);
   closing brackets of nested patterns are space-separated below for the
   same reason (other imports declare multi-bracket tokens). *)
Require Garden.Plonky3.M.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

(* [add_complete] (via [Field.Fermat]) loads ssreflect, which turns bullet
   discipline off; the proofs below rely on bullets focusing subgoals. *)
#[local] Set Bullet Behavior "Strict Subproofs".

Global Open Scope Z_scope.

Module OrchardVarBaseForward.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.

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

  (** ** The family's regions *)

  Definition vb_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul
        RegionId.AddressIntegrity.Mul.VariableBase).
  Definition ovs_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul
        RegionId.AddressIntegrity.Mul.OverflowS).
  Definition ovl_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul
        RegionId.AddressIntegrity.Mul.OverflowLookup).
  Definition ovc_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul
        RegionId.AddressIntegrity.Mul.OverflowCheck).
  Definition wpkd_region : RegionId.t :=
    RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD.

  (** ** The enabled-point shapes of family 37

      The (selector, sub-region, row) inventory of the family's enabled
      points, certified once against the concrete [enabled] list.  Points of
      other families pass vacuously. *)

  Definition pt37_ok (pt : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, row) := pt in
    match region with
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase) =>
        match sel with
        | Selector.QEccAdd =>
            ((row =? 0) || ((129 <=? row) && (row <=? 135)))%bool
        | Selector.QMulIncompleteHi1 => row =? 1
        | Selector.QMulIncompleteHi2 => ((2 <=? row) && (row <=? 125))%bool
        | Selector.QMulIncompleteHi3 => row =? 126
        | Selector.QMulIncompleteLo1 => row =? 1
        | Selector.QMulIncompleteLo2 => ((2 <=? row) && (row <=? 126))%bool
        | Selector.QMulIncompleteLo3 => row =? 127
        | Selector.QMulDecomposeVar =>
            ((row =? 130) || (row =? 132) || (row =? 134))%bool
        | Selector.QMulLsb => row =? 135
        | _ => false
        end
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowS) => false
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowLookup) =>
        match sel with
        | Selector.QLookup | Selector.QRunning =>
            ((0 <=? row) && (row <=? 12))%bool
        | _ => false
        end
    | RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowCheck) =>
        match sel with
        | Selector.QMulOverflow => row =? 1
        | _ => false
        end
    | RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD =>
        match sel with
        | Selector.QWitnessPointNonId => row =? 0
        | _ => false
        end
    | RegionId.AddressIntegrity RegionId.AddressIntegrity.Equality => false
    | _ => true
    end.

  Lemma pt37_cert : List.forallb pt37_ok enabled = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma pt37_shape_of (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    pt37_ok (sel, region, row) = true.
  Proof.
    intros Hin.
    exact (proj1 (List.forallb_forall pt37_ok enabled) pt37_cert _ Hin).
  Qed.

  (** ** Guarded-body extraction

      For a concrete selector, the bodies of the constraints it guards form
      a concrete list; membership of a [Select sel body] constraint anywhere
      in the configured system reduces to membership of [body] in that
      list. *)

  Definition body_of (sel : Selector.t) (c : Constraint.t columns)
      : list (Constraint.t columns) :=
    match c with
    | Constraint.Select s b =>
        if OrchardDecidableEq.selector_eqb s sel then [b] else []
    | _ => []
    end.

  Definition guarded_bodies (sel : Selector.t)
      : list (Constraint.t columns) :=
    List.flat_map
      (fun gate =>
        List.flat_map (fun '(_, c) => body_of sel c)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma selector_eqb_refl (sel : Selector.t) :
    OrchardDecidableEq.selector_eqb sel sel = true.
  Proof.
    apply OrchardDecidableEq.selector_eqb_eq.
    reflexivity.
  Qed.

  Lemma guarded_bodies_complete (sel : Selector.t)
      (gate : Gate.t columns) (name : option string)
      (body : Constraint.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
    List.In body (guarded_bodies sel).
  Proof.
    intros Hgate Hbody.
    apply List.in_flat_map.
    exists gate.
    split; [exact Hgate |].
    apply List.in_flat_map.
    exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    cbn [body_of].
    rewrite selector_eqb_refl.
    left; reflexivity.
  Qed.

  (** ** The hoisted-record projections

      [tables_of w] routes the family's cells through
      [vb_columns (t_ivk (tables_of w)) (hi_g_d_old w)]; the projection
      equations are definitional. *)

  Lemma t_vb_eq (w : HonestInput) :
    OrchardCompletenessTables.t_vb (OrchardCompletenessTables.tables_of w) =
    OrchardVarBaseTables.vb_columns
      (OrchardCompletenessTables.t_ivk (OrchardCompletenessTables.tables_of w))
      (hi_g_d_old w).
  Proof.
    unfold OrchardCompletenessTables.tables_of.
    reflexivity.
  Qed.

  Lemma t_vb_result_eq (w : HonestInput) :
    OrchardCompletenessTables.t_vb_result
      (OrchardCompletenessTables.tables_of w) =
    PallasModel.repr
      (Pallas.mul
        (OrchardCompletenessTables.t_ivk
          (OrchardCompletenessTables.tables_of w))
        (PallasModel.unrepr (hi_g_d_old w))).
  Proof.
    unfold OrchardCompletenessTables.tables_of.
    reflexivity.
  Qed.

  (** The [vb_columns] record as an explicit literal over the two raw
      [ladder_go] folds, and the per-field corollaries the cell lemmas
      rewrite with. *)

  Local Notation vbc alpha B := (OrchardVarBaseTables.vb_columns alpha B).

  Lemma vb_columns_eq (alpha : Z) (B : Point.t) :
    vbc alpha B =
    let k := alpha + Primes.t_q in
    let d := EccSpec.point_add B B in
    let ha := OrchardVarBaseTables.ladder_go B k d 254%nat 125%nat in
    let la :=
      OrchardVarBaseTables.ladder_go B k (snd ha) 129%nat 126%nat in
    let p3 := OrchardVarBaseTables.signed_pt B (scalar_bit k 3%nat) in
    let mid3 := EccSpec.point_add p3 (snd la) in
    let acc3 := EccSpec.point_add (snd la) mid3 in
    let p2 := OrchardVarBaseTables.signed_pt B (scalar_bit k 2%nat) in
    let mid2 := EccSpec.point_add p2 acc3 in
    let acc2 := EccSpec.point_add acc3 mid2 in
    let p1 := OrchardVarBaseTables.signed_pt B (scalar_bit k 1%nat) in
    let mid1 := EccSpec.point_add p1 acc2 in
    let acc1 := EccSpec.point_add acc2 mid1 in
    let p0 := OrchardVarBaseTables.lsb_pt B (scalar_bit k 0%nat) in
    let out := EccSpec.point_add p0 acc1 in
    let k254 := k / 2 ^ 254 in
    let z130 := k / 2 ^ 130 in
    {|
      OrchardVarBaseTables.vb_scalar := k;
      OrchardVarBaseTables.vb_hi := fst ha;
      OrchardVarBaseTables.vb_lo := fst la;
      OrchardVarBaseTables.vb_d := d;
      OrchardVarBaseTables.vb_acc130 := snd ha;
      OrchardVarBaseTables.vb_acc4 := snd la;
      OrchardVarBaseTables.vb_p3 := p3;
      OrchardVarBaseTables.vb_mid3 := mid3;
      OrchardVarBaseTables.vb_acc3 := acc3;
      OrchardVarBaseTables.vb_p2 := p2;
      OrchardVarBaseTables.vb_mid2 := mid2;
      OrchardVarBaseTables.vb_acc2 := acc2;
      OrchardVarBaseTables.vb_p1 := p1;
      OrchardVarBaseTables.vb_mid1 := mid1;
      OrchardVarBaseTables.vb_acc1 := acc1;
      OrchardVarBaseTables.vb_p0 := p0;
      OrchardVarBaseTables.vb_out := out;
      OrchardVarBaseTables.vb_k254 := k254;
      OrchardVarBaseTables.vb_s :=
        (alpha + k254 * 2 ^ 130) mod Primes.pallas_p;
      OrchardVarBaseTables.vb_eta :=
        if z130 =? 0 then 0 else mod_inverse z130 Primes.pallas_p;
    |}.
  Proof.
    cbv zeta.
    unfold OrchardVarBaseTables.vb_columns.
    destruct (OrchardVarBaseTables.ladder_go
      B (alpha + Primes.t_q) (EccSpec.point_add B B) 254%nat 125%nat)
      as [hi acc130] eqn:Hhi.
    cbn [fst snd].
    destruct (OrchardVarBaseTables.ladder_go B (alpha + Primes.t_q)
      acc130 129%nat 126%nat) as [lo acc4] eqn:Hlo.
    cbn [fst snd].
    reflexivity.
  Qed.

  (** ** Field-level helpers *)

  Lemma from_range (x : Z) : 0 <= UnOp.from x < Primes.pallas_p.
  Proof.
    unfold UnOp.from.
    apply Z.mod_pos_bound.
    unfold Primes.pallas_p, Primes.t_p; lia.
  Qed.

  Lemma pallas_p_pos : 2 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p; lia. Qed.

  Lemma sub_0_opp (y : Z) : 0 -F y = UnOp.opp y.
  Proof.
    unfold BinOp.sub, UnOp.opp.
    f_equal; lia.
  Qed.

  Lemma from_div_reduced (a b : Z) :
    UnOp.from (BinOp.div a b) = BinOp.div a b.
  Proof.
    unfold BinOp.div.
    apply from_mul_reduced.
  Qed.

  (** ** The specification accumulator of the double-and-add ladder

      [macc alpha B i] is the intended accumulator at bit boundary [i] —
      [repr ([2^(255−i) + 2·z_i + 1] B)] over the 255-bit scalar
      [alpha + t_q] — matching [OrchardWitnessInput.mul_acc] at
      [alpha = ivk w]; [mstep] is the signed per-bit point, matching
      [mul_step_point]. *)

  Definition mk (alpha : Z) : Z := alpha + Primes.t_q.

  Definition macc (alpha : Z) (B : Point.t) (i : nat) : Point.t :=
    PallasModel.repr
      (Pallas.mul
        (2 ^ (255 - Z.of_nat i) + 2 * (mk alpha / 2 ^ Z.of_nat i) + 1)
        (PallasModel.unrepr B)).

  Definition mstep (alpha : Z) (B : Point.t) (i : nat) : Point.t :=
    if scalar_bit (mk alpha) i =? 1 then B else point_neg B.

  (** The transported per-step nondegeneracy
      ([OrchardWitnessInput.mul_step_nondegenerate] at [alpha = ivk w]). *)
  Definition step_ok (alpha : Z) (B : Point.t) (m : nat) : Prop :=
    Point.x (macc alpha B (S m)) <> 0 /\
    Point.x (macc alpha B (S m)) <> Point.x B /\
    Point.x
      (EccSpec.point_add_incomplete (macc alpha B (S m)) (mstep alpha B m)) <>
      Point.x (macc alpha B (S m)).

  Definition ladder_ok (alpha : Z) (B : Point.t) : Prop :=
    forall m : nat, (4 <= m < 255)%nat -> step_ok alpha B m.

  (** Conversion across the [macc]/[mul_acc] constant boundary must be by
      explicit unfolding to syntactic identity — [reflexivity] alone hands
      the oracle the [ivk]/[Pallas.mul] chain. *)
  Lemma macc_mul_acc (w : HonestInput) (i : nat) :
    macc (ivk w) (hi_g_d_old w) i = mul_acc w i.
  Proof.
    unfold macc, mul_acc, mul_multiple, bit_running_sum, mul_scalar,
      mul_base, mk.
    reflexivity.
  Qed.

  Lemma mstep_mul_step_point (w : HonestInput) (i : nat) :
    mstep (ivk w) (hi_g_d_old w) i = mul_step_point w i.
  Proof.
    unfold mstep, mul_step_point, mul_scalar, mk.
    reflexivity.
  Qed.

  Lemma ladder_ok_of_nondegenerate (w : HonestInput) :
    nondegenerate w ->
    ladder_ok (ivk w) (hi_g_d_old w).
  Proof.
    intros Hnd m Hm.
    destruct Hnd as (_ & _ & _ & _ & Hmul).
    specialize (Hmul m Hm).
    unfold mul_step_nondegenerate in Hmul.
    cbv zeta in Hmul.
    unfold step_ok.
    rewrite (macc_mul_acc w (S m)), (mstep_mul_step_point w m).
    exact Hmul.
  Qed.

  (** ** Point-level glue *)

  (** A [point_ok] point is affine in the [unrepr] reading, with reduced,
      on-curve coordinates. *)
  Lemma point_ok_affine (B : Point.t) (HB : point_ok B) :
    PallasModel.unrepr B =
      Weierstrass.Affine (Point.x B) (Point.y B) /\
    UnOp.from (Point.x B) = Point.x B /\
    UnOp.from (Point.y B) = Point.y B.
  Proof.
    destruct HB as (Hred & Hoc & Hnid).
    assert (Haff : PallasModel.unrepr B =
        Weierstrass.Affine (Point.x B) (Point.y B)).
    { unfold PallasModel.unrepr.
      destruct ((Point.x B =? 0) && (Point.y B =? 0))%bool eqn:Hb;
        [| reflexivity].
      exfalso.
      apply andb_true_iff in Hb.
      destruct Hb as (Hx & Hy).
      apply Z.eqb_eq in Hx, Hy.
      apply Hnid.
      destruct B as [bx by']; cbn in *.
      subst; reflexivity. }
    split; [exact Haff |].
    rewrite Haff in Hred.
    destruct Hred as (Hx & Hy).
    split; [exact Hx | exact Hy].
  Qed.

  (** [macc] has reduced coordinates. *)
  Lemma macc_reduced (alpha : Z) (B : Point.t) (HB : point_ok B) (i : nat) :
    UnOp.from (Point.x (macc alpha B i)) = Point.x (macc alpha B i) /\
    UnOp.from (Point.y (macc alpha B i)) = Point.y (macc alpha B i).
  Proof.
    destruct HB as (Hred & _ & _).
    pose proof (VarBaseDefs.pallas_mul_reduced
      (2 ^ (255 - Z.of_nat i) + 2 * (mk alpha / 2 ^ Z.of_nat i) + 1)
      (PallasModel.unrepr B) Hred) as Hr.
    unfold macc.
    set (P := Pallas.mul _ (PallasModel.unrepr B)) in *.
    clearbody P.
    destruct P as [| ax ay].
    - cbn [PallasModel.repr Point.x Point.y].
      split; reflexivity.
    - destruct Hr as (Hx & Hy).
      cbn [PallasModel.repr Point.x Point.y].
      split; assumption.
  Qed.

  (** An affine [macc]: the accumulator with a nonzero [x] is the [repr] of
      an affine on-curve point with exactly its coordinates. *)
  Lemma macc_affine (alpha : Z) (B : Point.t) (i : nat)
      (Hx0 : Point.x (macc alpha B i) <> 0) :
    Pallas.mul
      (2 ^ (255 - Z.of_nat i) + 2 * (mk alpha / 2 ^ Z.of_nat i) + 1)
      (PallasModel.unrepr B) =
    Weierstrass.Affine (Point.x (macc alpha B i)) (Point.y (macc alpha B i)).
  Proof.
    unfold macc in *.
    set (P := Pallas.mul _ (PallasModel.unrepr B)) in *.
    clearbody P.
    destruct P as [| ax ay].
    - exfalso. apply Hx0. reflexivity.
    - reflexivity.
  Qed.

  Local Notation two_inv :=
    Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv.

  (** The [x_r] gate polynomial in the ladder's raw spelling. *)
  Lemma x_r_raw (xa bx l1 : Z) :
    x_r xa bx l1 = l1 *F l1 -F xa -F bx.
  Proof. reflexivity. Qed.

  (** The incomplete-addition [x] in the ladder's raw spelling. *)
  Lemma incomplete_add_x (P Q : Point.t) :
    Point.x (EccSpec.point_add_incomplete P Q) =
    (let l :=
      BinOp.div (Point.y P -F Point.y Q) (Point.x P -F Point.x Q) in
     l *F l -F Point.x P -F Point.x Q).
  Proof. reflexivity. Qed.

  Lemma mstep_x (alpha : Z) (B : Point.t) (m : nat) :
    Point.x (mstep alpha B m) = Point.x B.
  Proof.
    unfold mstep.
    destruct (scalar_bit (mk alpha) m =? 1); reflexivity.
  Qed.

  Lemma mstep_y (alpha : Z) (B : Point.t) (m : nat) :
    Point.y (mstep alpha B m) =
    (if scalar_bit (mk alpha) m =? 1 then Point.y B else 0 -F Point.y B).
  Proof.
    unfold mstep.
    destruct (scalar_bit (mk alpha) m =? 1); reflexivity.
  Qed.

  Lemma scalar_bit_01 (k : Z) (m : nat) :
    scalar_bit k m = 0 \/ scalar_bit k m = 1.
  Proof.
    unfold scalar_bit.
    pose proof (Z.mod_pos_bound (k / 2 ^ Z.of_nat m) 2 ltac:(lia)) as Hb.
    lia.
  Qed.

  (** ** The bit-independent chord core of one ladder step

      Over the raw step values ([L1]/[XR]/[YR]/[L2]/[XAN]/[YAN] as
      [ladder_step] computes them, from an accumulator [(xa, ya)], the base
      [x] [bx] and the signed base [y] [yp]): the [y_a] gate expression
      recovers [ya], [λ₁] multiplies back to the first chord, [XAN] is the
      [next_x_a] polynomial and the [gradient_2] identity holds. *)
  Lemma ladder_core (xa ya bx yp : Z)
      (Hxar : UnOp.from xa = xa)
      (Hyar : UnOp.from ya = ya)
      (Hd1 : UnOp.from (xa -F bx) <> 0)
      (Hd2 : UnOp.from
        (xa -F (BinOp.div (ya -F yp) (xa -F bx) *F
                  BinOp.div (ya -F yp) (xa -F bx) -F xa -F bx)) <> 0) :
    let L1 := BinOp.div (ya -F yp) (xa -F bx) in
    let XR := L1 *F L1 -F xa -F bx in
    let YR := L1 *F (xa -F XR) -F ya in
    let L2 := BinOp.div (ya -F YR) (xa -F XR) in
    let XAN := L2 *F L2 -F xa -F XR in
    let YAN := L2 *F (xa -F XAN) -F ya in
    y_a xa bx L1 L2 = ya /\
    L1 *F (xa -F bx) = ya -F yp /\
    XAN = next_x_a xa bx L1 L2 /\
    L2 *F (xa -F XAN) -F y_a xa bx L1 L2 -F YAN = 0.
  Proof.
    cbv zeta.
    set (L1 := BinOp.div (ya -F yp) (xa -F bx)) in *.
    set (XR := L1 *F L1 -F xa -F bx) in *.
    set (YR := L1 *F (xa -F XR) -F ya) in *.
    set (L2 := BinOp.div (ya -F YR) (xa -F XR)) in *.
    set (XAN := L2 *F L2 -F xa -F XR) in *.
    set (YAN := L2 *F (xa -F XAN) -F ya) in *.
    assert (Hs1 : L1 *F (xa -F bx) = ya -F yp).
    { unfold L1.
      rewrite div_mul;
        [| exact pallas_p_pos | exact Hd1].
      apply from_sub_reduced. }
    assert (Hs2 : L2 *F (xa -F XR) = ya -F YR).
    { unfold L2.
      rewrite div_mul;
        [| exact pallas_p_pos | exact Hd2].
      apply from_sub_reduced. }
    assert (Hchord1 : L1 *F (xa -F XR) = YR +F ya).
    { unfold YR. mod_ring_solve. }
    assert (Hya : y_a xa bx L1 L2 = ya).
    { unfold y_a.
      rewrite x_r_raw.
      change (utilities_proof.square L1) with (L1 *F L1).
      fold XR.
      assert (Hsum : (L1 +F L2) *F (xa -F XR) = ya +F ya).
      { transitivity ((L1 *F (xa -F XR)) +F (L2 *F (xa -F XR)));
          [mod_ring_solve |].
        rewrite Hchord1, Hs2.
        mod_ring_solve. }
      rewrite Hsum.
      transitivity
        ((ya *F UnOp.from two_inv) +F (ya *F UnOp.from two_inv));
        [mod_ring_solve |].
      rewrite VarBaseIncomplete.half_double_add.
      exact Hyar. }
    split; [exact Hya |].
    split; [exact Hs1 |].
    split.
    - unfold next_x_a.
      rewrite x_r_raw.
      change (utilities_proof.square L2) with (L2 *F L2).
      fold XR.
      unfold XAN.
      mod_ring_solve.
    - rewrite Hya.
      unfold YAN.
      apply (proj2 (sub_zero_equiv _ _)).
      rewrite !from_sub_reduced.
      reflexivity.
  Qed.

  (** ** The tables' scalar is the specification [ivk]

      [tables_of] computes the variable-base scalar as the x-extraction of
      the [Commit^ivk] point over the hoisted [hash_go] fold; the fold rows
      mirror [IncompleteAddition.output] literally, so the fold output is the
      specification hash and the scalar is [ivk w]. *)

  Module OCT := OrchardCompletenessTables.
  Module OAMS := OrchardAdviceMerkleSinsemilla.

  Lemma hash_go_snd (ws : list Z) :
    forall acc : Point.t,
      snd (OCT.hash_go acc ws) =
      SinsemillaSpec.sinsemilla_hash_to_point acc ws.
  Proof.
    induction ws as [| wd ws IH]; intro acc.
    - reflexivity.
    - cbn [OCT.hash_go].
      cbv zeta.
      rewrite (surjective_pairing (OCT.hash_go _ ws)).
      cbn [fst snd].
      rewrite IH.
      reflexivity.
  Qed.

  Lemma hd_out_hash_data_of (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_out (OCT.hash_data_of Q pieces) =
    SinsemillaSpec.sinsemilla_hash_to_point Q (List.concat pieces).
  Proof.
    unfold OCT.hash_data_of.
    cbv zeta.
    rewrite (surjective_pairing (OCT.hash_go Q (List.concat pieces))).
    cbn [OCT.hd_out].
    apply hash_go_snd.
  Qed.

  Lemma firstn_plus {A : Type} (n m : nat) (l : list A) :
    List.firstn (n + m) l =
    List.firstn n l ++ List.firstn m (List.skipn n l).
  Proof.
    revert l; induction n as [| n IH]; intro l.
    - reflexivity.
    - destruct l as [| x l'].
      + cbn [Nat.add List.firstn List.skipn].
        rewrite List.firstn_nil.
        reflexivity.
      + cbn [Nat.add List.firstn List.skipn List.app].
        f_equal.
        apply IH.
  Qed.

  Lemma words_le_length (count : nat) :
    forall n : Z, List.length (SinsemillaSpec.words_le count n) = count.
  Proof.
    induction count as [| c IH]; intro n.
    - reflexivity.
    - cbn [SinsemillaSpec.words_le List.length].
      now rewrite IH.
  Qed.

  Lemma commit_ivk_words_length (w : HonestInput) :
    List.length (commit_ivk_words w) = 51%nat.
  Proof.
    unfold commit_ivk_words, OrchardSpec.commit_ivk_message.
    apply words_le_length.
  Qed.

  Lemma split_pieces_concat_51 (l : list Z)
      (Hlen : List.length l = 51%nat) :
    List.concat (OAMS.split_pieces OAMS.commit_ivk_lens l) = l.
  Proof.
    cbn [OAMS.split_pieces OAMS.commit_ivk_lens List.concat].
    rewrite List.app_nil_r.
    rewrite <- (firstn_plus 24 1 (List.skipn 1 (List.skipn 25 l))).
    change (24 + 1)%nat with 25%nat.
    rewrite <- (firstn_plus 1 25 (List.skipn 25 l)).
    change (1 + 25)%nat with 26%nat.
    rewrite <- (firstn_plus 25 26 l).
    change (25 + 26)%nat with 51%nat.
    rewrite <- Hlen.
    apply List.firstn_all.
  Qed.

  Lemma t_ivk_eq (w : HonestInput) :
    OCT.t_ivk (OCT.tables_of w) = ivk w.
  Proof.
    unfold OCT.tables_of.
    cbv zeta.
    cbn [OCT.t_ivk].
    rewrite hd_out_hash_data_of.
    rewrite (split_pieces_concat_51 _ (commit_ivk_words_length w)).
    unfold OAMS.commit_ivk_Q, commit_ivk_words, ivk,
      OrchardProtocolSpec.commit_ivk.
    reflexivity.
  Qed.

  (** ** Range of the scalar *)

  Lemma repr_coord_reduced (P : Pallas.point) (HP : Pallas.reduced P) :
    UnOp.from (Point.x (PallasModel.repr P)) =
      Point.x (PallasModel.repr P) /\
    UnOp.from (Point.y (PallasModel.repr P)) =
      Point.y (PallasModel.repr P).
  Proof.
    destruct P as [| x y].
    - cbn [PallasModel.repr Point.x Point.y].
      split; reflexivity.
    - destruct HP as (Hx & Hy).
      cbn [PallasModel.repr Point.x Point.y].
      split; assumption.
  Qed.

  Lemma padd_inc_reduced (P Q : Point.t) :
    UnOp.from (Point.x (EccSpec.point_add_incomplete P Q)) =
      Point.x (EccSpec.point_add_incomplete P Q) /\
    UnOp.from (Point.y (EccSpec.point_add_incomplete P Q)) =
      Point.y (EccSpec.point_add_incomplete P Q).
  Proof.
    split; apply from_sub_reduced.
  Qed.

  Lemma hash_to_point_reduced (words : list Z) :
    forall acc : Point.t,
      words <> [] ->
      UnOp.from
        (Point.x (SinsemillaSpec.sinsemilla_hash_to_point acc words)) =
        Point.x (SinsemillaSpec.sinsemilla_hash_to_point acc words) /\
      UnOp.from
        (Point.y (SinsemillaSpec.sinsemilla_hash_to_point acc words)) =
        Point.y (SinsemillaSpec.sinsemilla_hash_to_point acc words).
  Proof.
    induction words as [| wd words IH]; intros acc Hne.
    - congruence.
    - destruct words as [| wd' words'].
      + cbn [SinsemillaSpec.sinsemilla_hash_to_point
          Stdlib.Lists.List.fold_left].
        apply padd_inc_reduced.
      + exact (IH (SinsemillaSpec.round acc wd) ltac:(discriminate)).
  Qed.

  Lemma point_add_x_reduced (P Q : Point.t)
      (HxP : UnOp.from (Point.x P) = Point.x P)
      (HxQ : UnOp.from (Point.x Q) = Point.x Q) :
    UnOp.from (Point.x (EccSpec.point_add P Q)) =
      Point.x (EccSpec.point_add P Q).
  Proof.
    unfold EccSpec.point_add, CompleteAddition.output.
    destruct (Point.x P =? 0).
    - exact HxQ.
    - destruct (Point.x Q =? 0).
      + exact HxP.
      + destruct ((Point.x P =? Point.x Q) &&
          (Point.y P +F Point.y Q =? 0))%bool.
        * cbn [Point.x]. reflexivity.
        * cbv zeta. cbn [Point.x]. apply from_sub_reduced.
  Qed.

  Lemma ivk_range (w : HonestInput) : 0 <= ivk w < Primes.pallas_p.
  Proof.
    assert (Hred : UnOp.from (ivk w) = ivk w).
    { unfold ivk, OrchardProtocolSpec.commit_ivk, EccSpec.extract_x.
      apply point_add_x_reduced.
      - refine (proj1 (hash_to_point_reduced _ _ _)).
        intro Hnil.
        apply (f_equal (@List.length Z)) in Hnil.
        unfold OrchardSpec.commit_ivk_message in Hnil.
        rewrite (words_le_length 51%nat) in Hnil.
        discriminate Hnil.
      - unfold OrchardProtocolSpec.mul_commit_ivk_r.
        refine (proj1 (repr_coord_reduced _ _)).
        apply VarBaseDefs.pallas_mul_reduced.
        exact PallasGenerators.commit_ivk_r_reduced. }
    rewrite <- Hred.
    apply from_range.
  Qed.

  Lemma mk_ivk_range (w : HonestInput) : 0 <= mk (ivk w) < 2 ^ 255.
  Proof.
    pose proof (ivk_range w) as Hr.
    unfold mk.
    unfold Primes.pallas_p, Primes.t_p in Hr.
    unfold Primes.t_q.
    lia.
  Qed.

  (** ** The [ladder_go] fold: shape and specification chain *)

  (** One [ladder_step] is the two spec-level incomplete additions of the
      signed base point. *)
  Lemma ladder_step_shape (B acc : Point.t) (bit : Z) :
    OrchardVarBaseTables.ladder_step B bit acc =
    (let P := {| Point.x := Point.x B;
                 Point.y :=
                   if bit =? 1 then Point.y B else 0 -F Point.y B |} in
     let mid := EccSpec.point_add_incomplete acc P in
     ({| OrchardVarBaseTables.sr_xa := Point.x acc;
         OrchardVarBaseTables.sr_l1 :=
           BinOp.div (Point.y acc -F Point.y P)
             (Point.x acc -F Point.x P);
         OrchardVarBaseTables.sr_l2 :=
           BinOp.div (Point.y acc -F Point.y mid)
             (Point.x acc -F Point.x mid) |},
      EccSpec.point_add_incomplete acc mid)).
  Proof.
    reflexivity.
  Qed.

  Lemma mstep_coords (alpha : Z) (B : Point.t) (m : nat) :
    mstep alpha B m =
    {| Point.x := Point.x B;
       Point.y :=
         if scalar_bit (mk alpha) m =? 1
         then Point.y B
         else 0 -F Point.y B |}.
  Proof.
    unfold mstep, point_neg.
    destruct (scalar_bit (mk alpha) m =? 1).
    - destruct B; reflexivity.
    - reflexivity.
  Qed.

  (** The shape of a [... = 0] field identity: reduce both sides to a mod
      congruence and close by [ring]. *)
  Lemma zero_mod_shape (x : Z) :
    x mod Primes.pallas_p = 0 mod Primes.pallas_p ->
    x mod Primes.pallas_p = 0.
  Proof.
    intro H.
    rewrite H.
    apply Zmod_0_l.
  Qed.

  Ltac mod_ring_zero :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from, UnOp.opp;
    apply zero_mod_shape;
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q =>
        change (Zdiv.eqm q x y);
        repeat setoid_rewrite (Zdiv.Zmod_eqm q)
    end;
    unfold Zdiv.eqm; f_equal; ring.

  (** One nondegenerate step advances the accumulator to the next [macc]. *)
  Lemma ladder_step_macc (alpha : Z) (B : Point.t) (m : nat)
      (HB : point_ok B) (Hm : (m < 255)%nat)
      (Hstep : step_ok alpha B m) :
    snd (OrchardVarBaseTables.ladder_step B (scalar_bit (mk alpha) m)
      (macc alpha B (S m))) = macc alpha B m.
  Proof.
    destruct Hstep as (Hx0 & Hxb & Hmid).
    pose proof (point_ok_affine B HB) as (Haff & Hbx & Hby).
    pose proof (macc_reduced alpha B HB (S m)) as (Hxar & Hyar).
    pose proof (scalar_bit_01 (mk alpha) m) as Hbit01.
    rewrite (mstep_coords alpha B m) in Hmid.
    set (acc := macc alpha B (S m)) in *.
    set (bit := scalar_bit (mk alpha) m) in *.
    set (yp := if bit =? 1 then Point.y B else 0 -F Point.y B) in *.
    set (xa := Point.x acc) in *.
    set (ya := Point.y acc) in *.
    set (L1 := BinOp.div (ya -F yp) (xa -F Point.x B)).
    set (XR := L1 *F L1 -F xa -F Point.x B).
    set (YR := L1 *F (xa -F XR) -F ya).
    set (L2 := BinOp.div (ya -F YR) (xa -F XR)).
    set (XAN := L2 *F L2 -F xa -F XR).
    set (YAN := L2 *F (xa -F XAN) -F ya).
    assert (HXRred : UnOp.from XR = XR)
      by (unfold XR; apply from_sub_reduced).
    (* The intermediate sum's x-coordinate is [XR]. *)
    assert (HmidX : Point.x (EccSpec.point_add_incomplete acc
        {| Point.x := Point.x B; Point.y := yp |}) = XR)
      by reflexivity.
    rewrite HmidX in Hmid.
    (* The two chord denominators are nonzero. *)
    assert (Hd1 : UnOp.from (xa -F Point.x B) <> 0).
    { intro Hz.
      rewrite from_sub_reduced in Hz.
      apply (proj1 (sub_zero_equiv xa (Point.x B))) in Hz.
      rewrite Hxar, Hbx in Hz.
      exact (Hxb Hz). }
    assert (Hd2 : UnOp.from (xa -F XR) <> 0).
    { intro Hz.
      rewrite from_sub_reduced in Hz.
      apply (proj1 (sub_zero_equiv xa XR)) in Hz.
      rewrite Hxar, HXRred in Hz.
      exact (Hmid (eq_sym Hz)). }
    pose proof (ladder_core xa ya (Point.x B) yp Hxar Hyar Hd1 Hd2) as Hcore.
    cbv zeta in Hcore.
    fold L1 in Hcore.
    fold XR in Hcore.
    fold YR in Hcore.
    fold L2 in Hcore.
    fold XAN in Hcore.
    fold YAN in Hcore.
    destruct Hcore as (Hya & Hs1 & Hxan & Hg2).
    (* The step output is the double incomplete addition. *)
    rewrite ladder_step_shape.
    cbv zeta.
    cbn [snd].
    fold yp.
    assert (Hout :
        EccSpec.point_add_incomplete acc
          (EccSpec.point_add_incomplete acc
            {| Point.x := Point.x B; Point.y := yp |}) =
        {| Point.x := XAN; Point.y := YAN |})
      by reflexivity.
    rewrite Hout.
    (* Group-level step at the raw values. *)
    set (c := 2 ^ (255 - Z.of_nat (S m)) +
      2 * (mk alpha / 2 ^ Z.of_nat (S m)) + 1).
    assert (Hstep_group :
        {| Point.x := XAN; Point.y := YAN |} =
        PallasModel.repr
          (Pallas.mul (2 * c + 2 * bit - 1) (PallasModel.unrepr B))).
    { destruct HB as (HBred & HBoc & _).
      apply (VarBaseIncomplete.incomplete_step_group
        (PallasModel.unrepr B) (Point.x B) (Point.y B) Haff HBred HBoc
        c bit xa L1 L2 XAN YAN).
      - unfold L1. apply from_div_reduced.
      - unfold L2. apply from_div_reduced.
      - unfold YAN. apply from_sub_reduced.
      - exact Hbit01.
      - rewrite Hya.
        change {| Point.x := xa; Point.y := ya |} with acc.
        unfold acc, macc, c.
        reflexivity.
      - exact Hx0.
      - exact Hxb.
      - rewrite x_r_raw.
        fold XR.
        intro Hz.
        exact (Hmid Hz).
      - (* gradient_1. *)
        rewrite Hya.
        destruct Hbit01 as [Hb | Hb];
          unfold yp in Hs1;
          rewrite Hb in Hs1 |- *;
          cbn [Z.eqb] in Hs1;
          rewrite Hs1;
          mod_ring_zero.
      - exact Hxan.
      - rewrite Hya in Hg2. exact Hg2. }
    rewrite Hstep_group.
    unfold macc.
    f_equal.
    f_equal.
    (* The multiple recurrence: absorbing bit [m]. *)
    unfold c, bit, scalar_bit.
    set (z := mk alpha / 2 ^ Z.of_nat m).
    assert (Hpow : 0 < 2 ^ Z.of_nat m)
      by (apply Z.pow_pos_nonneg; lia).
    assert (Hzsucc : mk alpha / 2 ^ Z.of_nat (S m) = z / 2).
    { unfold z.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite (Z.mul_comm 2 (2 ^ Z.of_nat m)).
      rewrite <- Z.div_div by (clear -Hpow; lia).
      reflexivity. }
    rewrite Hzsucc.
    assert (Hpowsucc :
        2 ^ (255 - Z.of_nat m) = 2 * 2 ^ (255 - Z.of_nat (S m))).
    { rewrite Nat2Z.inj_succ.
      replace (255 - Z.of_nat m)
        with (Z.succ (255 - Z.succ (Z.of_nat m)))
        by (clear -Hm; lia).
      rewrite Z.pow_succ_r by (clear -Hm; lia).
      reflexivity. }
    rewrite Hpowsucc.
    pose proof (Z.div_mod z 2 ltac:(lia)) as Hdm.
    clear -Hdm.
    lia.
  Qed.
  (** ** The fold chain: rows and accumulators of [ladder_go] *)

  Lemma ladder_go_cons (B : Point.t) (k : Z) (acc : Point.t) (i n : nat) :
    OrchardVarBaseTables.ladder_go B k acc i (S n) =
    (fst (OrchardVarBaseTables.ladder_step B (scalar_bit k i) acc)
       :: fst (OrchardVarBaseTables.ladder_go B k
            (snd (OrchardVarBaseTables.ladder_step B (scalar_bit k i) acc))
            (Nat.pred i) n),
     snd (OrchardVarBaseTables.ladder_go B k
       (snd (OrchardVarBaseTables.ladder_step B (scalar_bit k i) acc))
       (Nat.pred i) n)).
  Proof.
    cbn [OrchardVarBaseTables.ladder_go].
    rewrite (surjective_pairing
      (OrchardVarBaseTables.ladder_step B (scalar_bit k i) acc)).
    rewrite (surjective_pairing
      (OrchardVarBaseTables.ladder_go B k
        (snd (OrchardVarBaseTables.ladder_step B (scalar_bit k i) acc))
        (Nat.pred i) n)).
    reflexivity.
  Qed.

  (** The invariant chain of one incomplete half: from [macc (S i)], [count]
      nondegenerate steps land on [macc (S i − count)], and the [j]-th
      emitted row is the [ladder_step] row at the [j]-th intermediate
      accumulator. *)
  Lemma ladder_go_chain (alpha : Z) (B : Point.t)
      (HB : point_ok B) (Hlad : ladder_ok alpha B) :
    forall (count i : nat),
      (count + 4 <= S i)%nat -> (i < 255)%nat ->
      snd (OrchardVarBaseTables.ladder_go B (mk alpha)
        (macc alpha B (S i)) i count) = macc alpha B (S i - count) /\
      (forall j : nat, (j < count)%nat ->
        List.nth j
          (fst (OrchardVarBaseTables.ladder_go B (mk alpha)
            (macc alpha B (S i)) i count))
          OrchardVarBaseTables.sr0 =
        fst (OrchardVarBaseTables.ladder_step B
          (scalar_bit (mk alpha) (i - j)) (macc alpha B (S (i - j))))).
  Proof.
    induction count as [| count IH]; intros i Hlow Hhi.
    - cbn [OrchardVarBaseTables.ladder_go fst snd].
      rewrite Nat.sub_0_r.
      split; [reflexivity | intros j Hj; exfalso; lia].
    - rewrite ladder_go_cons.
      cbn [fst snd].
      assert (Hstep : step_ok alpha B i) by (apply Hlad; lia).
      pose proof (ladder_step_macc alpha B i HB ltac:(lia) Hstep) as Hs.
      rewrite Hs.
      destruct i as [| i']; [exfalso; lia |].
      cbn [Nat.pred].
      specialize (IH i' ltac:(lia) ltac:(lia)).
      destruct IH as [IHacc IHrows].
      split.
      + rewrite IHacc.
        f_equal.
        lia.
      + intros j Hj.
        destruct j as [| j'].
        * cbn [List.nth].
          rewrite Nat.sub_0_r.
          reflexivity.
        * cbn [List.nth].
          replace (S i' - S j')%nat with (i' - j')%nat by lia.
          exact (IHrows j' ltac:(lia)).
  Qed.

  (** ** The chain at the tables record

      [vb_columns alpha B] instantiates the two halves at the honest scalar
      and base; under [point_ok] and [ladder_ok] the boundary accumulators
      are the [macc] values and each step row reads the [macc] chain. *)

  Section Chain.
    Variable alpha : Z.
    Variable B : Point.t.
    Hypothesis HB : point_ok B.
    Hypothesis Hlad : ladder_ok alpha B.
    Hypothesis Hk : 0 <= mk alpha < 2 ^ 255.

    Let vb := OrchardVarBaseTables.vb_columns alpha B.

    Lemma vb_hi_unfold :
      OrchardVarBaseTables.vb_hi vb =
      fst (OrchardVarBaseTables.ladder_go B (mk alpha)
        (EccSpec.point_add B B) 254 125).
    Proof.
      unfold vb.
      rewrite vb_columns_eq.
      cbv zeta.
      cbn [OrchardVarBaseTables.vb_hi].
      reflexivity.
    Qed.

    Lemma vb_acc130_unfold :
      OrchardVarBaseTables.vb_acc130 vb =
      snd (OrchardVarBaseTables.ladder_go B (mk alpha)
        (EccSpec.point_add B B) 254 125).
    Proof.
      unfold vb.
      rewrite vb_columns_eq.
      cbv zeta.
      cbn [OrchardVarBaseTables.vb_acc130].
      reflexivity.
    Qed.

    Lemma vb_lo_unfold :
      OrchardVarBaseTables.vb_lo vb =
      fst (OrchardVarBaseTables.ladder_go B (mk alpha)
        (snd (OrchardVarBaseTables.ladder_go B (mk alpha)
          (EccSpec.point_add B B) 254 125)) 129 126).
    Proof.
      unfold vb.
      rewrite vb_columns_eq.
      cbv zeta.
      cbn [OrchardVarBaseTables.vb_lo].
      reflexivity.
    Qed.

    Lemma vb_acc4_unfold :
      OrchardVarBaseTables.vb_acc4 vb =
      snd (OrchardVarBaseTables.ladder_go B (mk alpha)
        (snd (OrchardVarBaseTables.ladder_go B (mk alpha)
          (EccSpec.point_add B B) 254 125)) 129 126).
    Proof.
      unfold vb.
      rewrite vb_columns_eq.
      cbv zeta.
      cbn [OrchardVarBaseTables.vb_acc4].
      reflexivity.
    Qed.

    (** The hi-half chain. *)
    Lemma hi_chain :
      OrchardVarBaseTables.vb_acc130 vb = macc alpha B 130 /\
      (forall j : nat, (j < 125)%nat ->
        List.nth j (OrchardVarBaseTables.vb_hi vb)
          OrchardVarBaseTables.sr0 =
        fst (OrchardVarBaseTables.ladder_step B
          (scalar_bit (mk alpha) (254 - j)) (macc alpha B (S (254 - j))))).
    Proof.
      pose proof (ladder_go_chain alpha B HB Hlad 125 254
        ltac:(lia) ltac:(lia)) as (Hacc & Hrows).
      rewrite (macc_255 alpha B HB Hk) in Hacc, Hrows.
      change (S 254 - 125)%nat with 130%nat in Hacc.
      split.
      - rewrite vb_acc130_unfold. exact Hacc.
      - intros j Hj.
        rewrite vb_hi_unfold.
        exact (Hrows j Hj).
    Qed.

    (** The lo-half chain. *)
    Lemma lo_chain :
      OrchardVarBaseTables.vb_acc4 vb = macc alpha B 4 /\
      (forall j : nat, (j < 126)%nat ->
        List.nth j (OrchardVarBaseTables.vb_lo vb)
          OrchardVarBaseTables.sr0 =
        fst (OrchardVarBaseTables.ladder_step B
          (scalar_bit (mk alpha) (129 - j)) (macc alpha B (S (129 - j))))).
    Proof.
      pose proof (ladder_go_chain alpha B HB Hlad 126 129
        ltac:(lia) ltac:(lia)) as (Hacc & Hrows).
      change (S 129 - 126)%nat with 4%nat in Hacc.
      pose proof (proj1 hi_chain) as Hacc130.
      rewrite vb_acc130_unfold in Hacc130.
      split.
      - rewrite vb_acc4_unfold, Hacc130.
        exact Hacc.
      - intros j Hj.
        rewrite vb_lo_unfold, Hacc130.
        exact (Hrows j Hj).
    Qed.
  End Chain.
  (** ** Guarded bodies of the family's selectors

      Each selector's guarded constraints are pinned to the raw bodies of
      its defining gate by one [vm_compute] over the configured system. *)

  Definition gate_raw_bodies (g : Gate.t columns)
      : list (Constraint.t columns) :=
    List.flat_map
      (fun '(_, c) =>
        match c with
        | Constraint.Select _ body => [body]
        | _ => []
        end)
      g.(Gate.constraints).

  Lemma bodies_ecc_add :
    guarded_bodies Selector.QEccAdd =
    gate_raw_bodies
      Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate)).
  Qed.

  Lemma bodies_hi1 :
    guarded_bodies Selector.QMulIncompleteHi1 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
        Selector.QMulIncompleteHi1 A3 A0 A4 A5).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteHi1 A3 A0 A4 A5))).
  Qed.

  Lemma bodies_hi2 :
    guarded_bodies Selector.QMulIncompleteHi2 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
        Selector.QMulIncompleteHi2 A9 A3 A0 A1 A4 A5).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteHi2 A9 A3 A0 A1 A4 A5))).
  Qed.

  Lemma bodies_hi3 :
    guarded_bodies Selector.QMulIncompleteHi3 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
        Selector.QMulIncompleteHi3 A9 A3 A0 A1 A4 A5).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteHi3 A9 A3 A0 A1 A4 A5))).
  Qed.

  Lemma bodies_lo1 :
    guarded_bodies Selector.QMulIncompleteLo1 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
        Selector.QMulIncompleteLo1 A7 A0 A8 A2).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteLo1 A7 A0 A8 A2))).
  Qed.

  Lemma bodies_lo2 :
    guarded_bodies Selector.QMulIncompleteLo2 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
        Selector.QMulIncompleteLo2 A6 A7 A0 A1 A8 A2).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteLo2 A6 A7 A0 A1 A8 A2))).
  Qed.

  Lemma bodies_lo3 :
    guarded_bodies Selector.QMulIncompleteLo3 =
    gate_raw_bodies
      (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
        Selector.QMulIncompleteLo3 A6 A7 A0 A1 A8 A2).
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteLo3 A6 A7 A0 A1 A8 A2))).
  Qed.

  Lemma bodies_decompose :
    guarded_bodies Selector.QMulDecomposeVar =
    gate_raw_bodies
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
        .decompose_scalar_complete_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
          .decompose_scalar_complete_gate)).
  Qed.

  Lemma bodies_lsb :
    guarded_bodies Selector.QMulLsb =
    gate_raw_bodies Garden.Halo2.halo2_gadgets.ecc.chip.mul.lsb_check_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.lsb_check_gate)).
  Qed.

  Lemma bodies_overflow :
    guarded_bodies Selector.QMulOverflow =
    gate_raw_bodies
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.overflow_checks_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow
          .overflow_checks_gate)).
  Qed.

  Lemma bodies_witness_non_id :
    guarded_bodies Selector.QWitnessPointNonId =
    gate_raw_bodies
      Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .witness_non_identity_point_gate.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (gate_raw_bodies
        Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .witness_non_identity_point_gate)).
  Qed.

  Lemma bodies_qlookup : guarded_bodies Selector.QLookup = [].
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns)) []).
  Qed.

  Lemma bodies_qrunning : guarded_bodies Selector.QRunning = [].
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns)) []).
  Qed.

  (** ** Field projections of the ladder record *)

  Ltac vbfield :=
    rewrite vb_columns_eq; cbv zeta;
    cbn [OrchardVarBaseTables.vb_scalar OrchardVarBaseTables.vb_hi
         OrchardVarBaseTables.vb_lo OrchardVarBaseTables.vb_d
         OrchardVarBaseTables.vb_acc130 OrchardVarBaseTables.vb_acc4
         OrchardVarBaseTables.vb_p3 OrchardVarBaseTables.vb_mid3
         OrchardVarBaseTables.vb_acc3 OrchardVarBaseTables.vb_p2
         OrchardVarBaseTables.vb_mid2 OrchardVarBaseTables.vb_acc2
         OrchardVarBaseTables.vb_p1 OrchardVarBaseTables.vb_mid1
         OrchardVarBaseTables.vb_acc1 OrchardVarBaseTables.vb_p0
         OrchardVarBaseTables.vb_out OrchardVarBaseTables.vb_k254
         OrchardVarBaseTables.vb_s OrchardVarBaseTables.vb_eta];
    reflexivity.

  Lemma vb_scalar_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_scalar (vbc alpha B) = mk alpha.
  Proof. vbfield. Qed.

  Lemma vb_d_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_d (vbc alpha B) = EccSpec.point_add B B.
  Proof. vbfield. Qed.

  Lemma vb_p3_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_p3 (vbc alpha B) =
    OrchardVarBaseTables.signed_pt B (scalar_bit (mk alpha) 3).
  Proof. vbfield. Qed.

  Lemma vb_p2_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_p2 (vbc alpha B) =
    OrchardVarBaseTables.signed_pt B (scalar_bit (mk alpha) 2).
  Proof. vbfield. Qed.

  Lemma vb_p1_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_p1 (vbc alpha B) =
    OrchardVarBaseTables.signed_pt B (scalar_bit (mk alpha) 1).
  Proof. vbfield. Qed.

  Lemma vb_p0_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_p0 (vbc alpha B) =
    OrchardVarBaseTables.lsb_pt B (scalar_bit (mk alpha) 0).
  Proof. vbfield. Qed.

  Lemma vb_mid3_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_mid3 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_p3 (vbc alpha B))
      (OrchardVarBaseTables.vb_acc4 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_acc3_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_acc3 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_acc4 (vbc alpha B))
      (OrchardVarBaseTables.vb_mid3 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_mid2_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_mid2 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_p2 (vbc alpha B))
      (OrchardVarBaseTables.vb_acc3 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_acc2_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_acc2 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_acc3 (vbc alpha B))
      (OrchardVarBaseTables.vb_mid2 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_mid1_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_mid1 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_p1 (vbc alpha B))
      (OrchardVarBaseTables.vb_acc2 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_acc1_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_acc1 (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_acc2 (vbc alpha B))
      (OrchardVarBaseTables.vb_mid1 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_out_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_out (vbc alpha B) =
    EccSpec.point_add (OrchardVarBaseTables.vb_p0 (vbc alpha B))
      (OrchardVarBaseTables.vb_acc1 (vbc alpha B)).
  Proof. vbfield. Qed.

  Lemma vb_k254_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_k254 (vbc alpha B) = mk alpha / 2 ^ 254.
  Proof. vbfield. Qed.

  Lemma vb_s_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_s (vbc alpha B) =
    (alpha + mk alpha / 2 ^ 254 * 2 ^ 130) mod Primes.pallas_p.
  Proof. vbfield. Qed.

  Lemma vb_eta_e (alpha : Z) (B : Point.t) :
    OrchardVarBaseTables.vb_eta (vbc alpha B) =
    (if mk alpha / 2 ^ 130 =? 0
     then 0
     else mod_inverse (mk alpha / 2 ^ 130) Primes.pallas_p).
  Proof. vbfield. Qed.

  (** The tables' ladder record at the specification scalar. *)
  Lemma t_vb_ivk (w : HonestInput) :
    OCT.t_vb (OCT.tables_of w) = vbc (ivk w) (hi_g_d_old w).
  Proof.
    rewrite t_vb_eq, t_ivk_eq.
    reflexivity.
  Qed.

  Lemma t_vb_result_ivk (w : HonestInput) :
    OCT.t_vb_result (OCT.tables_of w) =
    PallasModel.repr
      (Pallas.mul (ivk w) (PallasModel.unrepr (hi_g_d_old w))).
  Proof.
    rewrite t_vb_result_eq, t_ivk_eq.
    reflexivity.
  Qed.

  (** ** Rotation and plane helpers *)

  Lemma rot_prev (r : Z) : rotated_row r Rotation.prev = r - 1.
  Proof.
    unfold rotated_row.
    cbn [Rotation.prev Rotation.offset].
    lia.
  Qed.

  Lemma rot_cur (r : Z) : rotated_row r Rotation.cur = r.
  Proof.
    unfold rotated_row.
    cbn [Rotation.cur Rotation.offset].
    lia.
  Qed.

  Lemma rot_next (r : Z) : rotated_row r Rotation.next = r + 1.
  Proof. reflexivity. Qed.

  Definition memb (sel : Selector.t) (region : RegionId.t) (row : Z)
      : bool :=
    Complete.enabled_memb OrchardHonestAssignment.selector_eqb
      OrchardHonestAssignment.region_eqb OrchardHonestAssignment.facts
      sel region row.

  Lemma memb_of_in (sel : Selector.t) (region : RegionId.t) (row : Z) :
    List.In (sel, region, row) enabled ->
    memb sel region row = true.
  Proof.
    intros Hin.
    exact (Complete.enabled_memb_complete
      OrchardHonestAssignment.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardHonestAssignment.region_eqb OrchardDecidableEq.region_id_eqb_eq
      OrchardHonestAssignment.facts sel region row Hin).
  Qed.

  Lemma hsel_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.selector) =
    fun sel region row => if memb sel region row then 1 else 0.
  Proof. reflexivity. Qed.

  Lemma hlookup_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.lookup) =
    fun column row =>
      Complete.table_value OrchardHonestAssignment.lookup_eqb
        OrchardHonestAssignment.facts column row.
  Proof. reflexivity. Qed.

  (** Both range-check selectors are on at the overflow-lookup rows. *)
  Lemma ovl_memb_cert :
    List.forallb
      (fun r =>
        (memb Selector.QLookup ovl_region (Z.of_nat r) &&
         memb Selector.QRunning ovl_region (Z.of_nat r))%bool)
      (List.seq 0 13) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma ovl_memb (r : Z) (H0 : 0 <= r) (H12 : r <= 12) :
    memb Selector.QLookup ovl_region r = true /\
    memb Selector.QRunning ovl_region r = true.
  Proof.
    assert (Hin : List.In (Z.to_nat r) (List.seq 0 13))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) ovl_memb_cert _ Hin) as Hf.
    cbn beta in Hf.
    rewrite Z2Nat.id in Hf by lia.
    apply Bool.andb_true_iff in Hf.
    exact Hf.
  Qed.

  (** The loaded [TableIdx] table holds [i] at row [i]. *)
  Lemma table_idx_cert :
    List.forallb
      (fun i =>
        Complete.table_value OrchardHonestAssignment.lookup_eqb
          OrchardHonestAssignment.facts Lookup.TableIdx (Z.of_nat i)
        =? Z.of_nat i)
      (List.seq 0 1024) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma table_value_id (v : Z) (Hv : 0 <= v < 1024) :
    Complete.table_value OrchardHonestAssignment.lookup_eqb
      OrchardHonestAssignment.facts Lookup.TableIdx v = v.
  Proof.
    assert (Hin : List.In (Z.to_nat v) (List.seq 0 1024))
      by (apply List.in_seq; lia).
    pose proof (proj1 (List.forallb_forall _ _) table_idx_cert _ Hin) as Hf.
    cbn beta in Hf.
    rewrite Z2Nat.id in Hf by lia.
    exact (proj1 (Z.eqb_eq _ _) Hf).
  Qed.

  (** ** The range-check lookup argument *)

  Definition rotation_eq_dec (x y : Rotation.t) : {x = y} + {x <> y}.
  Proof. decide equality; apply Z.eq_dec. Defined.

  Definition expression_eq_dec (x y : Expression.t columns)
      : {x = y} + {x <> y}.
  Proof.
    decide equality;
      first
        [ apply Z.eq_dec
        | apply rotation_eq_dec
        | apply OrchardDecidableEq.selector_eq_dec
        | apply OrchardDecidableEq.fixed_eq_dec
        | apply OrchardDecidableEq.advice_eq_dec
        | apply OrchardDecidableEq.instance_eq_dec ].
  Defined.

  Definition arg_eq_dec (x y : LookupArgument.t columns)
      : {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply List.list_eq_dec.
    decide equality.
    - apply OrchardDecidableEq.lookup_eq_dec.
    - apply expression_eq_dec.
  Defined.

  Definition arg_eqb : LookupArgument.t columns
      -> LookupArgument.t columns -> bool :=
    OrchardDecidableEq.dec_to_eqb arg_eq_dec.
  Definition arg_eqb_eq (x y : LookupArgument.t columns) :
      arg_eqb x y = true <-> x = y :=
    OrchardDecidableEq.dec_to_eqb_eq arg_eq_dec x y.

  (** The range-check argument as configured
      ([lookup_range_check.configure] at [k = 10], column [A9], table
      [TableIdx]). *)
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
                (Expression.Negated
                  (Expression.Selector Selector.QRunning)))
              (Expression.Advice Advice.A9 Rotation.cur))),
        Lookup.TableIdx)];
  |}.

  (** No lookup argument mentions any of the family's gate selectors. *)
  Lemma vb_mentions_cert :
    List.forallb
      (fun arg =>
        (negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QEccAdd arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteHi1 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteHi2 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteHi3 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteLo1 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteLo2 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulIncompleteLo3 arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulDecomposeVar arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulLsb arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QMulOverflow arg) &&
         negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QWitnessPointNonId arg))%bool)
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Every argument mentioning a range-check selector is the range
      argument. *)
  Lemma range_arg_only_cert :
    List.forallb
      (fun arg =>
        (negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
                 Selector.QLookup arg
               || Complete.arg_mentions_selector
                    OrchardDecidableEq.selector_eqb
                    Selector.QRunning arg)
         || arg_eqb arg range_arg)%bool)
      system.(ConstraintSystem.lookups) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma range_arg_only (arg : LookupArgument.t columns)
      (Harg : List.In arg system.(ConstraintSystem.lookups))
      (Hmention :
        Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
          Selector.QLookup arg = true \/
        Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
          Selector.QRunning arg = true) :
    arg = range_arg.
  Proof.
    pose proof (proj1 (List.forallb_forall _ _) range_arg_only_cert
      arg Harg) as Hf.
    cbn beta in Hf.
    apply Bool.orb_true_iff in Hf.
    destruct Hf as [Hf | Hf].
    - exfalso.
      apply Bool.negb_true_iff in Hf.
      apply Bool.orb_false_iff in Hf.
      destruct Hf as (Hf1 & Hf2).
      destruct Hmention as [Hm | Hm]; congruence.
    - exact (proj1 (arg_eqb_eq _ _) Hf).
  Qed.
  (** ** Evaluation helpers *)

  (** Reduce a gate body's evaluation, keeping the field operations, the
      constants, the heavy generator and the region tags folded.  The
      concrete-row variant lets [rotated_row] compute; the symbolic-row
      variant keeps it folded for the [rot_*] rewrites. *)
  Ltac gate_cbn :=
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from UnOp.opp
       mod_inverse Z.pow Z.div Z.modulo
       Primes.pallas_p Primes.t_p Primes.t_q
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv
       vb_region ovs_region ovl_region ovc_region wpkd_region
       OrchardHonestAssignment.honest_assignment]
      cbn.

  Ltac gate_cbn_sym :=
    with_strategy opaque
      [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from UnOp.opp
       mod_inverse Z.pow Z.div Z.modulo rotated_row
       Primes.pallas_p Primes.t_p Primes.t_q
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b
       Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv
       vb_region ovs_region ovl_region ovc_region wpkd_region
       OrchardHonestAssignment.honest_assignment]
      cbn.

  (** The bit recovered from two adjacent running-sum cells. *)
  Lemma bit_eval_pair (k e f : Z) (He : 0 <= e) (Hf : f = e + 1) :
    UnOp.from (k / 2 ^ e) -F (UnOp.from 2 *F UnOp.from (k / 2 ^ f)) =
    (k / 2 ^ e) mod 2.
  Proof.
    subst f.
    assert (Hpos : 0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
    assert (Hstep : k / 2 ^ e =
        2 * (k / 2 ^ (e + 1)) + (k / 2 ^ e) mod 2).
    { replace (e + 1) with (Z.succ e) by lia.
      rewrite Z.pow_succ_r by lia.
      rewrite (Z.mul_comm 2 (2 ^ e)).
      rewrite <- Z.div_div by (clear -Hpos; lia).
      pose proof (Z.div_mod (k / 2 ^ e) 2 ltac:(lia)) as Hdm.
      clear -Hdm.
      lia. }
    set (q2 := k / 2 ^ (e + 1)) in *.
    set (b := (k / 2 ^ e) mod 2) in *.
    assert (Hb : 0 <= b < 2)
      by (unfold b; apply Z.mod_pos_bound; lia).
    unfold BinOp.sub, BinOp.mul, UnOp.from.
    transitivity (b mod Primes.pallas_p).
    2:{ apply Z.mod_small.
        pose proof pallas_p_pos as Hp.
        clear -Hb Hp.
        lia. }
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    f_equal.
    rewrite Hstep.
    ring.
  Qed.

  (** The last bit, from the raw scalar cell and the [z₁] cell. *)
  Lemma lsb_bit_eval (k : Z) :
    UnOp.from k -F (UnOp.from (k / 2 ^ 1) *F UnOp.from 2) = k mod 2.
  Proof.
    assert (Hstep : k = 2 * (k / 2 ^ 1) + k mod 2).
    { change (2 ^ 1) with 2.
      pose proof (Z.div_mod k 2 ltac:(lia)) as Hdm.
      clear -Hdm.
      lia. }
    set (q2 := k / 2 ^ 1) in *.
    set (b := k mod 2) in *.
    assert (Hb : 0 <= b < 2)
      by (unfold b; apply Z.mod_pos_bound; lia).
    unfold BinOp.sub, BinOp.mul, UnOp.from.
    transitivity (b mod Primes.pallas_p).
    2:{ apply Z.mod_small.
        pose proof pallas_p_pos as Hp.
        clear -Hb Hp.
        lia. }
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    f_equal.
    rewrite Hstep.
    ring.
  Qed.

  Lemma isbool_mod2 (x : Z) : IsBool.t (x mod 2).
  Proof.
    pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hb.
    assert (H : x mod 2 = 0 \/ x mod 2 = 1) by lia.
    destruct H as [H | H]; rewrite H; reflexivity.
  Qed.

  Lemma scalar_bit_0_mod2 (k : Z) : scalar_bit k 0 = k mod 2.
  Proof.
    unfold scalar_bit.
    change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, Z.div_1_r.
    reflexivity.
  Qed.

  (** ** Site: the scalar-decomposition gate of the complete rounds *)

  Lemma decompose_core (w : HonestInput) (row e f : Z) (i : nat)
      (He : 0 <= e) (Hf : f = e + 1) (Hei : e = Z.of_nat i)
      (Hzp : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) A9 vb_region (row - 1) =
        mk (ivk w) / 2 ^ f)
      (Hzn : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) A9 vb_region (row + 1) =
        mk (ivk w) / 2 ^ e)
      (Hby : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) A9 vb_region row = Point.y (hi_g_d_old w))
      (Hyp : (OrchardHonestAssignment.honest_assignment w)
          .(Assignment.advice) A1 vb_region (row - 1) =
        Point.y (OrchardVarBaseTables.signed_pt (hi_g_d_old w)
          (scalar_bit (mk (ivk w)) i)))
      (body : Constraint.t columns)
      (Hbody : List.In body
        (gate_raw_bodies
          Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
            .decompose_scalar_complete_gate)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (vb_region, row) body.
  Proof.
    cbn in Hbody.
    destruct Hbody as [H | [H | []]]; subst body.
    - (* bool_check *)
      gate_cbn_sym.
      rewrite rot_prev, rot_next.
      rewrite Hzp, Hzn.
      rewrite (bit_eval_pair (mk (ivk w)) e f He Hf).
      apply isbool_mod2.
    - (* y_switch *)
      gate_cbn_sym.
      rewrite rot_prev, rot_cur, rot_next.
      rewrite Hzp, Hzn, Hby, Hyp.
      rewrite (bit_eval_pair (mk (ivk w)) e f He Hf).
      subst e.
      change ((mk (ivk w) / 2 ^ Z.of_nat i) mod 2)
        with (scalar_bit (mk (ivk w)) i).
      destruct (scalar_bit_01 (mk (ivk w)) i) as [Hb | Hb];
        rewrite Hb;
        unfold OrchardVarBaseTables.signed_pt;
        cbn [Z.eqb];
        [ unfold point_neg; cbn [Point.x Point.y] | ];
        mod_ring_zero.
  Qed.

  Lemma site_decompose (w : HonestInput)
      (row : Z) (Hrow : row = 130 \/ row = 132 \/ row = 134)
      (body : Constraint.t columns)
      (Hbody : List.In body (guarded_bodies Selector.QMulDecomposeVar)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (vb_region, row) body.
  Proof.
    rewrite bodies_decompose in Hbody.
    destruct Hrow as [-> | [-> | ->]].
    - apply (decompose_core w 130 3 4 3%nat ltac:(lia) ltac:(lia)
        ltac:(reflexivity));
        try exact Hbody.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + reflexivity.
      + rewrite <- (vb_p3_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
    - apply (decompose_core w 132 2 3 2%nat ltac:(lia) ltac:(lia)
        ltac:(reflexivity));
        try exact Hbody.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + reflexivity.
      + rewrite <- (vb_p2_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
    - apply (decompose_core w 134 1 2 1%nat ltac:(lia) ltac:(lia)
        ltac:(reflexivity));
        try exact Hbody.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
      + reflexivity.
      + rewrite <- (vb_p1_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
        reflexivity.
  Qed.

  (** ** Site: the LSB gate *)

  Lemma site_lsb (w : HonestInput)
      (body : Constraint.t columns)
      (Hbody : List.In body (guarded_bodies Selector.QMulLsb)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (vb_region, 135) body.
  Proof.
    rewrite bodies_lsb in Hbody.
    assert (Hz1 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A9 vb_region 135 = mk (ivk w) / 2 ^ 1).
    { rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hz0 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A9 vb_region 136 = mk (ivk w)).
    { rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hx0 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A0 vb_region 135 =
      Point.x (OrchardVarBaseTables.lsb_pt (hi_g_d_old w)
        (scalar_bit (mk (ivk w)) 0))).
    { rewrite <- (vb_p0_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hy0 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A1 vb_region 135 =
      Point.y (OrchardVarBaseTables.lsb_pt (hi_g_d_old w)
        (scalar_bit (mk (ivk w)) 0))).
    { rewrite <- (vb_p0_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (HxB : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A0 vb_region 136 = Point.x (hi_g_d_old w))
      by reflexivity.
    assert (HyB : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A1 vb_region 136 = Point.y (hi_g_d_old w))
      by reflexivity.
    cbn in Hbody.
    destruct Hbody as [H | [H | [H | []]]]; subst body.
    - (* bool_check *)
      gate_cbn.
      rewrite Hz0, Hz1.
      rewrite lsb_bit_eval.
      apply isbool_mod2.
    - (* lsb_x *)
      gate_cbn.
      rewrite Hz0, Hz1, Hx0, HxB.
      rewrite lsb_bit_eval.
      rewrite <- scalar_bit_0_mod2.
      destruct (scalar_bit_01 (mk (ivk w)) 0) as [Hb | Hb];
        rewrite Hb;
        unfold OrchardVarBaseTables.lsb_pt;
        cbn [Z.eqb];
        [ unfold point_neg; cbn [Point.x Point.y] | cbn [Point.x Point.y] ];
        mod_ring_zero.
    - (* lsb_y *)
      gate_cbn.
      rewrite Hz0, Hz1, Hy0, HyB.
      rewrite lsb_bit_eval.
      rewrite <- scalar_bit_0_mod2.
      destruct (scalar_bit_01 (mk (ivk w)) 0) as [Hb | Hb];
        rewrite Hb;
        unfold OrchardVarBaseTables.lsb_pt;
        cbn [Z.eqb];
        [ unfold point_neg; cbn [Point.x Point.y] | cbn [Point.x Point.y] ];
        mod_ring_zero.
  Qed.

  (** ** Site: the overflow gate *)

  Lemma overflow_k254_bit (a : Z) (Ha : 0 <= a < Primes.pallas_p) :
    mk a / 2 ^ 254 = 0 \/ mk a / 2 ^ 254 = 1.
  Proof.
    assert (Hk : 0 <= mk a < 2 ^ 255).
    { unfold mk.
      unfold Primes.pallas_p, Primes.t_p in Ha.
      unfold Primes.t_q.
      lia. }
    pose proof (Z.div_lt_upper_bound (mk a) (2 ^ 254) 2
      ltac:(lia) ltac:(clear -Hk; lia)) as Hup.
    pose proof (Z.div_pos (mk a) (2 ^ 254)
      ltac:(clear -Hk; lia) ltac:(lia)) as Hlo.
    clear -Hup Hlo.
    lia.
  Qed.

  Lemma overflow_high (a : Z) (Ha : 0 <= a < Primes.pallas_p)
      (Hk1 : mk a / 2 ^ 254 = 1) :
    2 ^ 254 <= mk a < 2 ^ 254 + 2 ^ 130.
  Proof.
    assert (Hup : mk a < 2 ^ 254 + 2 ^ 130).
    { unfold mk.
      unfold Primes.pallas_p, Primes.t_p in Ha.
      unfold Primes.t_q.
      clear -Ha.
      lia. }
    split; [| exact Hup].
    pose proof (Z.mod_pos_bound (mk a) (2 ^ 254) ltac:(lia)) as Hm.
    pose proof (Z.div_mod (mk a) (2 ^ 254) ltac:(lia)) as Hdm.
    rewrite Hk1 in Hdm.
    clear -Hm Hdm.
    lia.
  Qed.

  Lemma overflow_z130_k1 (a : Z) (Ha : 0 <= a < Primes.pallas_p)
      (Hk1 : mk a / 2 ^ 254 = 1) :
    mk a / 2 ^ 130 = 2 ^ 124.
  Proof.
    pose proof (overflow_high a Ha Hk1) as Hb.
    replace (mk a) with (2 ^ 124 * 2 ^ 130 + (mk a - 2 ^ 254))
      by (clear -Hb; lia).
    rewrite Z.div_add_l by (clear; lia).
    rewrite (Z.div_small (mk a - 2 ^ 254)) by (clear -Hb; lia).
    clear; lia.
  Qed.

  Lemma overflow_s_low_k1 (a : Z) (Ha : 0 <= a < Primes.pallas_p)
      (Hk1 : mk a / 2 ^ 254 = 1) :
    (a + mk a / 2 ^ 254 * 2 ^ 130) mod Primes.pallas_p / 2 ^ 130 = 0.
  Proof.
    pose proof (overflow_high a Ha Hk1) as Hb.
    rewrite Hk1.
    assert (Hmod : (a + 1 * 2 ^ 130) mod Primes.pallas_p =
        a + 2 ^ 130 - Primes.pallas_p).
    { apply (Z.mod_unique _ _ 1).
      - left.
        unfold mk in Hb.
        unfold Primes.pallas_p, Primes.t_p in *.
        unfold Primes.t_q in Hb.
        clear -Ha Hb.
        lia.
      - clear; lia. }
    rewrite Hmod.
    apply Z.div_small.
    unfold mk in Hb.
    unfold Primes.pallas_p, Primes.t_p in *.
    unfold Primes.t_q in Hb.
    clear -Ha Hb.
    lia.
  Qed.

  Lemma overflow_s_low_k0 (a : Z) (Ha : 0 <= a < Primes.pallas_p)
      (Hz : mk a / 2 ^ 130 = 0) :
    (a + mk a / 2 ^ 254 * 2 ^ 130) mod Primes.pallas_p / 2 ^ 130 = 0.
  Proof.
    assert (Hks : 0 <= mk a < 2 ^ 130).
    { pose proof (Z.mod_pos_bound (mk a) (2 ^ 130) ltac:(lia)) as Hm.
      pose proof (Z.div_mod (mk a) (2 ^ 130) ltac:(lia)) as Hdm.
      rewrite Hz in Hdm.
      clear -Hm Hdm.
      lia. }
    assert (Hk254 : mk a / 2 ^ 254 = 0)
      by (apply Z.div_small; clear -Hks; lia).
    rewrite Hk254.
    rewrite Z.mul_0_l, Z.add_0_r.
    rewrite Z.mod_small by (clear -Ha; lia).
    apply Z.div_small.
    unfold mk in Hks.
    unfold Primes.t_q in Hks.
    clear -Hks Ha.
    lia.
  Qed.

  Lemma overflow_eta_eval (a : Z) (Ha : 0 <= a < Primes.pallas_p)
      (Hz : mk a / 2 ^ 130 <> 0) :
    UnOp.from 1 =
    UnOp.from (mk a / 2 ^ 130) *F
      UnOp.from (mod_inverse (mk a / 2 ^ 130) Primes.pallas_p).
  Proof.
    assert (Hk : 0 <= mk a < 2 ^ 255).
    { unfold mk.
      unfold Primes.pallas_p, Primes.t_p in Ha.
      unfold Primes.t_q.
      lia. }
    assert (Hpos : 0 <= mk a / 2 ^ 130 < Primes.pallas_p).
    { split.
      - apply Z.div_pos; [clear -Hk; lia | clear; lia].
      - apply Z.div_lt_upper_bound; [clear; lia |].
        unfold Primes.pallas_p, Primes.t_p.
        clear -Hk.
        lia. }
    assert (Hnz : (mk a / 2 ^ 130) mod Primes.pallas_p <> 0).
    { rewrite Z.mod_small by exact Hpos.
      exact Hz. }
    pose proof (mod_inverse_mul_prime (p := Primes.pallas_p)
      (mk a / 2 ^ 130) Hnz) as Hinv.
    unfold BinOp.mul, UnOp.from in Hinv |- *.
    rewrite Zdiv.Zmult_mod_idemp_l, Zdiv.Zmult_mod_idemp_r.
    rewrite (Z.mul_comm (mk a / 2 ^ 130)
      (mod_inverse (mk a / 2 ^ 130) Primes.pallas_p)).
    rewrite Hinv.
    symmetry.
    apply Z.mod_1_l.
    pose proof pallas_p_pos as Hp.
    clear -Hp.
    lia.
  Qed.

  Lemma from_zero : UnOp.from 0 = 0.
  Proof.
    unfold UnOp.from.
    apply Zmod_0_l.
  Qed.

  Lemma site_overflow (w : HonestInput)
      (body : Constraint.t columns)
      (Hbody : List.In body (guarded_bodies Selector.QMulOverflow)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (ovc_region, 1) body.
  Proof.
    rewrite bodies_overflow in Hbody.
    pose proof (ivk_range w) as Hival.
    assert (Hz0 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A6 ovc_region 0 = mk (ivk w)).
    { rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hz130 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A6 ovc_region 1 = mk (ivk w) / 2 ^ 130).
    { rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Heta : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A6 ovc_region 2 =
      (if mk (ivk w) / 2 ^ 130 =? 0
       then 0
       else mod_inverse (mk (ivk w) / 2 ^ 130) Primes.pallas_p)).
    { rewrite <- (vb_eta_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hk254 : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A7 ovc_region 0 = mk (ivk w) / 2 ^ 254).
    { rewrite <- (vb_scalar_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Halpha : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A7 ovc_region 1 = ivk w).
    { rewrite <- t_ivk_eq.
      reflexivity. }
    assert (Hslo : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A7 ovc_region 2 =
      (ivk w + mk (ivk w) / 2 ^ 254 * 2 ^ 130) mod Primes.pallas_p
        / 2 ^ 130).
    { rewrite <- (vb_s_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    assert (Hs : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A8 ovc_region 1 =
      (ivk w + mk (ivk w) / 2 ^ 254 * 2 ^ 130) mod Primes.pallas_p).
    { rewrite <- (vb_s_e (ivk w) (hi_g_d_old w)), <- t_vb_ivk.
      reflexivity. }
    cbn in Hbody.
    destruct Hbody as [H | [H | [H | [H | [H | []]]]]]; subst body.
    - (* s_check *)
      gate_cbn.
      rewrite Hs, Halpha, Hk254.
      assert (Hc : UnOp.from (2 ^ 124) *F UnOp.from (2 ^ 6) =
          UnOp.from (2 ^ 130))
        by (vm_compute; reflexivity).
      rewrite Hc.
      mod_ring_solve.
    - (* recovery *)
      gate_cbn.
      rewrite Hz0, Halpha.
      unfold Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q, mk.
      mod_ring_solve.
    - (* lo_zero *)
      gate_cbn.
      rewrite Hk254, Hz130.
      destruct (overflow_k254_bit (ivk w) Hival) as [H0 | H1].
      + left.
        rewrite H0.
        exact from_zero.
      + right.
        rewrite (overflow_z130_k1 (ivk w) Hival H1), H1.
        reflexivity.
    - (* s_minus_lo_130_check *)
      gate_cbn.
      rewrite Hk254, Hslo.
      destruct (overflow_k254_bit (ivk w) Hival) as [H0 | H1].
      + left.
        rewrite H0.
        exact from_zero.
      + right.
        rewrite (overflow_s_low_k1 (ivk w) Hival H1).
        exact from_zero.
    - (* canonicity *)
      gate_cbn.
      rewrite Hk254, Hz130, Heta, Hslo.
      destruct (overflow_k254_bit (ivk w) Hival) as [H0 | H1].
      + destruct (Z.eqb_spec (mk (ivk w) / 2 ^ 130) 0) as [Hz | Hz].
        * right.
          rewrite (overflow_s_low_k0 (ivk w) Hival Hz).
          exact from_zero.
        * left; right.
          exact (overflow_eta_eval (ivk w) Hival Hz).
      + left; left.
        rewrite H1.
        reflexivity.
  Qed.

  (** ** Site: the witnessed [pk_d_old] point *)

  Lemma site_wpkd (w : HonestInput) (Hval : valid w)
      (body : Constraint.t columns)
      (Hbody : List.In body (guarded_bodies Selector.QWitnessPointNonId)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (wpkd_region, 0) body.
  Proof.
    rewrite bodies_witness_non_id in Hbody.
    destruct Hval as (Hty & _ & _ & Hpk).
    assert (Hpkok : point_ok (hi_pk_d_old w)).
    { unfold well_typed in Hty.
      destruct Hty as
        (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpko & _).
      exact Hpko. }
    assert (Hx : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A0 wpkd_region 0 = Point.x (hi_pk_d_old w)).
    { transitivity (Point.x (OCT.t_vb_result (OCT.tables_of w)));
        [reflexivity |].
      rewrite t_vb_result_ivk.
      rewrite <- Hpk.
      reflexivity. }
    assert (Hy : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A1 wpkd_region 0 = Point.y (hi_pk_d_old w)).
    { transitivity (Point.y (OCT.t_vb_result (OCT.tables_of w)));
        [reflexivity |].
      rewrite t_vb_result_ivk.
      rewrite <- Hpk.
      reflexivity. }
    pose proof (point_ok_affine _ Hpkok) as (Haff & _ & _).
    assert (Hcurve :
        Point.y (hi_pk_d_old w) *F Point.y (hi_pk_d_old w) -F
          (Point.x (hi_pk_d_old w) *F Point.x (hi_pk_d_old w) *F
           Point.x (hi_pk_d_old w)) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0).
    { destruct Hpkok as (_ & Hoc & _).
      rewrite Haff in Hoc.
      exact (PallasModel.on_curve_affine_poly _ _ Hoc). }
    cbn in Hbody.
    destruct Hbody as [H | []]; subst body.
    gate_cbn.
    rewrite Hx, Hy.
    autorewrite with field_rewrite.
    exact Hcurve.
  Qed.

  (** ** Site: the range-check lookup rows of the overflow block *)

  Lemma site_ovl_lookup (w : HonestInput) (r : Z)
      (H0 : 0 <= r) (H12 : r <= 12) :
    eval_lookup_argument (OrchardHonestAssignment.honest_assignment w)
      (ovl_region, r) 1024 range_arg.
  Proof.
    destruct (ovl_memb r H0 H12) as (Hql & Hqr).
    assert (Hc : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A9 ovl_region r =
      OrchardVarBaseTables.vb_s (OCT.t_vb (OCT.tables_of w))
        / 2 ^ (10 * r)).
    { transitivity (OrchardVarBaseTables.overflow_lookup_advice_of
        (OCT.t_vb (OCT.tables_of w)) A9 r); [reflexivity |].
      unfold OrchardVarBaseTables.overflow_lookup_advice_of.
      replace ((0 <=? r) && (r <=? 13))%bool with true
        by (symmetry; apply Bool.andb_true_iff;
            split; apply Z.leb_le; lia).
      reflexivity. }
    assert (Hn : (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) A9 ovl_region (r + 1) =
      OrchardVarBaseTables.vb_s (OCT.t_vb (OCT.tables_of w))
        / 2 ^ (10 * r) / 1024).
    { transitivity (OrchardVarBaseTables.overflow_lookup_advice_of
        (OCT.t_vb (OCT.tables_of w)) A9 (r + 1)); [reflexivity |].
      unfold OrchardVarBaseTables.overflow_lookup_advice_of.
      replace ((0 <=? r + 1) && (r + 1 <=? 13))%bool with true
        by (symmetry; apply Bool.andb_true_iff;
            split; apply Z.leb_le; lia).
      rewrite Z.div_div
        by (try apply Z.pow_pos_nonneg; clear; lia).
      rewrite <- Z.pow_add_r by (clear -H0; lia).
      replace (10 * r + 10) with (10 * (r + 1)) by ring.
      reflexivity. }
    set (zc := OrchardVarBaseTables.vb_s (OCT.t_vb (OCT.tables_of w))
      / 2 ^ (10 * r)) in *.
    pose proof (Z.mod_pos_bound zc 1024 ltac:(lia)) as Hw.
    cbn [eval_lookup_argument range_arg LookupArgument.pairs].
    exists (zc mod 1024).
    split; [clear -Hw; lia |].
    constructor; [| constructor].
    cbn [eval_expression eval_selector].
    rewrite hsel_eq.
    cbn beta.
    rewrite Hql, Hqr.
    cbn iota.
    rewrite hlookup_eq.
    cbn beta.
    rewrite table_value_id by (clear -Hw; lia).
    rewrite rot_cur, rot_next.
    rewrite Hc, Hn.
    pose proof pallas_p_pos as Hp.
    unfold BinOp.mul, BinOp.add, BinOp.sub, UnOp.from.
    transitivity ((zc mod 1024) mod Primes.pallas_p);
      [| apply Z.mod_small; clear -Hw Hp; lia].
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end.
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p).
    unfold Zdiv.eqm.
    rewrite (Z.mod_eq zc 1024) by (clear; lia).
    f_equal.
    ring.
  Qed.
End OrchardVarBaseForward.
