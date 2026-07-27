(** * Forward lemmas: the slice-bound residue of the witness facts

    The subgroup of the open non-self-copy witness facts whose two cell
    addresses hold the *same* value reached through two different readers, so
    that the residual obligation is pure [Z] div/mod arithmetic:

    - index [0] of a running sum ([v = v / 2^(10·0)], [v = v / 8^0]): the
      canonicity-gate heads against their lookup columns' row 0, the
      magnitude against the [value_commit_v] short leg's first running sum,
      and the nullifier scalar against the base-field leg's first running
      sum;
    - the tail of a running sum is zero ([v / 8^22 = 0] for a 64-bit
      magnitude, [v / 8^85 = 0] for a field-reduced nullifier scalar,
      [ (y mod 2^250) / 2^250 = 0 ] for the y-canonicity [j] lookups);
    - a packed-message bit is a point's y-parity: bit 255 of the §5.4.8.4
      note message is [ỹ(g_d)] and bit 511 is [ỹ(pk_d)], which needs only
      [0 ≤ x(g_d), x(pk_d) < 2^255] from the typing envelope.

    Every fact literal is copied verbatim from the residue list of
    [forward/lookups_witness.v]; the coverage scan there is over a structural
    [fact_beq], so the residue may be regrouped freely. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Field.Pow2.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardWitnessSliceBounds.
  Import OrchardWitnessInput.
  Import OrchardNoteCommitCells.

  Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** ** Power-of-two slice arithmetic *)

  Lemma mod_mod_low (x a b : Z) : 0 <= a <= b ->
    (x mod 2 ^ b) mod 2 ^ a = x mod 2 ^ a.
  Proof.
    intros [Ha Hab].
    apply Z.mod_mod_divide.
    exists (2 ^ (b - a)).
    rewrite <- pow2_split by lia.
    f_equal; lia.
  Qed.

  Lemma mod_mod_two (x b : Z) : 1 <= b -> (x mod 2 ^ b) mod 2 = x mod 2.
  Proof.
    intros Hb.
    pose proof (mod_mod_low x 1 b ltac:(lia)) as H.
    change (2 ^ 1) with 2 in H.
    exact H.
  Qed.

  Lemma div_of_mod (x a b : Z) : 0 <= a <= b ->
    (x mod 2 ^ b) / 2 ^ a = x / 2 ^ a mod 2 ^ (b - a).
  Proof.
    intros [Ha Hab].
    pose proof (pow2_pos a Ha).
    pose proof (pow2_pos (b - a) ltac:(lia)).
    pose proof (pow2_pos b ltac:(lia)).
    rewrite (Z.mod_eq x (2 ^ b)) by lia.
    replace (x - 2 ^ b * (x / 2 ^ b))
      with (x + - (x / 2 ^ b) * 2 ^ (b - a) * 2 ^ a)
      by (rewrite <- Z.mul_assoc, <- pow2_split by lia;
          replace (b - a + a) with b by lia; ring).
    rewrite Z.div_add by lia.
    rewrite (Z.mod_eq (x / 2 ^ a) (2 ^ (b - a))) by lia.
    rewrite div_div_pow by lia.
    replace (a + (b - a)) with b by lia.
    ring.
  Qed.

  Lemma view_shift (LOW M b : Z) : 0 <= b -> 0 <= LOW < 2 ^ b ->
    (LOW + M * 2 ^ b) / 2 ^ b = M.
  Proof.
    intros Hb HL.
    pose proof (pow2_pos b Hb).
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    apply Z.add_0_l.
  Qed.

  (** ** Pallas modulus facts *)

  Lemma pallas_p_lt : Primes.pallas_p < 2 ^ 255.
  Proof. unfold Primes.pallas_p, Primes.t_p; lia. Qed.

  (** ** The typed points' coordinate ranges *)

  Lemma point_ok_coords (P : Point.t) :
    point_ok P ->
    0 <= Point.x P < Primes.pallas_p /\ 0 <= Point.y P < Primes.pallas_p.
  Proof.
    pose proof Primes.pallas_p_pos as Hp.
    intros (Hred & _ & Hid).
    unfold Pallas.reduced, Weierstrass.reduced, PallasModel.unrepr in Hred.
    destruct ((Point.x P =? 0) && (Point.y P =? 0))%bool eqn:Hz.
    - exfalso.
      apply Bool.andb_true_iff in Hz.
      destruct Hz as [Hx Hy].
      apply Z.eqb_eq in Hx.
      apply Z.eqb_eq in Hy.
      apply Hid.
      destruct P as [x y].
      cbn in Hx, Hy.
      subst.
      reflexivity.
    - destruct Hred as [Hx Hy].
      unfold UnOp.from in Hx, Hy.
      split; [rewrite <- Hx | rewrite <- Hy]; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma pt_x_255 (P : Point.t) (H : point_ok P) :
    0 <= EccSpec.extract_x P < 2 ^ 255.
  Proof.
    destruct (point_ok_coords P H) as [Hx _].
    pose proof pallas_p_lt.
    unfold EccSpec.extract_x.
    lia.
  Qed.

  Lemma wt_points (w : HonestInput) (Hv : valid w) :
    point_ok (hi_g_d_old w) /\ point_ok (hi_pk_d_old w) /\
    point_ok (hi_g_d_new w) /\ point_ok (hi_pk_d_new w).
  Proof.
    destruct Hv as (Hwt & _).
    unfold well_typed in Hwt.
    destruct Hwt as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hgo & Hpo & Hgn & Hpn & _).
    split; [exact Hgo |]. split; [exact Hpo |].
    split; [exact Hgn |]. exact Hpn.
  Qed.

  Lemma wt_values (w : HonestInput) (Hv : valid w) :
    0 <= hi_v_old w < 2 ^ 64 /\ 0 <= hi_v_new w < 2 ^ 64.
  Proof.
    destruct Hv as (Hwt & _).
    unfold well_typed in Hwt.
    destruct Hwt as (Hvo & Hvn & _).
    split; [exact Hvo | exact Hvn].
  Qed.

  (** ** Views of the packed §5.4.8.4 note message

      The packed message regrouped at the two compressed-point boundaries;
      the sign bits of [g_d] and [pk_d] sit at bit 255 and bit 511. *)

  Lemma nc_view_0 (gd pkd : Point.t) (v rho psi : Z) :
    nc_packed gd pkd v rho psi =
    EccSpec.extract_x gd +
    (Point.y gd mod 2 + EccSpec.extract_x pkd * 2 +
     Point.y pkd mod 2 * 2 ^ 256 + v * 2 ^ 257 + rho * 2 ^ 321 +
     psi * 2 ^ 576) * 2 ^ 255.
  Proof. unfold nc_packed. ring. Qed.

  Lemma nc_view_256 (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255) :
    nc_packed gd pkd v rho psi / 2 ^ 256 =
    EccSpec.extract_x pkd +
    (Point.y pkd mod 2 + v * 2 + rho * 2 ^ 65 + psi * 2 ^ 320) * 2 ^ 255.
  Proof.
    replace (nc_packed gd pkd v rho psi)
      with ((EccSpec.extract_x gd + Point.y gd mod 2 * 2 ^ 255) +
            (EccSpec.extract_x pkd +
             (Point.y pkd mod 2 + v * 2 + rho * 2 ^ 65 + psi * 2 ^ 320) *
             2 ^ 255) * 2 ^ 256)
      by (unfold nc_packed; ring).
    apply view_shift; [lia |].
    pose proof (Z.mod_pos_bound (Point.y gd) 2 ltac:(lia)).
    lia.
  Qed.

  (** The two sign bits of the packed message. *)

  Lemma nc_b2_eq (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255) :
    nc_b2 (nc_packed gd pkd v rho psi) = Point.y gd mod 2.
  Proof.
    unfold nc_b2, nc_b.
    rewrite div_of_mod by lia.
    rewrite mod_mod_two by lia.
    rewrite div_div_pow by lia.
    replace (250 + 5) with 255 by lia.
    rewrite nc_view_0.
    rewrite (view_shift (EccSpec.extract_x gd) _ 255 ltac:(lia) Hxg).
    replace (Point.y gd mod 2 + EccSpec.extract_x pkd * 2 +
             Point.y pkd mod 2 * 2 ^ 256 + v * 2 ^ 257 + rho * 2 ^ 321 +
             psi * 2 ^ 576)
      with (Point.y gd mod 2 +
            (EccSpec.extract_x pkd + Point.y pkd mod 2 * 2 ^ 255 +
             v * 2 ^ 256 + rho * 2 ^ 320 + psi * 2 ^ 575) * 2)
      by ring.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_mod by lia.
    reflexivity.
  Qed.

  Lemma nc_d1_eq (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255)
      (Hxp : 0 <= EccSpec.extract_x pkd < 2 ^ 255) :
    nc_d1 (nc_packed gd pkd v rho psi) = Point.y pkd mod 2.
  Proof.
    unfold nc_d1, nc_d.
    assert (Htwo : forall z : Z, z / 2 = z / 2 ^ 1) by (intros z; reflexivity).
    rewrite Htwo.
    rewrite div_of_mod by lia.
    rewrite mod_mod_two by lia.
    rewrite div_div_pow by lia.
    replace (510 + 1) with 511 by lia.
    transitivity (nc_packed gd pkd v rho psi / 2 ^ 256 / 2 ^ 255 mod 2).
    { rewrite div_div_pow by lia.
      replace (256 + 255) with 511 by lia.
      reflexivity. }
    rewrite (nc_view_256 gd pkd v rho psi Hxg).
    rewrite (view_shift (EccSpec.extract_x pkd) _ 255 ltac:(lia) Hxp).
    replace (Point.y pkd mod 2 + v * 2 + rho * 2 ^ 65 + psi * 2 ^ 320)
      with (Point.y pkd mod 2 + (v + rho * 2 ^ 64 + psi * 2 ^ 319) * 2)
      by ring.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_mod by lia.
    reflexivity.
  Qed.

  (** ** Index-0 and tail identities of the running-sum columns *)

  Lemma div_pow2_0 (x : Z) : x / 2 ^ (10 * 0) = x.
  Proof. change (2 ^ (10 * 0)) with 1. apply Z.div_1_r. Qed.

  Lemma div_pow8_0 (x : Z) : x / 8 ^ 0 = x.
  Proof. change (8 ^ 0) with 1. apply Z.div_1_r. Qed.

  Lemma running_sum_at_0 (k : Z) : running_sum_at k (Z.to_nat 0) = k.
  Proof.
    unfold running_sum_at.
    change (8 ^ Z.of_nat (Z.to_nat 0)) with 1.
    apply Z.div_1_r.
  Qed.

  Lemma running_sum_at_85 (k : Z) (Hk : 0 <= k < Primes.pallas_p) :
    running_sum_at k (Z.to_nat 85) = 0.
  Proof.
    unfold running_sum_at.
    assert (Hpow : 8 ^ Z.of_nat (Z.to_nat 85) = 2 ^ 255) by reflexivity.
    rewrite Hpow.
    apply Z.div_small.
    pose proof pallas_p_lt.
    lia.
  Qed.

  Lemma ycanon_j_tail (y : Z) : ycanon_j y / 2 ^ (10 * 25) = 0.
  Proof.
    unfold ycanon_j.
    change (2 ^ (10 * 25)) with (2 ^ 250).
    apply Z.div_small.
    apply Z.mod_pos_bound.
    apply pow2_pos; lia.
  Qed.

  Lemma mag_tail (w : HonestInput) (Hv : valid w) : magnitude w / 8 ^ 22 = 0.
  Proof.
    destruct (wt_values w Hv) as [Hvo Hvn].
    apply Z.div_small.
    unfold magnitude.
    assert (H8 : 8 ^ 22 = 73786976294838206464) by reflexivity.
    assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite H8.
    rewrite H64 in Hvo, Hvn.
    split; [apply Z.abs_nonneg |].
    destruct (Z.le_ge_cases (hi_v_new w) (hi_v_old w)) as [Hc | Hc].
    - rewrite Z.abs_eq by lia. lia.
    - rewrite Z.abs_neq by lia. lia.
  Qed.

  (** ** The nullifier scalar is a field element

      Its hoisted spelling is the field sum of the Poseidon output and
      [ψ_old], so it is reduced by construction.  This is the only place the
      hoisted record is unfolded; the [cbn] whitelist keeps the Poseidon
      round chain and every other derivation stuck. *)

  Lemma nscalar_shape (w : HonestInput) :
    OrchardCompletenessTables.t_nullifier_scalar
      (OrchardCompletenessTables.tables_of w) =
    OrchardCompletenessTables.t_hash2
      (OrchardCompletenessTables.tables_of w) +F hi_psi_old w.
  Proof.
    cbn [OrchardCompletenessTables.tables_of
         OrchardCompletenessTables.t_nullifier_scalar
         OrchardCompletenessTables.t_hash2].
    reflexivity.
  Qed.

  Lemma nscalar_range (w : HonestInput) :
    0 <= OrchardCompletenessTables.t_nullifier_scalar
           (OrchardCompletenessTables.tables_of w) < Primes.pallas_p.
  Proof.
    rewrite nscalar_shape.
    unfold BinOp.add.
    apply Z.mod_pos_bound.
    exact Primes.pallas_p_pos.
  Qed.

  (** The hoisted derivation record stays a stuck atom from here on: no
      reduction below reaches a spec fold (docs/compile-performance.md). *)
  #[local] Strategy opaque
    [OrchardCompletenessTables.tables_of
     BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** ** The fact list and its discharge *)

  (** The head of a witness-fact goal: the two cell addresses, with the
      advice dispatch reduced to the reader leaves.  Both sides are advice
      dispatches at concrete addresses, so the whitelist [cbn] stops at the
      hoisted projections and the [tables_nc] slice functions. *)
  Ltac cellred :=
    cbn [interpret_fact eval_cell
         Cell.column Cell.region Cell.row_offset
         Assignment.advice
         OrchardHonestAssignment.honest_assignment
         OrchardCompletenessTables.advice_t
         OrchardCompletenessTables.advice_ecc_t
         OrchardCompletenessTables.advice_nullifier_t
         OrchardCompletenessTables.fb_short_advice_t
         OrchardAdviceEccMuls.is_A9
         OrchardNoteCommitCells.nc_advice
         OrchardNoteCommitCells.civk_advice
         OrchardNoteCommitCells.ycanon_advice
         OrchardNoteCommitCells.running_lookup_advice
         Z.leb Z.ltb Z.eqb Z.compare Pos.compare Pos.compare_cont Pos.eqb
         andb negb].

  (** The canonicity-gate head equals its lookup column's row 0. *)
  Ltac idx0 := cellred; symmetry; apply div_pow2_0.

  (** The y-canonicity [j] lookup runs out after 25 rows. *)
  Ltac jtail := cellred; apply ycanon_j_tail.

  Definition orchardwitnessslicebounds_facts
      : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 22 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Nullifier RegionId.Nullifier.ScalarAdd; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 85 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Nullifier RegionId.Nullifier.AlphaLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.AkLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.NkLookup; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 25 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 25 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.XGDLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.XPKDLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RhoLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.PsiLookup; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 25 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 25 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.XGDLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.XPKDLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RhoLookup; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.PsiLookup; Cell.row_offset := 0 |}].

  Lemma orchardwitnessslicebounds_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w)
    : interpret_facts (OrchardHonestAssignment.honest_assignment w)
        orchardwitnessslicebounds_facts.
  Proof.
    destruct (wt_points w Hv) as (Hgo & Hpo & Hgn & Hpn).
    pose proof (pt_x_255 _ Hgo) as Xgo.
    pose proof (pt_x_255 _ Hpo) as Xpo.
    pose proof (pt_x_255 _ Hgn) as Xgn.
    pose proof (pt_x_255 _ Hpn) as Xpn.
    unfold orchardwitnessslicebounds_facts.
    cbn [interpret_facts].
    repeat apply conj.
    (* 0: magnitude vs the value_commit_v short leg's running sum *)
    - cellred. apply div_pow8_0.
    (* 1: the short leg's running sum runs out after 22 rows *)
    - cellred. exact (mag_tail w Hv).
    (* 5: the nullifier scalar vs the base-field leg's running sum *)
    - cellred. apply running_sum_at_0.
    (* 6: the base-field leg's running sum runs out after 85 rows *)
    - cellred. apply running_sum_at_85. apply nscalar_range.
    (* 9 *)
    - cellred. symmetry. apply running_sum_at_0.
    (* 10 *)
    - idx0.
    (* 21, 23 *)
    - idx0.
    - idx0.
    (* 30 *)
    - jtail.
    (* 31, 32 *)
    - idx0.
    - idx0.
    (* 33 *)
    - jtail.
    (* 35, 36 *)
    - idx0.
    - idx0.
    (* 47: bit 255 of the old note's packed message is ỹ(g_d_old) *)
    - cellred. unfold ycanon_lsb. apply nc_b2_eq. exact Xgo.
    (* 48: bit 511 is ỹ(pk_d_old) *)
    - cellred. unfold ycanon_lsb. apply nc_d1_eq; assumption.
    (* 51, 54, 57, 60 *)
    - idx0.
    - idx0.
    - idx0.
    - idx0.
    (* 64 *)
    - jtail.
    (* 65, 66 *)
    - idx0.
    - idx0.
    (* 67 *)
    - jtail.
    (* 68, 69 *)
    - idx0.
    - idx0.
    (* 80: bit 255 of the new note's packed message is ỹ(g_d_new) *)
    - cellred. unfold ycanon_lsb. apply nc_b2_eq. exact Xgn.
    (* 81: bit 511 is ỹ(pk_d_new) *)
    - cellred. unfold ycanon_lsb. apply nc_d1_eq; assumption.
    (* 84, 86, 90, 93 *)
    - idx0.
    - idx0.
    - idx0.
    - idx0.
    - exact I.
  Qed.

End OrchardWitnessSliceBounds.
