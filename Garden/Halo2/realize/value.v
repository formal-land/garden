(** * Operational soundness, conjunct 1: value agreement.

    The value a synthesis program computes is independent of any grid: the
    relational [layouter_value] and the value component of the operational
    [V1.eval_layouter] thread results through [Bind] / [AddRegion] /
    [InNamespace] identically.  This file proves that agreement, the first
    conjunct of [operational_sound].  It is self-contained — no side
    conditions and no reference to the replayed grid. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.

Import ListNotations.
Global Open Scope Z_scope.

(** The region-level value agreement: [region_value] equals the value
    component of [V1.eval_region].  Both ignore [indices] / [region_start]
    and the grid, threading only the values through [Bind]. *)
Lemma eval_region_value {columns : Columns.t} {RegionId : Set} {A : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
    (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A) :
  region_value program = fst (V1.eval_region idx rs region program).
Proof.
  revert A program.
  fix IH 2.
  intros A program.
  destruct program as
    [A value | A B first second | selector offset annotation
    | annotation column offset value | left right | cell value];
    cbn [region_value V1.eval_region].
  - reflexivity.
  - rewrite (IH _ first).
    destruct (V1.eval_region idx rs region first) as [value events_first].
    cbn [fst].
    rewrite (IH _ (second value)).
    destruct (V1.eval_region idx rs region (second value))
      as [value_second events_second].
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Conjunct 1 of [operational_sound]: [layouter_value] equals the value
    component of [V1.eval_layouter].  By induction on the program; the
    [AddRegion] case delegates to [eval_region_value]. *)
Lemma operational_sound_value {columns : Columns.t} {RegionId : Set} {A : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z)
    (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A) :
  layouter_value program = fst (V1.eval_layouter idx rs program).
Proof.
  revert A program.
  fix IH 2.
  intros A program.
  destruct program as
    [A value | A B first second | A region name region_program
    | cell instance row | name entries | A name nested];
    cbn [layouter_value V1.eval_layouter].
  - reflexivity.
  - rewrite (IH _ first).
    destruct (V1.eval_layouter idx rs first) as [value events_first].
    cbn [fst].
    rewrite (IH _ (second value)).
    destruct (V1.eval_layouter idx rs (second value))
      as [value_second events_second].
    reflexivity.
  - rewrite (eval_region_value idx rs region (region_program region)).
    destruct (V1.eval_region idx rs region (region_program region))
      as [value events].
    reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH _ nested).
    destruct (V1.eval_layouter idx rs nested) as [value events].
    reflexivity.
Qed.
