(** * Lightweight checked entry point for the final Orchard verifier MSM

    This module contains only the executable check on proof-supplied MSM
    points and its generic soundness argument.  In particular, it deliberately
    does not import the generated SRS provenance certificate: executable
    verifier clients should not retain that large proof graph merely to call
    [eval_srs_checked].  The concrete certificate is instantiated separately
    in [Garden.Orchard.Verifier.Assurance]. *)

From Stdlib Require Import ZArith Lists.List Bool.Bool Lia.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Eval.Commitment.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardVerifierChecked.
  Module Reference := CommitmentVerifier.

  (** Boolean counterpart of [Vesta.reduced].  Keeping the range test
      separate from curve membership makes the integer representation
      requirement explicit: both affine coordinates must already lie in
      [[0, pallas_q)], rather than merely denoting residues modulo the base
      field. *)
  Definition point_reducedb (point : Vesta.point) : bool :=
    match point with
    | Weierstrass.Infinity => true
    | Weierstrass.Affine x y =>
        ((0 <=? x) && (x <? Primes.pallas_q)) &&
        ((0 <=? y) && (y <? Primes.pallas_q))
    end.

  Definition point_goodb (point : Vesta.point) : bool :=
    point_reducedb point && Vesta.on_curveb point.

  Definition term_goodb (value : CommitmentEval.term) : bool :=
    point_goodb (snd value).

  (** This is the executable premise required by
      [CommitmentEval.eval_srs_refines_reference_srs]. *)
  Definition final_terms_well_formedb (state : Reference.msm) : bool :=
    List.forallb term_goodb (CommitmentEval.srs_fixed_terms state).

  Lemma point_reducedb_sound (point : Vesta.point) :
    point_reducedb point = true -> Vesta.reduced point.
  Proof.
    destruct point as [|x y].
    - exact (fun _ => I).
    - cbn [point_reducedb Vesta.reduced Weierstrass.reduced].
      intros Hrange.
      apply Bool.andb_true_iff in Hrange as [Hx Hy].
      apply Bool.andb_true_iff in Hx as [Hx_nonnegative Hx_bounded].
      apply Bool.andb_true_iff in Hy as [Hy_nonnegative Hy_bounded].
      apply Z.leb_le in Hx_nonnegative.
      apply Z.ltb_lt in Hx_bounded.
      apply Z.leb_le in Hy_nonnegative.
      apply Z.ltb_lt in Hy_bounded.
      unfold UnOp.from.
      split.
      + apply Z.mod_small. split; assumption.
      + apply Z.mod_small. split; assumption.
  Qed.

  Lemma point_goodb_sound (point : Vesta.point) :
    point_goodb point = true -> VkMsm.good point.
  Proof.
    unfold point_goodb, VkMsm.good.
    intros Hgood.
    apply Bool.andb_true_iff in Hgood as [Hreduced Hon_curve].
    split.
    - now apply point_reducedb_sound.
    - now apply Vesta.on_curveb_sound.
  Qed.

  Lemma term_goodb_sound (value : CommitmentEval.term) :
    term_goodb value = true -> CommitmentEval.term_good value.
  Proof.
    unfold term_goodb, CommitmentEval.term_good.
    apply point_goodb_sound.
  Qed.

  Theorem final_terms_well_formedb_sound (state : Reference.msm) :
    final_terms_well_formedb state = true ->
    CommitmentEval.srs_well_formed state.
  Proof.
    unfold final_terms_well_formedb, CommitmentEval.srs_well_formed.
    intros Hchecked.
    rewrite List.forallb_forall in Hchecked.
    apply List.Forall_forall.
    intros value Hvalue.
    apply term_goodb_sound.
    now apply Hchecked.
  Qed.

  Corollary eval_srs_refines_reference_srs
      (srs_refinement : VkSrsDataView.refinement)
      (state : Reference.msm) :
    final_terms_well_formedb state = true ->
    CommitmentEval.eval_srs state =
      Reference.eval CommitmentEval.reference_srs_parameters state.
  Proof.
    intros Hchecked.
    apply CommitmentEval.eval_srs_refines_reference_srs.
    - exact srs_refinement.
    - now apply final_terms_well_formedb_sound.
  Qed.

  (** Checked executable entry point.  A malformed dynamic point is rejected
      before entering the primitive-word evaluator. *)
  Definition eval_srs_checked (state : Reference.msm) : option bool :=
    if final_terms_well_formedb state
    then CommitmentEval.eval_srs state
    else None.

  Definition eval_reference_checked (state : Reference.msm) : option bool :=
    if final_terms_well_formedb state
    then Reference.eval CommitmentEval.reference_srs_parameters state
    else None.

  Theorem eval_srs_checked_refines
      (srs_refinement : VkSrsDataView.refinement)
      (state : Reference.msm) :
    eval_srs_checked state = eval_reference_checked state.
  Proof.
    unfold eval_srs_checked, eval_reference_checked.
    destruct (final_terms_well_formedb state) eqn:Hchecked.
    - now apply (eval_srs_refines_reference_srs srs_refinement).
    - reflexivity.
  Qed.
End OrchardVerifierChecked.
