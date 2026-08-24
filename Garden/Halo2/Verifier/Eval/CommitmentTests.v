(** * Executable checks for the primitive commitment backend

    The small cases exercise arbitrary variable-base terms, reference parity,
    generator-length rejection, and the same-x panic retained by the
    Rust-shaped MSM builder.  The final case runs the fixed 2,048-generator
    primitive-array path with one scalar for every SRS point. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.VestaOrder.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Eval.Commitment.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.
Local Open Scope Z_scope.

Module CommitmentEvalTests.
  Module E := CommitmentEval.
  Module R := CommitmentVerifier.
  Module J := VkJacobian.

  Definition generator : Vesta.point := Vesta.affine (-1) 2.

  Lemma generator_good : VkMsm.good generator.
  Proof.
    split.
    - exact VestaOrder.gen_reduced.
    - exact VestaOrder.gen_on_curve.
  Qed.

  Definition small_terms : list E.term :=
    [(3, generator); (5, generator); (-8, generator);
      (19, Vesta.identity)].

  Lemma small_terms_good : List.Forall E.term_good small_terms.
  Proof.
    repeat constructor; exact generator_good || exact VkMsm.good_identity.
  Qed.

  Example small_terms_cancel :
    J.is_identity (E.eval_terms small_terms) = true.
  Proof. vm_compute. reflexivity. Qed.

  Definition small_parameters : R.parameters := {|
    R.parameter_g := [];
    R.parameter_w := generator;
    R.parameter_u := generator;
  |}.

  Definition small_state : R.msm := {|
    R.params_n := 0;
    R.g_scalars := None;
    R.w_scalar := Some 11;
    R.u_scalar := Some (-11);
    R.other := [];
  |}.

  Example small_eval_matches_reference :
    E.eval small_parameters small_state = R.eval small_parameters small_state.
  Proof.
    apply E.eval_refines.
    repeat constructor; exact generator_good.
  Qed.

  Example small_eval_snapshot :
    E.eval small_parameters small_state = Some true /\
    R.eval small_parameters small_state = Some true.
  Proof. vm_compute. split; reflexivity. Qed.

  Definition mismatched_parameters : R.parameters := {|
    R.parameter_g := [generator];
    R.parameter_w := generator;
    R.parameter_u := generator;
  |}.

  Definition mismatched_state : R.msm := {|
    R.params_n := 1;
    R.g_scalars := Some [1; 2];
    R.w_scalar := None;
    R.u_scalar := None;
    R.other := [];
  |}.

  Example generator_length_mismatch :
    E.eval mismatched_parameters mismatched_state = None /\
    R.eval mismatched_parameters mismatched_state = None.
  Proof. vm_compute. split; reflexivity. Qed.

  Definition same_x_state : R.msm :=
    match R.append_coordinates 1 0 1 (R.empty 0) with
    | R.MsmOk state => state
    | R.MsmPanicked _ => R.empty 0
    end.

  Example inconsistent_same_x_panics_before_evaluation :
    R.append_coordinates 1 0 2 same_x_state =
      R.MsmPanicked (R.InconsistentSameXPoint 0 1 2).
  Proof. vm_compute. reflexivity. Qed.

  Definition empty_srs_state : R.msm := R.empty 2048.

  Example empty_srs_eval_matches_reference :
    E.eval_srs empty_srs_state =
      R.eval small_parameters empty_srs_state.
  Proof. vm_compute. reflexivity. Qed.

  Definition full_srs_scalars : list VerifierField.t :=
    VerifierField.repeat_scalar VerifierField.one 2048.

  Definition full_srs_state : R.msm := {|
    R.params_n := 2048;
    R.g_scalars := Some full_srs_scalars;
    R.w_scalar := None;
    R.u_scalar := None;
    R.other := [];
  |}.

  Example full_srs_scalar_length :
    List.length full_srs_scalars = 2048%nat.
  Proof. vm_compute. reflexivity. Qed.

  Example full_srs_dispatches_to_primitive_kernel :
    E.eval_srs full_srs_state =
      Some (J.is_identity
        (J.add (E.eval_terms (E.srs_fixed_terms full_srs_state))
          (E.eval_srs_g full_srs_scalars))).
  Proof.
    unfold E.eval_srs.
    cbv beta iota zeta delta [full_srs_state R.g_scalars].
    rewrite full_srs_scalar_length.
    reflexivity.
  Qed.

  Example full_srs_path_non_identity :
    E.eval_srs full_srs_state = Some false.
  Proof. Time vm_compute. reflexivity. Qed.

End CommitmentEvalTests.
