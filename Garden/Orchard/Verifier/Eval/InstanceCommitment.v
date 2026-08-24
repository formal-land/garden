(** * Primitive evaluation of Orchard instance commitments

    The public verifier keeps [reference_commitment] in the same list-shaped
    form as Halo2's Rust implementation: pad the instance column, run the
    inverse transform, and commit the resulting coefficients with the fixed
    SRS.  That definition is useful for auditing but much too slow under
    extraction because both operations use their mathematical list models.

    [evaluate_checked] uses the already-refined primitive-array inverse FFT
    and fixed-SRS Jacobian Pippenger kernels.  It takes the optimized branch
    only after checking the two hypotheses needed to identify the loaded
    evaluation vector with the reference vector: it has exactly 2^11 entries,
    and every entry is a canonical Pallas scalar.  Otherwise it returns
    [None], allowing callers to retain their reference fallback unchanged.

    The refinement theorem is parameterized by the existing domain and SRS
    certificates.  Those propositions erase during extraction and are
    instantiated outside the executable dependency closure. *)

From Corelib Require Import PrimArray.
From Stdlib Require Import ZArith Lists.List Bool.Bool Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Domain.
Require Import Garden.Orchard.vk.provenance.DomainRefinement.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.JacobianRefinement.
Require Import Garden.Orchard.vk.provenance.MsmChecks.
Require Import Garden.Orchard.vk.provenance.MsmRefinement.
Require Import Garden.Orchard.vk.provenance.SrsDataView.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.

Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module OrchardInstanceCommitmentEval.

  Definition vector_size : nat := VkIFFT.size_nat.

  Definition scalar_canonicalb (value : Z) : bool :=
    (0 <=? value) && (value <? Primes.pallas_p).

  Definition preconditionsb (values : list Z) : bool :=
    Nat.eqb (List.length values) vector_size
      && List.forallb scalar_canonicalb values.

  Definition evaluation_at (values : list Z) (index : nat) : Z :=
    List.nth index values 0.

  Definition transformed (values : list Z) : VkIFFT.field_array :=
    VkIFFT.inverse_fft VkDomain.bit_reversed_array
      VkDomain.inverse_roots_array VkDomainData.n_inverse
      (VkIFFT.load_evaluations (evaluation_at values)).

  (** Decode the Montgomery FFT output once.  The Pippenger kernel consumes
      standard scalar words so it can extract all 32 width-eight windows
      without another field conversion. *)
  Definition coefficients (values : list Z) :
      list Prim63Words.words5 :=
    let transformed_values := transformed values in
    List.map
      (fun index =>
        PallasP.decode
          (PrimArray.get@{VkIFFT.array_u} transformed_values
            (ArrayLinear.index index)))
      (List.seq O vector_size).

  Definition jacobian_commitment (values : list Z) : VkJacobian.point :=
    let coefficient_values := coefficients values in
    VkJacobian.assemble_halves
      (VkMsmChecks.low_msm coefficient_values)
      (VkMsmChecks.high_msm coefficient_values)
      VkSrsDataView.w.

  (** Normalize one projective result.  This pays two extended-Euclid field
      inversions, which is negligible beside the 32-window MSM and keeps the
      conversion definition close to the usual Jacobian-to-affine equation.
      [Vesta.affine] reduces both coordinates before exposing them to the
      transcript. *)
  Definition projective_to_point (point : VkJacobian.point) : Vesta.point :=
    if VkJacobian.is_identity point then Vesta.identity else
    let x := PallasQ.denote point.(VkJacobian.x) in
    let y := PallasQ.denote point.(VkJacobian.y) in
    let z := PallasQ.denote point.(VkJacobian.z) in
    let z2 := BinOp.mul (p := Primes.pallas_q) z z in
    let z3 := BinOp.mul (p := Primes.pallas_q) z2 z in
    Vesta.affine
      (BinOp.div (p := Primes.pallas_q) x z2)
      (BinOp.div (p := Primes.pallas_q) y z3).

  Definition fast_commitment (values : list Z) : Vesta.point :=
    projective_to_point (jacobian_commitment values).

  Definition evaluate_checked (values : list Z) : option Vesta.point :=
    if preconditionsb values then Some (fast_commitment values) else None.

  (** The deliberately Rust-shaped executable specification retained by the
      caller as its fallback. *)
  Definition reference_commitment (values : list Z) : Vesta.point :=
    Vesta.add
      (VkMsm.msm_pippenger (VkMsm.intt values) VkMsm.g_points)
      VkMsm.w_point.

  Lemma preconditionsb_sound (values : list Z) :
    preconditionsb values = true ->
    List.length values = vector_size /\
    List.Forall (fun value => 0 <= value < Primes.pallas_p) values.
  Proof.
    unfold preconditionsb.
    intros Hchecked.
    apply Bool.andb_true_iff in Hchecked as [Hlength Hvalues].
    apply Nat.eqb_eq in Hlength.
    rewrite List.forallb_forall in Hvalues.
    split; [exact Hlength |].
    apply List.Forall_forall.
    intros value Hvalue.
    specialize (Hvalues value Hvalue).
    unfold scalar_canonicalb in Hvalues.
    apply Bool.andb_true_iff in Hvalues as [Hnonnegative Hbounded].
    now apply Z.leb_le in Hnonnegative; apply Z.ltb_lt in Hbounded.
  Qed.

  Lemma evaluation_values_exact (values : list Z) :
    List.length values = vector_size ->
    List.Forall (fun value => 0 <= value < Primes.pallas_p) values ->
    VkDomainRefinement.evaluation_values (evaluation_at values) = values.
  Proof.
    intros Hlength Hvalues.
    unfold VkDomainRefinement.evaluation_values.
    apply List.nth_ext with (d := 0%Z) (d' := 0%Z).
    - rewrite VkDomainRefinement.tabulate_length. symmetry. exact Hlength.
    - intros index Hindex.
      rewrite VkDomainRefinement.tabulate_length in Hindex.
      unfold VkDomainRefinement.tabulate, evaluation_at.
      rewrite List.nth_indep with
        (d' := (List.nth O values 0 mod Primes.pallas_p)%Z)
        by (rewrite List.length_map, List.length_seq; exact Hindex).
      rewrite (List.map_nth
        (fun row => (List.nth row values 0 mod Primes.pallas_p)%Z)
        (List.seq O VkIFFT.size_nat) O index).
      rewrite List.seq_nth by exact Hindex.
      rewrite Nat.add_0_l.
      assert (Hin : List.In (List.nth index values 0) values).
      { apply List.nth_In. now rewrite Hlength. }
      pose proof (proj1 (List.Forall_forall _ _) Hvalues _ Hin)
        as Hrange.
      rewrite Z.mod_small by exact Hrange.
      reflexivity.
  Qed.

  Lemma coefficients_length (values : list Z) :
    List.length (coefficients values) = vector_size.
  Proof.
    unfold coefficients. now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma coefficient_values_exact
      (domain_certificate : VkDomain.certificate) (values : list Z) :
    List.length values = vector_size ->
    List.Forall (fun value => 0 <= value < Primes.pallas_p) values ->
    VkMsmRefinement.scalar_values (coefficients values) = VkMsm.intt values.
  Proof.
    intros Hlength Hvalues.
    pose proof (VkDomainRefinement.load_evaluations_sound
      (evaluation_at values)) as Hloaded.
    rewrite (evaluation_values_exact values Hlength Hvalues) in Hloaded.
    pose proof (VkDomainRefinement.inverse_fft_sound domain_certificate
      _ _ Hloaded) as Htransformed.
    change (VkDomainRefinement.array_denotes (transformed values)
      (VkMsm.intt values)) in Htransformed.
    unfold VkMsmRefinement.scalar_values, coefficients.
    rewrite List.map_map.
    apply List.nth_ext with (d := 0%Z) (d' := 0%Z).
    - rewrite List.length_map, List.length_seq.
      symmetry. apply VkMsm.intt_length. exact Hlength.
    - intros index Hindex.
      rewrite List.length_map, List.length_seq in Hindex.
      rewrite List.nth_indep with
        (d' := Prim63Words.eval5
          (PallasP.decode
            (PrimArray.get@{VkIFFT.array_u} (transformed values)
              (ArrayLinear.index O))))
        by (rewrite List.length_map, List.length_seq; exact Hindex).
      rewrite (List.map_nth
        (fun index =>
          Prim63Words.eval5
            (PallasP.decode
              (PrimArray.get@{VkIFFT.array_u} (transformed values)
                (ArrayLinear.index index))))
        (List.seq O vector_size) O index).
      rewrite List.seq_nth by exact Hindex.
      rewrite Nat.add_0_l.
      rewrite PallasPRefinement.decode_eval5.
      exact (proj2 (VkDomainRefinement.array_denotes_nth
        (transformed values) (VkMsm.intt values) Htransformed
        index Hindex)).
  Qed.

  Lemma coefficient_range (values : list Z) :
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (VkMsm.intt values).
  Proof.
    eapply List.Forall_impl; [|exact (VkMsm.intt_range values)].
    intros scalar Hscalar.
    change (0 <= scalar < Primes.pallas_p) in Hscalar.
    assert (Hmodulus : Primes.pallas_p < 2 ^ 256)
      by (vm_compute; reflexivity).
    lia.
  Qed.

  Lemma is_identity_spec
      (point : VkJacobian.point) (abstract : Vesta.point) :
    VkJacobianRefinement.represents point abstract ->
    VkJacobian.is_identity point =
      match abstract with
      | Weierstrass.Infinity => true
      | Weierstrass.Affine _ _ => false
      end.
  Proof.
    destruct point as [point_x point_y point_z], abstract as [|x y].
    - intros (Hcanonical & _ & _ & Hrepresents).
      destruct Hcanonical as (_ & _ & Hz).
      rewrite (VkJacobianRefinement.is_identity_denote
        {| VkJacobian.x := point_x;
           VkJacobian.y := point_y;
           VkJacobian.z := point_z |} Hz).
      apply Z.eqb_eq.
      apply VkJacobianRefinement.reduced_eqm_eq.
      + apply VkJacobianRefinement.denote_range.
      + split; [lia | exact VkJacobianRefinement.three_lt_q].
      + exact Hrepresents.
    - intros (Hcanonical & _ & _ & Hrepresents).
      destruct Hcanonical as (_ & _ & Hz).
      rewrite (VkJacobianRefinement.is_identity_denote
        {| VkJacobian.x := point_x;
           VkJacobian.y := point_y;
           VkJacobian.z := point_z |} Hz).
      apply Z.eqb_neq.
      intro Hz_zero.
      destruct Hrepresents as (Hz_nonzero & _ & _).
      apply Hz_nonzero.
      rewrite Hz_zero. reflexivity.
  Qed.

  Lemma projective_to_point_exact
      (point : VkJacobian.point) (abstract : Vesta.point) :
    VkJacobianRefinement.represents point abstract ->
    projective_to_point point = abstract.
  Proof.
    intros Hrepresents.
    destruct abstract as [|abstract_x abstract_y].
    - unfold projective_to_point.
      pose proof (is_identity_spec point Vesta.identity Hrepresents)
        as Hidentity.
      rewrite Hidentity. reflexivity.
    - unfold projective_to_point.
      pose proof (is_identity_spec point
        (Weierstrass.Affine abstract_x abstract_y) Hrepresents)
        as Hidentity.
      rewrite Hidentity.
      destruct Hrepresents as
        (Hcanonical & Hreduced & Hon_curve & Hprojective).
      pose proof Hprojective as Habstract_projective.
      apply (VkJacobianRefinement.jrepr_inj
        (VkJacobianRefinement.coordinates point)).
      + apply Vesta.affine_reduced.
      + exact Hreduced.
      + destruct point as [point_x point_y point_z].
        cbn [VkJacobianRefinement.coordinates VkJacobianRefinement.jrepr
          VkJacobian.x VkJacobian.y VkJacobian.z Vesta.affine].
        cbn [VkJacobianRefinement.coordinates VkJacobianRefinement.jrepr
          VkJacobian.x VkJacobian.y VkJacobian.z] in Hprojective.
        destruct Hprojective as [Hz_nonzero _].
        set (x := PallasQ.denote point_x).
        set (y := PallasQ.denote point_y).
        set (z := PallasQ.denote point_z).
        set (z2 := BinOp.mul (p := Primes.pallas_q) z z).
        set (z3 := BinOp.mul (p := Primes.pallas_q) z2 z).
        assert (Hz2_nonzero :
          ~ eqm Primes.pallas_q z2 0).
        { unfold z2. now apply VkJacobianRefinement.nz_mul. }
        assert (Hz3_nonzero :
          ~ eqm Primes.pallas_q z3 0).
        { unfold z3. now apply VkJacobianRefinement.nz_mul. }
        assert (Hz2_mod : z2 mod Primes.pallas_q <> 0).
        { intro Hz2. apply Hz2_nonzero. unfold eqm.
          rewrite Hz2, Z.mod_0_l by exact VkJacobianRefinement.q_pos.
          reflexivity. }
        assert (Hz3_mod : z3 mod Primes.pallas_q <> 0).
        { intro Hz3. apply Hz3_nonzero. unfold eqm.
          rewrite Hz3, Z.mod_0_l by exact VkJacobianRefinement.q_pos.
          reflexivity. }
        split; [exact Hz_nonzero | split].
        * unfold eqm, UnOp.from, BinOp.mul, Vesta.vesta_p.
          repeat rewrite Z.mod_mod by exact VkJacobianRefinement.q_pos.
          pose proof (div_mul (p := Primes.pallas_q) x z2
            VkJacobianRefinement.three_lt_q Hz2_mod) as Hdivision.
          unfold BinOp.mul in Hdivision.
          rewrite Zmult_mod_idemp_l.
          symmetry. exact Hdivision.
        * unfold eqm, UnOp.from, BinOp.mul, Vesta.vesta_p.
          repeat rewrite Z.mod_mod by exact VkJacobianRefinement.q_pos.
          pose proof (div_mul (p := Primes.pallas_q) y z3
            VkJacobianRefinement.three_lt_q Hz3_mod) as Hdivision.
          unfold BinOp.mul in Hdivision.
          rewrite Zmult_mod_idemp_l.
          symmetry. exact Hdivision.
      + exact Habstract_projective.
  Qed.

  Lemma jacobian_commitment_represents
      (domain_certificate : VkDomain.certificate)
      (srs_refinement : VkSrsDataView.refinement)
      (params_well_formed : VkMsm.params_well_formed)
      (values : list Z) :
    List.length values = vector_size ->
    List.Forall (fun value => 0 <= value < Primes.pallas_p) values ->
    VkJacobianRefinement.represents (jacobian_commitment values)
      (VkMsm.commit_lagrange values).
  Proof.
    intros Hlength Hvalues.
    assert (Hlength_2048 : List.length values = 2048%nat)
      by exact Hlength.
    assert (Hnonnegative : List.Forall (fun value => 0 <= value) values).
    { eapply List.Forall_impl; [|exact Hvalues].
      intros value [Hnonnegative _]. exact Hnonnegative. }
    assert (Hcoefficients :
      VkMsmRefinement.scalar_values (coefficients values) =
        VkMsm.intt values).
    { now apply coefficient_values_exact. }
    assert (Hcoefficient_range :
      List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
        (VkMsmRefinement.scalar_values (coefficients values))).
    { rewrite Hcoefficients. apply coefficient_range. }
    unfold jacobian_commitment.
    exact
      (VkMsmRefinement.assemble_halves_commit_lagrange_sound
        (coefficients values) values
        (coefficients_length values) srs_refinement Hcoefficient_range
        params_well_formed Hlength_2048 Hnonnegative Hcoefficients).
  Qed.

  Lemma reference_commitment_spec
      (params_well_formed : VkMsm.params_well_formed)
      (values : list Z) :
    List.length values = 2048%nat ->
    List.Forall (fun value => 0 <= value) values ->
    reference_commitment values = VkMsm.commit_lagrange values.
  Proof.
    intros Hlength Hnonnegative.
    unfold reference_commitment.
    rewrite (VkMsm.pippenger_correct
      (VkMsm.intt values) VkMsm.g_points).
    - symmetry.
      exact (VkMsm.commit_lagrange_intt values params_well_formed
        Hlength Hnonnegative).
    - rewrite VkMsm.intt_length by exact Hlength.
      symmetry. exact VkMsm.g_points_length.
    - exact (VkMsm.g_points_good params_well_formed).
    - eapply List.Forall_impl; [|exact (VkMsm.intt_range values)].
      intros scalar Hscalar.
      change (0 <= scalar < Primes.pallas_p) in Hscalar.
      assert (Hmodulus : Primes.pallas_p < 2 ^ 256)
        by (vm_compute; reflexivity).
      lia.
  Qed.

  Theorem fast_commitment_refines
      (domain_certificate : VkDomain.certificate)
      (srs_refinement : VkSrsDataView.refinement)
      (params_well_formed : VkMsm.params_well_formed)
      (values : list Z) :
    List.length values = vector_size ->
    List.Forall (fun value => 0 <= value < Primes.pallas_p) values ->
    fast_commitment values = reference_commitment values.
  Proof.
    intros Hlength Hvalues.
    assert (Hnonnegative : List.Forall (fun value => 0 <= value) values).
    { eapply List.Forall_impl; [|exact Hvalues].
      intros value [Hnonnegative _]. exact Hnonnegative. }
    unfold fast_commitment.
    rewrite (projective_to_point_exact _ _
      (jacobian_commitment_represents domain_certificate srs_refinement
        params_well_formed values Hlength Hvalues)).
    symmetry.
    exact (reference_commitment_spec params_well_formed values
      Hlength Hnonnegative).
  Qed.

  Theorem evaluate_checked_refines
      (domain_certificate : VkDomain.certificate)
      (srs_refinement : VkSrsDataView.refinement)
      (params_well_formed : VkMsm.params_well_formed)
      (values : list Z) :
    preconditionsb values = true ->
    evaluate_checked values = Some (reference_commitment values).
  Proof.
    intros Hchecked.
    destruct (preconditionsb_sound values Hchecked) as [Hlength Hvalues].
    unfold evaluate_checked. rewrite Hchecked.
    rewrite (fast_commitment_refines domain_certificate srs_refinement
      params_well_formed values Hlength Hvalues).
    reflexivity.
  Qed.

End OrchardInstanceCommitmentEval.
