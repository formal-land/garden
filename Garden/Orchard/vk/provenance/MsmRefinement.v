(** * Semantic refinement of the primitive-array Orchard MSM

    The executable checker uses primitive arrays, width-eight scalar windows,
    and Jacobian coordinates.  This file gives that implementation a purely
    mathematical meaning.  All production-sized loops are treated
    structurally: no proof evaluates a 2,048-point MSM inside Rocq's kernel. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import ZArith Lists.List Bool.Bool micromega.Lia.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Prim63.WindowRefinement.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.MsmChecks.
Require Import Garden.Orchard.vk.provenance.ArrayOfListRefinement.
Require Import Garden.Orchard.vk.provenance.JacobianRefinement.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope uint63_scope.

Module VkMsmRefinement.
  Module J := VkJacobian.
  Module JR := VkJacobianRefinement.
  Module W := Prim63WindowRefinement PallasPConfig.

  Definition scalar_values (coefficients : list Prim63Words.words5) : list Z :=
    List.map Prim63Words.eval5 coefficients.

  Definition scalar_digits (coefficients : list Prim63Words.words5)
      : list (list Z) :=
    List.map VkMsm.digits32 (scalar_values coefficients).

  (** ** Small list and group helpers *)

  Lemma nth_error_combine_some {A B : Type}
      (left : list A) (right : list B) (index : nat) (a : A) (b : B) :
    List.nth_error left index = Some a ->
    List.nth_error right index = Some b ->
    List.nth_error (List.combine left right) index = Some (a, b).
  Proof.
    revert left right.
    induction index as [|index IH]; intros [|a' left] [|b' right]
      Hleft Hright; cbn in *; try discriminate.
    - congruence.
    - now apply IH.
  Qed.

  Lemma firstn_succ_from_nth_error {A : Type}
      (values : list A) (index : nat) (value : A) :
    List.nth_error values index = Some value ->
    List.firstn (S index) values = List.firstn index values ++ [value].
  Proof.
    revert index value.
    induction values as [|head values IH]; intros [|index] value Hnth;
      cbn in *; try discriminate.
    - now inversion Hnth.
    - rewrite IH by exact Hnth. reflexivity.
  Qed.

  Lemma forall_map_snd_firstn {A : Type}
      (pairs : list (Z * A)) (P : A -> Prop) (count : nat) :
    List.Forall P (List.map snd pairs) ->
    List.Forall P (List.map snd (List.firstn count pairs)).
  Proof.
    revert count.
    induction pairs as [|[digit point] pairs IH]; intros [|count] Hall;
      cbn [List.map List.firstn snd]; constructor.
    - inversion Hall; assumption.
    - inversion Hall; subst. now apply IH.
  Qed.

  Lemma represents_good (p : J.point) (P : Vesta.point) :
    JR.represents p P -> VkMsm.good P.
  Proof. intros (_ & Hreduced & Hon_curve & _). now split. Qed.

  Lemma represents_transport (p : J.point) (P Q : Vesta.point) :
    JR.represents p P -> P = Q -> JR.represents p Q.
  Proof. intros H ->. exact H. Qed.

  Lemma psum_snoc (points : list Vesta.point) (point : Vesta.point) :
    List.Forall VkMsm.good points -> VkMsm.good point ->
    VkMsm.psum (points ++ [point]) =
      VkMsm.padd (VkMsm.psum points) point.
  Proof.
    intros Hpoints Hpoint.
    induction Hpoints as [|head points Hhead Hpoints IH].
    - cbn [VkMsm.psum].
      now rewrite VkMsm.vadd_0_l, VkMsm.vadd_0_r.
    - cbn [VkMsm.psum List.app].
      rewrite IH.
      symmetry.
      apply VkMsm.vadd_assoc.
      + exact Hhead.
      + apply VkMsm.psum_good. exact Hpoints.
      + exact Hpoint.
  Qed.

  Lemma filtered_pair_points_good (pairs : list (Z * Vesta.point))
      (value : Z) :
    List.Forall VkMsm.good (List.map snd pairs) ->
    List.Forall VkMsm.good
      (List.map snd
        (List.filter (fun pair => Z.eqb (fst pair) value) pairs)).
  Proof.
    intros Hgood.
    apply List.Forall_forall. intros point Hpoint.
    apply List.in_map_iff in Hpoint.
    destruct Hpoint as [[digit base] [Hpoint Hin]]. cbn in Hpoint. subst base.
    apply List.filter_In in Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) Hgood point
      (List.in_map snd pairs (digit, point) Hin)).
  Qed.

  Lemma bucket_snoc (pairs : list (Z * Vesta.point))
      (digit : Z) (base : Vesta.point) (value : Z) :
    List.Forall VkMsm.good (List.map snd pairs) ->
    VkMsm.good base ->
    VkMsm.bucket (pairs ++ [(digit, base)]) value =
      if Z.eqb digit value
      then VkMsm.padd (VkMsm.bucket pairs value) base
      else VkMsm.bucket pairs value.
  Proof.
    intros Hpairs Hbase.
    unfold VkMsm.bucket.
    rewrite List.filter_app, List.map_app.
    cbn [List.filter fst snd].
    destruct (Z.eqb digit value) eqn:Heq; cbn [List.map].
    - apply psum_snoc.
      + now apply filtered_pair_points_good.
      + exact Hbase.
    - now rewrite List.app_nil_r.
  Qed.

  (** ** Width-eight extraction denotes the abstract base-256 digit *)

  Lemma pow_256 (index : nat) :
    256 ^ Z.of_nat index = 2 ^ (8 * Z.of_nat index).
  Proof.
    replace 256 with (2 ^ 8) by reflexivity.
    symmetry. apply Z.pow_mul_r; lia.
  Qed.

  Lemma nth_digits_go (fuel index : nat) (scalar : Z) :
    (index < fuel)%nat ->
    List.nth index (VkMsm.digits_go fuel scalar) 0 =
      (scalar / 256 ^ Z.of_nat index) mod 256.
  Proof.
    revert index scalar.
    induction fuel as [|fuel IH]; intros [|index] scalar Hindex;
      cbn [VkMsm.digits_go List.nth]; try lia.
    - now rewrite Z.pow_0_r, Z.div_1_r.
    - rewrite IH by lia.
      rewrite Z.div_div by
        (try lia; apply Z.pow_pos_nonneg; lia).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      f_equal. ring.
  Qed.

  Lemma nth_digits32 (scalar : Z) (window : nat) :
    (window < 32)%nat ->
    List.nth window (VkMsm.digits32 scalar) 0 =
      (scalar / 2 ^ (8 * Z.of_nat window)) mod 256.
  Proof.
    intro Hwindow.
    unfold VkMsm.digits32.
    rewrite nth_digits_go by exact Hwindow.
    now rewrite pow_256.
  Qed.

  Lemma executable_digit_spec (coefficient : Prim63Words.words5)
      (window : nat) :
    (window < 32)%nat ->
    Uint63.to_Z
      (PallasP.window8_standard coefficient (ArrayLinear.index window)) =
      List.nth window (VkMsm.digits32 (Prim63Words.eval5 coefficient)) 0.
  Proof.
    intro Hwindow.
    rewrite W.window8_standard_spec.
    - rewrite ArrayLinear.to_Z_index.
      + symmetry. apply nth_digits32. exact Hwindow.
      + apply (ArrayLinear.fits_nat_lt window 32 Hwindow).
        exact ArrayLinear.window_count_fits_word.
    - rewrite ArrayLinear.to_Z_index.
      + lia.
      + apply (ArrayLinear.fits_nat_lt window 32 Hwindow).
        exact ArrayLinear.window_count_fits_word.
  Qed.

  Lemma executable_digit_bound (coefficient : Prim63Words.words5)
      (window : nat) :
    (window < 32)%nat ->
    0 <= Uint63.to_Z
      (PallasP.window8_standard coefficient (ArrayLinear.index window)) < 256.
  Proof.
    intro Hwindow.
    apply W.window8_standard_bound.
    rewrite ArrayLinear.to_Z_index.
    - lia.
    - apply (ArrayLinear.fits_nat_lt window 32 Hwindow).
      exact ArrayLinear.window_count_fits_word.
  Qed.

  (** ** Exact array views for coefficients and SRS bases *)

  Lemma hash_points_from_length (start count : nat) :
    List.length (VkSrs.hash_points_from start count) = count.
  Proof.
    unfold VkSrs.hash_points_from.
    now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma srs_lengths :
    VkSrsDataView.refinement ->
    List.length VkSrsDataView.g = 2048%nat /\
    List.length VkSrsDataView.denoted_g = 2048%nat.
  Proof.
    intro Hrefinement.
    pose proof (VkSrsDataView.g_exact Hrefinement) as Hexact.
    assert (Hdenoted : List.length VkSrsDataView.denoted_g = 2048%nat).
    { rewrite Hexact. apply hash_points_from_length. }
    split; [|exact Hdenoted].
    unfold VkSrsDataView.denoted_g in Hdenoted.
    now rewrite List.length_map in Hdenoted.
  Qed.

  Lemma scalar_array_view (coefficients : list Prim63Words.words5) :
    List.length coefficients = 2048%nat ->
    ArrayLinear.view (VkMsmChecks.scalar_array coefficients) coefficients.
  Proof.
    intro Hlength.
    unfold VkMsmChecks.scalar_array.
    apply VkArrayOfListRefinement.array_of_list_view.
    - rewrite Hlength. exact ArrayLinear.vector_size_fits_word.
    - rewrite Hlength. exact ArrayLinear.vector_size_fits_array.
  Qed.

  Lemma base_array_view :
    VkSrsDataView.refinement ->
    ArrayLinear.view VkSrsDataView.g_array VkSrsDataView.g.
  Proof.
    intro Hrefinement.
    unfold VkSrsDataView.g_array.
    apply VkArrayOfListRefinement.array_of_list_view.
    - rewrite (proj1 (srs_lengths Hrefinement)).
      exact ArrayLinear.vector_size_fits_word.
    - rewrite (proj1 (srs_lengths Hrefinement)).
      exact ArrayLinear.vector_size_fits_array.
  Qed.

  Lemma affine_denote_is_srs_denote (point : J.affine) :
    JR.affine_denote point = VkSrsDataView.denote_affine point.
  Proof.
    unfold JR.affine_denote, VkSrsDataView.denote_affine.
    rewrite !PallasQFacts.to_Z_denote.
    reflexivity.
  Qed.

  (** ** Bucket filling *)

  Record buckets_represent (buckets : PrimArray.array J.point)
      (pairs : list (Z * Vesta.point)) : Prop := {
    buckets_length :
      PrimArray.length buckets = ArrayLinear.pippenger_bucket_count;
    bucket_at : forall index,
      (index < ArrayLinear.pippenger_bucket_count_nat)%nat ->
      JR.represents (ArrayLinear.get_at buckets index)
        (VkMsm.bucket pairs (Z.of_nat (S index)))
  }.

  Lemma empty_buckets_represent :
    buckets_represent
      (PrimArray.make ArrayLinear.pippenger_bucket_count J.identity) [].
  Proof.
    constructor.
    - apply ArrayLinear.make_bucket_length.
    - intros index Hindex.
      change (JR.represents
        (ArrayLinear.get_at
          (PrimArray.make ArrayLinear.pippenger_bucket_count J.identity)
          index) Vesta.identity).
      assert (Hview : ArrayLinear.view
          (PrimArray.make ArrayLinear.pippenger_bucket_count J.identity)
          (List.repeat J.identity
            ArrayLinear.pippenger_bucket_count_nat)).
      { apply ArrayLinear.view_make.
        - exact ArrayLinear.bucket_count_fits_word.
        - exact ArrayLinear.bucket_count_fits_array. }
      rewrite (ArrayLinear.view_nth Hview index J.identity).
      + exact JR.identity_represents.
      + apply ArrayLinear.nth_error_repeat_value. exact Hindex.
  Qed.

  Lemma digit_bucket_index (digit : PrimInt63.int) :
    0 < Uint63.to_Z digit < 256 ->
    PrimInt63.sub digit 1%uint63 =
      ArrayLinear.index (Z.to_nat (Uint63.to_Z digit - 1)).
  Proof.
    intro Hdigit.
    set (index := Z.to_nat (Uint63.to_Z digit - 1)).
    assert (HindexZ : Z.of_nat index = Uint63.to_Z digit - 1).
    { unfold index. apply Z2Nat.id. lia. }
    assert (Hindex : (index < 255)%nat).
    { apply Nat2Z.inj_lt. rewrite HindexZ. lia. }
    apply Uint63.to_Z_inj.
    rewrite Uint63.sub_spec, Uint63.to_Z_1.
    rewrite ArrayLinear.to_Z_index.
    - rewrite HindexZ, Z.mod_small; [reflexivity |].
      split; [lia |].
      assert (Hcapacity : 256 < Uint63Axioms.wB) by
        (vm_compute; reflexivity).
      lia.
    - apply (ArrayLinear.fits_nat_lt index 255 Hindex).
      exact ArrayLinear.bucket_count_fits_word.
  Qed.

  Lemma bucket_step_sound
      (scalars : PrimArray.array Prim63Words.words5)
      (bases : PrimArray.array J.affine) (window index : nat)
      (buckets : PrimArray.array J.point)
      (pairs : list (Z * Vesta.point))
      (coefficient : Prim63Words.words5) (base : J.affine) :
    (window < 32)%nat ->
    PrimArray.get scalars (ArrayLinear.index index) = coefficient ->
    PrimArray.get bases (ArrayLinear.index index) = base ->
    JR.affine_canonical base ->
    Vesta.on_curve (VkSrsDataView.denote_affine base) ->
    List.Forall VkMsm.good (List.map snd pairs) ->
    buckets_represent buckets pairs ->
    buckets_represent
      (J.bucket_step scalars bases (ArrayLinear.index window)
        (ArrayLinear.index index) buckets)
      (pairs ++
        [(List.nth window
            (VkMsm.digits32 (Prim63Words.eval5 coefficient)) 0,
          VkSrsDataView.denote_affine base)]).
  Proof.
    intros Hwindow Hcoefficient Hbase Hbase_canonical Hbase_on_curve
      Hpairs Hstate.
    set (primitive_digit :=
      PallasP.window8_standard coefficient (ArrayLinear.index window)).
    set (digit := Uint63.to_Z primitive_digit).
    assert (Hdigit_spec :
      digit = List.nth window
        (VkMsm.digits32 (Prim63Words.eval5 coefficient)) 0).
    { unfold digit, primitive_digit. now apply executable_digit_spec. }
    assert (Hdigit_bound : 0 <= digit < 256).
    { unfold digit, primitive_digit. now apply executable_digit_bound. }
    assert (Hbase_represents :
      JR.represents (J.of_affine base) (VkSrsDataView.denote_affine base)).
    { eapply represents_transport.
      - apply JR.of_affine_represents.
        + exact Hbase_canonical.
        + rewrite affine_denote_is_srs_denote. exact Hbase_on_curve.
      - apply affine_denote_is_srs_denote. }
    assert (Hbase_good : VkMsm.good (VkSrsDataView.denote_affine base))
      by (now apply (represents_good (J.of_affine base))).
    unfold J.bucket_step.
    rewrite Hcoefficient, Hbase.
    fold primitive_digit.
    destruct (PrimInt63.eqb primitive_digit 0%uint63) eqn:Hzero.
    - apply Uint63.eqb_spec in Hzero. subst primitive_digit.
      assert (Hdigit_zero : digit = 0) by reflexivity.
      rewrite Hdigit_zero in Hdigit_spec.
      constructor.
      + exact (buckets_length _ _ Hstate).
      + intros bucket_index Hbucket_index.
        eapply represents_transport.
        * exact (bucket_at _ _ Hstate bucket_index Hbucket_index).
        * rewrite bucket_snoc by assumption.
          rewrite <- Hdigit_spec, Hdigit_zero.
          destruct (Z.eqb_spec 0 (Z.of_nat (S bucket_index)));
            [lia | reflexivity].
    - assert (Hprimitive_nonzero : primitive_digit <> 0%uint63).
      { intro Heq. subst primitive_digit.
        rewrite Uint63.eqb_refl in Hzero. discriminate. }
      assert (Hdigit_nonzero : digit <> 0).
      { intro Hdigit_zero. apply Hprimitive_nonzero.
        apply Uint63.to_Z_inj.
        change digit = Uint63.to_Z 0%uint63.
        rewrite Hdigit_zero. reflexivity. }
      assert (Hdigit_positive : 0 < digit) by
        (pose proof (Uint63.to_Z_bounded primitive_digit); lia).
      set (updated_index := Z.to_nat (digit - 1)).
      assert (Hupdated_index_Z : Z.of_nat updated_index = digit - 1).
      { unfold updated_index. apply Z2Nat.id. lia. }
      assert (Hupdated_index :
        (updated_index < ArrayLinear.pippenger_bucket_count_nat)%nat).
      { unfold ArrayLinear.pippenger_bucket_count_nat.
        apply Nat2Z.inj_lt. rewrite Hupdated_index_Z. lia. }
      assert (Hprimitive_index :
        PrimInt63.sub primitive_digit 1%uint63 =
          ArrayLinear.index updated_index).
      { unfold updated_index. apply digit_bucket_index. lia. }
      rewrite Hprimitive_index.
      constructor.
      + rewrite ArrayLinear.length_set.
        exact (buckets_length _ _ Hstate).
      + intros bucket_index Hbucket_index.
        destruct (Nat.eq_dec bucket_index updated_index) as [Heq | Hneq].
        * subst bucket_index.
          unfold ArrayLinear.get_at.
          rewrite ArrayLinear.get_set_same.
          2: { unfold ArrayLinear.in_bounds.
               rewrite (buckets_length _ _ Hstate).
               apply ArrayLinear.bucket_index_bound. exact Hupdated_index. }
          assert (Hvalue : Z.of_nat (S updated_index) = digit).
          { rewrite Nat2Z.inj_succ, Hupdated_index_Z. lia. }
          rewrite Hvalue.
          rewrite bucket_snoc by assumption.
          rewrite <- Hdigit_spec, Z.eqb_refl.
          apply JR.add_represents.
          -- exact (bucket_at _ _ Hstate updated_index Hupdated_index).
          -- exact Hbase_represents.
        * unfold ArrayLinear.get_at.
          rewrite ArrayLinear.get_set_other.
          2: { intro Heq. apply Hneq.
               apply ArrayLinear.index_inj.
               - apply (ArrayLinear.fits_nat_lt bucket_index 255);
                   assumption.
               - apply (ArrayLinear.fits_nat_lt updated_index 255);
                   assumption.
               - symmetry. exact Heq. }
          eapply represents_transport.
          -- exact (bucket_at _ _ Hstate bucket_index Hbucket_index).
          -- rewrite bucket_snoc by assumption.
             rewrite <- Hdigit_spec.
             destruct (Z.eqb_spec digit (Z.of_nat (S bucket_index)))
               as [Hequal | Hnot_equal]; [|reflexivity].
             exfalso. apply Hneq.
             apply Nat2Z.inj.
             rewrite Hupdated_index_Z, Nat2Z.inj_succ, Hequal. lia.
  Qed.

  Definition window_pairs (coefficients : list Prim63Words.words5)
      (window : nat) : list (Z * Vesta.point) :=
    VkMsm.win_pairs (scalar_digits coefficients)
      VkSrsDataView.denoted_g window.

  Lemma denoted_g_good :
    VkSrsDataView.refinement ->
    List.Forall VkMsm.good VkSrsDataView.denoted_g.
  Proof.
    intro Hrefinement.
    apply List.Forall_forall. intros point Hpoint. split.
    - exact (proj1 (List.Forall_forall _ _)
        (VkSrsDataView.g_reduced Hrefinement) point Hpoint).
    - exact (proj1 (List.Forall_forall _ _)
        (VkSrsDataView.g_on_curve Hrefinement) point Hpoint).
  Qed.

  Lemma window_pairs_length (coefficients : list Prim63Words.words5)
      (window : nat) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    List.length (window_pairs coefficients window) = 2048%nat.
  Proof.
    intros Hcoefficients Hrefinement.
    unfold window_pairs, VkMsm.win_pairs, scalar_digits, scalar_values.
    rewrite List.length_combine, !List.length_map, Hcoefficients.
    rewrite (proj2 (srs_lengths Hrefinement)).
    reflexivity.
  Qed.

  Lemma window_pairs_good (coefficients : list Prim63Words.words5)
      (window : nat) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    List.Forall VkMsm.good
      (List.map snd (window_pairs coefficients window)).
  Proof.
    intros Hcoefficients Hrefinement.
    unfold window_pairs, VkMsm.win_pairs.
    rewrite VkMsm.combine_snd.
    - exact (denoted_g_good Hrefinement).
    - unfold scalar_digits, scalar_values.
      rewrite !List.length_map, Hcoefficients.
      symmetry. exact (proj2 (srs_lengths Hrefinement)).
  Qed.

  Lemma window_pair_at (coefficients : list Prim63Words.words5)
      (window index : nat) (coefficient : Prim63Words.words5)
      (base : J.affine) :
    List.nth_error coefficients index = Some coefficient ->
    List.nth_error VkSrsDataView.g index = Some base ->
    List.nth_error (window_pairs coefficients window) index =
      Some
        (List.nth window
          (VkMsm.digits32 (Prim63Words.eval5 coefficient)) 0,
         VkSrsDataView.denote_affine base).
  Proof.
    intros Hcoefficient Hbase.
    unfold window_pairs, VkMsm.win_pairs, scalar_digits, scalar_values.
    apply nth_error_combine_some.
    - rewrite !List.nth_error_map, Hcoefficient. reflexivity.
    - unfold VkSrsDataView.denoted_g.
      rewrite List.nth_error_map, Hbase. reflexivity.
  Qed.

  Theorem fill_buckets_sound (coefficients : list Prim63Words.words5)
      (window : nat) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    (window < 32)%nat ->
    buckets_represent
      (J.fill_buckets (VkMsmChecks.scalar_array coefficients)
        VkSrsDataView.g_array (ArrayLinear.index window))
      (window_pairs coefficients window).
  Proof.
    intros Hcoefficients Hrefinement Hwindow.
    pose proof (scalar_array_view coefficients Hcoefficients) as Hscalars.
    pose proof (base_array_view Hrefinement) as Hbases.
    pose proof (window_pairs_good coefficients window
      Hcoefficients Hrefinement) as Hpairs_good.
    unfold J.fill_buckets.
    change (0%uint63) with (ArrayLinear.index 0).
    rewrite Prim63Loop.foldi_u63_index.
    2: { exact ArrayLinear.vector_size_fits_word. }
    set (pairs := window_pairs coefficients window).
    set (Inv := fun (index : nat) (buckets : PrimArray.array J.point) =>
      buckets_represent buckets (List.firstn index pairs)).
    assert (Hinitial : Inv 0
      (PrimArray.make ArrayLinear.pippenger_bucket_count J.identity)).
    { unfold Inv. cbn [List.firstn]. exact empty_buckets_represent. }
    assert (Hstep : forall index buckets,
      0 <= index < 0 + ArrayLinear.vector_size_nat ->
      Inv index buckets ->
      Inv (S index)
        (J.bucket_step (VkMsmChecks.scalar_array coefficients)
          VkSrsDataView.g_array (ArrayLinear.index window)
          (ArrayLinear.index index) buckets)).
    { intros index buckets Hindex Hstate.
      assert (Hindex_bound : (index < 2048)%nat) by
        (unfold ArrayLinear.vector_size_nat in Hindex; lia).
      destruct (List.nth_error coefficients index) as [coefficient|]
        eqn:Hcoefficient.
      2: { exfalso.
           assert (Hsome : List.nth_error coefficients index <> None).
           { apply (proj2 (List.nth_error_Some coefficients index)).
             rewrite Hcoefficients. exact Hindex_bound. }
           now apply Hsome. }
      destruct (List.nth_error VkSrsDataView.g index) as [base|]
        eqn:Hbase.
      2: { exfalso.
           assert (Hsome :
             List.nth_error VkSrsDataView.g index <> None).
           { apply (proj2
               (List.nth_error_Some VkSrsDataView.g index)).
             rewrite (proj1 (srs_lengths Hrefinement)).
             exact Hindex_bound. }
           now apply Hsome. }
      pose proof (window_pair_at coefficients window index coefficient base
        Hcoefficient Hbase) as Hpair.
      unfold Inv in Hstate |- *.
      rewrite (firstn_succ_from_nth_error pairs index _).
      2: { exact Hpair. }
      eapply bucket_step_sound.
      - exact Hwindow.
      - exact (ArrayLinear.view_nth Hscalars index coefficient Hcoefficient).
      - exact (ArrayLinear.view_nth Hbases index base Hbase).
      - pose proof (proj1 (List.Forall_forall _ _)
          (VkSrsDataView.g_normalized Hrefinement) base
          (List.nth_error_In _ _ Hbase)) as Hnormalized.
        destruct Hnormalized as [Hx Hy].
        now apply JR.affine_canonical_of_normalized.
      - exact (proj1 (List.Forall_forall _ _)
          (VkSrsDataView.g_on_curve Hrefinement)
          (VkSrsDataView.denote_affine base)
          (List.in_map _ _ _ (List.nth_error_In _ _ Hbase))).
      - apply forall_map_snd_firstn. exact Hpairs_good.
      - exact Hstate. }
    pose proof (Prim63Loop.foldi_from_invariant Inv
      ArrayLinear.vector_size_nat 0
      (fun index =>
        J.bucket_step (VkMsmChecks.scalar_array coefficients)
          VkSrsDataView.g_array (ArrayLinear.index window)
          (ArrayLinear.index index))
      (PrimArray.make ArrayLinear.pippenger_bucket_count J.identity)
      Hinitial Hstep) as Hfinal.
    unfold Inv in Hfinal.
    replace (0 + ArrayLinear.vector_size_nat)%nat with 2048%nat in Hfinal
      by reflexivity.
    rewrite List.firstn_all2 in Hfinal.
    - exact Hfinal.
    - rewrite (window_pairs_length coefficients window
      Hcoefficients Hrefinement). lia.
  Qed.

  (** ** Descending bucket aggregation *)

  Lemma descending_bucket_index (ascending : nat) :
    (ascending < ArrayLinear.pippenger_bucket_count_nat)%nat ->
    PrimInt63.sub 254%uint63 (ArrayLinear.index ascending) =
      ArrayLinear.index (254 - ascending).
  Proof.
    intro Hascending.
    assert (Hresult : (254 - ascending < 255)%nat) by lia.
    apply Uint63.to_Z_inj.
    rewrite Uint63.sub_spec.
    change (Uint63.to_Z 254%uint63) with 254.
    rewrite ArrayLinear.to_Z_index.
    - rewrite ArrayLinear.to_Z_index.
      + rewrite Z.mod_small.
        * f_equal. rewrite Nat2Z.inj_sub by lia. lia.
        * split; [lia |].
          assert (Hcapacity : 256 < Uint63Axioms.wB) by
            (vm_compute; reflexivity).
          lia.
      + apply (ArrayLinear.fits_nat_lt (254 - ascending) 255 Hresult).
        exact ArrayLinear.bucket_count_fits_word.
    - apply (ArrayLinear.fits_nat_lt ascending 255 Hascending).
      exact ArrayLinear.bucket_count_fits_word.
  Qed.

  Lemma nth_error_desc_from (count index : nat) :
    (index < count)%nat ->
    List.nth_error (VkMsm.desc_from count) index =
      Some (Z.of_nat (count - index)).
  Proof.
    revert index.
    induction count as [|count IH]; intros [|index] Hindex;
      cbn [VkMsm.desc_from List.nth_error]; try lia.
    - f_equal. f_equal. lia.
    - rewrite IH by lia. f_equal. f_equal. lia.
  Qed.

  Definition bucket_values (pairs : list (Z * Vesta.point))
      : list Vesta.point :=
    List.map (VkMsm.bucket pairs) (VkMsm.desc_from 255).

  Definition aggregate_step (state : Vesta.point * Vesta.point)
      (bucket : Vesta.point) : Vesta.point * Vesta.point :=
    let running := VkMsm.padd (fst state) bucket in
    (running, VkMsm.padd (snd state) running).

  Definition state_represents
      (state : J.point * J.point) (abstract : Vesta.point * Vesta.point) : Prop :=
    JR.represents (fst state) (fst abstract) /\
    JR.represents (snd state) (snd abstract).

  Lemma aggregate_step_sound (state : J.point * J.point)
      (abstract : Vesta.point * Vesta.point) (bucket : J.point)
      (abstract_bucket : Vesta.point) :
    state_represents state abstract ->
    JR.represents bucket abstract_bucket ->
    state_represents
      (J.add (fst state) bucket,
       J.add (snd state) (J.add (fst state) bucket))
      (aggregate_step abstract abstract_bucket).
  Proof.
    intros [Hrunning Hsum] Hbucket.
    unfold state_represents, aggregate_step. cbn [fst snd]. split.
    - now apply JR.add_represents.
    - apply JR.add_represents; [exact Hsum |].
      now apply JR.add_represents.
  Qed.

  Lemma bucket_sum_step_sound (buckets : PrimArray.array J.point)
      (pairs : list (Z * Vesta.point)) (ascending : nat)
      (state : J.point * J.point) (abstract : Vesta.point * Vesta.point) :
    (ascending < 255)%nat ->
    buckets_represent buckets pairs ->
    state_represents state abstract ->
    state_represents
      (J.bucket_sum_step buckets (ArrayLinear.index ascending) state)
      (aggregate_step abstract
        (List.nth ascending (bucket_values pairs) Vesta.identity)).
  Proof.
    intros Hascending Hbuckets Hstate.
    assert (Hindex : (254 - ascending < 255)%nat) by lia.
    assert (Hvalue :
      List.nth ascending (bucket_values pairs) Vesta.identity =
        VkMsm.bucket pairs (Z.of_nat (S (254 - ascending)))).
    { unfold bucket_values.
      assert (Hnth :
        List.nth_error
          (List.map (VkMsm.bucket pairs) (VkMsm.desc_from 255)) ascending =
        Some (VkMsm.bucket pairs (Z.of_nat (255 - ascending)))).
      { rewrite List.nth_error_map,
          (nth_error_desc_from 255 ascending Hascending).
        reflexivity. }
      apply List.nth_error_nth with (d := Vesta.identity) in Hnth.
      rewrite Hnth.
      f_equal. f_equal. lia. }
    unfold J.bucket_sum_step.
    rewrite descending_bucket_index by exact Hascending.
    fold (ArrayLinear.get_at buckets (254 - ascending)).
    rewrite Hvalue.
    apply aggregate_step_sound.
    - exact Hstate.
    - exact (bucket_at _ _ Hbuckets (254 - ascending) Hindex).
  Qed.

  Lemma aggregate_step_firstn (values : list Vesta.point) (index : nat)
      (value : Vesta.point) :
    List.nth_error values index = Some value ->
    List.fold_left aggregate_step (List.firstn (S index) values)
      (Vesta.identity, Vesta.identity) =
    aggregate_step
      (List.fold_left aggregate_step (List.firstn index values)
        (Vesta.identity, Vesta.identity)) value.
  Proof.
    intro Hnth.
    rewrite (firstn_succ_from_nth_error values index value Hnth).
    rewrite List.fold_left_app. reflexivity.
  Qed.

  Lemma bucket_sum_loop_sound (buckets : PrimArray.array J.point)
      (pairs : list (Z * Vesta.point)) :
    buckets_represent buckets pairs ->
    state_represents
      (Prim63Loop.foldi_u63 ArrayLinear.pippenger_bucket_count_nat 0
        (J.bucket_sum_step buckets) (J.identity, J.identity))
      (List.fold_left aggregate_step (bucket_values pairs)
        (Vesta.identity, Vesta.identity)).
  Proof.
    intro Hbuckets.
    change (0%uint63) with (ArrayLinear.index 0).
    rewrite Prim63Loop.foldi_u63_index.
    2: { exact ArrayLinear.bucket_count_fits_word. }
    set (values := bucket_values pairs).
    set (Inv := fun (index : nat) (state : J.point * J.point) =>
      state_represents state
        (List.fold_left aggregate_step (List.firstn index values)
          (Vesta.identity, Vesta.identity))).
    assert (Hinitial : Inv 0 (J.identity, J.identity)).
    { unfold Inv, state_represents. cbn [List.firstn List.fold_left fst snd].
      split; exact JR.identity_represents. }
    assert (Hstep : forall index state,
      0 <= index < 0 + ArrayLinear.pippenger_bucket_count_nat ->
      Inv index state ->
      Inv (S index)
        (J.bucket_sum_step buckets (ArrayLinear.index index) state)).
    { intros index state Hindex Hstate.
      assert (Hindex_bound : (index < 255)%nat) by
        (unfold ArrayLinear.pippenger_bucket_count_nat in Hindex; lia).
      assert (Hnth : List.nth_error values index =
          Some (List.nth index values Vesta.identity)).
      { apply List.nth_error_nth'.
        unfold values, bucket_values.
        rewrite List.length_map, VkMsm.desc_from_length.
        exact Hindex_bound. }
      unfold Inv in Hstate |- *.
      rewrite (aggregate_step_firstn values index
        (List.nth index values Vesta.identity) Hnth).
      apply bucket_sum_step_sound; assumption. }
    pose proof (Prim63Loop.foldi_from_invariant Inv
      ArrayLinear.pippenger_bucket_count_nat 0
      (fun index => J.bucket_sum_step buckets (ArrayLinear.index index))
      (J.identity, J.identity) Hinitial Hstep) as Hfinal.
    unfold Inv in Hfinal.
    replace (0 + ArrayLinear.pippenger_bucket_count_nat)%nat
      with 255%nat in Hfinal by reflexivity.
    rewrite List.firstn_all2 in Hfinal.
    - exact Hfinal.
    - unfold values, bucket_values.
      rewrite List.length_map, VkMsm.desc_from_length. lia.
  Qed.

  Lemma aggr_go_fold_left (values : list Vesta.point)
      (running sum : Vesta.point) :
    VkMsm.aggr_go values running sum =
      snd (List.fold_left aggregate_step values (running, sum)).
  Proof.
    revert running sum.
    induction values as [|value values IH]; intros running sum;
      cbn [VkMsm.aggr_go List.fold_left aggregate_step fst snd].
    - reflexivity.
    - apply IH.
  Qed.

  Theorem window_sum_sound (coefficients : list Prim63Words.words5)
      (window : nat) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    (window < 32)%nat ->
    JR.represents
      (J.window_sum (VkMsmChecks.scalar_array coefficients)
        VkSrsDataView.g_array (ArrayLinear.index window))
      (VkMsm.win_sum (scalar_digits coefficients)
        VkSrsDataView.denoted_g window).
  Proof.
    intros Hcoefficients Hrefinement Hwindow.
    pose proof (fill_buckets_sound coefficients window
      Hcoefficients Hrefinement Hwindow) as Hfilled.
    pose proof (bucket_sum_loop_sound
      (J.fill_buckets (VkMsmChecks.scalar_array coefficients)
        VkSrsDataView.g_array (ArrayLinear.index window))
      (window_pairs coefficients window) Hfilled) as Hsum.
    unfold J.window_sum.
    eapply represents_transport.
    - exact (proj2 Hsum).
    - unfold VkMsm.win_sum, VkMsm.aggr, bucket_values, window_pairs.
      symmetry. apply aggr_go_fold_left.
  Qed.

  (** ** Window ranges and the low/high split *)

  Fixpoint descending_windows (start count : nat) : list nat :=
    match count with
    | O => []
    | S count' => (start + count')%nat :: descending_windows start count'
    end.

  Lemma descending_windows_length (start count : nat) :
    List.length (descending_windows start count) = count.
  Proof.
    induction count as [|count IH]; cbn [descending_windows List.length];
      congruence.
  Qed.

  Lemma nth_error_descending_windows (start count index : nat) :
    (index < count)%nat ->
    List.nth_error (descending_windows start count) index =
      Some (start + count - 1 - index)%nat.
  Proof.
    revert index.
    induction count as [|count IH]; intros [|index] Hindex;
      cbn [descending_windows List.nth_error]; try lia.
    - f_equal. lia.
    - rewrite IH by lia. f_equal. lia.
  Qed.

  Definition abstract_window_step (digits : list (list Z))
      (bases : list Vesta.point) (acc : Vesta.point) (window : nat) :
      Vesta.point :=
    VkMsm.padd (VkMsm.pmul 256 acc) (VkMsm.win_sum digits bases window).

  Lemma pip_go_fold_left (digits : list (list Z))
      (bases : list Vesta.point) (windows : list nat) (acc : Vesta.point) :
    VkMsm.pip_go digits bases windows acc =
      List.fold_left (abstract_window_step digits bases) windows acc.
  Proof.
    revert acc.
    induction windows as [|window windows IH]; intros acc;
      cbn [VkMsm.pip_go List.fold_left abstract_window_step].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma iter_double_mul (count : nat) (point : Vesta.point) :
    VkMsm.good point ->
    Nat.iter count (fun current => VkMsm.padd current current) point =
      VkMsm.pmul (2 ^ Z.of_nat count) point.
  Proof.
    intro Hpoint.
    induction count as [|count IH].
    - cbn [Nat.iter]. now rewrite Z.pow_0_r, VkMsm.vmul_1.
    - rewrite Nat.iter_succ, IH.
      rewrite <- VkMsm.vmul_2.
      rewrite <- VkMsm.vmul_mul by exact Hpoint.
      f_equal.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
  Qed.

  Lemma eight_doubles (point : Vesta.point) :
    VkMsm.good point ->
    Nat.iter 8 (fun current => VkMsm.padd current current) point =
      VkMsm.pmul 256 point.
  Proof.
    intro Hpoint. rewrite iter_double_mul by exact Hpoint.
    f_equal. vm_compute. reflexivity.
  Qed.

  Lemma range_step_sound (coefficients : list Prim63Words.words5)
      (window : nat) (point : J.point) (abstract : Vesta.point) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    (window < 32)%nat ->
    JR.represents point abstract ->
    JR.represents
      (J.add (J.double_n ArrayLinear.pippenger_window_bits_nat point)
        (J.window_sum (VkMsmChecks.scalar_array coefficients)
          VkSrsDataView.g_array (ArrayLinear.index window)))
      (abstract_window_step (scalar_digits coefficients)
        VkSrsDataView.denoted_g abstract window).
  Proof.
    intros Hcoefficients Hrefinement Hwindow Hpoint.
    unfold ArrayLinear.pippenger_window_bits_nat.
    apply JR.add_represents.
    - eapply represents_transport.
      + apply JR.double_n_represents. exact Hpoint.
      + apply eight_doubles. now apply (represents_good point).
    - exact (window_sum_sound coefficients window
        Hcoefficients Hrefinement Hwindow).
  Qed.

  Theorem window_range_sound (coefficients : list Prim63Words.words5)
      (range_start range_count : nat) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    (range_start + range_count <= 32)%nat ->
    JR.represents
      (J.window_range (VkMsmChecks.scalar_array coefficients)
        VkSrsDataView.g_array range_start range_count)
      (VkMsm.pip_go (scalar_digits coefficients)
        VkSrsDataView.denoted_g
        (descending_windows range_start range_count) Vesta.identity).
  Proof.
    intros Hcoefficients Hrefinement Hrange.
    unfold J.window_range.
    set (windows := descending_windows range_start range_count).
    set (Inv := fun (index : nat) (point : J.point) =>
      JR.represents point
        (List.fold_left
          (abstract_window_step (scalar_digits coefficients)
            VkSrsDataView.denoted_g)
          (List.firstn index windows) Vesta.identity)).
    assert (Hinitial : Inv 0 J.identity).
    { unfold Inv. cbn [List.firstn List.fold_left].
      exact JR.identity_represents. }
    assert (Hstep : forall index point,
      0 <= index < 0 + range_count ->
      Inv index point ->
      Inv (S index)
        (J.window_range_step (VkMsmChecks.scalar_array coefficients)
          VkSrsDataView.g_array range_start range_count index point)).
    { intros index point Hindex Hpoint.
      assert (Hindex_bound : (index < range_count)%nat) by lia.
      set (window := range_start + range_count - 1 - index)%nat.
      assert (Hwindow : (window < 32)%nat) by
        (unfold window; lia).
      assert (Hnth : List.nth_error windows index = Some window).
      { unfold windows, window. now apply nth_error_descending_windows. }
      unfold Inv in Hpoint |- *.
      rewrite (firstn_succ_from_nth_error windows index window Hnth),
        List.fold_left_app.
      cbn [List.fold_left].
      unfold J.window_range_step.
      fold window.
      apply range_step_sound; assumption. }
    pose proof (Prim63Loop.foldi_from_invariant Inv range_count 0
      (J.window_range_step (VkMsmChecks.scalar_array coefficients)
        VkSrsDataView.g_array range_start range_count)
      J.identity Hinitial Hstep) as Hfinal.
    unfold Inv in Hfinal.
    replace (0 + range_count)%nat with range_count in Hfinal by lia.
    rewrite List.firstn_all2 in Hfinal.
    2: { unfold windows. rewrite descending_windows_length. lia. }
    eapply represents_transport; [exact Hfinal |].
    symmetry. apply pip_go_fold_left.
  Qed.

  Corollary low_half_sound (coefficients : list Prim63Words.words5) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    JR.represents (VkMsmChecks.low_msm coefficients)
      (VkMsm.pip_go (scalar_digits coefficients)
        VkSrsDataView.denoted_g (descending_windows 0 16) Vesta.identity).
  Proof.
    intros Hcoefficients Hrefinement.
    unfold VkMsmChecks.low_msm, J.low_half.
    apply window_range_sound; try assumption. lia.
  Qed.

  Corollary high_half_sound (coefficients : list Prim63Words.words5) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    JR.represents (VkMsmChecks.high_msm coefficients)
      (VkMsm.pip_go (scalar_digits coefficients)
        VkSrsDataView.denoted_g (descending_windows 16 16) Vesta.identity).
  Proof.
    intros Hcoefficients Hrefinement.
    unfold VkMsmChecks.high_msm, J.high_half.
    apply window_range_sound; try assumption. lia.
  Qed.

  Lemma pip_go_app (digits : list (list Z)) (bases : list Vesta.point)
      (left right : list nat) (acc : Vesta.point) :
    VkMsm.pip_go digits bases (left ++ right) acc =
      VkMsm.pip_go digits bases right
        (VkMsm.pip_go digits bases left acc).
  Proof.
    revert acc.
    induction left as [|window left IH]; intros acc;
      cbn [List.app VkMsm.pip_go].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma half_windows_partition :
    descending_windows 16 16 ++ descending_windows 0 16 = VkMsm.tsd 32.
  Proof. vm_compute. reflexivity. Qed.

  Lemma scalar_digits_length (coefficients : list Prim63Words.words5) :
    List.length (scalar_digits coefficients) = List.length coefficients.
  Proof.
    unfold scalar_digits, scalar_values. now rewrite !List.length_map.
  Qed.

  Lemma scalar_digits_bounded (coefficients : list Prim63Words.words5) :
    List.Forall (List.Forall (fun digit => 0 <= digit < 256))
      (scalar_digits coefficients).
  Proof.
    apply List.Forall_forall. intros digits Hdigits.
    unfold scalar_digits in Hdigits.
    apply List.in_map_iff in Hdigits.
    destruct Hdigits as [scalar [<- Hscalar]].
    apply VkMsm.digits_go_bound.
  Qed.

  (** Recombination is stated on the actual scalar list, before mapping to
      its digit vectors. *)
  Lemma scalar_halves_recombine (scalars : list Z)
      (bases : list Vesta.point) :
    List.length scalars = List.length bases ->
    List.Forall VkMsm.good bases ->
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256) scalars ->
    let digits := List.map VkMsm.digits32 scalars in
    let low := VkMsm.pip_go digits bases
      (descending_windows 0 16) Vesta.identity in
    let high := VkMsm.pip_go digits bases
      (descending_windows 16 16) Vesta.identity in
    VkMsm.good low -> VkMsm.good high ->
    VkMsm.padd low (VkMsm.pmul (2 ^ 128) high) = VkMsm.msm scalars bases.
  Proof.
    intros Hlength Hbases Hscalars digits low high Hlow Hhigh.
    assert (Hdigits_length : List.length digits = List.length bases).
    { unfold digits. now rewrite List.length_map. }
    assert (Hdigits_bound :
      List.Forall (List.Forall (fun digit => 0 <= digit < 256)) digits).
    { unfold digits. apply List.Forall_forall. intros ds Hds.
      apply List.in_map_iff in Hds. destruct Hds as [scalar [<- _]].
      apply VkMsm.digits_go_bound. }
    assert (Hlow_length :
      List.length (descending_windows 0 16) = 16%nat) by
      (rewrite descending_windows_length; reflexivity).
    rewrite <- (VkMsm.pippenger_correct scalars bases
      Hlength Hbases Hscalars).
    unfold VkMsm.msm_pippenger.
    rewrite <- half_windows_partition, pip_go_app.
    fold digits high low.
    rewrite (VkMsm.pip_go_spec digits bases
      (descending_windows 0 16) high
      Hdigits_length Hbases Hhigh Hdigits_bound).
    assert (Hlow_spec :
      low = VkMsm.msm
        (List.map
          (fun ds => VkMsm.pval (descending_windows 0 16) ds 0) digits)
        bases).
    { unfold low.
      rewrite (VkMsm.pip_go_spec digits bases
        (descending_windows 0 16) Vesta.identity
        Hdigits_length Hbases VkMsm.good_identity Hdigits_bound).
      rewrite VkMsm.vmul_identity, VkMsm.vadd_0_l. reflexivity. }
    rewrite <- Hlow_spec.
    rewrite Hlow_length.
    replace (256 ^ Z.of_nat 16) with (2 ^ 128) by
      (vm_compute; reflexivity).
    apply VkMsm.vadd_comm.
    - exact Hlow.
    - now apply VkMsm.good_mul.
  Qed.

  Theorem assemble_halves_sound (coefficients : list Prim63Words.words5) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (scalar_values coefficients) ->
    JR.represents
      (J.assemble_halves (VkMsmChecks.low_msm coefficients)
        (VkMsmChecks.high_msm coefficients) VkSrsDataView.w)
      (VkMsm.padd
        (VkMsm.msm (scalar_values coefficients)
          VkSrsDataView.denoted_g)
        VkSrsDataView.denoted_w).
  Proof.
    intros Hcoefficients Hrefinement Hrange.
    pose proof (low_half_sound coefficients Hcoefficients Hrefinement) as Hlow.
    pose proof (high_half_sound coefficients Hcoefficients Hrefinement) as Hhigh.
    set (low := VkMsm.pip_go (scalar_digits coefficients)
      VkSrsDataView.denoted_g (descending_windows 0 16) Vesta.identity) in *.
    set (high := VkMsm.pip_go (scalar_digits coefficients)
      VkSrsDataView.denoted_g (descending_windows 16 16) Vesta.identity) in *.
    assert (Hlow_good : VkMsm.good low) by
      (now apply (represents_good (VkMsmChecks.low_msm coefficients))).
    assert (Hhigh_good : VkMsm.good high) by
      (now apply (represents_good (VkMsmChecks.high_msm coefficients))).
    assert (Hlength :
      List.length (scalar_values coefficients) =
        List.length VkSrsDataView.denoted_g).
    { unfold scalar_values. rewrite List.length_map, Hcoefficients.
      exact (eq_sym (proj2 (srs_lengths Hrefinement))). }
    assert (Hmsm :
      VkMsm.padd low (VkMsm.pmul (2 ^ 128) high) =
        VkMsm.msm (scalar_values coefficients) VkSrsDataView.denoted_g).
    { apply scalar_halves_recombine; try assumption.
      exact (denoted_g_good Hrefinement). }
    assert (Hcombined :
      JR.represents
        (J.add (VkMsmChecks.low_msm coefficients)
          (J.double_n 128 (VkMsmChecks.high_msm coefficients)))
        (VkMsm.msm (scalar_values coefficients)
          VkSrsDataView.denoted_g)).
    { eapply represents_transport.
      - apply JR.add_represents.
        + exact Hlow.
        + eapply represents_transport.
          * apply JR.double_n_represents. exact Hhigh.
          * apply iter_double_mul. exact Hhigh_good.
      - exact Hmsm. }
    unfold J.assemble_halves.
    apply JR.add_represents.
    - exact Hcombined.
    - eapply represents_transport.
      + apply JR.of_affine_represents.
        * destruct (VkSrsDataView.w_normalized Hrefinement) as [Hx Hy].
          now apply JR.affine_canonical_of_normalized.
        * rewrite affine_denote_is_srs_denote.
          exact (VkSrsDataView.w_on_curve Hrefinement).
      + apply affine_denote_is_srs_denote.
  Qed.

  Corollary assemble_halves_vk_msm_sound
      (coefficients : list Prim63Words.words5) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (scalar_values coefficients) ->
    JR.represents
      (J.assemble_halves (VkMsmChecks.low_msm coefficients)
        (VkMsmChecks.high_msm coefficients) VkSrsDataView.w)
      (VkMsm.padd
        (VkMsm.msm (scalar_values coefficients) VkMsm.g_points)
        VkMsm.w_point).
  Proof.
    intros Hlength Hrefinement Hrange.
    eapply represents_transport.
    - exact (assemble_halves_sound coefficients
        Hlength Hrefinement Hrange).
    - unfold VkMsm.g_points, VkMsm.w_point.
      rewrite <- (VkSrsDataView.g_exact Hrefinement),
        <- (VkSrsDataView.w_exact Hrefinement).
      reflexivity.
  Qed.

  (** Exact hand-off to the public Halo2 commitment specification.  The FFT
      refinement supplies [Hcoefficients_exact]; the column model supplies
      the length and nonnegativity premises for [commit_lagrange_intt]. *)
  Corollary assemble_halves_commit_lagrange_sound
      (coefficients : list Prim63Words.words5) (values : list Z) :
    List.length coefficients = 2048%nat ->
    VkSrsDataView.refinement ->
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (scalar_values coefficients) ->
    VkMsm.params_well_formed ->
    List.length values = 2048%nat ->
    List.Forall (fun value => 0 <= value) values ->
    scalar_values coefficients = VkMsm.intt values ->
    JR.represents
      (J.assemble_halves (VkMsmChecks.low_msm coefficients)
        (VkMsmChecks.high_msm coefficients) VkSrsDataView.w)
      (VkMsm.commit_lagrange values).
  Proof.
    intros Hcoefficient_length Hrefinement Hcoefficient_range
      Hparams Hvalue_length Hvalues Hcoefficients_exact.
    eapply represents_transport.
    - exact (assemble_halves_vk_msm_sound coefficients
        Hcoefficient_length Hrefinement Hcoefficient_range).
    - rewrite Hcoefficients_exact.
      symmetry.
      exact (VkMsm.commit_lagrange_intt values
        Hparams Hvalue_length Hvalues).
  Qed.

End VkMsmRefinement.
