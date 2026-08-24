(** * Primitive-word evaluation of Halo2 commitment MSMs

    The reference verifier retains Rust's explicit MSM state and its panic
    boundaries.  This module begins only after that state exists: the
    generator-length check remains outside the arithmetic kernel, and the
    x-sorted [other] list has already passed [insert_other]'s same-x checks.

    The executable kernel converts reduced Vesta points to the existing
    five-word Montgomery representation, uses the complete Jacobian formulas,
    and evaluates a variable-length list by binary double-and-add.  The
    [reference_terms] view exposes the precise order in which [other], [W],
    [U], and [G] contributions enter the reference evaluator. *)

From Stdlib Require Import ZArith Lists.List Bool.Bool Lia.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.JacobianRefinement.
Require Import Garden.Orchard.vk.provenance.MsmChecks.
Require Import Garden.Orchard.vk.provenance.MsmRefinement.
Require Import Garden.Orchard.vk.provenance.SrsDataView.

Import ListNotations.
Local Open Scope Z_scope.

Module CommitmentEval.
  Module Reference := CommitmentVerifier.
  Module Scalar := VerifierField.
  Module J := VkJacobian.
  Module JR := VkJacobianRefinement.
  Module Fq := PallasQ.

  Definition term : Type := (Z * Vesta.point)%type.

  Definition contribution (value : term) : Vesta.point :=
    Vesta.mul (fst value) (snd value).

  Definition term_good (value : term) : Prop := VkMsm.good (snd value).

  Definition reference_sum_from
      (terms : list term) (accumulator : Vesta.point) : Vesta.point :=
    List.fold_left
      (fun accumulator value => Vesta.add accumulator (contribution value))
      terms accumulator.

  Definition reference_sum (terms : list term) : Vesta.point :=
    reference_sum_from terms Vesta.identity.

  Definition affine_of_coordinates (x y : Z) : J.affine :=
    {| J.affine_x := Fq.from_Z x; J.affine_y := Fq.from_Z y |}.

  Definition point_of_reference (point : Vesta.point) : J.point :=
    match point with
    | Weierstrass.Infinity => J.identity
    | Weierstrass.Affine x y => J.of_affine (affine_of_coordinates x y)
    end.

  Fixpoint mul_pos (scalar : positive) (point : J.point) : J.point :=
    match scalar with
    | xH => point
    | xO scalar => J.double (mul_pos scalar point)
    | xI scalar => J.add point (J.double (mul_pos scalar point))
    end.

  Definition mul (scalar : Z) (point : J.point) : J.point :=
    match Scalar.canon scalar with
    | Z0 => J.identity
    | Zpos scalar => mul_pos scalar point
    | Zneg _ => J.identity
    end.

  Definition eval_term (value : term) : J.point :=
    mul (fst value) (point_of_reference (snd value)).

  Fixpoint eval_terms_from
      (terms : list term) (accumulator : J.point) : J.point :=
    match terms with
    | [] => accumulator
    | value :: terms =>
        eval_terms_from terms (J.add accumulator (eval_term value))
    end.

  Definition eval_terms (terms : list term) : J.point :=
    eval_terms_from terms J.identity.

  Definition other_terms (state : Reference.msm) : list term :=
    List.map
      (fun value =>
        (value.(Reference.term_scalar),
          Vesta.affine value.(Reference.term_x) value.(Reference.term_y)))
      state.(Reference.other).

  Definition optional_term
      (scalar : option Scalar.t) (base : Vesta.point) : list term :=
    match scalar with
    | None => []
    | Some scalar => [(scalar, base)]
    end.

  Definition fixed_terms
      (params : Reference.parameters) (state : Reference.msm) : list term :=
    other_terms state ++
    optional_term state.(Reference.w_scalar) params.(Reference.parameter_w) ++
    optional_term state.(Reference.u_scalar) params.(Reference.parameter_u).

  Definition reference_terms
      (params : Reference.parameters) (state : Reference.msm)
      : option (list term) :=
    match state.(Reference.g_scalars) with
    | None => Some (fixed_terms params state)
    | Some scalars =>
        if Nat.eqb (List.length scalars)
            (List.length params.(Reference.parameter_g)) then
          Some (fixed_terms params state ++
            List.combine scalars params.(Reference.parameter_g))
        else
          None
    end.

  Definition well_formed
      (params : Reference.parameters) (state : Reference.msm) : Prop :=
    match reference_terms params state with
    | None => True
    | Some terms => List.Forall term_good terms
    end.

  Definition eval
      (params : Reference.parameters) (state : Reference.msm) : option bool :=
    match reference_terms params state with
    | None => None
    | Some terms => Some (J.is_identity (eval_terms terms))
    end.

  (** The production SRS path keeps scalar limbs in standard form because
      the width-eight extractor consumes those limbs directly. *)
  Definition scalar_words (scalar : Scalar.t) : Prim63Words.words5 :=
    PallasP.standard_of_Z (Scalar.canon scalar).

  Definition scalar_word_list
      (scalars : list Scalar.t) : list Prim63Words.words5 :=
    List.map scalar_words scalars.

  Definition eval_srs_g (scalars : list Scalar.t) : J.point :=
    let coefficients := scalar_word_list scalars in
    J.add
      (J.assemble_halves (VkMsmChecks.low_msm coefficients)
        (VkMsmChecks.high_msm coefficients) VkSrsDataView.w)
      (mul (-1) (point_of_reference VkSrsDataView.denoted_w)).

  Definition srs_parameters : Reference.parameters := {|
    Reference.parameter_g := VkSrsDataView.denoted_g;
    Reference.parameter_w := VkSrsDataView.denoted_w;
    Reference.parameter_u := VkSrsDataView.denoted_u;
  |}.

  (** This is the parameter record used by the public post-NU6.3 verifier.
      Keeping the spelling here avoids an import cycle from the evaluator back
      into the protocol assembly module. *)
  Definition reference_srs_parameters : Reference.parameters := {|
    Reference.parameter_g := VkMsm.g_points;
    Reference.parameter_w := VkMsm.w_point;
    Reference.parameter_u := VkMsm.u_point;
  |}.

  (** The executable fixed-term view omits the unused generator field.  This
      matters under call-by-value reduction: passing the full SRS parameter
      record would otherwise construct its 2,048-point reference list before
      projecting only [W] and [U]. *)
  Definition srs_fixed_terms (state : Reference.msm) : list term :=
    other_terms state ++
    optional_term state.(Reference.w_scalar) VkSrsDataView.denoted_w ++
    optional_term state.(Reference.u_scalar) VkSrsDataView.denoted_u.

  Lemma srs_fixed_terms_eq (state : Reference.msm) :
    srs_fixed_terms state = fixed_terms srs_parameters state.
  Proof. reflexivity. Qed.

  Definition srs_well_formed (state : Reference.msm) : Prop :=
    List.Forall term_good (srs_fixed_terms state).

  Definition eval_srs (state : Reference.msm) : option bool :=
    match state.(Reference.g_scalars) with
    | None =>
        Some (J.is_identity (eval_terms (srs_fixed_terms state)))
    | Some scalars =>
        if Nat.eqb (List.length scalars) 2048 then
          Some (J.is_identity
            (J.add (eval_terms (srs_fixed_terms state))
              (eval_srs_g scalars)))
        else
          None
    end.

  (** ** Refinement of the variable-length kernel *)

  Lemma affine_of_coordinates_denote (x y : Z) :
    JR.affine_denote (affine_of_coordinates x y) = Vesta.affine x y.
  Proof.
    unfold JR.affine_denote, affine_of_coordinates.
    cbn [J.affine_x J.affine_y].
    rewrite !PallasQFacts.from_Z_denote.
    unfold Vesta.affine, UnOp.from.
    rewrite !Z.mod_mod by exact JR.q_pos.
    reflexivity.
  Qed.

  Lemma point_of_reference_represents (point : Vesta.point) :
    VkMsm.good point -> JR.represents (point_of_reference point) point.
  Proof.
    destruct point as [|x y].
    - intros _. exact JR.identity_represents.
    - intros [Hreduced Hon_curve].
      cbn [Vesta.reduced Weierstrass.reduced] in Hreduced.
      destruct Hreduced as [Hx Hy].
      assert (Haffine : Vesta.affine x y = Weierstrass.Affine x y).
      { unfold Vesta.affine. now rewrite Hx, Hy. }
      eapply VkMsmRefinement.represents_transport.
      + apply JR.of_affine_represents.
        * unfold JR.affine_canonical, affine_of_coordinates.
          cbn [J.affine_x J.affine_y].
          split; apply PallasQFacts.from_Z_canonical.
        * rewrite affine_of_coordinates_denote, Haffine.
          exact Hon_curve.
      + now rewrite affine_of_coordinates_denote.
  Qed.

  Lemma mul_pos_represents
      (scalar : positive) (point : J.point) (abstract : Vesta.point) :
    JR.represents point abstract ->
    JR.represents (mul_pos scalar point)
      (Weierstrass.mul_pos (p := Vesta.vesta_p) Vesta.a scalar abstract).
  Proof.
    induction scalar as [scalar IH | scalar IH |]; intros Hpoint;
      cbn [mul_pos Weierstrass.mul_pos].
    - apply JR.add_represents.
      + exact Hpoint.
      + apply JR.double_represents, IH. exact Hpoint.
    - apply JR.double_represents, IH. exact Hpoint.
    - exact Hpoint.
  Qed.

  Lemma scalar_canon_mul (scalar : Z) (point : Vesta.point) :
    VkMsm.good point ->
    Vesta.mul (Scalar.canon scalar) point = Vesta.mul scalar point.
  Proof.
    unfold Scalar.canon, Scalar.modulus.
    apply VkMsm.vmul_mod.
  Qed.

  Lemma mul_represents (scalar : Z) (point : J.point)
      (abstract : Vesta.point) :
    JR.represents point abstract ->
    JR.represents (mul scalar point) (Vesta.mul scalar abstract).
  Proof.
    intro Hpoint.
    pose proof (VkMsmRefinement.represents_good point abstract Hpoint)
      as Hgood.
    pose proof (scalar_canon_mul scalar abstract Hgood) as Hcanon_mul.
    unfold Scalar.canon, Scalar.modulus in Hcanon_mul.
    unfold mul.
    destruct (Scalar.canon scalar) as [|positive|positive] eqn:Hcanon.
    - eapply VkMsmRefinement.represents_transport.
      + exact JR.identity_represents.
      + unfold Scalar.canon, Scalar.modulus in Hcanon.
        rewrite Hcanon in Hcanon_mul.
        exact Hcanon_mul.
    - eapply VkMsmRefinement.represents_transport.
      + apply mul_pos_represents. exact Hpoint.
      + unfold Scalar.canon, Scalar.modulus in Hcanon.
        rewrite Hcanon in Hcanon_mul.
        exact Hcanon_mul.
    - exfalso.
      assert (Hmodulus : 0 < Scalar.modulus) by
        (unfold Scalar.modulus; vm_compute; reflexivity).
      assert (Hrange : 0 <= Scalar.canon scalar).
      { unfold Scalar.canon.
        exact (proj1 (Z.mod_pos_bound scalar Scalar.modulus Hmodulus)). }
      rewrite Hcanon in Hrange.
      lia.
  Qed.

  Lemma eval_term_represents (value : term) :
    term_good value ->
    JR.represents (eval_term value) (contribution value).
  Proof.
    intros Hgood.
    unfold eval_term, contribution.
    apply mul_represents, point_of_reference_represents.
    exact Hgood.
  Qed.

  Lemma eval_terms_from_represents
      (terms : list term) (accumulator : J.point)
      (abstract : Vesta.point) :
    JR.represents accumulator abstract ->
    List.Forall term_good terms ->
    JR.represents (eval_terms_from terms accumulator)
      (reference_sum_from terms abstract).
  Proof.
    revert accumulator abstract.
    induction terms as [|value terms IH]; intros accumulator abstract
      Haccumulator Hterms.
    - exact Haccumulator.
    - inversion Hterms as [|? ? Hvalue Htail]; subst.
      cbn [eval_terms_from reference_sum_from List.fold_left].
      apply IH.
      + apply JR.add_represents.
        * exact Haccumulator.
        * now apply eval_term_represents.
      + exact Htail.
  Qed.

  Theorem eval_terms_represents (terms : list term) :
    List.Forall term_good terms ->
    JR.represents (eval_terms terms) (reference_sum terms).
  Proof.
    apply eval_terms_from_represents.
    exact JR.identity_represents.
  Qed.

  Lemma is_identity_spec (point : J.point) (abstract : Vesta.point) :
    JR.represents point abstract ->
    J.is_identity point =
      match abstract with
      | Weierstrass.Infinity => true
      | Weierstrass.Affine _ _ => false
      end.
  Proof.
    destruct point as [px py pz], abstract as [|x y].
    - intros (Hcanonical & _ & _ & Hrepresents).
      destruct Hcanonical as (_ & _ & Hpz).
      rewrite (JR.is_identity_denote
        {| J.x := px; J.y := py; J.z := pz |} Hpz).
      apply Z.eqb_eq.
      apply JR.reduced_eqm_eq.
      + apply JR.denote_range.
      + split; [lia | exact JR.three_lt_q].
      + exact Hrepresents.
    - intros (Hcanonical & _ & _ & Hrepresents).
      destruct Hcanonical as (_ & _ & Hpz).
      rewrite (JR.is_identity_denote
        {| J.x := px; J.y := py; J.z := pz |} Hpz).
      apply Z.eqb_neq.
      intro Hz.
      destruct Hrepresents as (Hnonzero & _ & _).
      apply Hnonzero.
      rewrite Hz. reflexivity.
  Qed.

  Lemma reference_sum_from_points
      (terms : list term) (accumulator : Vesta.point) :
    reference_sum_from terms accumulator =
      List.fold_left Vesta.add (List.map contribution terms) accumulator.
  Proof.
    revert accumulator.
    induction terms as [|value terms IH]; intros accumulator;
      cbn [reference_sum_from List.fold_left List.map].
    - reflexivity.
    - apply IH.
  Qed.

  Lemma reference_sum_points (terms : list term) :
    reference_sum terms =
      Reference.point_sum (List.map contribution terms).
  Proof.
    unfold reference_sum, Reference.point_sum.
    apply reference_sum_from_points.
  Qed.

  Lemma other_terms_points (state : Reference.msm) :
    List.map contribution (other_terms state) =
      Reference.terms_points state.(Reference.other).
  Proof.
    unfold other_terms, Reference.terms_points.
    rewrite List.map_map.
    apply List.map_ext.
    intros [x scalar y]. reflexivity.
  Qed.

  Lemma optional_term_points (scalar : option Scalar.t)
      (base : Vesta.point) :
    List.map contribution (optional_term scalar base) =
      Reference.optional_point scalar base.
  Proof. destruct scalar; reflexivity. Qed.

  Lemma fixed_terms_points
      (params : Reference.parameters) (state : Reference.msm) :
    List.map contribution (fixed_terms params state) =
      Reference.terms_points state.(Reference.other) ++
      Reference.optional_point state.(Reference.w_scalar)
        params.(Reference.parameter_w) ++
      Reference.optional_point state.(Reference.u_scalar)
        params.(Reference.parameter_u).
  Proof.
    unfold fixed_terms.
    rewrite !List.map_app, other_terms_points, !optional_term_points.
    reflexivity.
  Qed.

  Lemma generator_terms_points
      (scalars : list Scalar.t) (bases : list Vesta.point) :
    List.map contribution (List.combine scalars bases) =
      List.map (fun pair => Vesta.mul (fst pair) (snd pair))
        (List.combine scalars bases).
  Proof.
    apply List.map_ext. intros [scalar base]. reflexivity.
  Qed.

  Lemma eval_terms_identity (terms : list term) :
    List.Forall term_good terms ->
    J.is_identity (eval_terms terms) =
      match Reference.point_sum (List.map contribution terms) with
      | Weierstrass.Infinity => true
      | Weierstrass.Affine _ _ => false
      end.
  Proof.
    intro Hterms.
    pose proof (eval_terms_represents terms Hterms) as Hrepresents.
    rewrite (is_identity_spec
      (eval_terms terms) (reference_sum terms) Hrepresents).
    now rewrite reference_sum_points.
  Qed.

  Theorem eval_refines (params : Reference.parameters)
      (state : Reference.msm) :
    well_formed params state ->
    eval params state = Reference.eval params state.
  Proof.
    unfold well_formed, eval, reference_terms.
    destruct state.(Reference.g_scalars) as [scalars|] eqn:Hscalars.
    - destruct (Nat.eqb (List.length scalars)
        (List.length params.(Reference.parameter_g))) eqn:Hlength.
      + intro Hterms.
        unfold Reference.eval. rewrite Hscalars, Hlength.
        f_equal.
        rewrite eval_terms_identity by exact Hterms.
        rewrite List.map_app, fixed_terms_points, generator_terms_points.
        rewrite !List.app_assoc.
        reflexivity.
      + intros _. unfold Reference.eval. now rewrite Hscalars, Hlength.
    - intro Hterms.
      unfold Reference.eval. rewrite Hscalars.
      f_equal.
      rewrite eval_terms_identity by exact Hterms.
      rewrite fixed_terms_points.
      rewrite !List.app_assoc.
      reflexivity.
  Qed.

  (** ** Refinement of the fixed 2,048-generator SRS path *)

  Lemma scalar_words_value (scalar : Scalar.t) :
    Prim63Words.eval5 (scalar_words scalar) = Scalar.canon scalar.
  Proof.
    unfold scalar_words.
    rewrite PallasPRefinement.standard_of_Z_eval.
    unfold Scalar.canon, Scalar.modulus, PallasPConfig.modulus_Z.
    rewrite Z.mod_mod by (vm_compute; discriminate).
    reflexivity.
  Qed.

  Lemma scalar_word_list_values (scalars : list Scalar.t) :
    VkMsmRefinement.scalar_values (scalar_word_list scalars) =
      List.map Scalar.canon scalars.
  Proof.
    unfold VkMsmRefinement.scalar_values, scalar_word_list.
    rewrite List.map_map.
    apply List.map_ext.
    intros scalar. apply scalar_words_value.
  Qed.

  Lemma scalar_word_list_length (scalars : list Scalar.t) :
    List.length (scalar_word_list scalars) = List.length scalars.
  Proof. unfold scalar_word_list. apply List.length_map. Qed.

  Lemma scalar_canon_range (scalar : Scalar.t) :
    0 <= Scalar.canon scalar < 2 ^ 256.
  Proof.
    assert (Hmodulus : 0 < Scalar.modulus) by
      (unfold Scalar.modulus; vm_compute; reflexivity).
    pose proof (Z.mod_pos_bound scalar Scalar.modulus Hmodulus) as Hrange.
    unfold Scalar.canon.
    split; [exact (proj1 Hrange) |].
    eapply Z.lt_trans; [exact (proj2 Hrange) |].
    unfold Scalar.modulus. vm_compute. reflexivity.
  Qed.

  Lemma scalar_word_list_range (scalars : list Scalar.t) :
    List.Forall (fun scalar => 0 <= scalar < 2 ^ 256)
      (VkMsmRefinement.scalar_values (scalar_word_list scalars)).
  Proof.
    rewrite scalar_word_list_values.
    apply List.Forall_forall.
    intros value Hvalue.
    apply List.in_map_iff in Hvalue.
    destruct Hvalue as [scalar [<- _]].
    apply scalar_canon_range.
  Qed.

  Lemma msm_scalar_canon (scalars : list Scalar.t)
      (bases : list Vesta.point) :
    List.Forall VkMsm.good bases ->
    VkMsm.msm (List.map Scalar.canon scalars) bases =
      VkMsm.msm scalars bases.
  Proof.
    revert bases.
    induction scalars as [|scalar scalars IH]; intros [|base bases] Hbases;
      cbn [List.map VkMsm.msm]; try reflexivity.
    inversion Hbases as [|? ? Hbase Htail]; subst.
    change
      (Vesta.add (Vesta.mul (Scalar.canon scalar) base)
        (VkMsm.msm (List.map Scalar.canon scalars) bases) =
       Vesta.add (Vesta.mul scalar base) (VkMsm.msm scalars bases)).
    rewrite (scalar_canon_mul scalar base Hbase).
    rewrite IH by exact Htail.
    reflexivity.
  Qed.

  Lemma term_points_good (terms : list term) :
    List.Forall term_good terms ->
    List.Forall VkMsm.good (List.map contribution terms).
  Proof.
    induction terms as [|value terms IH]; intros Hterms;
      cbn [List.map]; constructor.
    - inversion Hterms as [|? ? Hvalue _]; subst.
      unfold contribution.
      apply VkMsm.good_mul. exact Hvalue.
    - apply IH. now inversion Hterms.
  Qed.

  Lemma generator_points_good (scalars : list Scalar.t)
      (bases : list Vesta.point) :
    List.Forall VkMsm.good bases ->
    List.Forall VkMsm.good
      (List.map contribution (List.combine scalars bases)).
  Proof.
    revert bases.
    induction scalars as [|scalar scalars IH]; intros [|base bases] Hbases;
      cbn [List.combine List.map]; constructor.
    - inversion Hbases as [|? ? Hbase _]; subst.
      unfold contribution. apply VkMsm.good_mul. exact Hbase.
    - apply IH. now inversion Hbases.
  Qed.

  Lemma point_sum_from_psum (points : list Vesta.point)
      (accumulator : Vesta.point) :
    VkMsm.good accumulator ->
    List.Forall VkMsm.good points ->
    List.fold_left Vesta.add points accumulator =
      Vesta.add accumulator (VkMsm.psum points).
  Proof.
    revert accumulator.
    induction points as [|point points IH]; intros accumulator Hacc Hpoints.
    - cbn [List.fold_left VkMsm.psum].
      symmetry. apply VkMsm.vadd_0_r.
    - inversion Hpoints as [|? ? Hpoint Htail]; subst.
      cbn [List.fold_left].
      rewrite IH.
      + change
          (Vesta.add (Vesta.add accumulator point) (VkMsm.psum points) =
           Vesta.add accumulator (Vesta.add point (VkMsm.psum points))).
        apply VkMsm.vadd_assoc.
        * exact Hacc.
        * exact Hpoint.
        * now apply VkMsm.psum_good.
      + now apply VkMsm.good_add.
      + exact Htail.
  Qed.

  Lemma point_sum_psum (points : list Vesta.point) :
    List.Forall VkMsm.good points ->
    Reference.point_sum points = VkMsm.psum points.
  Proof.
    intro Hpoints.
    unfold Reference.point_sum.
    rewrite point_sum_from_psum by
      (exact VkMsm.good_identity || exact Hpoints).
    apply VkMsm.vadd_0_l.
  Qed.

  Lemma psum_app (left right : list Vesta.point) :
    List.Forall VkMsm.good left ->
    List.Forall VkMsm.good right ->
    VkMsm.psum (left ++ right) =
      Vesta.add (VkMsm.psum left) (VkMsm.psum right).
  Proof.
    revert right.
    induction left as [|point left IH]; intros right Hleft Hright.
    - cbn [List.app VkMsm.psum]. symmetry. apply VkMsm.vadd_0_l.
    - inversion Hleft as [|? ? Hpoint Htail]; subst.
      change
        (Vesta.add point (VkMsm.psum (left ++ right)) =
         Vesta.add (Vesta.add point (VkMsm.psum left))
           (VkMsm.psum right)).
      rewrite IH by assumption.
      symmetry. apply VkMsm.vadd_assoc.
      + exact Hpoint.
      + now apply VkMsm.psum_good.
      + now apply VkMsm.psum_good.
  Qed.

  Lemma generator_psum_msm (scalars : list Scalar.t)
      (bases : list Vesta.point) :
    List.length scalars = List.length bases ->
    VkMsm.psum
      (List.map contribution (List.combine scalars bases)) =
      VkMsm.msm scalars bases.
  Proof.
    revert bases.
    induction scalars as [|scalar scalars IH]; intros [|base bases] Hlength;
      cbn [List.combine List.map VkMsm.psum VkMsm.msm] in *;
      try discriminate; try reflexivity.
    change
      (Vesta.add (Vesta.mul scalar base)
        (VkMsm.psum
          (List.map contribution (List.combine scalars bases))) =
       Vesta.add (Vesta.mul scalar base) (VkMsm.msm scalars bases)).
    f_equal. apply IH. now injection Hlength.
  Qed.

  Lemma add_mul_neg_one_cancel (left right : Vesta.point) :
    VkMsm.good left ->
    VkMsm.good right ->
    Vesta.add (Vesta.add left right) (Vesta.mul (-1) right) = left.
  Proof.
    intros Hleft Hright.
    transitivity
      (Vesta.add left (Vesta.add right (Vesta.mul (-1) right))).
    - apply VkMsm.vadd_assoc.
      + exact Hleft.
      + exact Hright.
      + now apply VkMsm.good_mul.
    - transitivity (Vesta.add left Vesta.identity).
      + f_equal.
        change
          (Vesta.add (Vesta.mul 1 right) (Vesta.mul (-1) right) =
           Vesta.identity).
        transitivity (Vesta.mul (1 + -1) right).
        * symmetry. exact (VkMsm.vmul_add 1 (-1) right Hright).
        * replace (1 + -1) with 0 by ring.
          apply VkMsm.vmul_0.
      + apply VkMsm.vadd_0_r.
  Qed.

  Theorem eval_srs_g_represents (scalars : list Scalar.t) :
    List.length scalars = 2048%nat ->
    VkSrsDataView.refinement ->
    JR.represents (eval_srs_g scalars)
      (VkMsm.msm scalars VkSrsDataView.denoted_g).
  Proof.
    intros Hlength Hsrs.
    set (coefficients := scalar_word_list scalars).
    assert (Hcoefficients : List.length coefficients = 2048%nat).
    { unfold coefficients. now rewrite scalar_word_list_length. }
    assert (Hw_good : VkMsm.good VkSrsDataView.denoted_w).
    { split.
      - exact (VkSrsDataView.w_reduced Hsrs).
      - exact (VkSrsDataView.w_on_curve Hsrs). }
    pose proof (VkMsmRefinement.assemble_halves_sound coefficients
      Hcoefficients Hsrs (scalar_word_list_range scalars)) as Hassembled.
    assert (Hminus_w :
      JR.represents
        (mul (-1) (point_of_reference VkSrsDataView.denoted_w))
        (Vesta.mul (-1) VkSrsDataView.denoted_w)).
    { apply mul_represents, point_of_reference_represents. exact Hw_good. }
    unfold eval_srs_g.
    fold coefficients.
    eapply VkMsmRefinement.represents_transport.
    - apply JR.add_represents.
      + exact Hassembled.
      + exact Hminus_w.
    -
      transitivity
        (VkMsm.msm (VkMsmRefinement.scalar_values coefficients)
          VkSrsDataView.denoted_g).
      + apply add_mul_neg_one_cancel.
        * apply VkMsm.msm_good.
          exact (VkMsmRefinement.denoted_g_good Hsrs).
        * exact Hw_good.
      +
      unfold coefficients.
      rewrite scalar_word_list_values.
      apply msm_scalar_canon.
      exact (VkMsmRefinement.denoted_g_good Hsrs).
  Qed.

  Lemma reference_sum_generators (prefix : list term)
      (scalars : list Scalar.t) (bases : list Vesta.point) :
    List.Forall term_good prefix ->
    List.Forall VkMsm.good bases ->
    List.length scalars = List.length bases ->
    Vesta.add (reference_sum prefix) (VkMsm.msm scalars bases) =
      reference_sum (prefix ++ List.combine scalars bases).
  Proof.
    intros Hprefix Hbases Hlength.
    pose proof (term_points_good prefix Hprefix) as Hprefix_points.
    pose proof (generator_points_good scalars bases Hbases)
      as Hgenerator_points.
    rewrite !reference_sum_points, List.map_app.
    rewrite (point_sum_psum (List.map contribution prefix)
      Hprefix_points).
    rewrite (point_sum_psum
      (List.map contribution prefix ++
        List.map contribution (List.combine scalars bases))).
    2: { now apply List.Forall_app. }
    rewrite psum_app by assumption.
    rewrite generator_psum_msm by exact Hlength.
    reflexivity.
  Qed.

  Theorem eval_srs_success_represents (state : Reference.msm)
      (scalars : list Scalar.t) :
    List.length scalars = 2048%nat ->
    VkSrsDataView.refinement ->
    srs_well_formed state ->
    JR.represents
      (J.add (eval_terms (srs_fixed_terms state))
        (eval_srs_g scalars))
      (reference_sum
        (srs_fixed_terms state ++
          List.combine scalars VkSrsDataView.denoted_g)).
  Proof.
    intros Hlength Hsrs Hfixed.
    eapply VkMsmRefinement.represents_transport.
    - apply JR.add_represents.
      + apply eval_terms_represents. exact Hfixed.
      + apply eval_srs_g_represents; assumption.
    - apply reference_sum_generators.
      + exact Hfixed.
      + exact (VkMsmRefinement.denoted_g_good Hsrs).
      + rewrite Hlength.
        exact (eq_sym (proj2 (VkMsmRefinement.srs_lengths Hsrs))).
  Qed.

  Theorem eval_srs_refines (state : Reference.msm) :
    VkSrsDataView.refinement ->
    srs_well_formed state ->
    eval_srs state = Reference.eval srs_parameters state.
  Proof.
    intros Hsrs Hfixed.
    unfold eval_srs.
    destruct state.(Reference.g_scalars) as [scalars|] eqn:Hscalars.
    - destruct (Nat.eqb (List.length scalars) 2048) eqn:Hlength.
      + assert (Hlength_nat : List.length scalars = 2048%nat) by
          now apply Nat.eqb_eq.
        pose proof (eval_srs_success_represents state scalars
          Hlength_nat Hsrs Hfixed) as Hrepresents.
        unfold Reference.eval. rewrite Hscalars.
        assert (Hsrs_length :
          List.length srs_parameters.(Reference.parameter_g) = 2048%nat).
        { change (List.length VkSrsDataView.denoted_g = 2048%nat).
          exact (proj2 (VkMsmRefinement.srs_lengths Hsrs)). }
        destruct (Nat.eqb (List.length scalars)
          (List.length srs_parameters.(Reference.parameter_g)))
          eqn:Hparameter.
        2: { apply Nat.eqb_neq in Hparameter. exfalso.
          apply Hparameter. congruence. }
        change srs_parameters.(Reference.parameter_g) with
          VkSrsDataView.denoted_g.
        f_equal.
        rewrite (is_identity_spec _ _ Hrepresents).
        rewrite srs_fixed_terms_eq.
        rewrite reference_sum_points, List.map_app,
          fixed_terms_points, generator_terms_points.
        rewrite !List.app_assoc.
        reflexivity.
      + unfold Reference.eval. rewrite Hscalars.
        assert (Hlength_neq : List.length scalars <> 2048%nat) by
          now apply Nat.eqb_neq.
        assert (Hsrs_length :
          List.length srs_parameters.(Reference.parameter_g) = 2048%nat).
        { change (List.length VkSrsDataView.denoted_g = 2048%nat).
          exact (proj2 (VkMsmRefinement.srs_lengths Hsrs)). }
        destruct (Nat.eqb (List.length scalars)
          (List.length srs_parameters.(Reference.parameter_g)))
          eqn:Hparameter.
        * apply Nat.eqb_eq in Hparameter. exfalso.
          apply Hlength_neq. congruence.
        * reflexivity.
    - pose proof (eval_terms_represents
        (srs_fixed_terms state) Hfixed) as Hrepresents.
      unfold Reference.eval. rewrite Hscalars.
      f_equal.
      rewrite (is_identity_spec _ _ Hrepresents).
      rewrite srs_fixed_terms_eq.
      rewrite reference_sum_points, fixed_terms_points.
      rewrite !List.app_assoc.
      reflexivity.
  Qed.

  Lemma srs_parameters_eq :
    VkSrsDataView.refinement ->
    srs_parameters = reference_srs_parameters.
  Proof.
    intro Hsrs.
    unfold srs_parameters, reference_srs_parameters.
    rewrite (VkSrsDataView.g_exact Hsrs),
      (VkSrsDataView.w_exact Hsrs),
      (VkSrsDataView.u_exact Hsrs).
    reflexivity.
  Qed.

  Corollary eval_srs_refines_reference_srs (state : Reference.msm) :
    VkSrsDataView.refinement ->
    srs_well_formed state ->
    eval_srs state = Reference.eval reference_srs_parameters state.
  Proof.
    intros Hsrs Hstate.
    rewrite <- (srs_parameters_eq Hsrs).
    now apply eval_srs_refines.
  Qed.

End CommitmentEval.
