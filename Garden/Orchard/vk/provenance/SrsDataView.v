(** * Aggregate executable view of the generated Orchard SRS

    The generic checker in [Srs] intentionally does not import this module:
    an individual provenance certificate can load one 64-entry shard instead
    of retaining all 2,048 generated entries.  Commitment computation is the
    consumer that needs the aggregate [g_array]. *)

From Corelib Require Import PrimArray.
From Stdlib Require Import ZArith Lists.List Bool.Bool.
Require Import Garden.Prim63.Pasta.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.
Require Import Garden.Orchard.vk.provenance.Srs.
Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinatesAll.

Local Open Scope Z_scope.

Module VkSrsDataView.
  Import ListNotations.
  Import VkProvenanceDataTypes.

  Definition affine_of_words (coordinates : affine_words)
      : VkJacobian.affine :=
    {| VkJacobian.affine_x := coordinates.(x_words);
       VkJacobian.affine_y := coordinates.(y_words) |}.

  Definition g : list VkJacobian.affine :=
    List.map affine_of_words VkSrsCoordinatesAll.g.
  Definition w : VkJacobian.affine :=
    affine_of_words VkSrsCoordinatesAll.w.
  Definition u : VkJacobian.affine :=
    affine_of_words VkSrsCoordinatesAll.u.

  Definition g_array : PrimArray.array VkJacobian.affine :=
    VkJacobian.array_of_list
      {| VkJacobian.affine_x := PallasQ.zero;
         VkJacobian.affine_y := PallasQ.zero |}
      g.

  (** Mathematical meaning of the primitive affine representation.  This
      deliberately lives outside [VkJacobian]: the executable MSM does not
      need to import the abstract group development. *)
  Definition denote_affine (point : VkJacobian.affine) : Vesta.point :=
    Vesta.affine
      (PallasQ.to_Z point.(VkJacobian.affine_x))
      (PallasQ.to_Z point.(VkJacobian.affine_y)).

  Definition denoted_g : list Vesta.point := List.map denote_affine g.
  Definition denoted_w : Vesta.point := denote_affine w.
  Definition denoted_u : Vesta.point := denote_affine u.

  Definition affine_normalized (point : VkJacobian.affine) : Prop :=
    point.(VkJacobian.affine_x) = PallasQ.from_Z
      (PallasQ.to_Z point.(VkJacobian.affine_x)) /\
    point.(VkJacobian.affine_y) = PallasQ.from_Z
      (PallasQ.to_Z point.(VkJacobian.affine_y)).

  Lemma denote_affine_of_words (coordinates : affine_words) :
    denote_affine (affine_of_words coordinates) =
      VkSrs.expected_point coordinates.
  Proof. reflexivity. Qed.

  Lemma denoted_g_is_coordinate_points :
    denoted_g = VkSrs.coordinate_points VkSrsCoordinatesAll.g.
  Proof.
    unfold denoted_g, g, VkSrs.coordinate_points.
    induction VkSrsCoordinatesAll.g as [|coordinate coordinates IH];
      cbn [List.map]; [reflexivity |].
    now rewrite denote_affine_of_words, IH.
  Qed.

  (** The exact semantic boundary exported by the coordinate-only SRS view.
      The generated shard certificates below discharge this record without
      making the executable MSM leaves import all 2,048 hash witnesses. *)
  Record refinement : Prop := {
    g_exact :
      denoted_g = VkSrs.hash_points_from 0 2048;
    w_exact :
      denoted_w =
        GroupHashVesta.group_hash VkSrs.domain_prefix [1];
    u_exact :
      denoted_u =
        GroupHashVesta.group_hash VkSrs.domain_prefix [2];
    g_reduced : List.Forall Vesta.reduced denoted_g;
    g_on_curve : List.Forall Vesta.on_curve denoted_g;
    w_reduced : Vesta.reduced denoted_w;
    w_on_curve : Vesta.on_curve denoted_w;
    u_reduced : Vesta.reduced denoted_u;
    u_on_curve : Vesta.on_curve denoted_u;
    g_normalized : List.Forall affine_normalized g;
    w_normalized : affine_normalized w;
    u_normalized : affine_normalized u
  }.

  Theorem refinement_from_checks
      (entries : list srs_entry) (w_entry u_entry : srs_entry) :
    VkSrs.g_entries_refine_from 0 entries VkSrsCoordinatesAll.g ->
    List.length VkSrsCoordinatesAll.g = 2048%nat ->
    VkSrs.extra_entries_refinement w_entry u_entry
      VkSrsCoordinatesAll.w VkSrsCoordinatesAll.u ->
    refinement.
  Proof.
    intros Hg Hlength Hextra.
    pose proof (VkSrs.g_entries_refine_from_hashes
      0 entries VkSrsCoordinatesAll.g Hg) as Hg_exact.
    pose proof (VkSrs.g_entries_refine_from_reduced
      0 entries VkSrsCoordinatesAll.g Hg) as Hg_reduced.
    pose proof (VkSrs.g_entries_refine_from_on_curve
      0 entries VkSrsCoordinatesAll.g Hg) as Hg_on_curve.
    pose proof (VkSrs.g_entries_refine_from_normalized
      0 entries VkSrsCoordinatesAll.g Hg) as Hg_normalized.
    destruct Hextra as [Hw Hu].
    destruct Hw as
      [_ _ Hw_exact Hw_on_curve Hw_reduced Hw_normalized].
    destruct Hu as
      [_ _ Hu_exact Hu_on_curve Hu_reduced Hu_normalized].
    constructor.
    - rewrite denoted_g_is_coordinate_points, Hg_exact, Hlength.
      reflexivity.
    - unfold denoted_w, w.
      rewrite denote_affine_of_words. symmetry. exact Hw_exact.
    - unfold denoted_u, u.
      rewrite denote_affine_of_words. symmetry. exact Hu_exact.
    - now rewrite denoted_g_is_coordinate_points.
    - now rewrite denoted_g_is_coordinate_points.
    - unfold denoted_w, w. now rewrite denote_affine_of_words.
    - unfold denoted_w, w. now rewrite denote_affine_of_words.
    - unfold denoted_u, u. now rewrite denote_affine_of_words.
    - unfold denoted_u, u. now rewrite denote_affine_of_words.
    - unfold g.
      apply List.Forall_forall.
      intros point Hpoint.
      apply List.in_map_iff in Hpoint.
      destruct Hpoint as [coordinate [<- Hcoordinate]].
      apply (proj1
        (List.Forall_forall VkSrs.affine_words_normalized
          VkSrsCoordinatesAll.g) Hg_normalized coordinate Hcoordinate).
    - exact Hw_normalized.
    - exact Hu_normalized.
  Qed.

  (** A lightweight spelling of the part of Halo2's parameter invariant used
      by the commitment proof.  [VkSrsCertificate.params_well_formed] below
      identifies this definition with [VkMsm.params_well_formed]. *)
  Definition params_well_formed : Prop :=
    List.Forall
      (fun point => Vesta.reduced point /\ Vesta.on_curve point)
      (VkSrs.hash_points_from 0 2048)
    /\ (Vesta.reduced
          (GroupHashVesta.group_hash VkSrs.domain_prefix [1])
        /\ Vesta.on_curve
          (GroupHashVesta.group_hash VkSrs.domain_prefix [1])).

  Theorem refinement_params_well_formed :
    refinement -> params_well_formed.
  Proof.
    intros Hrefinement.
    destruct Hrefinement as
      [Hg_exact Hw_exact _ Hg_reduced Hg_on_curve
       Hw_reduced Hw_on_curve _ _ _ _ _].
    split.
    - rewrite <- Hg_exact.
      apply List.Forall_forall. intros point Hpoint.
      split.
      + exact (proj1 (List.Forall_forall Vesta.reduced denoted_g)
          Hg_reduced point Hpoint).
      + exact (proj1 (List.Forall_forall Vesta.on_curve denoted_g)
          Hg_on_curve point Hpoint).
    - rewrite <- Hw_exact. split; assumption.
  Qed.
End VkSrsDataView.
