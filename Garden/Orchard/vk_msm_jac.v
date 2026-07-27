(** * The Jacobian mirror of the Pippenger MSM pipeline

    [VkMsm.msm_pippenger] ([Orchard/vk_msm.v]) is the computable
    bucket-method MSM the vk-commitment certificates [vm_compute].  Every
    one of its point additions is [Weierstrass.add], whose slope is a
    [BinOp.div] and therefore a [mod_inverse] — a bounded extended-Euclid
    loop over 255-bit [Z] division, the dominant cost of a shard.

    This file mirrors the computed path of that pipeline into Jacobian
    coordinates, where addition ([VestaJac.jadd]) is inversion-free, and
    connects the two by structural refinement: each mirrored definition
    maps [VestaJac.jrepr]-related inputs to [VestaJac.jrepr]-related
    outputs.  The bucket, aggregation and Horner mathematics is not
    restated — it is already proved on the affine side
    ([VkMsm.bucket_partition], [VkMsm.aggr_go_spec], [VkMsm.win_sum_spec],
    [VkMsm.pip_go_spec], [VkMsm.pippenger_correct]) and reached through
    the affine result that the Jacobian one represents.

    The scalar and structure producers of the pipeline
    ([VkMsm.digits32], [VkMsm.desc_from], [VkMsm.tsd]) carry no curve
    operation and are shared verbatim, so the digit and window lists are
    the same terms on both sides.

    The culminating statement is [msm_pippenger_jac_repr]: for [good]
    bases, the Jacobian checker run on the [VestaJac.jof] images of those
    bases represents the affine checker's result.  Composed with
    [VestaJac.jcheck_sound] it turns a shard certificate into an
    inversion-free computation checked against the pinned affine
    coordinates by four multiplications. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.VestaJacobian.
Require Import Garden.Orchard.vk_msm.

Import ListNotations.

Global Open Scope list_scope.
Global Open Scope Z_scope.

Module VkMsmJac.

(** ** The pinned interface at the [VkMsm] point layer

    [VkMsm.point] / [VkMsm.padd] / [VkMsm.identity] / [VkMsm.good] are the
    [Vesta] operations [VestaJac] is stated over; these three restatements
    fix the vocabulary the refinement lemmas below use. *)

Lemma jrepr_padd (J K : VestaJac.jpoint) (P Q : VkMsm.point) :
  VkMsm.good P -> VkMsm.good Q ->
  VestaJac.jrepr J P -> VestaJac.jrepr K Q ->
  VestaJac.jrepr (VestaJac.jadd J K) (VkMsm.padd P Q).
Proof.
  intros HP HQ HJ HK. apply VestaJac.jrepr_add; assumption.
Qed.

Lemma jrepr_jof (P : VkMsm.point) :
  VkMsm.good P -> VestaJac.jrepr (VestaJac.jof P) P.
Proof. intros HP. apply VestaJac.jrepr_of. assumption. Qed.

Lemma jrepr_identity : VestaJac.jrepr VestaJac.jzero VkMsm.identity.
Proof. exact VestaJac.jrepr_zero. Qed.

(** ** The mirrored computed pipeline

    One Jacobian counterpart per definition on the [vm_compute] path of
    [VkMsm.msm_pippenger], in the same order the evaluator walks them. *)

Definition psum_j (l : list VestaJac.jpoint) : VestaJac.jpoint :=
  List.fold_right VestaJac.jadd VestaJac.jzero l.

Definition bucket_j (pairs : list (Z * VestaJac.jpoint)) (vv : Z)
    : VestaJac.jpoint :=
  psum_j (List.map snd
            (List.filter (fun dg => Z.eqb (fst dg) vv) pairs)).

(** The suffix-sum aggregation of the bucket list.  The running sum is
    bound by a [let], so one addition is performed per bucket. *)
Fixpoint aggr_go_j (bs : list VestaJac.jpoint)
    (run acc : VestaJac.jpoint) : VestaJac.jpoint :=
  match bs with
  | [] => acc
  | b :: bs' =>
      let r := VestaJac.jadd run b in
      aggr_go_j bs' r (VestaJac.jadd acc r)
  end.

Definition aggr_j (bs : list VestaJac.jpoint) : VestaJac.jpoint :=
  aggr_go_j bs VestaJac.jzero VestaJac.jzero.

Definition win_pairs_j (dss : list (list Z)) (gs : list VestaJac.jpoint)
    (t : nat) : list (Z * VestaJac.jpoint) :=
  List.combine (List.map (fun ds => List.nth t ds 0) dss) gs.

Definition win_sum_j (dss : list (list Z)) (gs : list VestaJac.jpoint)
    (t : nat) : VestaJac.jpoint :=
  aggr_j (List.map (bucket_j (win_pairs_j dss gs t))
            (VkMsm.desc_from 255)).

Definition double_j (J : VestaJac.jpoint) : VestaJac.jpoint :=
  VestaJac.jadd J J.

(** The window shift [VkMsm.pmul 256] of the Horner accumulator is eight
    doublings. *)
Definition mul256_j (J : VestaJac.jpoint) : VestaJac.jpoint :=
  double_j (double_j (double_j (double_j
    (double_j (double_j (double_j (double_j J))))))).

Fixpoint pip_go_j (dss : list (list Z)) (gs : list VestaJac.jpoint)
    (ts : list nat) (acc : VestaJac.jpoint) : VestaJac.jpoint :=
  match ts with
  | [] => acc
  | t :: ts' =>
      pip_go_j dss gs ts'
        (VestaJac.jadd (mul256_j acc) (win_sum_j dss gs t))
  end.

(** The Jacobian Pippenger MSM: window 8, 32 windows MSB first, over the
    same digit lists as [VkMsm.msm_pippenger]. *)
Definition msm_pippenger_jac (cs : list Z) (gs : list VestaJac.jpoint)
    : VestaJac.jpoint :=
  pip_go_j (List.map VkMsm.digits32 cs) gs (VkMsm.tsd 32) VestaJac.jzero.

(** ** Goodness of the affine window sums

    [VestaJac.jrepr_add] carries [good] side conditions on the affine
    operands.  [VkMsm] establishes goodness for buckets
    ([VkMsm.bucket_good]) and sums ([VkMsm.psum_good]); the aggregation
    and window layers are covered here. *)

Lemma aggr_go_good (bs : list VkMsm.point) (run acc : VkMsm.point) :
  Forall VkMsm.good bs -> VkMsm.good run -> VkMsm.good acc ->
  VkMsm.good (VkMsm.aggr_go bs run acc).
Proof.
  revert run acc.
  induction bs as [| b bs IH]; intros run acc Hbs Hrun Hacc;
    cbn [VkMsm.aggr_go]; [exact Hacc |].
  apply IH.
  - exact (Forall_inv_tail Hbs).
  - apply VkMsm.good_add; [exact Hrun | exact (Forall_inv Hbs)].
  - apply VkMsm.good_add;
      [exact Hacc | apply VkMsm.good_add;
                     [exact Hrun | exact (Forall_inv Hbs)]].
Qed.

Lemma aggr_good (bs : list VkMsm.point) :
  Forall VkMsm.good bs -> VkMsm.good (VkMsm.aggr bs).
Proof.
  intros Hbs. unfold VkMsm.aggr.
  apply aggr_go_good;
    [exact Hbs | exact VkMsm.good_identity | exact VkMsm.good_identity].
Qed.

Lemma combine_snd_good (ds : list Z) (gs : list VkMsm.point) :
  Forall VkMsm.good gs ->
  Forall VkMsm.good (List.map snd (List.combine ds gs)).
Proof.
  revert gs. induction ds as [| d ds IH]; intros gs Hgs;
    [constructor |].
  destruct gs as [| g gs]; cbn [List.combine List.map]; [constructor |].
  constructor;
    [exact (Forall_inv Hgs) | apply IH; exact (Forall_inv_tail Hgs)].
Qed.

Lemma win_pairs_snd_good (dss : list (list Z)) (gs : list VkMsm.point)
    (t : nat) :
  Forall VkMsm.good gs ->
  Forall VkMsm.good (List.map snd (VkMsm.win_pairs dss gs t)).
Proof.
  intros Hgs. unfold VkMsm.win_pairs. apply combine_snd_good. exact Hgs.
Qed.

Lemma win_sum_good (dss : list (list Z)) (gs : list VkMsm.point)
    (t : nat) :
  Forall VkMsm.good gs -> VkMsm.good (VkMsm.win_sum dss gs t).
Proof.
  intros Hgs. unfold VkMsm.win_sum.
  apply aggr_good.
  apply Forall_forall. intros b Hb.
  apply in_map_iff in Hb. destruct Hb as (vv & <- & _).
  apply VkMsm.bucket_good. apply win_pairs_snd_good. exact Hgs.
Qed.

(** ** Structural refinement

    Each mirrored definition preserves [VestaJac.jrepr].  The bucket lists
    are related pairwise by [pair_repr]: the digit components are equal
    terms, the point components represent. *)

Definition pair_repr (jp : Z * VestaJac.jpoint) (p : Z * VkMsm.point)
    : Prop :=
  fst jp = fst p /\ VestaJac.jrepr (snd jp) (snd p).

Lemma psum_j_cons (j : VestaJac.jpoint) (js : list VestaJac.jpoint) :
  psum_j (j :: js) = VestaJac.jadd j (psum_j js).
Proof. reflexivity. Qed.

Lemma psum_cons (p : VkMsm.point) (ps : list VkMsm.point) :
  VkMsm.psum (p :: ps) = VkMsm.padd p (VkMsm.psum ps).
Proof. reflexivity. Qed.

Lemma psum_j_repr (js : list VestaJac.jpoint) (ps : list VkMsm.point) :
  Forall2 VestaJac.jrepr js ps ->
  Forall VkMsm.good ps ->
  VestaJac.jrepr (psum_j js) (VkMsm.psum ps).
Proof.
  induction 1 as [| j p js ps Hr H2 IH]; intros Hg.
  - exact jrepr_identity.
  - rewrite psum_j_cons, psum_cons.
    apply jrepr_padd.
    + exact (Forall_inv Hg).
    + apply VkMsm.psum_good. exact (Forall_inv_tail Hg).
    + exact Hr.
    + apply IH. exact (Forall_inv_tail Hg).
Qed.

Lemma filter_snd_repr (vv : Z) (jps : list (Z * VestaJac.jpoint))
    (ps : list (Z * VkMsm.point)) :
  Forall2 pair_repr jps ps ->
  Forall2 VestaJac.jrepr
    (List.map snd (List.filter (fun dg => Z.eqb (fst dg) vv) jps))
    (List.map snd (List.filter (fun dg => Z.eqb (fst dg) vv) ps)).
Proof.
  induction 1 as [| jp p jps ps [Hf Hs] H2 IH];
    cbn [List.filter List.map]; [constructor |].
  rewrite Hf.
  destruct (Z.eqb (fst p) vv); cbn [List.map];
    [constructor; assumption | exact IH].
Qed.

Lemma filter_snd_good (vv : Z) (ps : list (Z * VkMsm.point)) :
  Forall VkMsm.good (List.map snd ps) ->
  Forall VkMsm.good
    (List.map snd (List.filter (fun dg => Z.eqb (fst dg) vv) ps)).
Proof.
  induction ps as [| p ps IH]; intros Hg; cbn [List.filter];
    [constructor |].
  cbn [List.map] in Hg.
  destruct (Z.eqb (fst p) vv); cbn [List.map].
  - constructor;
      [exact (Forall_inv Hg) | apply IH; exact (Forall_inv_tail Hg)].
  - apply IH. exact (Forall_inv_tail Hg).
Qed.

Lemma bucket_j_repr (jps : list (Z * VestaJac.jpoint))
    (ps : list (Z * VkMsm.point)) (vv : Z) :
  Forall2 pair_repr jps ps ->
  Forall VkMsm.good (List.map snd ps) ->
  VestaJac.jrepr (bucket_j jps vv) (VkMsm.bucket ps vv).
Proof.
  intros H2 Hg. unfold bucket_j, VkMsm.bucket.
  apply psum_j_repr;
    [apply filter_snd_repr; exact H2 | apply filter_snd_good; exact Hg].
Qed.

Lemma aggr_go_j_repr (jbs : list VestaJac.jpoint)
    (bs : list VkMsm.point) :
  Forall2 VestaJac.jrepr jbs bs ->
  Forall VkMsm.good bs ->
  forall (jrun jacc : VestaJac.jpoint) (run acc : VkMsm.point),
    VkMsm.good run -> VkMsm.good acc ->
    VestaJac.jrepr jrun run -> VestaJac.jrepr jacc acc ->
    VestaJac.jrepr (aggr_go_j jbs jrun jacc) (VkMsm.aggr_go bs run acc).
Proof.
  induction 1 as [| jb b jbs bs Hr H2 IH];
    intros Hg jrun jacc run acc Hrun Hacc Hjr Hja.
  - cbn [aggr_go_j VkMsm.aggr_go]. exact Hja.
  - cbn [aggr_go_j VkMsm.aggr_go].
    apply IH.
    + exact (Forall_inv_tail Hg).
    + apply VkMsm.good_add; [exact Hrun | exact (Forall_inv Hg)].
    + apply VkMsm.good_add;
        [exact Hacc | apply VkMsm.good_add;
                       [exact Hrun | exact (Forall_inv Hg)]].
    + apply jrepr_padd;
        [exact Hrun | exact (Forall_inv Hg) | exact Hjr | exact Hr].
    + apply jrepr_padd.
      * exact Hacc.
      * apply VkMsm.good_add; [exact Hrun | exact (Forall_inv Hg)].
      * exact Hja.
      * apply jrepr_padd;
          [exact Hrun | exact (Forall_inv Hg) | exact Hjr | exact Hr].
Qed.

Lemma aggr_j_repr (jbs : list VestaJac.jpoint) (bs : list VkMsm.point) :
  Forall2 VestaJac.jrepr jbs bs ->
  Forall VkMsm.good bs ->
  VestaJac.jrepr (aggr_j jbs) (VkMsm.aggr bs).
Proof.
  intros H2 Hg. unfold aggr_j, VkMsm.aggr.
  apply (aggr_go_j_repr jbs bs H2 Hg);
    [exact VkMsm.good_identity | exact VkMsm.good_identity
     | exact jrepr_identity | exact jrepr_identity].
Qed.

Lemma Forall2_map_pointwise {A B C : Type} (f : A -> B) (g : A -> C)
    (R : B -> C -> Prop) (l : list A) :
  (forall x, R (f x) (g x)) -> Forall2 R (List.map f l) (List.map g l).
Proof.
  intros HR. induction l as [| x l IH]; cbn [List.map]; constructor;
    [apply HR | exact IH].
Qed.

Lemma combine_pair_repr (ds : list Z) (js : list VestaJac.jpoint)
    (gs : list VkMsm.point) :
  Forall2 VestaJac.jrepr js gs ->
  Forall2 pair_repr (List.combine ds js) (List.combine ds gs).
Proof.
  intros H2. revert ds.
  induction H2 as [| j g js gs Hr H2 IH]; intros ds.
  - destruct ds; cbn [List.combine]; constructor.
  - destruct ds as [| d ds]; cbn [List.combine]; [constructor |].
    constructor; [split; [reflexivity | exact Hr] | apply IH].
Qed.

Lemma win_pairs_j_repr (dss : list (list Z))
    (js : list VestaJac.jpoint) (gs : list VkMsm.point) (t : nat) :
  Forall2 VestaJac.jrepr js gs ->
  Forall2 pair_repr (win_pairs_j dss js t) (VkMsm.win_pairs dss gs t).
Proof.
  intros H2. unfold win_pairs_j, VkMsm.win_pairs.
  apply combine_pair_repr. exact H2.
Qed.

Lemma win_sum_j_repr (dss : list (list Z)) (js : list VestaJac.jpoint)
    (gs : list VkMsm.point) (t : nat) :
  Forall2 VestaJac.jrepr js gs ->
  Forall VkMsm.good gs ->
  VestaJac.jrepr (win_sum_j dss js t) (VkMsm.win_sum dss gs t).
Proof.
  intros H2 Hg. unfold win_sum_j, VkMsm.win_sum.
  apply aggr_j_repr.
  - apply Forall2_map_pointwise. intros vv.
    apply bucket_j_repr;
      [apply win_pairs_j_repr; exact H2
       | apply win_pairs_snd_good; exact Hg].
  - apply Forall_forall. intros b Hb.
    apply in_map_iff in Hb. destruct Hb as (vv & <- & _).
    apply VkMsm.bucket_good. apply win_pairs_snd_good. exact Hg.
Qed.

(** The affine window shift, as the eightfold doubling the Jacobian side
    mirrors. *)
Definition double_a (P : VkMsm.point) : VkMsm.point := VkMsm.padd P P.

Lemma pmul256_double_a (P : VkMsm.point) :
  VkMsm.pmul 256 P =
    double_a (double_a (double_a (double_a
      (double_a (double_a (double_a (double_a P))))))).
Proof. reflexivity. Qed.

Lemma double_a_good (P : VkMsm.point) :
  VkMsm.good P -> VkMsm.good (double_a P).
Proof. intros HP. apply VkMsm.good_add; exact HP. Qed.

Lemma double_j_repr (J : VestaJac.jpoint) (P : VkMsm.point) :
  VkMsm.good P -> VestaJac.jrepr J P ->
  VestaJac.jrepr (double_j J) (double_a P).
Proof. intros HP HJ. apply jrepr_padd; assumption. Qed.

Lemma mul256_j_repr (J : VestaJac.jpoint) (P : VkMsm.point) :
  VkMsm.good P -> VestaJac.jrepr J P ->
  VestaJac.jrepr (mul256_j J) (VkMsm.pmul 256 P).
Proof.
  intros HP HJ.
  rewrite pmul256_double_a. unfold mul256_j.
  do 8 (apply double_j_repr; [repeat apply double_a_good; exact HP |]).
  exact HJ.
Qed.

Lemma pip_go_j_repr (dss : list (list Z)) (js : list VestaJac.jpoint)
    (gs : list VkMsm.point) :
  Forall2 VestaJac.jrepr js gs ->
  Forall VkMsm.good gs ->
  forall (ts : list nat) (jacc : VestaJac.jpoint) (acc : VkMsm.point),
    VkMsm.good acc -> VestaJac.jrepr jacc acc ->
    VestaJac.jrepr (pip_go_j dss js ts jacc)
      (VkMsm.pip_go dss gs ts acc).
Proof.
  intros H2 Hg ts. revert dss js gs H2 Hg.
  induction ts as [| t ts IH]; intros dss js gs H2 Hg jacc acc Hacc Hja.
  - cbn [pip_go_j VkMsm.pip_go]. exact Hja.
  - cbn [pip_go_j VkMsm.pip_go].
    apply IH; [exact H2 | exact Hg | |].
    + apply VkMsm.good_add;
        [apply VkMsm.good_mul; exact Hacc | apply win_sum_good; exact Hg].
    + apply jrepr_padd.
      * apply VkMsm.good_mul. exact Hacc.
      * apply win_sum_good. exact Hg.
      * apply mul256_j_repr; assumption.
      * apply win_sum_j_repr; assumption.
Qed.

(** ** The Jacobian checker refines the affine one

    No hypothesis beyond goodness of the bases: the digit lists are the
    same terms on both sides, so the range and length conditions of
    [VkMsm.pippenger_correct] are needed only downstream of this
    refinement, where the affine result is identified with [VkMsm.msm]. *)

Theorem msm_pippenger_jac_repr_gen (cs : list Z)
    (js : list VestaJac.jpoint) (gs : list VkMsm.point) :
  Forall2 VestaJac.jrepr js gs ->
  Forall VkMsm.good gs ->
  VestaJac.jrepr (msm_pippenger_jac cs js) (VkMsm.msm_pippenger cs gs).
Proof.
  intros H2 Hg.
  unfold msm_pippenger_jac, VkMsm.msm_pippenger.
  apply pip_go_j_repr;
    [exact H2 | exact Hg | exact VkMsm.good_identity
     | exact jrepr_identity].
Qed.

Lemma jof_list_repr (gs : list VkMsm.point) :
  Forall VkMsm.good gs ->
  Forall2 VestaJac.jrepr (List.map VestaJac.jof gs) gs.
Proof.
  induction 1 as [| g gs Hg Hgs IH]; cbn [List.map]; constructor;
    [apply jrepr_jof; exact Hg | exact IH].
Qed.

Theorem msm_pippenger_jac_repr (cs : list Z) (gs : list VkMsm.point) :
  Forall VkMsm.good gs ->
  VestaJac.jrepr (msm_pippenger_jac cs (List.map VestaJac.jof gs))
    (VkMsm.msm_pippenger cs gs).
Proof.
  intros Hg.
  apply msm_pippenger_jac_repr_gen;
    [apply jof_list_repr; exact Hg | exact Hg].
Qed.

(** ** The inversion-free shard certificate

    A shard is certified by evaluating the Jacobian pipeline and checking the
    result against the pinned affine coordinates with four multiplications
    ([VestaJac.jcheck]).  Since [VkMsm.msm_pippenger] returns a reduced point
    and [VestaJac.jrepr] determines the reduced point it represents, that check
    is equivalent to the affine shard equation the certificates used to
    [vm_compute] directly. *)

Lemma pip_go_good (dss : list (list Z)) (gs : list VkMsm.point)
    (ts : list nat) (acc : VkMsm.point) :
  Forall VkMsm.good gs -> VkMsm.good acc ->
  VkMsm.good (VkMsm.pip_go dss gs ts acc).
Proof.
  revert acc. induction ts as [| t ts IH]; intros acc Hg Hacc;
    cbn [VkMsm.pip_go]; [exact Hacc |].
  apply IH; [exact Hg |].
  apply VkMsm.good_add;
    [apply VkMsm.good_mul; exact Hacc | apply win_sum_good; exact Hg].
Qed.

Lemma msm_pippenger_good (cs : list Z) (gs : list VkMsm.point) :
  Forall VkMsm.good gs -> VkMsm.good (VkMsm.msm_pippenger cs gs).
Proof.
  intros Hg. unfold VkMsm.msm_pippenger.
  apply pip_go_good; [exact Hg | exact VkMsm.good_identity].
Qed.

Theorem jshard_sound (cs : list Z) (gs : list VkMsm.point) (x y : Z) :
  Forall VkMsm.good gs ->
  VestaJac.jcheck (msm_pippenger_jac cs (List.map VestaJac.jof gs)) (x, y)
  = true ->
  VkMsm.msm_pippenger cs gs = Vesta.affine x y.
Proof.
  intros Hg Hchk.
  apply (VestaJac.jrepr_pin (msm_pippenger_jac cs (List.map VestaJac.jof gs)));
    [ exact (proj1 (msm_pippenger_good cs gs Hg))
    | apply msm_pippenger_jac_repr; exact Hg
    | exact Hchk ].
Qed.

(** The Jacobian analogue of [VkMsm.commit_two_shards]: the two heavy
    half-range checkpoints are inversion-free [VestaJac.jcheck] evaluations
    against the pinned coordinate pairs, and the remaining four hypotheses are
    the affine theorem's own — the 2048-row length of the Lagrange column, the
    range scan, the [VkMsm.intt] coefficient identity, and the
    blind-and-compare step carrying [Blind::default() = 1]. *)
Theorem commit_two_shards_jac (v c : list Z) (cpa cpb : Z * Z)
    (px py : Z) :
  List.length v = 2048%nat ->
  List.forallb (fun s => (0 <=? s) && (s <? VkMsm.scalar_p)) v = true ->
  VkMsm.intt v = c ->
  VestaJac.jcheck
    (msm_pippenger_jac (List.firstn 1024 c)
       (List.map VestaJac.jof (List.firstn 1024 VkMsm.g_points))) cpa
  = true ->
  VestaJac.jcheck
    (msm_pippenger_jac (List.skipn 1024 c)
       (List.map VestaJac.jof (List.skipn 1024 VkMsm.g_points))) cpb
  = true ->
  VkMsm.padd
    (VkMsm.padd (Vesta.affine (fst cpa) (snd cpa))
       (Vesta.affine (fst cpb) (snd cpb)))
    VkMsm.w_point
  = Weierstrass.Affine px py ->
  VkMsm.commit_lagrange v = Weierstrass.Affine px py.
Proof.
  destruct cpa as [xa ya]. destruct cpb as [xb yb]. cbn [fst snd].
  intros Hlen Hrange Hc Ha Hb Hfinal.
  exact (VkMsm.commit_two_shards v c
           (Vesta.affine xa ya) (Vesta.affine xb yb) px py
           Hlen Hrange Hc
           (jshard_sound (List.firstn 1024 c)
              (List.firstn 1024 VkMsm.g_points) xa ya
              (VkMsm.Forall_firstn VkMsm.good 1024 VkMsm.g_points
                 VkMsm.g_points_good) Ha)
           (jshard_sound (List.skipn 1024 c)
              (List.skipn 1024 VkMsm.g_points) xb yb
              (VkMsm.Forall_skipn VkMsm.good 1024 VkMsm.g_points
                 VkMsm.g_points_good) Hb)
           Hfinal).
Qed.

End VkMsmJac.
