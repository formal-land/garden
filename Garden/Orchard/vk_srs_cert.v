(** * The certified Halo2 Vesta SRS: assembly of the shard certificates

    The whole-SRS statement over the sixteen shard checkers
    ([Orchard/vk_srs_cert_0.v] … [Orchard/vk_srs_cert_15.v]) and the pasted
    literal tables ([Orchard/vk_srs_data.v]): every entry of
    [VkSrsData.g_points] is, at its position [i], the output of the
    [GroupHashVesta] pipeline at the SRS message [[0x00, le32(i)]] under a
    validated [sqrt_ratio] witness quadruple ([GroupHashVesta.witnesses_ok]
    pins each witness to the [sqrt_ratio] output — [λ_V] is a nonsquare — so
    the witnessed pipeline computes the point [hash_to_curve] specifies), and
    [VkSrsData.w_point] is likewise the blind generator
    [hash_to_curve("Halo2-Parameters")([0x01])].  This is exactly the SRS of
    [Params::<vesta::Affine>::new(11)]
    ([halo2_proofs/src/poly/commitment.rs]).

    Each shard contributes its raw-[forallb] checker (witness validation
    plus in-kernel recomputation of BLAKE2b-512 XMD, the witnessed SSWU
    maps, the iso-curve addition, and [SswuVesta.iso_map], per entry).  The
    only computations in this file are the index scan, the length checks,
    the per-point on-curve/reducedness scan, and the single-point [w]
    certificate; the glue is list plumbing. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.group_hash.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Orchard.vk_srs_entry.
Require Import Garden.Orchard.vk_srs_data.
Require Import Garden.Orchard.vk_srs_cert_0.
Require Import Garden.Orchard.vk_srs_cert_1.
Require Import Garden.Orchard.vk_srs_cert_2.
Require Import Garden.Orchard.vk_srs_cert_3.
Require Import Garden.Orchard.vk_srs_cert_4.
Require Import Garden.Orchard.vk_srs_cert_5.
Require Import Garden.Orchard.vk_srs_cert_6.
Require Import Garden.Orchard.vk_srs_cert_7.
Require Import Garden.Orchard.vk_srs_cert_8.
Require Import Garden.Orchard.vk_srs_cert_9.
Require Import Garden.Orchard.vk_srs_cert_10.
Require Import Garden.Orchard.vk_srs_cert_11.
Require Import Garden.Orchard.vk_srs_cert_12.
Require Import Garden.Orchard.vk_srs_cert_13.
Require Import Garden.Orchard.vk_srs_cert_14.
Require Import Garden.Orchard.vk_srs_cert_15.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module VkSrsCert.
  (** Provenance of one SRS point: some checked witness quadruple makes the
      witnessed [GroupHashVesta] pipeline at [msg] output exactly [xy]. *)
  Definition srs_point_ok (msg : list Z) (xy : Z * Z) : Prop :=
    exists (was_square0 : bool) (root0 : Z) (was_square1 : bool) (root1 : Z),
      GroupHashVesta.witnesses_ok GroupHashVesta.halo2_parameters_prefix
        msg was_square0 root0 was_square1 root1 = true /\
      GroupHashVesta.group_hash_with_witness
        GroupHashVesta.halo2_parameters_prefix
        msg was_square0 root0 was_square1 root1
      = Weierstrass.Affine (fst xy) (snd xy).

  (** The per-entry reading of a table entry: its own witnesses derive its
      own point at its own index's SRS message. *)
  Definition entry_ok (e : VkSrsEntry.t) : Prop :=
    srs_point_ok
      (GroupHashVesta.srs_message (VkSrsEntry.index e))
      (VkSrsEntry.point e).

  (** The shard files' per-entry checker, named. *)
  Definition entry_check (e : VkSrsEntry.t) : bool :=
    let '(i, was_square0, root0, was_square1, root1, x, y) := e in
    GroupHashVesta.witnesses_ok GroupHashVesta.halo2_parameters_prefix
      (GroupHashVesta.srs_message i) was_square0 root0 was_square1 root1
      && GroupHash.point_eqb
           (GroupHashVesta.group_hash_with_witness
             GroupHashVesta.halo2_parameters_prefix
             (GroupHashVesta.srs_message i)
             was_square0 root0 was_square1 root1)
           (Weierstrass.Affine x y).

  Lemma entry_check_ok (e : VkSrsEntry.t) :
    entry_check e = true -> entry_ok e.
  Proof.
    destruct e as [[[[[[i ws0] r0] ws1] r1] x] y].
    intros Hc.
    cbv beta iota delta [entry_check] in Hc.
    apply andb_prop in Hc. destruct Hc as [Hw Hp].
    apply GroupHash.point_eqb_eq in Hp.
    cbv beta iota delta
      [entry_ok srs_point_ok VkSrsEntry.index VkSrsEntry.point fst snd].
    exists ws0, r0, ws1, r1.
    split; [exact Hw | exact Hp].
  Qed.

  Lemma shard_forall (l : list VkSrsEntry.t) :
    List.forallb entry_check l = true -> Forall entry_ok l.
  Proof.
    intros Hall. apply Forall_forall. intros e He.
    apply entry_check_ok.
    exact (proj1 (List.forallb_forall entry_check l) Hall e He).
  Qed.

  (** ** The assembled table facts *)

  (** Every entry of the assembled table passes its own derivation. *)
  Theorem vk_srs_entries_ok : Forall entry_ok VkSrsData.g_entries.
  Proof.
    unfold VkSrsData.g_entries.
    rewrite !Forall_app.
    repeat split; apply shard_forall.
    - exact vk_srs_shard_0_check.
    - exact vk_srs_shard_1_check.
    - exact vk_srs_shard_2_check.
    - exact vk_srs_shard_3_check.
    - exact vk_srs_shard_4_check.
    - exact vk_srs_shard_5_check.
    - exact vk_srs_shard_6_check.
    - exact vk_srs_shard_7_check.
    - exact vk_srs_shard_8_check.
    - exact vk_srs_shard_9_check.
    - exact vk_srs_shard_10_check.
    - exact vk_srs_shard_11_check.
    - exact vk_srs_shard_12_check.
    - exact vk_srs_shard_13_check.
    - exact vk_srs_shard_14_check.
    - exact vk_srs_shard_15_check.
  Qed.

  (** The table indices are exactly [0 .. 2047], in order. *)
  Theorem vk_srs_indices :
    List.map VkSrsEntry.index VkSrsData.g_entries
    = List.map Z.of_nat (List.seq 0 2048).
  Proof. vm_compute; reflexivity. Qed.

  Theorem vk_srs_g_points_length :
    List.length VkSrsData.g_points = 2048%nat.
  Proof. vm_compute; reflexivity. Qed.

  Lemma Forall2_map_map {A B C : Type}
      (f : A -> B) (g : A -> C) (P : B -> C -> Prop) (l : list A) :
    Forall (fun e => P (f e) (g e)) l ->
    Forall2 P (List.map f l) (List.map g l).
  Proof. induction 1; cbn; constructor; assumption. Qed.

  (** ** The headline statement: the certified generator list

      Position by position — the point at position [i] of
      [VkSrsData.g_points] is [hash_to_curve("Halo2-Parameters")] of the
      5-byte message [[0x00, le32(i)]], through a validated witness
      quadruple. *)
  Theorem vk_srs_g_points_ok :
    Forall2
      (fun i xy => srs_point_ok (GroupHashVesta.srs_message i) xy)
      (List.map Z.of_nat (List.seq 0 2048))
      VkSrsData.g_points.
  Proof.
    rewrite <- vk_srs_indices.
    unfold VkSrsData.g_points.
    apply Forall2_map_map.
    exact vk_srs_entries_ok.
  Qed.

  (** ** The blind generator [w] *)

  Lemma vk_srs_w_cert :
    (let '(was_square0, root0, was_square1, root1, x, y) :=
       VkSrsData.w_entry in
     GroupHashVesta.witnesses_ok GroupHashVesta.halo2_parameters_prefix
       GroupHashVesta.w_message was_square0 root0 was_square1 root1
       && GroupHash.point_eqb
            (GroupHashVesta.group_hash_with_witness
              GroupHashVesta.halo2_parameters_prefix GroupHashVesta.w_message
              was_square0 root0 was_square1 root1)
            (Weierstrass.Affine x y))
    = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Theorem vk_srs_w_ok :
    srs_point_ok GroupHashVesta.w_message VkSrsData.w_point.
  Proof.
    pose proof vk_srs_w_cert as Hc.
    cbv beta iota delta [srs_point_ok VkSrsData.w_point].
    revert Hc.
    destruct VkSrsData.w_entry as [[[[[ws0 r0] ws1] r1] x] y].
    intros Hc.
    apply andb_prop in Hc. destruct Hc as [Hw Hp].
    apply GroupHash.point_eqb_eq in Hp.
    exists ws0, r0, ws1, r1.
    split; [exact Hw | exact Hp].
  Qed.

  (** ** Point validity: on-curve and reduced

      Per-point boolean check, mirroring [Vesta.on_curve] / [Vesta.reduced]
      term for term so the propositional transfer is definitional. *)
  Definition point_valid_b (xy : Z * Z) : bool :=
    let '(x, y) := xy in
    (UnOp.from (y *F y)
       =? UnOp.from (x *F x *F x +F Vesta.a *F x +F Vesta.b))
      && (UnOp.from x =? x) && (UnOp.from y =? y).

  Lemma point_valid_b_ok (xy : Z * Z) :
    point_valid_b xy = true ->
    Vesta.on_curve (Weierstrass.Affine (fst xy) (snd xy)) /\
    Vesta.reduced (Weierstrass.Affine (fst xy) (snd xy)).
  Proof.
    destruct xy as [x y]. intros Hb.
    cbv beta iota delta [point_valid_b] in Hb.
    apply andb_prop in Hb. destruct Hb as [Hb Hy].
    apply andb_prop in Hb. destruct Hb as [Hc Hx].
    apply Z.eqb_eq in Hc. apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy.
    cbv beta iota delta
      [Vesta.on_curve Vesta.reduced Weierstrass.on_curve Weierstrass.reduced
       fst snd].
    auto.
  Qed.

  Lemma vk_srs_points_valid_cert :
    List.forallb point_valid_b
      (VkSrsData.g_points ++ [VkSrsData.w_point]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** All 2049 SRS points are on the Vesta curve with reduced
      coordinates. *)
  Theorem vk_srs_points_valid :
    Forall
      (fun xy =>
        Vesta.on_curve (Weierstrass.Affine (fst xy) (snd xy)) /\
        Vesta.reduced (Weierstrass.Affine (fst xy) (snd xy)))
      (VkSrsData.g_points ++ [VkSrsData.w_point]).
  Proof.
    pose proof vk_srs_points_valid_cert as Hall.
    apply Forall_forall. intros xy Hin.
    apply point_valid_b_ok.
    exact (proj1 (List.forallb_forall point_valid_b _) Hall xy Hin).
  Qed.
End VkSrsCert.
