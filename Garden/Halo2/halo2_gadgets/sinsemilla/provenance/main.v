(** * Provenance of the Sinsemilla [S] table: [GroupHash^P], all 1024 entries

    The whole-table statement over the eight shard checkers
    ([provenance/shard_0.v] … [provenance/shard_7.v]): for every index
    [j ∈ [0, 1024)] there is a validated [sqrt_ratio] witness quadruple
    ([GroupHash.witnesses_ok], which pins each witness to the [sqrt_ratio]
    output — [λ_P] is a nonsquare — so the witnessed pipeline computes the
    point [GroupHash^P] specifies) under which the [GroupHash^P] pipeline of
    [GroupHash/group_hash.v] at
    [("z.cash:SinsemillaS", I2LEOSP_32(j))] (protocol §5.4.1.9) outputs
    exactly the table entry [(sinsemilla_s.x j, sinsemilla_s.y j)] of
    [Halo2/halo2_gadgets/sinsemilla/sinsemilla_s.v].

    Each shard contributes two facts: its raw-[forallb] checker (witness
    validation plus in-kernel recomputation of BLAKE2b-512 XMD, the
    witnessed SSWU maps, the iso-curve addition, and [iso_map], per entry)
    and its index lemma (its entries carry exactly one contiguous 128-index
    slice).  The glue below turns membership in a shard into the per-index
    existential; no heavy computation runs in this file. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu.
Require Import Garden.GroupHash.group_hash.
Require Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_0.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_1.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_2.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_3.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_4.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_5.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_6.
Require Garden.Halo2.halo2_gadgets.sinsemilla.provenance.shard_7.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

(** A shard's index lemma covers its 128-index range: every [j] in the range
    is the first component of one of its entries. *)
Lemma range_covered
    (entries : list (Z * bool * Z * bool * Z)) (lo : Z) :
  List.map
    (fun e : Z * bool * Z * bool * Z => let '(j, _, _, _, _) := e in j)
    entries
  = List.map (fun n : nat => lo + Z.of_nat n) (List.seq 0 128) ->
  forall j : Z, lo <= j < lo + 128 ->
  exists e, In e entries /\ (let '(j0, _, _, _, _) := e in j0) = j.
Proof.
  intros Hidx j Hj.
  assert (Hin : In j
    (List.map
      (fun e : Z * bool * Z * bool * Z => let '(j0, _, _, _, _) := e in j0)
      entries)).
  { rewrite Hidx. apply in_map_iff.
    exists (Z.to_nat (j - lo)). split; [lia|].
    apply in_seq. lia. }
  apply in_map_iff in Hin as [e [He Hine]].
  eauto.
Qed.

(** From a shard's checker and index lemma: every index in the shard's range
    admits a witness quadruple passing the shard's per-entry check. *)
Lemma shard_entry
    (check : Z * bool * Z * bool * Z -> bool)
    (entries : list (Z * bool * Z * bool * Z)) (lo : Z) :
  List.forallb check entries = true ->
  List.map
    (fun e : Z * bool * Z * bool * Z => let '(j, _, _, _, _) := e in j)
    entries
  = List.map (fun n : nat => lo + Z.of_nat n) (List.seq 0 128) ->
  forall j : Z, lo <= j < lo + 128 ->
  exists (was_square0 : bool) (root0 : Z) (was_square1 : bool) (root1 : Z),
    check (j, was_square0, root0, was_square1, root1) = true.
Proof.
  intros Hcheck Hidx j Hj.
  destruct (range_covered entries lo Hidx j Hj) as [e [Hin Hj0]].
  destruct e as [[[[j0 ws0] r0] ws1] r1].
  cbn in Hj0. subst j0.
  exists ws0, r0, ws1, r1.
  eapply forallb_forall in Hcheck; [exact Hcheck | exact Hin].
Qed.

(** Discharges the goal for the shard whose checker and index lemmas are
    [chk] and [idx], given a range hypothesis on [j] provable by [lia]. *)
Ltac from_shard chk idx j :=
  let ws0 := fresh "ws0" in let r0 := fresh "r0" in
  let ws1 := fresh "ws1" in let r1 := fresh "r1" in
  let HC := fresh "HC" in let Hw := fresh "Hw" in let He := fresh "He" in
  destruct (shard_entry _ _ _ chk idx j ltac:(lia))
    as (ws0 & r0 & ws1 & r1 & HC);
  cbv beta iota zeta in HC;
  apply andb_prop in HC; destruct HC as [Hw He];
  apply GroupHash.point_eqb_eq in He;
  exists ws0, r0, ws1, r1;
  split; [exact Hw|];
  unfold sinsemilla_s.x, sinsemilla_s.y;
  exact He.

(** Every entry of the Sinsemilla [S] table is the [GroupHash^P] output the
    protocol specifies for its index (§5.4.1.9): witnessed derivation, with
    the witness quadruple validated against the [sqrt_ratio] defining
    equations.  The message [[j mod 256; …]] is [I2LEOSP_32(j)]. *)
Theorem sinsemilla_s_group_hash_provenance :
  forall j : Z, 0 <= j < 1024 ->
  exists (was_square0 : bool) (root0 : Z) (was_square1 : bool) (root1 : Z),
    GroupHash.witnesses_ok
      (Xmd.bytes_of_string "z.cash:SinsemillaS"%string)
      [j mod 256; j / 256 mod 256; j / 65536 mod 256; j / 16777216 mod 256]
      was_square0 root0 was_square1 root1 = true /\
    GroupHash.group_hash_with_witness
      (Xmd.bytes_of_string "z.cash:SinsemillaS"%string)
      [j mod 256; j / 256 mod 256; j / 65536 mod 256; j / 16777216 mod 256]
      was_square0 root0 was_square1 root1
    = Weierstrass.Affine (sinsemilla_s.x j) (sinsemilla_s.y j).
Proof.
  intros j Hj.
  assert (Hband :
    0 <= j < 128 \/ 128 <= j < 256 \/ 256 <= j < 384 \/ 384 <= j < 512 \/
    512 <= j < 640 \/ 640 <= j < 768 \/ 768 <= j < 896 \/ 896 <= j < 1024)
    by lia.
  clear Hj.
  destruct Hband as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
  - from_shard
      shard_0.sinsemilla_s_shard_0_check shard_0.sinsemilla_s_shard_0_indices j.
  - from_shard
      shard_1.sinsemilla_s_shard_1_check shard_1.sinsemilla_s_shard_1_indices j.
  - from_shard
      shard_2.sinsemilla_s_shard_2_check shard_2.sinsemilla_s_shard_2_indices j.
  - from_shard
      shard_3.sinsemilla_s_shard_3_check shard_3.sinsemilla_s_shard_3_indices j.
  - from_shard
      shard_4.sinsemilla_s_shard_4_check shard_4.sinsemilla_s_shard_4_indices j.
  - from_shard
      shard_5.sinsemilla_s_shard_5_check shard_5.sinsemilla_s_shard_5_indices j.
  - from_shard
      shard_6.sinsemilla_s_shard_6_check shard_6.sinsemilla_s_shard_6_indices j.
  - from_shard
      shard_7.sinsemilla_s_shard_7_check shard_7.sinsemilla_s_shard_7_indices j.
Qed.
