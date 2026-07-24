(** * Vesta SRS provenance, shard 5: generators [g_640 .. g_767]

    In-kernel derivation of 128 generators of the Halo2 Vesta SRS
    ([Params::<vesta::Affine>::new(11)], [halo2_proofs/src/poly/commitment.rs]):
    for each index [i], [g_i = hash_to_curve("Halo2-Parameters")(m_i)] with
    [m_i] the 5 bytes [0x00, le32(i)], via the pipeline of
    [GroupHash/group_hash_vesta.v].  The two [sqrt_ratio] outputs per entry
    are pasted untrusted witnesses from
    [scripts/generate_vk_srs_witnesses.py], validated by
    [GroupHashVesta.witnesses_ok] (one squaring and one multiplication per
    root); the BLAKE2b-512 XMD expansion, the witnessed SSWU maps, the
    iso-curve addition, and [SswuVesta.iso_map] are recomputed by the
    checker's [vm_compute].  The index lemma pins this shard's entries to the
    contiguous index range, for the whole-SRS statement in
    [Orchard/vk_srs_cert.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.GroupHash.group_hash.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Orchard.vk_srs_entry.
Require Import Garden.Orchard.vk_srs_data_5.

Import ListNotations.

Global Open Scope Z_scope.

(** The entry indices are exactly [640 .. 767], in order. *)
Lemma vk_srs_shard_5_indices :
  List.map VkSrsEntry.index VkSrsData5.shard
  = List.map (fun n : nat => 640 + Z.of_nat n) (List.seq 0 128).
Proof. vm_compute; reflexivity. Qed.

(** Per entry: the pasted witnesses satisfy the [sqrt_ratio] defining
    equations at the two [hash_to_field] outputs for [m_i], and the witnessed
    [GroupHashVesta] recomputation equals the pasted generator. *)
Lemma vk_srs_shard_5_check :
  List.forallb
    (fun e : VkSrsEntry.t =>
      let '(i, was_square0, root0, was_square1, root1, x, y) := e in
      GroupHashVesta.witnesses_ok GroupHashVesta.halo2_parameters_prefix
        (GroupHashVesta.srs_message i) was_square0 root0 was_square1 root1
        && GroupHash.point_eqb
             (GroupHashVesta.group_hash_with_witness
               GroupHashVesta.halo2_parameters_prefix
               (GroupHashVesta.srs_message i)
               was_square0 root0 was_square1 root1)
             (Weierstrass.Affine x y))
    VkSrsData5.shard
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
