(** * MSM commitment certificate, fixed column 0, bases [0 .. 1023]

    The half-range Pippenger checkpoint of the [intt]-coefficient MSM of
    the compiled fixed column 0 over the certified Vesta SRS generators:
    one heavy [vm_compute] evaluating [VkMsm.msm_pippenger] (32 windows of
    8 bits, digit buckets, suffix-sum aggregation) on 1024 bases against
    the pasted checkpoint literal.  Consumed, together with the
    [vk_msm_calibrate_b.v] half, by the assembly in
    [Orchard/vk_msm_calibrate.v] through [VkMsm.commit_two_shards]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk_msm_data_fixed0.

Import ListNotations.

Global Open Scope Z_scope.

Lemma vk_msm_fixed0_shard_a :
  VkMsm.msm_pippenger (List.firstn 1024 VkMsmDataFixed0.c)
    (List.firstn 1024 VkMsm.g_points)
  = VkMsm.aff VkMsmDataFixed0.cpa.
Proof.
  vm_cast_no_check
    (@eq_refl VkMsm.point (VkMsm.aff VkMsmDataFixed0.cpa)).
Qed.
