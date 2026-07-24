(** * MSM commitment certificate, fixed column 0, bases [1024 .. 2047]

    The second half-range Pippenger checkpoint; see
    [Orchard/vk_msm_calibrate_a.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk_msm_data_fixed0.

Import ListNotations.

Global Open Scope Z_scope.

Lemma vk_msm_fixed0_shard_b :
  VkMsm.msm_pippenger (List.skipn 1024 VkMsmDataFixed0.c)
    (List.skipn 1024 VkMsm.g_points)
  = VkMsm.aff VkMsmDataFixed0.cpb.
Proof.
  vm_cast_no_check
    (@eq_refl VkMsm.point (VkMsm.aff VkMsmDataFixed0.cpb)).
Qed.
