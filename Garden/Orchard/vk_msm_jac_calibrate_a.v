(** * Inversion-free MSM commitment certificate, fixed column 0, bases
      [0 .. 1023]

    The half-range Pippenger checkpoint of the [intt]-coefficient MSM of the
    compiled fixed column 0, evaluated through the Jacobian mirror
    ([VkMsmJac.msm_pippenger_jac]) and checked against the pinned checkpoint
    literal by [VestaJac.jcheck] — four multiplications, no normalisation and
    no modular inversion anywhere on the computed path.  Consumed, together
    with the [vk_msm_jac_calibrate_b.v] half, by the assembly in
    [Orchard/vk_msm_jac_calibrate.v] through
    [VkMsmJac.commit_two_shards_jac]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.VestaJacobian.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk_msm_jac.
Require Import Garden.Orchard.vk_msm_data_fixed0.

Import ListNotations.

Global Open Scope Z_scope.

Lemma vk_msm_fixed0_shard_a_jac :
  VestaJac.jcheck
    (VkMsmJac.msm_pippenger_jac (List.firstn 1024 VkMsmDataFixed0.c)
       (List.map VestaJac.jof (List.firstn 1024 VkMsm.g_points)))
    VkMsmDataFixed0.cpa
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
