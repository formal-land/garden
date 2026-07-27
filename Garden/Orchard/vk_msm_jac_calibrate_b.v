(** * Inversion-free MSM commitment certificate, fixed column 0, bases
      [1024 .. 2047]

    The second half-range Jacobian checkpoint; see
    [Orchard/vk_msm_jac_calibrate_a.v]. *)

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

Lemma vk_msm_fixed0_shard_b_jac :
  VestaJac.jcheck
    (VkMsmJac.msm_pippenger_jac (List.skipn 1024 VkMsmDataFixed0.c)
       (List.map VestaJac.jof (List.skipn 1024 VkMsm.g_points)))
    VkMsmDataFixed0.cpb
  = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
