(** * The vk-commitment MSM certificate for fixed column 0, inversion-free
      route

    The same commitment [Orchard/vk_msm_calibrate.v] certifies — the
    [commit_lagrange] of the compiled fixed column 0 of the Orchard verifying
    key is the deployed pinned point [VkPinnedData.fixed_commitments[0]] —
    closed through the Jacobian mirror instead of the affine pipeline.

    The two heavy half-range checkpoints
    ([Orchard/vk_msm_jac_calibrate_{a,b}.v]) evaluate
    [VkMsmJac.msm_pippenger_jac] and test the result against the pinned
    coordinate pairs with [VestaJac.jcheck]: four multiplications, no
    normalisation, and no [mod_inverse] anywhere on the computed path.
    [VkMsmJac.commit_two_shards_jac] turns those two boolean facts back into
    the affine shard equations [VkMsm.commit_two_shards] consumes.

    The column, length, range, coefficient and blind-and-compare certificates
    are shared with the affine assembly; only the shard checkpoints differ.
    [vk_commit_fixed0_jac] states exactly the proposition the affine
    [vk_commit_fixed0] states, so the two routes are compared on the pinned
    point itself, and [fixed0_shard_a_via_jac] / [fixed0_shard_b_via_jac]
    re-derive the affine half-range checkpoint equations without ever
    evaluating the affine MSM. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.VestaJacobian.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.plonkish.lookup_compile.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.circuit_compiled_check.
Require Import Garden.Orchard.vk_pinned_data.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk_msm_jac.
Require Import Garden.Orchard.vk_msm_data_fixed0.
Require Import Garden.Orchard.vk_msm_calibrate.
Require Import Garden.Orchard.vk_msm_jac_calibrate_a.
Require Import Garden.Orchard.vk_msm_jac_calibrate_b.

Import ListNotations.

Global Open Scope Z_scope.

(** ** The checkpoint literals are canonical

    [VestaJac.jcheck] pins its target modulo [pallas_q], so the shard equation
    it yields is stated with [Vesta.affine]; the pasted checkpoints are already
    reduced, which identifies that with the raw [VkMsm.aff] pair. *)

Lemma fixed0_cpa_affine :
  Vesta.affine (fst VkMsmDataFixed0.cpa) (snd VkMsmDataFixed0.cpa)
  = VkMsm.aff VkMsmDataFixed0.cpa.
Proof.
  vm_cast_no_check
    (@eq_refl VkMsm.point (VkMsm.aff VkMsmDataFixed0.cpa)).
Qed.

Lemma fixed0_cpb_affine :
  Vesta.affine (fst VkMsmDataFixed0.cpb) (snd VkMsmDataFixed0.cpb)
  = VkMsm.aff VkMsmDataFixed0.cpb.
Proof.
  vm_cast_no_check
    (@eq_refl VkMsm.point (VkMsm.aff VkMsmDataFixed0.cpb)).
Qed.

(** The blind-and-compare step in the shape [commit_two_shards_jac] expects. *)
Lemma fixed0_final_jac :
  VkMsm.padd
    (VkMsm.padd
       (Vesta.affine (fst VkMsmDataFixed0.cpa) (snd VkMsmDataFixed0.cpa))
       (Vesta.affine (fst VkMsmDataFixed0.cpb) (snd VkMsmDataFixed0.cpb)))
    VkMsm.w_point
  = Weierstrass.Affine (fst pinned_fixed0) (snd pinned_fixed0).
Proof.
  rewrite fixed0_cpa_affine, fixed0_cpb_affine. exact fixed0_final.
Qed.

(** ** The affine half-range checkpoints, re-derived

    The statements of [vk_msm_fixed0_shard_a] and [vk_msm_fixed0_shard_b],
    obtained from the inversion-free certificates alone. *)

Lemma fixed0_shard_a_via_jac :
  VkMsm.msm_pippenger (List.firstn 1024 VkMsmDataFixed0.c)
    (List.firstn 1024 VkMsm.g_points)
  = VkMsm.aff VkMsmDataFixed0.cpa.
Proof.
  rewrite <- fixed0_cpa_affine.
  destruct VkMsmDataFixed0.cpa as [xa ya] eqn:Ea.
  apply (VkMsmJac.jshard_sound (List.firstn 1024 VkMsmDataFixed0.c)
           (List.firstn 1024 VkMsm.g_points) xa ya
           (VkMsm.Forall_firstn VkMsm.good 1024 VkMsm.g_points
              VkMsm.g_points_good)).
  rewrite <- Ea. exact vk_msm_fixed0_shard_a_jac.
Qed.

Lemma fixed0_shard_b_via_jac :
  VkMsm.msm_pippenger (List.skipn 1024 VkMsmDataFixed0.c)
    (List.skipn 1024 VkMsm.g_points)
  = VkMsm.aff VkMsmDataFixed0.cpb.
Proof.
  rewrite <- fixed0_cpb_affine.
  destruct VkMsmDataFixed0.cpb as [xb yb] eqn:Eb.
  apply (VkMsmJac.jshard_sound (List.skipn 1024 VkMsmDataFixed0.c)
           (List.skipn 1024 VkMsm.g_points) xb yb
           (VkMsm.Forall_skipn VkMsm.good 1024 VkMsm.g_points
              VkMsm.g_points_good)).
  rewrite <- Eb. exact vk_msm_fixed0_shard_b_jac.
Qed.

(** ** The commitment theorem through the inversion-free route

    The statement is [vk_commit_fixed0]'s: for the replayed zero-witness grid,
    the [commit_lagrange] of compiled fixed column 0 is the deployed verifying
    key's first fixed commitment. *)
Theorem vk_commit_fixed0_jac (grid : RawGrid.t) :
  apply_events orchard_events (initial_grid (fun _ _ => 0) (fun _ _ => 0))
  = Some grid ->
  VkMsm.commit_lagrange (orchard_fixed_column_of grid 0)
  = Weierstrass.Affine (fst pinned_fixed0) (snd pinned_fixed0).
Proof.
  intros Hgrid.
  pose proof
    (eq_trans
       (eq_sym (f_equal
          (option_map (fun g => orchard_fixed_column_of g 0)) Hgrid))
       fixed0_column_cert) as Hc.
  cbn [option_map] in Hc.
  assert (Hv : orchard_fixed_column_of grid 0 = VkMsmDataFixed0.v)
    by exact (f_equal
         (fun o : option (list Z) =>
            match o with Some l => l | None => VkMsmDataFixed0.v end)
         Hc).
  refine (eq_ind_r
            (fun w => VkMsm.commit_lagrange w
                      = Weierstrass.Affine (fst pinned_fixed0)
                          (snd pinned_fixed0)) _ Hv).
  exact (VkMsmJac.commit_two_shards_jac VkMsmDataFixed0.v VkMsmDataFixed0.c
           VkMsmDataFixed0.cpa VkMsmDataFixed0.cpb
           (fst pinned_fixed0) (snd pinned_fixed0)
           fixed0_length fixed0_range fixed0_intt
           vk_msm_fixed0_shard_a_jac vk_msm_fixed0_shard_b_jac
           fixed0_final_jac).
Qed.

(** The inversion-free route closes the affine route's proposition on the
    nose: [vk_commit_fixed0_jac] inhabits the type of [vk_commit_fixed0], so
    both certify the same pinned commitment point. *)
Definition vk_commit_fixed0_routes_agree
  : ltac:(let T := type of vk_commit_fixed0 in exact T)
  := vk_commit_fixed0_jac.
