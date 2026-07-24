(** * The vk-commitment MSM certificate for fixed column 0

    End-to-end instance of the [VkMsm] machinery on one pinned commitment:
    the compiled fixed column 0 of the Orchard verifying key — read from
    the replayed zero-witness grid with the combination planes installed,
    exactly the Lagrange vector keygen commits — has

      [commit_lagrange v = fixed_commitments[0]],

    the deployed vk point ([Orchard/vk_pinned_data.v], itself certified
    byte-level into the pinned description by [vk_pinned_parity.v]).  The
    chain is [VkMsm.commit_two_shards]: the replayed-column certificate,
    the range scan, the in-kernel [intt] coefficient certificate, the two
    heavy Pippenger half-range checkpoints
    ([vk_msm_calibrate_{a,b}.v]), and the final [+ w] blind-and-compare
    step.  This file is also the calibration gate of the certificate
    campaign: the per-certificate costs measured here size the remaining
    43 commitment runs. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.plonkish.lookup_compile.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.circuit_compiled_check.
Require Import Garden.Orchard.vk_pinned_data.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.vk_msm_data_fixed0.
Require Import Garden.Orchard.vk_msm_calibrate_a.
Require Import Garden.Orchard.vk_msm_calibrate_b.

Import ListNotations.

Global Open Scope Z_scope.

(** The full 2048-row Lagrange vector of a fixed column of the compiled
    system, over the replayed zero-witness grid with the combination
    planes installed — the vector keygen commits ([keygen.rs:233-236]). *)
Definition orchard_fixed_column_of (grid : RawGrid.t) (col : Z)
    : list Z :=
  List.map
    (fun r =>
      (PlonkishLookup.with_combination_planes
         OrchardCompiledCheck.compiled grid).(RawGrid.cell)
        Raw.ColumnKind.Fixed col (Z.of_nat r))
    (List.seq 0 2048).

(** ** The [vm_compute] certificates *)

(** The pasted column literal is the replayed column.  Stated as the raw
    [option_map] term so the assembly theorem composes with it
    syntactically. *)
Lemma fixed0_column_cert :
  option_map (fun g => orchard_fixed_column_of g 0)
    (apply_events orchard_events
       (initial_grid (fun _ _ => 0) (fun _ _ => 0)))
  = Some VkMsmDataFixed0.v.
Proof.
  vm_cast_no_check
    (@eq_refl (option (list Z)) (Some VkMsmDataFixed0.v)).
Qed.

Lemma fixed0_length :
  List.length VkMsmDataFixed0.v = 2048%nat.
Proof. vm_cast_no_check (@eq_refl nat 2048%nat). Qed.

Lemma fixed0_range :
  List.forallb (fun s => (0 <=? s) && (s <? Primes.pallas_p))
    VkMsmDataFixed0.v = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** The pasted coefficient vector is the in-kernel inverse NTT of the
    column. *)
Lemma fixed0_intt :
  VkMsm.intt VkMsmDataFixed0.v = VkMsmDataFixed0.c.
Proof. vm_cast_no_check (@eq_refl (list Z) VkMsmDataFixed0.c). Qed.

(** The pinned commitment of fixed column 0. *)
Definition pinned_fixed0 : Z * Z :=
  List.nth 0 VkPinnedData.fixed_commitments (0, 0).

(** Checkpoint recombination with the mandatory [Blind::default() = 1]
    term: [cpa + cpb + w] is the pinned point. *)
Lemma fixed0_final :
  VkMsm.padd
    (VkMsm.padd (VkMsm.aff VkMsmDataFixed0.cpa)
       (VkMsm.aff VkMsmDataFixed0.cpb))
    VkMsm.w_point
  = Weierstrass.Affine (fst pinned_fixed0) (snd pinned_fixed0).
Proof.
  vm_cast_no_check
    (@eq_refl VkMsm.point
       (Weierstrass.Affine (fst pinned_fixed0) (snd pinned_fixed0))).
Qed.

(** ** The commitment theorem

    For the replayed zero-witness grid — the fixed plane the keygen
    assembly holds — the [commit_lagrange] of compiled fixed column 0 is
    the deployed verifying key's first fixed commitment. *)
Theorem vk_commit_fixed0 (grid : RawGrid.t) :
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
  exact (VkMsm.commit_two_shards VkMsmDataFixed0.v VkMsmDataFixed0.c
           (VkMsm.aff VkMsmDataFixed0.cpa) (VkMsm.aff VkMsmDataFixed0.cpb)
           (fst pinned_fixed0) (snd pinned_fixed0)
           fixed0_length fixed0_range fixed0_intt
           vk_msm_fixed0_shard_a vk_msm_fixed0_shard_b fixed0_final).
Qed.
