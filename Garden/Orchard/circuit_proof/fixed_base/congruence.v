Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.

#[local] Existing Instance Garden.Plonky3.M.Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Fold congruence for the internal-soundness fixed-base multiplication

    The witness [us] enters
    [EccSpec.fixed_scalar_mul] only through the per-window points
    [fixed_window_point w (window_digit k i) (nth i us 0)].  This file proves that
    if the per-window points agree for two witness lists [us1] and [us2], then the
    whole fold — [fixed_scalar_mul_aux] and hence [fixed_scalar_mul] — agrees.

    The window enters the per-window point only through [fw_z w] (the x-coordinate
    is [u]-independent and the y-coordinate is [u² − fw_z w]), so the hypothesis is
    quantified over every window [w] and index [i]; consumers discharge it because
    the equality reduces to [(nth i us1 0)² = (nth i us2 0)²], independent of [w].

    Depends only on [ecc/chip/spec.v] (plus the field notations and the [Point]
    module, both transitive dependencies of [spec.v]). *)

Module FixedBaseCongruence.
  Import EccSpec.

  (** A single window point is [u]-independent up to the square of [u]: equal
      squares [u1² = u2²] give equal window points (the [x] is [u]-free and the
      [y] is [u² − fw_z w]).  This is the pointwise fact the fold threads. *)
  Lemma fixed_window_point_us_congr
      (w : fixed_window) (digit u1 u2 : Z)
      (Hsq : u1 *F u1 = u2 *F u2) :
    fixed_window_point w digit u1 = fixed_window_point w digit u2.
  Proof.
    unfold fixed_window_point.
    rewrite Hsq.
    reflexivity.
  Qed.

  (** Fold congruence for the auxiliary recursion at an arbitrary starting index
      [i0] and accumulator [acc]: equal per-window points give equal folds.  The
      induction threads [point_add] congruence through the accumulator, so the
      starting index and accumulator are generalised. *)
  Lemma fixed_scalar_mul_aux_us_congr
      (tbl : fixed_table) (k : Z) (us1 us2 : list Z)
      (Hwin : forall (w : fixed_window) (i : nat),
        fixed_window_point w (window_digit k i) (List.nth i us1 0) =
        fixed_window_point w (window_digit k i) (List.nth i us2 0)) :
    forall (i0 : nat) (acc : Point.t),
      fixed_scalar_mul_aux tbl k us1 i0 acc =
      fixed_scalar_mul_aux tbl k us2 i0 acc.
  Proof.
    induction tbl as [| w ws IH]; intros i0 acc.
    - reflexivity.
    - rewrite (fixed_scalar_mul_aux_cons w ws k us1 i0 acc).
      rewrite (fixed_scalar_mul_aux_cons w ws k us2 i0 acc).
      rewrite (Hwin w i0).
      apply IH.
  Qed.

  (** Fold congruence for the top-level fixed-base multiplication: equal
      per-window points across every window and index give equal [fixed_scalar_mul].
      This is the form instantiated with [us1 := read_us …] and
      [us2 := canonical_us_for tbl k]. *)
  Lemma fixed_scalar_mul_us_congr
      (tbl : fixed_table) (k : Z) (us1 us2 : list Z)
      (Hwin : forall (w : fixed_window) (i : nat),
        fixed_window_point w (window_digit k i) (List.nth i us1 0) =
        fixed_window_point w (window_digit k i) (List.nth i us2 0)) :
    fixed_scalar_mul tbl k us1 = fixed_scalar_mul tbl k us2.
  Proof.
    unfold fixed_scalar_mul.
    apply fixed_scalar_mul_aux_us_congr.
    exact Hwin.
  Qed.

  (** The convenient consumer form: the witness lists enter only through the
      per-index square [u²], so agreement of [(nth i us1 0)²] and [(nth i us2 0)²]
      at every index already forces equal folds.  The QR window-sign forcing
      supplies exactly this squares equality. *)
  Lemma fixed_scalar_mul_us_congr_of_sq
      (tbl : fixed_table) (k : Z) (us1 us2 : list Z)
      (Hsq : forall i : nat,
        List.nth i us1 0 *F List.nth i us1 0 =
        List.nth i us2 0 *F List.nth i us2 0) :
    fixed_scalar_mul tbl k us1 = fixed_scalar_mul tbl k us2.
  Proof.
    apply fixed_scalar_mul_us_congr.
    intros w i.
    apply (fixed_window_point_us_congr w (window_digit k i)
      (List.nth i us1 0) (List.nth i us2 0) (Hsq i)).
  Qed.
End FixedBaseCongruence.
