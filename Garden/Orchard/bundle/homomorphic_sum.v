(** * Homomorphic collapse of the bundle value-commitment sum (§4.14)

    The Pedersen-homomorphism step of the §4.14 balance argument: for a
    bundle whose actions all satisfy the per-action hypothesis package
    [OrchardBundleSpec.action_ok], the binding-validation key collapses to
    a single value commitment over the two §5.4.8.3 generators,

      [bvk = [Σ (v_old_i − v_new_i) − v^balance] 𝒱 + [Σ rcv_i] ℛ],

    i.e. [bundle_bvk b] is the point form of
    [ValueCommit_{Σ rcv}(Σ net − v^balance)].

    The per-action input is [CvNetValue.cv_net_commits_net_value_Z]
    ([Orchard/circuit_proof/cv_net_value.v]): each action's public
    [cv_net] equals [value_commit (v_old − v_new) rcv] over ℤ.  The
    collapse pulls those coordinate records back onto the Weierstrass
    group ([PallasModel.unrepr]), folds the action list with the group
    law, and merges the scalars with the ℤ-indexed homomorphism
    [Weierstrass.mul_add] (through the [FixedBaseLadder] wrappers), so
    the scalar sums stay in ℤ with no reduction modulo the group order.
    The [reduced]/[on_curve] side conditions of associativity and of the
    homomorphism are threaded through every addition from the generator
    facts of [Orchard/Pallas/Generators.v]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.cv_net_value.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.bundle.spec.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the conversion oracle: no
   up-to-conversion matching may evaluate [modpow] over the concrete Pallas
   [(p-1)/2] exponent (see [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module OrchardBundleSum.
  Import OrchardBundleSpec.

  (** ** Pallas group-law wrappers

      The [Weierstrass] abelian-group laws at the Pallas instance, with
      the characteristic and nonsingularity hypotheses discharged once
      ([Pallas.eleven_lt_p] / [Pallas.nonsingular]).  The multiplication
      wrappers ([pallas_mul_add] / [pallas_mul_neg] /
      [pallas_mul_reduced] / [pallas_mul_on_curve]) are the
      [FixedBaseLadder] kit of [Orchard/circuit_proof/ladder/main.v]. *)

  Lemma pallas_add_reduced (P Q : Pallas.point)
      (HrP : Pallas.reduced P) (HrQ : Pallas.reduced Q) :
    Pallas.reduced (Pallas.add P Q).
  Proof. apply Weierstrass.add_reduced; assumption. Qed.

  Lemma pallas_add_on_curve (P Q : Pallas.point)
      (HoP : Pallas.on_curve P) (HoQ : Pallas.on_curve Q) :
    Pallas.on_curve (Pallas.add P Q).
  Proof.
    apply Weierstrass.add_on_curve;
      [exact Pallas.three_lt_p | exact HoP | exact HoQ].
  Qed.

  Lemma pallas_add_comm (P Q : Pallas.point)
      (HoP : Pallas.on_curve P) (HoQ : Pallas.on_curve Q) :
    Pallas.add P Q = Pallas.add Q P.
  Proof.
    exact (Weierstrass.add_comm (p := Primes.pallas_p) Pallas.a Pallas.b
      P Q HoP HoQ).
  Qed.

  Lemma pallas_add_assoc (P Q S : Pallas.point)
      (HrP : Pallas.reduced P) (HrQ : Pallas.reduced Q)
      (HrS : Pallas.reduced S)
      (HoP : Pallas.on_curve P) (HoQ : Pallas.on_curve Q)
      (HoS : Pallas.on_curve S) :
    Pallas.add (Pallas.add P Q) S = Pallas.add P (Pallas.add Q S).
  Proof.
    exact (Weierstrass.add_assoc (p := Primes.pallas_p) Pallas.a Pallas.b
      P Q S Pallas.eleven_lt_p Pallas.nonsingular HrP HrQ HrS HoP HoQ HoS).
  Qed.

  (** Interchange of two parallel sums,
      [(A + B) + (C + D) = (A + C) + (B + D)] — the regrouping step that
      merges one action's [𝒱]/[ℛ] components into the running per-base
      accumulators. *)
  Lemma pallas_add_interchange (A B C D : Pallas.point)
      (HrA : Pallas.reduced A) (HrB : Pallas.reduced B)
      (HrC : Pallas.reduced C) (HrD : Pallas.reduced D)
      (HoA : Pallas.on_curve A) (HoB : Pallas.on_curve B)
      (HoC : Pallas.on_curve C) (HoD : Pallas.on_curve D) :
    Pallas.add (Pallas.add A B) (Pallas.add C D) =
      Pallas.add (Pallas.add A C) (Pallas.add B D).
  Proof.
    rewrite (pallas_add_assoc A B (Pallas.add C D) HrA HrB
      (pallas_add_reduced C D HrC HrD) HoA HoB
      (pallas_add_on_curve C D HoC HoD)).
    rewrite <- (pallas_add_assoc B C D HrB HrC HrD HoB HoC HoD).
    rewrite (pallas_add_comm B C HoB HoC).
    rewrite (pallas_add_assoc C B D HrC HrB HrD HoC HoB HoD).
    rewrite <- (pallas_add_assoc A C (Pallas.add B D) HrA HrC
      (pallas_add_reduced B D HrB HrD) HoA HoC
      (pallas_add_on_curve B D HoB HoD)).
    reflexivity.
  Qed.

  (** Right-operand swap, [(A + B) + C = (A + C) + B] — the regrouping
      step that folds the [⊟ ValueCommit_0(v^balance)] term into the [𝒱]
      component. *)
  Lemma pallas_add_swap (A B C : Pallas.point)
      (HrA : Pallas.reduced A) (HrB : Pallas.reduced B)
      (HrC : Pallas.reduced C)
      (HoA : Pallas.on_curve A) (HoB : Pallas.on_curve B)
      (HoC : Pallas.on_curve C) :
    Pallas.add (Pallas.add A B) C = Pallas.add (Pallas.add A C) B.
  Proof.
    rewrite (pallas_add_assoc A B C HrA HrB HrC HoA HoB HoC).
    rewrite (pallas_add_comm B C HoB HoC).
    rewrite <- (pallas_add_assoc A C B HrA HrC HrB HoA HoC HoB).
    reflexivity.
  Qed.

  (** ** Side-condition kit at the two value-commitment generators *)

  Lemma mul_v_reduced (k : Z) :
    Pallas.reduced (Pallas.mul k PallasGenerators.value_commit_v_G).
  Proof.
    apply FixedBaseLadder.pallas_mul_reduced.
    exact PallasGenerators.value_commit_v_reduced.
  Qed.

  Lemma mul_v_on_curve (k : Z) :
    Pallas.on_curve (Pallas.mul k PallasGenerators.value_commit_v_G).
  Proof.
    apply FixedBaseLadder.pallas_mul_on_curve.
    exact PallasGenerators.value_commit_v_on_curve.
  Qed.

  Lemma mul_r_reduced (k : Z) :
    Pallas.reduced (Pallas.mul k PallasGenerators.value_commit_r_G).
  Proof.
    apply FixedBaseLadder.pallas_mul_reduced.
    exact PallasGenerators.value_commit_r_reduced.
  Qed.

  Lemma mul_r_on_curve (k : Z) :
    Pallas.on_curve (Pallas.mul k PallasGenerators.value_commit_r_G).
  Proof.
    apply FixedBaseLadder.pallas_mul_on_curve.
    exact PallasGenerators.value_commit_r_on_curve.
  Qed.

  (** ** Per-action point form

      [unrepr] carries a [value_commit] coordinate record back onto the
      group; the argument of [repr] is on-curve (a sum of multiples of
      the on-curve generators), so the round trip is the identity. *)
  Lemma unrepr_value_commit (v rcv : Z) :
    PallasModel.unrepr (OrchardProtocolSpec.value_commit v rcv) =
      Pallas.add
        (Pallas.mul v PallasGenerators.value_commit_v_G)
        (Pallas.mul rcv PallasGenerators.value_commit_r_G).
  Proof.
    unfold OrchardProtocolSpec.value_commit.
    apply PallasModel.unrepr_repr.
    apply pallas_add_on_curve; [apply mul_v_on_curve | apply mul_r_on_curve].
  Qed.

  (** §4.18.4 'Value commitment integrity' in point form: the action's
      public [cv_net], read back onto the group, is
      [[v_old − v_new] 𝒱 + [rcv] ℛ] with the net value over ℤ. *)
  Lemma action_cv_net_eq (Γ : Assignment.t columns RegionId.t)
      (Hok : action_ok Γ) :
    action_cv_net Γ =
      Pallas.add
        (Pallas.mul (action_net_value Γ)
          PallasGenerators.value_commit_v_G)
        (Pallas.mul (action_rcv Γ)
          PallasGenerators.value_commit_r_G).
  Proof.
    destruct Hok as (Hcircuit & Hmerkle & Hnote & Hold).
    unfold action_cv_net, action_net_value, action_rcv.
    rewrite (CvNetValue.cv_net_commits_net_value_Z
      Γ Hcircuit Hmerkle Hnote Hold).
    apply unrepr_value_commit.
  Qed.

  (** ** Fold-cons unrollings *)

  Lemma cv_net_sum_cons (Γ : Assignment.t columns RegionId.t)
      (acts : list (Assignment.t columns RegionId.t)) :
    cv_net_sum (Γ :: acts) =
      Pallas.add (action_cv_net Γ) (cv_net_sum acts).
  Proof. reflexivity. Qed.

  Lemma net_value_sum_cons (Γ : Assignment.t columns RegionId.t)
      (acts : list (Assignment.t columns RegionId.t)) :
    net_value_sum (Γ :: acts) = action_net_value Γ + net_value_sum acts.
  Proof. reflexivity. Qed.

  Lemma rcv_sum_cons (Γ : Assignment.t columns RegionId.t)
      (acts : list (Assignment.t columns RegionId.t)) :
    rcv_sum (Γ :: acts) = action_rcv Γ + rcv_sum acts.
  Proof. reflexivity. Qed.

  (** ** The homomorphic sum over an action list

      [⊞ cv_net_i = [Σ (v_old_i − v_new_i)] 𝒱 + [Σ rcv_i] ℛ], both scalar
      sums over ℤ.  Induction over the list: each action contributes its
      point form ([action_cv_net_eq]), and the ℤ-indexed homomorphism
      [pallas_mul_add] plus the interchange law merge it into the running
      accumulators.  The empty bundle is the identity on both sides
      ([mul 0] and the empty fold). *)
  Lemma cv_net_sum_eq (acts : list (Assignment.t columns RegionId.t))
      (Hok : Forall action_ok acts) :
    cv_net_sum acts =
      Pallas.add
        (Pallas.mul (net_value_sum acts)
          PallasGenerators.value_commit_v_G)
        (Pallas.mul (rcv_sum acts)
          PallasGenerators.value_commit_r_G).
  Proof.
    revert Hok. induction acts as [| Γ acts IH]; intros Hok.
    - reflexivity.
    - pose proof (Forall_inv Hok) as HΓ.
      pose proof (Forall_inv_tail Hok) as Hacts.
      rewrite cv_net_sum_cons, net_value_sum_cons, rcv_sum_cons.
      rewrite (action_cv_net_eq Γ HΓ), (IH Hacts).
      rewrite (FixedBaseLadder.pallas_mul_add
        (action_net_value Γ) (net_value_sum acts)
        PallasGenerators.value_commit_v_G
        PallasGenerators.value_commit_v_reduced
        PallasGenerators.value_commit_v_on_curve).
      rewrite (FixedBaseLadder.pallas_mul_add
        (action_rcv Γ) (rcv_sum acts)
        PallasGenerators.value_commit_r_G
        PallasGenerators.value_commit_r_reduced
        PallasGenerators.value_commit_r_on_curve).
      apply pallas_add_interchange;
        [ apply mul_v_reduced | apply mul_r_reduced
        | apply mul_v_reduced | apply mul_r_reduced
        | apply mul_v_on_curve | apply mul_r_on_curve
        | apply mul_v_on_curve | apply mul_r_on_curve ].
  Qed.

  (** ** The collapse theorem

      §4.14: [bvk = (⊞ cv_net_i) ⊟ ValueCommit_0(v^balanceOrchard)]
      collapses to the single commitment
      [[Σ (v_old_i − v_new_i) − v^balance] 𝒱 + [Σ rcv_i] ℛ] — the point
      form of [ValueCommit_{Σ rcv}(Σ net − v^balance)].  The subtraction
      enters through [pallas_mul_neg]
      ([⊟ [v] 𝒱 = [−v] 𝒱]) and the same ℤ-indexed homomorphism. *)
  Theorem bundle_bvk_collapse (b : t) (Hok : actions_ok b) :
    bundle_bvk b =
      Pallas.add
        (Pallas.mul (sum_net_values b - value_balance b)
          PallasGenerators.value_commit_v_G)
        (Pallas.mul (sum_rcv b)
          PallasGenerators.value_commit_r_G).
  Proof.
    unfold bundle_bvk, value_commit_0, sum_net_values, sum_rcv.
    rewrite (cv_net_sum_eq (actions b) Hok).
    rewrite <- (FixedBaseLadder.pallas_mul_neg (value_balance b)
      PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_reduced).
    replace (net_value_sum (actions b) - value_balance b)
      with (net_value_sum (actions b) + - value_balance b)
      by (clear; lia).
    rewrite (FixedBaseLadder.pallas_mul_add
      (net_value_sum (actions b)) (- value_balance b)
      PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_reduced
      PallasGenerators.value_commit_v_on_curve).
    apply pallas_add_swap;
      [ apply mul_v_reduced | apply mul_r_reduced | apply mul_v_reduced
      | apply mul_v_on_curve | apply mul_r_on_curve | apply mul_v_on_curve ].
  Qed.

  (** The same collapse across the [repr] bridge: the coordinate-record
      form of [bvk] is literally the [OrchardProtocolSpec.value_commit]
      of the bundle's net value and randomness sums. *)
  Corollary bundle_bvk_commits (b : t) (Hok : actions_ok b) :
    PallasModel.repr (bundle_bvk b) =
      OrchardProtocolSpec.value_commit
        (sum_net_values b - value_balance b) (sum_rcv b).
  Proof.
    rewrite (bundle_bvk_collapse b Hok).
    unfold OrchardProtocolSpec.value_commit.
    reflexivity.
  Qed.
End OrchardBundleSum.
