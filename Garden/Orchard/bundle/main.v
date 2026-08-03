(** * Transaction-level value balance for Orchard bundles (§4.14, §4.17)

    The no-counterfeiting composition over a whole Orchard bundle, against
    §4.14 'Balance and Binding Signature (Orchard)' of the Zcash protocol
    specification:

    - [balanced_or_dlog] — for a bundle whose actions all satisfy the
      per-action hypothesis package, whose action count and declared
      balance are in the consensus ranges, and whose binding signature
      carries its knowledge content (§5.4.7.2), the declared balance is
      honest ([Σ (v_old_i - v_new_i) = v^balanceOrchard]) or the two
      openings of [bvk] yield an explicit discrete logarithm between the
      §5.4.8.3 value-commitment bases ([OrchardBundleSpec.dlog_relation]).
      Pedersen binding enters as this reduction only — discarding the
      right disjunct is exactly the discrete-log hardness assumption on
      the generator pair; no independence axiom is stated (such an axiom
      would be refutable in-model, the group being cyclic of prime
      order).

    - [no_inflation] — the §4.17 chain-pool composition over a list of
      bundles: with the per-bundle hypotheses and the consensus rule
      [ChainValuePoolBalance = - Σ v^balance >= 0], either every bundle
      balances and the total net value withdrawn from the shielded pool
      is nonpositive, or some bundle yields the discrete-log relation.

    The three ingredients are the sibling files of [Garden/Orchard/bundle/]:
    the homomorphic collapse of [bvk] ([OrchardBundleSum]), the
    two-openings reduction with its computable witness
    ([OrchardBindingReduction.extracted_k]), and the pure-ℤ lift of the
    balance residue ([OrchardBundleIntegerLift]).  The disjunction splits
    on the decidable residue test [(v* mod pallas_q) =? 0] — no classical
    axioms. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_proof.typed_inputs.value64.
Require Import Garden.Orchard.bundle.spec.
Require Import Garden.Orchard.bundle.homomorphic_sum.
Require Import Garden.Orchard.bundle.binding_reduction.
Require Import Garden.Orchard.bundle.integer_lift.
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

Module OrchardBundle.
  Import OrchardBundleSpec.

  (** ** The per-action net-value range

      Each action's net value [v_old - v_new] lies in the open interval
      [(-(2^64), 2^64)]: both note values are 64-bit under the action's
      hypothesis package, each through its lane's short-lookup range
      family. *)
  Lemma action_net_value_range (Γ : Assignment.t columns RegionId.t)
      (Hok : action_ok Γ) :
    - 2 ^ 64 < action_net_value Γ < 2 ^ 64.
  Proof.
    destruct Hok as (Hcircuit & Hnew & Hold).
    pose proof (TypedInputsValue64.in_v_old_64 Γ Hcircuit Hold) as Hvold.
    pose proof (TypedInputsValue64.in_v_new_64 Γ Hcircuit Hnew) as Hvnew.
    unfold action_net_value.
    clear -Hvold Hvnew; lia.
  Qed.

  (** ** The §4.14 balance theorem

      For a bundle whose actions all satisfy the per-action package,
      whose action count and declared balance are in the consensus
      ranges, and whose binding-validation key opens as [[bsk] ℛ] (the
      knowledge content of a valid binding signature, §5.4.7.2):

      - either the declared balance is honest,
        [Σ (v_old_i - v_new_i) = v^balanceOrchard] over ℤ,
      - or the two openings [(v*, Σ rcv)] and [(0, bsk)] of [bvk] yield
        the explicit discrete logarithm
        [ℛ^Orchard = [k] 𝒱^Orchard] at the computable witness
        [k = extracted_k v* 0 (Σ rcv) bsk].

      The split is on the decidable test [(v* mod pallas_q) =? 0] with
      [v* = Σ (v_old_i - v_new_i) - v^balance]: in the zero branch the
      consensus ranges cap [|v*|] below [pallas_q] and the residue lifts
      to [v* = 0] over ℤ; in the nonzero branch the homomorphic collapse
      of [bvk] and the signature opening collide as two openings with
      distinct value scalars modulo the group order. *)
  Theorem balanced_or_dlog (b : t) (bsk : Z)
      (Hok : actions_ok b)
      (Hside : side_conditions b)
      (Hsig : SignatureKnowledge b bsk) :
    sum_net_values b = value_balance b \/
    exists k : Z, dlog_relation k.
  Proof.
    destruct Hside as [Hn Hvb].
    unfold SignatureKnowledge in Hsig.
    destruct (Z.eqb_spec
        ((sum_net_values b - value_balance b) mod Primes.pallas_q) 0)
      as [Hz | Hnz].
    - (* The residue vanishes modulo the group order: the consensus
         ranges lift it to zero over ℤ. *)
      left.
      assert (Hranges :
          Forall (fun Γ => - 2 ^ 64 < action_net_value Γ < 2 ^ 64)
            (actions b)).
      { eapply Forall_impl; [| exact Hok].
        exact action_net_value_range. }
      assert (H0 : sum_net_values b - value_balance b = 0).
      { unfold sum_net_values, net_value_sum.
        apply (OrchardBundleIntegerLift.net_value_fold_lift
          action_net_value (actions b) (value_balance b)).
        - exact Hn.
        - exact Hranges.
        - exact Hvb.
        - exact Hz. }
      clear -H0; lia.
    - (* The residue is nonzero modulo the group order: the collapsed
         [bvk] and the signature opening are two openings of one
         commitment with distinct value scalars — the reduction extracts
         the discrete logarithm. *)
      right.
      exists (OrchardBindingReduction.extracted_k
        (sum_net_values b - value_balance b) 0 (sum_rcv b) bsk).
      assert (Heq :
          Pallas.add
            (Pallas.mul (sum_net_values b - value_balance b)
              PallasGenerators.value_commit_v_G)
            (Pallas.mul (sum_rcv b) PallasGenerators.value_commit_r_G) =
          Pallas.add
            (Pallas.mul 0 PallasGenerators.value_commit_v_G)
            (Pallas.mul bsk PallasGenerators.value_commit_r_G)).
      { rewrite <- (OrchardBundleSum.bundle_bvk_collapse b Hok).
        rewrite Hsig.
        reflexivity. }
      assert (Hne :
          (sum_net_values b - value_balance b) mod Pallas.pallas_q <>
          0 mod Pallas.pallas_q).
      { rewrite Zmod_0_l. exact Hnz. }
      exact (OrchardBindingReduction.two_openings_dlog
        (sum_net_values b - value_balance b) (sum_rcv b) 0 bsk Heq Hne).
  Qed.

  (** ** Per-bundle hypothesis package

      The hypotheses of [balanced_or_dlog] for one bundle, with the
      binding-signature witness existentially packaged. *)
  Definition bundle_ok (b : t) : Prop :=
    actions_ok b /\ side_conditions b /\
    exists bsk : Z, SignatureKnowledge b bsk.

  (** Every bundle of a list balances, or some bundle yields the
      discrete-log relation — the list composition of
      [balanced_or_dlog]. *)
  Lemma bundles_balanced_or_dlog (bundles : list t)
      (Hok : Forall bundle_ok bundles) :
    Forall (fun b => sum_net_values b = value_balance b) bundles \/
    exists k : Z, dlog_relation k.
  Proof.
    induction Hok as [| b bundles Hb Hrest IH].
    - left; constructor.
    - destruct Hb as (Hb_ok & Hb_side & [bsk Hb_sig]).
      destruct (balanced_or_dlog b bsk Hb_ok Hb_side Hb_sig)
        as [Hbal | Hdlog]; [| right; exact Hdlog].
      destruct IH as [Hall | Hdlog]; [| right; exact Hdlog].
      left; constructor; assumption.
  Qed.

  (** ** The §4.17 chain-pool corollary

      Over the bundles of a chain, the §4.17 consensus rule keeps
      [ChainValuePoolBalance = - Σ v^balanceOrchard(tx)] nonnegative.
      With every bundle satisfying the per-bundle package: either every
      declared balance is honest — so the total net value withdrawn from
      the shielded pool, [Σ_tx Σ_i (v_old_i - v_new_i)], equals
      [Σ v^balance] and is therefore nonpositive (withdrawals are bounded
      by deposits; the pool cannot be inflated) — or some bundle yields
      the explicit discrete-log relation between the value-commitment
      bases. *)
  Theorem no_inflation (bundles : list t)
      (Hok : Forall bundle_ok bundles)
      (Hpool :
        0 <= - OrchardBundleIntegerLift.zsum (map value_balance bundles)) :
    (Forall (fun b => sum_net_values b = value_balance b) bundles /\
      OrchardBundleIntegerLift.zsum (map sum_net_values bundles) <= 0) \/
    exists k : Z, dlog_relation k.
  Proof.
    destruct (bundles_balanced_or_dlog bundles Hok)
      as [Hall | Hdlog]; [left | right; exact Hdlog].
    split; [exact Hall |].
    assert (Hmaps :
        map sum_net_values bundles = map value_balance bundles).
    { clear Hok Hpool.
      induction Hall as [| b bundles Hb Hrest IH]; cbn [map];
        [reflexivity |].
      rewrite Hb, IH. reflexivity. }
    rewrite Hmaps.
    clear -Hpool; lia.
  Qed.
End OrchardBundle.
