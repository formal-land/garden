(** * Forward witness facts: the fixed-base leg sums

    The [fixed-legs] group of the open witness-fact residue: the six
    [Fact.InstanceIs] public rows and the six cross-gadget copies whose two
    cell addresses the honest generator fills through different derivations
    of one value, all of them reducing to the same bridge — the hoisted
    fixed-base LEG SUM is the specification scalar multiple.

    A leg's last row emits [point_add (leg_pt L (n−1)) (leg_acc L (n−2))],
    a fold over the pasted window-table points, while the specification
    value is [repr ([k] G)].  [forward/ecc_add.v] already identifies each
    window point and each interior accumulator with its signed-radix-8
    multiple ([ladder_window_repr] / [ladder_acc_repr]); what remains is the
    last complete addition and the telescoping identity
    [cumulative_scalar n k n = k] for [0 ≤ k < 8^n], which
    [cumulative_full] supplies.  The seven per-base instances
    ([t_sa_comm], [t_vcv_mul], [t_vcr_pt], [t_nk_prod], [t_civkr_pt],
    [t_nco_pt], [t_ncn_pt]) then read the leg sums as the protocol's
    [mul_*] constants.

    On top of that bridge the twelve facts are: the value-commitment public
    rows (the [ValueCommitV] sign flip plus [signed_net_value]), the
    nullifier public row and the new note's [ρ] input (one equation, taken
    twice, needing commutativity of the complete addition on good points),
    the spend-authority public rows (the summands in the opposite order),
    the [Commit^ivk] output against the overflow-check [α] cell, the old
    note commitment against its witness cells, the new note's [cmx] public
    row, and the nullifier leg's initial accumulator
    ([leg_acc L 0 = leg_pt L 0]).

    Exports: [orchardwitnessfixedlegs_facts] (the twelve fact literals,
    copied from [nt_open]) and [orchardwitnessfixedlegs_ok]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Field.Pow2.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_r.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_v.
Require Import Garden.Orchard.circuit_proof.ladder.nullifier_k.
Require Import Garden.Orchard.circuit_proof.ladder.note_commit_r.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.value_commit_v.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.ecc_add.
Require Import Garden.Field.Div.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardWitnessFixedLegs.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.
  Import OrchardCompletenessTables.
  Import OrchardCompletenessForwardEccAdd.
  Import FixedBaseLadder.

  (** The field inverse, the complete-addition output and the scalar
      multiplications stay stuck atoms, so a cell reduction stops at the
      reader leaves (docs/compile-performance.md); [ecc_add.v] already
      exports these.  The hoisted record itself is deliberately NOT made
      opaque here: the shape equations below relate a projection of
      [tables_of w] to a spelling that names another of its projections,
      and holding the record opaque makes the kernel unfold the Sinsemilla
      folds on the other side instead of the record. *)
  #[local] Strategy opaque
    [BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** The Poseidon schedule stays folded: unfolding the 36-round chain
      duplicates its state three times per round (the [3^36] trap of
      docs/compile-performance.md), and the nullifier scalar's shape
      equation is stated over it. *)
  #[local] Opaque pose_states_of states_go.

  (** Kept local: [forward/lookups_witness.v], which consumes this file,
      carries the same abbreviation. *)
  Local Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** ** The window-scalar telescoping identity

      The signed-radix-8 encoding of [FixedBaseLadder] offsets each of the
      first [n − 1] windows by [2·8^w] and subtracts the accumulated offset
      on the last window, so the [n] window scalars sum back to the scalar
      whenever it fits in [n] windows. *)

  Lemma wos_succ (m : nat) :
    window_offset_sum (S m) = 2 * 8 ^ Z.of_nat m + window_offset_sum m.
  Proof. reflexivity. Qed.

  Lemma pow8_succ (m : nat) :
    8 ^ Z.of_nat (S m) = 8 ^ Z.of_nat m * 8.
  Proof.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    lia.
  Qed.

  (** Every window strictly below the last carries its [+2·8^w] offset, so
      the cumulative scalar after [m < n] windows is the scalar's low
      [m]-window remainder plus the accumulated offset. *)
  Lemma cumulative_prefix (n : nat) (k : Z) (Hk : 0 <= k) :
    forall m : nat, (m < n)%nat ->
    cumulative_scalar n k m = k mod 8 ^ Z.of_nat m + window_offset_sum m.
  Proof.
    induction m as [| m IH]; intro Hm.
    - cbn [cumulative_scalar partial_sum window_offset_sum].
      change (Z.of_nat 0) with 0.
      rewrite Z.pow_0_r, Z.mod_1_r.
      reflexivity.
    - rewrite cumulative_scalar_succ_gen.
      rewrite (IH ltac:(lia)).
      rewrite (window_scalar_nonlast_gen n m _ ltac:(lia)).
      rewrite wos_succ, pow8_succ.
      unfold EccSpec.window_digit.
      pose proof (pow8_pos m) as Hp.
      rewrite (Z.rem_mul_r k (8 ^ Z.of_nat m) 8 ltac:(lia) ltac:(lia)).
      lia.
  Qed.

  Lemma cumulative_full (m : nat) (k : Z)
      (Hk : 0 <= k < 8 ^ Z.of_nat (S m)) :
    cumulative_scalar (S m) k (S m) = k.
  Proof.
    rewrite cumulative_scalar_succ_gen.
    rewrite (cumulative_prefix (S m) k ltac:(lia) m ltac:(lia)).
    rewrite window_scalar_last_gen.
    unfold EccSpec.window_digit.
    pose proof (pow8_pos m) as Hp.
    assert (Hdiv : k / 8 ^ Z.of_nat m < 8).
    { apply Z.div_lt_upper_bound; [lia |].
      rewrite pow8_succ in Hk. lia. }
    assert (Hdiv0 : 0 <= k / 8 ^ Z.of_nat m)
      by (apply Z.div_pos; lia).
    rewrite (Z.mod_small (k / 8 ^ Z.of_nat m) 8 ltac:(lia)).
    pose proof (Z.div_mod k (8 ^ Z.of_nat m) ltac:(lia)) as Hdm.
    lia.
  Qed.

  (** Index side conditions, proved in an empty context: [lia] preprocesses
      every hypothesis it sees, and the leg section's context carries the
      window-table bridges and a [Z.pow] bound
      (docs/compile-performance.md). *)
  Lemma two_le_SS (m : nat) : (2 <= S (S m))%nat.
  Proof. apply le_n_S, le_n_S, Nat.le_0_l. Qed.

  Lemma lt_S_SS (m : nat) : (S m < S (S m))%nat.
  Proof. apply le_n. Qed.

  (** ** The leg sum is the specification multiple

      Same hypotheses as [ecc_add.v]'s [LegLadder] section: an abstract
      prime-order base whose window table is certified against its
      multiples.  The last row's complete addition composes the last window
      point with the accumulator of all the earlier ones, and the
      telescoping identity above collapses the two scalars to [k]. *)
  Section LegSum.
    Variable G : Pallas.point.
    Hypothesis HGoc : Pallas.on_curve G.
    Hypothesis HGred : Pallas.reduced G.
    Hypothesis HGne : G <> Pallas.identity.
    Hypothesis HGord : Pallas.mul Pallas.pallas_q G = Pallas.identity.
    Variable m : nat.
    Hypothesis Hm85 : (S (S m) <= 85)%nat.
    Variable tbl : EccSpec.fixed_table.
    Hypothesis Htlen : List.length tbl = S (S m).
    Variable roots : list (list Z).
    Hypothesis Hx_bridge :
      forall (wi : nat) (d u : Z),
        (wi < S (S m))%nat -> 0 <= d < 8 ->
        Point.x
          (EccSpec.fixed_window_point
            (List.nth wi tbl OrchardActionFixedBase.fixed_window_default) d u) =
        Point.x
          (PallasModel.repr
            (Pallas.mul (window_scalar (S (S m)) wi d) G)).
    Hypothesis Hroot_bridge :
      forall (wi : nat) (d : Z),
        (wi < S (S m))%nat -> 0 <= d < 8 ->
        List.nth (Z.to_nat d) (List.nth wi roots []) 0 *F
          List.nth (Z.to_nat d) (List.nth wi roots []) 0 =
        UnOp.from
          (EccSpec.fw_z
            (List.nth wi tbl OrchardActionFixedBase.fixed_window_default) +F
           Point.y
             (PallasModel.repr
               (Pallas.mul (window_scalar (S (S m)) wi d) G))).
    Variable k : Z.
    Hypothesis Hk : 0 <= k < 8 ^ Z.of_nat (S (S m)).

    Lemma leg_sum_repr :
      EccSpec.point_add
        (leg_pt (leg_of tbl roots k) (S m))
        (leg_acc (leg_of tbl roots k) m) =
      PallasModel.repr (Pallas.mul k G).
    Proof using All.
      pose proof (ladder_window_repr G HGoc HGred HGne HGord (S (S m))
        (two_le_SS m) Hm85 tbl Htlen roots Hx_bridge Hroot_bridge k (S m)
        (lt_S_SS m)) as Hwin.
      pose proof (ladder_acc_repr G HGoc HGred HGne HGord (S (S m))
        (two_le_SS m) Hm85 tbl Htlen roots Hx_bridge Hroot_bridge k m
        (lt_S_SS m)) as Hacc.
      rewrite Hwin, Hacc.
      rewrite <- (pallas_repr_add _ _
        (pallas_mul_reduced _ G HGred) (pallas_mul_reduced _ G HGred)
        (pallas_mul_on_curve _ G HGoc) (pallas_mul_on_curve _ G HGoc)).
      rewrite <- (pallas_mul_add _ _ G HGred HGoc).
      apply (f_equal PallasModel.repr), mul_scalar_eq.
      rewrite Z.add_comm.
      rewrite <- (cumulative_scalar_succ_gen (S (S m)) k (S m)).
      exact (cumulative_full (S m) k Hk).
    Qed.
  End LegSum.

  (** ** The typing envelope's scalar bounds

      Each windowed scalar must fit in its leg's window count: the scalars
      are below [q_P] (seven full-width legs), the value magnitude below
      [2^64], and the nullifier scalar is a field representative. *)

  Lemma pow8_85_eq : 8 ^ Z.of_nat 85 = 8 ^ 85.
  Proof. reflexivity. Qed.

  Lemma pow8_22_eq : 8 ^ Z.of_nat 22 = 8 ^ 22.
  Proof. reflexivity. Qed.

  Lemma pallas_q_lt_pow8 : Primes.pallas_q < 8 ^ 85.
  Proof. unfold Primes.pallas_q, Primes.t_q. lia. Qed.

  Lemma pallas_p_lt_pow8 : Primes.pallas_p < 8 ^ 85.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma pow64_lt_pow8_22 : 2 ^ 64 < 8 ^ 22.
  Proof. lia. Qed.

  Lemma le_85_85 : (85 <= 85)%nat.
  Proof. apply le_n. Qed.

  Lemma le_22_85 : (22 <= 85)%nat.
  Proof. lia. Qed.

  Lemma wt_v_old (w : HonestInput) (H : well_typed w) :
    0 <= hi_v_old w < 2 ^ 64.
  Proof. destruct H as (H & _). exact H. Qed.

  Lemma wt_v_new (w : HonestInput) (H : well_typed w) :
    0 <= hi_v_new w < 2 ^ 64.
  Proof. destruct H as (_ & H & _). exact H. Qed.

  Lemma wt_alpha (w : HonestInput) (H : well_typed w) :
    0 <= hi_alpha w < Primes.pallas_q.
  Proof. destruct H as (_ & _ & H & _). exact H. Qed.

  Lemma wt_rcv (w : HonestInput) (H : well_typed w) :
    0 <= hi_rcv w < Primes.pallas_q.
  Proof. destruct H as (_ & _ & _ & H & _). exact H. Qed.

  Lemma wt_rcm_old (w : HonestInput) (H : well_typed w) :
    0 <= hi_rcm_old w < Primes.pallas_q.
  Proof. destruct H as (_ & _ & _ & _ & H & _). exact H. Qed.

  Lemma wt_rcm_new (w : HonestInput) (H : well_typed w) :
    0 <= hi_rcm_new w < Primes.pallas_q.
  Proof. destruct H as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

  Lemma wt_rivk (w : HonestInput) (H : well_typed w) :
    0 <= hi_rivk w < Primes.pallas_q.
  Proof. destruct H as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

  Lemma wt_ak (w : HonestInput) (H : well_typed w) : point_ok (hi_ak w).
  Proof.
    destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
    exact H.
  Qed.

  Lemma q_range (k : Z) (H : 0 <= k < Primes.pallas_q) :
    0 <= k < 8 ^ Z.of_nat 85.
  Proof. rewrite pow8_85_eq. pose proof pallas_q_lt_pow8. lia. Qed.

  Lemma magnitude_range (w : HonestInput) (Hty : well_typed w) :
    0 <= magnitude w < 8 ^ Z.of_nat 22.
  Proof.
    pose proof (wt_v_old w Hty) as H1.
    pose proof (wt_v_new w Hty) as H2.
    pose proof pow64_lt_pow8_22 as H3.
    rewrite pow8_22_eq.
    unfold magnitude.
    clear -H1 H2 H3. lia.
  Qed.

  Lemma nscalar_shape (w : HonestInput) :
    t_nullifier_scalar (tables_of w) = t_hash2 (tables_of w) +F hi_psi_old w.
  Proof. cbn [tables_of t_nullifier_scalar t_hash2]. reflexivity. Qed.

  Lemma nscalar_range (w : HonestInput) :
    0 <= t_nullifier_scalar (tables_of w) < 8 ^ Z.of_nat 85.
  Proof.
    rewrite nscalar_shape, pow8_85_eq.
    pose proof pallas_p_lt_pow8 as Hp.
    assert (Hpos : 0 < Primes.pallas_p)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    unfold BinOp.add.
    pose proof (Z.mod_pos_bound
      (t_hash2 (tables_of w) + hi_psi_old w) Primes.pallas_p Hpos) as Hb.
    clear -Hp Hb. lia.
  Qed.

  (** ** The seven leg sums

      Each hoisted leg point is the protocol's fixed-base multiple of its
      scalar. *)

  Lemma sa_comm_repr (w : HonestInput) (Hty : well_typed w) :
    t_sa_comm (tables_of w) =
    OrchardProtocolSpec.mul_spend_auth_g (hi_alpha w).
  Proof.
    rewrite t_sa_comm_eq, t_sa_leg_eq.
    unfold OrchardProtocolSpec.mul_spend_auth_g.
    apply (leg_sum_repr PallasGenerators.spend_auth_g_G
      PallasGenerators.spend_auth_g_on_curve
      PallasGenerators.spend_auth_g_reduced
      PallasGenerators.spend_auth_g_ne_identity
      PallasGeneratorsOrder.spend_auth_g_order
      83%nat le_85_85
      OrchardAdviceEccMuls.tbl_spend_auth sa_tbl_len
      SpendAuthGWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (FixedBaseLadder.spend_auth_g_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact sa_root_bridge.
    - exact (q_range _ (wt_alpha w Hty)).
  Qed.

  Lemma vcr_pt_repr (w : HonestInput) (Hty : well_typed w) :
    t_vcr_pt (tables_of w) =
    OrchardProtocolSpec.mul_value_commit_r (hi_rcv w).
  Proof.
    rewrite t_vcr_pt_eq, t_vcr_leg_eq.
    unfold OrchardProtocolSpec.mul_value_commit_r.
    apply (leg_sum_repr PallasGenerators.value_commit_r_G
      PallasGenerators.value_commit_r_on_curve
      PallasGenerators.value_commit_r_reduced
      PallasGenerators.value_commit_r_ne_identity
      PallasGeneratorsOrder.value_commit_r_order
      83%nat le_85_85
      OrchardAdviceEccMuls.tbl_value_commit_r vcr_tbl_len
      ValueCommitRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (ValueCommitRLadder.value_commit_r_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact vcr_root_bridge.
    - exact (q_range _ (wt_rcv w Hty)).
  Qed.

  Lemma vcv_mul_repr (w : HonestInput) (Hty : well_typed w) :
    t_vcv_mul (tables_of w) =
    OrchardProtocolSpec.mul_value_commit_v (magnitude w).
  Proof.
    rewrite t_vcv_mul_eq, t_vcv_leg_eq.
    unfold OrchardProtocolSpec.mul_value_commit_v.
    apply (leg_sum_repr PallasGenerators.value_commit_v_G
      PallasGenerators.value_commit_v_on_curve
      PallasGenerators.value_commit_v_reduced
      PallasGenerators.value_commit_v_ne_identity
      PallasGeneratorsOrder.value_commit_v_order
      20%nat le_22_85
      OrchardAdviceEccMuls.tbl_value_commit_v vcv_tbl_len
      ValueCommitVWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (ValueCommitVLadder.value_commit_v_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact vcv_root_bridge.
    - exact (magnitude_range w Hty).
  Qed.

  Lemma nk_prod_repr (w : HonestInput) :
    t_nk_prod (tables_of w) =
    OrchardProtocolSpec.mul_nullifier_k (t_nullifier_scalar (tables_of w)).
  Proof.
    rewrite t_nk_prod_eq, t_nk_leg_shape.
    unfold OrchardProtocolSpec.mul_nullifier_k.
    apply (leg_sum_repr PallasGenerators.nullifier_k_G
      PallasGenerators.nullifier_k_on_curve
      PallasGenerators.nullifier_k_reduced
      PallasGenerators.nullifier_k_ne_identity
      PallasGeneratorsOrder.nullifier_k_order
      83%nat le_85_85
      OrchardAdvicePoseidonNullifier.nk_table nk_tbl_len
      NullifierKWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (NullifierKLadder.nullifier_k_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact nk_root_bridge.
    - exact (nscalar_range w).
  Qed.

  Lemma nco_pt_repr (w : HonestInput) (Hty : well_typed w) :
    t_nco_pt (tables_of w) =
    OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w).
  Proof.
    rewrite t_nco_pt_eq, t_nco_leg_eq.
    unfold OrchardProtocolSpec.mul_note_commit_r.
    apply (leg_sum_repr PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      PallasGenerators.note_commit_r_ne_identity
      PallasGeneratorsOrder.note_commit_r_order
      83%nat le_85_85
      OrchardAdviceEccMuls.tbl_note_commit_r ncr_tbl_len
      NoteCommitRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (NoteCommitRLadder.note_commit_r_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact ncr_root_bridge.
    - exact (q_range _ (wt_rcm_old w Hty)).
  Qed.

  Lemma ncn_pt_repr (w : HonestInput) (Hty : well_typed w) :
    t_ncn_pt (tables_of w) =
    OrchardProtocolSpec.mul_note_commit_r (hi_rcm_new w).
  Proof.
    rewrite t_ncn_pt_eq, t_ncn_leg_eq.
    unfold OrchardProtocolSpec.mul_note_commit_r.
    apply (leg_sum_repr PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      PallasGenerators.note_commit_r_ne_identity
      PallasGeneratorsOrder.note_commit_r_order
      83%nat le_85_85
      OrchardAdviceEccMuls.tbl_note_commit_r ncr_tbl_len
      NoteCommitRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (NoteCommitRLadder.note_commit_r_fixed_window_point_x_eq_mul
        wi d u Hwi Hd).
    - exact ncr_root_bridge.
    - exact (q_range _ (wt_rcm_new w Hty)).
  Qed.

  Lemma civkr_pt_repr (w : HonestInput) (Hty : well_typed w) :
    t_civkr_pt (tables_of w) =
    OrchardProtocolSpec.mul_commit_ivk_r (hi_rivk w).
  Proof.
    rewrite t_civkr_pt_eq, t_civkr_leg_eq.
    unfold OrchardProtocolSpec.mul_commit_ivk_r.
    apply (leg_sum_repr PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced
      PallasGenerators.commit_ivk_r_ne_identity
      PallasGeneratorsOrder.commit_ivk_r_order
      83%nat le_85_85
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params) civkr_tbl_len
      CommitIvkRWindowSignCert.root_table).
    - intros wi d u Hwi Hd.
      exact (civkr_x_bridge wi d u Hwi Hd).
    - exact civkr_root_bridge.
    - exact (q_range _ (wt_rivk w Hty)).
  Qed.

  (** ** Commutativity of the complete addition on good points

      Both summands are [repr]s of reduced on-curve Weierstrass points, so
      the chip's complete addition is the [repr] of the group addition,
      which is commutative. *)

  Lemma wgood_comm (P Q : Point.t) (HP : wgood P) (HQ : wgood Q) :
    EccSpec.point_add P Q = EccSpec.point_add Q P.
  Proof.
    destruct HP as (Pw & HPr & HPo & ->).
    destruct HQ as (Qw & HQr & HQo & ->).
    rewrite <- (pallas_repr_add Pw Qw HPr HQr HPo HQo).
    rewrite <- (pallas_repr_add Qw Pw HQr HPr HQo HPo).
    apply (f_equal PallasModel.repr).
    unfold Pallas.add.
    exact (Weierstrass.add_comm Pallas.a Pallas.b Pw Qw HPo HQo).
  Qed.

  Lemma mul_wgood (G : Pallas.point) (k : Z)
      (Hr : Pallas.reduced G) (Ho : Pallas.on_curve G) :
    wgood (PallasModel.repr (Pallas.mul k G)).
  Proof. exact (wgood_repr_mul G k Hr Ho). Qed.

  Lemma nc_old_hash_out_wgood (w : HonestInput) (Hnd : nondegenerate w) :
    wgood (hd_out (t_nc_old_hash (tables_of w))).
  Proof.
    destruct Hnd as (_ & Hnc & _).
    rewrite t_nc_old_hash_eq.
    apply pt_affine_wgood.
    exact (note_commit_hash_out_affine _ _ _ _ _ Hnc).
  Qed.

  Lemma cm_old_wgood (w : HonestInput) (Hnd : nondegenerate w) :
    wgood (t_cm_old (tables_of w)).
  Proof.
    rewrite t_cm_old_eq.
    apply wgood_point_add.
    - exact (nc_old_hash_out_wgood w Hnd).
    - unfold OrchardProtocolSpec.mul_note_commit_r.
      exact (mul_wgood _ _ PallasGenerators.note_commit_r_reduced
        PallasGenerators.note_commit_r_on_curve).
  Qed.

  Lemma nk_prod_wgood (w : HonestInput) : wgood (t_nk_prod (tables_of w)).
  Proof.
    rewrite nk_prod_repr.
    unfold OrchardProtocolSpec.mul_nullifier_k.
    exact (mul_wgood _ _ PallasGenerators.nullifier_k_reduced
      PallasGenerators.nullifier_k_on_curve).
  Qed.

  (** ** Shapes of the derived record fields

      Each equation reduces only the record builder and the projections it
      names, so the Sinsemilla, Poseidon and ladder folds the fields carry
      stay stuck (docs/compile-performance.md). *)

  Lemma t_nf_spec_shape (w : HonestInput) :
    t_nf_spec (tables_of w) =
    EccSpec.extract_x
      (EccSpec.point_add
        (OrchardProtocolSpec.mul_nullifier_k (t_nullifier_scalar (tables_of w)))
        (t_cm_old (tables_of w))).
  Proof.
    cbn [tables_of t_nf_spec t_nullifier_scalar t_cm_old]. reflexivity.
  Qed.

  Lemma t_ivk_shape (w : HonestInput) :
    t_ivk (tables_of w) =
    EccSpec.extract_x
      (EccSpec.point_add (hd_out (t_civk_hash (tables_of w)))
        (OrchardProtocolSpec.mul_commit_ivk_r (hi_rivk w))).
  Proof. cbn [tables_of t_ivk t_civk_hash]. reflexivity. Qed.

  Lemma t_cmx_spec_shape (w : HonestInput) :
    t_cmx_spec (tables_of w) =
    EccSpec.extract_x
      (EccSpec.point_add (hd_out (t_nc_new_hash (tables_of w)))
        (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_new w))).
  Proof. cbn [tables_of t_cmx_spec t_nc_new_hash]. reflexivity. Qed.

  Lemma t_cv_spec_shape (w : HonestInput) :
    t_cv_spec (tables_of w) =
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value (magnitude w) (sign w))
      (hi_rcv w).
  Proof. cbn [tables_of t_cv_spec]. reflexivity. Qed.

  Lemma t_rk_spec_shape (w : HonestInput) :
    t_rk_spec (tables_of w) =
    OrchardProtocolSpec.spend_auth_randomize (hi_ak w) (hi_alpha w).
  Proof. cbn [tables_of t_rk_spec]. reflexivity. Qed.

  (** ** The sign-adjusted value-commitment summand

      The most-significant-word region negates the magnitude multiple's
      ordinate on a negative net value, which is the [repr] of the negated
      group multiple. *)

  Lemma repr_point_neg (Pw : Pallas.point) :
    point_neg (PallasModel.repr Pw) = PallasModel.repr (Pallas.neg Pw).
  Proof. destruct Pw; reflexivity. Qed.

  Lemma vcv_point_repr (w : HonestInput) (Hty : well_typed w) :
    vcv_point_t w (tables_of w) =
    OrchardProtocolSpec.mul_value_commit_v
      (OrchardProtocolSpec.signed_net_value (magnitude w) (sign w)).
  Proof.
    unfold vcv_point_t, vcv_y_var_t, OrchardProtocolSpec.signed_net_value.
    rewrite (vcv_mul_repr w Hty).
    destruct (sign w =? 1).
    - apply FixedBaseLadder.point_eq; reflexivity.
    - unfold OrchardProtocolSpec.mul_value_commit_v.
      rewrite (pallas_mul_neg (magnitude w) PallasGenerators.value_commit_v_G
        PallasGenerators.value_commit_v_reduced).
      rewrite <- repr_point_neg.
      unfold point_neg.
      reflexivity.
  Qed.

  (** ** The four commitment identities *)

  Lemma cv_point_eq (w : HonestInput) (Hty : well_typed w) :
    EccSpec.point_add (vcv_point_t w (tables_of w)) (t_vcr_pt (tables_of w)) =
    t_cv_spec (tables_of w).
  Proof.
    rewrite (vcv_point_repr w Hty), (vcr_pt_repr w Hty), t_cv_spec_shape.
    unfold OrchardProtocolSpec.value_commit,
      OrchardProtocolSpec.mul_value_commit_v,
      OrchardProtocolSpec.mul_value_commit_r.
    symmetry.
    apply pallas_repr_add.
    - exact (pallas_mul_reduced _ _ PallasGenerators.value_commit_v_reduced).
    - exact (pallas_mul_reduced _ _ PallasGenerators.value_commit_r_reduced).
    - exact (pallas_mul_on_curve _ _ PallasGenerators.value_commit_v_on_curve).
    - exact (pallas_mul_on_curve _ _ PallasGenerators.value_commit_r_on_curve).
  Qed.

  Lemma rk_point_eq (w : HonestInput) (Hty : well_typed w) :
    EccSpec.point_add (t_sa_comm (tables_of w)) (hi_ak w) =
    t_rk_spec (tables_of w).
  Proof.
    rewrite t_rk_spec_shape.
    unfold OrchardProtocolSpec.spend_auth_randomize.
    rewrite (sa_comm_repr w Hty).
    apply wgood_comm.
    - unfold OrchardProtocolSpec.mul_spend_auth_g.
      exact (mul_wgood _ _ PallasGenerators.spend_auth_g_reduced
        PallasGenerators.spend_auth_g_on_curve).
    - exact (wgood_of_point_ok _ (wt_ak w Hty)).
  Qed.

  Lemma nf_point_eq (w : HonestInput) (Hnd : nondegenerate w) :
    Point.x
      (EccSpec.point_add (t_cm_old (tables_of w)) (t_nk_prod (tables_of w))) =
    t_nf_spec (tables_of w).
  Proof.
    rewrite t_nf_spec_shape, <- nk_prod_repr.
    unfold EccSpec.extract_x.
    exact (f_equal Point.x
      (wgood_comm _ _ (cm_old_wgood w Hnd) (nk_prod_wgood w))).
  Qed.

  Lemma ivk_point_eq (w : HonestInput) (Hty : well_typed w) :
    t_ivk (tables_of w) =
    Point.x
      (EccSpec.point_add (hd_out (t_civk_hash (tables_of w)))
        (t_civkr_pt (tables_of w))).
  Proof. rewrite t_ivk_shape, (civkr_pt_repr w Hty). reflexivity. Qed.

  Lemma cm_old_point_eq (w : HonestInput) (Hty : well_typed w) :
    EccSpec.point_add (hd_out (t_nc_old_hash (tables_of w)))
      (t_nco_pt (tables_of w)) =
    t_cm_old (tables_of w).
  Proof. rewrite t_cm_old_eq, (nco_pt_repr w Hty). reflexivity. Qed.

  Lemma cmx_point_eq (w : HonestInput) (Hty : well_typed w) :
    Point.x
      (EccSpec.point_add (hd_out (t_nc_new_hash (tables_of w)))
        (t_ncn_pt (tables_of w))) =
    t_cmx_spec (tables_of w).
  Proof. rewrite t_cmx_spec_shape, (ncn_pt_repr w Hty). reflexivity. Qed.

  Lemma nk_acc0 (w : HonestInput) :
    leg_acc (t_nk_leg (tables_of w)) 0 = leg_pt (t_nk_leg (tables_of w)) 0.
  Proof.
    rewrite t_nk_leg_shape.
    apply leg_acc_zero.
    rewrite nk_tbl_len.
    apply Nat.lt_0_succ.
  Qed.

  (** ** The fact literals

      The twelve entries of [nt_open] this group owns, in increasing index
      order (indices 2, 3, 7, 8, 11, 12, 13, 27, 62, 63, 89, 95). *)

  Definition orchardwitnessfixedlegs_facts : list (Fact.t columns RegionId.t) := [
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 1;
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 2;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 0 |};
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 3;
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 4;
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 5;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.CmOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.CmOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 1 |};
    Fact.InstanceIs {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 1 |} Instance_.Primary 6
  ].

  (** ** The cell readings

      Each address's reader, read off by definitional equality (the
      [cmold_read] shape of [forward/lookups_witness.v]). *)

  Lemma read_vc_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (vcv_point_t w (tables_of w))
      (t_vcr_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_vc_cpa_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd) 1 =
    Point.y (EccSpec.point_add (vcv_point_t w (tables_of w))
      (t_vcr_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_nk_acc0_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 =
    Point.x (leg_acc (t_nk_leg (tables_of w)) 0).
  Proof. reflexivity. Qed.

  Lemma read_nk_acc0_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 =
    Point.y (leg_acc (t_nk_leg (tables_of w)) 0).
  Proof. reflexivity. Qed.

  Lemma read_nk_pt0_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0 =
    Point.x (leg_pt (t_nk_leg (tables_of w)) 0).
  Proof. reflexivity. Qed.

  Lemma read_nk_pt0_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0 =
    Point.y (leg_pt (t_nk_leg (tables_of w)) 0).
  Proof. reflexivity. Qed.

  Lemma read_nf_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.Nullifier RegionId.Nullifier.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (t_cm_old (tables_of w))
      (t_nk_prod (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_sa_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (t_sa_comm (tables_of w)) (hi_ak w)).
  Proof. reflexivity. Qed.

  Lemma read_sa_cpa_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd) 1 =
    Point.y (EccSpec.point_add (t_sa_comm (tables_of w)) (hi_ak w)).
  Proof. reflexivity. Qed.

  Lemma read_overflow_alpha (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowCheck)) 1 =
    t_ivk (tables_of w).
  Proof. reflexivity. Qed.

  Lemma read_civk_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (hd_out (t_civk_hash (tables_of w)))
      (t_civkr_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_nco_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (hd_out (t_nc_old_hash (tables_of w)))
      (t_nco_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_nco_cpa_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 1 =
    Point.y (EccSpec.point_add (hd_out (t_nc_old_hash (tables_of w)))
      (t_nco_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_cm_old_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 =
    Point.x (t_cm_old (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_cm_old_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 =
    Point.y (t_cm_old (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_rho_new (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputRho) 0 =
    t_nf_spec (tables_of w).
  Proof. reflexivity. Qed.

  Lemma read_ncn_cpa_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 1 =
    Point.x (EccSpec.point_add (hd_out (t_nc_new_hash (tables_of w)))
      (t_ncn_pt (tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_inst_1 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 1 =
    Point.x (t_cv_spec (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_inst_2 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 2 =
    Point.y (t_cv_spec (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_inst_3 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 3 =
    t_nf_spec (tables_of w).
  Proof. reflexivity. Qed.

  Lemma read_inst_4 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 4 =
    Point.x (t_rk_spec (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_inst_5 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 5 =
    Point.y (t_rk_spec (tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_inst_6 (w : HonestInput) :
    (Γw w).(Assignment.instance_) Instance_.Primary 6 =
    t_cmx_spec (tables_of w).
  Proof. reflexivity. Qed.

  (** ** The twelve facts *)

  Lemma fact_vc_x (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 1.
  Proof.
    rewrite read_vc_cpa_x, read_inst_1.
    exact (f_equal Point.x (cv_point_eq w Hty)).
  Qed.

  Lemma fact_vc_y (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 2.
  Proof.
    rewrite read_vc_cpa_y, read_inst_2.
    exact (f_equal Point.y (cv_point_eq w Hty)).
  Qed.

  Lemma fact_nk_acc0_x (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 =
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0.
  Proof.
    rewrite read_nk_acc0_x, read_nk_pt0_x.
    exact (f_equal Point.x (nk_acc0 w)).
  Qed.

  Lemma fact_nk_acc0_y (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 =
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0.
  Proof.
    rewrite read_nk_acc0_y, read_nk_pt0_y.
    exact (f_equal Point.y (nk_acc0 w)).
  Qed.

  Lemma fact_nf (w : HonestInput) (Hnd : nondegenerate w) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.Nullifier RegionId.Nullifier.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 3.
  Proof.
    rewrite read_nf_cpa_x, read_inst_3.
    exact (nf_point_eq w Hnd).
  Qed.

  Lemma fact_rk_x (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 4.
  Proof.
    rewrite read_sa_cpa_x, read_inst_4.
    exact (f_equal Point.x (rk_point_eq w Hty)).
  Qed.

  Lemma fact_rk_y (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 5.
  Proof.
    rewrite read_sa_cpa_y, read_inst_5.
    exact (f_equal Point.y (rk_point_eq w Hty)).
  Qed.

  Lemma fact_ivk (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowCheck)) 1 =
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) 1.
  Proof.
    rewrite read_overflow_alpha, read_civk_cpa_x.
    exact (ivk_point_eq w Hty).
  Qed.

  Lemma fact_cm_old_x (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 1 =
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0.
  Proof.
    rewrite read_nco_cpa_x, read_cm_old_x.
    exact (f_equal Point.x (cm_old_point_eq w Hty)).
  Qed.

  Lemma fact_cm_old_y (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.CompletePointAdd) 1 =
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0.
  Proof.
    rewrite read_nco_cpa_y, read_cm_old_y.
    exact (f_equal Point.y (cm_old_point_eq w Hty)).
  Qed.

  Lemma fact_rho_new (w : HonestInput) (Hnd : nondegenerate w) :
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputRho) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.Nullifier RegionId.Nullifier.CompletePointAdd) 1.
  Proof.
    rewrite read_rho_new, read_nf_cpa_x.
    exact (eq_sym (nf_point_eq w Hnd)).
  Qed.

  Lemma fact_cmx (w : HonestInput) (Hty : well_typed w) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.CompletePointAdd) 1 =
    (Γw w).(Assignment.instance_) Instance_.Primary 6.
  Proof.
    rewrite read_ncn_cpa_x, read_inst_6.
    exact (cmx_point_eq w Hty).
  Qed.

  (** ** The group export *)

  Lemma orchardwitnessfixedlegs_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) :
    interpret_facts (OrchardHonestAssignment.honest_assignment w)
      orchardwitnessfixedlegs_facts.
  Proof.
    pose proof (proj1 Hv) as Hty.
    unfold orchardwitnessfixedlegs_facts.
    cbn [interpret_facts interpret_fact eval_cell
         Cell.column Cell.region Cell.row_offset].
    repeat apply conj.
    - exact (fact_vc_x w Hty).
    - exact (fact_vc_y w Hty).
    - exact (fact_nk_acc0_x w).
    - exact (fact_nk_acc0_y w).
    - exact (fact_nf w Hnd).
    - exact (fact_rk_x w Hty).
    - exact (fact_rk_y w Hty).
    - exact (fact_ivk w Hty).
    - exact (fact_cm_old_x w Hty).
    - exact (fact_cm_old_y w Hty).
    - exact (fact_rho_new w Hnd).
    - exact (fact_cmx w Hty).
    - exact I.
  Qed.

End OrchardWitnessFixedLegs.
