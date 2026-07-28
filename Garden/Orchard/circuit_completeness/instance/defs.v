(** * Definitions for the concrete Orchard completeness instance

    The shared definitions of the completeness-instance certificate: the
    concrete honest input [test_input], the Boolean forms of the
    completeness-domain predicates ([valid_b], [nondegenerate_b]) with their
    soundness lemmas, the generated assignment [Γtest], and the per-point
    checker [check_point] with its region-family shard partition, and the
    pinned read-back value [test_action_inputs].  The [vm_compute]
    certificates over these definitions live in the sibling leaf files,
    grouped by the heavy computation they share rather than by subject:
    everything reading [Γtest] in [instance/certs.v], everything reading
    [test_input] in [instance/domain.v] and [instance/read.v].
    [instance/cert.v] joins them into the instance theorem.

    The nondegeneracy checkers are linear: each Sinsemilla clause folds the
    accumulator through the message once ([sins_nondeg_go]), the Merkle
    clause threads the running node through the 32 layers
    ([merkle_nondeg_go]), and the variable-base clause threads the ladder
    accumulator through the 251 bit indices ([mul_chain_go]), instead of
    recomputing per-round hash prefixes or per-index scalar multiples — the
    per-read recomputation pitfall of [docs/compile-performance.md]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompletenessInstanceDefs.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.

  (** ** The concrete honest input

      Small in-range scalars; every point is a small multiple of the on-curve
      base [affine (-1) 2] (the shared placeholder generator, order [q]), so
      on-curve/reduced/non-identity hold by computation.  [pk_d_old] is
      [[ivk] g_d_old] with [ivk = Commit^ivk_rivk(ak_x, nk)], making
      'Diversified address integrity' true by construction.  [v_old = 2],
      [v_new = 1]: both enable flags are exercised, and the active-spend
      branch ([v_old <> 0]) forces Merkle path validity against the computed
      anchor. *)

  Definition test_base : Pallas.point := Pallas.affine (-1) 2.

  Definition test_g_d_old : Point.t :=
    PallasModel.repr (Pallas.mul 3 test_base).
  Definition test_ak : Point.t :=
    PallasModel.repr (Pallas.mul 5 test_base).
  Definition test_g_d_new : Point.t :=
    PallasModel.repr (Pallas.mul 7 test_base).
  Definition test_pk_d_new : Point.t :=
    PallasModel.repr (Pallas.mul 11 test_base).
  Definition test_nk : Z := 11.
  Definition test_rivk : Z := 8.
  Definition test_ivk : Z :=
    OrchardProtocolSpec.commit_ivk orchard_circuit_params
      (EccSpec.extract_x test_ak) test_nk test_rivk.
  Definition test_pk_d_old : Point.t :=
    PallasModel.repr (Pallas.mul test_ivk (PallasModel.unrepr test_g_d_old)).

  Definition test_input : HonestInput := {|
    hi_path := List.map Z.of_nat (List.seq 1 32);
    hi_pos := 5;
    hi_g_d_old := test_g_d_old;
    hi_pk_d_old := test_pk_d_old;
    hi_v_old := 2;
    hi_rho_old := 12;
    hi_psi_old := 13;
    hi_rcm_old := 9;
    hi_alpha := 6;
    hi_ak := test_ak;
    hi_nk := test_nk;
    hi_rivk := test_rivk;
    hi_g_d_new := test_g_d_new;
    hi_pk_d_new := test_pk_d_new;
    hi_v_new := 1;
    hi_psi_new := 14;
    hi_rcm_new := 10;
    hi_rcv := 4;
    hi_anchor_public := 0;
    hi_enable_spends := 1;
    hi_enable_outputs := 1;
  |}.

  (** ** Boolean forms of the completeness-domain predicates

      [valid_b] / [nondegenerate_b] mirror [OrchardWitnessInput.valid] /
      [nondegenerate] as computable checks, with soundness lemmas into the
      [Prop] forms, so the concrete instance discharges by one [vm_compute]
      each. *)

  Definition range_b (x bound : Z) : bool := (0 <=? x) && (x <? bound).

  Lemma range_b_sound (x bound : Z) :
    range_b x bound = true -> 0 <= x < bound.
  Proof.
    unfold range_b.
    intros Hrange.
    apply Bool.andb_true_iff in Hrange.
    destruct Hrange as [Hlow Hhigh].
    apply Z.leb_le in Hlow.
    apply Z.ltb_lt in Hhigh.
    exact (conj Hlow Hhigh).
  Qed.

  Definition flag_b (x : Z) : bool := (x =? 0) || (x =? 1).

  Lemma flag_b_sound (x : Z) :
    flag_b x = true -> x = 0 \/ x = 1.
  Proof.
    unfold flag_b.
    intros Hflag.
    apply Bool.orb_true_iff in Hflag.
    destruct Hflag as [Hflag | Hflag]; [left | right];
      apply Z.eqb_eq in Hflag; exact Hflag.
  Qed.

  Definition point_t_eqb (P Q : Point.t) : bool :=
    (Point.x P =? Point.x Q) && (Point.y P =? Point.y Q).

  Lemma point_t_eqb_eq (P Q : Point.t) :
    point_t_eqb P Q = true -> P = Q.
  Proof.
    destruct P as [xP yP], Q as [xQ yQ].
    unfold point_t_eqb; cbn.
    intros Heq.
    apply Bool.andb_true_iff in Heq.
    destruct Heq as [Hx Hy].
    apply Z.eqb_eq in Hx.
    apply Z.eqb_eq in Hy.
    subst; reflexivity.
  Qed.

  Lemma point_t_eqb_refl (P : Point.t) :
    point_t_eqb P P = true.
  Proof.
    unfold point_t_eqb.
    rewrite !Z.eqb_refl.
    reflexivity.
  Qed.

  Definition pallas_reduced_b (P : Pallas.point) : bool :=
    match P with
    | Weierstrass.Infinity => true
    | Weierstrass.Affine x y => (UnOp.from x =? x) && (UnOp.from y =? y)
    end.

  Lemma pallas_reduced_b_sound (P : Pallas.point) :
    pallas_reduced_b P = true -> Pallas.reduced P.
  Proof.
    unfold Pallas.reduced, Weierstrass.reduced, pallas_reduced_b.
    destruct P as [| x y]; intros Hred.
    - exact I.
    - apply Bool.andb_true_iff in Hred.
      destruct Hred as [Hx Hy].
      apply Z.eqb_eq in Hx.
      apply Z.eqb_eq in Hy.
      exact (conj Hx Hy).
  Qed.

  Definition pallas_on_curve_b (P : Pallas.point) : bool :=
    match P with
    | Weierstrass.Infinity => true
    | Weierstrass.Affine x y =>
        UnOp.from (y *F y) =?
        UnOp.from (x *F x *F x +F Pallas.a *F x +F Pallas.b)
    end.

  Lemma pallas_on_curve_b_sound (P : Pallas.point) :
    pallas_on_curve_b P = true -> Pallas.on_curve P.
  Proof.
    unfold Pallas.on_curve, Weierstrass.on_curve, pallas_on_curve_b.
    destruct P as [| x y]; intros Hcurve.
    - exact I.
    - apply Z.eqb_eq in Hcurve.
      exact Hcurve.
  Qed.

  Definition point_ok_b (P : Point.t) : bool :=
    pallas_reduced_b (PallasModel.unrepr P) &&
    pallas_on_curve_b (PallasModel.unrepr P) &&
    negb (point_t_eqb P EccSpec.identity).

  Lemma point_ok_b_sound (P : Point.t) :
    point_ok_b P = true -> point_ok P.
  Proof.
    unfold point_ok_b, point_ok.
    intros Hok.
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok Hident].
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hred Hcurve].
    split; [exact (pallas_reduced_b_sound _ Hred) |].
    split; [exact (pallas_on_curve_b_sound _ Hcurve) |].
    intros Heq.
    subst P.
    rewrite point_t_eqb_refl in Hident.
    discriminate.
  Qed.

  Definition well_typed_b (w : HonestInput) : bool :=
    range_b (hi_v_old w) (2 ^ 64) &&
    range_b (hi_v_new w) (2 ^ 64) &&
    range_b (hi_alpha w) Primes.pallas_q &&
    range_b (hi_rcv w) Primes.pallas_q &&
    range_b (hi_rcm_old w) Primes.pallas_q &&
    range_b (hi_rcm_new w) Primes.pallas_q &&
    range_b (hi_rivk w) Primes.pallas_q &&
    range_b (hi_nk w) Primes.pallas_p &&
    range_b (hi_rho_old w) Primes.pallas_p &&
    range_b (hi_psi_old w) Primes.pallas_p &&
    range_b (hi_psi_new w) Primes.pallas_p &&
    range_b (hi_anchor_public w) Primes.pallas_p &&
    point_ok_b (hi_ak w) &&
    point_ok_b (hi_g_d_old w) &&
    point_ok_b (hi_pk_d_old w) &&
    point_ok_b (hi_g_d_new w) &&
    point_ok_b (hi_pk_d_new w) &&
    Nat.eqb (List.length (hi_path w)) 32 &&
    List.forallb (fun s => range_b s Primes.pallas_p) (hi_path w) &&
    range_b (hi_pos w) (2 ^ 32) &&
    flag_b (hi_enable_spends w) &&
    flag_b (hi_enable_outputs w).

  Lemma well_typed_b_sound (w : HonestInput) :
    well_typed_b w = true -> well_typed w.
  Proof.
    unfold well_typed_b.
    intros H.
    apply Bool.andb_true_iff in H; destruct H as [H Hflag_out].
    apply Bool.andb_true_iff in H; destruct H as [H Hflag_sp].
    apply Bool.andb_true_iff in H; destruct H as [H Hpos].
    apply Bool.andb_true_iff in H; destruct H as [H Hpath_range].
    apply Bool.andb_true_iff in H; destruct H as [H Hpath_len].
    apply Bool.andb_true_iff in H; destruct H as [H Hpk_new].
    apply Bool.andb_true_iff in H; destruct H as [H Hg_new].
    apply Bool.andb_true_iff in H; destruct H as [H Hpk_old].
    apply Bool.andb_true_iff in H; destruct H as [H Hg_old].
    apply Bool.andb_true_iff in H; destruct H as [H Hak].
    apply Bool.andb_true_iff in H; destruct H as [H Hanchor].
    apply Bool.andb_true_iff in H; destruct H as [H Hpsi_new].
    apply Bool.andb_true_iff in H; destruct H as [H Hpsi_old].
    apply Bool.andb_true_iff in H; destruct H as [H Hrho].
    apply Bool.andb_true_iff in H; destruct H as [H Hnk].
    apply Bool.andb_true_iff in H; destruct H as [H Hrivk].
    apply Bool.andb_true_iff in H; destruct H as [H Hrcm_new].
    apply Bool.andb_true_iff in H; destruct H as [H Hrcm_old].
    apply Bool.andb_true_iff in H; destruct H as [H Hrcv].
    apply Bool.andb_true_iff in H; destruct H as [H Halpha].
    apply Bool.andb_true_iff in H; destruct H as [Hv_old Hv_new].
    unfold well_typed.
    split; [exact (range_b_sound _ _ Hv_old) |].
    split; [exact (range_b_sound _ _ Hv_new) |].
    split; [exact (range_b_sound _ _ Halpha) |].
    split; [exact (range_b_sound _ _ Hrcv) |].
    split; [exact (range_b_sound _ _ Hrcm_old) |].
    split; [exact (range_b_sound _ _ Hrcm_new) |].
    split; [exact (range_b_sound _ _ Hrivk) |].
    split; [exact (range_b_sound _ _ Hnk) |].
    split; [exact (range_b_sound _ _ Hrho) |].
    split; [exact (range_b_sound _ _ Hpsi_old) |].
    split; [exact (range_b_sound _ _ Hpsi_new) |].
    split; [exact (range_b_sound _ _ Hanchor) |].
    split; [exact (point_ok_b_sound _ Hak) |].
    split; [exact (point_ok_b_sound _ Hg_old) |].
    split; [exact (point_ok_b_sound _ Hpk_old) |].
    split; [exact (point_ok_b_sound _ Hg_new) |].
    split; [exact (point_ok_b_sound _ Hpk_new) |].
    split; [exact (proj1 (Nat.eqb_eq _ _) Hpath_len) |].
    split.
    { apply List.Forall_forall.
      intros s Hs.
      exact (range_b_sound _ _
        (proj1 (List.forallb_forall _ _) Hpath_range s Hs)). }
    split; [exact (range_b_sound _ _ Hpos) |].
    split; [exact (flag_b_sound _ Hflag_sp) |].
    exact (flag_b_sound _ Hflag_out).
  Qed.

  Definition valid_b (w : HonestInput) : bool :=
    well_typed_b w &&
    ((hi_v_old w =? 0) || (hi_enable_spends w =? 1)) &&
    ((hi_v_new w =? 0) || (hi_enable_outputs w =? 1)) &&
    point_t_eqb (hi_pk_d_old w)
      (PallasModel.repr
        (Pallas.mul (ivk w) (PallasModel.unrepr (hi_g_d_old w)))).

  Lemma valid_b_sound (w : HonestInput) :
    valid_b w = true -> valid w.
  Proof.
    unfold valid_b.
    intros H.
    apply Bool.andb_true_iff in H; destruct H as [H Hpk].
    apply Bool.andb_true_iff in H; destruct H as [H Hout].
    apply Bool.andb_true_iff in H; destruct H as [Hty Hsp].
    unfold valid.
    split; [exact (well_typed_b_sound w Hty) |].
    split.
    { apply Bool.orb_true_iff in Hsp.
      destruct Hsp as [Hsp | Hsp]; [left | right];
        apply Z.eqb_eq in Hsp; exact Hsp. }
    split.
    { apply Bool.orb_true_iff in Hout.
      destruct Hout as [Hout | Hout]; [left | right];
        apply Z.eqb_eq in Hout; exact Hout. }
    exact (point_t_eqb_eq _ _ Hpk).
  Qed.

  (** Reflection of a [forall] over a [nat] segment. *)
  Lemma forallb_seq_sound (f : nat -> bool) (start count : nat) :
    List.forallb f (List.seq start count) = true ->
    forall i : nat, (start <= i < start + count)%nat -> f i = true.
  Proof.
    intros Hall i Hi.
    rewrite List.forallb_forall in Hall.
    apply Hall.
    apply List.in_seq.
    lia.
  Qed.

  (** ** The linear Sinsemilla nondegeneracy checker

      One pass over the message, threading the accumulator: at each round the
      chord to the generator and the chord back to the accumulator are both
      non-vertical.  [vm_compute] cost: three incomplete additions per word,
      once — never a per-round prefix refold. *)
  Fixpoint sins_nondeg_go (acc : Point.t) (ws : list Z) : bool :=
    match ws with
    | [] => true
    | wd :: ws' =>
        let g := SinsemillaSpec.generator wd in
        let mid := EccSpec.point_add_incomplete acc g in
        negb (Point.x acc =? Point.x g) &&
        negb (Point.x acc =? Point.x mid) &&
        sins_nondeg_go (EccSpec.point_add_incomplete mid acc) ws'
    end.

  Lemma sins_nondeg_go_sound (ws : list Z) :
    forall acc : Point.t,
      sins_nondeg_go acc ws = true ->
      forall k : nat, (k < List.length ws)%nat ->
        let acck :=
          SinsemillaSpec.sinsemilla_hash_to_point acc (List.firstn k ws) in
        let wk := List.nth k ws 0 in
        Point.x acck <> Point.x (SinsemillaSpec.generator wk) /\
        Point.x acck <>
          Point.x (EccSpec.point_add_incomplete acck
            (SinsemillaSpec.generator wk)).
  Proof.
    induction ws as [| wd ws' IH]; intros acc Hgo k Hk.
    - cbn [List.length] in Hk. lia.
    - cbn [sins_nondeg_go] in Hgo.
      apply Bool.andb_true_iff in Hgo.
      destruct Hgo as [Hhead Hrest].
      apply Bool.andb_true_iff in Hhead.
      destruct Hhead as [Hchord1 Hchord2].
      apply Bool.negb_true_iff in Hchord1.
      apply Bool.negb_true_iff in Hchord2.
      apply Z.eqb_neq in Hchord1.
      apply Z.eqb_neq in Hchord2.
      destruct k as [| k'].
      + cbn [List.firstn List.nth SinsemillaSpec.sinsemilla_hash_to_point
          Stdlib.Lists.List.fold_left].
        exact (conj Hchord1 Hchord2).
      + cbn [List.length] in Hk.
        cbn [List.firstn List.nth].
        assert (Hfold :
          SinsemillaSpec.sinsemilla_hash_to_point acc
            (wd :: List.firstn k' ws') =
          SinsemillaSpec.sinsemilla_hash_to_point
            (SinsemillaSpec.round acc wd) (List.firstn k' ws'))
          by reflexivity.
        rewrite Hfold.
        exact (IH (SinsemillaSpec.round acc wd) Hrest k' ltac:(lia)).
  Qed.

  Lemma sins_nondeg_sound (Q : Point.t) (words : list Z) :
    sins_nondeg_go Q words = true ->
    SinsemillaHash.nondegenerate Q words.
  Proof.
    intros Hgo k Hk.
    exact (sins_nondeg_go_sound words Q Hgo k Hk).
  Qed.

  (** ** The linear Merkle-chain nondegeneracy checker

      Threads the running node through the 32 layers, checking each layer's
      hash with [sins_nondeg_go]. *)
  Definition merkle_words_node (w : HonestInput) (node : Z) (i : nat)
      : list Z :=
    let sibling := List.nth i (hi_path w) 0 in
    if path_bit w i
    then SinsemillaSpec.merkle_message (Z.of_nat i) sibling node
    else SinsemillaSpec.merkle_message (Z.of_nat i) node sibling.

  (** The chain fold is a higher-order fixpoint over abstract [step]/[check]
      functions, instantiated by a plain definition: a fixpoint body that
      references the [merkle_layer] constant chain directly stalls the
      compiler's end-of-file processing for minutes (see the pitfall entry in
      [docs/compile-performance.md]). *)
  Fixpoint chain_nondeg_go (step : Z -> nat -> Z) (check : Z -> nat -> bool)
      (node : Z) (i count : nat) : bool :=
    match count with
    | O => true
    | S count' =>
        check node i &&
        chain_nondeg_go step check (step node i) (S i) count'
    end.

  Definition merkle_step (w : HonestInput) (node : Z) (i : nat) : Z :=
    SinsemillaSpec.merkle_layer merkle_Q (Z.of_nat i) node
      (List.nth i (hi_path w) 0) (path_bit w i).

  Definition merkle_check (w : HonestInput) (node : Z) (i : nat) : bool :=
    sins_nondeg_go merkle_Q (merkle_words_node w node i).

  Definition merkle_nondeg_b (w : HonestInput) : bool :=
    chain_nondeg_go (merkle_step w) (merkle_check w) (leaf w) 0%nat 32%nat.

  Lemma merkle_words_node_eq (w : HonestInput) (i : nat) :
    merkle_words_node w (merkle_node w i) i = merkle_layer_words w i.
  Proof.
    unfold merkle_words_node, merkle_layer_words.
    destruct (path_bit w i); reflexivity.
  Qed.

  Lemma merkle_step_node (w : HonestInput) (i : nat) :
    (i < 32)%nat ->
    merkle_step w (merkle_node w i) i = merkle_node w (S i).
  Proof.
    intro Hi.
    unfold merkle_step.
    symmetry.
    exact (merkle_node_succ w i Hi).
  Qed.

  Lemma merkle_nondeg_go_sound (w : HonestInput) :
    forall (count i : nat),
      (i + count = 32)%nat ->
      chain_nondeg_go (merkle_step w) (merkle_check w)
        (merkle_node w i) i count = true ->
      forall j : nat, (i <= j < 32)%nat ->
        SinsemillaHash.nondegenerate merkle_Q (merkle_layer_words w j).
  Proof.
    induction count as [| count' IH]; intros i Hcount Hgo j Hj.
    - lia.
    - cbn [chain_nondeg_go] in Hgo.
      apply Bool.andb_true_iff in Hgo.
      destruct Hgo as [Hhead Hrest].
      destruct (Nat.eq_dec i j) as [<- | Hne].
      + unfold merkle_check in Hhead.
        rewrite merkle_words_node_eq in Hhead.
        exact (sins_nondeg_sound _ _ Hhead).
      + rewrite (merkle_step_node w i ltac:(lia)) in Hrest.
        exact (IH (S i) ltac:(lia) Hrest j ltac:(lia)).
  Qed.

  (** ** The variable-base mul nondegeneracy checker

      The accumulators form a chain: [mul_acc w i] is one double-and-add
      step from [mul_acc w (S i)].  Folding the chain once costs two group
      additions per bit index, where checking each index on its own costs a
      [Pallas.mul] over a [256 − i]-bit scalar — the per-read recomputation
      pitfall of [docs/compile-performance.md], at the range level.

      The fold runs on the group law ([Pallas.add]), where
      [VarBaseDefs.double_add_step_multiple] holds with no side condition
      beyond the base point being reduced and on-curve.  The
      incomplete-addition nondegeneracy the conjuncts assert is checked at
      every step, never assumed, so the chain certifies exactly the
      predicate a per-index scan does. *)
  Definition mul_multiple_at (k : Z) (i : nat) : Z :=
    2 ^ (255 - Z.of_nat i) + 2 * bit_running_sum k i + 1.

  Definition mul_step_point_at (k : Z) (B : Point.t) (i : nat) : Point.t :=
    if scalar_bit k i =? 1 then B else point_neg B.

  Definition mul_step_nondeg_at (k : Z) (B : Point.t) (Bp : Pallas.point)
      (i : nat) : Prop :=
    let acc := PallasModel.repr (Pallas.mul (mul_multiple_at k (S i)) Bp) in
    Point.x acc <> 0 /\
    Point.x acc <> Point.x B /\
    Point.x (EccSpec.point_add_incomplete acc (mul_step_point_at k B i)) <>
      Point.x acc.

  Definition mul_chain_step (Bp : Pallas.point) (k : Z) (i : nat)
      (acc : Pallas.point) : Pallas.point :=
    Pallas.add (Pallas.add acc (VarBaseDefs.signed_base Bp (scalar_bit k i)))
      acc.

  Definition mul_chain_check (B : Point.t) (k : Z) (i : nat)
      (acc : Pallas.point) : bool :=
    let a := PallasModel.repr acc in
    negb (Point.x a =? 0) &&
    negb (Point.x a =? Point.x B) &&
    negb
      (Point.x (EccSpec.point_add_incomplete a (mul_step_point_at k B i)) =?
       Point.x a).

  (** [count] steps from bit index [i] downwards, threading the accumulator.
      Every constant the body mentions is a parameter, so no spec chain is
      reachable from the fixpoint. *)
  Fixpoint mul_chain_go (B : Point.t) (Bp : Pallas.point) (k : Z)
      (acc : Pallas.point) (i count : nat) : bool :=
    match count with
    | O => true
    | S count' =>
        mul_chain_check B k i acc &&
        mul_chain_go B Bp k (mul_chain_step Bp k i acc) (Nat.pred i) count'
    end.

  (** Bits [254 .. 4], from the initial accumulator [mul_acc w 255]. *)
  Definition mul_chain_b (w : HonestInput) : bool :=
    point_ok_b (hi_g_d_old w) &&
    mul_chain_go (hi_g_d_old w) (mul_base w) (mul_scalar w)
      (Pallas.mul (mul_multiple_at (mul_scalar w) 255%nat) (mul_base w))
      254%nat 251%nat.

  Lemma mul_chain_check_sound (B : Point.t) (Bp : Pallas.point) (k : Z)
      (i : nat) :
    mul_chain_check B k i (Pallas.mul (mul_multiple_at k (S i)) Bp) = true ->
    mul_step_nondeg_at k B Bp i.
  Proof.
    intros Hcheck.
    unfold mul_chain_check in Hcheck.
    cbv beta zeta in Hcheck.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcheck Hthird].
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hfirst Hsecond].
    apply Bool.negb_true_iff in Hfirst.
    apply Bool.negb_true_iff in Hsecond.
    apply Bool.negb_true_iff in Hthird.
    apply Z.eqb_neq in Hfirst.
    apply Z.eqb_neq in Hsecond.
    apply Z.eqb_neq in Hthird.
    unfold mul_step_nondeg_at.
    cbv zeta.
    exact (conj Hfirst (conj Hsecond Hthird)).
  Qed.

  (** One chain step advances the multiple by one bit: the group-law
      identity of [VarBaseDefs.double_add_step_multiple] at the
      [2^(255−i) + 2 z_i + 1] shape. *)
  Lemma mul_chain_step_multiple (Bp : Pallas.point) (k : Z) (i : nat) :
    Pallas.reduced Bp -> Pallas.on_curve Bp -> (i < 255)%nat ->
    mul_chain_step Bp k i (Pallas.mul (mul_multiple_at k (S i)) Bp) =
    Pallas.mul (mul_multiple_at k i) Bp.
  Proof.
    intros HrB HoB Hi.
    assert (Hbit : scalar_bit k i = 0 \/ scalar_bit k i = 1).
    { unfold scalar_bit.
      pose proof (Z.mod_pos_bound (k / 2 ^ Z.of_nat i) 2 ltac:(lia)).
      lia. }
    unfold mul_chain_step.
    rewrite (VarBaseDefs.double_add_step_multiple Bp
      (mul_multiple_at k (S i)) (scalar_bit k i) HrB HoB Hbit).
    f_equal.
    unfold mul_multiple_at.
    rewrite (bit_running_sum_step k i).
    assert (Hpow : 255 - Z.of_nat i = (255 - Z.of_nat (S i)) + 1) by lia.
    rewrite Hpow, Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    lia.
  Qed.

  Lemma mul_chain_go_sound (B : Point.t) (Bp : Pallas.point) (k : Z)
      (HrB : Pallas.reduced Bp) (HoB : Pallas.on_curve Bp) :
    forall (count i : nat),
      (count <= S i)%nat -> (i < 255)%nat ->
      mul_chain_go B Bp k (Pallas.mul (mul_multiple_at k (S i)) Bp) i count
        = true ->
      forall j : nat, (S i - count <= j <= i)%nat ->
        mul_step_nondeg_at k B Bp j.
  Proof.
    induction count as [| c IH]; intros i Hci Hi Hgo j Hj.
    - lia.
    - cbn [mul_chain_go] in Hgo.
      apply Bool.andb_true_iff in Hgo.
      destruct Hgo as [Hhead Hrest].
      destruct (Nat.eq_dec i j) as [<- | Hne].
      + exact (mul_chain_check_sound B Bp k i Hhead).
      + rewrite (mul_chain_step_multiple Bp k i HrB HoB Hi) in Hrest.
        assert (Hi1 : (1 <= i)%nat) by lia.
        replace i with (S (Nat.pred i)) in Hrest at 1 by lia.
        exact (IH (Nat.pred i) ltac:(lia) ltac:(lia) Hrest j ltac:(lia)).
  Qed.

  (** Conversion must not be allowed to reach [ivk]: [mul_step_point_at]
      guards on [scalar_bit (mul_scalar w) i], so whnf of either side forces
      [ivk w], whose body unfolds the whole symbolic [Commit^ivk] chain at a
      variable input and does not terminate.  With [ivk] opaque both sides
      get stuck at the same atom and the comparison is structural.  The
      setting is [Local]: [forward/ecc_add.v] and
      [forward/var_base_ladder.v] unfold [ivk] and must not inherit it. *)
  Local Strategy opaque [ivk].

  Lemma mul_step_nondeg_at_transfer (w : HonestInput) (i : nat) :
    mul_step_nondeg_at (mul_scalar w) (hi_g_d_old w) (mul_base w) i ->
    mul_step_nondegenerate w i.
  Proof. exact (fun H => H). Qed.

  Local Strategy transparent [ivk].

  Lemma mul_chain_sound (w : HonestInput) :
    mul_chain_b w = true -> mul_nondegenerate_input w.
  Proof.
    intros Hchain i Hi.
    unfold mul_chain_b in Hchain.
    apply Bool.andb_true_iff in Hchain.
    destruct Hchain as [Hok Hgo].
    pose proof (point_ok_b_sound _ Hok) as (HrB & HoB & _).
    apply (mul_step_nondeg_at_transfer w i).
    exact (mul_chain_go_sound (hi_g_d_old w) (mul_base w) (mul_scalar w)
      HrB HoB 251%nat 254%nat ltac:(lia) ltac:(lia) Hgo i ltac:(lia)).
  Qed.

  (** ** The nondegeneracy assembly

      [nondegenerate w] from the clause-wise Boolean certificates: the
      Merkle chain, the three Sinsemilla hashes and the four variable-base
      ranges. *)
  Lemma nondegenerate_of_certs (w : HonestInput) :
    merkle_nondeg_b w = true ->
    sins_nondeg_go
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_old_words w) = true ->
    sins_nondeg_go
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_new_words w) = true ->
    sins_nondeg_go
      (OrchardSpec.commit_ivk_q orchard_circuit_params)
      (commit_ivk_words w) = true ->
    mul_chain_b w = true ->
    nondegenerate w.
  Proof.
    intros Hmerkle Hnc_old Hnc_new Hivk Hchain.
    unfold nondegenerate.
    split.
    { intros i Hi.
      refine (merkle_nondeg_go_sound w 32%nat 0%nat eq_refl _ i ltac:(lia)).
      (* [merkle_node w 0] unfolds to the empty-prefix fold, i.e. [leaf w]. *)
      exact Hmerkle. }
    split; [exact (sins_nondeg_sound _ _ Hnc_old) |].
    split; [exact (sins_nondeg_sound _ _ Hnc_new) |].
    split; [exact (sins_nondeg_sound _ _ Hivk) |].
    exact (mul_chain_sound w Hchain).
  Qed.

  (** ** The generated assignment and the enabled-point shards *)

  Definition Γtest : Assignment.t columns RegionId.t :=
    OrchardHonestAssignment.honest_assignment test_input.

  Definition facts : list (Fact.t columns RegionId.t) :=
    OrchardHonestAssignment.facts.

  Definition system : ConstraintSystem.t columns :=
    OrchardCompletenessCertificates.system.

  Definition enabled : list (Selector.t * RegionId.t * Z) :=
    Complete.enabled_points facts.

  (** Shard key: one index per region family, the 32 Merkle layers split
      one shard per layer (they carry roughly half the enabled points). *)
  Definition family_index (region : RegionId.t) : Z :=
    match region with
    | RegionId.WitnessInput _ => 0
    | RegionId.Merkle layer _ => 1 + RegionId.Merkle.Layer.to_index layer
    | RegionId.Poseidon _ => 33
    | RegionId.ValueCommitment _ => 34
    | RegionId.Nullifier _ => 35
    | RegionId.SpendAuthority _ => 36
    | RegionId.AddressIntegrity _ => 37
    | RegionId.CommitIvk _ => 38
    | RegionId.NoteCommit RegionId.NoteCommit.Which.Old _ => 39
    | RegionId.NoteCommit RegionId.NoteCommit.Which.New _ => 40
    | RegionId.GadgetLocal _ => 41
    | RegionId.NoteCommitOldEquality => 42
    | RegionId.NoteCommitNewWitnessGD => 42
    | RegionId.NoteCommitNewWitnessPkD => 42
    | RegionId.NoteCommitNewWitnessPsi => 42
    | RegionId.OrchardCircuitChecks => 42
    end.

  (** The enabled points of a group of region families. *)
  Definition shard_in (indices : list Z)
      : list (Selector.t * RegionId.t * Z) :=
    List.filter
      (fun '(_, region, _) =>
        List.existsb (Z.eqb (family_index region)) indices)
      enabled.

  (** The per-point checker.  Only the constraints guarded by the point's own
      selector are evaluated (the honest selector plane makes every other
      guarded constraint vacuous, handled once by [circuit_holds_intro]), and
      only the lookup arguments mentioning that selector are checked, with
      the argument's first expression — the looked-up word — as the table-row
      hint. *)
  Definition check_point (pt : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, row) := pt in
    List.forallb
      (fun gate =>
        List.forallb
          (fun '(_, constraint) =>
            match constraint with
            | Constraint.Select s body =>
                if OrchardDecidableEq.selector_eqb s sel
                then Complete.check_constraint Γtest (region, row) body
                else true
            | _ => true
            end)
          gate.(Gate.constraints))
      system.(ConstraintSystem.gates) &&
    List.forallb
      (fun arg =>
        if Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
             sel arg
        then
          Complete.check_lookup_argument Γtest (region, row) 1024
            (match arg.(LookupArgument.pairs) with
             | (expression, _) :: _ =>
                 eval_expression Γtest (region, row) expression
             | [] => 0
             end)
            arg
        else true)
      system.(ConstraintSystem.lookups).

  (** The join helper: a certified shard group covers each of its enabled
      points. *)
  Lemma check_point_shard_in (indices : list Z) (sel : Selector.t)
      (region : RegionId.t) (row : Z) :
    List.forallb check_point (shard_in indices) = true ->
    List.In (sel, region, row) enabled ->
    List.existsb (Z.eqb (family_index region)) indices = true ->
    check_point (sel, region, row) = true.
  Proof.
    intros Hcert Hin Hfam.
    refine (proj1 (List.forallb_forall check_point (shard_in indices))
      Hcert _ _).
    apply List.filter_In.
    split; [exact Hin | exact Hfam].
  Qed.

  (** The value both sides of the read-back certificate reduce to.
      Pinning it lets the reader side and the specification side be
      certified independently, in parallel, instead of being compared
      to each other in one conversion that evaluates [inputs_of] twice. *)
  Definition test_action_inputs : OrchardSpec.ActionInputs :=
     {|
        OrchardSpec.in_ak :=
          {|
            Point.x :=
              23086803432884955728087073312209723542120506047735460087757239757681103736529;
            Point.y :=
              2008260733349480776792597907324841974075376177005355926586073894450279518853
          |};
        OrchardSpec.in_nk := 11;
        OrchardSpec.in_rho_old := 12;
        OrchardSpec.in_psi_old := 13;
        OrchardSpec.in_cm_old :=
          {|
            Point.x :=
              24630627294302742423012669121045034654997501738907340497975122850196611208508;
            Point.y :=
              26033792874846409567060615178532519341822716432177126186718375341188937453618
          |};
        OrchardSpec.in_g_d_old :=
          {|
            Point.x :=
              4027241023027617754036171531542546502751647131375064771810253584944963179107;
            Point.y :=
              21762326383673887073830845720227757791980770399450032709429395080608314263493
          |};
        OrchardSpec.in_pk_d_old :=
          {| Point.x := 0; Point.y := 0 |};
        OrchardSpec.in_v_old := 2;
        OrchardSpec.in_rivk := 0;
        OrchardSpec.in_alpha := 6;
        OrchardSpec.in_anchor_public :=
          9554279788040663870271245084527973707977976412104891855744717376222267472079;
        OrchardSpec.in_rcv := 4;
        OrchardSpec.in_magnitude := 1;
        OrchardSpec.in_sign := 1;
        OrchardSpec.in_leaf :=
          24630627294302742423012669121045034654997501738907340497975122850196611208508;
        OrchardSpec.in_path :=
          cons (pair (pair 0 1) true)
            (cons (pair (pair 1 2) false)
               (cons (pair (pair 2 3) true)
                  (cons (pair (pair 3 4) false)
                     (cons (pair (pair 4 5) false)
                        (cons (pair (pair 5 6) false)
                           (cons (pair (pair 6 7) false)
                              (cons (pair (pair 7 8) false)
                                 (cons (pair (pair 8 9) false)
                                    (cons (pair (pair 9 10) false)
                                       (cons (pair (pair 10 11) false)
                                          (cons (pair (pair 11 12) false)
                                             (cons
                                                (pair (pair 12 13) false)
                                                (cons
                                                (pair (pair 13 14) false)
                                                (cons
                                                (pair (pair 14 15) false)
                                                (cons
                                                (pair (pair 15 16) false)
                                                (cons
                                                (pair (pair 16 17) false)
                                                (cons
                                                (pair (pair 17 18) false)
                                                (cons
                                                (pair (pair 18 19) false)
                                                (cons
                                                (pair (pair 19 20) false)
                                                (cons
                                                (pair (pair 20 21) false)
                                                (cons
                                                (pair (pair 21 22) false)
                                                (cons
                                                (pair (pair 22 23) false)
                                                (cons
                                                (pair (pair 23 24) false)
                                                (cons
                                                (pair (pair 24 25) false)
                                                (cons
                                                (pair (pair 25 26) false)
                                                (cons
                                                (pair (pair 26 27) false)
                                                (cons
                                                (pair (pair 27 28) false)
                                                (cons
                                                (pair (pair 28 29) false)
                                                (cons
                                                (pair (pair 29 30) false)
                                                (cons
                                                (pair (pair 30 31) false)
                                                (cons
                                                (pair (pair 31 32) false)
                                                nil)))))))))))))))))))))))))))))));
        OrchardSpec.in_g_d_new :=
          {|
            Point.x :=
              11597971188910290580510217765257817734852330887059848818989398919746936474521;
            Point.y :=
              16072930402498746743190202080148926785915484279186972392222802455510868042413
          |};
        OrchardSpec.in_pk_d_new :=
          {|
            Point.x :=
              22395455290326124500977609662008208779573158769178530571879529796377080762153;
            Point.y :=
              13514763571731510787947890306543887240625618236391309711294671830650954541887
          |};
        OrchardSpec.in_v_new := 1;
        OrchardSpec.in_psi_new := 14;
        OrchardSpec.in_rcm_new := 10
      |}.

End OrchardCompletenessInstanceDefs.
