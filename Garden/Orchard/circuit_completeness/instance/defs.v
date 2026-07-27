(** * Definitions for the concrete Orchard completeness instance

    The shared definitions of the completeness-instance certificate: the
    concrete honest input [test_input], the Boolean forms of the
    completeness-domain predicates ([valid_b], [nondegenerate_b]) with their
    soundness lemmas, the generated assignment [Γtest], and the per-point
    checker [check_point] with its region-family shard partition.  The
    [vm_compute] certificates over these definitions live in the sibling
    [instance_*] leaf files (so they compile in parallel and are never
    re-paid while this file is edited); [instance/cert.v] joins them into
    the instance theorem.

    The nondegeneracy checkers are linear: each Sinsemilla clause folds the
    accumulator through the message once ([sins_nondeg_go]) and the Merkle
    clause threads the running node through the 32 layers
    ([merkle_nondeg_go]), instead of recomputing per-round hash prefixes —
    the per-read recomputation pitfall of [docs/compile-performance.md]. *)

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

      One accumulator multiple per bit index (the [let] binds the point once
      per step).  The 251 indices are certified in four ranges across
      parallel leaf files ([instance_mul_*.v]); [mul_ranges_sound] joins
      them. *)
  Definition mul_step_b (w : HonestInput) (i : nat) : bool :=
    let acc := mul_acc w (S i) in
    negb (Point.x acc =? 0) &&
    negb (Point.x acc =? Point.x (hi_g_d_old w)) &&
    negb
      (Point.x (EccSpec.point_add_incomplete acc (mul_step_point w i)) =?
       Point.x acc).

  Lemma mul_step_b_sound (w : HonestInput) (i : nat) :
    mul_step_b w i = true -> mul_step_nondegenerate w i.
  Proof.
    intros Hcheck.
    unfold mul_step_b in Hcheck.
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
    unfold mul_step_nondegenerate.
    cbv zeta.
    exact (conj Hfirst (conj Hsecond Hthird)).
  Qed.

  Lemma mul_ranges_sound (w : HonestInput) :
    List.forallb (mul_step_b w) (List.seq 4 63) = true ->
    List.forallb (mul_step_b w) (List.seq 67 63) = true ->
    List.forallb (mul_step_b w) (List.seq 130 63) = true ->
    List.forallb (mul_step_b w) (List.seq 193 62) = true ->
    mul_nondegenerate_input w.
  Proof.
    intros Ha Hb Hc Hd i Hi.
    apply mul_step_b_sound.
    destruct (Nat.lt_ge_cases i 67) as [H1 | H1];
      [exact (forallb_seq_sound _ _ _ Ha i ltac:(lia)) |].
    destruct (Nat.lt_ge_cases i 130) as [H2 | H2];
      [exact (forallb_seq_sound _ _ _ Hb i ltac:(lia)) |].
    destruct (Nat.lt_ge_cases i 193) as [H3 | H3];
      [exact (forallb_seq_sound _ _ _ Hc i ltac:(lia)) |].
    exact (forallb_seq_sound _ _ _ Hd i ltac:(lia)).
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
    List.forallb (mul_step_b w) (List.seq 4 63) = true ->
    List.forallb (mul_step_b w) (List.seq 67 63) = true ->
    List.forallb (mul_step_b w) (List.seq 130 63) = true ->
    List.forallb (mul_step_b w) (List.seq 193 62) = true ->
    nondegenerate w.
  Proof.
    intros Hmerkle Hnc_old Hnc_new Hivk Ha Hb Hc Hd.
    unfold nondegenerate.
    split.
    { intros i Hi.
      refine (merkle_nondeg_go_sound w 32%nat 0%nat eq_refl _ i ltac:(lia)).
      (* [merkle_node w 0] unfolds to the empty-prefix fold, i.e. [leaf w]. *)
      exact Hmerkle. }
    split; [exact (sins_nondeg_sound _ _ Hnc_old) |].
    split; [exact (sins_nondeg_sound _ _ Hnc_new) |].
    split; [exact (sins_nondeg_sound _ _ Hivk) |].
    exact (mul_ranges_sound w Ha Hb Hc Hd).
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

End OrchardCompletenessInstanceDefs.
