(** * Forward completeness: the Poseidon gate family (family index 33)

    The symbolic per-gate forward lemmas for the Poseidon regions of the
    Orchard circuit — the [family_gates_ok] / [family_lookups_ok] obligations
    of [forward/api.v] at the family list [[33]], universally quantified over
    every valid, nondegenerate honest input.

    The enabled points of the family ([poseidon_points_eq]) are the
    pad-and-add row of the sponge absorb region ([AddInput] offset 1) and the
    36 rows of the permutation region ([PermuteState]): full rounds at
    offsets 0..3 and 32..35 (rounds 0..3 and 60..63), packed partial-round
    pairs at offsets 4..31 (rounds 4..59).  The honest cells are the
    [Poseidon.permute] round schedule ([pose_states_of], read through
    [pose_state_t]), so each gate reduces to the round-function identity:

    - full rounds: the gate sum is definitionally [FullRound.output] on the
      current row state ([full_round_complete]);
    - partial rounds: the [mid_0] witness is the round-[a] S-box output, and
      the two MDS-inverse-mixed next-row reads recover the round-[b] S-box
      inputs through [mds_inv_mul (mds_mul u) = u] ([partial_next_dot0-2],
      [partial_round_complete]);
    - pad-and-add: the absorb sums of the seed and input rows
      ([pad_input_ok]).

    The gate bodies guarded by the three Poseidon selectors are pinned by the
    [vm_compute] certificates [guarded_full_eq] / [guarded_partial_eq] /
    [guarded_pad_eq]; no configured lookup argument mentions a Poseidon
    selector ([poseidon_no_lookup_mentions]), so the lookup obligation is
    vacuous. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Garden.Halo2.halo2_gadgets.poseidon.pow5.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.advice_poseidon_nullifier.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardPoseidon.
  Import OrchardWitnessInput.
  Import OrchardCompletenessTables.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.

  (** ** The constraint bodies guarded by each Poseidon selector

      [guarded sel] collects, over the whole configured system, the bodies of
      the constraints guarded by [sel]; the certificates pin each Poseidon
      selector's list to the pow5 gate bodies. *)
  Definition guarded (sel : Selector.t) : list (Constraint.t columns) :=
    List.flat_map (fun gate =>
      List.flat_map (fun '(_, c) =>
        match c with
        | Constraint.Select s body =>
            if OrchardDecidableEq.selector_eqb s sel then [body] else []
        | _ => []
        end) gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma guarded_complete (sel : Selector.t) (gate : Gate.t columns)
      (name : option string) (body : Constraint.t columns)
      (Hgate : List.In gate system.(ConstraintSystem.gates))
      (Hbody : List.In (name, Constraint.Select sel body)
        gate.(Gate.constraints)) :
    List.In body (guarded sel).
  Proof.
    unfold guarded.
    apply List.in_flat_map. exists gate. split; [exact Hgate |].
    apply List.in_flat_map. exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    cbn. rewrite OrchardDecidableEq.selector_eqb_refl. now left.
  Qed.

  Definition full_bodies : list (Constraint.t columns) := [
    Constraint.Equal (pow5.full_round_sum 0)
      (Expression.Advice Advice.A6 Rotation.next);
    Constraint.Equal (pow5.full_round_sum 1)
      (Expression.Advice Advice.A7 Rotation.next);
    Constraint.Equal (pow5.full_round_sum 2)
      (Expression.Advice Advice.A8 Rotation.next)
  ].

  Definition partial_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (pow5.pow_5 (Expression.Sum
        (Expression.Advice Advice.A6 Rotation.cur)
        (Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur)))
      (Expression.Advice Advice.A5 Rotation.cur);
    Constraint.Equal
      (pow5.pow_5 (Expression.Sum
        (pow5.mid 0)
        (Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur)))
      (pow5.next 0);
    Constraint.Equal
      (Expression.Sum (pow5.mid 1)
        (Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur))
      (pow5.next 1);
    Constraint.Equal
      (Expression.Sum (pow5.mid 2)
        (Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur))
      (pow5.next 2)
  ].

  Definition pad_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum (Expression.Advice Advice.A6 Rotation.prev)
        (Expression.Advice Advice.A6 Rotation.cur))
      (Expression.Advice Advice.A6 Rotation.next);
    Constraint.Equal
      (Expression.Sum (Expression.Advice Advice.A7 Rotation.prev)
        (Expression.Advice Advice.A7 Rotation.cur))
      (Expression.Advice Advice.A7 Rotation.next);
    Constraint.Equal (Expression.Advice Advice.A8 Rotation.prev)
      (Expression.Advice Advice.A8 Rotation.next)
  ].

  Lemma guarded_full_eq : guarded Selector.QPoseidonFull = full_bodies.
  Proof.
    vm_cast_no_check
      (@eq_refl (list (Constraint.t columns))
        (guarded Selector.QPoseidonFull)).
  Qed.

  Lemma guarded_partial_eq : guarded Selector.QPoseidonPartial = partial_bodies.
  Proof.
    vm_cast_no_check
      (@eq_refl (list (Constraint.t columns))
        (guarded Selector.QPoseidonPartial)).
  Qed.

  Lemma guarded_pad_eq : guarded Selector.QPoseidonPadAndAdd = pad_bodies.
  Proof.
    vm_cast_no_check
      (@eq_refl (list (Constraint.t columns))
        (guarded Selector.QPoseidonPadAndAdd)).
  Qed.

  (** ** The enabled points of family 33 *)
  Definition poseidon_points : list (Selector.t * RegionId.t * Z) := [
    (Selector.QPoseidonPadAndAdd,
      RegionId.Poseidon RegionId.Poseidon.AddInput, 1);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 0);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 1);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 2);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 3);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 4);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 5);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 6);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 7);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 8);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 9);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 10);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 11);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 12);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 13);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 14);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 15);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 16);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 17);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 18);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 19);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 20);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 21);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 22);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 23);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 24);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 25);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 26);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 27);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 28);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 29);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 30);
    (Selector.QPoseidonPartial,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 31);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 32);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 33);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 34);
    (Selector.QPoseidonFull,
      RegionId.Poseidon RegionId.Poseidon.PermuteState, 35)
  ].

  Lemma poseidon_points_eq : shard_in [33] = poseidon_points.
  Proof.
    vm_cast_no_check
      (@eq_refl (list (Selector.t * RegionId.t * Z)) (shard_in [33])).
  Qed.

  (** No configured lookup argument mentions a Poseidon selector. *)
  Lemma poseidon_no_lookup_mentions :
    List.forallb (fun pt =>
      let '(sel, _, _) := pt in
      List.forallb (fun arg =>
        negb (Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
          sel arg))
        system.(ConstraintSystem.lookups))
      (shard_in [33]) = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** Membership of an enabled family-33 point in the shard. *)
  Lemma poseidon_point_in (sel : Selector.t) (region : RegionId.t) (row : Z)
      (Hin : List.In (sel, region, row) enabled)
      (Hfam : List.In (family_index region) [33]) :
    List.In (sel, region, row) (shard_in [33]).
  Proof.
    apply List.filter_In.
    split; [exact Hin |].
    destruct Hfam as [Hf | Habs]; [| destruct Habs].
    cbn. rewrite <- Hf. reflexivity.
  Qed.

  (** ** The generator round schedule, one row at a time *)

  Lemma t_pose_tables_of (w : HonestInput) :
    t_pose (tables_of w) = pose_states_of w.
  Proof. reflexivity. Qed.

  Lemma states_go_head (s : State.t) (row count : nat) :
    List.nth 0 (states_go s row count) state0 = s.
  Proof. destruct count; reflexivity. Qed.

  Lemma states_go_nth (count : nat) :
    forall (s : State.t) (row n : nat),
    (n < count)%nat ->
    List.nth (S n) (states_go s row count) state0 =
    poseidon_round (row + n)%nat (List.nth n (states_go s row count) state0).
  Proof.
    induction count as [| count IH]; intros s row n Hn; [lia |].
    cbn [states_go].
    destruct n as [| n].
    - cbn [List.nth]. rewrite Nat.add_0_r. now rewrite states_go_head.
    - cbn [List.nth]. rewrite IH by lia. f_equal. lia.
  Qed.

  (** Row [n + 1] of the permutation region is the round-[n] image of
      row [n]. *)
  Lemma pose_state_succ (w : HonestInput) (n : nat) (Hn : (n < 36)%nat) :
    pose_state_t (tables_of w) (S n) =
    poseidon_round n (pose_state_t (tables_of w) n).
  Proof.
    unfold pose_state_t.
    rewrite t_pose_tables_of.
    unfold pose_states_of.
    rewrite (states_go_nth 36 _ 0 n Hn).
    reflexivity.
  Qed.

  (** The successor equation with the round function pre-dispatched:
      consumers [rewrite <-] with the [apply_full]/[apply_partial]
      application found syntactically, so [poseidon_round] at a literal row
      index never reaches unification. *)
  Lemma pose_state_succ_t (w : HonestInput) (n : nat)
      (t : State.t -> State.t) (Hn : (n < 36)%nat)
      (Ht : forall s, t s = poseidon_round n s) :
    pose_state_t (tables_of w) (S n) = t (pose_state_t (tables_of w) n).
  Proof.
    rewrite (pose_state_succ w n Hn). symmetry. apply Ht.
  Qed.

  (** ** Field algebra: the MDS inverse consumes the MDS mix *)

  Lemma mds_consume (u : State.t)
      (H0 : UnOp.from u.(State.x0) = u.(State.x0))
      (H1 : UnOp.from u.(State.x1) = u.(State.x1))
      (H2 : UnOp.from u.(State.x2) = u.(State.x2)) :
    mds_inv_mul (mds_mul u) = u.
  Proof.
    assert (Hmm : Field.map_mod u = u).
    { destruct u; cbn in *; now rewrite H0, H1, H2. }
    rewrite <- Hmm at 1.
    rewrite mds_inv_mul_mds_identity.
    exact Hmm.
  Qed.

  Lemma from_pow5 (x : Z) : UnOp.from (pow5 x) = pow5 x.
  Proof. unfold pow5. apply FieldRewrite.from_mul. Qed.

  (** The state after the first partial round of a packed pair: the round-[a]
      S-box output mixed by the MDS matrix. *)
  Definition partial_mid_state (round_a : nat) (s : State.t) : State.t :=
    mds_mul (PartialRound.sbox_partial {|
      State.x0 := s.(State.x0) +F Poseidon.rc round_a 0;
      State.x1 := s.(State.x1) +F Poseidon.rc round_a 1;
      State.x2 := s.(State.x2) +F Poseidon.rc round_a 2;
    |}).

  Lemma partial_next_dot0 (round_a round_b : nat) (s : State.t) :
    UnOp.from (State.x0 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 0 0) +F
    UnOp.from (State.x1 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 0 1) +F
    UnOp.from (State.x2 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 0 2) =
    pow5 (State.x0 (partial_mid_state round_a s) +F Poseidon.rc round_b 0).
  Proof.
    unfold Poseidon.apply_partial, PartialRound.output.
    fold (partial_mid_state round_a s).
    set (u := PartialRound.sbox_partial {|
      State.x0 :=
        State.x0 (partial_mid_state round_a s) +F Poseidon.rc round_b 0;
      State.x1 :=
        State.x1 (partial_mid_state round_a s) +F Poseidon.rc round_b 1;
      State.x2 :=
        State.x2 (partial_mid_state round_a s) +F Poseidon.rc round_b 2;
    |}).
    assert (Hu0 : UnOp.from (State.x0 u) = State.x0 u).
    { cbn [u PartialRound.sbox_partial State.x0]. apply from_pow5. }
    assert (Hu1 : UnOp.from (State.x1 u) = State.x1 u).
    { cbn [u PartialRound.sbox_partial State.x1].
      apply FieldRewrite.from_add. }
    assert (Hu2 : UnOp.from (State.x2 u) = State.x2 u).
    { cbn [u PartialRound.sbox_partial State.x2].
      apply FieldRewrite.from_add. }
    assert (Hueq := mds_consume u Hu0 Hu1 Hu2).
    assert (Hux : State.x0 u = pow5 (State.x0 (partial_mid_state round_a s) +F Poseidon.rc round_b 0))
      by reflexivity.
    cbn [mds_mul matrix_mul lin State.x0 State.x1 State.x2].
    unfold lin.
    rewrite !FieldRewrite.from_add.
    rewrite <- dot3.
    transitivity (State.x0 (mds_inv_mul (mds_mul u))).
    { unfold mds_inv_mul, mds_mul, matrix_mul, lin, coeff, mds_inv_coeff,
        mds_coeff.
      cbn [State.x0 State.x1 State.x2].
      reflexivity. }
    rewrite Hueq.
    exact Hux.
  Qed.

  Lemma partial_next_dot1 (round_a round_b : nat) (s : State.t) :
    UnOp.from (State.x0 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 1 0) +F
    UnOp.from (State.x1 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 1 1) +F
    UnOp.from (State.x2 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 1 2) =
    State.x1 (partial_mid_state round_a s) +F Poseidon.rc round_b 1.
  Proof.
    unfold Poseidon.apply_partial, PartialRound.output.
    fold (partial_mid_state round_a s).
    set (u := PartialRound.sbox_partial {|
      State.x0 :=
        State.x0 (partial_mid_state round_a s) +F Poseidon.rc round_b 0;
      State.x1 :=
        State.x1 (partial_mid_state round_a s) +F Poseidon.rc round_b 1;
      State.x2 :=
        State.x2 (partial_mid_state round_a s) +F Poseidon.rc round_b 2;
    |}).
    assert (Hu0 : UnOp.from (State.x0 u) = State.x0 u).
    { cbn [u PartialRound.sbox_partial State.x0]. apply from_pow5. }
    assert (Hu1 : UnOp.from (State.x1 u) = State.x1 u).
    { cbn [u PartialRound.sbox_partial State.x1].
      apply FieldRewrite.from_add. }
    assert (Hu2 : UnOp.from (State.x2 u) = State.x2 u).
    { cbn [u PartialRound.sbox_partial State.x2].
      apply FieldRewrite.from_add. }
    assert (Hueq := mds_consume u Hu0 Hu1 Hu2).
    assert (Hux : State.x1 u = State.x1 (partial_mid_state round_a s) +F Poseidon.rc round_b 1)
      by reflexivity.
    cbn [mds_mul matrix_mul lin State.x0 State.x1 State.x2].
    unfold lin.
    rewrite !FieldRewrite.from_add.
    rewrite <- dot3.
    transitivity (State.x1 (mds_inv_mul (mds_mul u))).
    { unfold mds_inv_mul, mds_mul, matrix_mul, lin, coeff, mds_inv_coeff,
        mds_coeff.
      cbn [State.x0 State.x1 State.x2].
      reflexivity. }
    rewrite Hueq.
    exact Hux.
  Qed.

  Lemma partial_next_dot2 (round_a round_b : nat) (s : State.t) :
    UnOp.from (State.x0 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 2 0) +F
    UnOp.from (State.x1 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 2 1) +F
    UnOp.from (State.x2 (Poseidon.apply_partial round_a round_b s)) *F
      UnOp.from (mds_inv_coeff 2 2) =
    State.x2 (partial_mid_state round_a s) +F Poseidon.rc round_b 2.
  Proof.
    unfold Poseidon.apply_partial, PartialRound.output.
    fold (partial_mid_state round_a s).
    set (u := PartialRound.sbox_partial {|
      State.x0 :=
        State.x0 (partial_mid_state round_a s) +F Poseidon.rc round_b 0;
      State.x1 :=
        State.x1 (partial_mid_state round_a s) +F Poseidon.rc round_b 1;
      State.x2 :=
        State.x2 (partial_mid_state round_a s) +F Poseidon.rc round_b 2;
    |}).
    assert (Hu0 : UnOp.from (State.x0 u) = State.x0 u).
    { cbn [u PartialRound.sbox_partial State.x0]. apply from_pow5. }
    assert (Hu1 : UnOp.from (State.x1 u) = State.x1 u).
    { cbn [u PartialRound.sbox_partial State.x1].
      apply FieldRewrite.from_add. }
    assert (Hu2 : UnOp.from (State.x2 u) = State.x2 u).
    { cbn [u PartialRound.sbox_partial State.x2].
      apply FieldRewrite.from_add. }
    assert (Hueq := mds_consume u Hu0 Hu1 Hu2).
    assert (Hux : State.x2 u = State.x2 (partial_mid_state round_a s) +F Poseidon.rc round_b 2)
      by reflexivity.
    cbn [mds_mul matrix_mul lin State.x0 State.x1 State.x2].
    unfold lin.
    rewrite !FieldRewrite.from_add.
    rewrite <- dot3.
    transitivity (State.x2 (mds_inv_mul (mds_mul u))).
    { unfold mds_inv_mul, mds_mul, matrix_mul, lin, coeff, mds_inv_coeff,
        mds_coeff.
      cbn [State.x0 State.x1 State.x2].
      reflexivity. }
    rewrite Hueq.
    exact Hux.
  Qed.

  (** ** The per-gate forward lemmas over an abstract assignment *)

  (** A full-round row: the next-row state is [Poseidon.apply_full] of the
      current row state, and the fixed cells carry the round constants. *)
  Lemma full_round_complete (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (round : nat) (s : State.t)
      (Hc0 : Gamma.(Assignment.advice) Advice.A6 region
        (rotated_row row Rotation.cur) = State.x0 s)
      (Hc1 : Gamma.(Assignment.advice) Advice.A7 region
        (rotated_row row Rotation.cur) = State.x1 s)
      (Hc2 : Gamma.(Assignment.advice) Advice.A8 region
        (rotated_row row Rotation.cur) = State.x2 s)
      (Hn0 : Gamma.(Assignment.advice) Advice.A6 region
        (rotated_row row Rotation.next) =
        State.x0 (Poseidon.apply_full round s))
      (Hn1 : Gamma.(Assignment.advice) Advice.A7 region
        (rotated_row row Rotation.next) =
        State.x1 (Poseidon.apply_full round s))
      (Hn2 : Gamma.(Assignment.advice) Advice.A8 region
        (rotated_row row Rotation.next) =
        State.x2 (Poseidon.apply_full round s))
      (Hf0 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs2 region
        (rotated_row row Rotation.cur) = Poseidon.rc round 0)
      (Hf1 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs3 region
        (rotated_row row Rotation.cur) = Poseidon.rc round 1)
      (Hf2 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs4 region
        (rotated_row row Rotation.cur) = Poseidon.rc round 2) :
    forall body, List.In body full_bodies ->
    eval_constraint Gamma (region, row) body.
  Proof.
    intros body [<- | [<- | [<- | [] ] ] ];
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        p128pow5t3.mds_coeff p128pow5t3.round_constant
        Poseidon.apply_full Poseidon.rc] cbn;
      rewrite Hc0, Hc1, Hc2, ?Hn0, ?Hn1, ?Hn2, Hf0, Hf1, Hf2;
      unfold Poseidon.apply_full, FullRound.output, FullRound.output_coordinate,
        pow5;
      cbn [State.x0 State.x1 State.x2];
      FieldRewrite.run;
      rewrite ?FieldRewrite.from_add;
      reflexivity.
  Qed.

  (** A packed partial-round row: the [mid_0] cell is the round-[a] S-box
      output, the next-row state is [Poseidon.apply_partial], and the six
      fixed cells carry the two rounds' constants. *)
  Lemma partial_round_complete (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z) (round_a round_b : nat) (s : State.t)
      (Hc0 : Gamma.(Assignment.advice) Advice.A6 region
        (rotated_row row Rotation.cur) = State.x0 s)
      (Hc1 : Gamma.(Assignment.advice) Advice.A7 region
        (rotated_row row Rotation.cur) = State.x1 s)
      (Hc2 : Gamma.(Assignment.advice) Advice.A8 region
        (rotated_row row Rotation.cur) = State.x2 s)
      (Hmid : Gamma.(Assignment.advice) Advice.A5 region
        (rotated_row row Rotation.cur) =
        pow5 (State.x0 s +F Poseidon.rc round_a 0))
      (Hn0 : Gamma.(Assignment.advice) Advice.A6 region
        (rotated_row row Rotation.next) =
        State.x0 (Poseidon.apply_partial round_a round_b s))
      (Hn1 : Gamma.(Assignment.advice) Advice.A7 region
        (rotated_row row Rotation.next) =
        State.x1 (Poseidon.apply_partial round_a round_b s))
      (Hn2 : Gamma.(Assignment.advice) Advice.A8 region
        (rotated_row row Rotation.next) =
        State.x2 (Poseidon.apply_partial round_a round_b s))
      (Hf0 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs2 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_a 0)
      (Hf1 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs3 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_a 1)
      (Hf2 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs4 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_a 2)
      (Hf3 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs5 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_b 0)
      (Hf4 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs6 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_b 1)
      (Hf5 : Gamma.(Assignment.fixed) Fixed.LagrangeCoeffs7 region
        (rotated_row row Rotation.cur) = Poseidon.rc round_b 2) :
    forall body, List.In body partial_bodies ->
    eval_constraint Gamma (region, row) body.
  Proof.
    intros body [<- | [<- | [<- | [<- | [] ] ] ] ].
    - (* Round a's S-box output is the mid cell. *)
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff
        p128pow5t3.round_constant Poseidon.apply_partial Poseidon.rc
        pow5_proof.pow5] cbn.
      rewrite Hc0, Hmid, Hf0.
      rewrite from_pow5.
      rewrite ?FieldRewrite.add_from_left, ?FieldRewrite.add_from_right.
      unfold pow5.
      reflexivity.
    - (* Round b's S-box on lane 0. *)
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff
        p128pow5t3.round_constant Poseidon.apply_partial Poseidon.rc
        pow5_proof.pow5] cbn.
      rewrite Hmid, Hc1, Hc2, Hn0, Hn1, Hn2, Hf1, Hf2, Hf3.
      rewrite partial_next_dot0.
      rewrite ?FieldRewrite.add_from_left, ?FieldRewrite.add_from_right.
      rewrite from_pow5.
      rewrite <- dot3.
      unfold partial_mid_state, mds_mul, matrix_mul, lin, coeff, mds_coeff,
        PartialRound.sbox_partial, pow5.
      cbn [State.x0 State.x1 State.x2].
      reflexivity.
    - (* Lane 1 is linear across round b. *)
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff
        p128pow5t3.round_constant Poseidon.apply_partial Poseidon.rc
        pow5_proof.pow5] cbn.
      rewrite Hmid, Hc1, Hc2, Hn0, Hn1, Hn2, Hf1, Hf2, Hf4.
      rewrite partial_next_dot1.
      rewrite ?FieldRewrite.add_from_left, ?FieldRewrite.add_from_right.
      rewrite from_pow5.
      rewrite <- dot3.
      unfold partial_mid_state, mds_mul, matrix_mul, lin, coeff, mds_coeff,
        PartialRound.sbox_partial, pow5.
      cbn [State.x0 State.x1 State.x2].
      reflexivity.
    - (* Lane 2 is linear across round b. *)
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff
        p128pow5t3.round_constant Poseidon.apply_partial Poseidon.rc
        pow5_proof.pow5] cbn.
      rewrite Hmid, Hc1, Hc2, Hn0, Hn1, Hn2, Hf1, Hf2, Hf5.
      rewrite partial_next_dot2.
      rewrite ?FieldRewrite.add_from_left, ?FieldRewrite.add_from_right.
      rewrite from_pow5.
      rewrite <- dot3.
      unfold partial_mid_state, mds_mul, matrix_mul, lin, coeff, mds_coeff,
        PartialRound.sbox_partial, pow5.
      cbn [State.x0 State.x1 State.x2].
      reflexivity.
  Qed.

  (** The pad-and-add row of the absorb region: seed row 0 plus input row 1
      gives the absorbed state of row 2. *)
  Lemma pad_input_ok (w : HonestInput) :
    forall body, List.In body pad_bodies ->
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (RegionId.Poseidon RegionId.Poseidon.AddInput, 1) body.
  Proof.
    intros body [<- | [<- | [<- | [] ] ] ];
      with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
        OrchardCompletenessTables.tables_of] cbn;
      rewrite ?FieldRewrite.from_zero, ?FieldRewrite.add_zero_left,
        ?FieldRewrite.from_from;
      reflexivity.
  Qed.

  (** ** The family obligations *)

  (** The cell-shape discharge for the Poseidon advice holes: reduce the
      generator dispatch with the hoisted record, the field operations and
      the round schedule kept opaque, then compare syntactically — a bare
      [reflexivity]/[exact]-style unification here normalizes the round
      chain ([docs/compile-performance.md], the Poseidon-chain and
      hoisted-advice-plane pitfalls). *)
  Ltac pose_cell :=
    with_strategy opaque
      [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
       p128pow5t3.round_constant p128pow5t3.mds_coeff
       p128pow5t3.mds_inv_coeff
       Poseidon.apply_full Poseidon.apply_partial
       OrchardCompletenessTables.tables_of] cbn;
    reflexivity.

  (** The packed-pair mid cell: the generator spells the round-[a] S-box
      output through [poseidon_mid_t]/[pow5_field], the gate through
      [pow5]/[Poseidon.rc]; unfold both spellings to one syntactic form
      before the compare. *)
  Ltac mid_cell :=
    with_strategy opaque
      [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
       p128pow5t3.round_constant p128pow5t3.mds_coeff
       p128pow5t3.mds_inv_coeff
       Poseidon.apply_full Poseidon.apply_partial
       OrchardCompletenessTables.tables_of] cbn;
    unfold OrchardCompletenessTables.poseidon_mid_t,
      OrchardAdvicePoseidonNullifier.pow5_field, pow5, Poseidon.rc;
    with_strategy opaque
      [BinOp.add BinOp.mul BinOp.sub UnOp.opp UnOp.from
       p128pow5t3.round_constant
       OrchardCompletenessTables.tables_of] cbn;
    reflexivity.

  (** The fixed-plane holes: the targeted projection reduction drops the
      advice record (the fixed plane is input-independent), leaving a
      closed fact lookup for the VM. *)
  Ltac fixed_cell :=
    cbn [OrchardHonestAssignment.honest_assignment Assignment.fixed];
    vm_compute; reflexivity.

  (** One enabled permutation-region point.  [Hstep] pins the next-row
      state with the round function pre-dispatched, so the [Hn] holes
      close by [rewrite <-] plus the syntactic cell compare and the round
      chain never reaches unification. *)
  Ltac full_case Heq Hb body w n round :=
    injection Heq as <- <- <-;
    rewrite guarded_full_eq in Hb;
    pose proof (pose_state_succ_t w n (Poseidon.apply_full round)
      ltac:(lia) (fun s => eq_refl)) as Hstep;
    refine (full_round_complete _ _ _ round
      (pose_state_t (tables_of w) n) _ _ _ _ _ _ _ _ _ body Hb);
    [ pose_cell | pose_cell | pose_cell
    | rewrite <- Hstep; pose_cell
    | rewrite <- Hstep; pose_cell
    | rewrite <- Hstep; pose_cell
    | fixed_cell | fixed_cell | fixed_cell ].

  Ltac partial_case Heq Hb body w n ra rb :=
    injection Heq as <- <- <-;
    rewrite guarded_partial_eq in Hb;
    pose proof (pose_state_succ_t w n (Poseidon.apply_partial ra rb)
      ltac:(lia) (fun s => eq_refl)) as Hstep;
    refine (partial_round_complete _ _ _ ra rb
      (pose_state_t (tables_of w) n) _ _ _ _ _ _ _ _ _ _ _ _ _ body Hb);
    [ pose_cell | pose_cell | pose_cell | mid_cell
    | rewrite <- Hstep; pose_cell
    | rewrite <- Hstep; pose_cell
    | rewrite <- Hstep; pose_cell
    | fixed_cell | fixed_cell | fixed_cell
    | fixed_cell | fixed_cell | fixed_cell ].

  Theorem poseidon_gates_ok : family_gates_ok [33].
  Proof.
    intros w Hvalid Hnondeg sel region row Hin Hfam gate Hgate name body Hbody.
    pose proof (guarded_complete sel gate name body Hgate Hbody) as Hb.
    clear Hgate Hbody.
    pose proof (poseidon_point_in sel region row Hin Hfam) as Hpt.
    clear Hin Hfam.
    rewrite poseidon_points_eq in Hpt.
    cbn in Hpt.
    (* AddInput, row 1: pad-and-add. *)
    destruct Hpt as [Heq | Hpt].
    { injection Heq as <- <- <-.
      rewrite guarded_pad_eq in Hb.
      exact (pad_input_ok w body Hb). }
    (* PermuteState, row 0: full round 0. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 0%nat 0%nat. }
    (* PermuteState, row 1: full round 1. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 1%nat 1%nat. }
    (* PermuteState, row 2: full round 2. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 2%nat 2%nat. }
    (* PermuteState, row 3: full round 3. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 3%nat 3%nat. }
    (* PermuteState, row 4: partial rounds 4 and 5. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 4%nat 4%nat 5%nat. }
    (* PermuteState, row 5: partial rounds 6 and 7. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 5%nat 6%nat 7%nat. }
    (* PermuteState, row 6: partial rounds 8 and 9. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 6%nat 8%nat 9%nat. }
    (* PermuteState, row 7: partial rounds 10 and 11. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 7%nat 10%nat 11%nat. }
    (* PermuteState, row 8: partial rounds 12 and 13. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 8%nat 12%nat 13%nat. }
    (* PermuteState, row 9: partial rounds 14 and 15. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 9%nat 14%nat 15%nat. }
    (* PermuteState, row 10: partial rounds 16 and 17. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 10%nat 16%nat 17%nat. }
    (* PermuteState, row 11: partial rounds 18 and 19. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 11%nat 18%nat 19%nat. }
    (* PermuteState, row 12: partial rounds 20 and 21. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 12%nat 20%nat 21%nat. }
    (* PermuteState, row 13: partial rounds 22 and 23. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 13%nat 22%nat 23%nat. }
    (* PermuteState, row 14: partial rounds 24 and 25. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 14%nat 24%nat 25%nat. }
    (* PermuteState, row 15: partial rounds 26 and 27. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 15%nat 26%nat 27%nat. }
    (* PermuteState, row 16: partial rounds 28 and 29. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 16%nat 28%nat 29%nat. }
    (* PermuteState, row 17: partial rounds 30 and 31. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 17%nat 30%nat 31%nat. }
    (* PermuteState, row 18: partial rounds 32 and 33. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 18%nat 32%nat 33%nat. }
    (* PermuteState, row 19: partial rounds 34 and 35. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 19%nat 34%nat 35%nat. }
    (* PermuteState, row 20: partial rounds 36 and 37. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 20%nat 36%nat 37%nat. }
    (* PermuteState, row 21: partial rounds 38 and 39. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 21%nat 38%nat 39%nat. }
    (* PermuteState, row 22: partial rounds 40 and 41. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 22%nat 40%nat 41%nat. }
    (* PermuteState, row 23: partial rounds 42 and 43. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 23%nat 42%nat 43%nat. }
    (* PermuteState, row 24: partial rounds 44 and 45. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 24%nat 44%nat 45%nat. }
    (* PermuteState, row 25: partial rounds 46 and 47. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 25%nat 46%nat 47%nat. }
    (* PermuteState, row 26: partial rounds 48 and 49. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 26%nat 48%nat 49%nat. }
    (* PermuteState, row 27: partial rounds 50 and 51. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 27%nat 50%nat 51%nat. }
    (* PermuteState, row 28: partial rounds 52 and 53. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 28%nat 52%nat 53%nat. }
    (* PermuteState, row 29: partial rounds 54 and 55. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 29%nat 54%nat 55%nat. }
    (* PermuteState, row 30: partial rounds 56 and 57. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 30%nat 56%nat 57%nat. }
    (* PermuteState, row 31: partial rounds 58 and 59. *)
    destruct Hpt as [Heq | Hpt]. { partial_case Heq Hb body w 31%nat 58%nat 59%nat. }
    (* PermuteState, row 32: full round 60. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 32%nat 60%nat. }
    (* PermuteState, row 33: full round 61. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 33%nat 61%nat. }
    (* PermuteState, row 34: full round 62. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 34%nat 62%nat. }
    (* PermuteState, row 35: full round 63. *)
    destruct Hpt as [Heq | Hpt]. { full_case Heq Hb body w 35%nat 63%nat. }
    destruct Hpt.
  Qed.

  Theorem poseidon_lookups_ok : family_lookups_ok [33].
  Proof.
    intros w Hvalid Hnondeg sel region row Hin Hfam arg Harg Hmention.
    exfalso.
    pose proof (poseidon_point_in sel region row Hin Hfam) as Hpt.
    pose proof (proj1 (List.forallb_forall _ (shard_in [33]))
      poseidon_no_lookup_mentions _ Hpt) as Hrow.
    cbn zeta in Hrow.
    pose proof (proj1 (List.forallb_forall _ _) Hrow arg Harg) as Hneg.
    cbn beta in Hneg.
    rewrite Hmention in Hneg.
    discriminate Hneg.
  Qed.

End OrchardForwardPoseidon.
