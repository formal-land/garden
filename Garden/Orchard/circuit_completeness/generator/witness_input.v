Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Garden.Orchard.circuit.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * The honest witness input and its derived values

    The shared spine of the Orchard completeness witness generator: the
    protocol-level auxiliary input of the Action statement (§4.18.4 of the
    Zcash protocol specification), the values the honest prover derives from
    it (commitments, nullifier, randomized key, ladder states, per-round hash
    accumulators — everything the circuit's advice plane carries), the typing
    envelope [valid], the exceptional-case exclusions [nondegenerate], and
    the completeness target [completeness_statement].

    Layering:

    - this file computes *values* only, reusing the specification layer
      ([OrchardProtocolSpec], [SinsemillaSpec], [Poseidon], [EccSpec],
      [Pallas]) — no cryptography is re-derived and no cell placement is
      fixed here;
    - the witness generator maps these values onto the concrete
      [(column, region, offset)] grid of [circuit.synthesize] and proves the
      resulting assignment satisfies [circuit_holds];
    - [completeness_statement] is stated here, abstracted over the generator
      ([honest_assignment] is a forward reference, passed as an argument);
      the assembly file instantiates it. *)

Module OrchardWitnessInput.
  Import OrchardActionInputs.

  (** ** The auxiliary input (§4.18.4)

      One record per action, carrying the §4.18.4 auxiliary-input bundle —
      the Merkle path and position, the old note's opening
      ([g_d], [pk_d], [v], [ρ], [ψ], [rcm]), the spend randomizer [α], the
      spend-authority data ([ak], [nk], [rivk]), the new note's fields, and
      the value-commitment trapdoor [rcv] — plus the primary-input
      passthroughs the circuit reads but §4.18.4 treats as public: the
      public anchor row (consumed verbatim on dummy spends, [v_old = 0]) and
      the [enableSpends] / [enableOutputs] flags.

      All numeric fields are plain [Z]; the type/range envelope is the
      separate predicate [valid] below.  [magnitude], [sign], [cm_old],
      [rho_new] and the anchor do not appear: they are derived values. *)
  Record HonestInput : Set := {
    (* Merkle authentication path: 32 sibling hashes, leaf position. *)
    hi_path : list Z;
    hi_pos : Z;
    (* Old note opening and spend data. *)
    hi_g_d_old : Point.t;
    hi_pk_d_old : Point.t;
    hi_v_old : Z;
    hi_rho_old : Z;
    hi_psi_old : Z;
    hi_rcm_old : Z;
    hi_alpha : Z;
    hi_ak : Point.t;
    hi_nk : Z;
    hi_rivk : Z;
    (* New note fields ([ρ_new] is derived: the old note's nullifier). *)
    hi_g_d_new : Point.t;
    hi_pk_d_new : Point.t;
    hi_v_new : Z;
    hi_psi_new : Z;
    hi_rcm_new : Z;
    (* Value-commitment trapdoor. *)
    hi_rcv : Z;
    (* Primary-input passthroughs. *)
    hi_anchor_public : Z;
    hi_enable_spends : Z;
    hi_enable_outputs : Z;
  }.

  (** ** Derived values: the honest prover's computations

      Each definition reuses the specification layer at the concrete circuit
      parameters ([orchard_circuit_params]); together they cover every value
      the generator writes into the advice plane. *)

  (** Position bit at layer [i]: whether the node is the right child.
      Protocol: §4.9, the [i]-th bit of the leaf position. *)
  Definition path_bit (w : HonestInput) (i : nat) : bool :=
    Z.testbit (hi_pos w) (Z.of_nat i).

  (** The path in the [ActionInputs] shape: layer index, sibling, swap bit
      per layer — the exact tuples [merkle_path_of] reads back from the
      generated assignment's cond-swap regions. *)
  Definition path_of (w : HonestInput) : list (Z * Z * bool) :=
    List.map
      (fun i => (Z.of_nat i, List.nth i (hi_path w) 0, path_bit w i))
      (List.seq 0%nat 32%nat).

  (** §5.4.8.4 [NoteCommit^Orchard] of the old note's opening — the
      commitment the witnessed [cm_old] point carries (§4.18.4 'Old note
      commitment integrity', honest branch). *)
  Definition cm_old (w : HonestInput) : Point.t :=
    OrchardProtocolSpec.note_commit orchard_circuit_params
      (hi_g_d_old w) (hi_pk_d_old w)
      (hi_v_old w) (hi_rho_old w) (hi_psi_old w) (hi_rcm_old w).

  (** The Merkle leaf: [Extract_P(cm_old)] (§4.9). *)
  Definition leaf (w : HonestInput) : Z :=
    EccSpec.extract_x (cm_old w).

  (** §4.18.4 'Nullifier integrity': [nf_old = DeriveNullifier_nk(ρ, ψ, cm)]
      (§4.16). *)
  Definition nf_old (w : HonestInput) : Z :=
    OrchardProtocolSpec.nullifier
      (hi_nk w) (hi_rho_old w) (hi_psi_old w) (cm_old w).

  (** The new note's [ρ]: the old note's nullifier (§4.18.4 note). *)
  Definition rho_new (w : HonestInput) : Z := nf_old w.

  (** §4.18.4 'Spend authority': [rk = ak + [α] 𝒢^Orchard]. *)
  Definition rk (w : HonestInput) : Point.t :=
    OrchardProtocolSpec.spend_auth_randomize (hi_ak w) (hi_alpha w).

  (** The net value's magnitude/sign split, as the circuit witnesses it:
      [v_old − v_new = magnitude · sign] with [sign ∈ {1, p − 1}]. *)
  Definition magnitude (w : HonestInput) : Z :=
    Z.abs (hi_v_old w - hi_v_new w).
  Definition sign (w : HonestInput) : Z :=
    if hi_v_new w <=? hi_v_old w then 1 else Primes.pallas_p - 1.

  (** §4.18.4 'Value commitment integrity':
      [cv_net = ValueCommit^Orchard_rcv(v_old − v_new)] (§5.4.8.3). *)
  Definition cv_net (w : HonestInput) : Point.t :=
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value (magnitude w) (sign w))
      (hi_rcv w).

  (** §4.18.4 'New note commitment integrity', honest branch:
      [cmx = Extract_P(NoteCommit^Orchard_rcm_new(…))] with
      [ρ_new = nf_old]. *)
  Definition cmx (w : HonestInput) : Z :=
    OrchardProtocolSpec.OrchardCmx orchard_circuit_params
      (hi_g_d_new w) (hi_pk_d_new w)
      (hi_v_new w) (rho_new w) (hi_psi_new w) (hi_rcm_new w).

  (** §4.9 'Merkle path validity': the root reached from the leaf along the
      authentication path.  The leaf is a parameter of [anchor_of_leaf] so
      that a caller already holding it — [inputs_of] does — reaches the root
      without recomputing [cm_old]. *)
  Definition anchor_of_leaf (w : HonestInput) (lf : Z) : Z :=
    OrchardSpec.anchor orchard_circuit_params lf (path_of w).

  Definition anchor_root (w : HonestInput) : Z :=
    anchor_of_leaf w (leaf w).

  (** The value of the public [ANCHOR] instance row: the passthrough on a
      dummy spend ([v_old = 0], where §4.18.4 waives path validity), the
      computed root otherwise (the [QOrchard] gate constrains
      [root = anchor] whenever [v_old ≠ 0]). *)
  Definition anchor_public_row_of_leaf (w : HonestInput) (lf : Z) : Z :=
    if hi_v_old w =? 0 then hi_anchor_public w else anchor_of_leaf w lf.

  Definition anchor_public_row (w : HonestInput) : Z :=
    anchor_public_row_of_leaf w (leaf w).

  (** §5.4.8.4 [Commit^ivk]: the incoming viewing key derived from
      [ak], [nk], [rivk] — the variable-base scalar of §4.18.4 'Diversified
      address integrity'. *)
  Definition ivk (w : HonestInput) : Z :=
    OrchardProtocolSpec.commit_ivk orchard_circuit_params
      (EccSpec.extract_x (hi_ak w)) (hi_nk w) (hi_rivk w).

  (** The nullifier's fixed-base scalar:
      [(PRF^nfOrchard_nk(ρ) + ψ) mod q_P] (§4.16). *)
  Definition nullifier_scalar (w : HonestInput) : Z :=
    Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w) +F hi_psi_old w.

  (** ** The [ActionInputs] record the readers reproduce

      [inputs_of w] is the [OrchardSpec.ActionInputs] record that
      [read_action_inputs] returns on the generated assignment.  The two
      constant pins mirror the reader ([in_pk_d_old := identity],
      [in_rivk := 0]: the public outputs do not depend on them, and the
      reader pins them so the determinism statement is witness-free); the
      genuine [pk_d_old] / [rivk] enter through the ownership conditions
      only. *)
  (** [cm_old] is a Sinsemilla commitment and [vm_compute] shares no work
      between two applications of the same function, so the commitment, the
      leaf extracted from it and the root folded over that leaf are bound
      once here instead of once per field that needs them. *)
  Definition inputs_of (w : HonestInput) : OrchardSpec.ActionInputs :=
    let cm := cm_old w in
    let lf := EccSpec.extract_x cm in
    {|
    OrchardSpec.in_ak := hi_ak w;
    OrchardSpec.in_nk := hi_nk w;
    OrchardSpec.in_rho_old := hi_rho_old w;
    OrchardSpec.in_psi_old := hi_psi_old w;
    OrchardSpec.in_cm_old := cm;
    OrchardSpec.in_g_d_old := hi_g_d_old w;
    OrchardSpec.in_pk_d_old := EccSpec.identity;
    OrchardSpec.in_v_old := hi_v_old w;
    OrchardSpec.in_rivk := 0;
    OrchardSpec.in_alpha := hi_alpha w;
    OrchardSpec.in_anchor_public := anchor_public_row_of_leaf w lf;
    OrchardSpec.in_rcv := hi_rcv w;
    OrchardSpec.in_magnitude := magnitude w;
    OrchardSpec.in_sign := sign w;
    OrchardSpec.in_leaf := lf;
    OrchardSpec.in_path := path_of w;
    OrchardSpec.in_g_d_new := hi_g_d_new w;
    OrchardSpec.in_pk_d_new := hi_pk_d_new w;
    OrchardSpec.in_v_new := hi_v_new w;
    OrchardSpec.in_psi_new := hi_psi_new w;
    OrchardSpec.in_rcm_new := hi_rcm_new w;
  |}.

  (** The action's public outputs on the honest input — the record the
      generated instance column carries. *)
  Definition outputs_of (w : HonestInput) : OrchardSpec.ActionOutputs :=
    OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
      (inputs_of w).

  (** ** Fixed-base legs: window digits, running sums, square-root witnesses

      Each fixed-base multiplication witnesses its scalar as 3-bit window
      cells with a running-sum decomposition ([z_{i} = k_i + 8·z_{i+1}],
      [z_0 = k]) and one square-root witness [u] per window. *)

  (** Running sum after [i] absorbed windows: [z_i = k / 8^i]. *)
  Definition running_sum_at (k : Z) (i : nat) : Z :=
    k / 8 ^ Z.of_nat i.

  (** The running-sum column [z_0 .. z_count]. *)
  Definition running_sums (k : Z) (count : nat) : list Z :=
    List.map (running_sum_at k) (List.seq 0%nat (S count)).

  (** The decomposition identity of one running-sum step. *)
  Lemma running_sum_step (k : Z) (i : nat) :
    running_sum_at k i =
      EccSpec.window_digit k i + 8 * running_sum_at k (S i).
  Proof.
    unfold running_sum_at, EccSpec.window_digit.
    assert (Hpos : 0 < 8 ^ Z.of_nat i) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite (Z.mul_comm 8 (8 ^ Z.of_nat i)).
    rewrite <- Z.div_div by lia.
    pose proof (Z.div_mod (k / 8 ^ Z.of_nat i) 8 ltac:(lia)) as Hdm.
    clear -Hdm. lia.
  Qed.

  (** The per-leg square-root witness lists: [canonical_us_for] at each
      leg's table and scalar, mirroring [canonical_witness]
      ([circuit_proof/inputs.v]). *)
  Definition us_alpha (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (hi_alpha w).
  Definition us_magnitude (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.value_commit_v orchard_internal_params)
      (magnitude w).
  Definition us_rcv (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.value_commit_r orchard_internal_params)
      (hi_rcv w).
  Definition us_nullifier (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      (nullifier_scalar w).
  Definition us_rcm_new (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (hi_rcm_new w).

  (** The two legs outside [ActionWitness]: the old note's blinding leg and
      the [Commit^ivk] blinding leg. *)
  Definition us_rcm_old (w : HonestInput) : list Z :=
    canonical_us_for (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (hi_rcm_old w).

  (** The five-leg witness record, bundled in the [ActionWitness] shape. *)
  Definition honest_witness (w : HonestInput)
      : OrchardCircuitSpec.ActionWitness := {|
    OrchardCircuitSpec.w_us_alpha := us_alpha w;
    OrchardCircuitSpec.w_us_v := us_magnitude w;
    OrchardCircuitSpec.w_us_rcv := us_rcv w;
    OrchardCircuitSpec.w_us_k := us_nullifier w;
    OrchardCircuitSpec.w_us_rcm := us_rcm_new w;
  |}.

  (** ** Poseidon: the permutation's per-row states

      The nullifier PRF's permutation region computes one schedule row per
      circuit row: four full rounds, twenty-eight partial-round pairs, four
      full rounds (36 rows).  [poseidon_round] is the row transition;
      [poseidon_state] iterates it, so [poseidon_state s n] is the state the
      row-[n] advice cells carry.  The round chain is never normalized (each
      unfolded round references its predecessor three times); consumers peel
      it row by row. *)
  Definition poseidon_round (row : nat) (s : State.t) : State.t :=
    if (row <? 4)%nat then Poseidon.apply_full row s
    else if (row <? 32)%nat then
      Poseidon.apply_partial (2 * row - 4)%nat (2 * row - 3)%nat s
    else Poseidon.apply_full (28 + row)%nat s.

  Definition poseidon_state (s : State.t) (n : nat) : State.t :=
    Stdlib.Lists.List.fold_left (fun t row => poseidon_round row t)
      (List.seq 0%nat n) s.

  (** The 36-row iterate is the P128Pow5T3 permutation.  The proof reduces
      the schedule bookkeeping only ([apply_full] / [apply_partial] stay
      folded), so both sides align as the same linear 36-deep chain. *)
  Lemma poseidon_state_permute (s : State.t) :
    poseidon_state s 36%nat = Poseidon.permute s.
  Proof.
    cbv beta iota zeta delta
      [poseidon_state poseidon_round List.seq Stdlib.Lists.List.fold_left
       Nat.ltb Nat.leb Nat.mul Nat.sub Nat.add Poseidon.permute].
    reflexivity.
  Qed.

  (** The permutation input state of the nullifier PRF:
      [{nk, ρ_old, 2⁶⁵}] (§5.4.1.10, [ConstantLength<2>]). *)
  Definition poseidon_input_state (w : HonestInput) : State.t := {|
    State.x0 := hi_nk w;
    State.x1 := hi_rho_old w;
    State.x2 := Poseidon.domain_iv_constant_length_2;
  |}.

  Definition poseidon_round_state (w : HonestInput) (n : nat) : State.t :=
    poseidon_state (poseidon_input_state w) n.

  (** The squeezed lane of the final row state is the PRF output.  The
      permutation application is aligned syntactically before
      [reflexivity] (never hand conversion two sides that differ under
      [permute]). *)
  Lemma poseidon_round_state_hash2 (w : HonestInput) :
    State.x0 (poseidon_round_state w 36%nat) =
      Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w).
  Proof.
    unfold poseidon_round_state.
    rewrite poseidon_state_permute.
    unfold poseidon_input_state, Poseidon.poseidon_hash2.
    reflexivity.
  Qed.

  (** ** Sinsemilla: per-round accumulator points

      Each hash-to-point region carries, per round, the accumulator after
      that round; [sinsemilla_acc Q words n] is the accumulator after [n]
      absorbed words (§5.4.1.9: [Acc ← (Acc ⊕ 𝒮(m)) ⊕ Acc] from [Q]). *)
  Definition sinsemilla_acc (Q : Point.t) (words : list Z) (n : nat)
      : Point.t :=
    SinsemillaSpec.sinsemilla_hash_to_point Q (List.firstn n words).

  Lemma sinsemilla_acc_zero (Q : Point.t) (words : list Z) :
    sinsemilla_acc Q words 0%nat = Q.
  Proof. reflexivity. Qed.

  Lemma firstn_succ_nth {A : Type} (d : A) (l : list A) :
    forall n : nat,
      (n < List.length l)%nat ->
      List.firstn (S n) l = List.firstn n l ++ [List.nth n l d].
  Proof.
    induction l as [| x l IH]; intros n Hn.
    - cbn [List.length] in Hn. lia.
    - destruct n as [| n].
      + reflexivity.
      + rewrite !List.firstn_cons.
        cbn [List.nth List.app].
        rewrite (IH n) by (cbn [List.length] in Hn; lia).
        reflexivity.
  Qed.

  (** One more round extends the accumulator by one [round] step. *)
  Lemma sinsemilla_acc_succ (Q : Point.t) (words : list Z) (n : nat) :
    (n < List.length words)%nat ->
    sinsemilla_acc Q words (S n) =
      SinsemillaSpec.round (sinsemilla_acc Q words n)
        (List.nth n words 0).
  Proof.
    intro Hn.
    unfold sinsemilla_acc.
    rewrite (firstn_succ_nth 0 words n Hn).
    apply SinsemillaSpec.sinsemilla_hash_to_point_app.
  Qed.

  Lemma sinsemilla_acc_full (Q : Point.t) (words : list Z) :
    sinsemilla_acc Q words (List.length words) =
      SinsemillaSpec.sinsemilla_hash_to_point Q words.
  Proof. unfold sinsemilla_acc. rewrite List.firstn_all. reflexivity. Qed.

  (** The four hash families of the circuit: the messages... *)

  (** The 109-word old-note message (§5.4.8.4 [NoteCommit^Orchard]). *)
  Definition note_commit_old_words (w : HonestInput) : list Z :=
    OrchardSpec.note_commit_message (hi_g_d_old w) (hi_pk_d_old w)
      (hi_v_old w) (hi_rho_old w) (hi_psi_old w).

  (** The 109-word new-note message ([ρ_new = nf_old]). *)
  Definition note_commit_new_words (w : HonestInput) : list Z :=
    OrchardSpec.note_commit_message (hi_g_d_new w) (hi_pk_d_new w)
      (hi_v_new w) (rho_new w) (hi_psi_new w).

  (** The 51-word [Commit^ivk] message (§5.4.8.4). *)
  Definition commit_ivk_words (w : HonestInput) : list Z :=
    OrchardSpec.commit_ivk_message
      (EccSpec.extract_x (hi_ak w)) (hi_nk w).

  (** The Merkle CRH domain point (the [q_*] synthesis constants). *)
  Definition merkle_Q : Point.t :=
    OrchardSpec.merkle_crh_q orchard_circuit_params.

  (** The running node hash after [i] Merkle layers ([merkle_root] on the
      path prefix; [merkle_node w 0 = leaf w]). *)
  Definition merkle_node (w : HonestInput) (i : nat) : Z :=
    SinsemillaSpec.merkle_root merkle_Q (leaf w)
      (List.firstn i (path_of w)).

  (** The 52-word message hashed at layer [i] (§5.4.1.3): the layer prefix
      and the two children in position order. *)
  Definition merkle_layer_words (w : HonestInput) (i : nat) : list Z :=
    let node := merkle_node w i in
    let sibling := List.nth i (hi_path w) 0 in
    if path_bit w i
    then SinsemillaSpec.merkle_message (Z.of_nat i) sibling node
    else SinsemillaSpec.merkle_message (Z.of_nat i) node sibling.

  (** One layer advances the running node by [merkle_layer]. *)
  Lemma merkle_node_succ (w : HonestInput) (i : nat) :
    (i < 32)%nat ->
    merkle_node w (S i) =
      SinsemillaSpec.merkle_layer merkle_Q (Z.of_nat i)
        (merkle_node w i) (List.nth i (hi_path w) 0) (path_bit w i).
  Proof.
    intro Hi.
    unfold merkle_node.
    rewrite (firstn_succ_nth (0, 0, false) (path_of w) i)
      by (unfold path_of;
          rewrite List.length_map, List.length_seq; exact Hi).
    unfold SinsemillaSpec.merkle_root.
    rewrite Stdlib.Lists.List.fold_left_app.
    cbn [Stdlib.Lists.List.fold_left].
    unfold path_of.
    rewrite (nth_map_seq
      (fun j : nat => (Z.of_nat j, List.nth j (hi_path w) 0, path_bit w j))
      32%nat i (0, 0, false) Hi).
    reflexivity.
  Qed.

  (** The layer hash consumes exactly [merkle_layer_words]. *)
  Lemma merkle_layer_words_spec (w : HonestInput) (i : nat) :
    SinsemillaSpec.merkle_layer merkle_Q (Z.of_nat i)
      (merkle_node w i) (List.nth i (hi_path w) 0) (path_bit w i) =
    SinsemillaSpec.sinsemilla_hash merkle_Q (merkle_layer_words w i).
  Proof.
    unfold SinsemillaSpec.merkle_layer, SinsemillaSpec.merkle_crh,
      merkle_layer_words.
    destruct (path_bit w i); reflexivity.
  Qed.

  (** ** Variable-base mul: the [[ivk] g_d_old] ladder values

      The mul chip witnesses the 255-bit decomposition of [ivk + t_q]
      (the running sum recovered by the overflow block equals [ivk + t_q]
      over the integers) and maintains, after processing bits down to index
      [i], the accumulator [[2^(255−i) + 2·z_i + 1] B]. *)

  (** Bit [i] of [k] and the bit-level running sum [z_i = k / 2^i]. *)
  Definition scalar_bit (k : Z) (i : nat) : Z :=
    (k / 2 ^ Z.of_nat i) mod 2.
  Definition bit_running_sum (k : Z) (i : nat) : Z :=
    k / 2 ^ Z.of_nat i.

  Lemma bit_running_sum_step (k : Z) (i : nat) :
    bit_running_sum k i =
      scalar_bit k i + 2 * bit_running_sum k (S i).
  Proof.
    unfold bit_running_sum, scalar_bit.
    assert (Hpos : 0 < 2 ^ Z.of_nat i) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite (Z.mul_comm 2 (2 ^ Z.of_nat i)).
    rewrite <- Z.div_div by lia.
    pose proof (Z.div_mod (k / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hdm.
    clear -Hdm. lia.
  Qed.

  (** The mul chip's scalar: [ivk + t_q] ([q_P = 2^254 + t_q], so the sum is
      [ivk] modulo the group order and fits in 255 bits). *)
  Definition mul_scalar (w : HonestInput) : Z :=
    ivk w + Primes.t_q.

  Definition mul_base (w : HonestInput) : Pallas.point :=
    PallasModel.unrepr (hi_g_d_old w).

  (** The accumulator's multiple at bit boundary [i] (bits [254..i]
      processed): [2^(255−i) + 2·z_i + 1]. *)
  Definition mul_multiple (w : HonestInput) (i : nat) : Z :=
    2 ^ (255 - Z.of_nat i) + 2 * bit_running_sum (mul_scalar w) i + 1.

  (** The ladder accumulator point at bit boundary [i]; at [i = 255] this is
      the initial doubling [[2] B]. *)
  Definition mul_acc (w : HonestInput) (i : nat) : Point.t :=
    PallasModel.repr
      (Pallas.mul (mul_multiple w i) (mul_base w)).

  (** Affine negation in the chip's coordinate representation. *)
  Definition point_neg (P : Point.t) : Point.t := {|
    Point.x := Point.x P;
    Point.y := 0 -F Point.y P;
  |}.

  (** The point one double-and-add step adds: [B] on bit 1, [−B] on bit 0
      ([[2k−1] B]). *)
  Definition mul_step_point (w : HonestInput) (i : nat) : Point.t :=
    if scalar_bit (mul_scalar w) i =? 1
    then hi_g_d_old w
    else point_neg (hi_g_d_old w).

  (** ** Nondegeneracy: the exceptional-case exclusions

      §4.18.4 weakens its conditions on the exceptional cases of incomplete
      addition ([∈ {cm, ⊥}], [ivk = ⊥ ∨ …], the Merkle hash-⊥-to-0
      allowance); on those cases the circuit leaves witness values
      unconstrained, so the completeness domain excludes them.  The clauses
      below are stated over the spec-computed honest values, shaped so that
      reading the generated assignment back turns them into the honesty
      predicates of the soundness surface:

      - the Merkle clause into [OrchardActionMerkle.merkle_witness_ok]'s
        per-layer [SinsemillaHash.nondegenerate] conjunct (its canonicity
        conjunct holds by construction: the generator decomposes in-range
        hashes canonically);
      - the note-commitment clauses into the [SinsemillaHash.nondegenerate]
        conjuncts of [NoteCommitNewCmx.note_commit_witness_ok] and
        [OrchardValidActionInputs.old_note_witness_ok] (their short-lookup
        conjuncts hold by construction);
      - the [Commit^ivk] and mul clauses into
        [OrchardValidActionInputs.commit_ivk_witness_ok] (the hash
        nondegeneracy and [VarBaseMul.mul_nondegenerate] conjuncts).

      The shaping is a design correspondence, not a theorem: no lemma
      derives those predicates at [honest_assignment w], so the completeness
      surface certifies [circuit_holds] rather than the hypotheses of the
      Action statement. *)

  (** One incomplete double-and-add step is nondegenerate: the accumulator
      is affine (no curve point has [x = 0]), the first chord is
      non-vertical ([x_acc ≠ x_B]; [B] and [−B] share [x]), and the second
      chord is non-vertical (the intermediate sum's [x] differs from the
      accumulator's). *)
  Definition mul_step_nondegenerate (w : HonestInput) (i : nat) : Prop :=
    let acc := mul_acc w (S i) in
    Point.x acc <> 0 /\
    Point.x acc <> Point.x (hi_g_d_old w) /\
    Point.x (EccSpec.point_add_incomplete acc (mul_step_point w i)) <>
      Point.x acc.

  (** All incomplete steps of both mul halves: bits [254..130] (hi) and
      [129..4] (lo); bits [3..0] use complete addition. *)
  Definition mul_nondegenerate_input (w : HonestInput) : Prop :=
    forall i : nat, (4 <= i < 255)%nat -> mul_step_nondegenerate w i.

  Definition nondegenerate (w : HonestInput) : Prop :=
    (forall i : nat, (i < 32)%nat ->
      SinsemillaHash.nondegenerate merkle_Q (merkle_layer_words w i)) /\
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_old_words w) /\
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_new_words w) /\
    SinsemillaHash.nondegenerate
      (OrchardSpec.commit_ivk_q orchard_circuit_params)
      (commit_ivk_words w) /\
    mul_nondegenerate_input w.

  (** ** The typing envelope and input-side conditions

      [point_ok]: an on-curve, non-identity Pallas point with reduced
      coordinates — the §4.18.4 point type [P*]. *)
  Definition point_ok (P : Point.t) : Prop :=
    Pallas.reduced (PallasModel.unrepr P) /\
    Pallas.on_curve (PallasModel.unrepr P) /\
    P <> EccSpec.identity.

  (** The §4.18.4 type envelope: 64-bit values, scalars below the group
      order [q_P], base-field elements below [p_P], points in [P*], a
      32-layer path of field elements, a 32-bit position, boolean flags.
      Decomposition canonicity needs no clause: every §4.18.4 canonicity
      MUST concerns witnessed decompositions, and the generator decomposes
      these in-range values canonically. *)
  Definition well_typed (w : HonestInput) : Prop :=
    0 <= hi_v_old w < 2 ^ 64 /\
    0 <= hi_v_new w < 2 ^ 64 /\
    0 <= hi_alpha w < Primes.pallas_q /\
    0 <= hi_rcv w < Primes.pallas_q /\
    0 <= hi_rcm_old w < Primes.pallas_q /\
    0 <= hi_rcm_new w < Primes.pallas_q /\
    0 <= hi_rivk w < Primes.pallas_q /\
    0 <= hi_nk w < Primes.pallas_p /\
    0 <= hi_rho_old w < Primes.pallas_p /\
    0 <= hi_psi_old w < Primes.pallas_p /\
    0 <= hi_psi_new w < Primes.pallas_p /\
    0 <= hi_anchor_public w < Primes.pallas_p /\
    point_ok (hi_ak w) /\
    point_ok (hi_g_d_old w) /\
    point_ok (hi_pk_d_old w) /\
    point_ok (hi_g_d_new w) /\
    point_ok (hi_pk_d_new w) /\
    List.length (hi_path w) = 32%nat /\
    List.Forall (fun s => 0 <= s < Primes.pallas_p) (hi_path w) /\
    0 <= hi_pos w < 2 ^ 32 /\
    (hi_enable_spends w = 0 \/ hi_enable_spends w = 1) /\
    (hi_enable_outputs w = 0 \/ hi_enable_outputs w = 1).

  (** [valid]: the type envelope plus the input-side §4.18.4 conditions the
      circuit checks against free witness fields — the two enable-flag
      clauses ([v_old ≠ 0 ⇒ enableSpends], [v_new ≠ 0 ⇒ enableOutputs]) and
      'Diversified address integrity' ([pk_d_old = [ivk] g_d_old], honest
      branch; [ivk ≠ ⊥]).  The remaining §4.18.4 conditions constrain
      derived values only, so they hold by construction: old and new note
      commitment integrity ([cm_old] / [cmx] are computed), nullifier
      integrity, spend authority, value-commitment integrity, and Merkle
      path validity via [anchor_public_row]. *)
  Definition valid (w : HonestInput) : Prop :=
    well_typed w /\
    (hi_v_old w = 0 \/ hi_enable_spends w = 1) /\
    (hi_v_new w = 0 \/ hi_enable_outputs w = 1) /\
    hi_pk_d_old w =
      PallasModel.repr
        (Pallas.mul (ivk w) (PallasModel.unrepr (hi_g_d_old w))).

  (** ** The completeness target

      The in-model residue of §4.1.13 completeness at the §4.18.4 Action
      statement: every valid, nondegenerate honest input yields a satisfying
      assignment whose free-witness cells read back as the input record.
      Stated over the generator as an argument ([honest_assignment] is
      defined downstream); the assembly file instantiates it and proves the
      resulting proposition. *)
  Definition completeness_statement
      (honest_assignment : HonestInput -> Assignment.t columns RegionId.t)
      : Prop :=
    forall w : HonestInput,
      valid w ->
      nondegenerate w ->
      circuit_holds (honest_assignment w)
        Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
      read_action_inputs (honest_assignment w) = inputs_of w.

End OrchardWitnessInput.
