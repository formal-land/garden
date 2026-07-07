Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit.gadget.add_chip_proof.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.constants.fixed_bases.spend_auth_g.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Garden.Orchard.constants.fixed_bases.commit_ivk_r.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.circuit_proof.fixed_base.congruence.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.witness_point_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.setoid_ring.Ring.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module OrchardActionInputs.
  (* The circuit's free degrees of freedom — the regions whose advice cells the
     prover witnesses via [assign_free_advice] / [witness_point], audited across
     all of [circuit.synthesize] and its helpers.  An Orchard action ranges over
     four input groups:
       - the OLD note, witnessed in [RegionId.WitnessInput.*] (psi_old, rho_old,
         cm_old, g_d_old, ak_P, nk, v_old, v_new);
       - the NEW note's diversified base / public key / randomness, witnessed in
         [NoteCommitNewWitnessGD] / [NoteCommitNewWitnessPkD] /
         [NoteCommitNewWitnessPsi];
       - the net value's [magnitude] / [sign], witnessed in
         [ValueCommitment.MagnitudeRangeCheck] / [SignRangeCheck];
       - the Merkle authentication path's sibling / position per layer,
         witnessed in [RegionId.Merkle _ Merkle.Region.NodePosition];
       - the per-window square-root witnesses [u] of each fixed-base
         multiplication, witnessed in its running-sum region (the [Incomplete]
         region of [SpendAuthority] / [ValueCommitment] V & R / [Nullifier]
         base-field / new-note [NoteCommit]).
     In this relational model the [u] cells are treated as part of the witness
     (the model reads them as advice; sharpening them to *determined* by the
     scalar is the canonical-soundness content).  Every other advice cell is a
     [Copy] target or a gate output, hence determined by these. *)
  Definition free_witness_region (region : RegionId.t) : Prop :=
    (exists w : RegionId.WitnessInput.t, region = RegionId.WitnessInput w) \/
    region = RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck \/
    region = RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck \/
    region = RegionId.NoteCommitNewWitnessGD \/
    region = RegionId.NoteCommitNewWitnessPkD \/
    region = RegionId.NoteCommitNewWitnessPsi \/
    (exists layer : RegionId.Merkle.Layer.t,
       region = RegionId.Merkle layer RegionId.Merkle.Region.NodePosition) \/
    region = RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete \/
    region = RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete \/
    region = RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete \/
    region = RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete \/
    region =
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete.

  (* Layout-specific free-witness readers.  Each input reader below mirrors the
     cells returned by [circuit.synthesize] and its helper gadgets; this is what
     lets the top-level determinism statement say "the public outputs are the
     function of the actual free witness cells", just like the smaller chip
     theorems. *)
  Definition read_advice
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (row : Z) : Z :=
    Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row).

  Definition read (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A0 region 0.
  Definition read1 (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A1 region 0.
  Definition read2 (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A2 region 0.
  Definition read4 (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A4 region 0.
  Definition read6 (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A6 region 0.
  Definition read9 (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Z :=
    read_advice Γ Advice.A9 region 0.
  Definition read_point
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) : Point.t := {|
    Point.x := read Γ region;
    Point.y := read1 Γ region;
  |}.

  (* The Merkle authentication path: 32 layers, each read from its
     [NodePosition] region.  The cond-swap layout puts, at row 0, the node on
     the [a] column, the witnessed sibling on the [b] column, and the
     boolean-checked position bit on the [swap] column — on [A0]/[A1]/[A4]
     for layers 0–15 ([QCondSwap1]) and [A5]/[A6]/[A9] for layers 16–31
     ([QCondSwap2]) ([synthesize_node_position_{1,2}], [cond_swap_gate]).
     The gate's boolean constraint on [swap] makes the [=? 1] decode
     faithful. *)
  Definition merkle_path_of
      (Γ : Assignment.t columns RegionId.t) : list (Z * Z * bool) :=
    Stdlib.Lists.List.map
      (fun i =>
        let region :=
          RegionId.Merkle (RegionId.Merkle.Layer.of_index (Z.of_nat i))
            RegionId.Merkle.Region.NodePosition in
        if Z.of_nat i <? 16
        then (Z.of_nat i, read1 Γ region, Z.eqb (read4 Γ region) 1)
        else (Z.of_nat i, read6 Γ region, Z.eqb (read9 Γ region) 1))
      (Stdlib.Lists.List.seq 0%nat 32%nat).

  (* Full-width fixed-base scalar multiplication lazily witnesses the scalar as
     3-bit window cells on [A4] of its incomplete region.  There is no separate
     scalar cell in the synthesized layout, so the proof-side input scalar is
     reconstructed from those windows. *)
  Fixpoint scalar_from_windows_aux (windows : list Z) (i : nat) : Z :=
    match windows with
    | [] => 0
    | window :: windows =>
        window * 8 ^ Z.of_nat i + scalar_from_windows_aux windows (S i)
    end.

  Definition scalar_from_windows (windows : list Z) : Z :=
    scalar_from_windows_aux windows 0%nat.

  Lemma scalar_from_windows_aux_shift1 (windows : list Z) :
    forall i : nat,
      scalar_from_windows_aux windows (S i) =
        8 * scalar_from_windows_aux windows i.
  Proof.
    induction windows as [| w windows IH]; intros i;
      cbn [scalar_from_windows_aux].
    - lia.
    - rewrite (IH (S i)).
      replace (8 ^ Z.of_nat (S i)) with (8 * 8 ^ Z.of_nat i) by
        (rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r; lia).
      ring.
  Qed.

  Lemma scalar_from_windows_cons (w : Z) (windows : list Z) :
    scalar_from_windows (w :: windows) =
      w + 8 * scalar_from_windows windows.
  Proof.
    unfold scalar_from_windows.
    cbn [scalar_from_windows_aux].
    rewrite scalar_from_windows_aux_shift1.
    replace (8 ^ Z.of_nat 0) with 1 by reflexivity.
    ring.
  Qed.

  Lemma window_digit_cons_succ
      (w n : Z) (i : nat) :
    0 <= w < 8 ->
    0 <= n ->
    EccSpec.window_digit (w + 8 * n) (S i) =
      EccSpec.window_digit n i.
  Proof.
    intros Hw Hn.
    unfold EccSpec.window_digit.
    set (P := 8 ^ Z.of_nat i).
    assert (HPpos : 0 < P).
    { subst P. apply Z.pow_pos_nonneg; lia. }
    replace (8 ^ Z.of_nat (S i)) with (8 * P).
    2:{ subst P. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r; lia. }
    replace ((w + 8 * n) / (8 * P)) with (n / P).
    { reflexivity. }
    apply Z.div_unique with (r := w + 8 * (n mod P)).
    - left. pose proof (Z.mod_pos_bound n P HPpos). lia.
    - rewrite (Z.div_mod n P ltac:(lia)) at 1.
      ring.
  Qed.

  Lemma scalar_from_windows_nonnegative
      (windows : list Z) :
    List.Forall (fun w => 0 <= w) windows ->
    0 <= scalar_from_windows windows.
  Proof.
    induction windows as [| w windows IH]; intros Hbounded.
    - unfold scalar_from_windows.
      cbn [scalar_from_windows_aux].
      lia.
    - inversion Hbounded as [| ? ? Hw Htail]; subst.
      rewrite scalar_from_windows_cons.
      specialize (IH Htail).
      lia.
  Qed.

  Lemma window_digit_scalar_from_windows_nth
      (windows : list Z) :
    forall i : nat,
      List.Forall (fun w => 0 <= w < 8) windows ->
      (i < List.length windows)%nat ->
      EccSpec.window_digit (scalar_from_windows windows) i =
        List.nth i windows 0.
  Proof.
    induction windows as [| w windows IH]; intros i Hbounded Hi.
    - cbn in Hi. lia.
    - inversion Hbounded as [| ? ? Hw Htail]; subst.
      destruct i as [| i].
      + rewrite scalar_from_windows_cons.
        unfold EccSpec.window_digit.
        cbn [List.nth].
        replace (8 ^ Z.of_nat 0) with 1 by reflexivity.
        rewrite Z.div_1_r.
        replace (w + 8 * scalar_from_windows windows) with
          (w + scalar_from_windows windows * 8) by ring.
        rewrite Z.mod_add by lia.
        apply Z.mod_small. exact Hw.
      + cbn [List.nth].
        rewrite scalar_from_windows_cons.
        rewrite window_digit_cons_succ.
        * apply IH.
          -- exact Htail.
          -- cbn in Hi. lia.
        * exact Hw.
        * apply scalar_from_windows_nonnegative.
          eapply List.Forall_impl; [| exact Htail].
          intros x Hx. cbn in Hx. lia.
  Qed.

  Definition read_windows
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (count : nat)
      : list Z :=
    Stdlib.Lists.List.map
      (fun i => read_advice Γ Advice.A4 region (Z.of_nat i))
      (Stdlib.Lists.List.seq 0%nat count).

  Lemma read_windows_nth
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (count i : nat) :
    (i < count)%nat ->
    List.nth i (read_windows Γ region count) 0 =
      read_advice Γ Advice.A4 region (Z.of_nat i).
  Proof.
    intros Hi.
    unfold read_windows.
    exact (nth_map_seq
      (fun j : nat => read_advice Γ Advice.A4 region (Z.of_nat j))
      count i 0 Hi).
  Qed.

  Definition read_scalar_from_windows
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (count : nat)
      : Z :=
    scalar_from_windows (read_windows Γ region count).

  Lemma window_digit_read_scalar_from_windows
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (count i : nat) :
    List.Forall (fun w => 0 <= w < 8) (read_windows Γ region count) ->
    (i < count)%nat ->
    EccSpec.window_digit (read_scalar_from_windows Γ region count) i =
      read_advice Γ Advice.A4 region (Z.of_nat i).
  Proof.
    intros Hbounded Hi.
    unfold read_scalar_from_windows.
    rewrite (window_digit_scalar_from_windows_nth
      (read_windows Γ region count) i Hbounded).
    - apply read_windows_nth. exact Hi.
    - unfold read_windows. rewrite List.length_map, List.length_seq. exact Hi.
  Qed.

  (* The per-window square-root witnesses [u] of a fixed-base multiplication:
     [count] windows, each read on [A5] of the incomplete [region].  [A4] is the
     scalar window / running-sum column, not the [u] column. *)
  Definition read_us
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (count : nat)
      : list Z :=
    Stdlib.Lists.List.map
      (fun i => read_advice Γ Advice.A5 region (Z.of_nat i))
      (Stdlib.Lists.List.seq 0%nat count).

  Lemma read_us_nth
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (count i : nat) :
    (i < count)%nat ->
    List.nth i (read_us Γ region count) 0 =
      read_advice Γ Advice.A5 region (Z.of_nat i).
  Proof.
    intros Hi.
    unfold read_us.
    exact (nth_map_seq
      (fun j : nat => read_advice Γ Advice.A5 region (Z.of_nat j))
      count i 0 Hi).
  Qed.

  (* Public instance rows are read through expression evaluation, matching the
     smaller chip determinism statements.  The chosen region is irrelevant for
     [Expression.Instance_]; only the row and rotation are used. *)
  Definition read_public_instance
      (Γ : Assignment.t columns RegionId.t) (row : Z) : Z :=
    Γ ⊢ ⟦ Expression.Instance_ Instance_.Primary Rotation.cur ⟧
      (RegionId.OrchardCircuitChecks, row).

  (* The whole-action input bundle read from Γ's free-witness cells.  The anchor
     public row is an explicit parameter because the circuit treats it as a
     passthrough value on disabled-spend actions.  The fields the public outputs
     do not depend on ([pk_d_old], [rivk]) are pinned to constants. *)
  Definition read_action_inputs_with_anchor
      (Γ : Assignment.t columns RegionId.t) (anchor_public : Z)
      : OrchardSpec.ActionInputs := {|
    OrchardSpec.in_ak :=
      read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.AkP);
    OrchardSpec.in_nk := read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk);
    OrchardSpec.in_rho_old := read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld);
    OrchardSpec.in_psi_old := read Γ (RegionId.WitnessInput RegionId.WitnessInput.PsiOld);
    OrchardSpec.in_cm_old :=
      read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld);
    OrchardSpec.in_g_d_old :=
      read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.GDOld);
    OrchardSpec.in_pk_d_old := EccSpec.identity;
    OrchardSpec.in_v_old := read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld);
    OrchardSpec.in_rivk := 0;
    OrchardSpec.in_alpha :=
      read_scalar_from_windows Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete) 85;
    OrchardSpec.in_anchor_public := anchor_public;
    OrchardSpec.in_rcv :=
      read_scalar_from_windows Γ
        (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete) 85;
    OrchardSpec.in_magnitude :=
      read9 Γ (RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck);
    OrchardSpec.in_sign :=
      read9 Γ (RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck);
    OrchardSpec.in_leaf := read Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld);
    OrchardSpec.in_path := merkle_path_of Γ;
    OrchardSpec.in_g_d_new := read_point Γ RegionId.NoteCommitNewWitnessGD;
    OrchardSpec.in_pk_d_new := read_point Γ RegionId.NoteCommitNewWitnessPkD;
    OrchardSpec.in_v_new := read Γ (RegionId.WitnessInput RegionId.WitnessInput.VNew);
    OrchardSpec.in_psi_new := read Γ RegionId.NoteCommitNewWitnessPsi;
    OrchardSpec.in_rcm_new :=
      read_scalar_from_windows Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
           RegionId.NoteCommit.FixedBaseIncomplete) 85;
  |}.

  Definition read_action_inputs
      (Γ : Assignment.t columns RegionId.t) : OrchardSpec.ActionInputs :=
    read_action_inputs_with_anchor Γ
      (read_public_instance Γ Garden.Orchard.circuit.ANCHOR).

  (* The fixed-base square-root witnesses, read from advice [A5] of each
     incomplete region — the [ActionWitness] companion to [read_action_inputs].
     These are the benign nondeterminism the public outputs depend on only
     through [u²]; [read_action_inputs] does not carry them. *)
  Definition read_action_witness
      (Γ : Assignment.t columns RegionId.t) : OrchardSpec.ActionWitness := {|
    OrchardSpec.w_us_alpha :=
      read_us Γ (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete) 85;
    OrchardSpec.w_us_v :=
      read_us Γ
        (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete) 22;
    OrchardSpec.w_us_rcv :=
      read_us Γ
        (RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete) 85;
    OrchardSpec.w_us_k :=
      read_us Γ (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 85;
    OrchardSpec.w_us_rcm :=
      read_us Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
           RegionId.NoteCommit.FixedBaseIncomplete) 85;
  |}.

  (* The public outputs read from the [Instance_.Primary] column, packaged as an
     [OrchardSpec.ActionOutputs] after field-expression evaluation.  The
     [CV_NET]/[RK] rows are the coordinates of the value-commitment /
     spend-auth points.  This is the "output record" side of the chip-style
     equation [outputs Γ = output (inputs Γ)]. *)
  Definition read_action_outputs
      (Γ : Assignment.t columns RegionId.t) : OrchardSpec.ActionOutputs := {|
    OrchardSpec.out_anchor :=
      read_public_instance Γ Garden.Orchard.circuit.ANCHOR;
    OrchardSpec.out_cv_net := {|
      Point.x :=
        read_public_instance Γ Garden.Orchard.circuit.CV_NET_X;
      Point.y :=
        read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y;
    |};
    OrchardSpec.out_nf_old :=
      read_public_instance Γ Garden.Orchard.circuit.NF_OLD;
    OrchardSpec.out_rk := {|
      Point.x :=
        read_public_instance Γ Garden.Orchard.circuit.RK_X;
      Point.y :=
        read_public_instance Γ Garden.Orchard.circuit.RK_Y;
    |};
    OrchardSpec.out_cmx :=
      read_public_instance Γ Garden.Orchard.circuit.CMX;
  |}.

  (* Discharge a [free_witness_region] obligation: scan the disjunction, taking
     [left] (with [eexists] for the existential cases) or stepping [right]. *)
  Ltac fwr :=
    unfold free_witness_region;
    repeat
      first [ reflexivity | left; eexists; reflexivity | left; reflexivity | right ].

  (* The fixed public Orchard parameters, as a genuine [Definition] from the
     circuit's own constants: the Sinsemilla domain points are the affine
     [q_*] literals, and the six fixed-base generators are the windowed Lagrange
     tables.  Nothing here is abstract — so the functional theorem below is
     about a *single* concrete value and is not refutable. *)
  Definition orchard_circuit_params : OrchardSpec.Params := {|
    OrchardSpec.spend_auth_g :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows;
    OrchardSpec.value_commit_v :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.value_commit_v.short_fixed_rows;
    OrchardSpec.value_commit_r :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows;
    OrchardSpec.nullifier_k :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows;
    OrchardSpec.note_commit_q := {|
      Point.x := Garden.Orchard.circuit.note_commit.q_note_commit_m_x;
      Point.y := Garden.Orchard.circuit.note_commit.q_note_commit_m_y;
    |};
    OrchardSpec.note_commit_r :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows;
    OrchardSpec.commit_ivk_q := {|
      Point.x := Garden.Orchard.circuit.commit_ivk.q_commit_ivk_m_x;
      Point.y := Garden.Orchard.circuit.commit_ivk.q_commit_ivk_m_y;
    |};
    OrchardSpec.commit_ivk_r :=
      EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows;
    OrchardSpec.merkle_crh_q := {|
      Point.x := Garden.Orchard.circuit.merkle_q_x;
      Point.y := Garden.Orchard.circuit.merkle_q_y;
    |};
  |}.

  (* Abbreviation for "Γ is a satisfying assignment of the Orchard circuit". *)
  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* Whole-action output for a GIVEN square-root witness: the spec at the concrete
     circuit parameters.  The witness ([ActionWitness]) is the benign square-root
     nondeterminism, kept separate from the genuine inputs. *)
  Definition output_with_witness (inputs : OrchardSpec.ActionInputs)
      (wit : OrchardSpec.ActionWitness)
      : OrchardSpec.ActionOutputs :=
    OrchardSpec.orchard_action_spec orchard_circuit_params inputs wit.

  (* The Orchard action's output record as the spec computes it from the cells
     read out of Γ.  Naming it keeps the (large) spec application out of the
     per-output statements and internal proof terms. *)
  Definition action_spec_of (Γ : Assignment.t columns RegionId.t)
      : OrchardSpec.ActionOutputs :=
    output_with_witness (read_action_inputs Γ) (read_action_witness Γ).

  (* The canonical square-root list for scalar [k] over table [tbl]: per window,
     the [u] whose square is the canonical window point's [y + z].  Feeding these
     to the witness-carrying spec reproduces the canonical (witness-free) points. *)
  Fixpoint canonical_us_for_aux
      (ws : EccSpec.fixed_table) (k : Z) (i : nat) : list Z :=
    match ws with
    | nil => nil
    | w :: ws' =>
        field_sqrt
          (Point.y (fixed_window_point_canonical w (EccSpec.window_digit k i))
            +F EccSpec.fw_z w)
        :: canonical_us_for_aux ws' k (S i)
    end.
  Definition canonical_us_for (tbl : EccSpec.fixed_table) (k : Z) : list Z :=
    canonical_us_for_aux tbl k 0%nat.

  (* The witness reconstructed from the genuine inputs alone: the canonical square
     roots for each fixed-base multiplication's scalar (exactly the scalars
     [orchard_action_spec] feeds to [fixed_scalar_mul]). *)
  Definition canonical_witness (inp : OrchardSpec.ActionInputs)
      : OrchardSpec.ActionWitness := {|
    OrchardSpec.w_us_alpha :=
      canonical_us_for (OrchardSpec.spend_auth_g orchard_circuit_params)
        (OrchardSpec.in_alpha inp);
    OrchardSpec.w_us_v :=
      canonical_us_for (OrchardSpec.value_commit_v orchard_circuit_params)
        (OrchardSpec.in_magnitude inp);
    OrchardSpec.w_us_rcv :=
      canonical_us_for (OrchardSpec.value_commit_r orchard_circuit_params)
        (OrchardSpec.in_rcv inp);
    OrchardSpec.w_us_k :=
      canonical_us_for (OrchardSpec.nullifier_k orchard_circuit_params)
        (Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp)
          +F OrchardSpec.in_psi_old inp);
    OrchardSpec.w_us_rcm :=
      canonical_us_for (OrchardSpec.note_commit_r orchard_circuit_params)
        (OrchardSpec.in_rcm_new inp);
  |}.

  (* The whole-action output as a function of the genuine inputs ALONE — the
     us-free spec, obtained by feeding the canonical witness.  This is THE Orchard
     action output the determinism theorems are stated against. *)
  Definition output (inp : OrchardSpec.ActionInputs)
      : OrchardSpec.ActionOutputs :=
    output_with_witness inp (canonical_witness inp).

  (** ** Witness-elimination math core (Qed)

      The lemmas below carry the whole mathematical content of [action_spec_us_free]
      as reusable, standalone facts.
      They deliberately take the per-window on-curve facts as *hypotheses*
      rather than deriving them from [Holds Γ]: the circuit on-curve extraction lives
      in [Orchard/circuit_proof/fixed_base/main.v], which sits DOWNSTREAM of this file
      (via [circuit_proof.facts.Include OrchardActionInputs]), so it is not in scope
      here.  The final [action_spec_us_free] therefore lives downstream
      ([Orchard/circuit_proof/us_free/nullifier_k.v]), where the on-curve
      hypotheses are discharged under [Holds Γ] and combined with these lemmas. *)

  (** [(a - b) + b] reduces to [a] modulo [p] (a field-normalisation helper). *)
  Lemma sub_then_add (a b : Z) : (a -F b) +F b = UnOp.from a.
  Proof.
    unfold BinOp.add, BinOp.sub, UnOp.from.
    rewrite Zplus_mod_idemp_l. f_equal. ring.
  Qed.

  (** The canonical [u]-list has one entry per window. *)
  Lemma canonical_us_for_aux_length :
    forall (ws : EccSpec.fixed_table) (k : Z) (i0 : nat),
      List.length (canonical_us_for_aux ws k i0) = List.length ws.
  Proof.
    induction ws as [| w ws' IH]; intros k i0; cbn [canonical_us_for_aux List.length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma canonical_us_for_length (tbl : EccSpec.fixed_table) (k : Z) :
    List.length (canonical_us_for tbl k) = List.length tbl.
  Proof. unfold canonical_us_for. apply canonical_us_for_aux_length. Qed.

  (** The [i]-th canonical [u] is the square root of the [i]-th canonical window
      point's [y + z] — the read-off of [canonical_us_for] at an in-range index. *)
  Lemma canonical_us_for_aux_nth
      (wdef : EccSpec.fixed_window) (k : Z) :
    forall (ws : EccSpec.fixed_table) (i0 i : nat),
      (i < List.length ws)%nat ->
      List.nth i (canonical_us_for_aux ws k i0) 0 =
      field_sqrt
        (Point.y
          (fixed_window_point_canonical (List.nth i ws wdef)
            (EccSpec.window_digit k (i0 + i))) +F
          EccSpec.fw_z (List.nth i ws wdef)).
  Proof.
    intros ws. induction ws as [| w ws' IH]; intros i0 i Hi.
    - cbn [List.length] in Hi. lia.
    - destruct i as [| i'].
      + cbn [canonical_us_for_aux List.nth]. rewrite Nat.add_0_r. reflexivity.
      + cbn [canonical_us_for_aux List.nth].
        replace (i0 + S i')%nat with (S i0 + i')%nat by lia.
        apply (IH (S i0) i'). cbn [List.length] in Hi. lia.
  Qed.

  Lemma canonical_us_for_nth
      (wdef : EccSpec.fixed_window) (tbl : EccSpec.fixed_table) (k : Z) (i : nat)
      (Hi : (i < List.length tbl)%nat) :
    List.nth i (canonical_us_for tbl k) 0 =
    field_sqrt
      (Point.y
        (fixed_window_point_canonical (List.nth i tbl wdef)
          (EccSpec.window_digit k i)) +F
        EccSpec.fw_z (List.nth i tbl wdef)).
  Proof.
    unfold canonical_us_for.
    exact (canonical_us_for_aux_nth wdef k tbl 0%nat i Hi).
  Qed.

  (** Per-window QR window-sign forcing (square form).  A witnessed window
      point [fixed_window_point w digit u] that is on the curve ([Honcurve]) and
      whose window discriminant is a non-residue ([Hdisc]) has [u²] equal to the
      canonical [u]'s square: the witnessed and canonical roots agree up to sign,
      and both enter the fold only through [u²].  Consumes [window_point_forced_of_disc]
      plus [field_sqrt_sound] and the [is_square] algebra. *)
  Lemma window_us_sq_free
      (w : EccSpec.fixed_window) (digit u : Z)
      (Honcurve :
        let P := EccSpec.fixed_window_point w digit u in
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (Hdisc : is_square (window_disc w digit) = false) :
    u *F u =
    field_sqrt
      (Point.y (fixed_window_point_canonical w digit) +F EccSpec.fw_z w) *F
    field_sqrt
      (Point.y (fixed_window_point_canonical w digit) +F EccSpec.fw_z w).
  Proof.
    pose proof (window_point_forced_of_disc w digit u Honcurve Hdisc) as Hforced.
    assert (Hy :
      Point.y (EccSpec.fixed_window_point w digit u) =
      Point.y (fixed_window_point_canonical w digit))
      by (rewrite Hforced; reflexivity).
    cbn [EccSpec.fixed_window_point Point.y] in Hy.
    assert (HV :
      UnOp.from
        (Point.y (fixed_window_point_canonical w digit) +F EccSpec.fw_z w) =
      u *F u).
    { rewrite <- Hy. rewrite sub_then_add. rewrite from_idem.
      apply from_mul_reduced. }
    assert (Hsq :
      is_square
        (Point.y (fixed_window_point_canonical w digit) +F EccSpec.fw_z w) = true).
    { rewrite (is_square_cong _ (u *F u)).
      - apply is_square_sq.
      - rewrite HV. symmetry. apply from_mul_reduced. }
    rewrite (field_sqrt_sound _ Hsq).
    rewrite HV. reflexivity.
  Qed.

  (** Fold congruence from a per-index square equality.  The
      witness enters [fixed_scalar_mul] only through the per-window [u²], so equal
      squares at every in-range index (and equal lengths) force equal folds.
      Pure ([FixedBaseCongruence] + list algebra). *)
  Lemma fixed_scalar_mul_squares_free
      (tbl : EccSpec.fixed_table) (k : Z) (us1 us2 : list Z)
      (Hlen1 : List.length us1 = List.length tbl)
      (Hlen2 : List.length us2 = List.length tbl)
      (Hsq : forall i, (i < List.length tbl)%nat ->
        List.nth i us1 0 *F List.nth i us1 0 =
        List.nth i us2 0 *F List.nth i us2 0) :
    EccSpec.fixed_scalar_mul tbl k us1 = EccSpec.fixed_scalar_mul tbl k us2.
  Proof.
    apply (FixedBaseCongruence.fixed_scalar_mul_us_congr_of_sq tbl k us1 us2).
    intro i.
    destruct (Nat.ltb i (List.length tbl)) eqn:Hb.
    - apply Nat.ltb_lt in Hb. apply Hsq. exact Hb.
    - apply Nat.ltb_ge in Hb.
      rewrite (List.nth_overflow us1 0) by lia.
      rewrite (List.nth_overflow us2 0) by lia.
      reflexivity.
  Qed.

  (** Per-table witness elimination.  Given, for every in-range window, the
      circuit on-curve fact and the non-residue discriminant certificate,
      the fixed-base multiplication on the witnessed [u]-list equals the one on
      the canonical [u]-list.  Combines [window_us_sq_free], the canonical
      read-off ([canonical_us_for_nth]) and the fold congruence. *)
  Lemma table_us_free_of_oncurve
      (tbl : EccSpec.fixed_table) (k : Z) (us_read : list Z)
      (wdef : EccSpec.fixed_window)
      (Hlen : List.length us_read = List.length tbl)
      (Hfacts : forall i, (i < List.length tbl)%nat ->
        (let P := EccSpec.fixed_window_point (List.nth i tbl wdef)
                    (EccSpec.window_digit k i) (List.nth i us_read 0) in
          Point.y P *F Point.y P -F
            (Point.x P *F Point.x P *F Point.x P) -F
            Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
        /\ is_square
             (window_disc (List.nth i tbl wdef) (EccSpec.window_digit k i))
           = false) :
    EccSpec.fixed_scalar_mul tbl k us_read =
    EccSpec.fixed_scalar_mul tbl k (canonical_us_for tbl k).
  Proof.
    apply (fixed_scalar_mul_squares_free tbl k us_read (canonical_us_for tbl k)).
    - exact Hlen.
    - apply canonical_us_for_length.
    - intros i Hi.
      destruct (Hfacts i Hi) as [Honc Hdisc].
      rewrite !(canonical_us_for_nth wdef tbl k i Hi).
      exact (window_us_sq_free (List.nth i tbl wdef) (EccSpec.window_digit k i)
               (List.nth i us_read 0) Honc Hdisc).
  Qed.

  (** Action-spec congruence over the witness.  The five fixed-base
      multiplications are the witness's only entry points into
      [orchard_action_spec]; equal muls (with [nf_old] threaded into [rho_new])
      give equal outputs.  Pure unfolding + rewriting. *)
  Lemma orchard_action_spec_us_congr
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs)
      (W1 W2 : OrchardSpec.ActionWitness)
      (Ek : EccSpec.fixed_scalar_mul (OrchardSpec.nullifier_k prm)
              (Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp)
                 (OrchardSpec.in_rho_old inp) +F OrchardSpec.in_psi_old inp)
              (OrchardSpec.w_us_k W1) =
            EccSpec.fixed_scalar_mul (OrchardSpec.nullifier_k prm)
              (Poseidon.poseidon_hash2 (OrchardSpec.in_nk inp)
                 (OrchardSpec.in_rho_old inp) +F OrchardSpec.in_psi_old inp)
              (OrchardSpec.w_us_k W2))
      (Ev : EccSpec.fixed_scalar_mul (OrchardSpec.value_commit_v prm)
              (OrchardSpec.in_magnitude inp) (OrchardSpec.w_us_v W1) =
            EccSpec.fixed_scalar_mul (OrchardSpec.value_commit_v prm)
              (OrchardSpec.in_magnitude inp) (OrchardSpec.w_us_v W2))
      (Er : EccSpec.fixed_scalar_mul (OrchardSpec.value_commit_r prm)
              (OrchardSpec.in_rcv inp) (OrchardSpec.w_us_rcv W1) =
            EccSpec.fixed_scalar_mul (OrchardSpec.value_commit_r prm)
              (OrchardSpec.in_rcv inp) (OrchardSpec.w_us_rcv W2))
      (Ea : EccSpec.fixed_scalar_mul (OrchardSpec.spend_auth_g prm)
              (OrchardSpec.in_alpha inp) (OrchardSpec.w_us_alpha W1) =
            EccSpec.fixed_scalar_mul (OrchardSpec.spend_auth_g prm)
              (OrchardSpec.in_alpha inp) (OrchardSpec.w_us_alpha W2))
      (Ercm : EccSpec.fixed_scalar_mul (OrchardSpec.note_commit_r prm)
                (OrchardSpec.in_rcm_new inp) (OrchardSpec.w_us_rcm W1) =
              EccSpec.fixed_scalar_mul (OrchardSpec.note_commit_r prm)
                (OrchardSpec.in_rcm_new inp) (OrchardSpec.w_us_rcm W2)) :
    OrchardSpec.orchard_action_spec prm inp W1 =
    OrchardSpec.orchard_action_spec prm inp W2.
  Proof.
    unfold OrchardSpec.orchard_action_spec, OrchardSpec.value_commit,
      OrchardSpec.spend_auth_randomize, OrchardSpec.nullifier,
      OrchardSpec.OrchardCmx, OrchardSpec.note_commit.
    cbv zeta.
    rewrite !Ek, !Ev, !Er, !Ea, !Ercm.
    reflexivity.
  Qed.

  (** Witness-elimination reduction (Qed): the witness elimination follows from
      the five per-table mul equalities (each an instance of
      [table_us_free_of_oncurve]).  This isolates the downstream obligation —
      discharging those equalities under [Holds Γ] via the circuit on-curve
      extraction — from the spec-level assembly. *)
  Lemma action_spec_us_free_of_table_eqs
      (Γ : Assignment.t columns RegionId.t)
      (Ek : EccSpec.fixed_scalar_mul
              (OrchardSpec.nullifier_k orchard_circuit_params)
              (Poseidon.poseidon_hash2
                 (OrchardSpec.in_nk (read_action_inputs Γ))
                 (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
                 OrchardSpec.in_psi_old (read_action_inputs Γ))
              (OrchardSpec.w_us_k (read_action_witness Γ)) =
            EccSpec.fixed_scalar_mul
              (OrchardSpec.nullifier_k orchard_circuit_params)
              (Poseidon.poseidon_hash2
                 (OrchardSpec.in_nk (read_action_inputs Γ))
                 (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
                 OrchardSpec.in_psi_old (read_action_inputs Γ))
              (OrchardSpec.w_us_k (canonical_witness (read_action_inputs Γ))))
      (Ev : EccSpec.fixed_scalar_mul
              (OrchardSpec.value_commit_v orchard_circuit_params)
              (OrchardSpec.in_magnitude (read_action_inputs Γ))
              (OrchardSpec.w_us_v (read_action_witness Γ)) =
            EccSpec.fixed_scalar_mul
              (OrchardSpec.value_commit_v orchard_circuit_params)
              (OrchardSpec.in_magnitude (read_action_inputs Γ))
              (OrchardSpec.w_us_v (canonical_witness (read_action_inputs Γ))))
      (Er : EccSpec.fixed_scalar_mul
              (OrchardSpec.value_commit_r orchard_circuit_params)
              (OrchardSpec.in_rcv (read_action_inputs Γ))
              (OrchardSpec.w_us_rcv (read_action_witness Γ)) =
            EccSpec.fixed_scalar_mul
              (OrchardSpec.value_commit_r orchard_circuit_params)
              (OrchardSpec.in_rcv (read_action_inputs Γ))
              (OrchardSpec.w_us_rcv (canonical_witness (read_action_inputs Γ))))
      (Ea : EccSpec.fixed_scalar_mul
              (OrchardSpec.spend_auth_g orchard_circuit_params)
              (OrchardSpec.in_alpha (read_action_inputs Γ))
              (OrchardSpec.w_us_alpha (read_action_witness Γ)) =
            EccSpec.fixed_scalar_mul
              (OrchardSpec.spend_auth_g orchard_circuit_params)
              (OrchardSpec.in_alpha (read_action_inputs Γ))
              (OrchardSpec.w_us_alpha (canonical_witness (read_action_inputs Γ))))
      (Ercm : EccSpec.fixed_scalar_mul
                (OrchardSpec.note_commit_r orchard_circuit_params)
                (OrchardSpec.in_rcm_new (read_action_inputs Γ))
                (OrchardSpec.w_us_rcm (read_action_witness Γ)) =
              EccSpec.fixed_scalar_mul
                (OrchardSpec.note_commit_r orchard_circuit_params)
                (OrchardSpec.in_rcm_new (read_action_inputs Γ))
                (OrchardSpec.w_us_rcm (canonical_witness (read_action_inputs Γ)))) :
    action_spec_of Γ = output (read_action_inputs Γ).
  Proof.
    unfold action_spec_of, output, output_with_witness.
    apply (orchard_action_spec_us_congr orchard_circuit_params
             (read_action_inputs Γ) (read_action_witness Γ)
             (canonical_witness (read_action_inputs Γ))
             Ek Ev Er Ea Ercm).
  Qed.

  (* Witness elimination — the final statement
       [action_spec_of Γ = output (read_action_inputs Γ)]
     lives DOWNSTREAM, in [Orchard/circuit_proof/us_free/nullifier_k.v]
     ([OrchardActionUsFreeNullifierK.action_spec_us_free], Qed), because the
     per-window on-curve facts that discharge the five table
     equalities [Ek..Ercm] of [action_spec_us_free_of_table_eqs] live in
     [Orchard/circuit_proof/fixed_base/main.v], which is downstream of this file
     (it is required by [circuit_proof.facts], which [Include]s this module).
     The assembly:
     - [Orchard/circuit_proof/us_free/main.v] (module [OrchardActionUsFree])
       discharges the [Ea]/[Er]/[Ercm]/[Ev] table equalities and proves the
       reduction [action_spec_us_free_of_nullifier_k] onto the single
       [nullifier_k] table equality [Ek];
     - [Orchard/circuit_proof/us_free/nullifier_k.v] discharges [Ek] itself:
       Poseidon full-permutation soundness ([poseidon_hash_cell_correct])
       composed through the [ScalarAdd] [QAdd]/[Copy] chain identifies the
       base-field scalar cell with [poseidon_hash2 nk rho_old +F psi_old],
       and the base-field canonicity digit match
       ([BaseFieldCanonicity.nullifier_k_window_digit_scalar_cell]) aligns
       the region words with that scalar's canonical base-8 digits. *)

End OrchardActionInputs.
