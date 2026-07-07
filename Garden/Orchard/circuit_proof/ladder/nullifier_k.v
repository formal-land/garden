(** * NullifierK fixed-base ladder: word-form full window correctness and
    distinctness

    The per-base instance, for NullifierK (the NF_OLD base-field base, 85
    windows), of the parameterized window-table-to-distinctness chain of
    [circuit_proof/ladder/main.v] ([full_table_entry_eq_mul_gen],
    [fixed_window_point_x_eq_mul_gen], [full_window_correct_gen],
    [ladder_distinct_precondition_holds_gen]).  The NullifierK certificate
    ingredients are proved in their own files:
    [circuit_proof/nullifier_k/table.v] (the octupling-chain-computed
    window table [NullifierKFullTable.full_table] and its materialised
    literal), [circuit_proof/nullifier_k/x_cert.v] (the
    Lagrange x-coordinate agreement), [circuit_proof/nullifier_k/sign_cert.v]
    (the positive-QR witness), and
    [circuit_proof/nullifier_k/disc_cert.v] (the
    discriminant non-residue certificate).

    Unlike ValueCommitV / ValueCommitR, NullifierK has no per-window circuit
    fact at the spec-table [window_digit]: the base-field running sum
    has 85 windows and [8^85 > pallas_q], so the digit identification
    [window_digit alpha i = <circuit word i>] is not derivable from the
    zero-tail boundary alone over a 85-window decomposition — it needs the
    scalar-canonicity machinery, out of scope here.  This file
    therefore states EVERYTHING at the circuit word

      [nullifier_k_word Γ i :=
        (A4[i] of the incomplete region) -F (A4[i+1]) *F h]

    instead of at [EccSpec.window_digit alpha i].  This is sufficient for
    the ladder-distinctness lemmas below (they never mention the scalar
    [alpha]/[window_digit] itself, only per-window points and their
    scalars); the digit-form restatement — [window_digit alpha i =
    nullifier_k_word Γ i] — belongs to the canonicity machinery and composes
    with [nullifier_k_full_window_correct_word] below by
    rewriting.  The word plugs into the shared chain as the abstract [digit]
    parameter, with [nullifier_k_word_range] as its range fact.

    Because no per-base window-equation lemma exists for NullifierK
    (analogous to
    [OrchardActionFixedBase.value_commit_v_window_correct]), this file also
    proves the base-field region-plumbing lemmas: the facts extraction
    [nullifier_k_incomplete_facts], the generic base-field selector/fixed
    facts, the word-form running-sum window correctness, and the word range
    bound — all specialised to the concrete NullifierK region so this single
    file is self-contained. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.nullifier_k.table.
Require Import Garden.Orchard.circuit_proof.nullifier_k.x_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.sign_cert.
Require Import Garden.Orchard.circuit_proof.nullifier_k.disc_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import ListNotations.
Import OrchardActionFacts.
Import OrchardActionInputs.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the [Holds] hypotheses below are at [pallas_p] (every other EC
   and Orchard file sets this; see [circuit_proof/ladder/main.v]). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NullifierKLadder.
  Import FixedBaseLadder.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The NullifierK base-field incomplete-additions region, spelled out (not
     aliased) in every top-level statement below so downstream consumers
     match syntactically. *)
  Local Notation NK :=
    (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete).

  (* The scalar cell [synth_nullifier_k_mul] is
     called with in [synthesize_nullifier]: the output of the
     [poseidon_hash(nk, rho) + psi] scalar-add region,
     i.e. [Cell.advice (nullifier_region ScalarAdd) Advice.A6 0]
     (assigned by [synthesize_scalar_add] in [circuit.v]). *)
  Definition nullifier_k_scalar_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    Garden.Halo2.Synthesis.Cell.advice
      (Garden.Orchard.circuit.nullifier_region RegionId.Nullifier.ScalarAdd)
      Advice.A6 0.

  (** ** Base-field region plumbing, specialised to NullifierK

      [synth_base_field_mul_incomplete] has exactly
      the same operation sequence as
      [synth_short_mul_incomplete] (both in
      [circuit.v]: [Copy]; [ConstrainConstant]; [enable_mul_fixed_running_sum_rows];
      [assign_fixed_rows_with_selector]; two [assign_mul_fixed_window]s
      around [assign_incomplete_additions]), only with [22 -> 85] and the
      short table replaced by [nullifier_k.base_field_fixed_rows] — so the
      selector-fact / fixed-fact extraction lemmas follow
      [OrchardActionFixedBase.short_incomplete_selector_fact]
      / [..._fixed_fact] ([circuit_proof/fixed_base/main.v]),
      generic in [region]/[scalar] exactly like those templates. *)

  Lemma base_field_incomplete_selector_fact
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) :
    (i < 85)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedRunningSum region (Z.of_nat i))
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          region scalar)).
  Proof.
    intros Hi.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply OrchardActionFixedBase.running_sum_rows_selector_fact.
    exact Hi.
  Qed.

  Lemma base_field_incomplete_fixed_fact
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.nth_error
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
      i =
      Some row ->
    List.In (column, annotation, value) row ->
    List.In
      (Fact.FixedIs column region (Z.of_nat i) value)
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          region scalar)).
  Proof.
    intros Hrow Hin.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply (OrchardActionFixedBase.assign_fixed_rows_with_selector_fixed_fact
      region Selector.QMulFixedRunningSum 0
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
      i row column annotation value Hrow Hin).
  Qed.

  (* Facts of the NullifierK base-field incomplete region, peeled from
     [Holds].  The same peeling as
     [OrchardActionFixedBase.nullifier_k_z_boundary_of_holds]
     ([circuit_proof/fixed_base/main.v]), stopping right after
     "unfold synth_base_field_mul_incomplete" (i.e.
     before its own [add_region]/[bind_right]/[bind_left] peeling), so the
     scalar cell here is exactly [nullifier_k_scalar_cell]. *)
  Lemma nullifier_k_incomplete_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          NK nullifier_k_scalar_cell)).
  Proof.
    pose proof (OrchardActionFacts.nullifier_facts Γ Hcircuit) as Hfacts.
    destruct (layouter_value Garden.Orchard.circuit.synthesize_witness_inputs)
      as [ [ [ [ [ [ [psi_old rho_old] cm_old] g_d_old] ak_P] nk] v_old]
        v_new].
    unfold Garden.Orchard.circuit.synthesize_nullifier in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma nullifier_k_table_length :
    List.length (OrchardSpec.nullifier_k orchard_circuit_params) = 85%nat.
  Proof. reflexivity. Qed.

  (* The circuit word at row [i] of the NullifierK base-field running sum:
     the running-sum decrement [A4[i] -F A4[i+1] *F h].  Stated directly (no
     [window_digit]/[alpha] involved) since the 85-window digit
     identification needs the scalar-canonicity machinery, out of scope
     here. *)
  Definition nullifier_k_word
      (Γ : Assignment.t columns RegionId.t) (i : nat) : Z :=
    (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (NK, Z.of_nat i)) -F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (NK, Z.of_nat i)) *F
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.

  Lemma nullifier_k_word_range
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    0 <= nullifier_k_word Γ i < 8.
  Proof.
    unfold nullifier_k_word.
    apply (OrchardActionFixedBase.running_sum_word_range_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          NK nullifier_k_scalar_cell))
      NK (Z.of_nat i)
      (nullifier_k_incomplete_facts Γ Hcircuit)).
    - apply base_field_incomplete_selector_fact. exact Hi.
    - exact (holds_gates Γ Hcircuit).
  Qed.

  (* Correctness of a base-field running-sum window row at the CIRCUIT WORD
     (not the spec digit): the assigned point (A0, A1) equals the spec window
     point at [nullifier_k_word Γ i].  The word-form analogue of
     [OrchardActionFixedBase.short_incomplete_window_correct]
     ([circuit_proof/fixed_base/main.v]), without the digit-match step:
     [running_sum_fixed_window_correct_of_facts] concludes at the
     raw running-sum word, and no [z_boundary] hypothesis is needed to state
     it. *)
  Lemma base_field_incomplete_window_correct_word
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (a0 a1 a2 a3 a4 a5 a6 a7 az : string)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hrow :
        List.nth_error
          Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
          i =
          Some [
            (Fixed.LagrangeCoeffs0, a0, c0);
            (Fixed.LagrangeCoeffs1, a1, c1);
            (Fixed.LagrangeCoeffs2, a2, c2);
            (Fixed.LagrangeCoeffs3, a3, c3);
            (Fixed.LagrangeCoeffs4, a4, c4);
            (Fixed.LagrangeCoeffs5, a5, c5);
            (Fixed.LagrangeCoeffs6, a6, c6);
            (Fixed.LagrangeCoeffs7, a7, c7);
            (Fixed.FixedZ, az, z)
          ])
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_base_field_mul_incomplete
              region scalar)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    Field.map_mod {|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
          (region, Z.of_nat i);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
          (region, Z.of_nat i);
    |} =
      EccSpec.fixed_window_point
        (EccSpec.fixed_window_of_row [
          (Fixed.LagrangeCoeffs0, a0, c0);
          (Fixed.LagrangeCoeffs1, a1, c1);
          (Fixed.LagrangeCoeffs2, a2, c2);
          (Fixed.LagrangeCoeffs3, a3, c3);
          (Fixed.LagrangeCoeffs4, a4, c4);
          (Fixed.LagrangeCoeffs5, a5, c5);
          (Fixed.LagrangeCoeffs6, a6, c6);
          (Fixed.LagrangeCoeffs7, a7, c7);
          (Fixed.FixedZ, az, z)
        ])
        ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
          (region, Z.of_nat i)) -F
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
            (region, Z.of_nat i)) *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)
        (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧
          (region, Z.of_nat i)).
  Proof.
    cbn [EccSpec.fixed_window_of_row EccSpec.fw_coeffs EccSpec.fw_z
      List.firstn List.map List.nth_error snd].
    apply (OrchardActionFixedBase.running_sum_fixed_window_correct_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          region scalar))
      region (Z.of_nat i) c0 c1 c2 c3 c4 c5 c6 c7 z Hfacts).
    - apply base_field_incomplete_selector_fact.
      exact Hi.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs0 a0 c0 Hrow).
      cbn. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs1 a1 c1 Hrow).
      cbn. right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs2 a2 c2 Hrow).
      cbn. do 2 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs3 a3 c3 Hrow).
      cbn. do 3 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs4 a4 c4 Hrow).
      cbn. do 4 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs5 a5 c5 Hrow).
      cbn. do 5 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs6 a6 c6 Hrow).
      cbn. do 6 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.LagrangeCoeffs7 a7 c7 Hrow).
      cbn. do 7 right. left. reflexivity.
    - apply (base_field_incomplete_fixed_fact region scalar i _
        Fixed.FixedZ az z Hrow).
      cbn. do 8 right. left. reflexivity.
    - exact Hgates.
  Qed.

  (* Per-window correctness against the NullifierK spec table at the
     CIRCUIT WORD: window [j] of the incomplete region equals the spec
     window point at [nullifier_k_word Γ j].  Word-form analogue of
     [OrchardActionFixedBase.value_commit_v_window_correct]
     ([circuit_proof/fixed_base/main.v]).
     The [do 85 destruct] costs minutes to compile, so this lemma stays in
     this leaf file. *)
  Lemma nullifier_k_window_correct_word
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error (OrchardSpec.nullifier_k orchard_circuit_params) j
          = Some w) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ NK
      (Z.of_nat j) =
    EccSpec.fixed_window_point w (nullifier_k_word Γ j)
      (List.nth j (OrchardActionInputs.read_us Γ NK 85) 0).
  Proof.
    pose proof (nullifier_k_incomplete_facts Γ Hcircuit) as Hfacts.
    unfold OrchardSpec.nullifier_k, orchard_circuit_params in Hnth.
    cbn in Hnth.
    do 85
      (destruct j as [| j];
        [ cbn in Hnth;
          inversion Hnth; subst; clear Hnth;
          rewrite <- OrchardActionFixedBase.incomplete_additions_window_point_map_mod;
          unfold OrchardActionFixedBase.incomplete_additions_window_point;
          eapply
            (base_field_incomplete_window_correct_word Γ
              NK nullifier_k_scalar_cell);
          [ reflexivity
          | exact Hfacts
          | exact (holds_gates Γ Hcircuit)
          | lia ]
        | cbn in Hnth ]).
    destruct j; discriminate Hnth.
  Qed.

  (* Make scalar multiplication opaque to conversion for the x-coordinate
     instances:
     window points are closed multiples of a concrete 254-bit generator, so
     any [reflexivity]/[rewrite]/[f_equal] that would reduce one to
     weak-head normal form runs the full double-and-add ladder.  Restored to
     transparent right after the x-coordinate bridge (the same opaque
     window as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (* The table-entry bridge: window [w], digit [d]'s entry of
     [NullifierKFullTable.full_table] is exactly the abstract multiple
     [window_scalar 85 w d * nullifier_k_G].  Consumed to transport the
     positive QR certificate [NullifierKWindowSignCert.y_check_entry] onto
     [repr (mul (window_scalar ..) G)]. *)
  Lemma nullifier_k_full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w NullifierKFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 85 w d) PallasGenerators.nullifier_k_G.
  Proof.
    unfold NullifierKFullTable.full_table, NullifierKFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.nullifier_k_G
             PallasGenerators.nullifier_k_on_curve
             PallasGenerators.nullifier_k_reduced 84 w d Hw Hd).
  Qed.

  (* The window point's x-coordinate agreement — the unconditional half,
     from the Lagrange
     x-coordinate [vm_compute] certificate
     [NullifierKFixedWindowCert.x_check_entry]. *)
  Lemma nullifier_k_fixed_window_point_x_eq_mul (w : nat) (d u : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardSpec.nullifier_k orchard_circuit_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 w d) PallasGenerators.nullifier_k_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.nullifier_k_G
              PallasGenerators.nullifier_k_on_curve
              PallasGenerators.nullifier_k_reduced 84
              (OrchardSpec.nullifier_k orchard_circuit_params)
              _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (NullifierKFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold NullifierKFixedWindowCert.table, NullifierKFixedWindowCert.default
      in Hx.
    unfold NullifierKFullTable.full_table, NullifierKFullTable.G in Hx.
    exact Hx.
  Qed.

  (* Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (* Keep the square-root / QR chain opaque to the kernel's conversion oracle
     so up-to-conversion matching in [nullifier_k_full_window_correct_word]
     never evaluates [modpow] over the concrete Pallas [(p-1)/2] exponent
     (as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** ** Per-window full correctness (word form) from a satisfying
      assignment

      [full_window_correct_gen] at the NullifierK base with the CIRCUIT WORD
      as the digit sequence: the window equation from
      [nullifier_k_window_correct_word], the
      on-curve fact from [base_field_incomplete_region_window_on_curve]
      rewritten through it, the discriminant certificate from
      [window_disc_qr_nullifier_k_all_Z],
      the positive QR certificate from
      [NullifierKWindowSignCert.y_check_entry] transported by
      [nullifier_k_full_table_entry_eq_mul], and the x-coordinate agreement
      from
      [nullifier_k_fixed_window_point_x_eq_mul]. *)
  Lemma nullifier_k_full_window_correct_word
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ NK
      (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j (nullifier_k_word Γ j))
        PallasGenerators.nullifier_k_G).
  Proof.
    refine (full_window_correct_gen Γ NK
      PallasGenerators.nullifier_k_G
      PallasGenerators.nullifier_k_on_curve
      PallasGenerators.nullifier_k_reduced
      85
      (fun i => nullifier_k_word Γ i)
      (fun i Hi => nullifier_k_word_range Γ Hcircuit i Hi)
      (OrchardSpec.nullifier_k orchard_circuit_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      assert (Hnth : List.nth_error
          (OrchardSpec.nullifier_k orchard_circuit_params) i
        = Some (List.nth i (OrchardSpec.nullifier_k orchard_circuit_params)
                  OrchardActionFixedBase.fixed_window_default)).
      { apply List.nth_error_nth'.
        rewrite nullifier_k_table_length. exact Hi. }
      exact (nullifier_k_window_correct_word Γ Hcircuit i _ Hnth).
    - (* Hwindow_on_curve *)
      intros i Hi.
      assert (Hnth : List.nth_error
          (OrchardSpec.nullifier_k orchard_circuit_params) i
        = Some (List.nth i (OrchardSpec.nullifier_k orchard_circuit_params)
                  OrchardActionFixedBase.fixed_window_default)).
      { apply List.nth_error_nth'.
        rewrite nullifier_k_table_length. exact Hi. }
      pose proof (OrchardActionFixedBase.base_field_incomplete_region_window_on_curve
        Γ NK nullifier_k_scalar_cell i
        (nullifier_k_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit) Hi) as H.
      rewrite (nullifier_k_window_correct_word Γ Hcircuit i _ Hnth) in H.
      exact H.
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_nullifier_k_all_Z i (nullifier_k_word Γ i) Hi
        (nullifier_k_word_range Γ Hcircuit i Hi)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (nullifier_k_word_range Γ Hcircuit i Hi) as Hdj.
      pose proof (NullifierKWindowSignCert.y_check_entry i
        (Z.to_nat (nullifier_k_word Γ i)) Hi ltac:(lia)) as Hfc.
      rewrite (nullifier_k_full_table_entry_eq_mul i (nullifier_k_word Γ i)
        Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (nullifier_k_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** ** The FULL NullifierK ladder-distinctness predicate

      All 83 incomplete edges (rows 1..83) at once:
      [ladder_distinct_precondition_holds_gen] fed with
      [nullifier_k_full_window_correct_word] (the word plays the digit
      sequence, with [nullifier_k_word_range] as its range fact) and the
      NullifierK generator's on-curve/reduced/non-identity/order facts. *)
  Lemma nullifier_k_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ NK
      1 83
      (OrchardActionFixedBase.incomplete_additions_window_point Γ NK 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ NK
      PallasGenerators.nullifier_k_G
      PallasGenerators.nullifier_k_on_curve
      PallasGenerators.nullifier_k_reduced
      85
      (fun i => nullifier_k_word Γ i)
      (fun i Hi => nullifier_k_word_range Γ Hcircuit i Hi)
      PallasGenerators.nullifier_k_ne_identity
      PallasGeneratorsOrder.nullifier_k_order
      ltac:(lia)
      (fun j Hj => nullifier_k_full_window_correct_word Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

End NullifierKLadder.
