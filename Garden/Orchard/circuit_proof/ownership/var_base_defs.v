(** * Variable-base scalar multiplication: shared definitions and proof kit

    The statement-level surface of the address-integrity variable-base [mul]
    composition ([circuit_proof/ownership/var_base_mul.v]): the concrete
    regions and cells of the [[ivk] g_d_old] block, the cell readers, the
    nondegeneracy side conditions, the Pallas spec-layer step laws, the
    whole-region facts extractor and the pure overflow arithmetic core.

    [var_base_mul.v] aliases every name of this module under [VarBaseMul]
    (notation abbreviations denoting these constants), so consumers keep the
    [VarBaseMul.*] paths; the phase lemmas' proofs consume the definitions
    from here.  See [var_base_mul.v] for the composition overview and the
    per-phase documentation. *)

Require Export Garden.Halo2.main.
Require Export Garden.Halo2.Synthesis.
Require Export Garden.Halo2.proof.
Require Export Garden.Halo2.lemmas.
Require Export Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Export Garden.Orchard.circuit_proof.inputs.
Require Export Garden.Orchard.circuit_proof.facts.
Require Export Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Export Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Export Garden.Halo2.PallasModel.
Require Export Garden.EllipticCurve.Weierstrass.
Require Export Garden.EllipticCurve.Pallas.
(* [Garden.Plonky3.M] is deliberately Require'd but NOT Imported: its
   notations break nested or-intropatterns ([destruct H as [A | [B | C]]]
   fails to parse under it).  [Primes] and the [PallasPIsPrime] instance are
   the [Field.Field] originals that [M.Primes] aliases; any [M]-qualified
   rewrite lemmas are referenced by full path. *)
Require Garden.Plonky3.M.
Require Export Garden.Field.Field.
Require Export Stdlib.ZArith.ZArith.
Require Export Stdlib.Lists.List.
Require Export Stdlib.micromega.Lia.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module VarBaseDefs.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** The concrete cells of the address-integrity [mul] instance *)

  (** The 137-row variable-base region. *)
  Definition mul_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase).

  Definition overflow_s_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowS).
  Definition overflow_lookup_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowLookup).
  Definition overflow_check_region : RegionId.t :=
    RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck).

  (** The witnessed old-note diversified base [g_d_old]. *)
  Definition gd_old_region : RegionId.t :=
    RegionId.WitnessInput RegionId.WitnessInput.GDOld.

  (** The [ivk] point ([M + [rivk] R] complete add of the [Commit^ivk]
      block); its x-coordinate is the scalar the chip multiplies by. *)
  Definition ivk_add_region : RegionId.t :=
    RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd.

  Definition alpha_cell : Cell.t columns RegionId.t :=
    Cell.advice ivk_add_region Advice.A2 1.
  Definition gd_x_cell : Cell.t columns RegionId.t :=
    Cell.advice gd_old_region Advice.A0 0.
  Definition gd_y_cell : Cell.t columns RegionId.t :=
    Cell.advice gd_old_region Advice.A1 0.

  (** ** Readers

      [av]: the (field-reduced) evaluation of an advice cell of the
      variable-base region. *)
  Definition av
      (Γ : Assignment.t columns RegionId.t) (column : Advice.t) (row : Z) : Z :=
    read_advice Γ column mul_region row.

  (** The scalar: the [ivk] x-coordinate cell's value. *)
  Definition alpha_value (Γ : Assignment.t columns RegionId.t) : Z :=
    read_advice Γ Advice.A2 ivk_add_region 1.

  (** The base point, as witnessed (chip representation). *)
  Definition base_point (Γ : Assignment.t columns RegionId.t) : Point.t :=
    read_point Γ gd_old_region.

  (** The base point, as a Weierstrass point. *)
  Definition base_wpoint (Γ : Assignment.t columns RegionId.t) : Pallas.point :=
    PallasModel.unrepr (base_point Γ).

  (** The chip's output point [(A2@136, A3@136)] ([MulResult.x]/[.y]). *)
  Definition result_point (Γ : Assignment.t columns RegionId.t) : Point.t := {|
    Point.x := av Γ Advice.A2 136;
    Point.y := av Γ Advice.A3 136;
  |}.

  (** The recovered 255-bit scalar.  The [z] running sums are field cells in
      [0, p); every partial sum through [z_1] is [< 2^254 < p], so those
      cells hold the true integer bit sums, but the final step
      [z_0 = 2·z_1 + k_0] can exceed [p], leaving the [A9@136] cell equal to
      it only mod [p].  [lsb_bit] recovers the last bit as the mod-[p]
      difference the [QMulLsb] boolean constraint ranges over, and
      [recovered_scalar] is the true integer bit sum [2·z_1 + k_0] the
      accumulator's final multiple is built from. *)
  Definition lsb_bit (Γ : Assignment.t columns RegionId.t) : Z :=
    (av Γ Advice.A9 136 - 2 * av Γ Advice.A9 135) mod Primes.pallas_p.
  Definition recovered_scalar (Γ : Assignment.t columns RegionId.t) : Z :=
    2 * av Γ Advice.A9 135 + lsb_bit Γ.

  (** ** The nondegeneracy side condition

      Each incomplete double-and-add step at row [r] performs two incomplete
      additions: [acc + (±B)] (chord from [(x_a, y_a)] to [(x_p, ±y_p)]) and
      then [(acc + (±B)) + acc] (chord from the intermediate [x_r] back to
      [x_a]).  The gates ([q_mul_{1,2,3}_checks_gate]) constrain nothing when
      either chord is vertical or when the accumulator is the [(0,0)]
      identity sentinel, so soundness of the step needs, per row:
      the accumulator is affine ([x_a ≠ 0], since no curve point has [x = 0]),
      the first chord is non-vertical ([x_a ≠ x_p]) and the second chord is
      non-vertical ([x_r ≠ x_a]).  [x_r = λ₁² − x_a − x_p] is the
      intermediate x ([incomplete_proof.x_r]). *)
  Definition step_nondegenerate
      (Γ : Assignment.t columns RegionId.t)
      (x_a x_p lambda_1 : Advice.t) (r : Z) : Prop :=
    av Γ x_a r <> 0 /\
    av Γ x_a r <> av Γ x_p r /\
    x_r (av Γ x_a r) (av Γ x_p r) (av Γ lambda_1 r) <> av Γ x_a r.

  (** Hi half: [x_a = A3], [x_p = A0], [λ₁ = A4]; steps at rows 2..126. *)
  Definition hi_step_nondegenerate
      (Γ : Assignment.t columns RegionId.t) (r : Z) : Prop :=
    step_nondegenerate Γ Advice.A3 Advice.A0 Advice.A4 r.

  (** Lo half: [x_a = A7], [x_p = A0], [λ₁ = A8]; steps at rows 2..127. *)
  Definition lo_step_nondegenerate
      (Γ : Assignment.t columns RegionId.t) (r : Z) : Prop :=
    step_nondegenerate Γ Advice.A7 Advice.A0 Advice.A8 r.

  (** The whole-region honesty condition: every incomplete step of both
      halves is nondegenerate.  A conjunct of
      [OrchardValidActionInputs.commit_ivk_witness_ok]
      ([circuit_proof/valid_action_inputs.v]). *)
  Definition mul_nondegenerate (Γ : Assignment.t columns RegionId.t) : Prop :=
    (forall r, 2 <= r <= 126 -> hi_step_nondegenerate Γ r) /\
    (forall r, 2 <= r <= 127 -> lo_step_nondegenerate Γ r).

  (** ** Spec layer: the double-and-add step at the Pallas group

      Small wrappers around the generic [Weierstrass] laws (the same shape as
      the [FixedBaseLadder] kit in [circuit_proof/ladder/main.v], restated
      here to keep this file's [Require] closure lean). *)

  Lemma pallas_11_lt : 11 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma pallas_mul_one (P : Pallas.point) : Pallas.mul 1 P = P.
  Proof. reflexivity. Qed.

  Lemma pallas_mul_add (i j : Z) (P : Pallas.point) :
    Pallas.reduced P -> Pallas.on_curve P ->
    Pallas.mul (i + j) P = Pallas.add (Pallas.mul i P) (Pallas.mul j P).
  Proof.
    intros HrP HoP.
    exact (Weierstrass.mul_add (p := Primes.pallas_p) Pallas.a Pallas.b i j P
      pallas_11_lt Pallas.nonsingular HrP HoP).
  Qed.

  Lemma pallas_mul_neg (i : Z) (P : Pallas.point) :
    Pallas.reduced P ->
    Pallas.mul (- i) P = Pallas.neg (Pallas.mul i P).
  Proof.
    intro HrP.
    exact (Weierstrass.mul_neg (p := Primes.pallas_p) Pallas.a Pallas.b i P HrP).
  Qed.

  Lemma pallas_mul_2 (B : Pallas.point) :
    Pallas.reduced B -> Pallas.on_curve B ->
    Pallas.mul 2 B = Pallas.add B B.
  Proof.
    intros HrB HoB.
    replace 2 with (1 + 1) by lia.
    rewrite (pallas_mul_add 1 1 B HrB HoB).
    rewrite !pallas_mul_one. reflexivity.
  Qed.

  Lemma pallas_3_lt : 3 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  (** On-curve closure of [neg] and [mul] (the [reduced] closures are the
      [Weierstrass.neg_reduced]/[mul_reduced] laws; the [on_curve] ones are
      the small inductions below, the same shape as the [FixedBaseLadder]
      kit). *)
  Section OnCurveClosure.
    Context {p : Z} `{Prime p}.
    Variables (a b : Z).

    Lemma w_neg_on_curve (P : Weierstrass.point) :
      Weierstrass.on_curve (p := p) a b P ->
      Weierstrass.on_curve (p := p) a b (Weierstrass.neg (p := p) P).
    Proof.
      intro HP. destruct P as [| x y].
      - exact I.
      - cbn [Weierstrass.neg Weierstrass.on_curve] in *.
        rewrite <- HP.
        assert (Heq : (UnOp.opp (p := p) y) *F (UnOp.opp (p := p) y) = y *F y).
        { unfold UnOp.opp, BinOp.mul.
          rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_opp_opp.
          reflexivity. }
        rewrite Heq. reflexivity.
    Qed.

    Lemma w_mul_pos_on_curve (n : positive) (P : Weierstrass.point) :
      3 < p -> Weierstrass.on_curve (p := p) a b P ->
      Weierstrass.on_curve (p := p) a b (Weierstrass.mul_pos (p := p) a n P).
    Proof.
      intros Hp HP. induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos].
      - apply Weierstrass.add_on_curve; [exact Hp | exact HP |].
        apply Weierstrass.add_on_curve; [exact Hp | exact IH | exact IH].
      - apply Weierstrass.add_on_curve; [exact Hp | exact IH | exact IH].
      - exact HP.
    Qed.

    Lemma w_mul_on_curve (k : Z) (P : Weierstrass.point) :
      3 < p -> Weierstrass.on_curve (p := p) a b P ->
      Weierstrass.on_curve (p := p) a b (Weierstrass.mul (p := p) a k P).
    Proof.
      intros Hp HP. destruct k as [| n | n]; cbn [Weierstrass.mul].
      - exact I.
      - apply w_mul_pos_on_curve; assumption.
      - apply w_neg_on_curve. apply w_mul_pos_on_curve; assumption.
    Qed.
  End OnCurveClosure.

  Lemma pallas_mul_on_curve (k : Z) (G : Weierstrass.point) :
    Pallas.on_curve G -> Pallas.on_curve (Pallas.mul k G).
  Proof.
    intro HG. unfold Pallas.on_curve, Pallas.mul in *.
    apply w_mul_on_curve; [exact pallas_3_lt | exact HG].
  Qed.

  Lemma pallas_mul_reduced (k : Z) (G : Weierstrass.point) :
    Pallas.reduced G -> Pallas.reduced (Pallas.mul k G).
  Proof.
    intro HG. unfold Pallas.reduced, Pallas.mul in *.
    apply Weierstrass.mul_reduced. exact HG.
  Qed.

  Lemma pallas_neg_on_curve (G : Weierstrass.point) :
    Pallas.on_curve G -> Pallas.on_curve (Pallas.neg G).
  Proof.
    intro HG. unfold Pallas.on_curve, Pallas.neg in *.
    apply (w_neg_on_curve Pallas.a Pallas.b). exact HG.
  Qed.

  Lemma pallas_neg_reduced (G : Weierstrass.point) :
    Pallas.reduced G -> Pallas.reduced (Pallas.neg G).
  Proof.
    intro HG. unfold Pallas.reduced, Pallas.neg in *.
    apply Weierstrass.neg_reduced. exact HG.
  Qed.

  (** The point a bit [k] contributes to a step: [B] for [k = 1], [−B] for
      [k = 0] — i.e. [[2k−1] B]. *)
  Definition signed_base (B : Pallas.point) (k : Z) : Pallas.point :=
    if k =? 1 then B else Pallas.neg B.

  Lemma signed_base_mul (B : Pallas.point) (k : Z) :
    Pallas.reduced B ->
    k = 0 \/ k = 1 ->
    signed_base B k = Pallas.mul (2 * k - 1) B.
  Proof.
    intros HrB Hk.
    destruct Hk as [-> | ->]; unfold signed_base; cbn [Z.eqb].
    - replace (2 * 0 - 1) with (- (1)) by lia.
      rewrite (pallas_mul_neg 1 B HrB), pallas_mul_one. reflexivity.
    - replace (2 * 1 - 1) with 1 by lia.
      rewrite pallas_mul_one. reflexivity.
  Qed.

  (** One double-and-add step on the multiple: from accumulator [[c] B] and
      bit [k], the circuit's [(acc + [2k−1]B) + acc] lands on
      [[2c + 2k − 1] B]. *)
  Lemma double_add_step_multiple (B : Pallas.point) (c k : Z) :
    Pallas.reduced B -> Pallas.on_curve B ->
    k = 0 \/ k = 1 ->
    Pallas.add (Pallas.add (Pallas.mul c B) (signed_base B k)) (Pallas.mul c B) =
    Pallas.mul (2 * c + 2 * k - 1) B.
  Proof.
    intros HrB HoB Hk.
    rewrite (signed_base_mul B k HrB Hk).
    rewrite <- (pallas_mul_add c (2 * k - 1) B HrB HoB).
    rewrite <- (pallas_mul_add (c + (2 * k - 1)) c B HrB HoB).
    f_equal. lia.
  Qed.

  (** The step law on the [2^m + 2z + 1] invariant shape: absorbing a bit [k]
      into the running sum [z ↦ 2z + k] matches the multiple update. *)
  Lemma step_scalar_shape (m z k : Z) :
    0 <= m ->
    2 * (2 ^ m + 2 * z + 1) + 2 * k - 1 = 2 ^ (m + 1) + 2 * (2 * z + k) + 1.
  Proof.
    intro Hm.
    rewrite Z.pow_add_r by lia.
    lia.
  Qed.

  (** ** Facts extractors: from [Holds Γ] to the mul block's own fact lists *)

  (** The variable-base region's synthesis facts, with the scalar and base
      cell arguments in their concrete form. *)
  Lemma variable_base_region_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (region_facts mul_region
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul
          .synthesize_variable_base_scalar_mul_region
          mul_region alpha_cell gd_x_cell gd_y_cell)).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 7 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_address_integrity in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    exact Hfacts.
  Qed.

  (** ** The overflow argument

      Pure arithmetic core: the constraints of [overflow_checks_gate]
      combined with the 130-bit lookup decomposition of [s] force the 255-bit
      running sum [z_0] to equal [α + t_q] over the integers (no mod-[p]
      wrap).  The hypotheses transcribe, in order: the ranges of [α] (a field
      evaluation), [z_0] (255 boolean bits) and [s] (a field evaluation); the
      [recovery] constraint [z_0 − α = t_q (mod p)]; the [s_check] constraint
      [s = α + k_254·2^130 (mod p)] with [k_254 = z_0 / 2^254]; the
      [k_254 ⋅ (z_130 − 2^124)] constraint ([z_130 = z_0 / 2^130]); and the
      two [s]-decomposition constraints ([k_254 ⋅ s_minus_lo] and the
      [η]-guarded [(1−k_254)(1−z_130 η) s_minus_lo], whose forced cases are
      exactly [k_254 = 1] and [k_254 = 0 ∧ z_130 = 0]). *)
  Lemma overflow_no_wrap
      (alpha z0 s : Z)
      (Halpha : 0 <= alpha < Primes.pallas_p)
      (Hz0 : 0 <= z0 < 2 ^ 255)
      (Hs : 0 <= s < Primes.pallas_p)
      (Hrecovery :
        z0 mod Primes.pallas_p = (alpha + Primes.t_q) mod Primes.pallas_p)
      (Hs_check :
        s mod Primes.pallas_p =
        (alpha + (z0 / 2 ^ 254) * 2 ^ 130) mod Primes.pallas_p)
      (Hhigh : z0 / 2 ^ 254 = 1 -> z0 / 2 ^ 130 = 2 ^ 124)
      (Hs_low : z0 / 2 ^ 254 = 1 \/ z0 / 2 ^ 130 = 0 -> s < 2 ^ 130) :
    z0 = alpha + Primes.t_q.
  Proof.
    assert (Hp : Primes.pallas_p = 2 ^ 254 + Primes.t_p) by reflexivity.
    assert (Htp : Primes.t_p = 45560315531419706090280762371685220353)
      by reflexivity.
    assert (Htq : Primes.t_q = 45560315531506369815346746415080538113)
      by reflexivity.
    assert (Hpow254 : 2 ^ 255 = 2 * 2 ^ 254) by (rewrite <- Z.pow_succ_r; lia).
    assert (Hpow130 : 2 ^ 254 = 2 ^ 124 * 2 ^ 130)
      by (rewrite <- Z.pow_add_r by lia; reflexivity).
    assert (H130pos : 0 < 2 ^ 130) by (apply Z.pow_pos_nonneg; lia).
    assert (H254pos : 0 < 2 ^ 254) by (apply Z.pow_pos_nonneg; lia).
    assert (H124pos : 0 < 2 ^ 124) by (apply Z.pow_pos_nonneg; lia).
    assert (H130le254 : 2 ^ 130 <= 2 ^ 254) by (apply Z.pow_le_mono_r; lia).
    assert (Htq130 : Primes.t_q < 2 ^ 130).
    { rewrite Htq.
      assert (H126le : 2 ^ 126 <= 2 ^ 130) by (apply Z.pow_le_mono_r; lia).
      assert (H126v : (2 : Z) ^ 126 = 85070591730234615865843651857942052864)
        by reflexivity.
      lia. }
    (* The recovery congruence, as a divisibility with a small quotient. *)
    assert (Hdvd : (z0 - (alpha + Primes.t_q)) mod Primes.pallas_p = 0).
    { rewrite Zminus_mod, Hrecovery, <- Zminus_mod, Z.sub_diag.
      apply Zmod_0_l. }
    apply Z.mod_divide in Hdvd; [| rewrite Hp, Htp; clear - H254pos; lia].
    destruct Hdvd as [k Hk].
    rewrite Hp, Htp in Hk, Hs.
    rewrite Htq in Hk, Hrecovery, Htq130 |- *.
    rewrite Hp, Htp in Halpha.
    assert (Hkrange : k = -1 \/ k = 0 \/ k = 1).
    { clear - Hk Hz0 Halpha Hpow254 H254pos. nia. }
    destruct Hkrange as [Hkm1 | [Hk0 | Hk1]].
    - (* Wrap down: [z0 = α + t_q − p] puts [α] above [p − t_q] while the
         [k_254 = 0 ∧ z_130 = 0] branch of the [s]-decomposition forces
         [α = s < 2^130]. *)
      exfalso.
      rewrite Hkm1 in Hk.
      assert (Hz0small : z0 < 45560315531506369815346746415080538113)
        by (clear - Hk Halpha; lia).
      assert (Hz130 : z0 / 2 ^ 130 = 0)
        by (apply Z.div_small; clear - Hz0small Htq130 Hz0; lia).
      assert (Hk254 : z0 / 2 ^ 254 = 0)
        by (apply Z.div_small; clear - Hz0small Htq130 H130le254 Hz0; lia).
      assert (Hslow : s < 2 ^ 130) by (apply Hs_low; right; exact Hz130).
      rewrite Hk254 in Hs_check.
      rewrite Z.mul_0_l, Z.add_0_r in Hs_check.
      rewrite (Z.mod_small s) in Hs_check by (rewrite Hp, Htp; lia).
      rewrite (Z.mod_small alpha) in Hs_check by (rewrite Hp, Htp; lia).
      clear - Hs_check Hslow Hk Hz0 H130le254.
      lia.
    - (* No wrap: the conclusion. *)
      rewrite Hk0 in Hk. clear - Hk. lia.
    - (* Wrap up: [z0 ≥ 2^254] forces [k_254 = 1], hence [z_130 = 2^124] and
         [s = α + 2^130 < 2^130] — impossible. *)
      exfalso.
      rewrite Hk1 in Hk.
      assert (Hz0big : 2 ^ 254 <= z0) by (clear - Hk Halpha; lia).
      assert (Hk254 : z0 / 2 ^ 254 = 1).
      { replace z0 with (1 * 2 ^ 254 + (z0 - 2 ^ 254)) by lia.
        rewrite Z.div_add_l by (clear - H254pos; lia).
        rewrite Z.div_small by (clear - Hz0 Hz0big Hpow254; lia).
        lia. }
      assert (Hz130 : z0 / 2 ^ 130 = 2 ^ 124) by (apply Hhigh; exact Hk254).
      assert (Hz0upper : z0 < 2 ^ 254 + 2 ^ 130).
      { pose proof (Z.mod_pos_bound z0 (2 ^ 130) H130pos) as Hmr.
        pose proof (Z.div_mod z0 (2 ^ 130) ltac:(clear - H130pos; lia)) as Hdm.
        rewrite Hz130 in Hdm.
        clear - Hmr Hdm Hpow130.
        nia. }
      assert (Halpha_small : alpha + 45560315531506369815346746415080538113 +
          45560315531419706090280762371685220353 < 2 ^ 130)
        by (clear - Hk Hz0upper; lia).
      assert (Hslow : s < 2 ^ 130) by (apply Hs_low; left; exact Hk254).
      rewrite Hk254, Z.mul_1_l in Hs_check.
      rewrite (Z.mod_small s) in Hs_check by (rewrite Hp, Htp; lia).
      rewrite (Z.mod_small (alpha + 2 ^ 130)) in Hs_check.
      2:{ rewrite Hp, Htp.
          clear - Halpha_small Halpha H130le254 H130pos.
          lia. }
      clear - Hs_check Hslow Halpha.
      lia.
  Qed.
End VarBaseDefs.
