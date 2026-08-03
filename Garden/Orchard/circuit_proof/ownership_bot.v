(** * §4.18.4 'Diversified address integrity', adversarial reading

    The ownership track of the ⊥-disjunctive Action statement: from circuit
    acceptance alone — no nondegeneracy and no canonicity hypothesis — the
    §4.18.4 clause

      [ivk = ⊥ or pk_d^old = [ivk] g_d^old],   [ivk = Commit^ivk_rivk(ak, nk)]

    in the form [OrchardAdversarialApi.diversified_address_obligation]
    ([circuit_proof/adversarial_api.v]).

    The clause's two halves are different in kind.

    - The ⊥ belongs to the [Commit^ivk] Sinsemilla fold and to nothing else.
      [Commit^ivk] is a [SinsemillaShortCommit], whose hash-to-point is the
      §5.4.1.9 incomplete-addition fold; on an exceptional operand pair the
      fold is ⊥ and the gates leave the circuit's value unconstrained.
      [OrchardProtocolSpecBot.commit_ivk_bot] carries that ⊥, and
      [OrchardProtocolSpecBot.commit_ivk_bot_defined_iff] identifies
      definedness with the [SinsemillaHash.nondegenerate] hypothesis the
      existing chain consumes — so the ⊥ branch is discharged by a case
      split, with the tracking branch reusing
      [OrchardValidActionInputs.diversified_address_integrity] verbatim.

    - The variable-base multiplication gets no protocol slack.  §4.18.4's
      note requires the scalar decomposition of [ivk] in [[ivk] g_d^old] to
      be canonical, and neither the clause nor its non-normative notes grant
      the ladder's incomplete additions an exceptional escape.  The mul
      chip's per-row nondegeneracy side condition
      ([VarBaseDefs.mul_nondegenerate]) is therefore *derived from the
      gates* here rather than assumed or disjuncted: at each row of the two
      incomplete halves the accumulator is a group multiple [[c] B] of the
      witnessed base, the scalar stays in [1 < c] with [2c + 1 < q_P], and
      the multiples [[0] B], [[1] B], [[c ± 1] B] are pairwise distinct in
      their x-coordinates by injectivity of scalar multiplication on
      residues modulo the prime group order.  The derivation runs inside the
      round induction, because nondegeneracy at a row follows from the
      accumulator invariant *at that row*.

    The strengthened round induction is a separate lemma whose conclusion
    is exactly the [Hnondeg] premise of
    [VarBaseIncomplete.incomplete_half_generic], so it composes with the
    half lemmas and their consumers as stated.

    The generic Pallas kit ([pallas_affine_x_nonzero],
    [repr_x_eq_eq_or_neg], [mul_x_neq]) is restated locally over
    [EllipticCurve/{Weierstrass,Pallas}.v], the same convention
    [circuit_proof/ownership/var_base_defs.v] documents for its spec-layer
    wrappers: the [FixedBaseLadder] originals live in
    [circuit_proof/ladder/main.v], whose [Require] closure carries the
    fixed-base certificate leaves. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_incomplete.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_mul.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_proof.ownership.diversified_address.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.adversarial_api.
(* [Garden.Plonky3.M] is deliberately Require'd but NOT Imported: its
   notations break nested or-intropatterns.  [Primes] and the
   [PallasPIsPrime] instance are the [Field.Field] originals. *)
Require Garden.Plonky3.M.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardOwnershipBot.
  Import OrchardActionInputs.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The raw advice reader of the variable-base region, aligned with
      [VarBaseDefs.av] by [VarBaseIncomplete.av_adv]. *)
  Local Notation adv Γ c row :=
    (UnOp.from (Γ.(Assignment.advice) c VarBaseDefs.mul_region row)).

  (** ** Pallas kit, restated locally

      [FixedBaseLadder]'s x-coordinate injectivity chain
      ([circuit_proof/ladder/main.v]), over
      [EllipticCurve/{Weierstrass,Pallas}.v] and [Halo2/PallasModel.v]
      only. *)

  Lemma mul_x_zero {q : Z} `{Prime q} (c x : Z) :
    UnOp.from x = 0 -> c *F x = 0.
  Proof.
    intro Hx. unfold BinOp.mul, UnOp.from in *.
    rewrite <- Zmult_mod_idemp_r, Hx, Z.mul_0_r. apply Zmod_0_l.
  Qed.

  Lemma curve_x_zero_absurd {q : Z} `{Prime q} (x y c : Z) :
    UnOp.from x = 0 ->
    UnOp.from (y *F y) = UnOp.from (x *F x *F x +F 0 *F x +F c) ->
    UnOp.from (y *F y) = UnOp.from c.
  Proof.
    intros Hx Hc. rewrite Hc.
    assert (H3 : x *F x *F x = 0) by (apply mul_x_zero; exact Hx).
    assert (H0x : (0:Z) *F x = 0)
      by (unfold BinOp.mul; rewrite Z.mul_0_l; apply Zmod_0_l).
    rewrite H3, H0x.
    show_equality_modulo.
  Qed.

  (** No Pallas point has [x = 0]: [b = 5] is a quadratic non-residue
      (§5.4.9.7 note). *)
  Lemma pallas_affine_x_nonzero (x y : Z) :
    Pallas.on_curve (Weierstrass.Affine x y) -> UnOp.from x <> 0.
  Proof.
    intros Hc Hx0.
    cbn [Pallas.on_curve Weierstrass.on_curve] in Hc.
    unfold Pallas.a, Pallas.b in Hc.
    apply (EccSpec.pallas_b_quadratic_nonresidue y).
    change (Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b) with 5.
    exact (curve_x_zero_absurd x y 5 Hx0 Hc).
  Qed.

  (** On the curve, [x(P) = x(Q)] iff [P = ±Q]. *)
  Lemma repr_x_eq_eq_or_neg (P Q : Weierstrass.point) :
    Pallas.reduced P -> Pallas.reduced Q ->
    Pallas.on_curve P -> Pallas.on_curve Q ->
    UnOp.from (Point.x (PallasModel.repr P)) =
      UnOp.from (Point.x (PallasModel.repr Q)) ->
    P = Q \/ P = Pallas.neg Q.
  Proof.
    intros HPr HQr HPo HQo Hx.
    destruct P as [| xp yp]; destruct Q as [| xq yq].
    - left. reflexivity.
    - exfalso.
      cbn [PallasModel.repr Point.x EccSpec.identity] in Hx.
      apply (pallas_affine_x_nonzero xq yq HQo).
      rewrite <- Hx. reflexivity.
    - exfalso.
      cbn [PallasModel.repr Point.x EccSpec.identity] in Hx.
      apply (pallas_affine_x_nonzero xp yp HPo).
      rewrite Hx. reflexivity.
    - cbn [PallasModel.repr Point.x] in Hx.
      destruct HPr as [Hxp Hyp]. destruct HQr as [Hxq Hyq].
      assert (Hxeq : xp = xq).
      { rewrite <- Hxp, <- Hxq. exact Hx. }
      destruct (Weierstrass.same_x_eq_or_neg Pallas.a Pallas.b
        (Weierstrass.Affine xp yp) (Weierstrass.Affine xq yq)
        (conj Hxp Hyp) (conj Hxq Hyq) HPo HQo) as [Heq | Hneg].
      + cbn [Weierstrass.x_coord]. rewrite Hxeq. reflexivity.
      + left. exact Heq.
      + right. exact Hneg.
  Qed.

  (** Multiples of a prime-order generator with distinct residues [±] have
      distinct x-coordinates. *)
  Lemma mul_x_neq (G : Weierstrass.point) (i j : Z)
      (HGoc : Pallas.on_curve G) (HGred : Pallas.reduced G)
      (HGne : G <> Pallas.identity)
      (HGord : Pallas.mul Pallas.pallas_q G = Pallas.identity)
      (Hij : i mod Pallas.pallas_q <> j mod Pallas.pallas_q)
      (Hijn : i mod Pallas.pallas_q <> (- j) mod Pallas.pallas_q) :
    UnOp.from (Point.x (PallasModel.repr (Pallas.mul i G))) <>
    UnOp.from (Point.x (PallasModel.repr (Pallas.mul j G))).
  Proof.
    intro Hx.
    destruct (repr_x_eq_eq_or_neg (Pallas.mul i G) (Pallas.mul j G)
      (VarBaseDefs.pallas_mul_reduced i G HGred)
      (VarBaseDefs.pallas_mul_reduced j G HGred)
      (VarBaseDefs.pallas_mul_on_curve i G HGoc)
      (VarBaseDefs.pallas_mul_on_curve j G HGoc) Hx)
      as [Heq | Hneg].
    - apply Hij.
      apply (proj1 (Weierstrass.mul_injective_mod Pallas.a Pallas.b
        G Pallas.pallas_q VarBaseDefs.pallas_11_lt Pallas.nonsingular
        HGred HGoc HGne Pallas.pallas_q_is_prime HGord i j)).
      exact Heq.
    - apply Hijn.
      assert (Heq2 : Pallas.mul i G = Pallas.mul (- j) G).
      { rewrite Hneg. symmetry.
        exact (Weierstrass.mul_neg Pallas.a Pallas.b j G HGred). }
      apply (proj1 (Weierstrass.mul_injective_mod Pallas.a Pallas.b
        G Pallas.pallas_q VarBaseDefs.pallas_11_lt Pallas.nonsingular
        HGred HGoc HGne Pallas.pallas_q_is_prime HGord i (- j))).
      exact Heq2.
  Qed.

  (** ** Small readers of the representation map *)

  Lemma mul_zero_x (G : Weierstrass.point) :
    UnOp.from (Point.x (PallasModel.repr (Pallas.mul 0 G))) = 0.
  Proof.
    unfold Pallas.mul.
    cbn [Weierstrass.mul PallasModel.repr EccSpec.identity Point.x].
    unfold UnOp.from. apply Zmod_0_l.
  Qed.

  (** A represented record whose x is nonzero comes from an affine point. *)
  Lemma repr_eq_affine (P : Weierstrass.point) (x y : Z) :
    {| Point.x := x; Point.y := y |} = PallasModel.repr P ->
    x <> 0 ->
    P = Weierstrass.Affine x y.
  Proof.
    intros Heq Hx.
    destruct P as [| ax ay].
    - exfalso. apply Hx. exact (f_equal Point.x Heq).
    - f_equal.
      + exact (eq_sym (f_equal Point.x Heq)).
      + exact (eq_sym (f_equal Point.y Heq)).
  Qed.

  Lemma pallas_q_lower : 3 < Pallas.pallas_q.
  Proof.
    unfold Pallas.pallas_q, Primes.pallas_q.
    assert (H : 0 < 2 ^ 254) by (apply Z.pow_pos_nonneg; lia).
    unfold Primes.t_q. lia.
  Qed.

  Lemma mod_opp_small (a : Z) (Ha : 0 < a < Pallas.pallas_q) :
    (- a) mod Pallas.pallas_q = Pallas.pallas_q - a.
  Proof.
    pose proof pallas_q_lower as Hq.
    rewrite Z.mod_opp_l_nz.
    - rewrite (Z.mod_small a) by (clear - Ha; lia). reflexivity.
    - clear - Hq. lia.
    - rewrite (Z.mod_small a) by (clear - Ha; lia). clear - Ha. lia.
  Qed.

  (** ** The per-row nondegeneracy derivation

      At a row whose accumulator represents the multiple [[c] B] of the
      witnessed base, with the [gradient_1] constraint of
      [incomplete.q_mul_{2,3}_checks_gate] in force, all three
      nondegeneracy conjuncts of [VarBaseDefs.step_nondegenerate] are
      forced.

      - [x_a <> 0]: [[c] B] is not the point at infinity ([0 < c < q_P]),
        and no Pallas point has [x = 0].
      - [x_a <> x_p]: [x_p] is the base's x, i.e. [x([1] B)], and
        [c ≢ ±1 (mod q_P)].
      - [x_r <> x_a]: with [x_a <> x_p] the [gradient_1] constraint pins
        [λ₁] to the chord slope from the accumulator to the signed base
        [[2k−1] B], so [x_r = λ₁² − x_a − x_p] is the x-coordinate of
        [[c + 2k − 1] B], and [c + 2k − 1 ≢ ±c (mod q_P)] because
        [0 < 2c ± 1 < q_P].

      The scalar bound [1 < c] with [2c + 1 < q_P] is what the round
      induction supplies from the running-sum range. *)
  Lemma step_nondegenerate_derived
      (B : Pallas.point) (bx byv : Z)
      (HB : B = Weierstrass.Affine bx byv)
      (HBred : Pallas.reduced B) (HBoc : Pallas.on_curve B)
      (HBne : B <> Pallas.identity)
      (HBord : Pallas.mul Pallas.pallas_q B = Pallas.identity)
      (c k xa l1 l2 : Z)
      (Hl1 : UnOp.from l1 = l1)
      (Hk : k = 0 \/ k = 1)
      (Hc1 : 1 < c)
      (Hcq : 2 * c + 1 < Pallas.pallas_q)
      (Hacc : {| Point.x := xa; Point.y := y_a xa bx l1 l2 |} =
              PallasModel.repr (Pallas.mul c B))
      (Hg1 : l1 *F (xa -F bx) -F y_a xa bx l1 l2
               +F ((k *F UnOp.from 2 -F UnOp.from 1) *F byv) = 0) :
    xa <> 0 /\ xa <> bx /\ x_r xa bx l1 <> xa.
  Proof.
    pose proof pallas_q_lower as Hq3.
    assert (Hcmod : c mod Pallas.pallas_q = c)
      by (apply Z.mod_small; clear - Hc1 Hcq Hq3; lia).
    assert (Hxaeq : Point.x (PallasModel.repr (Pallas.mul c B)) = xa)
      by (rewrite <- Hacc; reflexivity).
    (* [x_a <> 0]: the accumulator is not the identity. *)
    assert (Hxa0 : xa <> 0).
    { pose proof (mul_x_neq B c 0 HBoc HBred HBne HBord) as Hne.
      rewrite Z.mod_0_l in Hne by (clear - Hq3; lia).
      cbn [Z.opp] in Hne.
      rewrite Z.mod_0_l in Hne by (clear - Hq3; lia).
      specialize (Hne ltac:(clear - Hcmod Hc1; lia)
        ltac:(clear - Hcmod Hc1; lia)).
      rewrite mul_zero_x, Hxaeq in Hne.
      intro H0. apply Hne. rewrite H0. unfold UnOp.from. apply Zmod_0_l. }
    (* [x_a <> x_p]: the first chord is not vertical. *)
    assert (Hxab : xa <> bx).
    { pose proof (mul_x_neq B c 1 HBoc HBred HBne HBord) as Hne.
      rewrite (Z.mod_small 1) in Hne by (clear - Hq3; lia).
      rewrite (mod_opp_small 1) in Hne by (clear - Hq3; lia).
      specialize (Hne ltac:(clear - Hcmod Hc1; lia)
        ltac:(clear - Hcmod Hc1 Hcq; lia)).
      rewrite (VarBaseDefs.pallas_mul_one B) in Hne.
      rewrite Hxaeq in Hne.
      rewrite HB in Hne.
      cbn [PallasModel.repr Point.x] in Hne.
      intro Hc'. apply Hne. rewrite Hc'. reflexivity. }
    split; [exact Hxa0 |].
    split; [exact Hxab |].
    (* [x_r <> x_a]: the second chord is not vertical. *)
    assert (HBred' : Pallas.reduced (Weierstrass.Affine bx byv))
      by (rewrite <- HB; exact HBred).
    assert (Hbx : UnOp.from bx = bx) by (exact (proj1 HBred')).
    assert (Hbyv : UnOp.from byv = byv) by (exact (proj2 HBred')).
    set (Ya := y_a xa bx l1 l2) in *.
    assert (HYa : UnOp.from Ya = Ya)
      by (subst Ya; unfold y_a; apply from_mul_reduced).
    assert (Hxa : UnOp.from xa = xa).
    { rewrite <- Hxaeq.
      pose proof (VarBaseDefs.pallas_mul_reduced c B HBred) as HAred.
      destruct (Pallas.mul c B) as [| ax ay].
      - cbn [PallasModel.repr EccSpec.identity Point.x].
        unfold UnOp.from. apply Zmod_0_l.
      - cbn [PallasModel.repr Point.x]. exact (proj1 HAred). }
    (* The signed base [[2k−1] B] the row adds, per bit branch. *)
    assert (Hsigned : exists yb : Z,
        UnOp.from yb = yb /\
        VarBaseDefs.signed_base B k = Weierstrass.Affine bx yb /\
        l1 *F (xa -F bx) = Ya -F yb).
    { destruct Hk as [-> | ->].
      - exists (UnOp.opp byv).
        split; [| split].
        + unfold UnOp.opp, UnOp.from. apply Z.mod_mod.
          unfold Primes.pallas_p, Primes.t_p; lia.
        + unfold VarBaseDefs.signed_base. cbn [Z.eqb].
          rewrite HB. reflexivity.
        + assert (Hs : (0 *F UnOp.from 2 -F UnOp.from 1) *F byv = UnOp.opp byv).
          { unfold UnOp.opp. mod_ring_solve. }
          rewrite Hs in Hg1.
          assert (Hmv : l1 *F (xa -F bx) -F (Ya -F UnOp.opp byv) =
              l1 *F (xa -F bx) -F Ya +F UnOp.opp byv) by mod_ring_solve.
          rewrite Hg1 in Hmv.
          apply sub_zero_equiv in Hmv.
          rewrite from_mul_reduced, from_sub_reduced in Hmv.
          exact Hmv.
      - exists byv.
        split; [| split].
        + exact Hbyv.
        + unfold VarBaseDefs.signed_base. cbn [Z.eqb].
          exact HB.
        + assert (Hs : (1 *F UnOp.from 2 -F UnOp.from 1) *F byv = UnOp.from byv).
          { mod_ring_solve. }
          rewrite Hbyv in Hs.
          rewrite Hs in Hg1.
          assert (Hmv : l1 *F (xa -F bx) -F (Ya -F byv) =
              l1 *F (xa -F bx) -F Ya +F byv) by mod_ring_solve.
          rewrite Hg1 in Hmv.
          apply sub_zero_equiv in Hmv.
          rewrite from_mul_reduced, from_sub_reduced in Hmv.
          exact Hmv. }
    destruct Hsigned as (yb & Hyb & Hsb & Hslope1).
    pose proof (VarBaseIncomplete.chord_add xa Ya bx yb l1
      Hxa HYa Hbx Hyb Hl1 Hxab Hslope1) as Hchord1.
    assert (HAaff : Pallas.mul c B = Weierstrass.Affine xa Ya)
      by (exact (repr_eq_affine (Pallas.mul c B) xa Ya Hacc Hxa0)).
    (* The step's intermediate point is the multiple [[c + 2k − 1] B]. *)
    assert (Hsum : Pallas.mul (c + (2 * k - 1)) B =
        Weierstrass.Affine (x_r xa bx l1) (l1 *F (xa -F x_r xa bx l1) -F Ya)).
    { rewrite (VarBaseDefs.pallas_mul_add c (2 * k - 1) B HBred HBoc).
      rewrite <- (VarBaseDefs.signed_base_mul B k HBred Hk).
      rewrite HAaff, Hsb.
      rewrite Hchord1.
      reflexivity. }
    assert (Hxreq :
        Point.x (PallasModel.repr (Pallas.mul (c + (2 * k - 1)) B)) =
        x_r xa bx l1)
      by (rewrite Hsum; reflexivity).
    pose proof (mul_x_neq B (c + (2 * k - 1)) c HBoc HBred HBne HBord) as Hne.
    assert (Hs1 : c + (2 * k - 1) = c - 1 \/ c + (2 * k - 1) = c + 1)
      by (clear - Hk; destruct Hk as [-> | ->]; [left | right]; lia).
    assert (Hlo : 0 < c + (2 * k - 1) < Pallas.pallas_q)
      by (clear - Hs1 Hc1 Hcq Hq3; lia).
    rewrite (Z.mod_small (c + (2 * k - 1))) in Hne by (clear - Hlo; lia).
    rewrite (mod_opp_small c) in Hne
      by (clear - Hc1 Hcq Hq3; lia).
    specialize (Hne ltac:(clear - Hs1 Hc1 Hcmod; lia)
      ltac:(clear - Hs1 Hc1 Hcq; lia)).
    rewrite Hxreq, Hxaeq in Hne.
    intro Hcc. apply Hne. rewrite Hcc. reflexivity.
  Qed.

  (** ** The strengthened round induction

      The [n]-step incomplete half with the nondegeneracy premise of
      [VarBaseIncomplete.incomplete_half_generic] replaced by the base
      point's order fact and a bound on the multiples the half traverses.
      Its conclusion is exactly that premise, so it composes directly with
      [VarBaseIncomplete.hi_half_correct] and [lo_half_correct].

      [Hqcap] is the scalar bound: the invariant multiple at step [j] is
      [2^(m0+j) + 2 z_{1+j} + 1] with [z_{1+j} < 2^j (z_1 + 1)], so
      [2 c + 1 <= 2^(m0+n) + 2^(n+1) (z_1 + 1) - 1] for every [j <= n − 1].
      For the hi half ([m0 = 0], [n = 125], [z_1 = 0]) the bound is
      [3·2^125]; for the lo half ([m0 = 125], [n = 126],
      [z_1 < 2^125]) it is [3·2^251] — both far below [q_P ≈ 2^254]. *)
  Lemma incomplete_half_nondeg
      (Γ : Assignment.t columns RegionId.t)
      (q2 q3 : Selector.t) (Zc Xa Xp Yp L1 L2 : Advice.t)
      (B : Pallas.point) (bx byv : Z)
      (n m0 : Z)
      (Hn : 1 <= n)
      (Hm0 : 0 <= m0)
      (HB : B = Weierstrass.Affine bx byv)
      (HBred : Pallas.reduced B)
      (HBoc : Pallas.on_curve B)
      (HBne : B <> Pallas.identity)
      (HBord : Pallas.mul Pallas.pallas_q B = Pallas.identity)
      (Hbx2 : adv Γ Xp 2 = bx)
      (Hby2 : adv Γ Yp 2 = byv)
      (Hcap : 2 ^ n * (adv Γ Zc 1 + 1) <= 2 ^ 254)
      (Hqcap :
        2 ^ (m0 + n) + 2 ^ (n + 1) * (adv Γ Zc 1 + 1) < Pallas.pallas_q)
      (Hacc0 : {| Point.x := adv Γ Xa 2; Point.y := adv Γ L1 1 |} =
          PallasModel.repr (Pallas.mul (2 ^ m0 + 2 * adv Γ Zc 1 + 1) B))
      (Hya2 : adv Γ L1 1 =
          y_a (adv Γ Xa 2) (adv Γ Xp 2) (adv Γ L1 2) (adv Γ L2 2))
      (Hsel2 : forall r, 2 <= r <= n ->
          Γ.(Assignment.selector) q2 VarBaseDefs.mul_region r = 1)
      (Hsel3 : Γ.(Assignment.selector) q3 VarBaseDefs.mul_region (n + 1) = 1)
      (Hgate2 : forall row : Z, eval_gate Γ (VarBaseDefs.mul_region, row)
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
            q2 Zc Xa Xp Yp L1 L2))
      (Hgate3 : forall row : Z, eval_gate Γ (VarBaseDefs.mul_region, row)
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
            q3 Zc Xa Xp Yp L1 L2)) :
    forall r, 2 <= r <= n + 1 ->
      adv Γ Xa r <> 0 /\
      adv Γ Xa r <> adv Γ Xp r /\
      x_r (adv Γ Xa r) (adv Γ Xp r) (adv Γ L1 r) <> adv Γ Xa r.
  Proof.
    pose proof pallas_q_lower as Hq3.
    assert (Hplit : 0 < Primes.pallas_p)
      by (unfold Primes.pallas_p, Primes.t_p; lia).
    assert (Hadv_bound : forall (c : Advice.t) (row : Z),
        0 <= adv Γ c row < Primes.pallas_p)
      by (intros; unfold UnOp.from; apply Z.mod_pos_bound; exact Hplit).
    assert (Hadv_red : forall (c : Advice.t) (row : Z),
        UnOp.from (adv Γ c row) = adv Γ c row)
      by (intros; apply from_idem).
    (* The per-row boolean bit, as a field congruence on the running sum. *)
    assert (Hbitfacts : forall r, 2 <= r <= n + 1 ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc r = (2 * adv Γ Zc (r - 1) + k) mod Primes.pallas_p).
    { intros r Hr.
      assert (Hkb : (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) =
          Z.b2z (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2))).
      { destruct (Z.eq_dec r (n + 1)) as [-> | Hne].
        - pose proof (VarBaseIncomplete.q_mul_3_row_facts Γ q3
            Zc Xa Xp Yp L1 L2 (n + 1) Hsel3 (Hgate3 (n + 1))) as H3.
          cbv zeta beta in H3.
          exact (proj1 H3).
        - pose proof (VarBaseIncomplete.q_mul_2_row_facts Γ q2
            Zc Xa Xp Yp L1 L2 r (Hsel2 r ltac:(lia)) (Hgate2 r)) as H2f.
          cbv zeta beta in H2f.
          exact (proj1 (proj2 (proj2 H2f))). }
      assert (Hkv01 : (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) = 0 \/
          (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2) = 1).
      { destruct (Z.odd (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2));
          cbn in Hkb; [right | left]; exact Hkb. }
      exists (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2).
      split; [exact Hkv01 |].
      assert (Hfe : UnOp.from
          (2 * adv Γ Zc (r - 1) +
           (adv Γ Zc r -F adv Γ Zc (r - 1) *F UnOp.from 2)) =
          UnOp.from (adv Γ Zc r)) by mod_ring_solve.
      rewrite Hadv_red in Hfe.
      exact (eq_sym Hfe). }
    assert (Hbits1 : forall j, 0 <= j < n ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc (1 + j + 1) = (2 * adv Γ Zc (1 + j) + k) mod Primes.pallas_p).
    { intros j Hj.
      destruct (Hbitfacts (1 + j + 1) ltac:(lia)) as (k & Hk & He).
      exists k.
      split; [exact Hk |].
      replace (1 + j + 1 - 1) with (1 + j) in He by lia.
      exact He. }
    assert (Hz1 : forall j, 0 <= j <= n ->
        0 <= adv Γ Zc (1 + j) - 2 ^ j * adv Γ Zc 1 < 2 ^ j).
    { apply (VarBaseIncomplete.running_sum_exact
        (fun row => adv Γ Zc row) 1 n).
      - lia.
      - intros j _. apply Hadv_bound.
      - exact Hcap.
      - exact Hbits1. }
    assert (Hzstep : forall j, 0 <= j < n ->
        exists k, (k = 0 \/ k = 1) /\
        adv Γ Zc (1 + j + 1) = 2 * adv Γ Zc (1 + j) + k).
    { apply (VarBaseIncomplete.running_sum_bits_exact
        (fun row => adv Γ Zc row) 1 n).
      - lia.
      - intros j _. apply Hadv_bound.
      - exact Hcap.
      - exact Hbits1. }
    assert (Hyared : forall xa xp l1 l2 : Z,
        UnOp.from (y_a xa xp l1 l2) = y_a xa xp l1 l2)
      by (intros; unfold y_a; apply from_mul_reduced).
    (* The scalar bound at step [j]. *)
    assert (Hcbound : forall j, 0 <= j <= n - 1 ->
        1 < 2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1 /\
        2 * (2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1) + 1 < Pallas.pallas_q).
    { intros j Hj.
      pose proof (Hz1 j ltac:(lia)) as Hzj.
      assert (Hz1nn : 0 <= adv Γ Zc 1) by apply Hadv_bound.
      assert (Hpowmj : 0 < 2 ^ (m0 + j)) by (apply Z.pow_pos_nonneg; lia).
      assert (Hpowj : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
      split; [clear - Hzj Hpowmj Hz1nn Hpowj; nia |].
      assert (Hpowm1 : 2 ^ (m0 + j + 1) = 2 * 2 ^ (m0 + j))
        by (rewrite Z.pow_add_r by lia; lia).
      assert (Hpowmn : 2 ^ (m0 + j + 1) <= 2 ^ (m0 + n))
        by (apply Z.pow_le_mono_r; lia).
      assert (Hpowj2 : (2:Z) ^ (j + 2) = 4 * 2 ^ j)
        by (rewrite Z.pow_add_r by lia; lia).
      assert (Hpowjn : (2:Z) ^ (j + 2) <= 2 ^ (n + 1))
        by (apply Z.pow_le_mono_r; lia).
      assert (Hprod : 2 ^ (j + 2) * (adv Γ Zc 1 + 1) <=
          2 ^ (n + 1) * (adv Γ Zc 1 + 1))
        by (apply Z.mul_le_mono_nonneg_r; [clear - Hz1nn; lia |
              clear - Hpowjn; lia]).
      assert (Hz4 : 4 * adv Γ Zc (1 + j) <=
          2 ^ (j + 2) * (adv Γ Zc 1 + 1) - 4).
      { rewrite Hpowj2. clear - Hzj Hpowj. nia. }
      clear - Hqcap Hpowm1 Hpowmn Hprod Hz4.
      lia. }
    (* Nondegeneracy at row [2 + j] from the invariant at [2 + j]. *)
    assert (Hnd_of_inv : forall j : Z, 0 <= j <= n - 1 ->
        adv Γ Xp (2 + j) = bx -> adv Γ Yp (2 + j) = byv ->
        {| Point.x := adv Γ Xa (2 + j);
           Point.y := y_a (adv Γ Xa (2 + j)) (adv Γ Xp (2 + j))
                        (adv Γ L1 (2 + j)) (adv Γ L2 (2 + j)) |} =
          PallasModel.repr
            (Pallas.mul (2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1) B) ->
        adv Γ Xa (2 + j) <> 0 /\
        adv Γ Xa (2 + j) <> adv Γ Xp (2 + j) /\
        x_r (adv Γ Xa (2 + j)) (adv Γ Xp (2 + j)) (adv Γ L1 (2 + j)) <>
          adv Γ Xa (2 + j)).
    { intros j Hj Hxpr Hypr Hacc.
      destruct (Hzstep j ltac:(lia)) as (k & Hk & Hstep).
      replace (1 + j + 1) with (2 + j) in Hstep by lia.
      assert (Hkv : (adv Γ Zc (2 + j) -F adv Γ Zc (1 + j) *F UnOp.from 2) = k).
      { rewrite Hstep.
        destruct Hk as [-> | ->].
        - transitivity (UnOp.from 0).
          + mod_ring_solve.
          + unfold UnOp.from. apply Zmod_0_l.
        - transitivity (UnOp.from 1).
          + mod_ring_solve.
          + unfold UnOp.from. apply Z.mod_small.
            unfold Primes.pallas_p, Primes.t_p; lia. }
      assert (Hg1 :
          adv Γ L1 (2 + j) *F (adv Γ Xa (2 + j) -F adv Γ Xp (2 + j))
            -F y_a (adv Γ Xa (2 + j)) (adv Γ Xp (2 + j))
                 (adv Γ L1 (2 + j)) (adv Γ L2 (2 + j))
            +F (((adv Γ Zc (2 + j) -F adv Γ Zc (2 + j - 1) *F UnOp.from 2)
                 *F UnOp.from 2 -F UnOp.from 1) *F adv Γ Yp (2 + j)) = 0).
      { destruct (Z.eq_dec (2 + j) (n + 1)) as [Heqr | Hner].
        - rewrite Heqr.
          pose proof (VarBaseIncomplete.q_mul_3_row_facts Γ q3
            Zc Xa Xp Yp L1 L2 (n + 1) Hsel3 (Hgate3 (n + 1))) as H3.
          cbv zeta beta in H3.
          exact (proj1 (proj2 H3)).
        - pose proof (VarBaseIncomplete.q_mul_2_row_facts Γ q2
            Zc Xa Xp Yp L1 L2 (2 + j)
            (Hsel2 (2 + j) ltac:(lia)) (Hgate2 (2 + j))) as H2f.
          cbv zeta beta in H2f.
          exact (proj1 (proj2 (proj2 (proj2 H2f)))). }
      replace (2 + j - 1) with (1 + j) in Hg1 by lia.
      rewrite Hkv in Hg1.
      rewrite Hxpr in Hg1, Hacc |- *.
      rewrite Hypr in Hg1.
      destruct (Hcbound j Hj) as (Hc1 & Hcq).
      exact (step_nondegenerate_derived B bx byv HB HBred HBoc HBne HBord
        (2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1) k
        (adv Γ Xa (2 + j)) (adv Γ L1 (2 + j)) (adv Γ L2 (2 + j))
        (Hadv_red _ _) Hk Hc1 Hcq Hacc Hg1). }
    (* The accumulator invariant, one step at a time. *)
    assert (Hinv : forall j, 0 <= j -> j <= n - 1 ->
        (adv Γ Xp (2 + j) = bx /\ adv Γ Yp (2 + j) = byv) /\
        {| Point.x := adv Γ Xa (2 + j);
           Point.y := y_a (adv Γ Xa (2 + j)) (adv Γ Xp (2 + j))
                        (adv Γ L1 (2 + j)) (adv Γ L2 (2 + j)) |} =
        PallasModel.repr
          (Pallas.mul (2 ^ (m0 + j) + 2 * adv Γ Zc (1 + j) + 1) B)).
    { intros j Hj0.
      pattern j.
      revert Hj0.
      apply natlike_ind.
      - intros _.
        replace (2 + 0) with 2 by lia.
        replace (1 + 0) with 1 by lia.
        replace (m0 + 0) with m0 by lia.
        split.
        + split; [exact Hbx2 | exact Hby2].
        + rewrite <- Hya2. exact Hacc0.
      - intros x Hx IH Hsx.
        specialize (IH ltac:(lia)).
        destruct IH as [[Hxpr Hypr] Hacc].
        pose proof (VarBaseIncomplete.q_mul_2_row_facts Γ q2
          Zc Xa Xp Yp L1 L2 (2 + x)
          (Hsel2 (2 + x) ltac:(lia)) (Hgate2 (2 + x))) as HF.
        cbv zeta beta in HF.
        destruct HF as (Hxp' & Hyp' & _ & Hg1 & Hxan & Hg2).
        replace (2 + x + 1) with (2 + Z.succ x) in Hxp', Hyp', Hxan, Hg2 by lia.
        replace (2 + x - 1) with (1 + x) in Hg1 by lia.
        destruct (Hzstep x ltac:(lia)) as (k & Hk & Hstep).
        replace (1 + x + 1) with (2 + x) in Hstep by lia.
        assert (Hkv : (adv Γ Zc (2 + x) -F adv Γ Zc (1 + x) *F UnOp.from 2) = k).
        { rewrite Hstep.
          destruct Hk as [-> | ->].
          - transitivity (UnOp.from 0).
            + mod_ring_solve.
            + unfold UnOp.from. apply Zmod_0_l.
          - transitivity (UnOp.from 1).
            + mod_ring_solve.
            + unfold UnOp.from. apply Z.mod_small.
              unfold Primes.pallas_p, Primes.t_p; lia. }
        pose proof (Hnd_of_inv x ltac:(lia) Hxpr Hypr Hacc)
          as (Hnd1 & Hnd2 & Hnd3).
        rewrite Hkv in Hg1.
        rewrite Hxpr in Hg1, Hxan, Hg2, Hacc, Hnd2, Hnd3.
        rewrite Hypr in Hg1.
        pose proof (VarBaseIncomplete.incomplete_step_group B bx byv
          HB HBred HBoc
          (2 ^ (m0 + x) + 2 * adv Γ Zc (1 + x) + 1) k
          (adv Γ Xa (2 + x)) (adv Γ L1 (2 + x)) (adv Γ L2 (2 + x))
          (adv Γ Xa (2 + Z.succ x))
          (y_a (adv Γ Xa (2 + Z.succ x)) (adv Γ Xp (2 + Z.succ x))
               (adv Γ L1 (2 + Z.succ x)) (adv Γ L2 (2 + Z.succ x)))
          (Hadv_red _ _) (Hadv_red _ _)
          (Hyared _ _ _ _)
          Hk Hacc Hnd1 Hnd2 Hnd3 Hg1 Hxan Hg2) as Hnext.
        rewrite (VarBaseDefs.step_scalar_shape (m0 + x) (adv Γ Zc (1 + x)) k
          ltac:(lia)) in Hnext.
        rewrite <- Hstep in Hnext.
        replace (m0 + x + 1) with (m0 + Z.succ x) in Hnext by lia.
        split.
        + split; [rewrite Hxp'; exact Hxpr | rewrite Hyp'; exact Hypr].
        + replace (1 + Z.succ x) with (2 + x) by lia.
          exact Hnext. }
    intros r Hr.
    replace r with (2 + (r - 2)) by lia.
    destruct (Hinv (r - 2) ltac:(lia) ltac:(lia)) as [[Hxpr Hypr] Hacc].
    exact (Hnd_of_inv (r - 2) ltac:(lia) Hxpr Hypr Hacc).
  Qed.

  (** ** The two halves, with their nondegeneracy derived

      The region navigations mirror [VarBaseIncomplete.hi_half_correct] and
      [lo_half_correct] (facts 5–13 and 14–21 of
      [mul.synthesize_variable_base_scalar_mul_region]); they differ only
      in the final application, which feeds the nondegeneracy core above
      rather than the invariant core. *)

  Lemma hi_half_nondeg
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (VarBaseDefs.base_wpoint Γ))
      (HBoc : Pallas.on_curve (VarBaseDefs.base_wpoint Γ))
      (HBne : VarBaseDefs.base_wpoint Γ <> Pallas.identity)
      (HBord :
        Pallas.mul Pallas.pallas_q (VarBaseDefs.base_wpoint Γ) =
          Pallas.identity)
      (Hinit :
        {| Point.x := VarBaseDefs.av Γ Advice.A2 1;
           Point.y := VarBaseDefs.av Γ Advice.A3 1 |} =
        PallasModel.repr (Pallas.mul 2 (VarBaseDefs.base_wpoint Γ))) :
    forall r, 2 <= r <= 126 -> VarBaseDefs.hi_step_nondegenerate Γ r.
  Proof.
    pose proof (VarBaseDefs.variable_base_region_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hz1c.
    do 5 apply interpret_region_facts_bind_right in Hz1c.
    apply interpret_region_facts_bind_left in Hz1c.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hz1c.
    destruct Hz1c as [Hz1c _].
    pose proof Hfacts as Hsel1.
    do 6 apply interpret_region_facts_bind_right in Hsel1.
    apply interpret_region_facts_bind_left in Hsel1.
    cbn [region_facts interpret_facts interpret_fact] in Hsel1.
    destruct Hsel1 as [Hsel1 _].
    pose proof Hfacts as Hblock.
    do 7 apply interpret_region_facts_bind_right in Hblock.
    apply interpret_region_facts_bind_left in Hblock.
    pose proof Hfacts as Hsel3.
    do 8 apply interpret_region_facts_bind_right in Hsel3.
    apply interpret_region_facts_bind_left in Hsel3.
    cbn [region_facts interpret_facts interpret_fact] in Hsel3.
    destruct Hsel3 as [Hsel3 _].
    pose proof Hfacts as Hcopy_x.
    do 10 apply interpret_region_facts_bind_right in Hcopy_x.
    apply interpret_region_facts_bind_left in Hcopy_x.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_x.
    destruct Hcopy_x as [Hcopy_x _].
    pose proof Hfacts as Hcopy_y.
    do 11 apply interpret_region_facts_bind_right in Hcopy_y.
    apply interpret_region_facts_bind_left in Hcopy_y.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_y.
    destruct Hcopy_y as [Hcopy_y _].
    pose proof Hfacts as Hcopy_bx.
    do 12 apply interpret_region_facts_bind_right in Hcopy_bx.
    apply interpret_region_facts_bind_left in Hcopy_bx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_bx.
    destruct Hcopy_bx as [Hcopy_bx _].
    pose proof Hfacts as Hcopy_by.
    do 13 apply interpret_region_facts_bind_right in Hcopy_by.
    apply interpret_region_facts_bind_left in Hcopy_by.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_by.
    destruct Hcopy_by as [Hcopy_by _].
    cbn in Hz1c, Hcopy_x, Hcopy_y, Hcopy_bx, Hcopy_by.
    assert (Hz1adv : adv Γ Advice.A9 1 = 0)
      by (rewrite Hz1c; apply Zmod_0_l).
    assert (Hcx : adv Γ Advice.A3 2 = adv Γ Advice.A2 1)
      by (f_equal; exact Hcopy_x).
    assert (Hcy : adv Γ Advice.A4 1 = adv Γ Advice.A3 1)
      by (f_equal; exact Hcopy_y).
    set (bx :=
      UnOp.from (Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0)).
    set (byv :=
      UnOp.from (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0)).
    assert (Hcbx : adv Γ Advice.A0 2 = bx)
      by (subst bx; f_equal; exact Hcopy_bx).
    assert (Hcby : adv Γ Advice.A1 2 = byv)
      by (subst byv; f_equal; exact Hcopy_by).
    assert (Hbp : VarBaseDefs.base_point Γ =
        {| Point.x := Γ.(Assignment.advice) Advice.A0
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p;
           Point.y := Γ.(Assignment.advice) Advice.A1
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p |}).
    { unfold VarBaseDefs.base_point, OrchardActionInputs.read_point,
        OrchardActionInputs.read, OrchardActionInputs.read1,
        OrchardActionInputs.read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : VarBaseDefs.base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold VarBaseDefs.base_wpoint.
      rewrite Hbp.
      unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0) &&
        (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0))%bool eqn:Hid.
      - exfalso. apply HBne.
        unfold VarBaseDefs.base_wpoint.
        rewrite Hbp.
        unfold PallasModel.unrepr.
        cbn [Point.x Point.y].
        rewrite Hid.
        reflexivity.
      - reflexivity. }
    pose proof (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteHi1 Advice.A3 Advice.A0 Advice.A4 Advice.A5)
        VarBaseDefs.mul_region 1
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate1.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteHi2 Advice.A9 Advice.A3 Advice.A0 Advice.A1
          Advice.A4 Advice.A5)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate2.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteHi3 Advice.A9 Advice.A3 Advice.A0 Advice.A1
          Advice.A4 Advice.A5)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate3.
    pose proof (QMul1Checks.deterministic Γ VarBaseDefs.mul_region 1
        Selector.QMulIncompleteHi1 Advice.A3 Advice.A0 Advice.A4 Advice.A5
        (enabled_nonzero Γ Selector.QMulIncompleteHi1 VarBaseDefs.mul_region 1
          Hsel1)
        Hgate1) as Hq1.
    unfold QMul1Checks.output in Hq1.
    injection Hq1.
    intro Hya2raw.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hya2raw.
    change (rotated_row 1 Rotation.next) with 2 in Hya2raw.
    change (rotated_row 1 Rotation.cur) with 1 in Hya2raw.
    assert (Hcap' : 2 ^ 125 * (adv Γ Advice.A9 1 + 1) <= 2 ^ 254).
    { rewrite Hz1adv.
      replace (0 + 1) with 1 by lia.
      rewrite Z.mul_1_r.
      apply Z.pow_le_mono_r; lia. }
    assert (Hqcap' :
        2 ^ (0 + 125) + 2 ^ (125 + 1) * (adv Γ Advice.A9 1 + 1) <
          Pallas.pallas_q).
    { rewrite Hz1adv.
      replace (0 + 125) with 125 by lia.
      replace (125 + 1) with 126 by lia.
      replace (0 + 1) with 1 by lia.
      rewrite Z.mul_1_r.
      assert (H125 : (2:Z) ^ 125 <= 2 ^ 253) by (apply Z.pow_le_mono_r; lia).
      assert (H126 : (2:Z) ^ 126 <= 2 ^ 253) by (apply Z.pow_le_mono_r; lia).
      assert (H254 : (2:Z) ^ 254 = 2 * 2 ^ 253)
        by (replace 254 with (Z.succ 253) by lia;
            rewrite Z.pow_succ_r by lia; lia).
      unfold Pallas.pallas_q, Primes.pallas_q, Primes.t_q.
      clear - H125 H126 H254. lia. }
    assert (Hacc0' :
        {| Point.x := adv Γ Advice.A3 2; Point.y := adv Γ Advice.A4 1 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 0 + 2 * adv Γ Advice.A9 1 + 1)
            (VarBaseDefs.base_wpoint Γ))).
    { rewrite Hcx, Hcy, Hz1adv.
      replace (2 ^ 0 + 2 * 0 + 1) with 2 by lia.
      rewrite !VarBaseIncomplete.av_adv in Hinit.
      exact Hinit. }
    assert (Hsel2' : forall r, 2 <= r <= 125 ->
        Γ.(Assignment.selector) Selector.QMulIncompleteHi2
          VarBaseDefs.mul_region r = 1).
    { intros r Hr.
      apply (VarBaseIncomplete.enable_selector_rows_on Γ VarBaseDefs.mul_region
        Selector.QMulIncompleteHi2 124 2 Hblock).
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
      lia. }
    pose proof (incomplete_half_nondeg Γ
      Selector.QMulIncompleteHi2 Selector.QMulIncompleteHi3
      Advice.A9 Advice.A3 Advice.A0 Advice.A1 Advice.A4 Advice.A5
      (VarBaseDefs.base_wpoint Γ) bx byv 125 0
      ltac:(lia) ltac:(lia) HB HBred HBoc HBne HBord Hcbx Hcby
      Hcap' Hqcap' Hacc0' Hya2raw Hsel2' Hsel3 Hgate2 Hgate3) as Hmain.
    intros r Hr.
    unfold VarBaseDefs.hi_step_nondegenerate, VarBaseDefs.step_nondegenerate.
    rewrite !VarBaseIncomplete.av_adv.
    apply Hmain.
    lia.
  Qed.

  Lemma lo_half_nondeg
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (HBred : Pallas.reduced (VarBaseDefs.base_wpoint Γ))
      (HBoc : Pallas.on_curve (VarBaseDefs.base_wpoint Γ))
      (HBne : VarBaseDefs.base_wpoint Γ <> Pallas.identity)
      (HBord :
        Pallas.mul Pallas.pallas_q (VarBaseDefs.base_wpoint Γ) =
          Pallas.identity)
      (Hz_hi : 0 <= VarBaseDefs.av Γ Advice.A9 126 < 2 ^ 125)
      (Hinit :
        {| Point.x := VarBaseDefs.av Γ Advice.A3 127;
           Point.y := VarBaseDefs.av Γ Advice.A4 127 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 125 + 2 * VarBaseDefs.av Γ Advice.A9 126 + 1)
            (VarBaseDefs.base_wpoint Γ))) :
    forall r, 2 <= r <= 127 -> VarBaseDefs.lo_step_nondegenerate Γ r.
  Proof.
    pose proof (VarBaseDefs.variable_base_region_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hsel1.
    do 14 apply interpret_region_facts_bind_right in Hsel1.
    apply interpret_region_facts_bind_left in Hsel1.
    cbn [region_facts interpret_facts interpret_fact] in Hsel1.
    destruct Hsel1 as [Hsel1 _].
    pose proof Hfacts as Hblock.
    do 15 apply interpret_region_facts_bind_right in Hblock.
    apply interpret_region_facts_bind_left in Hblock.
    pose proof Hfacts as Hsel3.
    do 16 apply interpret_region_facts_bind_right in Hsel3.
    apply interpret_region_facts_bind_left in Hsel3.
    cbn [region_facts interpret_facts interpret_fact] in Hsel3.
    destruct Hsel3 as [Hsel3 _].
    pose proof Hfacts as Hcopy_z.
    do 17 apply interpret_region_facts_bind_right in Hcopy_z.
    apply interpret_region_facts_bind_left in Hcopy_z.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_z.
    destruct Hcopy_z as [Hcopy_z _].
    pose proof Hfacts as Hcopy_x.
    do 18 apply interpret_region_facts_bind_right in Hcopy_x.
    apply interpret_region_facts_bind_left in Hcopy_x.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_x.
    destruct Hcopy_x as [Hcopy_x _].
    pose proof Hfacts as Hcopy_y.
    do 19 apply interpret_region_facts_bind_right in Hcopy_y.
    apply interpret_region_facts_bind_left in Hcopy_y.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_y.
    destruct Hcopy_y as [Hcopy_y _].
    pose proof Hfacts as Hcopy_bx.
    do 20 apply interpret_region_facts_bind_right in Hcopy_bx.
    apply interpret_region_facts_bind_left in Hcopy_bx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_bx.
    destruct Hcopy_bx as [Hcopy_bx _].
    pose proof Hfacts as Hcopy_by.
    do 21 apply interpret_region_facts_bind_right in Hcopy_by.
    apply interpret_region_facts_bind_left in Hcopy_by.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_by.
    destruct Hcopy_by as [Hcopy_by _].
    cbn in Hcopy_z, Hcopy_x, Hcopy_y, Hcopy_bx, Hcopy_by.
    assert (Hz1lo : adv Γ Advice.A6 1 = adv Γ Advice.A9 126)
      by (f_equal; exact Hcopy_z).
    assert (Hcx : adv Γ Advice.A7 2 = adv Γ Advice.A3 127)
      by (f_equal; exact Hcopy_x).
    assert (Hcy : adv Γ Advice.A8 1 = adv Γ Advice.A4 127)
      by (f_equal; exact Hcopy_y).
    set (bx :=
      UnOp.from (Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0)).
    set (byv :=
      UnOp.from (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0)).
    assert (Hcbx : adv Γ Advice.A0 2 = bx)
      by (subst bx; f_equal; exact Hcopy_bx).
    assert (Hcby : adv Γ Advice.A1 2 = byv)
      by (subst byv; f_equal; exact Hcopy_by).
    assert (Hbp : VarBaseDefs.base_point Γ =
        {| Point.x := Γ.(Assignment.advice) Advice.A0
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p;
           Point.y := Γ.(Assignment.advice) Advice.A1
             VarBaseDefs.gd_old_region 0 mod Primes.pallas_p |}).
    { unfold VarBaseDefs.base_point, OrchardActionInputs.read_point,
        OrchardActionInputs.read, OrchardActionInputs.read1,
        OrchardActionInputs.read_advice.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression].
      change (rotated_row 0 Rotation.cur) with 0.
      reflexivity. }
    assert (HB : VarBaseDefs.base_wpoint Γ = Weierstrass.Affine bx byv).
    { unfold VarBaseDefs.base_wpoint.
      rewrite Hbp.
      unfold PallasModel.unrepr.
      cbn [Point.x Point.y].
      destruct ((Γ.(Assignment.advice) Advice.A0 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0) &&
        (Γ.(Assignment.advice) Advice.A1 VarBaseDefs.gd_old_region 0
          mod Primes.pallas_p =? 0))%bool eqn:Hid.
      - exfalso. apply HBne.
        unfold VarBaseDefs.base_wpoint.
        rewrite Hbp.
        unfold PallasModel.unrepr.
        cbn [Point.x Point.y].
        rewrite Hid.
        reflexivity.
      - reflexivity. }
    pose proof (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          Selector.QMulIncompleteLo1 Advice.A7 Advice.A0 Advice.A8 Advice.A2)
        VarBaseDefs.mul_region 1
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate1.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          Selector.QMulIncompleteLo2 Advice.A6 Advice.A7 Advice.A0 Advice.A1
          Advice.A8 Advice.A2)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate2.
    pose proof (fun row => satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          Selector.QMulIncompleteLo3 Advice.A6 Advice.A7 Advice.A0 Advice.A1
          Advice.A8 Advice.A2)
        VarBaseDefs.mul_region row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (OrchardActionFacts.holds_gates Γ Hcircuit)) as Hgate3.
    pose proof (QMul1Checks.deterministic Γ VarBaseDefs.mul_region 1
        Selector.QMulIncompleteLo1 Advice.A7 Advice.A0 Advice.A8 Advice.A2
        (enabled_nonzero Γ Selector.QMulIncompleteLo1 VarBaseDefs.mul_region 1
          Hsel1)
        Hgate1) as Hq1.
    unfold QMul1Checks.output in Hq1.
    injection Hq1.
    intro Hya2raw.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression] in Hya2raw.
    change (rotated_row 1 Rotation.next) with 2 in Hya2raw.
    change (rotated_row 1 Rotation.cur) with 1 in Hya2raw.
    rewrite !VarBaseIncomplete.av_adv in Hz_hi, Hinit.
    assert (Hpow251 : (2:Z) ^ 126 * 2 ^ 125 = 2 ^ 251)
      by (rewrite <- Z.pow_add_r by lia; reflexivity).
    assert (Hcap' : 2 ^ 126 * (adv Γ Advice.A6 1 + 1) <= 2 ^ 254).
    { rewrite Hz1lo.
      assert (Hle : adv Γ Advice.A9 126 + 1 <= 2 ^ 125) by lia.
      assert (Hmul : 2 ^ 126 * (adv Γ Advice.A9 126 + 1) <= 2 ^ 126 * 2 ^ 125)
        by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hp3 : (2:Z) ^ 251 <= 2 ^ 254) by (apply Z.pow_le_mono_r; lia).
      lia. }
    assert (Hqcap' :
        2 ^ (125 + 126) + 2 ^ (126 + 1) * (adv Γ Advice.A6 1 + 1) <
          Pallas.pallas_q).
    { rewrite Hz1lo.
      replace (125 + 126) with 251 by lia.
      replace (126 + 1) with 127 by lia.
      assert (Hle : adv Γ Advice.A9 126 + 1 <= 2 ^ 125) by lia.
      assert (Hmul : 2 ^ 127 * (adv Γ Advice.A9 126 + 1) <= 2 ^ 127 * 2 ^ 125)
        by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hpow252 : (2:Z) ^ 127 * 2 ^ 125 = 2 ^ 252)
        by (rewrite <- Z.pow_add_r by lia; reflexivity).
      assert (H251 : (2:Z) ^ 251 <= 2 ^ 253) by (apply Z.pow_le_mono_r; lia).
      assert (H252 : (2:Z) ^ 252 <= 2 ^ 253) by (apply Z.pow_le_mono_r; lia).
      assert (H254 : (2:Z) ^ 254 = 2 * 2 ^ 253)
        by (replace 254 with (Z.succ 253) by lia;
            rewrite Z.pow_succ_r by lia; lia).
      unfold Pallas.pallas_q, Primes.pallas_q, Primes.t_q.
      clear - Hmul Hpow252 H251 H252 H254. lia. }
    assert (Hacc0' :
        {| Point.x := adv Γ Advice.A7 2; Point.y := adv Γ Advice.A8 1 |} =
        PallasModel.repr
          (Pallas.mul (2 ^ 125 + 2 * adv Γ Advice.A6 1 + 1)
            (VarBaseDefs.base_wpoint Γ))).
    { rewrite Hcx, Hcy, Hz1lo.
      exact Hinit. }
    assert (Hsel2' : forall r, 2 <= r <= 126 ->
        Γ.(Assignment.selector) Selector.QMulIncompleteLo2
          VarBaseDefs.mul_region r = 1).
    { intros r Hr.
      apply (VarBaseIncomplete.enable_selector_rows_on Γ VarBaseDefs.mul_region
        Selector.QMulIncompleteLo2 125 2 Hblock).
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
      lia. }
    pose proof (incomplete_half_nondeg Γ
      Selector.QMulIncompleteLo2 Selector.QMulIncompleteLo3
      Advice.A6 Advice.A7 Advice.A0 Advice.A1 Advice.A8 Advice.A2
      (VarBaseDefs.base_wpoint Γ) bx byv 126 125
      ltac:(lia) ltac:(lia) HB HBred HBoc HBne HBord Hcbx Hcby
      Hcap' Hqcap' Hacc0' Hya2raw Hsel2' Hsel3 Hgate2 Hgate3) as Hmain.
    intros r Hr.
    unfold VarBaseDefs.lo_step_nondegenerate, VarBaseDefs.step_nondegenerate.
    rewrite !VarBaseIncomplete.av_adv.
    apply Hmain.
    lia.
  Qed.

  (** ** [VarBaseMul.mul_nondegenerate], derived from the gates

      §4.18.4 grants the variable-base multiplication no exceptional
      escape, and none is needed: on a satisfying assignment every
      incomplete double-and-add step of the [[ivk] g_d^old] ladder is
      nondegenerate.  The base facts are themselves circuit-derived — the
      [QWitnessPointNonId] curve-equation gate at the [GDOld] region
      ([DiversifiedAddress.base_point_facts]) and the Pallas curve-order
      theorem ([DiversifiedAddress.base_point_order]). *)
  Theorem mul_nondegenerate_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    VarBaseMul.mul_nondegenerate Γ.
  Proof.
    destruct (DiversifiedAddress.base_point_facts Γ Hcircuit)
      as (HBred & HBoc & HBne).
    pose proof (DiversifiedAddress.base_point_order Γ Hcircuit) as HBord.
    pose proof (VarBaseMul.init_acc_correct Γ Hcircuit HBred HBoc) as Hinit.
    pose proof (hi_half_nondeg Γ Hcircuit HBred HBoc HBne HBord Hinit)
      as Hhi_nd.
    pose proof
      (VarBaseMul.hi_half_correct Γ Hcircuit HBred HBoc HBne Hhi_nd Hinit)
      as (Hzh_range & _ & Hhi_acc).
    pose proof
      (lo_half_nondeg Γ Hcircuit HBred HBoc HBne HBord Hzh_range Hhi_acc)
      as Hlo_nd.
    exact (conj Hhi_nd Hlo_nd).
  Qed.

  (** ** The §4.18.4 clause

      'Diversified address integrity': [ivk = ⊥ or pk_d^old = [ivk] g_d^old].
      The only hypotheses are circuit acceptance and the [Commit^ivk]
      short-lookup range family — the relational selector model's residue
      (the range-check lookup leaves [q_running] free), discharged from
      operational acceptance by the lookup-closure machinery.  No
      nondegeneracy hypothesis appears: the Sinsemilla one is replaced by
      the clause's own ⊥ disjunct, and the mul chip's is derived above. *)
  Theorem diversified_address_obligation_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : CommitIvkHash.commit_ivk_short_lookup_ok Γ) :
    OrchardAdversarialApi.diversified_address_obligation Γ.
  Proof.
    destruct (OrchardAdversarialApi.commit_ivk_bot_of Γ) as [ivk |] eqn:E.
    2: { left. exact E. }
    right.
    exists ivk.
    split; [exact E |].
    (* Definedness of the ⊥-carrying commitment is nondegeneracy of the
       [Commit^ivk] fold. *)
    assert (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.commit_ivk_q orchard_circuit_params)
          (OrchardSpec.commit_ivk_message
            (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
            (OrchardSpec.in_nk (read_action_inputs Γ)))).
    { apply (proj1 (OrchardProtocolSpecBot.commit_ivk_bot_defined_iff
        orchard_circuit_params
        (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
        (OrchardSpec.in_nk (read_action_inputs Γ))
        (OrchardValidActionInputs.read_rivk Γ))).
      unfold OrchardAdversarialApi.commit_ivk_bot_of in E.
      rewrite E.
      discriminate. }
    (* On the tracking branch the ⊥-carrying commitment is the total one. *)
    assert (Hivk :
        ivk =
        OrchardProtocolSpec.commit_ivk orchard_circuit_params
          (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
          (OrchardSpec.in_nk (read_action_inputs Γ))
          (OrchardValidActionInputs.read_rivk Γ)).
    { unfold OrchardAdversarialApi.commit_ivk_bot_of in E.
      rewrite (OrchardProtocolSpecBot.commit_ivk_bot_some
        orchard_circuit_params
        (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
        (OrchardSpec.in_nk (read_action_inputs Γ))
        (OrchardValidActionInputs.read_rivk Γ) Hnd) in E.
      exact (eq_sym
        (f_equal (fun o : option Z => match o with Some z => z | None => 0 end)
          E)). }
    rewrite Hivk.
    apply (OrchardValidActionInputs.diversified_address_integrity Γ Hcircuit).
    refine (conj _ (conj Hshort (mul_nondegenerate_of_holds Γ Hcircuit))).
    change (OrchardValidActionInputs.commit_ivk_words Γ)
      with (CommitIvkHash.commit_ivk_words Γ).
    rewrite (CommitIvkHash.commit_ivk_words_correct Γ Hcircuit Hshort).
    exact Hnd.
  Qed.

  (** The residue the adversarial assembly re-points: with the mul-chip
      nondegeneracy derived, [commit_ivk_witness_ok] reduces to the
      Sinsemilla nondegeneracy and the short-lookup family. *)
  Theorem commit_ivk_witness_ok_of_nondegenerate
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate
          (OrchardSpec.commit_ivk_q orchard_circuit_params)
          (OrchardValidActionInputs.commit_ivk_words Γ))
      (Hshort : CommitIvkHash.commit_ivk_short_lookup_ok Γ) :
    OrchardValidActionInputs.commit_ivk_witness_ok Γ.
  Proof.
    exact (conj Hnondeg
      (conj Hshort (mul_nondegenerate_of_holds Γ Hcircuit))).
  Qed.
End OrchardOwnershipBot.
