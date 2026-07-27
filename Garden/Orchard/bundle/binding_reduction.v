(** * Pedersen-binding reduction for the Orchard value-commitment bases

    The two-openings reduction behind the §4.14 balance argument: two
    distinct openings of one Orchard value commitment (§5.4.8.3,
    [ValueCommit^Orchard_rcv(v) = [v] 𝒱^Orchard + [rcv] ℛ^Orchard]) yield an
    explicit discrete logarithm of [ℛ^Orchard] in base [𝒱^Orchard] — the
    [OrchardBundleSpec.dlog_relation] disjunct of the balance theorems.

    Binding is stated as a reduction, never as an independence axiom: the
    Pallas group is cyclic of prime order, so [∃ k, ℛ = [k] 𝒱] is a theorem
    and an axiom [([a] 𝒱 + [b] ℛ = 𝒪) -> a ≡ b ≡ 0 (mod q)] would be
    refutable in-model.  The content of this file is therefore the
    computability of the witness: from a collision
    [[v] 𝒱 + [r] ℛ = [v'] 𝒱 + [r'] ℛ] with [v ≢ v' (mod q)], the scalar

      [k := ((v - v') * mod_inverse (r' - r) q) mod q]

    is an explicit function of the two openings with [ℛ = [k] 𝒱]
    ([extracted_k] / [two_openings_dlog]).  Discarding the resulting
    disjunct is exactly the discrete-log hardness assumption on the
    generator pair, mirroring the protocol's own reduction pattern.

    The proof: cancellation in the abelian group collapses the collision to
    [[v - v'] 𝒱 = [r' - r] ℛ] ([openings_collapse]); [r' - r ≢ 0 (mod q)],
    since otherwise the right side is the identity and injectivity of
    [mul] on [𝒱] ([PallasGeneratorsOrder.value_commit_v_mul_injective])
    forces [v ≡ v' (mod q)]; inverting [r' - r] modulo the (prime) group
    order [q] and moving the inverse across with the scalar-multiplication
    composition law gives the relation.  All scalar arithmetic stays in ℤ,
    reduced modulo [pallas_q] only at the injectivity and inversion steps. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.bundle.spec.
Require Import Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardBindingReduction.
  Import Pallas.
  Import PallasGenerators.

  (** ** Group-law closure and algebra at the Pallas instance

      Pallas-level wrappers of the generic [Weierstrass] group laws, with
      the curve side conditions ([eleven_lt_p], [nonsingular]) discharged
      once, so the reduction proofs below rewrite syntactically on
      [Pallas.add] / [Pallas.mul] terms. *)

  Lemma neg_reduced_p (P : point) : reduced P -> reduced (neg P).
  Proof. apply Weierstrass.neg_reduced. Qed.

  Lemma mul_reduced_p (k : Z) (P : point) : reduced P -> reduced (mul k P).
  Proof. apply Weierstrass.mul_reduced. Qed.

  Lemma add_reduced_p (P Q : point) :
    reduced P -> reduced Q -> reduced (add P Q).
  Proof. apply Weierstrass.add_reduced. Qed.

  Lemma add_on_curve_p (P Q : point) :
    on_curve P -> on_curve Q -> on_curve (add P Q).
  Proof.
    intros HP HQ.
    exact (Weierstrass.add_on_curve (p := Primes.pallas_p) a b P Q
             three_lt_p HP HQ).
  Qed.

  Lemma neg_on_curve_p (P : point) : on_curve P -> on_curve (neg P).
  Proof.
    intro HP. unfold on_curve, neg, Pallas.on_curve, Pallas.neg in *.
    destruct P as [| x y].
    - exact I.
    - cbn [Weierstrass.neg Weierstrass.on_curve] in *.
      rewrite <- HP.
      assert (Heq :
          UnOp.opp (p := Primes.pallas_p) y *F UnOp.opp (p := Primes.pallas_p) y
          = y *F y).
      { unfold UnOp.opp, BinOp.mul.
        rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_opp_opp.
        reflexivity. }
      rewrite Heq. reflexivity.
  Qed.

  Lemma mul_pos_on_curve_p (n : positive) (P : point) :
    on_curve P ->
    on_curve (Weierstrass.mul_pos (p := Primes.pallas_p) a n P).
  Proof.
    intros HP. induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos].
    - apply add_on_curve_p; [exact HP |].
      apply add_on_curve_p; exact IH.
    - apply add_on_curve_p; exact IH.
    - exact HP.
  Qed.

  Lemma mul_on_curve_p (k : Z) (P : point) :
    on_curve P -> on_curve (mul k P).
  Proof.
    intros HP. unfold mul, Weierstrass.mul. destruct k as [| n | n].
    - exact I.
    - apply mul_pos_on_curve_p. exact HP.
    - apply neg_on_curve_p. apply mul_pos_on_curve_p. exact HP.
  Qed.

  Lemma add_comm_p (P Q : point) :
    on_curve P -> on_curve Q -> add P Q = add Q P.
  Proof. apply Weierstrass.add_comm. Qed.

  Lemma add_assoc_p (P Q R : point) :
    reduced P -> reduced Q -> reduced R ->
    on_curve P -> on_curve Q -> on_curve R ->
    add (add P Q) R = add P (add Q R).
  Proof.
    intros HrP HrQ HrR HoP HoQ HoR.
    exact (Weierstrass.add_assoc (p := Primes.pallas_p) a b P Q R
             eleven_lt_p nonsingular HrP HrQ HrR HoP HoQ HoR).
  Qed.

  Lemma add_neg_p (P : point) : add P (neg P) = identity.
  Proof. exact (Weierstrass.add_neg (p := Primes.pallas_p) a b P). Qed.

  Lemma add_identity_r_p (P : point) : add P identity = P.
  Proof. exact (Weierstrass.add_Infinity_r (p := Primes.pallas_p) a b P). Qed.

  Lemma mul_add_p (i j : Z) (P : point) :
    reduced P -> on_curve P ->
    mul (i + j) P = add (mul i P) (mul j P).
  Proof.
    intros Hr Ho.
    exact (Weierstrass.mul_add (p := Primes.pallas_p) a b i j P
             eleven_lt_p nonsingular Hr Ho).
  Qed.

  Lemma mul_neg_p (i : Z) (P : point) :
    reduced P -> mul (- i) P = neg (mul i P).
  Proof. exact (Weierstrass.mul_neg (p := Primes.pallas_p) a b i P). Qed.

  Lemma mul_mul_p (i j : Z) (P : point) :
    reduced P -> on_curve P ->
    mul (i * j) P = mul i (mul j P).
  Proof.
    intros Hr Ho.
    exact (Weierstrass.mul_mul (p := Primes.pallas_p) a b i j P
             eleven_lt_p nonsingular Hr Ho).
  Qed.

  Lemma mul_1_p (P : point) : mul 1 P = P.
  Proof. reflexivity. Qed.

  (** Cancellation in the abelian group: a collision [A ⊕ B = A' ⊕ B']
      switches to [A ⊖ A' = B' ⊖ B]. *)
  Lemma add_switch (A B A' B' : point) :
    reduced A -> reduced B -> reduced A' -> reduced B' ->
    on_curve A -> on_curve B -> on_curve A' -> on_curve B' ->
    add A B = add A' B' ->
    add A (neg A') = add B' (neg B).
  Proof.
    intros HrA HrB HrA' HrB' HoA HoB HoA' HoB' Heq.
    assert (HrnA' : reduced (neg A')) by (apply neg_reduced_p; exact HrA').
    assert (HrnB : reduced (neg B)) by (apply neg_reduced_p; exact HrB).
    assert (HonA' : on_curve (neg A')) by (apply neg_on_curve_p; exact HoA').
    assert (HonB : on_curve (neg B)) by (apply neg_on_curve_p; exact HoB).
    assert (HrA'B' : reduced (add A' B'))
      by (apply add_reduced_p; assumption).
    assert (HoA'B' : on_curve (add A' B'))
      by (apply add_on_curve_p; assumption).
    assert (HA : A = add (add A' B') (neg B)).
    { rewrite <- Heq.
      rewrite (add_assoc_p A B (neg B) HrA HrB HrnB HoA HoB HonB).
      rewrite (add_neg_p B).
      rewrite (add_identity_r_p A).
      reflexivity. }
    rewrite HA.
    rewrite (add_assoc_p (add A' B') (neg B) (neg A')
               HrA'B' HrnB HrnA' HoA'B' HonB HonA').
    rewrite (add_comm_p (neg B) (neg A') HonB HonA').
    rewrite <- (add_assoc_p (add A' B') (neg A') (neg B)
                  HrA'B' HrnA' HrnB HoA'B' HonA' HonB).
    rewrite (add_comm_p A' B' HoA' HoB').
    rewrite (add_assoc_p B' A' (neg A') HrB' HrA' HrnA' HoB' HoA' HonA').
    rewrite (add_neg_p A').
    rewrite (add_identity_r_p B').
    reflexivity.
  Qed.

  (** ** The two-openings collapse

      A collision between two openings of one value commitment collapses to
      a single scalar relation between the §5.4.8.3 bases,
      [[v - v'] 𝒱 = [r' - r] ℛ], with both scalar differences in ℤ. *)
  Lemma openings_collapse (v r v' r' : Z) :
    add (mul v value_commit_v_G) (mul r value_commit_r_G) =
    add (mul v' value_commit_v_G) (mul r' value_commit_r_G) ->
    mul (v - v') value_commit_v_G = mul (r' - r) value_commit_r_G.
  Proof.
    intros Heq.
    pose proof value_commit_v_reduced as HrV.
    pose proof value_commit_v_on_curve as HoV.
    pose proof value_commit_r_reduced as HrR.
    pose proof value_commit_r_on_curve as HoR.
    assert (Hswitch :
        add (mul v value_commit_v_G) (neg (mul v' value_commit_v_G)) =
        add (mul r' value_commit_r_G) (neg (mul r value_commit_r_G))).
    { apply add_switch;
        try (apply mul_reduced_p; assumption);
        try (apply mul_on_curve_p; assumption).
      exact Heq. }
    replace (v - v') with (v + - v') by ring.
    rewrite (mul_add_p v (- v') value_commit_v_G HrV HoV).
    rewrite (mul_neg_p v' value_commit_v_G HrV).
    replace (r' - r) with (r' + - r) by ring.
    rewrite (mul_add_p r' (- r) value_commit_r_G HrR HoR).
    rewrite (mul_neg_p r value_commit_r_G HrR).
    exact Hswitch.
  Qed.

  (** ** The explicit discrete-log witness

      The scalar extracted from two openings [(v, r)] and [(v', r')] of one
      commitment: [(v - v') / (r' - r)] modulo the group order, computed
      with the extended-Euclid field inverse.  When the openings collide
      and [v ≢ v' (mod q)], this is a discrete logarithm of [ℛ^Orchard] in
      base [𝒱^Orchard] ([two_openings_dlog]). *)
  Definition extracted_k (v v' r r' : Z) : Z :=
    ((v - v') * mod_inverse (r' - r) pallas_q) mod pallas_q.

  (** The Pedersen-binding reduction: a collision between two openings of
      one value commitment with distinct value scalars modulo the group
      order yields the explicit discrete-log relation at [extracted_k]. *)
  Theorem two_openings_dlog (v r v' r' : Z) :
    add (mul v value_commit_v_G) (mul r value_commit_r_G) =
    add (mul v' value_commit_v_G) (mul r' value_commit_r_G) ->
    v mod pallas_q <> v' mod pallas_q ->
    OrchardBundleSpec.dlog_relation (extracted_k v v' r r').
  Proof.
    intros Heq Hv.
    pose proof (openings_collapse v r v' r' Heq) as Hcol.
    assert (Hq2 : 2 <= pallas_q).
    { apply Znumtheory.prime_ge_2. exact pallas_q_is_prime. }
    (* [r' - r] is nonzero modulo [q]: otherwise [[r' - r] ℛ] is the
       identity, so [[v - v'] 𝒱] is too, and injectivity of [mul] on [𝒱]
       forces [v ≡ v' (mod q)]. *)
    assert (Hd : (r' - r) mod pallas_q <> 0).
    { intros Hd0. apply Hv.
      assert (HR0 : mul (r' - r) value_commit_r_G = identity).
      { apply (proj2 (PallasGeneratorsOrder.value_commit_r_order_eq (r' - r))).
        apply (proj1 (Z.mod_divide (r' - r) pallas_q ltac:(clear -Hq2; lia))).
        exact Hd0. }
      rewrite HR0 in Hcol.
      apply PallasGeneratorsOrder.value_commit_v_order_eq in Hcol.
      apply (proj2 (Z.cong_iff_0 v v' pallas_q)).
      apply (proj2 (Z.mod_divide (v - v') pallas_q ltac:(clear -Hq2; lia))).
      exact Hcol. }
    (* The inverse of [r' - r] modulo the prime group order. *)
    assert (Hinv :
        (mod_inverse (r' - r) pallas_q * (r' - r)) mod pallas_q = 1).
    { exact (mod_inverse_mul_prime (p := Primes.pallas_q) (r' - r) Hd). }
    pose proof value_commit_v_reduced as HrV.
    pose proof value_commit_v_on_curve as HoV.
    pose proof value_commit_r_reduced as HrR.
    pose proof value_commit_r_on_curve as HoR.
    unfold OrchardBundleSpec.dlog_relation, extracted_k.
    symmetry.
    (* Drop the outer reduction modulo [q] of the witness. *)
    transitivity
      (mul ((v - v') * mod_inverse (r' - r) pallas_q) value_commit_v_G).
    { apply (proj2 (PallasGeneratorsOrder.value_commit_v_mul_injective
        (((v - v') * mod_inverse (r' - r) pallas_q) mod pallas_q)
        ((v - v') * mod_inverse (r' - r) pallas_q))).
      apply Zmod_mod. }
    (* Move the inverse across the collapsed relation with [mul_mul]. *)
    transitivity
      (mul (mod_inverse (r' - r) pallas_q * (v - v')) value_commit_v_G).
    { f_equal. ring. }
    rewrite (mul_mul_p (mod_inverse (r' - r) pallas_q) (v - v')
               value_commit_v_G HrV HoV).
    rewrite Hcol.
    rewrite <- (mul_mul_p (mod_inverse (r' - r) pallas_q) (r' - r)
                  value_commit_r_G HrR HoR).
    transitivity (mul 1 value_commit_r_G).
    { apply (proj2 (PallasGeneratorsOrder.value_commit_r_mul_injective
        (mod_inverse (r' - r) pallas_q * (r' - r)) 1)).
      rewrite Z.mod_1_l by (clear -Hq2; lia).
      exact Hinv. }
    exact (mul_1_p value_commit_r_G).
  Qed.

  (** The reduction at the coordinate-record commitment
      [OrchardProtocolSpec.value_commit] (the form the homomorphic bundle
      collapse produces): both sides are [repr]s of on-curve points, so the
      collision descends to the point level and [two_openings_dlog]
      applies. *)
  Theorem value_commit_collision_dlog (v r v' r' : Z) :
    OrchardProtocolSpec.value_commit v r =
    OrchardProtocolSpec.value_commit v' r' ->
    v mod pallas_q <> v' mod pallas_q ->
    OrchardBundleSpec.dlog_relation (extracted_k v v' r r').
  Proof.
    intros Hvc Hv.
    pose proof value_commit_v_on_curve as HoV.
    pose proof value_commit_r_on_curve as HoR.
    assert (HoX : on_curve
        (add (mul v value_commit_v_G) (mul r value_commit_r_G))).
    { apply add_on_curve_p; apply mul_on_curve_p; assumption. }
    assert (HoX' : on_curve
        (add (mul v' value_commit_v_G) (mul r' value_commit_r_G))).
    { apply add_on_curve_p; apply mul_on_curve_p; assumption. }
    apply (two_openings_dlog v r v' r'); [| exact Hv].
    rewrite <- (PallasModel.unrepr_repr _ HoX).
    rewrite <- (PallasModel.unrepr_repr _ HoX').
    unfold OrchardProtocolSpec.value_commit in Hvc.
    rewrite Hvc.
    reflexivity.
  Qed.
End OrchardBindingReduction.
