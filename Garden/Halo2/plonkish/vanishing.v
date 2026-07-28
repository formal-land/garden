(** * The vanishing argument: the all-challenge quotient identity.

    The gate conjunct of the deployed verifier is a single polynomial
    identity: the gate polynomials are combined with powers of a challenge
    [y] ([plonk/vanishing/verifier.rs] folds [h_eval * y + v] over the
    gate expressions, so the first expression carries the highest power)
    and the prover exhibits a quotient [h] with
    [combined = h * (X^n - 1)].  This file proves the all-challenge
    reading of that identity equivalent to row-wise gate vanishing on the
    evaluation domain [H = <w>] of order [n = 2^s]:

      (forall y, exists h, sum_i y^i * E_i = h * (X^n - 1))
        <->  forall i, forall j < n, E_i (w^j) = 0.

    Soundness fixes a domain point, reads the combined evaluation as a
    polynomial in the challenge [y] whose coefficients are the gate
    evaluations, instantiates [y] at the first [length Es] field points,
    and applies the root bound ([Poly.zero_of_roots] — the Vandermonde
    argument; the gate count is far below [p]).  Completeness divides by
    the monic [X^n - 1] ([Poly.pdivmod_spec]) and kills the remainder by
    counting its roots over the repetition-free enumeration
    [Poly.w_pows].

    Both combination orders are covered: [combine] gives index [i] the
    power [y^i]; [combine_horner] is the verifier's left fold, related by
    list reversal ([combine_horner_rev]), and the equivalence is
    insensitive to the order ([vanishing_sound_horner]).  The statements
    are generic over the gate list; [vanishing_sound_rows] is the
    interpolation-bridge form, over polynomials agreeing with given row
    evaluations on [H].  The pinned Orchard instantiation
    ([PolyDomain.omega], [n = 2048]) is the assembly layer's job. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.plonkish.poly.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Vanishing.
Section WithPrime.
  Context {p : Z} `{Prime p}.

  Local Notation poly := Poly.t.
  Local Notation padd := (Poly.padd (p := p)).
  Local Notation pscale := (Poly.pscale (p := p)).
  Local Notation pmul := (Poly.pmul (p := p)).
  Local Notation peq := (Poly.peq (p := p)).
  Local Notation eval := (Poly.eval (p := p)).
  Local Notation pdeg := (Poly.pdeg (p := p)).
  Local Notation norm := (Poly.norm (p := p)).
  Local Notation coef := (Poly.coef (p := p)).
  Local Notation xn1 := (Poly.xn1 (p := p)).
  Local Notation NoDupP := (Poly.NoDupP (p := p)).

  (** ** The challenge combinations of a gate-polynomial list *)

  (** [combine y [E_0; ...; E_(m-1)]] is [sum_i y^i * E_i]: index [i]
      carries the power [y^i]. *)
  Fixpoint combine (y : Z) (Es : list poly) : poly :=
    match Es with
    | [] => []
    | E :: Es' => padd E (pscale y (combine y Es'))
    end.

  (** The verifier's fold [h_eval * y + v] over the expression list: the
      first gate polynomial carries the highest power of [y]. *)
  Definition combine_horner (y : Z) (Es : list poly) : poly :=
    List.fold_left (fun acc E => padd (pscale y acc) E) Es [].

  (** Evaluating the combination at [x] is evaluating, at the challenge
      [y], the polynomial whose coefficients are the gate evaluations at
      [x]. *)
  Lemma eval_combine (y : Z) (Es : list poly) (x : Z) :
    eval (combine y Es) x = eval (List.map (fun E => eval E x) Es) y.
  Proof.
    induction Es as [| E Es' IH]; [reflexivity |].
    cbn [combine List.map].
    rewrite Poly.eval_padd, Poly.eval_pscale.
    rewrite Zplus_mod_idemp_r, IH.
    reflexivity.
  Qed.

  (** ** Small auxiliary facts *)

  Lemma eval_zeros (l : list Z) (y : Z) :
    (forall a, List.In a l -> a = 0) -> eval l y = 0.
  Proof.
    induction l as [| a l' IH]; intros Hz; [reflexivity |].
    cbn [eval].
    rewrite (Hz a) by (left; reflexivity).
    rewrite IH by (intros b Hb; apply Hz; right; exact Hb).
    rewrite Z.mul_0_r, Z.add_0_r. apply Zmod_0_l.
  Qed.

  Lemma pdeg_le_length (f : poly) : (pdeg f <= List.length f)%nat.
  Proof.
    apply Poly.pdeg_le_of_coef. intros i Hi.
    apply Poly.coef_ge. exact Hi.
  Qed.

  (** ** The Vandermonde step

      A combination vanishing at [x] for every challenge [y] forces every
      gate evaluation at [x] to vanish: the gate evaluations are the
      coefficients of a polynomial in [y] with more roots (all of
      [0 .. length Es - 1], distinct mod [p]) than significant
      coefficients. *)
  Lemma combine_all_y_zero (Es : list poly) (x : Z) :
    Z.of_nat (List.length Es) <= p ->
    (forall y, eval (combine y Es) x = 0) ->
    forall i, (i < List.length Es)%nat -> eval (List.nth i Es []) x = 0.
  Proof.
    intros Hm Hall i Hi.
    set (A := List.map (fun E => eval E x) Es).
    assert (HA : forall y, eval A y = 0).
    { intros y. unfold A. rewrite <- eval_combine. apply Hall. }
    assert (Hnil : norm A = []).
    { apply (Poly.zero_of_roots (p := p) A
               (List.map Z.of_nat (List.seq 0 (List.length Es)))).
      - apply (Poly.NoDupP_of_nat_seq (p := p)). exact Hm.
      - rewrite List.Forall_forall. intros y _. apply HA.
      - rewrite List.length_map, List.length_seq.
        eapply Nat.le_trans; [apply pdeg_le_length |].
        unfold A. rewrite List.length_map. reflexivity. }
    pose proof (Poly.norm_nil_coef (p := p) A Hnil i) as Hc.
    unfold Poly.coef in Hc.
    assert (Hnth : List.nth i A 0 = eval (List.nth i Es []) x).
    { unfold A. exact (List.map_nth (fun E => eval E x) Es [] i). }
    rewrite Hnth in Hc.
    rewrite Poly.eval_canonical in Hc.
    exact Hc.
  Qed.

  (** ** Order insensitivity of the combination *)

  Lemma pscale_compat (c : Z) (f g : poly) :
    peq f g -> peq (pscale c f) (pscale c g).
  Proof.
    rewrite !Poly.peq_iff_coef. intros Hc i.
    rewrite !Poly.coef_pscale, Hc. reflexivity.
  Qed.

  (** The verifier's left fold is the [y^i]-combination of the reversed
      list. *)
  Lemma combine_horner_rev (y : Z) (Es : list poly) :
    peq (combine_horner y Es) (combine y (List.rev Es)).
  Proof.
    induction Es as [| E Es' IH] using List.rev_ind.
    - apply Poly.peq_refl.
    - unfold combine_horner.
      rewrite List.fold_left_app. cbn [List.fold_left].
      rewrite List.rev_app_distr. cbn [List.rev List.app combine].
      eapply Poly.peq_trans; [apply Poly.padd_comm |].
      apply Poly.padd_compat; [apply Poly.peq_refl |].
      apply pscale_compat. exact IH.
  Qed.

  (** ** The equivalence, over a primitive [2^s]-th root of unity *)

  Section WithRoot.
    Variable w : Z.
    Variable s : nat.
    Hypothesis Hs : (1 <= s)%nat.
    Hypothesis Hp2 : 2 < p.
    Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
    Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).

    Lemma domain_point_in (j : nat) :
      (j < 2 ^ s)%nat -> List.In (Fpow w (Z.of_nat j)) (Poly.w_pows (p := p) w s).
    Proof.
      intros Hj.
      rewrite <- (Poly.w_pows_nth (p := p) w s Hs j Hj).
      apply List.nth_In.
      rewrite Poly.w_pows_length. exact Hj.
    Qed.

    Lemma xn1_domain_root (j : nat) :
      (j < 2 ^ s)%nat -> eval (xn1 (2 ^ s)%nat) (Fpow w (Z.of_nat j)) = 0.
    Proof.
      intros Hj.
      apply (Poly.w_pows_root (p := p) w s Hs Hp2 Hw_full).
      apply domain_point_in. exact Hj.
    Qed.

    (** The headline equivalence: the quotient identity for every
        challenge [y] holds exactly when every gate polynomial vanishes
        at every domain point.  The count hypothesis is the Vandermonde
        room: at most [p] gate polynomials (the concrete Orchard gate
        count is a few hundred against [p ~ 2^254]). *)
    Theorem vanishing_sound (Es : list poly)
      (Hcount : Z.of_nat (List.length Es) <= p) :
      (forall y, exists h, peq (combine y Es) (pmul h (xn1 (2 ^ s)%nat)))
      <->
      (forall i, (i < List.length Es)%nat ->
       forall j, (j < 2 ^ s)%nat ->
       eval (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0).
    Proof.
      split.
      - (* Soundness: instantiate the challenge, then count roots. *)
        intros Hdiv i Hi j Hj.
        apply (combine_all_y_zero Es (Fpow w (Z.of_nat j)) Hcount);
          [| exact Hi].
        intros y.
        destruct (Hdiv y) as [h Hh].
        rewrite (Poly.eval_peq _ _ _ Hh).
        rewrite Poly.eval_pmul.
        rewrite (xn1_domain_root j Hj).
        rewrite Z.mul_0_r. apply Zmod_0_l.
      - (* Completeness: divide by the monic [X^n - 1]; the remainder
           has [2^s] distinct roots and degree at most [2^s]. *)
        intros Hvan y.
        assert (H2s : (2 ^ s <> 0)%nat) by (apply Nat.pow_nonzero; lia).
        assert (Hn1 : (1 <= 2 ^ s)%nat) by lia.
        pose proof (Poly.xn1_monic (p := p) (2 ^ s)%nat Hn1) as Hmonic.
        destruct (Poly.pdivmod_spec (p := p)
                    (combine y Es) (xn1 (2 ^ s)%nat) Hmonic) as [Heq Hdeg].
        exists (Poly.pdiv (p := p) (combine y Es) (xn1 (2 ^ s)%nat)).
        assert (Hzero : forall x, List.In x (Poly.w_pows (p := p) w s) ->
                  eval (combine y Es) x = 0).
        { intros x Hx.
          rewrite eval_combine.
          apply eval_zeros.
          intros a Ha.
          apply List.in_map_iff in Ha.
          destruct Ha as [E [HE HEin]].
          destruct (List.In_nth Es E [] HEin) as [i [Hi Hia]].
          destruct (Poly.w_pows_in_char (p := p) w s Hs x Hx) as [j [Hj Hxj]].
          rewrite <- HE, <- Hia, Hxj.
          apply Hvan; assumption. }
        assert (Hrnil : norm (Poly.pmod (p := p)
                                (combine y Es) (xn1 (2 ^ s)%nat)) = []).
        { apply (Poly.zero_of_roots (p := p) _ (Poly.w_pows (p := p) w s)).
          - exact (Poly.w_pows_NoDupP (p := p) w s Hs Hp2 Hw_full Hw_half).
          - rewrite List.Forall_forall. intros x Hx.
            pose proof (Poly.eval_peq _ _ x Heq) as He.
            rewrite (Hzero x Hx) in He.
            rewrite Poly.eval_padd, Poly.eval_pmul in He.
            rewrite (Poly.w_pows_root (p := p) w s Hs Hp2 Hw_full x Hx) in He.
            rewrite Z.mul_0_r, Zmod_0_l, Z.add_0_l in He.
            rewrite Poly.eval_canonical in He.
            symmetry. exact He.
          - rewrite (Poly.xn1_pdeg (p := p) (2 ^ s)%nat Hn1) in Hdeg.
            rewrite Poly.w_pows_length. lia. }
        eapply Poly.peq_trans; [exact Heq |].
        apply Poly.padd_zero_r. exact Hrnil.
    Qed.

    (** The same equivalence with the gate side as a [Forall]. *)
    Corollary vanishing_sound_forall (Es : list poly)
      (Hcount : Z.of_nat (List.length Es) <= p) :
      (forall y, exists h, peq (combine y Es) (pmul h (xn1 (2 ^ s)%nat)))
      <->
      List.Forall
        (fun E => forall j, (j < 2 ^ s)%nat ->
           eval E (Fpow w (Z.of_nat j)) = 0) Es.
    Proof.
      pose proof (vanishing_sound Es Hcount) as Hbase.
      split.
      - intros Hdiv.
        apply List.Forall_forall. intros E HE j Hj.
        destruct (List.In_nth Es E [] HE) as [i [Hi HiE]].
        rewrite <- HiE.
        exact (proj1 Hbase Hdiv i Hi j Hj).
      - intros HF.
        apply Hbase. intros i Hi j Hj.
        rewrite List.Forall_forall in HF.
        apply HF; [| exact Hj].
        apply List.nth_In. exact Hi.
    Qed.

    (** The verifier's combination order: the left fold [h_eval * y + v]
        (the first gate polynomial carries the highest power of [y])
        satisfies the same equivalence — vanishing on [H] is insensitive
        to which power of [y] tags which polynomial. *)
    Theorem vanishing_sound_horner (Es : list poly)
      (Hcount : Z.of_nat (List.length Es) <= p) :
      (forall y, exists h, peq (combine_horner y Es) (pmul h (xn1 (2 ^ s)%nat)))
      <->
      (forall i, (i < List.length Es)%nat ->
       forall j, (j < 2 ^ s)%nat ->
       eval (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0).
    Proof.
      assert (Hrev : Z.of_nat (List.length (List.rev Es)) <= p)
        by (rewrite List.length_rev; exact Hcount).
      pose proof (vanishing_sound (List.rev Es) Hrev) as Hbase.
      split.
      - intros Hdiv i Hi j Hj.
        assert (Hdiv' : forall y, exists h,
                   peq (combine y (List.rev Es)) (pmul h (xn1 (2 ^ s)%nat))).
        { intros y. destruct (Hdiv y) as [h Hh]. exists h.
          eapply Poly.peq_trans;
            [apply Poly.peq_sym; apply combine_horner_rev | exact Hh]. }
        assert (Hin : List.In (List.nth i Es []) (List.rev Es))
          by (apply -> List.in_rev; apply List.nth_In; exact Hi).
        destruct (List.In_nth (List.rev Es) (List.nth i Es []) [] Hin)
          as [i' [Hi' Hnth]].
        rewrite <- Hnth.
        exact (proj1 Hbase Hdiv' i' Hi' j Hj).
      - intros Hvan y.
        assert (Hvan' : forall i, (i < List.length (List.rev Es))%nat ->
                  forall j, (j < 2 ^ s)%nat ->
                  eval (List.nth i (List.rev Es) []) (Fpow w (Z.of_nat j)) = 0).
        { intros i Hi j Hj.
          assert (Hin : List.In (List.nth i (List.rev Es) []) Es)
            by (apply <- List.in_rev; apply List.nth_In; exact Hi).
          destruct (List.In_nth Es (List.nth i (List.rev Es) []) [] Hin)
            as [i0 [Hi0 Hnth0]].
          rewrite <- Hnth0.
          apply Hvan; assumption. }
        destruct (proj2 Hbase Hvan' y) as [h Hh]. exists h.
        eapply Poly.peq_trans; [apply combine_horner_rev | exact Hh].
    Qed.

    (** The interpolation-bridge form: for gate polynomials agreeing with
        given row evaluations on [H] (e.g. the Lagrange interpolants of
        the compiled-gate row evaluations, [Poly.lagrange_eval]), the
        all-challenge quotient identity says exactly that every row
        evaluation vanishes. *)
    Corollary vanishing_sound_rows (Es : list poly) (rowv : nat -> nat -> Z)
      (Hcount : Z.of_nat (List.length Es) <= p)
      (Hagree : forall i, (i < List.length Es)%nat ->
        forall j, (j < 2 ^ s)%nat ->
        eval (List.nth i Es []) (Fpow w (Z.of_nat j)) = rowv i j mod p) :
      (forall y, exists h, peq (combine y Es) (pmul h (xn1 (2 ^ s)%nat)))
      <->
      (forall i, (i < List.length Es)%nat ->
       forall j, (j < 2 ^ s)%nat -> rowv i j mod p = 0).
    Proof.
      rewrite (vanishing_sound Es Hcount).
      split; intros Hz i Hi j Hj.
      - rewrite <- (Hagree i Hi j Hj). exact (Hz i Hi j Hj).
      - rewrite (Hagree i Hi j Hj). exact (Hz i Hi j Hj).
    Qed.

  End WithRoot.

End WithPrime.
End Vanishing.
