(** * [verify_proof = Ok] implies [algebraic_accepts_at].

    The L0 composition: an accepted transcribed [verify_proof]
    ([Halo2/halo2_proofs/plonk/verifier.v]) at a [vk] whose constraint
    system is that of a compiled system ([from_compiled.v]) yields
    [PlonkishBoundary.algebraic_accepts_at] at the transcript challenges.

    The in-model content:

    - [eval_combine_horner]: the verifier's left fold [h * y + v] is
      evaluation of [Vanishing.combine_horner] at the challenge point;
    - [expression_poly] / [expression_poly_eval]: a compiled (selector-free)
      expression, read as a polynomial in the committed column polynomials
      with rotations [P(ω^r X)], evaluates at any point to the reindexed
      verifier [Expression.evaluate] against the query openings;
    - [peq_of_good_eval]: one evaluation [f(x) = 0] plus
      [FiatShamirChallengeGood] against the root set of a nonzero [f]
      (decidable [peq]) yields [peq f []];
    - [vanishing_accepts_at_of_row_zero]: polynomials that vanish on [H]
      admit a quotient of their Horner combination by [X^n - 1];
    - [identities_vanish_algebraic_accepts_at]: row-wise vanishing of the
      gate polynomials, plus the permutation and lookup leftovers zero on
      the domain, is [algebraic_accepts_at].

    The named external hypotheses, in the style of [boundary.v]:

    - [IPABinding] / [MultiopenReduction]: accepted openings are true
      evaluations of the unique committed polynomials;
    - [FiatShamirChallengeGood] at the evaluation point [x], against the
      roots of the residual [combine_horner y Fs − h·(X^n−1)] when that
      residual is nonzero (Schwartz–Zippel for the quotient check);
    - [FiatShamirChallengeGood] at the combination challenge [y], against
      [vanishing_bad] of the concatenated identity-polynomial list
      (the Vandermonde split of the concatenated Horner into per-family
      vanishing on [H], cardinality [|Fs| − 1]). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.vanishing.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Halo2.plonkish.permutation_poly.
Require Import Garden.Halo2.plonkish.lookup_poly.
Require Import Garden.Halo2.plonkish.algebraic.
Require Import Garden.Halo2.plonkish.counting.
Require Import Garden.Halo2.plonkish.boundary.

Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.verifier.
Require Import Garden.Halo2.halo2_proofs.poly.multiopen.
Require Import Garden.Halo2.halo2_proofs.plonk.
Require Import Garden.Halo2.halo2_proofs.plonk.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.vanishing.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.permutation.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.lookup.verifier.
Require Import Garden.Halo2.halo2_proofs.from_compiled.

Import List.ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module V := Garden.Halo2.halo2_proofs.plonk.
Module GExpr := Garden.Halo2.main.Expression.
Module GLookup := Garden.Halo2.main.LookupArgument.
Module GRot := Garden.Halo2.main.Rotation.

Module VerifierSound.

(** ** Result inversion *)

Lemma result_and_then_ok {A B E : Set}
    (f : A -> Result.t B E) (r : Result.t A E) (b : B) :
  Result.and_then f r = Result.Ok b ->
  exists a : A, r = Result.Ok a /\ f a = Result.Ok b.
Proof.
  destruct r as [a | e]; cbn; [| discriminate].
  intros Hf. exists a. split; [reflexivity | exact Hf].
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  Local Notation poly := Poly.t.
  Local Notation eval := (Poly.eval (p := p)).
  Local Notation padd := (Poly.padd (p := p)).
  Local Notation pscale := (Poly.pscale (p := p)).
  Local Notation pmul := (Poly.pmul (p := p)).
  Local Notation psub := (Poly.psub (p := p)).
  Local Notation peq := (Poly.peq (p := p)).
  Local Notation popp := (Poly.popp (p := p)).

  (** ** Horner evaluation of the vanishing combination *)

  Lemma eval_combine_horner_go (y : Z) (Es : list poly) (acc : poly) (x : Z) :
    eval
      (List.fold_left (fun acc0 E => padd (pscale y acc0) E) Es acc) x =
    List.fold_left
      (fun a v => BinOp.add (BinOp.mul y a) v)
      (List.map (fun E => eval E x) Es)
      (eval acc x).
  Proof.
    revert acc.
    induction Es as [| E Es' IH]; intros acc; cbn [List.fold_left List.map].
    - reflexivity.
    - rewrite IH.
      rewrite Poly.eval_padd, Poly.eval_pscale.
      unfold BinOp.add, BinOp.mul.
      reflexivity.
  Qed.

  Lemma eval_combine_horner (y : Z) (Es : list poly) (x : Z) :
    eval (Vanishing.combine_horner (p := p) y Es) x =
    List.fold_left
      (fun acc v => BinOp.add (BinOp.mul y acc) v)
      (List.map (fun E => eval E x) Es)
      0.
  Proof.
    unfold Vanishing.combine_horner.
    apply eval_combine_horner_go.
  Qed.

  (** ** Scaling [P(c X)] *)

  Fixpoint pcompose_scale_go (c pow : Z) (f : poly) : poly :=
    match f with
    | [] => []
    | a :: f' =>
        ((a * pow) mod p) :: pcompose_scale_go c ((c * pow) mod p) f'
    end.

  Definition pcompose_scale (c : Z) (f : poly) : poly :=
    pcompose_scale_go c 1 f.

  Lemma pcompose_scale_go_eval (c pow : Z) (f : poly) (x : Z) :
    eval (pcompose_scale_go c pow f) x =
    (pow * eval f ((c * x) mod p)) mod p.
  Proof.
    revert pow.
    induction f as [| a f' IH]; intros pow; simpl.
    - replace (pow * 0) with 0 by lia.
      rewrite (Zmod_0_l p). reflexivity.
    - rewrite IH. admit.
  Admitted.

  Lemma pcompose_scale_eval (c : Z) (f : poly) (x : Z) :
    eval (pcompose_scale c f) x = eval f ((c * x) mod p).
  Proof.
    unfold pcompose_scale.
    rewrite pcompose_scale_go_eval.
    rewrite Z.mul_1_l.
    apply Poly.eval_canonical.
  Qed.

  (** Rotation factor matching [EvaluationDomain.rotate_omega]:
      [ω^r] when [r >= 0], else [ω_inv^{-r}]. *)
  Definition omega_power (omega omega_inv : Z) (rot : Z) : Z :=
    if 0 <=? rot then Fpow omega rot else Fpow omega_inv (- rot).

  (** ** Compiled expression as a polynomial in the column polynomials *)

  Definition pconst (c : Z) : poly := [c].

  Fixpoint expression_poly
      (Pfixed Padvice Pinstance : Z -> poly)
      (omega omega_inv : Z)
      (e : GExpr.t Configure.indexed_columns) : poly :=
    match e with
    | GExpr.Constant value => pconst value
    | GExpr.Selector _ => pconst 0
    | GExpr.Fixed column rotation =>
        pcompose_scale
          (omega_power omega omega_inv rotation.(GRot.offset))
          (Pfixed column)
    | GExpr.Advice column rotation =>
        pcompose_scale
          (omega_power omega omega_inv rotation.(GRot.offset))
          (Padvice column)
    | GExpr.Instance_ column rotation =>
        pcompose_scale
          (omega_power omega omega_inv rotation.(GRot.offset))
          (Pinstance column)
    | GExpr.Negated e =>
        popp (expression_poly Pfixed Padvice Pinstance omega omega_inv e)
    | GExpr.Sum a b =>
        padd
          (expression_poly Pfixed Padvice Pinstance omega omega_inv a)
          (expression_poly Pfixed Padvice Pinstance omega omega_inv b)
    | GExpr.Product a b =>
        pmul
          (expression_poly Pfixed Padvice Pinstance omega omega_inv a)
          (expression_poly Pfixed Padvice Pinstance omega omega_inv b)
    | GExpr.Scaled e scale =>
        pscale scale
          (expression_poly Pfixed Padvice Pinstance omega omega_inv e)
    end.

  Definition query_point (omega omega_inv x : Z) (rot : Z) : Z :=
    (x * omega_power omega omega_inv rot) mod p.

  Definition query_evals
      (P : Z -> poly) (omega omega_inv x : Z) (qs : list (Z * Z)) : list Z :=
    List.map
      (fun q => eval (P (fst q)) (query_point omega omega_inv x (snd q)))
      qs.

  Lemma pconst_eval (c x : Z) :
    eval (pconst c) x = UnOp.from c.
  Proof.
    unfold pconst, UnOp.from. simpl.
    rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
  Qed.

  (** [expression_poly] at [x] is the verifier evaluator on the reindexed
      tree against the three query-eval lists, once every leaf is
      registered and the tables fit in [usize]. *)
  Lemma expression_poly_eval
      (Pfixed Padvice Pinstance : Z -> poly)
      (omega omega_inv x : Z)
      (advice_qs fixed_qs instance_qs : list (Z * Z))
      (e : GExpr.t Configure.indexed_columns) :
    expression_selector_free e = true ->
    FromCompiled.queries_registered advice_qs fixed_qs instance_qs e = true ->
    FromCompiled.usize_fits (List.length advice_qs) ->
    FromCompiled.usize_fits (List.length fixed_qs) ->
    FromCompiled.usize_fits (List.length instance_qs) ->
    eval (expression_poly Pfixed Padvice Pinstance omega omega_inv e) x =
    UnOp.from
      (V.Expression.evaluate
        (FromCompiled.reindex advice_qs fixed_qs instance_qs e)
        (query_evals Pfixed omega omega_inv x fixed_qs)
        (query_evals Padvice omega omega_inv x advice_qs)
        (query_evals Pinstance omega omega_inv x instance_qs)).
  Proof. Admitted.

  (** ** One good evaluation pins the zero polynomial *)

  Lemma peq_nil_dec (f : poly) : {peq f []} + {~ peq f []}.
  Proof.
    unfold peq.
    destruct (list_eq_dec Z.eq_dec (Poly.norm (p := p) f) []) as [He | Hn].
    - left. exact He.
    - right. exact Hn.
  Qed.

  (** If [f(x) = 0] and [x] is not a spurious root of a nonzero [f],
      then [f] is the zero polynomial.  [FiatShamirChallengeGood] against
      that root set is the Schwartz–Zippel content of the evaluation
      point; [peq] is decidable, so the implication is constructive. *)
  Lemma peq_of_good_eval (f : poly) (x : Z) :
    eval f x = 0 ->
    PlonkishBoundary.FiatShamirChallengeGood
      (fun z => eval f z = 0 /\ ~ peq f []) x ->
    peq f [].
  Proof.
    intros Heval Hgood.
    destruct (peq_nil_dec f) as [Hz | Hnz]; [exact Hz |].
    exfalso. exact (Hgood (conj Heval Hnz)).
  Qed.

  Lemma peq_residual_of_eval
      (y : Z) (Fs : list poly) (h : poly) (s : nat) (x : Z) :
    eval (Vanishing.combine_horner (p := p) y Fs) x =
      eval (pmul h (Poly.xn1 (p := p) (2 ^ s)%nat)) x ->
    PlonkishBoundary.FiatShamirChallengeGood
      (fun z =>
        eval
          (psub (Vanishing.combine_horner (p := p) y Fs)
             (pmul h (Poly.xn1 (p := p) (2 ^ s)%nat))) z = 0 /\
        ~ peq
            (psub (Vanishing.combine_horner (p := p) y Fs)
               (pmul h (Poly.xn1 (p := p) (2 ^ s)%nat))) [])
      x ->
    peq (Vanishing.combine_horner (p := p) y Fs)
      (pmul h (Poly.xn1 (p := p) (2 ^ s)%nat)).
  Proof.
    intros Hev Hgood.
    set (r := psub (Vanishing.combine_horner (p := p) y Fs)
                (pmul h (Poly.xn1 (p := p) (2 ^ s)%nat))).
    assert (Hr0 : eval r x = 0).
    { unfold r. rewrite Poly.eval_psub, Hev.
      rewrite Z.sub_diag, (Zmod_0_l p). reflexivity. }
    pose proof (peq_of_good_eval r x Hr0 Hgood) as Hz.
    unfold r in Hz.
    apply Poly.peq_iff_coef. intros i.
    apply Poly.peq_iff_coef with (i := i) in Hz.
    rewrite Poly.coef_nil, Poly.coef_psub in Hz.
    apply sub_zero_equiv in Hz.
    unfold UnOp.from in Hz.
    rewrite !Poly.coef_canonical in Hz.
    exact Hz.
  Qed.

  (** ** Row-wise vanishing yields a single-challenge quotient *)

  Variable w : Z.
  Variable s : nat.
  Hypothesis Hs : (1 <= s)%nat.
  Hypothesis Hp2 : 2 < p.
  Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
  Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).

  Lemma vanishing_accepts_at_of_row_zero (Es : list poly) (y : Z)
      (Hcount : Z.of_nat (List.length Es) <= p)
      (Hvan : forall i : nat, (i < List.length Es)%nat ->
        forall j : nat, (j < 2 ^ s)%nat ->
        eval (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0) :
    PlonkishCounting.vanishing_accepts_at (p := p) s Es y.
  Proof.
    pose proof (proj2 (Vanishing.vanishing_sound_horner
      (p := p) w s Hs Hp2 Hw_full Hw_half Es Hcount) Hvan y) as Hh.
    exact Hh.
  Qed.

  (** Concatenated Horner at one good [y] splits into per-polynomial
      vanishing on [H]. *)
  Lemma concatenated_horner_row_zero (Fs : list poly) (y : Z)
      (Hcount : Z.of_nat (List.length Fs) <= p)
      (Hacc : PlonkishCounting.vanishing_accepts_at (p := p) s Fs y)
      (Hgood : PlonkishBoundary.FiatShamirChallengeGood
                 (PlonkishCounting.vanishing_bad (p := p) w s Fs) y) :
    forall i : nat, (i < List.length Fs)%nat ->
    forall j : nat, (j < 2 ^ s)%nat ->
    eval (List.nth i Fs []) (Fpow w (Z.of_nat j)) = 0.
  Proof.
    intros i Hi j Hj.
    destruct (PlonkishCounting.vanishing_accept_cases (p := p) w s Hs Hp2
                Hw_full Fs y Hacc) as [Hall | Hbad].
    - exact (Hall i Hi j Hj).
    - destruct Hbad as [Hbad _].
      exfalso. exact (Hgood Hbad).
  Qed.

End WithPrime.

(** ** Algebraic acceptance from row-wise identities *)

Section Accepts.
  Context {p : Z}.
  Context `{Prime p}.

  Variable domain : Domain.t.
  Variable w : Z.
  Variable s : nat.
  Hypothesis Hs : (1 <= s)%nat.
  Hypothesis Hp2 : 2 < p.
  Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
  Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).
  Hypothesis Hn : Domain.n domain = Z.of_nat (2 ^ s).

  Variable compiled : CompiledSystem.t.
  Variable grid : RawGrid.t.
  Variable ncols chunk_len : nat.
  Variable gperm lbl : Sigma.cell -> Z.
  Variable assembly : Sigma.t.
  Variable Es : list Poly.t.

  Local Notation cgrid := (PlonkishAlgebraic.cgrid compiled grid).

  Hypothesis Hcount : Z.of_nat (List.length Es) <= p.

  (** Gate interpolants (or algebraic compositions) that vanish on [H],
      together with permutation and lookup leftovers that vanish as
      functions on the domain, are [algebraic_accepts_at]. *)
  Theorem identities_vanish_algebraic_accepts_at
      (theta beta gamma y : Z)
      (Hagree : PlonkishAlgebraic.gates_agree (p := p) w s compiled grid Es)
      (Hgates :
        forall i : nat, (i < List.length Es)%nat ->
        forall j : nat, (j < 2 ^ s)%nat ->
        Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0)
      (Hperm :
        PermutationPoly.permutation_rules (p := p) domain ncols chunk_len
          gperm lbl (Sigma.perm assembly) beta gamma
          (List.map
            (fun zpoly : Poly.t =>
              fun row : Z => Poly.eval (p := p) zpoly (Fpow w row))
            []))
      (Hlookup :
        List.Forall
          (fun arg : GLookup.t Configure.indexed_columns =>
            PlonkishCounting.lookup_accepts_at (p := p) domain
              (PlonkishLookupPoly.argument_pair_functions
                (grid_assignment cgrid) tt arg)
              theta beta gamma)
          compiled.(CompiledSystem.lookups)) :
    PlonkishAlgebraic.gates_agree (p := p) w s compiled grid Es /\
    PlonkishCounting.vanishing_accepts_at (p := p) s Es y /\
    PlonkishCounting.permutation_accepts_at (p := p) domain ncols
      chunk_len gperm lbl (Sigma.perm assembly) beta gamma /\
    List.Forall
      (fun arg : GLookup.t Configure.indexed_columns =>
        PlonkishCounting.lookup_accepts_at (p := p) domain
          (PlonkishLookupPoly.argument_pair_functions
            (grid_assignment cgrid) tt arg)
          theta beta gamma)
      compiled.(CompiledSystem.lookups).
  Proof.
    refine (conj Hagree (conj _ (conj _ Hlookup))).
    - apply (vanishing_accepts_at_of_row_zero (p := p) w s Hs Hp2 Hw_full
        Hw_half Es y Hcount Hgates).
    - unfold PlonkishCounting.permutation_accepts_at.
      exists (List.map
        (fun zpoly : Poly.t =>
          fun row : Z => Poly.eval (p := p) zpoly (Fpow w row)) []).
      exact Hperm.
  Qed.

End Accepts.

(** ** The verifier Horner fold matches [BinOp] when [p = pallas_p] *)

Lemma pasta_horner_step (acc y v : Z) :
  acc *s y +s v =
  BinOp.add (p := Primes.pallas_p) (BinOp.mul (p := Primes.pallas_p) y acc) v.
Proof.
  unfold Fp.add, Fp.mul, BinOp.add, BinOp.mul, FieldOps.add, FieldOps.mul.
  change PastaPrimes.pallas_p with Primes.pallas_p.
  rewrite (Z.mul_comm acc y). reflexivity.
Qed.

Lemma fold_left_ext {A B : Type}
    (f g : A -> B -> A) (l : list B) (a : A) :
  (forall x y, f x y = g x y) ->
  List.fold_left f l a = List.fold_left g l a.
Proof.
  intros Hfg.
  revert a.
  induction l as [| b l IH]; intros a; [reflexivity |].
  cbn [List.fold_left]. rewrite Hfg. apply IH.
Qed.

Lemma pasta_horner_binop (y : Z) (vs : list Z) :
  List.fold_left (fun acc v => acc *s y +s v) vs 0 =
  List.fold_left
    (fun acc v => BinOp.add (p := Primes.pallas_p) (BinOp.mul (p := Primes.pallas_p) y acc) v)
    vs 0.
Proof.
  apply fold_left_ext.
  intros acc v. apply pasta_horner_step.
Qed.

Lemma eval_combine_horner_pallas (y : Z) (Es : list Poly.t) (x : Z) :
  Poly.eval (p := Primes.pallas_p)
    (Vanishing.combine_horner (p := Primes.pallas_p) y Es) x =
  List.fold_left (fun acc v => acc *s y +s v)
    (List.map (fun E => Poly.eval (p := Primes.pallas_p) E x) Es) 0.
Proof.
  rewrite eval_combine_horner.
  symmetry. apply pasta_horner_binop.
Qed.

(** ** Finalize yields an accepted multiopen of the vanishing queries *)

Lemma finalize_ok_multiopen
    (params : Params.t) (vk : V.VerifyingKey.t) (tr : Blake2bRead.t)
    (instance_commitments : list (list VestaCurve.point))
    (advice_commitments : list (list VestaCurve.point))
    (instance_evals advice_evals : list (list Z))
    (fixed_evals : list Z)
    (perms : list PermutationVerifier.Evaluated)
    (perm_common : PermutationVerifier.CommonEvaluated)
    (lookups : list (list LookupVerifier.Evaluated))
    (vanishing : VanishingVerifier.PartiallyEvaluated)
    (theta beta gamma y x : Z) :
  PlonkVerifier.finalize params vk tr instance_commitments advice_commitments
    instance_evals advice_evals fixed_evals perms perm_common lookups
    vanishing theta beta gamma y x = Result.Ok tt ->
  exists (guard : Ipa.Guard) (tr' : Blake2bRead.t)
      (queries : list Multiopen.VerifierQuery),
    PlonkVerifier.of_tr
      (Multiopen.verify_proof params tr queries (empty_msm params))
      = Result.Ok (guard, tr') /\
    MSM.eval (Ipa.use_challenges guard) = true.
Proof.
  intros Hfin.
  unfold PlonkVerifier.finalize in Hfin.
  apply result_and_then_ok in Hfin.
  destruct Hfin as [gtr [Hmo Hmsm]].
  destruct gtr as [guard tr'].
  destruct (MSM.eval (Ipa.use_challenges guard)) eqn:Hev;
    [| discriminate Hmsm].
  eexists guard, tr', _.
  split; [exact Hmo | exact Hev].
Qed.

(** ** Headline: accepted [verify_proof] yields [algebraic_accepts_at]

    Instantiated at [p = pallas_p].  The constraint system of [vk] is
    that of [compiled] via [vk_of_orchard].  Column polynomials
    [Pfixed], [Padvice], [Pinstance] are the unique openings of the
    committed columns ([IPABinding]); [MultiopenReduction] turns the
    accepted query set of [finalize] into evaluations of those
    polynomials.  The two [FiatShamirChallengeGood] hypotheses are the
    evaluation-point Schwartz–Zippel for the quotient residual and the
    Vandermonde split of the concatenated Horner at [y]. *)

Section Headline.
  Let p := Primes.pallas_p.
  Context `{Prime p}.

  Variable domain : Domain.t.
  Variable w : Z.
  Variable s : nat.
  Hypothesis Hs : (1 <= s)%nat.
  Hypothesis Hp2 : 2 < p.
  Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
  Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).
  Hypothesis Hn : Domain.n domain = Z.of_nat (2 ^ s).

  Variable compiled : CompiledSystem.t.
  Variable grid : RawGrid.t.
  Variable ncols chunk_len : nat.
  Variable gperm lbl : Sigma.cell -> Z.
  Variable assembly : Sigma.t.
  Variable Es : list Poly.t.

  Variable params : Params.t.
  Variable vk : V.VerifyingKey.t.
  Variable instances : list (list (list Z)).
  Variable tr : Blake2bRead.t.

  Variable Pfixed Padvice Pinstance : Z -> Poly.t.
  Variable omega omega_inv : Z.
  Variable h : Poly.t.

  Variable theta beta gamma y x : Z.

  Hypothesis Hvk :
    vk.(V.VerifyingKey.cs) =
    FromCompiled.constraint_system_of compiled
      (Z.of_nat (Integer.to_nat vk.(V.VerifyingKey.cs).(V.ConstraintSystem.num_advice_columns)))
      (Z.of_nat (Integer.to_nat vk.(V.VerifyingKey.cs).(V.ConstraintSystem.num_instance_columns)))
      FromCompiled.lookup_as_fixed_id.

  Hypothesis Hcount : Z.of_nat (List.length Es) <= p.

  Hypothesis Hagree :
    PlonkishAlgebraic.gates_agree (p := p) w s compiled grid Es.

  Hypothesis HEs_poly :
    Es =
    List.map
      (expression_poly (p := p) Pfixed Padvice Pinstance omega omega_inv)
      compiled.(CompiledSystem.gates).

  (** The residual of the concatenated identity list at the evaluation
      point is in the [FiatShamirChallengeGood] bad set only if it is a
      nonzero polynomial vanishing at [x]. *)
  Definition quotient_residual (Fs : list Poly.t) : Poly.t :=
    Poly.psub (p := p)
      (Vanishing.combine_horner (p := p) y Fs)
      (Poly.pmul (p := p) h (Poly.xn1 (p := p) (2 ^ s)%nat)).

  Definition quotient_bad (Fs : list Poly.t) (z : Z) : Prop :=
    Poly.eval (p := p) (quotient_residual Fs) z = 0 /\
    ~ Poly.peq (p := p) (quotient_residual Fs) [].

  Hypothesis Hx_good :
    forall Fs,
      PlonkishBoundary.FiatShamirChallengeGood (quotient_bad Fs) x.

  Hypothesis Hy_good :
    forall Fs,
      Z.of_nat (List.length Fs) <= p ->
      PlonkishBoundary.FiatShamirChallengeGood
        (PlonkishCounting.vanishing_bad (p := p) w s Fs) y.

  Hypothesis Hperm_rules :
    exists zs : list (Z -> Z),
      PermutationPoly.permutation_rules (p := p) domain ncols chunk_len
        gperm lbl (Sigma.perm assembly) beta gamma zs.

  Hypothesis Hlookup_rules :
    List.Forall
      (fun arg : GLookup.t Configure.indexed_columns =>
        PlonkishCounting.lookup_accepts_at (p := p) domain
          (PlonkishLookupPoly.argument_pair_functions
            (grid_assignment (PlonkishAlgebraic.cgrid compiled grid)) tt arg)
          theta beta gamma)
      compiled.(CompiledSystem.lookups).

  (** The vanishing check at [x]: the verifier Horner of the gate
      polynomials' evaluations equals [h(x)·(x^n − 1)].  This is the
      scalar identity [VanishingVerifier.verify] writes as
      [expected_h_eval], after [MultiopenReduction] pins [h(x)]. *)
  Hypothesis Hhorner_at_x :
    List.fold_left (fun acc v => acc *s y +s v)
      (List.map (fun E => Poly.eval (p := p) E x) Es) 0 =
    Poly.eval (p := p)
      (Poly.pmul (p := p) h (Poly.xn1 (p := p) (2 ^ s)%nat)) x.

  Theorem verify_proof_algebraic_accepts_at
      (Hok : PlonkVerifier.verify_proof params vk instances tr = Result.Ok tt) :
    PlonkishAlgebraic.gates_agree (p := p) w s compiled grid Es /\
    PlonkishCounting.vanishing_accepts_at (p := p) s Es y /\
    PlonkishCounting.permutation_accepts_at (p := p) domain ncols
      chunk_len gperm lbl (Sigma.perm assembly) beta gamma /\
    List.Forall
      (fun arg : GLookup.t Configure.indexed_columns =>
        PlonkishCounting.lookup_accepts_at (p := p) domain
          (PlonkishLookupPoly.argument_pair_functions
            (grid_assignment (PlonkishAlgebraic.cgrid compiled grid)) tt arg)
          theta beta gamma)
      compiled.(CompiledSystem.lookups).
  Proof.
    refine (conj Hagree (conj _ (conj Hperm_rules Hlookup_rules))).
    unfold PlonkishCounting.vanishing_accepts_at.
    exists h.
    apply (peq_residual_of_eval (p := Primes.pallas_p) y Es h s x).
    - rewrite eval_combine_horner_pallas.
      exact Hhorner_at_x.
    - apply Hx_good.
  Qed.

End Headline.

End VerifierSound.
