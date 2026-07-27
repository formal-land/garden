(** * Counting bound for reduced on-curve short-Weierstrass points

    A coordinate-wise injection of the reduced on-curve points of the generic
    short-Weierstrass curve ([Garden.EllipticCurve.Weierstrass]) into the
    integer interval [[0, 2*p + 1)]: an affine point [(x, y)] maps to
    [2*x + y_bit y], where [y_bit] records which half of [[0, p)] the reduced
    [y]-coordinate lies in, and the point at infinity maps to [2*p]. An
    affine [x]-coordinate carries at most two on-curve points — a [y] and its
    field negation ([Weierstrass.same_x_eq_or_neg]) — and, because [p] is
    odd, [y_bit] separates the two, so the code is injective
    ([point_code_inj]). The pigeonhole consequence [family_bound]: a
    [Z]-indexed family of reduced on-curve points that is injective on
    [[0, n)] forces [n <= 2*p + 1].

    All interval reasoning is over symbolic [List.seq] terms ([p] is an
    abstract prime); nothing of size [p] is ever computed, and the statements
    are [Z]-only so consumers never touch [nat]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.

Global Open Scope Z_scope.

Module GroupOrderCounting.

(** [map] preserves [NoDup] when the function is injective on the list. *)
Lemma NoDup_map_in {A B : Type} (g : A -> B) (l : list A) :
  (forall u v, In u l -> In v l -> g u = g v -> u = v) ->
  NoDup l ->
  NoDup (map g l).
Proof.
  induction l as [|x l IH]; intros Hinj Hnd.
  - constructor.
  - inversion Hnd as [|? ? Hnotin Hnd']; subst.
    cbn [map]. constructor.
    + intros Hin. apply in_map_iff in Hin.
      destruct Hin as (u & Hgu & Hu).
      apply Hnotin.
      replace x with u; [exact Hu|].
      apply Hinj; [right; exact Hu | left; reflexivity | exact Hgu].
    + apply IH; [|exact Hnd'].
      intros u v Hu Hv. apply Hinj; right; assumption.
Qed.

Section Counting.
  (** The abstract base field [Z/pZ], as in [Weierstrass.Curve]. *)
  Context {p : Z} `{Prime p}.

  (** The short-Weierstrass coefficients [y^2 = x^3 + a*x + b]. *)
  Variables (a b : Z).

  (** ** The point code

      Which half of [[0, p)] a reduced coordinate lies in: [0] on the lower
      half ([2*y < p]), [1] on the upper. For odd [p] and [0 < y < p], [y]
      and its field negation [p - y] land in different halves. *)
  Definition y_bit (y : Z) : Z := if 2 * y <? p then 0 else 1.

  (** The injection of points into [[0, 2*p + 1)]: an affine point
      contributes its (reduced) [x]-coordinate tagged with the [y] half-bit,
      the point at infinity takes the one remaining value [2*p]. *)
  Definition point_code (P : Weierstrass.point) : Z :=
    match P with
    | Weierstrass.Infinity => 2 * p
    | Weierstrass.Affine x y => 2 * x + y_bit y
    end.

  (** [p] is odd (a prime above [2]). *)
  Lemma p_odd : 2 < p -> p mod 2 = 1.
  Proof.
    intros Hp2.
    pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
    assert (H2 : ~ (2 | p)).
    { intro Hd. pose proof (Znumtheory.prime_divisors p Hp 2 Hd). lia. }
    assert (Hmod : p mod 2 <> 0).
    { intro Hc. apply H2. apply Z.mod_divide; [lia | exact Hc]. }
    pose proof (Z.mod_pos_bound p 2 ltac:(lia)). lia.
  Qed.

  (** A reduced coordinate lies in [[0, p)]. *)
  Lemma reduced_coord_range (x : Z) : UnOp.from x = x -> 0 <= x < p.
  Proof.
    intros Hx.
    pose proof (prime_range (p := p)).
    unfold UnOp.from in Hx. rewrite <- Hx.
    apply Z.mod_pos_bound. lia.
  Qed.

  (** ** The code is a map into [[0, 2*p + 1)] *)
  Lemma point_code_range (P : Weierstrass.point) :
    Weierstrass.reduced P ->
    Weierstrass.on_curve a b P ->
    0 <= point_code P < 2 * p + 1.
  Proof.
    intros Hr _.
    pose proof (prime_range (p := p)).
    destruct P as [|x y]; cbn [point_code].
    - lia.
    - destruct Hr as [Hx Hy].
      apply reduced_coord_range in Hx.
      unfold y_bit. destruct (2 * y <? p); lia.
  Qed.

  (** ** The code is injective on reduced on-curve points

      Equal codes force equal [x]-coordinates and equal half-bits; by
      [same_x_eq_or_neg] the points are equal or opposite, and in the
      opposite case [y2 = p - y1] with [y1 <> 0], which flips the half-bit
      because [p] is odd. *)
  Lemma point_code_inj (P Q : Weierstrass.point) :
    3 < p ->
    Weierstrass.reduced P ->
    Weierstrass.reduced Q ->
    Weierstrass.on_curve a b P ->
    Weierstrass.on_curve a b Q ->
    point_code P = point_code Q ->
    P = Q.
  Proof.
    intros H3p Hr1 Hr2 Ho1 Ho2 Hcode.
    destruct P as [|x1 y1]; destruct Q as [|x2 y2]; cbn [point_code] in Hcode.
    - reflexivity.
    - exfalso. destruct Hr2 as [Hx2 _]. apply reduced_coord_range in Hx2.
      unfold y_bit in Hcode. destruct (2 * y2 <? p); lia.
    - exfalso. destruct Hr1 as [Hx1 _]. apply reduced_coord_range in Hx1.
      unfold y_bit in Hcode. destruct (2 * y1 <? p); lia.
    - assert (Hbx1 : 0 <= x1 < p) by (apply reduced_coord_range, Hr1).
      assert (Hby1 : 0 <= y1 < p) by (apply reduced_coord_range, Hr1).
      assert (Hbx2 : 0 <= x2 < p) by (apply reduced_coord_range, Hr2).
      assert (Hby2 : 0 <= y2 < p) by (apply reduced_coord_range, Hr2).
      assert (Hb1 : y_bit y1 = 0 \/ y_bit y1 = 1)
        by (unfold y_bit; destruct (2 * y1 <? p); [left | right]; reflexivity).
      assert (Hb2 : y_bit y2 = 0 \/ y_bit y2 = 1)
        by (unfold y_bit; destruct (2 * y2 <? p); [left | right]; reflexivity).
      assert (Hx12 : x1 = x2) by lia.
      assert (Hbit : y_bit y1 = y_bit y2) by lia.
      subst x2.
      destruct (Weierstrass.same_x_eq_or_neg a b
                  (Weierstrass.Affine x1 y1) (Weierstrass.Affine x1 y2)
                  Hr1 Hr2 Ho1 Ho2 eq_refl) as [Heq | Hneg]; [exact Heq |].
      cbn [Weierstrass.neg] in Hneg.
      injection Hneg as Hyneg.
      unfold UnOp.opp in Hyneg.
      destruct (Z.eq_dec y2 0) as [Hz | Hz].
      + subst y2. rewrite Z.opp_0, Z.mod_0_l in Hyneg by lia.
        subst y1. reflexivity.
      + exfalso.
        assert (Hopp : (- y2) mod p = p - y2).
        { replace (- y2) with ((p - y2) + (-1) * p) by ring.
          rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
        rewrite Hopp in Hyneg.
        pose proof (p_odd ltac:(lia)) as Hoddp.
        pose proof (Z.div_mod p 2 ltac:(lia)) as Hdm.
        unfold y_bit in Hbit.
        clear -Hbit Hyneg Hby1 Hby2 Hz Hoddp Hdm.
        destruct (Z.ltb_spec (2 * y1) p); destruct (Z.ltb_spec (2 * y2) p); lia.
  Qed.

  (** ** The pigeonhole bound

      A family of reduced on-curve points indexed injectively by [[0, n)]
      has at most [2*p + 1] members: its codes are [n] pairwise-distinct
      integers inside [[0, 2*p + 1)]. The [List.seq] terms stay symbolic
      ([Z.to_nat] is never evaluated); the statement itself is [Z]-only. *)
  Lemma family_bound (n : Z) (f : Z -> Weierstrass.point) :
    3 < p ->
    (forall i, 0 <= i < n -> Weierstrass.reduced (f i)) ->
    (forall i, 0 <= i < n -> Weierstrass.on_curve a b (f i)) ->
    (forall i j, 0 <= i < n -> 0 <= j < n -> f i = f j -> i = j) ->
    n <= 2 * p + 1.
  Proof.
    intros H3p Hred Hoc Hinj.
    destruct (Z.le_gt_cases n 0) as [Hn0 | Hn0]; [lia |].
    assert (Hidx : forall k : nat,
               In k (seq 0 (Z.to_nat n)) -> 0 <= Z.of_nat k < n).
    { intros k Hk. apply in_seq in Hk. lia. }
    assert (Hnd : NoDup (map (fun k : nat => point_code (f (Z.of_nat k)))
                           (seq 0 (Z.to_nat n)))).
    { apply NoDup_map_in; [| apply seq_NoDup].
      intros u v Hu Hv Hg.
      apply Hidx in Hu. apply Hidx in Hv.
      apply Nat2Z.inj.
      apply (Hinj _ _ Hu Hv).
      exact (point_code_inj _ _ H3p
               (Hred _ Hu) (Hred _ Hv) (Hoc _ Hu) (Hoc _ Hv) Hg). }
    assert (Hincl : incl (map (fun k : nat => point_code (f (Z.of_nat k)))
                            (seq 0 (Z.to_nat n)))
                         (map Z.of_nat (seq 0 (Z.to_nat (2 * p + 1))))).
    { intros c Hc.
      apply in_map_iff in Hc. destruct Hc as (k & Hck & Hk).
      apply Hidx in Hk.
      assert (Hc' : 0 <= c < 2 * p + 1)
        by (rewrite <- Hck;
            exact (point_code_range _ (Hred _ Hk) (Hoc _ Hk))).
      replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
      apply in_map. apply in_seq. lia. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite !List.length_map, !List.length_seq in Hlen.
    lia.
  Qed.

End Counting.

End GroupOrderCounting.
