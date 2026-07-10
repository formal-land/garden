(** * Fixed-base windowed ladder distinctness

    Bridges the generic
    Weierstrass / Pallas elliptic-curve theory ([EllipticCurve/Weierstrass.v],
    [EllipticCurve/Pallas.v]) to the Orchard fixed-base ladder predicate
    [incomplete_additions_distinct_precondition]
    ([Garden/Orchard/circuit_proof/fixed_base/main.v]).  The windowed fixed-base
    multiplication folds per-window points through the incomplete-addition
    chip, whose soundness needs, at every step, that the next window point's
    x-coordinate differs from the running accumulator's.  This file proves the
    facts that discharge that ladder-distinctness precondition from the
    prime-order subgroup structure of the base point, PARAMETRICALLY in the
    base: the per-base developments (SpendAuthG here; ValueCommitR /
    NoteCommitR / NullifierK / ValueCommitV in their
    [circuit_proof/ladder/*.v] files) are instances of the shared
    sections below.

    The signed-radix-8 window-scalar encoding is defined here over an abstract
    window count [n] ([window_scalar], [partial_sum], [cumulative_scalar]),
    together with the [n]-generic numeric layer ([window_scalar_nonlast_gen],
    [window_scalar_last_gen], [partial_sum_window_bound],
    [window_scalar_range_bound], [partial_sum_split_1]) whose 85-window
    instances are [window_scalar_nonlast],
    [cumulative_scalar_bound], [spend_auth_g_window_scalar_range_bound], ....

    The per-base window-table-to-distinctness chain is factored into two
    parameterized sections over an abstract base point [G] (on-curve, reduced)
    and window count:
    - [PerBaseTable] ([last_entry_eq_gen], [full_table_entry_eq_mul_gen],
      [fixed_window_point_x_eq_mul_gen]): the octupling-chain window table
      ([FixedBaseTableDefs]) computes the abstract multiples
      [window_scalar n w d * G], and the Lagrange x-coordinate certificate
      (passed in as the [Hx_cert] hypothesis, discharged per base by the
      [vm_compute] certificate [<Base>FixedWindowCert.x_check_entry]) pins the
      spec table's x-coordinates to those multiples.
    - [PerBaseChain] ([full_window_correct_gen], [partial_sum_eq_mul_gen],
      [ladder_distinct_precondition_holds_gen]): from the per-window circuit
      facts (window equation, on-curve, discriminant certificate, positive
      QR certificate, x-coordinate agreement), every window point equals the
      [repr] of its Weierstrass multiple; folding them identifies the
      accumulator with the cumulative multiple ([partial_sum_eq_mul_gen]); and
      [incomplete_distinct_of_range_bounds] with the
      signed-radix-8 range bounds ([window_scalar_range_bound]) yields the
      full ladder-distinctness predicate over rows [1 .. count].

    The [vm_compute] certificate facts and the [Strategy] directives stay
    outside the sections; each instantiation site wraps its concrete-generator
    reasoning in the same opaque windows used here.

    SpendAuthG instances:
    - [spend_auth_g_fixed_window_point_eq_mul]: the per-window point equals
      the Weierstrass multiple (via the unconditional x half
      [spend_auth_g_fixed_window_point_x_eq_mul] and the witnessed y);
    - the table-entry bridge [full_table_entry_eq_mul];
    - [incomplete_distinct_of_range_bounds];
    - [spend_auth_g_distinct_holds]: the full 83-edge
      (rows 1..83) SpendAuthG ladder distinctness, from
      [spend_auth_g_full_window_correct] (the QR window-sign forcing pins each
      window to its canonical multiple).  Row 84 is the ladder's *complete*
      addition, deliberately outside the predicate (at the all-zeros scalar
      window 84 is the [Weierstrass.neg] of the rows-0..83 accumulator and
      shares its x).  The proved statements rest on the generic
      [Weierstrass] / [Pallas] interface. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.table.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.x_cert.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.disc_cert.
Require Import Garden.Orchard.circuit_proof.spend_auth_g.sign_cert.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the [circuit_holds] ([Holds]) hypotheses of the statements below
   are at [pallas_p], matching the Orchard proof side (every other EC and
   Orchard file sets this).  Without it the implicit field prime defaults to
   [goldilocks] and the [Holds] hypotheses would be incompatible with the
   Orchard [pallas_p] assignments. *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module FixedBaseLadder.
  (** ** Signed-radix-8 window-scalar encoding

      The Halo2 fixed-base multiplication decomposes a scalar into [n] base-8
      windows of [fixed_base_window_size = 3] bits ([n = 85] for the full-width
      bases, [n = 22] for the short ValueCommitV base).
      [EccSpec.window_digit k i = (k / 8^i) mod 8] is the i-th digit; the
      windowed table for window [w] with digit [d] encodes the point
      [(window_scalar n w d) · G].  To keep every loaded window point a valid
      non-identity affine point, each of the first [n - 1] windows carries an
      additive offset [2 · 8^w]; the last window subtracts the accumulated
      offset [window_offset_sum (n - 1)], so the windows still sum to the
      scalar.  The radix and offset sum are the shared
      [FixedBaseTableDefs] definitions (the same constants the per-base window
      tables are built from). *)

  (** The window radix [8 = 2^3]. *)
  Notation window_radix := FixedBaseTableDefs.window_radix.

  (** The accumulated per-window offset of the first [m] windows,
      [sum_{j=0}^{m-1} 2 · 8^j]. *)
  Notation window_offset_sum := FixedBaseTableDefs.window_offset_sum.

  (** The scalar that window [w] (of an [n]-window decomposition) with digit
      [d] contributes: [(d + 2) · 8^w] on every window but the last, and
      [d · 8^w - window_offset_sum (n - 1)] on the last window. *)
  Definition window_scalar (n w : nat) (d : Z) : Z :=
    if Nat.eqb (S w) n then
      d * window_radix ^ Z.of_nat w - window_offset_sum (n - 1)%nat
    else
      (d + 2) * window_radix ^ Z.of_nat w.

  (** The cumulative scalar of an arbitrary per-window scalar sequence after
      [k] windows. *)
  Fixpoint partial_sum (ks : nat -> Z) (k : nat) : Z :=
    match k with
    | O => 0
    | S k' => partial_sum ks k' + ks k'
    end.

  (** [S_k]: the cumulative window scalar of the scalar [alpha] after [k]
      windows of an [n]-window decomposition. *)
  Definition cumulative_scalar (n : nat) (alpha : Z) (k : nat) : Z :=
    partial_sum (fun w => window_scalar n w (EccSpec.window_digit alpha w)) k.

  (** The SpendAuthG full-fixed incomplete-addition region. *)
  Definition spend_auth_g_region : RegionId.t :=
    RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete.

  (** ** Group-theoretic helpers

      Closure / canonicality of the binary multiple [mul k G], the [repr]
      homomorphism, the curve [x]-nonzero fact, the same-[x] dichotomy lifted to
      [repr], and the per-step distinctness [x(mul i G) <> x(mul j G)] when
      [i <> +/- j (mod q)].  These are proved from the generic [Weierstrass] /
      [Model] / [Pallas] interface and are the bridge that the ladder argument
      [incomplete_distinct_of_range_bounds] consumes.
      They live in this Orchard-facing file
      because that lemma is stated here; they depend only on [EllipticCurve/].
      Reducedness of [add]/[neg]/[mul] outputs is [Weierstrass.add_reduced] /
      [neg_reduced] / [mul_reduced]; only the [on_curve] closure facts for
      [mul] need local glue. *)

  Section Generic.
  Context {p : Z} `{Prime p}.
  Variables (a b : Z).

  Lemma w_neg_on_curve (P : Weierstrass.point) :
    Weierstrass.on_curve (p:=p) a b P ->
    Weierstrass.on_curve (p:=p) a b (Weierstrass.neg (p:=p) P).
  Proof.
    intro HP. destruct P as [| x y].
    - exact I.
    - cbn [Weierstrass.neg Weierstrass.on_curve] in *.
      rewrite <- HP.
      assert (Heq : (UnOp.opp (p:=p) y) *F (UnOp.opp (p:=p) y) = y *F y).
      { unfold UnOp.opp, BinOp.mul.
        rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_opp_opp. reflexivity. }
      rewrite Heq. reflexivity.
  Qed.

  Lemma w_mul_pos_on_curve (n : positive) (P : Weierstrass.point) :
    3 < p -> Weierstrass.on_curve (p:=p) a b P ->
    Weierstrass.on_curve (p:=p) a b (Weierstrass.mul_pos (p:=p) a n P).
  Proof.
    intros Hp HP. induction n as [n IH | n IH | ]; cbn [Weierstrass.mul_pos].
    - apply Weierstrass.add_on_curve; [exact Hp | exact HP |].
      apply Weierstrass.add_on_curve; [exact Hp | exact IH | exact IH].
    - apply Weierstrass.add_on_curve; [exact Hp | exact IH | exact IH].
    - exact HP.
  Qed.

  Lemma w_mul_on_curve (k : Z) (P : Weierstrass.point) :
    3 < p -> Weierstrass.on_curve (p:=p) a b P ->
    Weierstrass.on_curve (p:=p) a b (Weierstrass.mul (p:=p) a k P).
  Proof.
    intros Hp HP. destruct k as [| n | n]; cbn [Weierstrass.mul].
    - exact I.
    - apply w_mul_pos_on_curve; assumption.
    - apply w_neg_on_curve. apply w_mul_pos_on_curve; assumption.
  Qed.

  End Generic.

  Lemma pallas_3_lt : 3 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma pallas_11_lt : 11 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

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

  Lemma affine_reduced (x y : Z) : Pallas.reduced (Pallas.affine x y).
  Proof.
    unfold Pallas.reduced, Pallas.affine, Weierstrass.reduced.
    split; apply from_idem.
  Qed.

  Lemma pallas_repr_add (P Q : Weierstrass.point) :
    Pallas.reduced P -> Pallas.reduced Q -> Pallas.on_curve P -> Pallas.on_curve Q ->
    PallasModel.repr (Pallas.add P Q) =
      EccSpec.point_add (PallasModel.repr P) (PallasModel.repr Q).
  Proof.
    intros HPr HQr HPo HQo. exact (PallasModel.repr_add P Q HPr HQr HPo HQo).
  Qed.

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
      (pallas_mul_reduced i G HGred) (pallas_mul_reduced j G HGred)
      (pallas_mul_on_curve i G HGoc) (pallas_mul_on_curve j G HGoc) Hx)
      as [Heq | Hneg].
    - apply Hij.
      apply (proj1 (Weierstrass.mul_injective_mod Pallas.a Pallas.b
        G Pallas.pallas_q pallas_11_lt Pallas.nonsingular HGred HGoc HGne
        Pallas.pallas_q_is_prime HGord i j)).
      exact Heq.
    - apply Hijn.
      assert (Heq2 : Pallas.mul i G = Pallas.mul (- j) G).
      { rewrite Hneg. symmetry.
        exact (Weierstrass.mul_neg Pallas.a Pallas.b j G HGred). }
      apply (proj1 (Weierstrass.mul_injective_mod Pallas.a Pallas.b
        G Pallas.pallas_q pallas_11_lt Pallas.nonsingular HGred HGoc HGne
        Pallas.pallas_q_is_prime HGord i (- j))).
      exact Heq2.
  Qed.

  Lemma partial_sum_shift (ks : nat -> Z) (i : nat) :
    ks 0%nat + partial_sum (fun j => ks (S j)) i = partial_sum ks (S i).
  Proof.
    induction i as [| i IH].
    - cbn [partial_sum]. lia.
    - cbn [partial_sum] in IH |- *. lia.
  Qed.

  (** ** Numeric layer, generic in the window count [n]

      The per-window scalar shapes ([window_scalar_nonlast_gen],
      [window_scalar_last_gen]), the base-8 carry bound on partial sums
      ([partial_sum_window_bound]), the signed-radix-8 range bound
      ([window_scalar_range_bound]) and the window-1 split
      ([partial_sum_split_1]) over an abstract digit sequence [ds] and window
      count [n <= 85].  The [n = 85] / [window_digit]-digit instances are
      stated below. *)

  (** Each window digit is a base-8 digit, [0 <= digit < 8]. *)
  Lemma window_digit_bound (alpha : Z) (w : nat) :
    0 <= EccSpec.window_digit alpha w < 8.
  Proof.
    unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (** A window [w] that is not the last carries the additive offset [+2]: its
      scalar is [(d + 2) · 8^w]. *)
  Lemma window_scalar_nonlast_gen (n w : nat) (d : Z) :
    (S w <> n)%nat ->
    window_scalar n w d = (d + 2) * 8 ^ Z.of_nat w.
  Proof.
    intro Hw. unfold window_scalar.
    rewrite (proj2 (Nat.eqb_neq (S w) n) Hw). reflexivity.
  Qed.

  Lemma window_scalar_nonlast (w : nat) (d : Z) :
    (w < 84)%nat ->
    window_scalar 85 w d = (d + 2) * 8 ^ Z.of_nat w.
  Proof.
    intro Hw. apply window_scalar_nonlast_gen. lia.
  Qed.

  (** The last window's scalar of an [S m]-window decomposition. *)
  Lemma window_scalar_last_gen (m : nat) (d : Z) :
    window_scalar (S m) m d = d * 8 ^ Z.of_nat m - window_offset_sum m.
  Proof.
    unfold window_scalar. rewrite Nat.eqb_refl.
    replace (S m - 1)%nat with m by lia. reflexivity.
  Qed.

  (** The last window's scalar at [n = 85] (closed purely by conversion). *)
  Lemma window_scalar_last (d : Z) :
    window_scalar 85 84 d = d * 8 ^ Z.of_nat 84 - window_offset_sum 84.
  Proof. reflexivity. Qed.

  (** The cumulative scalar's one-step unfolding. *)
  Lemma cumulative_scalar_succ_gen (n : nat) (alpha : Z) (m : nat) :
    cumulative_scalar n alpha (S m) =
    cumulative_scalar n alpha m + window_scalar n m (EccSpec.window_digit alpha m).
  Proof. reflexivity. Qed.

  Lemma cumulative_scalar_succ (alpha : Z) (m : nat) :
    cumulative_scalar 85 alpha (S m) =
    cumulative_scalar 85 alpha m + window_scalar 85 m (EccSpec.window_digit alpha m).
  Proof. reflexivity. Qed.

  (** The partial window-scalar sum over [m < n] non-last windows of digits
      [ds] is nonnegative and satisfies [7 · S_m + 9 <= 9 · 8^m]; this is the
      base-8 carry bound on the offset digits [d_w + 2 <= 9], and it implies
      the sharper [S_m < 2 · 8^m] used below. *)
  Lemma partial_sum_window_bound (n : nat) (ds : nat -> Z)
      (Hds : forall w : nat, (w < n)%nat -> 0 <= ds w < 8)
      (m : nat) :
    (m < n)%nat ->
    0 <= partial_sum (fun w => window_scalar n w (ds w)) m
    /\ 7 * partial_sum (fun w => window_scalar n w (ds w)) m + 9
         <= 9 * 8 ^ Z.of_nat m.
  Proof.
    induction m as [| m IH]; intro Hm.
    - cbn [partial_sum]. rewrite Z.pow_0_r. lia.
    - destruct (IH ltac:(lia)) as [IH0 IH7].
      assert (Hsum :
        partial_sum (fun w => window_scalar n w (ds w)) (S m) =
        partial_sum (fun w => window_scalar n w (ds w)) m +
          window_scalar n m (ds m)) by (cbn [partial_sum]; reflexivity).
      rewrite Hsum.
      rewrite (window_scalar_nonlast_gen n m (ds m) ltac:(lia)).
      pose proof (Hds m ltac:(lia)) as Hd.
      assert (Hpow : 8 ^ Z.of_nat (S m) = 8 * 8 ^ Z.of_nat m).
      { rewrite Nat2Z.inj_succ.
        rewrite Z.pow_succ_r; [reflexivity | apply Nat2Z.is_nonneg]. }
      assert (Hp1 : 0 < 8 ^ Z.of_nat m)
        by (apply Z.pow_pos_nonneg; [lia | apply Nat2Z.is_nonneg]).
      assert (Hprod : (ds m + 2) * 8 ^ Z.of_nat m <= 9 * 8 ^ Z.of_nat m) by nia.
      rewrite Hpow. split; nia.
  Qed.

  Lemma cumulative_scalar_bound (alpha : Z) (m : nat) :
    (m <= 84)%nat ->
    0 <= cumulative_scalar 85 alpha m
    /\ 7 * cumulative_scalar 85 alpha m + 9 <= 9 * 8 ^ Z.of_nat m.
  Proof.
    intro Hm.
    exact (partial_sum_window_bound 85 (fun w => EccSpec.window_digit alpha w)
             (fun w _ => window_digit_bound alpha w) m ltac:(lia)).
  Qed.

  (** Numeric headroom: every non-last window scalar and partial sum that
      appears below stays well under [pallas_q], because [11 · 8^83 < pallas_q]
      ([8^83 = 2^249], [pallas_q > 2^254 = 32 · 2^249]). *)
  Lemma pow8_83_lt_pallas_q : 11 * 8 ^ 83 < Pallas.pallas_q.
  Proof.
    unfold Pallas.pallas_q, Primes.pallas_q, Primes.t_q. vm_compute. reflexivity.
  Qed.

  (** ** Signed-radix-8 range bound

      For a non-last window ([0 < m], [S m < n]) of an [n <= 85]-window
      decomposition with digits [ds], the per-window scalar
      [k_m = window_scalar n m (ds m)] is, modulo [pallas_q], neither the
      partial sum [S_m] nor its negation.  This is the digit-dependent fact
      that, via the same-x dichotomy ([Weierstrass.same_x_eq_or_neg]) and the
      injectivity of [mul] modulo the prime order
      ([Weierstrass.mul_injective_mod]), separates the next window point's x
      from the accumulator's.

      The bound [S m < n] is necessary, not cosmetic: the statement is false at
      the last window.  There the windowed encoding makes [k_{n-1} + S_{n-1}]
      the scalar itself, so [k_{n-1} = -S_{n-1} (mod pallas_q)] exactly at the
      zero scalar (refuting the second conjunct), and [k_{n-1} = S_{n-1}
      (mod pallas_q)] for a specific nonzero scalar (refuting the first), so no
      side condition on the scalar alone rescues the last window.  The circuit
      avoids the issue by closing the windowed ladder with a *complete*
      addition at the last window rather than the incomplete addition this
      distinctness precondition guards. *)
  Lemma window_scalar_range_bound (n : nat) (ds : nat -> Z)
      (Hds : forall w : nat, (w < n)%nat -> 0 <= ds w < 8)
      (Hn : (n <= 85)%nat)
      (m : nat) (Hm : (0 < m)%nat) (HSm : (S m < n)%nat) :
    window_scalar n m (ds m) mod Pallas.pallas_q <>
      partial_sum (fun w => window_scalar n w (ds w)) m mod Pallas.pallas_q /\
    window_scalar n m (ds m) mod Pallas.pallas_q <>
      (- partial_sum (fun w => window_scalar n w (ds w)) m) mod Pallas.pallas_q.
  Proof.
    destruct (partial_sum_window_bound n ds Hds m ltac:(lia)) as [HS0 HS7].
    pose proof (Hds m ltac:(lia)) as Hd.
    rewrite (window_scalar_nonlast_gen n m (ds m) ltac:(lia)).
    pose proof pow8_83_lt_pallas_q as Hq.
    assert (HP1 : 1 <= 8 ^ Z.of_nat m).
    { replace 1 with (8 ^ 0) by reflexivity. apply Z.pow_le_mono_r; lia. }
    assert (HPub : 8 ^ Z.of_nat m <= 8 ^ 83).
    { apply Z.pow_le_mono_r; lia. }
    assert (Hk_pos : 0 < (ds m + 2) * 8 ^ Z.of_nat m) by nia.
    assert (Hk_lb : 2 * 8 ^ Z.of_nat m <= (ds m + 2) * 8 ^ Z.of_nat m) by nia.
    assert (Hk_ub1 : (ds m + 2) * 8 ^ Z.of_nat m <= 9 * 8 ^ Z.of_nat m) by nia.
    assert (Hk_ub : (ds m + 2) * 8 ^ Z.of_nat m <= 9 * 8 ^ 83) by lia.
    assert (HS_ub :
      partial_sum (fun w => window_scalar n w (ds w)) m < 2 * 8 ^ Z.of_nat m)
      by lia.
    assert (Hk_lt_q : (ds m + 2) * 8 ^ Z.of_nat m < Pallas.pallas_q) by lia.
    assert (HS_lt_q :
      partial_sum (fun w => window_scalar n w (ds w)) m < Pallas.pallas_q)
      by lia.
    assert (Hsum_lt_q :
      (ds m + 2) * 8 ^ Z.of_nat m
        + partial_sum (fun w => window_scalar n w (ds w)) m
        < Pallas.pallas_q) by lia.
    rewrite (Z.mod_small ((ds m + 2) * 8 ^ Z.of_nat m)
      Pallas.pallas_q ltac:(lia)).
    rewrite (Z.mod_small
      (partial_sum (fun w => window_scalar n w (ds w)) m)
      Pallas.pallas_q ltac:(lia)).
    split.
    - lia.
    - intro Hc.
      assert (H1 :
        ((ds m + 2) * 8 ^ Z.of_nat m
          + partial_sum (fun w => window_scalar n w (ds w)) m)
          mod Pallas.pallas_q = 0).
      { rewrite Hc, Zplus_mod_idemp_l.
        replace
          (- partial_sum (fun w => window_scalar n w (ds w)) m
            + partial_sum (fun w => window_scalar n w (ds w)) m)
          with 0 by lia.
        apply Zmod_0_l. }
      rewrite (Z.mod_small
        ((ds m + 2) * 8 ^ Z.of_nat m
          + partial_sum (fun w => window_scalar n w (ds w)) m)
        Pallas.pallas_q ltac:(lia)) in H1.
      lia.
  Qed.

  Lemma spend_auth_g_window_scalar_range_bound
      (alpha : Z) (n : nat)
      (Hn : (0 < n < 84)%nat) :
    window_scalar 85 n (EccSpec.window_digit alpha n) mod Pallas.pallas_q <>
      cumulative_scalar 85 alpha n mod Pallas.pallas_q /\
    window_scalar 85 n (EccSpec.window_digit alpha n) mod Pallas.pallas_q <>
      (- cumulative_scalar 85 alpha n) mod Pallas.pallas_q.
  Proof.
    exact (window_scalar_range_bound 85 (fun w => EccSpec.window_digit alpha w)
             (fun w _ => window_digit_bound alpha w) ltac:(lia) n
             ltac:(lia) ltac:(lia)).
  Qed.

  (** Any partial sum splits at window 1 (the accumulator scalar after windows
      [0 .. i] is the window-0 scalar plus the windows-1.. partial sum). *)
  Lemma partial_sum_split_1 (ks : nat -> Z) (i : nat) :
    partial_sum ks (1 + i)%nat =
    partial_sum ks 1 + partial_sum (fun m => ks (1 + m)%nat) i.
  Proof.
    induction i as [| i IH].
    - cbn [Nat.add partial_sum]. lia.
    - replace (1 + S i)%nat with (S (1 + i))%nat by lia.
      cbn [partial_sum] in IH |- *. lia.
  Qed.

  Lemma cumulative_scalar_split_1 (alpha : Z) (i : nat) :
    cumulative_scalar 85 alpha (1 + i)%nat =
    cumulative_scalar 85 alpha 1 +
    partial_sum
      (fun m => window_scalar 85 (1 + m)%nat
        (EccSpec.window_digit alpha (1 + m)%nat))
      i.
  Proof.
    exact (partial_sum_split_1
             (fun w => window_scalar 85 w (EccSpec.window_digit alpha w)) i).
  Qed.

  (** ** The scalar-multiplication composition law at Pallas

      The window points are computed through the Weierstrass homomorphism
      [mul_add], the scalar composition law [mul_mul], and [mul_neg].
      These Pallas-level wrappers thread [11 < p], [nonsingular] and the
      [reduced]/[on_curve] witnesses these laws require. *)
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

  Lemma pallas_mul_mul (i j : Z) (P : Pallas.point) :
    Pallas.reduced P -> Pallas.on_curve P ->
    Pallas.mul (i * j) P = Pallas.mul i (Pallas.mul j P).
  Proof.
    intros HrP HoP.
    exact (Weierstrass.mul_mul (p := Primes.pallas_p) Pallas.a Pallas.b i j P
             pallas_11_lt Pallas.nonsingular HrP HoP).
  Qed.

  Lemma pallas_mul_neg (i : Z) (P : Pallas.point) :
    Pallas.reduced P ->
    Pallas.mul (- i) P = Pallas.neg (Pallas.mul i P).
  Proof.
    intro HrP.
    exact (Weierstrass.mul_neg (p := Primes.pallas_p) Pallas.a Pallas.b i P HrP).
  Qed.

  (** Scalar congruence for [mul]: peels [mul A P = mul B P] to the scalar
      equation [A = B] by *unification only*, so a closed point multiple is
      never forced through conversion (unlike [f_equal]/[reflexivity], whose
      reflexivity attempt would evaluate the 254-bit ladder). *)
  Lemma mul_scalar_eq (A B : Z) (P : Pallas.point) :
    A = B -> Pallas.mul A P = Pallas.mul B P.
  Proof. intros ->. reflexivity. Qed.

  Lemma pallas_mul_2 (B : Pallas.point) :
    Pallas.reduced B -> Pallas.on_curve B ->
    Pallas.mul 2 B = Pallas.add B B.
  Proof.
    intros HrB HoB.
    replace 2 with (1 + 1) by lia.
    rewrite (pallas_mul_add 1 1 B HrB HoB).
    rewrite !pallas_mul_one. reflexivity.
  Qed.

  (** Two-field record equality for [Point.t]. *)
  Lemma point_eq (P Q : Point.t) :
    Point.x P = Point.x Q -> Point.y P = Point.y Q -> P = Q.
  Proof.
    destruct P as [px py]; destruct Q as [qx qy]; simpl.
    intros Hx Hy; rewrite Hx, Hy; reflexivity.
  Qed.

  (** ** Correctness of the cert's incremental window table

      [mults_aux_nth] / [window_row_nth]: the cert's per-window row
      [[2]B; [3]B; ...; [9]B] computes the small multiples of [B].
      [nonlast_points_correct]: row [w], digit [i] of [nonlast_points n B] is
      the multiple [[(2+i) * 8^w] B] (composition law [mul_mul] threads the
      octupling chain).  [base_pow8_correct]: [base_pow8 n B = [8^n] B]. *)
  Lemma mults_aux_nth :
    forall (k : nat) (B acc : Pallas.point) (s : Z) (i : nat),
      Pallas.reduced B -> Pallas.on_curve B -> 0 <= s ->
      acc = Pallas.mul s B ->
      (i < k)%nat ->
      List.nth i (FixedBaseTableDefs.mults_aux B acc k) Pallas.identity
        = Pallas.mul (s + Z.of_nat i) B.
  Proof.
    induction k as [| k IH]; intros B acc s i HrB HoB Hs Hacc Hi.
    - lia.
    - cbn [FixedBaseTableDefs.mults_aux].
      destruct i as [| i'].
      + cbn [List.nth]. rewrite Hacc. f_equal. lia.
      + cbn [List.nth].
        assert (Hacc1 : Pallas.add acc B = Pallas.mul (s + 1) B).
        { rewrite Hacc. rewrite (pallas_mul_add s 1 B HrB HoB).
          rewrite pallas_mul_one. reflexivity. }
        rewrite (IH B (Pallas.add acc B) (s + 1) i' HrB HoB ltac:(lia) Hacc1 ltac:(lia)).
        f_equal. lia.
  Qed.

  Lemma window_row_nth (B : Pallas.point) (i : nat) :
    Pallas.reduced B -> Pallas.on_curve B -> (i < 8)%nat ->
    List.nth i (FixedBaseTableDefs.window_row B) Pallas.identity
      = Pallas.mul (2 + Z.of_nat i) B.
  Proof.
    intros HrB HoB Hi.
    unfold FixedBaseTableDefs.window_row.
    rewrite (mults_aux_nth 8 B (Pallas.add B B) 2 i HrB HoB ltac:(lia)
               (eq_sym (pallas_mul_2 B HrB HoB)) Hi).
    reflexivity.
  Qed.

  Lemma nonlast_points_length (n : nat) (B : Pallas.point) :
    List.length (FixedBaseTableDefs.nonlast_points n B) = n.
  Proof.
    revert B. induction n as [| n IH]; intro B.
    - reflexivity.
    - cbn [FixedBaseTableDefs.nonlast_points List.length]. rewrite IH. reflexivity.
  Qed.

  Lemma nonlast_points_correct :
    forall (n : nat) (B : Pallas.point) (w i : nat),
      Pallas.reduced B -> Pallas.on_curve B ->
      (w < n)%nat -> (i < 8)%nat ->
      List.nth i
        (List.nth w (FixedBaseTableDefs.nonlast_points n B) []) Pallas.identity
        = Pallas.mul ((2 + Z.of_nat i) * 8 ^ Z.of_nat w) B.
  Proof.
    induction n as [| n IH]; intros B w i HrB HoB Hw Hi.
    - lia.
    - cbn [FixedBaseTableDefs.nonlast_points].
      assert (Hbase :
        List.nth 6 (FixedBaseTableDefs.window_row B) Pallas.identity
        = Pallas.mul 8 B).
      { rewrite (window_row_nth B 6 HrB HoB ltac:(lia)). f_equal. }
      destruct w as [| w'].
      + cbn [List.nth].
        rewrite (window_row_nth B i HrB HoB Hi).
        replace (Z.of_nat 0) with 0 by reflexivity.
        rewrite Z.pow_0_r. f_equal. lia.
      + cbn [List.nth].
        rewrite Hbase.
        assert (HrB8 : Pallas.reduced (Pallas.mul 8 B))
          by (apply pallas_mul_reduced; exact HrB).
        assert (HoB8 : Pallas.on_curve (Pallas.mul 8 B))
          by (apply pallas_mul_on_curve; exact HoB).
        rewrite (IH (Pallas.mul 8 B) w' i HrB8 HoB8 ltac:(lia) Hi).
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        rewrite <- (pallas_mul_mul ((2 + Z.of_nat i) * 8 ^ Z.of_nat w') 8 B HrB HoB).
        f_equal. ring.
  Qed.

  Lemma base_pow8_correct (n : nat) (B : Pallas.point) :
    Pallas.reduced B -> Pallas.on_curve B ->
    FixedBaseTableDefs.base_pow8 n B = Pallas.mul (8 ^ Z.of_nat n) B.
  Proof.
    revert B. induction n as [| n IH]; intros B HrB HoB.
    - cbn [FixedBaseTableDefs.base_pow8].
      replace (Z.of_nat 0) with 0 by reflexivity.
      rewrite Z.pow_0_r. symmetry. apply pallas_mul_one.
    - cbn [FixedBaseTableDefs.base_pow8].
      assert (HrB8 : Pallas.reduced (Pallas.mul 8 B))
        by (apply pallas_mul_reduced; exact HrB).
      assert (HoB8 : Pallas.on_curve (Pallas.mul 8 B))
        by (apply pallas_mul_on_curve; exact HoB).
      rewrite (IH (Pallas.mul 8 B) HrB8 HoB8).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite <- (pallas_mul_mul (8 ^ Z.of_nat n) 8 B HrB HoB).
      f_equal. ring.
  Qed.

  (** Make scalar multiplication opaque to conversion: window points at a
      concrete generator are closed 254-bit multiples, so any
      [reflexivity]/[rewrite]/[f_equal] that would reduce one to weak-head
      normal form runs the full double-and-add ladder.  With [mul] opaque,
      conversion compares the *scalar arguments* instead, and the [mul_*]
      rewrite lemmas still fire (matching is syntactic).  Restored to
      transparent right after the x-coordinate instances.  ([Pallas.v] does
      the same for its order certificate; the per-base instantiation files
      repeat the same opaque window around their instances.) *)
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** The [j]-th last-window entry (abstract [j < 8], with abstract base/offset
      [b]/[c], so no closed point is materialised). *)
  Lemma last_row_nth (b c : Pallas.point) (j : nat) :
    (j < 8)%nat ->
    List.nth j (FixedBaseTableDefs.last_row b c) Pallas.identity
    = Pallas.add (Pallas.mul (Z.of_nat j) b) (Pallas.neg c).
  Proof.
    intro Hj.
    unfold FixedBaseTableDefs.last_row.
    do 8 (destruct j as [| j]; [reflexivity |]).
    exfalso; lia.
  Qed.

  (** ** Parameterized per-base window table (x-coordinate half)

      The table-correctness chain over an abstract on-curve reduced base point
      [G] and last
      window index [m] (window count [S m]): correctness of the last-window
      cert entry, the table-entry bridge (the octupling-chain table entry is
      the
      abstract multiple [window_scalar (S m) w d * G]), and the unconditional
      x-coordinate half (the spec-table window point's x equals the
      multiple's x), the latter from the per-base Lagrange x-coordinate
      [vm_compute] certificate passed in as [Hx_cert]. *)
  Section PerBaseTable.
    Variable G : Pallas.point.
    Hypothesis HG_on_curve : Pallas.on_curve G.
    Hypothesis HG_reduced : Pallas.reduced G.
    (** The last window index; the decomposition has [S m] windows. *)
    Variable m : nat.

    (** Correctness of a last-window cert entry.
        [[i] B_m - [C] G = [i * 8^m - C] G]. *)
    Lemma last_entry_eq_gen (i : Z) :
      Pallas.add
        (Pallas.mul i (FixedBaseTableDefs.base_pow8 m G))
        (Pallas.neg (Pallas.mul (FixedBaseTableDefs.window_offset_sum m) G))
      = Pallas.mul
          (i * 8 ^ Z.of_nat m - FixedBaseTableDefs.window_offset_sum m) G.
    Proof using HG_on_curve HG_reduced.
      rewrite (base_pow8_correct m G HG_reduced HG_on_curve).
      rewrite <- (pallas_mul_mul i (8 ^ Z.of_nat m) G HG_reduced HG_on_curve).
      rewrite <- (pallas_mul_neg (FixedBaseTableDefs.window_offset_sum m) G
                    HG_reduced).
      rewrite <- (pallas_mul_add (i * 8 ^ Z.of_nat m)
                    (- FixedBaseTableDefs.window_offset_sum m) G
                    HG_reduced HG_on_curve).
      apply mul_scalar_eq. generalize (8 ^ Z.of_nat m); intro P. ring.
    Qed.

    (** ** Table-entry bridge — the certificate table entry is the Weierstrass
        multiple.  Window [w], digit [d]'s entry of the octupling-chain window
        table (the shape of every per-base [<Base>FullTable.full_table]) is
        exactly the abstract multiple [window_scalar (S m) w d * G].  Consumed
        to transport the positive QR certificate
        [<Base>WindowSignCert.y_check_entry] onto
        [repr (mul (window_scalar ..) G)]. *)
    Lemma full_table_entry_eq_mul_gen (w : nat) (d : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      List.nth (Z.to_nat d)
        (List.nth w
          (FixedBaseTableDefs.nonlast_points m G ++
           [FixedBaseTableDefs.last_row (FixedBaseTableDefs.base_pow8 m G)
              (Pallas.mul (FixedBaseTableDefs.window_offset_sum m) G)]) [])
        Pallas.identity
      = Pallas.mul (window_scalar (S m) w d) G.
    Proof using HG_on_curve HG_reduced.
      assert (Hlen : List.length (FixedBaseTableDefs.nonlast_points m G) = m)
        by apply nonlast_points_length.
      destruct (Nat.lt_ge_cases w m) as [Hwm | Hwm].
      - (* Non-last windows *)
        rewrite List.app_nth1 by (rewrite Hlen; lia).
        rewrite (nonlast_points_correct m G w (Z.to_nat d)
                   HG_reduced HG_on_curve Hwm ltac:(lia)).
        rewrite (Z2Nat.id d ltac:(lia)).
        rewrite (window_scalar_nonlast_gen (S m) w d ltac:(lia)).
        f_equal. generalize (8 ^ Z.of_nat w); intro X. ring.
      - (* Last window.  Use the closed-form last-window scalar; keep [d]
           abstract throughout, so no closed point is ever materialised (which
           would be evaluated by unification/conversion). *)
        assert (Hw_eq : w = m) by lia. subst w.
        rewrite List.app_nth2 by (rewrite Hlen; lia).
        rewrite Hlen.
        replace (m - m)%nat with 0%nat by lia.
        cbn [List.nth].
        rewrite (window_scalar_last_gen m d).
        rewrite (last_row_nth (FixedBaseTableDefs.base_pow8 m G)
                   (Pallas.mul (FixedBaseTableDefs.window_offset_sum m) G)
                   (Z.to_nat d) ltac:(lia)).
        rewrite (Z2Nat.id d ltac:(lia)).
        rewrite (last_entry_eq_gen d).
        reflexivity.
    Qed.

    (** The per-base spec table and its Lagrange x-coordinate certificate
        (each base's [<Base>FixedWindowCert.x_check_entry], with the cert's
        [table]/[default] constants unfolded to the spec table). *)
    Variable spec_table : list EccSpec.fixed_window.
    Hypothesis Hx_cert :
      forall (w i : nat), (w < S m)%nat -> (i < 8)%nat ->
        Point.x
          (EccSpec.fixed_window_point
            (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
            (Z.of_nat i) 0) =
        Point.x
          (PallasModel.repr
            (List.nth i
              (List.nth w
                (FixedBaseTableDefs.nonlast_points m G ++
                 [FixedBaseTableDefs.last_row (FixedBaseTableDefs.base_pow8 m G)
                    (Pallas.mul (FixedBaseTableDefs.window_offset_sum m) G)]) [])
              Pallas.identity)).

    (** ** Window-point x-coordinate agreement — the *unconditional* half

        The x-coordinate agreement needs no y-sign witness: it is purely
        the Lagrange-interpolation [vm_compute] certificate transported through
        the composition-law-built window table.  This is the part of the
        per-window table correctness that
        survives without pinning the y-coordinate sign, so it is the reusable
        foundation for the circuit-fact extraction (the window point's x equals
        the multiple [window_scalar · G]'s x regardless of which y-sign the
        prover witnessed). *)
    Lemma fixed_window_point_x_eq_mul_gen (w : nat) (d u : Z)
        (Hw : (w < S m)%nat) (Hd : 0 <= d < 8) :
      Point.x
        (EccSpec.fixed_window_point
          (List.nth w spec_table OrchardActionFixedBase.fixed_window_default)
          d u) =
      Point.x
        (PallasModel.repr (Pallas.mul (window_scalar (S m) w d) G)).
    Proof using HG_on_curve HG_reduced Hx_cert.
      pose proof (Hx_cert w (Z.to_nat d) Hw ltac:(lia)) as Hx.
      rewrite (Z2Nat.id d ltac:(lia)) in Hx.
      cbn [EccSpec.fixed_window_point Point.x] in Hx |- *.
      rewrite Hx; clear Hx.
      rewrite (full_table_entry_eq_mul_gen w d Hw Hd).
      reflexivity.
    Qed.
  End PerBaseTable.

  (** ** Table-entry bridge, SpendAuthG instance *)
  Lemma full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w SpendAuthGFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 85 w d) PallasGenerators.spend_auth_g_G.
  Proof.
    unfold SpendAuthGFullTable.full_table, SpendAuthGFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.spend_auth_g_G
             PallasGenerators.spend_auth_g_on_curve
             PallasGenerators.spend_auth_g_reduced 84 w d Hw Hd).
  Qed.

  (** ** Window-point x-coordinate agreement, SpendAuthG instance *)
  Lemma spend_auth_g_fixed_window_point_x_eq_mul
      (w : nat) (d u : Z)
      (Hw : (w < 85)%nat)
      (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w OrchardActionFixedBase.spend_auth_g_fixed_table
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 w d) PallasGenerators.spend_auth_g_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.spend_auth_g_G
              PallasGenerators.spend_auth_g_on_curve
              PallasGenerators.spend_auth_g_reduced 84
              OrchardActionFixedBase.spend_auth_g_fixed_table _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (SpendAuthGFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold SpendAuthGFixedWindowCert.table, SpendAuthGFixedWindowCert.default
      in Hx.
    unfold SpendAuthGFullTable.full_table, SpendAuthGFullTable.G in Hx.
    exact Hx.
  Qed.

  (** ** Per-window point equals the Weierstrass multiple

      The [w]-th SpendAuthG window point at digit [d], with the witnessed
      square root [u] pinning the y-coordinate, equals the [repr] of the
      Weierstrass multiple [window_scalar 85 w d · spend_auth_g_G].  The
      x-coordinate equality is [spend_auth_g_fixed_window_point_x_eq_mul];
      the hypothesis [Hwitness] ties [u] to the on-curve y so the sign is
      fixed. *)
  Lemma spend_auth_g_fixed_window_point_eq_mul
      (w : nat) (d u : Z)
      (Hw : (w < 85)%nat)
      (Hd : 0 <= d < 8)
      (Hwitness :
        Point.y
          (EccSpec.fixed_window_point
            (List.nth w OrchardActionFixedBase.spend_auth_g_fixed_table
              OrchardActionFixedBase.fixed_window_default) d u) =
        Point.y
          (PallasModel.repr
            (Pallas.mul (window_scalar 85 w d)
              PallasGenerators.spend_auth_g_G))) :
    EccSpec.fixed_window_point
      (List.nth w OrchardActionFixedBase.spend_auth_g_fixed_table
        OrchardActionFixedBase.fixed_window_default) d u =
    PallasModel.repr
      (Pallas.mul (window_scalar 85 w d) PallasGenerators.spend_auth_g_G).
  Proof.
    apply point_eq.
    - exact (spend_auth_g_fixed_window_point_x_eq_mul w d u Hw Hd).
    - exact Hwitness.
  Qed.

  (** Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].

  (** The [repr] of a nonzero multiple of an on-curve base lies on the Pallas
      curve.  [mul k G] is on the curve (group law A3); its [repr] is the
      affine record unless [mul k G] is the identity, which is ruled out by the
      field-nonzero x-coordinate hypothesis (the [(0,0)] sentinel has
      [x = 0]). *)
  Lemma repr_mul_on_curve_gen (G : Pallas.point)
      (HG_on_curve : Pallas.on_curve G) (k : Z)
      (Hx0 : UnOp.from (Point.x (PallasModel.repr (Pallas.mul k G))) <> 0) :
    OrchardActionFixedBase.point_on_curve
      (PallasModel.repr (Pallas.mul k G)).
  Proof.
    pose proof (pallas_mul_on_curve k G HG_on_curve) as Hmoc.
    unfold OrchardActionFixedBase.point_on_curve.
    destruct (Pallas.mul k G) as [| x y] eqn:Emul.
    - exfalso. apply Hx0. reflexivity.
    - cbn [PallasModel.repr Point.x Point.y].
      exact (PallasModel.on_curve_affine_poly x y Hmoc).
  Qed.

  (* [repr] of a reduced Weierstrass point has a reduced y-coordinate (the
     [Infinity] case is the [(0,0)] sentinel). *)
  Lemma repr_y_reduced (Q : Weierstrass.point) :
    Pallas.reduced Q ->
    UnOp.from (Point.y (PallasModel.repr Q)) = Point.y (PallasModel.repr Q).
  Proof.
    intro HQ. destruct Q as [| x y].
    - unfold PallasModel.repr, EccSpec.identity. cbn [Point.y].
      unfold UnOp.from. apply Zmod_0_l.
    - cbn [PallasModel.repr Point.y]. destruct HQ as [_ Hy]. exact Hy.
  Qed.

  (* Subtracting something [≡ 0] does not change the residue class. *)
  Lemma from_sub_zero_r (a b : Z) :
    UnOp.from b = 0 -> UnOp.from (a -F b) = UnOp.from a.
  Proof.
    intro Hb. unfold BinOp.sub, UnOp.from in *.
    rewrite Zmod_mod, (Zminus_mod a b), Hb, Z.sub_0_r, !Zmod_mod. reflexivity.
  Qed.

  (* A cube of something [≡ 0] is [≡ 0]. *)
  Lemma cube_from_zero (a : Z) :
    UnOp.from a = 0 -> UnOp.from (a *F a *F a) = 0.
  Proof.
    intro Ha.
    assert (Hc : a *F a *F a = 0)
      by (rewrite mul_zero_implies_zero; right; exact Ha).
    rewrite Hc. unfold UnOp.from. apply Zmod_0_l.
  Qed.

  (* An on-curve point cannot have [x ≡ 0]: that forces [y² = b], contradicting
     [pallas_b] being a quadratic non-residue.  Feeds the [x ≠ 0] side condition
     of [repr_mul_on_curve_gen] via the witnessed window point (whose x is the
     same Lagrange interpolation as the multiple's). *)
  Lemma oncurve_x_zero_absurd (P : Point.t) :
    OrchardActionFixedBase.point_on_curve P ->
    UnOp.from (Point.x P) = 0 -> False.
  Proof.
    destruct P as [x y]. intros Honc Hx.
    unfold OrchardActionFixedBase.point_on_curve in Honc.
    cbn [Point.x Point.y] in Honc, Hx.
    apply sub_zero_equiv in Honc.
    apply (EccSpec.pallas_b_quadratic_nonresidue y).
    rewrite <- Honc. symmetry. apply from_sub_zero_r.
    apply cube_from_zero. exact Hx.
  Qed.

  (** ** Generic ladder distinctness from range bounds

      For a prime-order generator [G] (on the curve, reduced, non-identity,
      with order certificate [mul pallas_q G = identity]), if every ladder
      window point is the [repr] of a multiple [ks i · G] and each per-step
      scalar [ks i] differs, modulo [pallas_q], from [+/- (S0 + partial_sum ks
      i)] (the running accumulator's scalar), then the windowed ladder starting
      at [repr (mul S0 G)] satisfies [incomplete_additions_distinct_precondition].
      The distinctness of each x follows from [Weierstrass.same_x_eq_or_neg]
      (equal x implies equal or
      opposite) and [Weierstrass.mul_injective_mod] (injectivity of [mul]
      modulo the prime order). *)
  Lemma incomplete_distinct_of_range_bounds
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (G : Pallas.point)
      (ks : nat -> Z) (S0 : Z) (count : nat)
      (HG_on_curve : Pallas.on_curve G)
      (HG_reduced : Pallas.reduced G)
      (HG_ne : G <> Pallas.identity)
      (HG_order : Pallas.mul Pallas.pallas_q G = Pallas.identity)
      (Hwindows :
        forall i : nat,
          (i < count)%nat ->
          OrchardActionFixedBase.incomplete_additions_window_point Γ region
            (offset + Z.of_nat i) =
          PallasModel.repr (Pallas.mul (ks i) G))
      (Hrange :
        forall i : nat,
          (i < count)%nat ->
          ks i mod Pallas.pallas_q <>
            (S0 + partial_sum ks i) mod Pallas.pallas_q /\
          ks i mod Pallas.pallas_q <>
            (- (S0 + partial_sum ks i)) mod Pallas.pallas_q) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ region
      offset count (PallasModel.repr (Pallas.mul S0 G)).
  Proof.
    revert offset S0 ks Hwindows Hrange.
    induction count as [| n IH]; intros offset S0 ks Hwindows Hrange.
    - exact I.
    - cbn [OrchardActionFixedBase.incomplete_additions_distinct_precondition].
      split.
      + pose proof (Hwindows 0%nat ltac:(lia)) as Hw0.
        replace (offset + Z.of_nat 0) with offset in Hw0 by lia.
        rewrite Hw0.
        pose proof (Hrange 0%nat ltac:(lia)) as Hr.
        destruct Hr as [Hr1 Hr2].
        cbn [partial_sum] in Hr1, Hr2.
        apply (mul_x_neq G (ks 0%nat) S0 HG_on_curve HG_reduced HG_ne HG_order).
        * replace (S0 + 0) with S0 in Hr1 by lia. exact Hr1.
        * replace (S0 + 0) with S0 in Hr2 by lia. exact Hr2.
      + pose proof (Hwindows 0%nat ltac:(lia)) as Hw0.
        replace (offset + Z.of_nat 0) with offset in Hw0 by lia.
        rewrite Hw0.
        assert (Hadd :
            Pallas.mul (S0 + ks 0%nat) G =
            Pallas.add (Pallas.mul S0 G) (Pallas.mul (ks 0%nat) G)).
        { exact (Weierstrass.mul_add Pallas.a Pallas.b S0 (ks 0%nat) G
            pallas_11_lt Pallas.nonsingular HG_reduced HG_on_curve). }
        assert (Hhom :
            EccSpec.point_add (PallasModel.repr (Pallas.mul S0 G))
              (PallasModel.repr (Pallas.mul (ks 0%nat) G)) =
            PallasModel.repr (Pallas.mul (S0 + ks 0%nat) G)).
        { rewrite Hadd. symmetry.
          apply pallas_repr_add.
          - apply pallas_mul_reduced; exact HG_reduced.
          - apply pallas_mul_reduced; exact HG_reduced.
          - apply pallas_mul_on_curve; exact HG_on_curve.
          - apply pallas_mul_on_curve; exact HG_on_curve. }
        rewrite Hhom.
        apply (IH (offset + 1) (S0 + ks 0%nat) (fun j => ks (S j))).
        * intros i Hi.
          replace (offset + 1 + Z.of_nat i)
            with (offset + Z.of_nat (S i)) by lia.
          apply (Hwindows (S i)). lia.
        * intros i Hi.
          pose proof (Hrange (S i) ltac:(lia)) as Hr.
          destruct Hr as [Hr1 Hr2].
          rewrite <- (partial_sum_shift ks i) in Hr1, Hr2.
          split.
          -- replace (S0 + ks 0%nat + partial_sum (fun j => ks (S j)) i)
               with (S0 + (ks 0%nat + partial_sum (fun j => ks (S j)) i)) by lia.
             exact Hr1.
          -- replace (S0 + ks 0%nat + partial_sum (fun j => ks (S j)) i)
               with (S0 + (ks 0%nat + partial_sum (fun j => ks (S j)) i)) by lia.
             exact Hr2.
  Qed.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** [nth_error] of the split window list agrees with the [nth] of the shared
      fixed-base table for every in-range window index (the split-list and the
      table are definitionally equal).  Feeds the [w] side condition of
      [OrchardActionFixedBase.spend_auth_g_window_correct]. *)
  Lemma spend_auth_g_window_nth_error (j : nat) (Hj : (j < 85)%nat) :
    List.nth_error
      (OrchardActionFixedBase.spend_auth_g_first
       :: OrchardActionFixedBase.spend_auth_g_middle
          ++ [OrchardActionFixedBase.spend_auth_g_last]) j
    = Some (List.nth j OrchardActionFixedBase.spend_auth_g_fixed_table
              OrchardActionFixedBase.fixed_window_default).
  Proof.
    assert (Htbl :
      OrchardActionFixedBase.spend_auth_g_fixed_table =
      OrchardActionFixedBase.spend_auth_g_first
      :: OrchardActionFixedBase.spend_auth_g_middle
         ++ [OrchardActionFixedBase.spend_auth_g_last]).
    { change OrchardActionFixedBase.spend_auth_g_fixed_table
        with (EccSpec.fixed_table_of_rows
          Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows).
      exact OrchardActionFixedBase.spend_auth_g_table_split. }
    rewrite Htbl.
    apply nth_error_nth'.
    cbn [List.length]. rewrite List.length_app. cbn [List.length].
    rewrite OrchardActionFixedBase.spend_auth_g_middle_length. lia.
  Qed.

  (* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
     up-to-conversion matching in the composition below never evaluates [modpow]
     over the concrete Pallas [(p-1)/2] exponent (which blows the term up). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (** ** Parameterized per-base ladder chain

      The circuit-facing chain over a fixed satisfying assignment [Γ], region,
      abstract prime-order base [G], window count [n], per-window digit
      sequence [digit] and spec table:
      - [full_window_correct_gen]: every window point equals the
        [repr] of its Weierstrass multiple.  Composes
        - [Hwindow_eq]: the circuit window point equals
          [fixed_window_point] at the read digit / witnessed square root;
        - the on-curve fact [Hwindow_on_curve] at the same digit/witness;
        - [window_point_forced_of_disc]: that witnessed on-curve point
          equals the canonical (QR-sign-selected) window point, from the
          per-base discriminant certificate [Hwindow_disc];
        - [window_y_forced_of_disc] applied to the true multiple
          [repr (mul (window_scalar ..) G)], whose x agrees with the Lagrange
          x ([Hwindow_x]), whose on-curveness comes from
          the group law (identity ruled out by the same x), and whose [y + z]
          quadratic-residue side is the per-base positive certificate
          [Hwindow_qr].
        Elaborating the forcing-lemma applications requires the shared
        [Primes] instance (see the module alias in [Plonky3/M.v]): with
        distinct duplicate instances the [is_square] hypothesis types are only
        reconcilable by unfolding [modpow] at the concrete exponent, which
        does not terminate in practice.
      - [partial_sum_eq_mul_gen]: folding the first [k] window points
        (each the [repr] of its window multiple) through complete addition
        from the identity yields the [repr] of the cumulative multiple.
      - [ladder_distinct_precondition_holds_gen]: the full
        [count]-edge (rows 1..count, [n = count + 2]) ladder-distinctness
        predicate, from the per-window facts, the base accumulator (window 0)
        identified with [repr (mul S_1 G)] by [partial_sum_eq_mul_gen], and
        the range side by [window_scalar_range_bound]. *)
  Section PerBaseChain.
    Variable Γ : Assignment.t columns RegionId.t.
    Variable region : RegionId.t.
    Variable G : Pallas.point.
    Hypothesis HG_on_curve : Pallas.on_curve G.
    Hypothesis HG_reduced : Pallas.reduced G.
    (** The window count of the decomposition. *)
    Variable n : nat.
    (** The per-window digit read from the circuit (the [window_digit] of the
        recovered scalar for the running-sum bases, the raw running-sum word
        for the base-field NullifierK base). *)
    Variable digit : nat -> Z.
    Hypothesis Hdigit : forall j : nat, (j < n)%nat -> 0 <= digit j < 8.

    (** ** Partial sum as a multiple, over an arbitrary digit sequence *)
    Lemma partial_sum_eq_mul_gen (ds : nat -> Z) (k : nat)
        (Hwindows :
          forall i : nat,
            (i < k)%nat ->
            OrchardActionFixedBase.incomplete_additions_window_point Γ region
              (Z.of_nat i) =
            PallasModel.repr
              (Pallas.mul (window_scalar n i (ds i)) G)) :
      OrchardActionFixedBase.complete_additions_output Γ region 0 k
        EccSpec.identity =
      PallasModel.repr
        (Pallas.mul (partial_sum (fun w => window_scalar n w (ds w)) k) G).
    Proof using HG_on_curve HG_reduced.
      revert Hwindows.
      induction k as [| k' IH]; intro Hwindows.
      - cbn [OrchardActionFixedBase.complete_additions_output].
        cbn [partial_sum]. reflexivity.
      - assert (IHk :
          OrchardActionFixedBase.complete_additions_output Γ region 0 k'
            EccSpec.identity =
          PallasModel.repr
            (Pallas.mul (partial_sum (fun w => window_scalar n w (ds w)) k')
              G)).
        { apply IH. intros i Hi. apply Hwindows. lia. }
        rewrite OrchardActionFixedBase.complete_additions_output_succ.
        rewrite IHk.
        replace (0 + Z.of_nat k') with (Z.of_nat k') by lia.
        rewrite (Hwindows k' ltac:(lia)).
        assert (Hsum :
            partial_sum (fun w => window_scalar n w (ds w)) (S k') =
            partial_sum (fun w => window_scalar n w (ds w)) k' +
              window_scalar n k' (ds k')).
        { cbn [partial_sum]. reflexivity. }
        rewrite Hsum.
        assert (Hadd :
            Pallas.mul
              (partial_sum (fun w => window_scalar n w (ds w)) k' +
                window_scalar n k' (ds k'))
              G =
            Pallas.add
              (Pallas.mul (partial_sum (fun w => window_scalar n w (ds w)) k')
                G)
              (Pallas.mul (window_scalar n k' (ds k')) G)).
        { exact (Weierstrass.mul_add Pallas.a Pallas.b
            (partial_sum (fun w => window_scalar n w (ds w)) k')
            (window_scalar n k' (ds k'))
            G pallas_11_lt Pallas.nonsingular HG_reduced HG_on_curve). }
        rewrite Hadd.
        symmetry.
        apply pallas_repr_add.
        + apply pallas_mul_reduced; exact HG_reduced.
        + apply pallas_mul_reduced; exact HG_reduced.
        + apply pallas_mul_on_curve; exact HG_on_curve.
        + apply pallas_mul_on_curve; exact HG_on_curve.
    Qed.

    (** The per-base spec table and the per-window circuit facts. *)
    Variable spec_table : list EccSpec.fixed_window.
    (** The circuit window point equals the spec window point at the read
        digit and witnessed square root. *)
    Hypothesis Hwindow_eq :
      forall j : nat,
        (j < n)%nat ->
        OrchardActionFixedBase.incomplete_additions_window_point Γ region
          (Z.of_nat j) =
        EccSpec.fixed_window_point
          (List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
          (digit j)
          (List.nth j (OrchardActionInputs.read_us Γ region n) 0).
    (** The witnessed spec window point lies on the curve. *)
    Hypothesis Hwindow_on_curve :
      forall j : nat,
        (j < n)%nat ->
        OrchardActionFixedBase.point_on_curve
          (EccSpec.fixed_window_point
            (List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
            (digit j)
            (List.nth j (OrchardActionInputs.read_us Γ region n) 0)).
    (** The per-window discriminant is a quadratic non-residue. *)
    Hypothesis Hwindow_disc :
      forall j : nat,
        (j < n)%nat ->
        is_square
          (window_disc
            (List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
            (digit j)) = false.
    (** The positive QR certificate at the true multiple. *)
    Hypothesis Hwindow_qr :
      forall j : nat,
        (j < n)%nat ->
        is_square
          (UnOp.from
            (EccSpec.fw_z
              (List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
             +F Point.y
                  (PallasModel.repr
                    (Pallas.mul (window_scalar n j (digit j)) G)))) = true.
    (** The spec window point's x equals the multiple's x. *)
    Hypothesis Hwindow_x :
      forall (j : nat) (d u : Z),
        (j < n)%nat -> 0 <= d < 8 ->
        Point.x
          (EccSpec.fixed_window_point
            (List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
            d u) =
        Point.x
          (PallasModel.repr (Pallas.mul (window_scalar n j d) G)).

    (** ** Per-window full correctness from a satisfying assignment *)
    Lemma full_window_correct_gen (j : nat) (Hj : (j < n)%nat) :
      OrchardActionFixedBase.incomplete_additions_window_point Γ region
        (Z.of_nat j) =
      PallasModel.repr (Pallas.mul (window_scalar n j (digit j)) G).
    Proof using HG_on_curve HG_reduced Hdigit Hwindow_eq Hwindow_on_curve
      Hwindow_disc Hwindow_qr Hwindow_x.
      pose proof (Hdigit j Hj) as Hdj.
      pose proof (Hwindow_eq j Hj) as HF1.
      pose proof (Hwindow_on_curve j Hj) as Honc.
      pose proof (Hwindow_disc j Hj) as Hdisc.
      pose proof (Hwindow_qr j Hj) as HqrM.
      set (W := List.nth j spec_table OrchardActionFixedBase.fixed_window_default)
        in *.
      set (dj := digit j) in *.
      set (uj := List.nth j (OrchardActionInputs.read_us Γ region n) 0) in *.
      set (M := PallasModel.repr (Pallas.mul (window_scalar n j dj) G)) in *.
      assert (HxM : Point.x M =
                    EccSpec.fixed_interp (EccSpec.fw_coeffs W) dj (UnOp.from 1)).
      { unfold M. rewrite <- (Hwindow_x j dj uj Hj Hdj). reflexivity. }
      assert (Hx0 : UnOp.from (Point.x M) <> 0).
      { rewrite HxM. intro Hz.
        exact (oncurve_x_zero_absurd (EccSpec.fixed_window_point W dj uj) Honc Hz). }
      assert (HoncM : OrchardActionFixedBase.point_on_curve M).
      { exact (repr_mul_on_curve_gen G HG_on_curve (window_scalar n j dj) Hx0). }
      assert (HredM : UnOp.from (Point.y M) = Point.y M).
      { unfold M. apply repr_y_reduced. apply pallas_mul_reduced.
        exact HG_reduced. }
      pose proof (window_y_forced_of_disc W dj M HxM HoncM HqrM Hdisc HredM)
        as HF3.
      transitivity (fixed_window_point_canonical W dj).
      - rewrite HF1. apply (window_point_forced_of_disc W dj uj).
        + exact Honc.
        + exact Hdisc.
      - symmetry. exact HF3.
    Qed.

    Hypothesis HG_ne : G <> Pallas.identity.
    Hypothesis HG_order : Pallas.mul Pallas.pallas_q G = Pallas.identity.
    Hypothesis Hn_le : (n <= 85)%nat.

    (** ** The FULL per-base ladder-distinctness predicate

        All [count] incomplete edges (rows 1..count) at once, from the
        per-window facts (taken as the [Hwindow_full] hypothesis so
        each instantiation feeds its own [full_window_correct_gen]
        instance), the base
        accumulator (window 0) identified with [repr (mul S_1 G)] by
        [partial_sum_eq_mul_gen], and
        the range side by [window_scalar_range_bound]. *)
    Lemma ladder_distinct_precondition_holds_gen
        (Hwindow_full :
          forall j : nat,
            (j < n)%nat ->
            OrchardActionFixedBase.incomplete_additions_window_point Γ region
              (Z.of_nat j) =
            PallasModel.repr (Pallas.mul (window_scalar n j (digit j)) G))
        (count : nat) (Hcount : n = S (S count)) :
      OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ region
        1 count
        (OrchardActionFixedBase.incomplete_additions_window_point Γ region 0).
    Proof using HG_on_curve HG_reduced HG_ne HG_order Hdigit Hn_le.
      assert (Hacc0 :
        OrchardActionFixedBase.incomplete_additions_window_point Γ region 0 =
        PallasModel.repr
          (Pallas.mul (partial_sum (fun w => window_scalar n w (digit w)) 1)
            G)).
      { pose proof (partial_sum_eq_mul_gen digit 1
          (fun i Hi => Hwindow_full i ltac:(lia))) as HD2.
        cbn [OrchardActionFixedBase.complete_additions_output] in HD2.
        rewrite !EccSpec.point_add_identity_left in HD2.
        exact HD2. }
      rewrite Hacc0.
      refine (incomplete_distinct_of_range_bounds Γ
        region 1 G
        (fun i => window_scalar n (1 + i)%nat (digit (1 + i)%nat))
        (partial_sum (fun w => window_scalar n w (digit w)) 1) count
        HG_on_curve HG_reduced HG_ne HG_order _ _).
      - intros i Hi.
        cbn beta.
        replace (1 + Z.of_nat i) with (Z.of_nat (1 + i)) by lia.
        exact (Hwindow_full (1 + i)%nat ltac:(lia)).
      - intros i Hi.
        cbn beta.
        pose proof (window_scalar_range_bound n digit Hdigit Hn_le (1 + i)%nat
          ltac:(lia) ltac:(lia)) as [Hr1 Hr2].
        assert (Hsum :
          partial_sum (fun w => window_scalar n w (digit w)) 1 +
          partial_sum
            (fun m => window_scalar n (1 + m)%nat (digit (1 + m)%nat)) i =
          partial_sum (fun w => window_scalar n w (digit w)) (1 + i)%nat).
        { symmetry.
          exact (partial_sum_split_1
                   (fun w => window_scalar n w (digit w)) i). }
        split.
        + rewrite Hsum. exact Hr1.
        + rewrite Hsum. exact Hr2.
    Qed.
  End PerBaseChain.

  (** ** Per-window full correctness, SpendAuthG instance

      Per-window full correctness from a satisfying assignment: every
      SpendAuthG window point equals the [repr] of its Weierstrass multiple.
      The window equation and the on-curve fact come from the
      SpendAuthG-specific circuit
      lemmas ([spend_auth_g_window_correct] via [spend_auth_g_window_nth_error],
      [full_width_incomplete_region_window_on_curve]); the discriminant, sign
      and x certificates are the SpendAuthG [vm_compute] leaves. *)
  Lemma spend_auth_g_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ
      spend_auth_g_region (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j
          (EccSpec.window_digit
            (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) j))
        PallasGenerators.spend_auth_g_G).
  Proof.
    pose proof (OrchardActionFixedBase.spend_authority_fixed_base_facts Γ Hcircuit)
      as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    pose proof (OrchardActionFixedBase.holds_gates Γ Hcircuit) as Hgates.
    refine (full_window_correct_gen Γ spend_auth_g_region
      PallasGenerators.spend_auth_g_G
      PallasGenerators.spend_auth_g_on_curve
      PallasGenerators.spend_auth_g_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
      OrchardActionFixedBase.spend_auth_g_fixed_table
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      exact (OrchardActionFixedBase.spend_auth_g_window_correct Γ Hfacts Hgates i
        (List.nth i OrchardActionFixedBase.spend_auth_g_fixed_table
          OrchardActionFixedBase.fixed_window_default)
        (spend_auth_g_window_nth_error i Hi)).
    - (* Hwindow_on_curve *)
      intros i Hi.
      pose proof (OrchardActionFixedBase.full_width_incomplete_region_window_on_curve
        Γ (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        i Hfacts Hgates Hi) as H.
      rewrite (OrchardActionFixedBase.spend_auth_g_window_correct Γ Hfacts Hgates i
        (List.nth i OrchardActionFixedBase.spend_auth_g_fixed_table
          OrchardActionFixedBase.fixed_window_default)
        (spend_auth_g_window_nth_error i Hi)) in H.
      exact H.
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_spend_auth_g_all_Z i
        (EccSpec.window_digit
          (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
        Hi
        (window_digit_bound
          (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
        as Hdj.
      set (dj := EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
        in *.
      pose proof (SpendAuthGWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (full_table_entry_eq_mul i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (spend_auth_g_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** ** The FULL SpendAuthG ladder-distinctness predicate

      All 83 incomplete edges (rows 1..83) at once, through
      [ladder_distinct_precondition_holds_gen] fed with
      [spend_auth_g_full_window_correct].  The RK bridges consume it through
      [rk_{x,y}_correct_of_spend_auth_g_ladder_distinct]. *)
  Lemma spend_auth_g_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.spend_auth_g_ladder_distinct_precondition Γ.
  Proof.
    unfold OrchardActionFixedBase.spend_auth_g_ladder_distinct_precondition.
    change (OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ
      spend_auth_g_region 1 83
      (OrchardActionFixedBase.incomplete_additions_window_point Γ
        spend_auth_g_region 0)).
    refine (ladder_distinct_precondition_holds_gen Γ spend_auth_g_region
      PallasGenerators.spend_auth_g_G
      PallasGenerators.spend_auth_g_on_curve
      PallasGenerators.spend_auth_g_reduced
      85
      (fun i => EccSpec.window_digit
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
      (fun i _ => window_digit_bound
        (OrchardActionInputs.read_scalar_from_windows Γ spend_auth_g_region 85) i)
      PallasGenerators.spend_auth_g_ne_identity
      PallasGeneratorsOrder.spend_auth_g_order
      ltac:(lia)
      (fun j Hj => spend_auth_g_full_window_correct Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

End FixedBaseLadder.
