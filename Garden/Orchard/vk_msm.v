(** * Exact Halo2 [commit_lagrange] semantics and abstract MSM refinement

    The reusable machinery behind the 44 vk-commitment certificates.  The
    deployed keygen commits each fixed/permutation column [v] as
    [commit_lagrange v = sum_j v_j * g_lagrange_j + w]
    ([third-party/halo2/halo2_proofs/src/poly/commitment.rs];
    [Blind::default() = 1], so the
    [+ w] term is mandatory), with [g_lagrange] the inverse EC-FFT of the
    deterministic [Params::new(11)] generators [g].  Computing
    [g_lagrange] in-model is infeasible, so the certificates run over the
    raw [g] with the coefficient vector [c = intt v]:

    - [commit_lagrange] is the faithful spec: [g_lagrange j] is the closed
      iDFT form [n_inv * sum_m ((omega_inv^m)^j) g_m] — the mathematical
      output of [best_fft(g, ROOT_OF_UNITY_INV^(2^(S-k)), k)] scaled by
      [TWO_INV^k] — and is never computed;
    - [commit_lagrange_intt] (the linearity theorem) moves the commitment
      to the coefficient side, [commit_lagrange v = msm (intt v) g + w],
      by scalar-multiplication algebra over the Vesta group and reduction
      modulo the certified group order ([Garden/EllipticCurve/VestaOrder.v]);
    - [intt] computes the coefficients through a radix-2
      decimation-in-time FFT over the scalar field [F_{pallas_p}], proved
      pointwise equal to the Horner evaluations
      [Poly.eval v (omega_inv^m)] ([fft_spec]);
    - [msm_pippenger] is the computable bucket-method MSM the heavy
      certificates [vm_compute] (window 8, digit buckets, suffix-sum
      aggregation, shared-doubling Horner across the 32 windows), proved
      equal to the defining sum [msm] ([pippenger_correct]);
    - [commit_two_shards] packages the abstract chain for a leaf certificate:
      two
      Pippenger half-range checkpoints, the [intt] coefficient
      certificate, the [+ w] blind term, and the coordinate equality with
      the pinned literal.

    Scalars live modulo [pallas_p] (the Vesta group order); point
    coordinates modulo [pallas_q].  The definitions of [g_points] and
    [w_point] below mirror Halo2's exact domain separator and message
    schedule.  Their validity is an explicit premise [params_well_formed]
    of the algebraic refinement theorems, to be discharged by the sharded
    SRS provenance certificates rather than assumed globally.  This file
    sets no ambient [Prime] instance: scalar-field arithmetic is explicit
    [mod scalar_p], curve arithmetic goes through the [Vesta] wrappers. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Classes.Morphisms.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.GroupOrderCosets.
Require Import Garden.EllipticCurve.GroupOrderTight.
Require Import Garden.EllipticCurve.VestaOrder.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Orchard.vk.provenance.Srs.

Import ListNotations.

Global Open Scope list_scope.
Global Open Scope Z_scope.

Module VkMsm.

(** ** The scalar field and the inverse-FFT constants *)

Notation scalar_p := Primes.pallas_p.

(** [omega^{-1}] and [2048^{-1}] in [F_{pallas_p}], pasted literals
    certified by one multiplication each. *)
Definition omega_inv : Z :=
  12090924349175082951735926351876795190327940813373804453937320912039602712324.

Definition n_inv : Z :=
  28933887532810821781256079872166033615236414364518737688261339519836124872705.

Lemma omega_inv_spec : (PolyDomain.omega * omega_inv) mod scalar_p = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma n_inv_spec : (2048 * n_inv) mod scalar_p = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma scalar_p_big : 1 < scalar_p.
Proof. vm_compute. reflexivity. Qed.

Lemma omega_inv_range : 0 <= omega_inv < scalar_p.
Proof.
  split; [vm_compute; discriminate | vm_compute; reflexivity].
Qed.

Lemma n_inv_nonneg : 0 <= n_inv.
Proof. vm_compute. discriminate. Qed.

(** The half-order fact the FFT butterflies consume.  The closed
    square-and-multiply certificate is checked by the kernel. *)
Lemma omega_inv_half_fast_check :
  fast_pow_modulo_positive 1 omega_inv scalar_p 1024 = scalar_p - 1.
Proof. vm_compute. reflexivity. Qed.

(** The opacity barrier prevents conversion from evaluating the unreduced
    concrete power while the [modpow] certificate is transferred to the
    [Z.pow] spelling. *)
Strategy opaque [Z.pow Z.pow_pos].

Lemma omega_inv_half : (omega_inv ^ 1024) mod scalar_p = scalar_p - 1.
Proof.
  assert (Hp : 0 < scalar_p) by (pose proof scalar_p_big; lia).
  pose proof (fast_pow_correct scalar_p Hp 1024%positive 1 omega_inv) as H.
  rewrite Z.mul_1_l in H.
  rewrite <- H.
  exact omega_inv_half_fast_check.
Qed.

Strategy transparent [Z.pow Z.pow_pos].

(** ** Congruence modulo [scalar_p] as a setoid *)

Local Notation eqp := (eqm scalar_p).

Local Instance eqp_equiv : Equivalence eqp.
Proof. unfold eqm. constructor; congruence. Qed.
Local Instance add_eqp_mor : Proper (eqp ==> eqp ==> eqp) Z.add :=
  Zplus_eqm scalar_p.
Local Instance mul_eqp_mor : Proper (eqp ==> eqp ==> eqp) Z.mul :=
  Zmult_eqm scalar_p.
Local Instance opp_eqp_mor : Proper (eqp ==> eqp) Z.opp :=
  Zopp_eqm scalar_p.
Local Instance sub_eqp_mor : Proper (eqp ==> eqp ==> eqp) Z.sub.
Proof.
  intros u u' Hu v v' Hv. unfold eqm in *.
  rewrite Zminus_mod, Hu, Hv, <- Zminus_mod. reflexivity.
Qed.

(** Close an [eqp] goal whose sides are ring-equal after erasing the
    inner [mod scalar_p]s.  [Poly.eval] applications are frozen as opaque
    atoms first: their arguments carry [mod] subterms the setoid pass has
    no [Proper] chain for, and one unrewritable occurrence fails the whole
    rewrite. *)
Local Ltac eqp_ring :=
  repeat match goal with
         | |- context[Poly.eval ?l ?x] => set (Poly.eval l x) in *
         end;
  repeat setoid_rewrite (Zmod_eqm scalar_p);
  unfold eqm; f_equal; ring.

Lemma eqp_canon (u v : Z) :
  eqp u v -> u mod scalar_p = v mod scalar_p.
Proof. exact (fun h => h). Qed.

(** Exponentiation reads its base modulo [scalar_p]. *)
Lemma pow_mod_base (a n : Z) :
  0 <= n ->
  ((a mod scalar_p) ^ n) mod scalar_p = (a ^ n) mod scalar_p.
Proof.
  intros _. symmetry. apply Zpower_mod.
  pose proof scalar_p_big. lia.
Qed.

(** ** The Vesta point layer *)

Definition point := Vesta.point.
Definition identity : point := Vesta.identity.
Definition padd := Vesta.add.
Definition pmul := Vesta.mul.

Definition good (X : point) : Prop := Vesta.reduced X /\ Vesta.on_curve X.

Lemma good_identity : good identity.
Proof. split; exact I. Qed.

Lemma three_lt_q : 3 < Primes.pallas_q.
Proof. pose proof VestaOrder.eleven_lt_q. lia. Qed.

(** The group-law instances are consumed as fully applied terms: [apply]
    against the [Vesta.*] wrappers can send unification into evaluating
    concrete curve terms. *)
Lemma good_add (X Y : point) : good X -> good Y -> good (padd X Y).
Proof.
  intros [HrX HoX] [HrY HoY].
  exact (conj (Weierstrass.add_reduced Vesta.a X Y HrX HrY)
              (Weierstrass.add_on_curve Vesta.a Vesta.b X Y three_lt_q
                 HoX HoY)).
Qed.

Lemma good_mul (k : Z) (X : point) : good X -> good (pmul k X).
Proof.
  intros [HrX HoX].
  exact (conj (Weierstrass.mul_reduced Vesta.a k X HrX)
              (GroupOrderCosets.mul_on_curve Vesta.a Vesta.b
                 VestaOrder.eleven_lt_q k X HoX)).
Qed.

Lemma vadd_0_l (X : point) : padd identity X = X.
Proof. exact (Weierstrass.add_Infinity_l Vesta.a Vesta.b X). Qed.

Lemma vadd_0_r (X : point) : padd X identity = X.
Proof. exact (Weierstrass.add_Infinity_r Vesta.a Vesta.b X). Qed.

Lemma vadd_comm (X Y : point) :
  good X -> good Y -> padd X Y = padd Y X.
Proof.
  intros [_ HoX] [_ HoY].
  exact (Weierstrass.add_comm Vesta.a Vesta.b X Y HoX HoY).
Qed.

Lemma vadd_assoc (X Y Z : point) :
  good X -> good Y -> good Z ->
  padd (padd X Y) Z = padd X (padd Y Z).
Proof.
  intros [HrX HoX] [HrY HoY] [HrZ HoZ].
  exact (Weierstrass.add_assoc Vesta.a Vesta.b X Y Z
           VestaOrder.eleven_lt_q Vesta.nonsingular
           HrX HrY HrZ HoX HoY HoZ).
Qed.

Lemma vswap4 (A B C D : point) :
  good A -> good B -> good C -> good D ->
  padd (padd A B) (padd C D) = padd (padd A C) (padd B D).
Proof.
  intros [HrA HoA] [HrB HoB] [HrC HoC] [HrD HoD].
  exact (GroupOrderTight.add_swap4 Vesta.a Vesta.b
           VestaOrder.eleven_lt_q Vesta.nonsingular A B C D
           HrA HrB HrC HrD HoA HoB HoC HoD).
Qed.

Lemma vmul_0 (X : point) : pmul 0 X = identity.
Proof. reflexivity. Qed.

Lemma vmul_1 (X : point) : pmul 1 X = X.
Proof. reflexivity. Qed.

Lemma vmul_2 (X : point) : pmul 2 X = padd X X.
Proof. reflexivity. Qed.

Lemma vmul_identity (k : Z) : pmul k identity = identity.
Proof. exact (GroupOrderTight.mul_Infinity_r Vesta.a k). Qed.

Lemma vmul_add (i j : Z) (X : point) :
  good X -> pmul (i + j) X = padd (pmul i X) (pmul j X).
Proof.
  intros [HrX HoX].
  exact (Weierstrass.mul_add Vesta.a Vesta.b i j X
           VestaOrder.eleven_lt_q Vesta.nonsingular HrX HoX).
Qed.

Lemma vmul_mul (i j : Z) (X : point) :
  good X -> pmul (i * j) X = pmul i (pmul j X).
Proof.
  intros [HrX HoX].
  exact (Weierstrass.mul_mul Vesta.a Vesta.b i j X
           VestaOrder.eleven_lt_q Vesta.nonsingular HrX HoX).
Qed.

Lemma vmul_point_add (k : Z) (X Y : point) :
  0 <= k -> good X -> good Y ->
  pmul k (padd X Y) = padd (pmul k X) (pmul k Y).
Proof.
  intros Hk [HrX HoX] [HrY HoY].
  exact (GroupOrderTight.mul_point_add Vesta.a Vesta.b
           VestaOrder.eleven_lt_q Vesta.nonsingular k X Y
           Hk HrX HrY HoX HoY).
Qed.

(** Scalar reduction modulo the certified Vesta group order
    ([scalar_p = Vesta.vesta_q]). *)
Lemma vmul_mod (X : point) (n : Z) :
  good X -> pmul (n mod scalar_p) X = pmul n X.
Proof.
  intros [HrX HoX].
  exact (VestaOrder.vesta_mul_mod X n HrX HoX).
Qed.

(** ** Point sums and the defining multi-scalar sum *)

Definition psum (l : list point) : point := List.fold_right padd identity l.

Lemma psum_good (l : list point) : Forall good l -> good (psum l).
Proof.
  induction l as [| x l IH]; intros Hl; [exact good_identity |].
  inversion Hl; subst.
  apply good_add; [assumption | apply IH; assumption].
Qed.

Fixpoint msm (cs : list Z) (gs : list point) : point :=
  match cs, gs with
  | c :: cs', g :: gs' => padd (pmul c g) (msm cs' gs')
  | _, _ => identity
  end.

Lemma msm_nil_l (gs : list point) : msm [] gs = identity.
Proof. destruct gs; reflexivity. Qed.

Lemma msm_good (cs : list Z) (gs : list point) :
  Forall good gs -> good (msm cs gs).
Proof.
  revert gs. induction cs as [| c cs IH]; intros gs Hgs.
  - rewrite msm_nil_l. exact good_identity.
  - destruct gs as [| g gs]; [exact good_identity |].
    inversion Hgs; subst.
    apply good_add; [apply good_mul; assumption | apply IH; assumption].
Qed.

Lemma msm_app (cs1 cs2 : list Z) (gs1 gs2 : list point) :
  List.length cs1 = List.length gs1 ->
  Forall good gs1 -> Forall good gs2 ->
  msm (cs1 ++ cs2) (gs1 ++ gs2) = padd (msm cs1 gs1) (msm cs2 gs2).
Proof.
  revert gs1. induction cs1 as [| c cs1 IH]; intros gs1 Hlen Hg1 Hg2.
  - destruct gs1; [| discriminate].
    cbn [app]. rewrite msm_nil_l, vadd_0_l. reflexivity.
  - destruct gs1 as [| g gs1]; [discriminate |].
    inversion Hg1; subst.
    cbn [app msm].
    rewrite IH; [| cbn in Hlen; lia | assumption | assumption].
    rewrite vadd_assoc;
      [reflexivity
      | apply good_mul; assumption
      | apply msm_good; assumption
      | apply msm_good; assumption].
Qed.

Lemma msm_zeros (cs : list Z) (gs : list point) :
  Forall (fun c => c = 0) cs -> msm cs gs = identity.
Proof.
  revert gs. induction cs as [| c cs IH]; intros gs Hcs.
  - rewrite msm_nil_l. reflexivity.
  - destruct gs as [| g gs]; [reflexivity |].
    inversion Hcs; subst.
    cbn [msm]. rewrite vmul_0, vadd_0_l. apply IH. assumption.
Qed.

Lemma forall_map_zero {A : Type} (l : list A) :
  Forall (fun c => c = 0) (List.map (fun _ => 0) l).
Proof. induction l; cbn; constructor; auto. Qed.

(** Pointwise addition of scalar vectors distributes over [msm]. *)
Fixpoint zipadd (u v : list Z) : list Z :=
  match u, v with
  | x :: u', y :: v' => (x + y) :: zipadd u' v'
  | _, _ => []
  end.

Lemma zipadd_map {A : Type} (f1 f2 : A -> Z) (l : list A) :
  zipadd (List.map f1 l) (List.map f2 l)
  = List.map (fun x => f1 x + f2 x) l.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite IH]; reflexivity. Qed.

Lemma msm_zipadd (u v : list Z) (gs : list point) :
  List.length u = List.length v ->
  Forall good gs ->
  msm (zipadd u v) gs = padd (msm u gs) (msm v gs).
Proof.
  revert v gs. induction u as [| x u IH]; intros v gs Hlen Hgs.
  - destruct v; [| discriminate].
    cbn [zipadd]. rewrite !msm_nil_l, vadd_0_l. reflexivity.
  - destruct v as [| y v]; [discriminate |].
    destruct gs as [| g gs]; [reflexivity |].
    inversion Hgs; subst.
    cbn [zipadd msm].
    rewrite IH; [| cbn in Hlen; lia | assumption].
    rewrite (vmul_add x y g) by assumption.
    apply vswap4;
      try (apply good_mul; assumption);
      try (apply msm_good; assumption).
Qed.

(** A shared scalar factor moves through [msm]. *)
Lemma msm_map_mul (s : Z) (cs : list Z) (gs : list point) :
  0 <= s ->
  Forall good gs ->
  pmul s (msm cs gs) = msm (List.map (Z.mul s) cs) gs.
Proof.
  revert gs. induction cs as [| c cs IH]; intros gs Hs Hgs.
  - cbn [List.map]. rewrite !msm_nil_l. apply vmul_identity.
  - destruct gs as [| g gs]; [apply vmul_identity |].
    inversion Hgs; subst.
    cbn [List.map msm].
    rewrite vmul_point_add;
      [| assumption
      | apply good_mul; assumption
      | apply msm_good; assumption].
    rewrite <- (vmul_mul s c g) by assumption.
    rewrite IH; [reflexivity | assumption | assumption].
Qed.

(** [msm] only sees scalars modulo [scalar_p]. *)
Lemma msm_ext_mod (cs cs' : list Z) (gs : list point) :
  List.length cs = List.length cs' ->
  (forall m : nat, (m < List.length cs)%nat ->
    List.nth m cs 0 mod scalar_p = List.nth m cs' 0 mod scalar_p) ->
  Forall good gs ->
  msm cs gs = msm cs' gs.
Proof.
  revert cs' gs. induction cs as [| c cs IH]; intros cs' gs Hlen Heq Hgs.
  - destruct cs'; [reflexivity | discriminate].
  - destruct cs' as [| c' cs']; [discriminate |].
    destruct gs as [| g gs]; [reflexivity |].
    inversion Hgs; subst.
    cbn [msm].
    assert (Hg : good g) by assumption.
    assert (Hhead : pmul c g = pmul c' g).
    { rewrite <- (vmul_mod g c Hg), <- (vmul_mod g c' Hg).
      assert (Hc0 : c mod scalar_p = c' mod scalar_p)
        by exact (Heq O ltac:(cbn; lia)).
      rewrite Hc0. reflexivity. }
    rewrite Hhead.
    f_equal.
    apply IH; [cbn in Hlen; lia | | assumption].
    intros m Hm. exact (Heq (S m) ltac:(cbn [List.length]; lia)).
Qed.

(** ** Exact [Params::new(11)] SRS semantics

    Halo2 hashes [0x00 || LE32(i)] for [g_i], then the one-byte messages
    [0x01] and [0x02] for [w] and [u].  Only [g] and [w] participate in
    [commit_lagrange]. *)

Definition g_points : list point :=
  List.map
    (fun index =>
      GroupHashVesta.group_hash VkSrs.domain_prefix (VkSrs.g_message index))
    (List.seq 0 2048).

Definition w_point : point :=
  GroupHashVesta.group_hash VkSrs.domain_prefix [1].

Definition u_point : point :=
  GroupHashVesta.group_hash VkSrs.domain_prefix [2].

Lemma g_points_length : List.length g_points = 2048%nat.
Proof.
  unfold g_points. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

Definition params_well_formed : Prop :=
  Forall good g_points /\ good w_point.

Lemma g_points_good : params_well_formed -> Forall good g_points.
Proof. exact (@proj1 _ _). Qed.

Lemma w_point_good : params_well_formed -> good w_point.
Proof. exact (@proj2 _ _). Qed.

(** ** The faithful commitment spec

    [g_lagrange j = n_inv * sum_m ((omega_inv^m)^j) g_m] — the closed
    iDFT form of [best_fft(g, omega_inv, 11)] scaled by [TWO_INV^11].
    Spec only; no certificate ever computes it. *)

Fixpoint pow_list_from (t y : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => t :: pow_list_from ((t * y) mod scalar_p) y n'
  end.

Lemma pow_list_from_length (t y : Z) (n : nat) :
  List.length (pow_list_from t y n) = n.
Proof.
  revert t. induction n as [| n IH]; intros t; cbn; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(** Entry [m] is [t * y^m] reduced, provided [t] is reduced. *)
Lemma pow_list_from_nth (t y : Z) (n m : nat) :
  (m < n)%nat ->
  t mod scalar_p = t ->
  List.nth m (pow_list_from t y n) 0 = (t * y ^ Z.of_nat m) mod scalar_p.
Proof.
  revert t m. induction n as [| n IH]; intros t m Hm Ht; [lia |].
  destruct m as [| m].
  - cbn [pow_list_from List.nth].
    rewrite Z.pow_0_r, Z.mul_1_r. symmetry. exact Ht.
  - cbn [pow_list_from List.nth].
    rewrite IH; [| lia | apply Zmod_mod].
    apply eqp_canon.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    eqp_ring.
Qed.

Definition omega_inv_pows : list Z := pow_list_from 1 omega_inv 2048.

Lemma omega_inv_pows_length : List.length omega_inv_pows = 2048%nat.
Proof. apply pow_list_from_length. Qed.

Lemma omega_inv_pows_nth (m : nat) :
  (m < 2048)%nat ->
  List.nth m omega_inv_pows 0 = (omega_inv ^ Z.of_nat m) mod scalar_p.
Proof.
  intros Hm.
  unfold omega_inv_pows.
  rewrite pow_list_from_nth;
    [| exact Hm | apply Z.mod_1_l; exact scalar_p_big].
  f_equal. ring.
Qed.

Definition g_lagrange (j : nat) : point :=
  pmul n_inv
    (msm (List.map (fun y => (y ^ Z.of_nat j) mod scalar_p) omega_inv_pows)
       g_points).

Definition g_lagrange_list : list point := List.map g_lagrange (List.seq 0 2048).

(** Halo2's commitment of a full 2048-row Lagrange column with an explicit
    blinding scalar. *)
Definition commit_lagrange_with_blind (v : list Z) (blind : Z) : point :=
  padd (msm v g_lagrange_list) (pmul blind w_point).

(** The key-generation call uses [Blind::default() = 1]. *)
Definition commit_lagrange (v : list Z) : point :=
  commit_lagrange_with_blind v 1.

(** ** The scalar-side inverse NTT *)

(** Split a list into even- and odd-position elements. *)
Fixpoint deinter (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | x :: l' => let '(e, o) := deinter l' in (x :: o, e)
  end.

Definition evens (l : list Z) : list Z := fst (deinter l).
Definition odds (l : list Z) : list Z := snd (deinter l).

Lemma deinter_cons (x : Z) (l : list Z) :
  evens (x :: l) = x :: odds l /\ odds (x :: l) = evens l.
Proof.
  unfold evens, odds. cbn [deinter].
  destruct (deinter l) as [e o]. cbn. split; reflexivity.
Qed.

Lemma deinter_length (l : list Z) (n : nat) :
  List.length l = (2 * n)%nat ->
  List.length (evens l) = n /\ List.length (odds l) = n.
Proof.
  revert l. induction n as [| n IH]; intros l Hl.
  - destruct l; [cbn; split; reflexivity | cbn in Hl; lia].
  - destruct l as [| x l]; [cbn in Hl; lia |].
    destruct l as [| y l]; [cbn in Hl; lia |].
    destruct (IH l) as [He Ho]; [cbn in Hl; lia |].
    destruct (deinter_cons x (y :: l)) as [Hex Hox].
    destruct (deinter_cons y l) as [Hey Hoy].
    rewrite Hex, Hox, Hey, Hoy.
    cbn [List.length].
    split; [rewrite He; reflexivity | rewrite Ho; reflexivity].
Qed.

(** Horner split at the reduced square point:
    [eval l x = eval (evens l) (x^2) + x * eval (odds l) (x^2)]. *)
Lemma eval_split (l : list Z) (x : Z) :
  Poly.eval (p := scalar_p) l x
  = (Poly.eval (p := scalar_p) (evens l) ((x * x) mod scalar_p)
     + x * Poly.eval (p := scalar_p) (odds l) ((x * x) mod scalar_p))
      mod scalar_p.
Proof.
  induction l as [| a l IH].
  - cbn. rewrite Z.mul_0_r, ?Z.add_0_r, Zmod_0_l. reflexivity.
  - destruct (deinter_cons a l) as [He Ho].
    rewrite He, Ho.
    cbn [Poly.eval].
    rewrite IH.
    apply eqp_canon.
    eqp_ring.
Qed.

(** The butterfly pass: entry [j] of the two output halves is
    [e_j +- t*w^j*o_j] modulo [scalar_p]. *)
Fixpoint bfly (w t : Z) (es os : list Z) : list Z * list Z :=
  match es, os with
  | e :: es', o :: os' =>
      let u := (t * o) mod scalar_p in
      let '(hs, ls) := bfly w ((t * w) mod scalar_p) es' os' in
      (((e + u) mod scalar_p) :: hs, ((e - u) mod scalar_p) :: ls)
  | _, _ => ([], [])
  end.

Lemma bfly_length (w t : Z) (es os : list Z) :
  List.length es = List.length os ->
  List.length (fst (bfly w t es os)) = List.length es /\
  List.length (snd (bfly w t es os)) = List.length es.
Proof.
  revert t os. induction es as [| e es IH]; intros t os Hlen.
  - cbn. split; reflexivity.
  - destruct os as [| o os]; [discriminate |].
    cbn [bfly].
    destruct (IH ((t * w) mod scalar_p) os ltac:(cbn in Hlen; lia))
      as [Hf Hs].
    destruct (bfly w ((t * w) mod scalar_p) es os) as [hs ls].
    cbn [fst snd List.length] in *.
    split; f_equal; assumption.
Qed.

Lemma bfly_nth (w t : Z) (es os : list Z) (j : nat) :
  List.length es = List.length os ->
  (j < List.length es)%nat ->
  List.nth j (fst (bfly w t es os)) 0
    = (List.nth j es 0 + t * w ^ Z.of_nat j * List.nth j os 0) mod scalar_p /\
  List.nth j (snd (bfly w t es os)) 0
    = (List.nth j es 0 - t * w ^ Z.of_nat j * List.nth j os 0) mod scalar_p.
Proof.
  revert t os j. induction es as [| e es IH]; intros t os j Hlen Hj;
    [cbn in Hj; lia |].
  destruct os as [| o os]; [discriminate |].
  cbn [bfly].
  destruct (bfly w ((t * w) mod scalar_p) es os) as [hs ls] eqn:Hbf.
  destruct j as [| j].
  - cbn [fst snd List.nth].
    rewrite Z.pow_0_r.
    split; apply eqp_canon; eqp_ring.
  - cbn [fst snd List.nth].
    assert (Hj' : (j < List.length es)%nat) by (cbn in Hj; lia).
    destruct (IH ((t * w) mod scalar_p) os j ltac:(cbn in Hlen; lia) Hj')
      as [Hf Hs].
    rewrite Hbf in Hf, Hs. cbn [fst snd] in Hf, Hs.
    rewrite Hf, Hs.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    split; apply eqp_canon; eqp_ring.
Qed.

(** The radix-2 decimation-in-time FFT over [F_{scalar_p}]. *)
Fixpoint fft (k : nat) (w : Z) (l : list Z) : list Z :=
  match k with
  | O => [(List.hd 0 l) mod scalar_p]
  | S k' =>
      let e := fft k' ((w * w) mod scalar_p) (evens l) in
      let o := fft k' ((w * w) mod scalar_p) (odds l) in
      let '(hs, ls) := bfly w 1 e o in
      hs ++ ls
  end.

Lemma fft_length (k : nat) (w : Z) (l : list Z) :
  List.length l = (2 ^ k)%nat ->
  List.length (fft k w l) = (2 ^ k)%nat.
Proof.
  revert w l. induction k as [| k IH]; intros w l Hl; [reflexivity |].
  cbn [fft].
  assert (Hl2 : List.length l = (2 * 2 ^ k)%nat) by (rewrite Hl; cbn; lia).
  destruct (deinter_length l (2 ^ k) Hl2) as [He Ho].
  pose proof (IH ((w * w) mod scalar_p) (evens l) He) as Hfe.
  pose proof (IH ((w * w) mod scalar_p) (odds l) Ho) as Hfo.
  destruct (bfly_length w 1
              (fft k ((w * w) mod scalar_p) (evens l))
              (fft k ((w * w) mod scalar_p) (odds l))
              ltac:(rewrite Hfe, Hfo; reflexivity)) as [Hbf Hbs].
  destruct (bfly w 1 (fft k ((w * w) mod scalar_p) (evens l))
              (fft k ((w * w) mod scalar_p) (odds l))) as [hs ls].
  cbn [fst snd] in *.
  rewrite List.length_app, Hbf, Hbs, Hfe.
  cbn [Nat.pow]. lia.
Qed.

(** Squaring the evaluation point matches squaring the root. *)
Lemma sq_point (w : Z) (m : nat) :
  (((w ^ Z.of_nat m) mod scalar_p) * ((w ^ Z.of_nat m) mod scalar_p))
    mod scalar_p
  = (((w * w) mod scalar_p) ^ Z.of_nat m) mod scalar_p.
Proof.
  rewrite pow_mod_base by lia.
  rewrite <- Zmult_mod.
  rewrite Z.pow_mul_l.
  reflexivity.
Qed.

(** FFT correctness: entry [m] is the Horner evaluation at [w^m], under
    the half-order hypothesis [w^(2^(k-1)) = -1 mod p]. *)
Lemma fft_spec (k : nat) (w : Z) (l : list Z) :
  List.length l = (2 ^ k)%nat ->
  (k = O \/ (w ^ Z.of_nat (2 ^ (k - 1)) mod scalar_p) = scalar_p - 1) ->
  forall m : nat,
  (m < 2 ^ k)%nat ->
  List.nth m (fft k w l) 0
  = Poly.eval (p := scalar_p) l ((w ^ Z.of_nat m) mod scalar_p).
Proof.
  revert w l. induction k as [| k IH]; intros w l Hl Hw m Hm.
  - (* k = 0 *)
    assert (Hm0 : m = O) by (cbn in Hm; lia).
    subst m.
    destruct l as [| a l]; [cbn in Hl; lia |].
    destruct l; [| cbn in Hl; lia].
    cbn [fft List.nth List.hd Poly.eval].
    apply eqp_canon. eqp_ring.
  - (* k = S k' *)
    destruct Hw as [Hw | Hw]; [discriminate |].
    replace (S k - 1)%nat with k in Hw by lia.
    cbn [fft].
    assert (Hl2 : List.length l = (2 * 2 ^ k)%nat) by (rewrite Hl; cbn; lia).
    destruct (deinter_length l (2 ^ k) Hl2) as [He Ho].
    set (w2 := (w * w) mod scalar_p) in *.
    assert (Hfe : List.length (fft k w2 (evens l)) = (2 ^ k)%nat)
      by (apply fft_length; exact He).
    assert (Hfo : List.length (fft k w2 (odds l)) = (2 ^ k)%nat)
      by (apply fft_length; exact Ho).
    (* Propagate the half-order fact to the squared root. *)
    assert (Hw2 : k = O \/
      (w2 ^ Z.of_nat (2 ^ (k - 1)) mod scalar_p) = scalar_p - 1).
    { destruct k as [| k']; [left; reflexivity | right].
      replace (S k' - 1)%nat with k' by lia.
      unfold w2.
      rewrite pow_mod_base by lia.
      rewrite Z.pow_mul_l.
      rewrite <- Z.pow_add_r by lia.
      replace (Z.of_nat (2 ^ k') + Z.of_nat (2 ^ k'))
        with (Z.of_nat (2 ^ S k')) by (cbn [Nat.pow]; lia).
      exact Hw. }
    (* The (w^(2^k) + 1) multiple that kills the second-half shift. *)
    assert (Hp1 : (w ^ Z.of_nat (2 ^ k) + 1) mod scalar_p = 0).
    { rewrite Zplus_mod, Hw, (Z.mod_1_l scalar_p scalar_p_big).
      replace (scalar_p - 1 + 1) with scalar_p by ring.
      apply Z_mod_same_full. }
    destruct (bfly_length w 1 (fft k w2 (evens l)) (fft k w2 (odds l))
                ltac:(rewrite Hfe, Hfo; reflexivity)) as [Hlh Hll].
    pose proof (fun j Hj =>
      bfly_nth w 1 (fft k w2 (evens l)) (fft k w2 (odds l)) j
        ltac:(rewrite Hfe, Hfo; reflexivity) Hj) as Hnth.
    destruct (bfly w 1 (fft k w2 (evens l)) (fft k w2 (odds l)))
      as [hs ls] eqn:Hbf.
    cbn [fst snd] in Hlh, Hll, Hnth.
    destruct (Nat.lt_ge_cases m (2 ^ k)) as [Hmlt | Hmge].
    + (* first half *)
      rewrite app_nth1 by (rewrite Hlh, Hfe; exact Hmlt).
      destruct (Hnth m ltac:(rewrite Hfe; exact Hmlt)) as [Hf _].
      rewrite Hf.
      rewrite (IH w2 (evens l) He Hw2 m ltac:(exact Hmlt)).
      rewrite (IH w2 (odds l) Ho Hw2 m ltac:(exact Hmlt)).
      rewrite (eval_split l ((w ^ Z.of_nat m) mod scalar_p)).
      rewrite sq_point.
      fold w2.
      apply eqp_canon. eqp_ring.
    + (* second half *)
      set (j := (m - 2 ^ k)%nat).
      assert (Hjlt : (j < 2 ^ k)%nat)
        by (unfold j; clear -Hm Hmge; cbn [Nat.pow] in Hm; lia).
      assert (Hmj : m = (j + 2 ^ k)%nat)
        by (unfold j; clear -Hmge; lia).
      rewrite app_nth2 by (rewrite Hlh, Hfe; exact Hmge).
      rewrite Hlh, Hfe.
      fold j.
      destruct (Hnth j ltac:(rewrite Hfe; exact Hjlt)) as [_ Hs].
      rewrite Hs.
      rewrite (IH w2 (evens l) He Hw2 j Hjlt).
      rewrite (IH w2 (odds l) Ho Hw2 j Hjlt).
      rewrite (eval_split l ((w ^ Z.of_nat m) mod scalar_p)).
      rewrite sq_point.
      fold w2.
      (* The squared point has period 2^k. *)
      assert (Hper : (w2 ^ Z.of_nat m) mod scalar_p
                     = (w2 ^ Z.of_nat j) mod scalar_p).
      { rewrite Hmj.
        rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
        rewrite Zmult_mod.
        assert (Hsq1 : (w2 ^ Z.of_nat (2 ^ k)) mod scalar_p = 1).
        { unfold w2.
          rewrite pow_mod_base by lia.
          rewrite Z.pow_mul_l.
          rewrite Zmult_mod, Hw.
          replace ((scalar_p - 1) * (scalar_p - 1))
            with (1 + (scalar_p - 2) * scalar_p) by ring.
          rewrite Z_mod_plus_full.
          apply Z.mod_1_l. exact scalar_p_big. }
        rewrite Hsq1, Z.mul_1_r, Zmod_mod.
        reflexivity. }
      rewrite Hper.
      (* [w^m = w^j * w^(2^k) = -w^j] modulo [scalar_p]. *)
      set (Ej := Poly.eval (p := scalar_p) (evens l)
                   ((w2 ^ Z.of_nat j) mod scalar_p)).
      set (Oj := Poly.eval (p := scalar_p) (odds l)
                   ((w2 ^ Z.of_nat j) mod scalar_p)).
      rewrite (eqp_canon
                 (Ej + ((w ^ Z.of_nat m) mod scalar_p) * Oj)
                 (Ej + w ^ Z.of_nat m * Oj))
        by eqp_ring.
      apply (proj2 (Z.cong_iff_0 _ _ scalar_p)).
      rewrite Hmj.
      rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
      replace (Ej - 1 * w ^ Z.of_nat j * Oj
               - (Ej + w ^ Z.of_nat j * w ^ Z.of_nat (2 ^ k) * Oj))
        with ((-1 * (w ^ Z.of_nat j * Oj))
              * (w ^ Z.of_nat (2 ^ k) + 1))
        by ring.
      rewrite Zmult_mod, Hp1, Z.mul_0_r.
      apply Zmod_0_l.
Qed.

(** With the correctness and length facts in place, [fft] is made opaque
    to every conversion engine: at the concrete [k = 11] a conversion
    unfolding [fft] on a symbolic list doubles the term at each level.
    [vm_compute] in the leaf certificates is unaffected by [Strategy]. *)
Strategy opaque [fft].

(** ** The inverse NTT and its pointwise reading

    The [intt] lemmas are stated through helpers over an abstract list and
    composed as proof terms: running tactic unification against a goal
    that contains the concrete [fft 11] application diverges (each of the
    eleven levels doubles the term). *)

Definition intt (v : list Z) : list Z :=
  List.map (fun x => (n_inv * x) mod scalar_p) (fft 11 omega_inv v).

Lemma map_mod_length (l : list Z) :
  List.length (List.map (fun x => (n_inv * x) mod scalar_p) l)
  = List.length l.
Proof. apply List.length_map. Qed.

Lemma map_mod_range (l : list Z) :
  Forall (fun c => 0 <= c < scalar_p)
    (List.map (fun x => (n_inv * x) mod scalar_p) l).
Proof.
  induction l as [| x l IH]; cbn [List.map]; constructor;
    [apply Z.mod_pos_bound; pose proof scalar_p_big; lia | exact IH].
Qed.

Lemma map_mod_nth (l : list Z) (m : nat) :
  (m < List.length l)%nat ->
  List.nth m (List.map (fun x => (n_inv * x) mod scalar_p) l) 0
  = (n_inv * List.nth m l 0) mod scalar_p.
Proof.
  intros Hm.
  rewrite List.nth_indep with (d' := ((n_inv * 0) mod scalar_p))
    by (rewrite List.length_map; exact Hm).
  exact (List.map_nth (fun x : Z => (n_inv * x) mod scalar_p) l 0 m).
Qed.

Lemma intt_length (v : list Z) :
  List.length v = 2048%nat -> List.length (intt v) = 2048%nat.
Proof.
  intros Hv.
  exact (eq_trans (map_mod_length (fft 11 omega_inv v))
           (fft_length 11 omega_inv v Hv)).
Qed.

Lemma intt_range (v : list Z) :
  Forall (fun c => 0 <= c < scalar_p) (intt v).
Proof.
  exact (map_mod_range (fft 11 omega_inv v)).
Qed.

Lemma intt_nth (v : list Z) (m : nat) :
  List.length v = 2048%nat ->
  (m < 2048)%nat ->
  List.nth m (intt v) 0
  = (n_inv * Poly.eval (p := scalar_p) v
       ((omega_inv ^ Z.of_nat m) mod scalar_p)) mod scalar_p.
Proof.
  intros Hv Hm.
  assert (Hhalf : 11%nat = O \/
    (omega_inv ^ Z.of_nat (2 ^ (11 - 1)) mod scalar_p) = scalar_p - 1)
    by (right; exact omega_inv_half).
  exact (eq_trans
    (map_mod_nth (fft 11 omega_inv v) m
       (eq_ind_r (fun n : nat => (m < n)%nat) Hm
          (fft_length 11 omega_inv v Hv)))
    (f_equal (fun z : Z => (n_inv * z) mod scalar_p)
       (fft_spec 11 omega_inv v Hv Hhalf m Hm))).
Qed.

(** ** The linearity theorem: from [g_lagrange] to coefficients over [g] *)

(** The scalar collected per SRS base [g_m] once every
    [v_j * g_lagrange_j] summand is expanded: the inner product
    [sum_j v_j * n_inv * (y_m^{j0+j})] over the tail of [v]. *)
Fixpoint dot (v : list Z) (y : Z) (j : nat) : Z :=
  match v with
  | [] => 0
  | a :: v' =>
      a * n_inv * ((y ^ Z.of_nat j) mod scalar_p) + dot v' y (S j)
  end.

Lemma msm_glag_collect (v : list Z) (j0 : nat) :
  params_well_formed ->
  Forall (fun s => 0 <= s) v ->
  msm v (List.map g_lagrange (List.seq j0 (List.length v)))
  = msm (List.map (fun y => dot v y j0) omega_inv_pows) g_points.
Proof.
  revert j0. induction v as [| a v IH]; intros j0 Hparams Hv.
  - cbn [List.length List.seq List.map]. rewrite msm_nil_l.
    symmetry. apply msm_zeros.
    apply Forall_forall. intros c Hc.
    apply in_map_iff in Hc. destruct Hc as (y & Hc & _). subst c.
    reflexivity.
  - inversion Hv; subst.
    cbn [List.length List.seq List.map msm].
    rewrite (IH (S j0) Hparams) by assumption.
    unfold g_lagrange at 1.
    rewrite <- (vmul_mul a n_inv
      (msm (List.map (fun y => (y ^ Z.of_nat j0) mod scalar_p)
              omega_inv_pows) g_points))
      by (apply msm_good; exact (g_points_good Hparams)).
    rewrite (msm_map_mul (a * n_inv)
      (List.map (fun y => (y ^ Z.of_nat j0) mod scalar_p) omega_inv_pows)
      g_points)
      by (first [apply Z.mul_nonneg_nonneg;
                 [assumption | exact n_inv_nonneg]
                | exact (g_points_good Hparams)]).
    rewrite List.map_map.
    rewrite <- msm_zipadd;
      [ | rewrite !List.length_map; reflexivity
        | exact (g_points_good Hparams)].
    rewrite zipadd_map.
    f_equal.
Qed.

Lemma dot_eval (v : list Z) (y : Z) (j0 : nat) :
  eqp (dot v y j0)
      (n_inv * ((y ^ Z.of_nat j0) mod scalar_p)
       * Poly.eval (p := scalar_p) v y).
Proof.
  revert j0. induction v as [| a v IH]; intros j0.
  - cbn [dot Poly.eval]. rewrite Z.mul_0_r. reflexivity.
  - cbn [dot Poly.eval].
    transitivity (a * n_inv * ((y ^ Z.of_nat j0) mod scalar_p)
                  + n_inv * ((y ^ Z.of_nat (S j0)) mod scalar_p)
                    * Poly.eval (p := scalar_p) v y).
    { apply add_eqp_mor; [reflexivity | exact (IH (S j0))]. }
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    eqp_ring.
Qed.

(** The linearity theorem: the commitment over [g_lagrange]
    equals the [intt]-coefficient MSM over the raw certified [g], for any
    blinding scalar. *)
Theorem commit_lagrange_intt_with_blind (v : list Z) (blind : Z) :
  params_well_formed ->
  List.length v = 2048%nat ->
  Forall (fun s => 0 <= s) v ->
  commit_lagrange_with_blind v blind =
    padd (msm (intt v) g_points) (pmul blind w_point).
Proof.
  intros Hparams Hlen Hv.
  unfold commit_lagrange_with_blind, g_lagrange_list.
  apply (f_equal (fun X : point => padd X (pmul blind w_point))).
  rewrite <- Hlen.
  rewrite (msm_glag_collect v 0 Hparams Hv).
  apply msm_ext_mod.
  - rewrite List.length_map, omega_inv_pows_length.
    rewrite (intt_length v Hlen). reflexivity.
  - intros m Hm.
    rewrite List.length_map, omega_inv_pows_length in Hm.
    rewrite List.nth_indep with (d' := dot v 0 0)
      by (rewrite List.length_map, omega_inv_pows_length; exact Hm).
    rewrite (List.map_nth (fun y => dot v y 0) omega_inv_pows 0 m).
    rewrite (omega_inv_pows_nth m Hm).
    rewrite (intt_nth v m Hlen Hm).
    rewrite Zmod_mod.
    pose proof (dot_eval v ((omega_inv ^ Z.of_nat m) mod scalar_p) 0)
      as Hd.
    rewrite Z.pow_0_r, (Z.mod_1_l scalar_p scalar_p_big), Z.mul_1_r
      in Hd.
    exact Hd.
  - exact (g_points_good Hparams).
Qed.

(** Specialization to the exact key-generation call
    [Blind::default() = 1]. *)
Theorem commit_lagrange_intt (v : list Z) :
  params_well_formed ->
  List.length v = 2048%nat ->
  Forall (fun s => 0 <= s) v ->
  commit_lagrange v = padd (msm (intt v) g_points) w_point.
Proof.
  intros Hparams Hlen Hv.
  unfold commit_lagrange.
  rewrite (commit_lagrange_intt_with_blind v 1 Hparams Hlen Hv).
  rewrite vmul_1. reflexivity.
Qed.

(** ** The Pippenger checker *)

(** Base-256 digits, least significant first. *)
Fixpoint digits_go (fuel : nat) (c : Z) : list Z :=
  match fuel with
  | O => []
  | S f => (c mod 256) :: digits_go f (c / 256)
  end.

Definition digits32 (c : Z) : list Z := digits_go 32 c.

Fixpoint recomp (ds : list Z) : Z :=
  match ds with
  | [] => 0
  | d :: ds' => d + 256 * recomp ds'
  end.

Lemma digits_go_length (fuel : nat) (c : Z) :
  List.length (digits_go fuel c) = fuel.
Proof.
  revert c. induction fuel as [| f IH]; intros c; cbn; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma digits_go_bound (fuel : nat) (c : Z) :
  Forall (fun d => 0 <= d < 256) (digits_go fuel c).
Proof.
  revert c. induction fuel as [| f IH]; intros c; cbn; constructor.
  - apply Z.mod_pos_bound. lia.
  - apply IH.
Qed.

Lemma digits_go_recomp (fuel : nat) (c : Z) :
  0 <= c < 256 ^ Z.of_nat fuel ->
  recomp (digits_go fuel c) = c.
Proof.
  revert c. induction fuel as [| f IH]; intros c Hc.
  - cbn in Hc |- *. lia.
  - cbn [digits_go recomp].
    rewrite IH.
    + pose proof (Z.div_mod c 256 ltac:(lia)) as Hdm. lia.
    + split; [apply Z.div_pos; lia |].
      apply Z.div_lt_upper_bound; [lia |].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
      lia.
Qed.

(** Buckets: the sum of the bases whose digit equals the bucket value. *)
Definition bucket (pairs : list (Z * point)) (vv : Z) : point :=
  psum (List.map snd
          (List.filter (fun dg => Z.eqb (fst dg) vv) pairs)).

Lemma bucket_cons (d : Z) (g : point) (pairs : list (Z * point))
    (vv : Z) :
  bucket ((d, g) :: pairs) vv
  = if d =? vv then padd g (bucket pairs vv) else bucket pairs vv.
Proof.
  unfold bucket. cbn [List.filter fst].
  destruct (d =? vv); reflexivity.
Qed.

Lemma bucket_good (pairs : list (Z * point)) (vv : Z) :
  Forall good (List.map snd pairs) -> good (bucket pairs vv).
Proof.
  induction pairs as [| [d g] pairs IH]; intros Hg;
    [exact good_identity |].
  inversion Hg; subst.
  rewrite bucket_cons.
  destruct (d =? vv); [apply good_add; [assumption |] |]; apply IH;
    assumption.
Qed.

(** Bucket values [255; 254; ...; 1]. *)
Fixpoint desc_from (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => Z.of_nat (S n') :: desc_from n'
  end.

Lemma desc_from_in (n : nat) (vv : Z) :
  List.In vv (desc_from n) <-> 1 <= vv <= Z.of_nat n.
Proof.
  induction n as [| n IH]; cbn [desc_from List.In].
  - cbn. lia.
  - rewrite IH. lia.
Qed.

Lemma desc_from_nodup (n : nat) : NoDup (desc_from n).
Proof.
  induction n as [| n IH]; cbn [desc_from]; constructor;
    [| exact IH].
  rewrite desc_from_in. lia.
Qed.

(** Value-indexed weighted sums over the bucket range. *)
Fixpoint wsum_vals (f : Z -> point) (vs : list Z) : point :=
  match vs with
  | [] => identity
  | vv :: vs' => padd (pmul vv (f vv)) (wsum_vals f vs')
  end.

Lemma wsum_vals_good (f : Z -> point) (vs : list Z) :
  (forall vv, List.In vv vs -> good (f vv)) ->
  good (wsum_vals f vs).
Proof.
  induction vs as [| v vs IH]; intros Hf; [exact good_identity |].
  cbn [wsum_vals].
  apply good_add.
  - apply good_mul. apply Hf. left. reflexivity.
  - apply IH. intros vv Hvv. apply Hf. right. exact Hvv.
Qed.

Lemma wsum_vals_ext (f f' : Z -> point) (vs : list Z) :
  (forall vv, List.In vv vs -> f vv = f' vv) ->
  wsum_vals f vs = wsum_vals f' vs.
Proof.
  induction vs as [| v vs IH]; intros Hf; [reflexivity |].
  cbn [wsum_vals].
  rewrite (Hf v (or_introl eq_refl)).
  rewrite IH; [reflexivity |].
  intros vv Hvv. apply Hf. right. exact Hvv.
Qed.

Lemma wsum_vals_id (vs : list Z) :
  wsum_vals (fun _ => identity) vs = identity.
Proof.
  induction vs as [| v vs IH]; cbn [wsum_vals]; [reflexivity |].
  rewrite vmul_identity, vadd_0_l. exact IH.
Qed.

(** Adding one base into bucket [v0] adds [ [v0] g ] to the weighted
    sum. *)
Lemma wsum_vals_pull (f f' : Z -> point) (vs : list Z) (v0 : Z)
    (g : point) :
  NoDup vs ->
  List.In v0 vs ->
  Forall (fun vv => 0 <= vv) vs ->
  (forall vv, List.In vv vs -> good (f vv)) ->
  good g ->
  f' v0 = padd g (f v0) ->
  (forall vv, vv <> v0 -> f' vv = f vv) ->
  wsum_vals f' vs = padd (pmul v0 g) (wsum_vals f vs).
Proof.
  induction vs as [| v vs IH];
    intros Hnd Hin Hnn Hgood Hg Hpull Hother; [destruct Hin |].
  inversion Hnd; subst.
  inversion Hnn; subst.
  destruct (Z.eq_dec v v0) as [-> | Hne].
  - cbn [wsum_vals].
    rewrite Hpull.
    rewrite (vmul_point_add v0 g (f v0));
      [ | assumption | assumption
        | apply Hgood; left; reflexivity].
    rewrite (wsum_vals_ext f' f vs)
      by (intros vv Hvv; apply Hother; intros ->; contradiction).
    rewrite (vadd_assoc (pmul v0 g) (pmul v0 (f v0)) (wsum_vals f vs));
      [reflexivity
      | apply good_mul; assumption
      | apply good_mul; apply Hgood; left; reflexivity
      | apply wsum_vals_good;
        intros vv Hvv; apply Hgood; right; exact Hvv].
  - cbn [wsum_vals].
    rewrite (Hother v Hne).
    rewrite IH; try assumption;
      [ | destruct Hin as [Hin | Hin]; [congruence | exact Hin]
        | intros vv Hvv; apply Hgood; right; exact Hvv].
    assert (Ha : good (pmul v (f v)))
      by (apply good_mul; apply Hgood; left; reflexivity).
    assert (Hb : good (pmul v0 g)) by (apply good_mul; assumption).
    assert (Hc : good (wsum_vals f vs))
      by (apply wsum_vals_good;
          intros vv Hvv; apply Hgood; right; exact Hvv).
    rewrite <- (vadd_assoc (pmul v (f v)) (pmul v0 g)
                 (wsum_vals f vs)); try assumption.
    rewrite (vadd_comm (pmul v (f v)) (pmul v0 g)); try assumption.
    rewrite (vadd_assoc (pmul v0 g) (pmul v (f v))
               (wsum_vals f vs)); try assumption.
    reflexivity.
Qed.

(** Partition: the weighted bucket sum is the window MSM. *)
Lemma bucket_partition (pairs : list (Z * point)) :
  Forall good (List.map snd pairs) ->
  Forall (fun dg => 0 <= fst dg < 256) pairs ->
  wsum_vals (bucket pairs) (desc_from 255)
  = msm (List.map fst pairs) (List.map snd pairs).
Proof.
  induction pairs as [| [d g] pairs IH]; intros Hgood Hbound.
  - cbn [List.map msm].
    rewrite (wsum_vals_ext (bucket []) (fun _ => identity))
      by (intros vv _; reflexivity).
    apply wsum_vals_id.
  - inversion Hgood; subst.
    inversion Hbound; subst.
    cbn [List.map msm].
    cbn [fst snd] in *.
    destruct (Z.eq_dec d 0) as [-> | Hd0].
    + rewrite (wsum_vals_ext (bucket ((0, g) :: pairs)) (bucket pairs)).
      2: { intros vv Hvv.
           rewrite bucket_cons.
           apply desc_from_in in Hvv.
           destruct (Z.eqb_spec 0 vv); [lia | reflexivity]. }
      rewrite IH by assumption.
      rewrite vmul_0, vadd_0_l. reflexivity.
    + rewrite (wsum_vals_pull (bucket pairs)
                 (bucket ((d, g) :: pairs)) (desc_from 255) d g).
      * rewrite IH by assumption. reflexivity.
      * exact (desc_from_nodup 255).
      * apply desc_from_in. cbn. lia.
      * apply Forall_forall. intros vv Hvv.
        apply desc_from_in in Hvv. lia.
      * intros vv _. apply bucket_good. assumption.
      * assumption.
      * rewrite bucket_cons, Z.eqb_refl. reflexivity.
      * intros vv Hne. rewrite bucket_cons.
        destruct (Z.eqb_spec d vv); [congruence | reflexivity].
Qed.

(** Suffix-sum aggregation of the descending bucket list. *)
Lemma desc_from_length (n : nat) : List.length (desc_from n) = n.
Proof.
  induction n as [| n IH]; cbn [desc_from List.length];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint wsum_desc (bs : list point) : point :=
  match bs with
  | [] => identity
  | b :: bs' =>
      padd (pmul (Z.of_nat (S (List.length bs'))) b) (wsum_desc bs')
  end.

Lemma wsum_desc_good (bs : list point) :
  Forall good bs -> good (wsum_desc bs).
Proof.
  induction bs as [| b bs IH]; intros Hb; [exact good_identity |].
  inversion Hb; subst.
  apply good_add; [apply good_mul; assumption | apply IH; assumption].
Qed.

Fixpoint aggr_go (bs : list point) (run acc : point) : point :=
  match bs with
  | [] => acc
  | b :: bs' => aggr_go bs' (padd run b) (padd acc (padd run b))
  end.

Definition aggr (bs : list point) : point := aggr_go bs identity identity.

Lemma aggr_go_spec (bs : list point) (run acc : point) :
  Forall good bs -> good run -> good acc ->
  aggr_go bs run acc
  = padd acc (padd (pmul (Z.of_nat (List.length bs)) run) (wsum_desc bs)).
Proof.
  revert run acc.
  induction bs as [| b bs IH]; intros run acc Hbs Hrun Hacc.
  - cbn [aggr_go List.length wsum_desc].
    change (Z.of_nat 0) with 0.
    rewrite vmul_0, vadd_0_l, vadd_0_r. reflexivity.
  - inversion Hbs; subst.
    cbn [aggr_go List.length wsum_desc].
    rewrite IH; try assumption;
      try (apply good_add; assumption).
    2: { apply good_add; [assumption |].
         apply good_add; assumption. }
    set (n := Z.of_nat (List.length bs)) in *.
    assert (Hn : 0 <= n) by (unfold n; lia).
    assert (Hgr : good (pmul n run)) by (apply good_mul; assumption).
    assert (Hgb : good (pmul n b)) by (apply good_mul; assumption).
    assert (Hgw : good (wsum_desc bs))
      by (apply wsum_desc_good; assumption).
    rewrite (vmul_point_add n run b); try assumption.
    assert (Hsn : forall X : point, good X ->
        pmul (Z.of_nat (S (List.length bs))) X = padd X (pmul n X)).
    { intros X HX.
      rewrite Nat2Z.inj_succ, <- Z.add_1_l.
      rewrite (vmul_add 1 (Z.of_nat (List.length bs)) X HX).
      rewrite vmul_1. reflexivity. }
    rewrite (Hsn run Hrun), (Hsn b ltac:(assumption)).
    rewrite (vadd_assoc acc (padd run b)
               (padd (padd (pmul n run) (pmul n b)) (wsum_desc bs)));
      try assumption;
      try (apply good_add; assumption);
      try (apply good_add; apply good_add; assumption).
    2: { apply good_add; [apply good_add; assumption | assumption]. }
    f_equal.
    rewrite <- (vadd_assoc (padd run b) (padd (pmul n run) (pmul n b))
                  (wsum_desc bs));
      try assumption;
      try (apply good_add; assumption).
    rewrite (vswap4 run b (pmul n run) (pmul n b));
      try assumption.
    rewrite (vadd_assoc (padd run (pmul n run)) (padd b (pmul n b))
               (wsum_desc bs));
      try assumption;
      try (apply good_add; assumption).
    reflexivity.
Qed.

Lemma wsum_desc_map (f : Z -> point) (n : nat) :
  wsum_desc (List.map f (desc_from n)) = wsum_vals f (desc_from n).
Proof.
  induction n as [| n IH]; cbn [desc_from List.map wsum_desc wsum_vals];
    [reflexivity |].
  rewrite List.length_map, desc_from_length, IH. reflexivity.
Qed.

Lemma aggr_vals (f : Z -> point) :
  (forall vv, List.In vv (desc_from 255) -> good (f vv)) ->
  aggr (List.map f (desc_from 255)) = wsum_vals f (desc_from 255).
Proof.
  intros Hf.
  unfold aggr.
  rewrite aggr_go_spec;
    [ | apply Forall_forall; intros x Hx;
        apply in_map_iff in Hx; destruct Hx as (vv & <- & Hvv);
        exact (Hf vv Hvv)
      | exact good_identity | exact good_identity].
  rewrite vmul_identity, vadd_0_l, vadd_0_l.
  apply wsum_desc_map.
Qed.

(** ** The window pipeline *)

Definition win_pairs (dss : list (list Z)) (gs : list point) (t : nat)
    : list (Z * point) :=
  List.combine (List.map (fun ds => List.nth t ds 0) dss) gs.

Definition win_sum (dss : list (list Z)) (gs : list point) (t : nat)
    : point :=
  aggr (List.map (bucket (win_pairs dss gs t)) (desc_from 255)).

Fixpoint pip_go (dss : list (list Z)) (gs : list point) (ts : list nat)
    (acc : point) : point :=
  match ts with
  | [] => acc
  | t :: ts' => pip_go dss gs ts' (padd (pmul 256 acc) (win_sum dss gs t))
  end.

Fixpoint tsd (n : nat) : list nat :=
  match n with O => [] | S n' => n' :: tsd n' end.

(** The computable Pippenger MSM: window 8, 32 windows MSB first. *)
Definition msm_pippenger (cs : list Z) (gs : list point) : point :=
  pip_go (List.map digits32 cs) gs (tsd 32) identity.

Lemma combine_fst {A B : Type} (l1 : list A) (l2 : list B) :
  List.length l1 = List.length l2 ->
  List.map fst (List.combine l1 l2) = l1.
Proof.
  revert l2. induction l1 as [| x l1 IH]; intros l2 Hlen;
    [reflexivity |].
  destruct l2 as [| y l2]; [discriminate |].
  cbn [List.combine List.map fst].
  rewrite IH; [reflexivity | cbn in Hlen; lia].
Qed.

Lemma combine_snd {A B : Type} (l1 : list A) (l2 : list B) :
  List.length l1 = List.length l2 ->
  List.map snd (List.combine l1 l2) = l2.
Proof.
  revert l2. induction l1 as [| x l1 IH]; intros l2 Hlen.
  - destruct l2; [reflexivity | discriminate].
  - destruct l2 as [| y l2]; [discriminate |].
    cbn [List.combine List.map snd].
    rewrite IH; [reflexivity | cbn in Hlen; lia].
Qed.

Lemma nth_digit_bound (ds : list Z) (t : nat) :
  Forall (fun d => 0 <= d < 256) ds ->
  0 <= List.nth t ds 0 < 256.
Proof.
  intros Hds.
  destruct (le_lt_dec (List.length ds) t) as [Hge | Hlt].
  - rewrite List.nth_overflow by exact Hge. lia.
  - exact (proj1 (Forall_forall _ _) Hds (List.nth t ds 0)
             (List.nth_In ds 0 Hlt)).
Qed.

Lemma win_sum_spec (dss : list (list Z)) (gs : list point) (t : nat) :
  List.length dss = List.length gs ->
  Forall good gs ->
  Forall (Forall (fun d => 0 <= d < 256)) dss ->
  win_sum dss gs t = msm (List.map (fun ds => List.nth t ds 0) dss) gs.
Proof.
  intros Hlen Hgs Hdss.
  unfold win_sum.
  set (pairs := win_pairs dss gs t).
  assert (Hsnd : List.map snd pairs = gs)
    by (unfold pairs, win_pairs; apply combine_snd;
        rewrite List.length_map; exact Hlen).
  assert (Hfst : List.map fst pairs
                 = List.map (fun ds => List.nth t ds 0) dss)
    by (unfold pairs, win_pairs; apply combine_fst;
        rewrite List.length_map; exact Hlen).
  assert (Hgoodsnd : Forall good (List.map snd pairs))
    by (rewrite Hsnd; exact Hgs).
  assert (Hbounds : Forall (fun dg => 0 <= fst dg < 256) pairs).
  { apply Forall_forall. intros [d g] Hin.
    cbn [fst].
    apply in_combine_l in Hin.
    apply in_map_iff in Hin. destruct Hin as (ds & <- & Hds).
    apply nth_digit_bound.
    exact (proj1 (Forall_forall _ _) Hdss ds Hds). }
  rewrite (aggr_vals (bucket pairs))
    by (intros vv _; apply bucket_good; exact Hgoodsnd).
  rewrite (bucket_partition pairs Hgoodsnd Hbounds).
  rewrite Hfst, Hsnd. reflexivity.
Qed.

Fixpoint pval (ts : list nat) (ds : list Z) (v0 : Z) : Z :=
  match ts with
  | [] => v0
  | t :: ts' => pval ts' ds (v0 * 256 + List.nth t ds 0)
  end.

Lemma pval_affine (ts : list nat) (ds : list Z) (v0 : Z) :
  pval ts ds v0 = v0 * 256 ^ Z.of_nat (List.length ts) + pval ts ds 0.
Proof.
  revert v0. induction ts as [| t ts IH]; intros v0.
  - cbn [pval List.length]. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r. ring.
  - cbn [pval List.length].
    rewrite (IH (v0 * 256 + List.nth t ds 0)).
    rewrite (IH (0 * 256 + List.nth t ds 0)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.

Lemma pip_go_spec (dss : list (list Z)) (gs : list point)
    (ts : list nat) (acc : point) :
  List.length dss = List.length gs ->
  Forall good gs -> good acc ->
  Forall (Forall (fun d => 0 <= d < 256)) dss ->
  pip_go dss gs ts acc
  = padd (pmul (256 ^ Z.of_nat (List.length ts)) acc)
         (msm (List.map (fun ds => pval ts ds 0) dss) gs).
Proof.
  revert acc.
  induction ts as [| t ts IH]; intros acc Hlen Hgs Hacc Hdss.
  - cbn [pip_go List.length pval].
    change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, vmul_1.
    rewrite msm_zeros.
    + rewrite vadd_0_r. reflexivity.
    + apply Forall_forall. intros x Hx.
      apply in_map_iff in Hx. destruct Hx as (ds & <- & _).
      reflexivity.
  - cbn [pip_go].
    rewrite (win_sum_spec dss gs t Hlen Hgs Hdss).
    rewrite IH; try assumption.
    2: { apply good_add;
         [apply good_mul; exact Hacc | apply msm_good; exact Hgs]. }
    assert (Hpn : 0 <= 256 ^ Z.of_nat (List.length ts))
      by (apply Z.pow_nonneg; lia).
    rewrite (vmul_point_add (256 ^ Z.of_nat (List.length ts))
               (pmul 256 acc)
               (msm (List.map (fun ds => List.nth t ds 0) dss) gs));
      [ | exact Hpn | apply good_mul; exact Hacc
        | apply msm_good; exact Hgs].
    rewrite <- (vmul_mul (256 ^ Z.of_nat (List.length ts)) 256 acc Hacc).
    rewrite (msm_map_mul (256 ^ Z.of_nat (List.length ts))
               (List.map (fun ds => List.nth t ds 0) dss) gs Hpn Hgs).
    rewrite List.map_map.
    rewrite vadd_assoc;
      [ | apply good_mul; exact Hacc
        | apply msm_good; exact Hgs
        | apply msm_good; exact Hgs].
    rewrite <- msm_zipadd;
      [ | rewrite !List.length_map; reflexivity | exact Hgs].
    rewrite zipadd_map.
    f_equal.
    + f_equal. cbn [List.length].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
    + f_equal. apply List.map_ext. intros ds.
      cbn [pval].
      rewrite (pval_affine ts ds (0 * 256 + List.nth t ds 0)).
      ring.
Qed.

(** ** Digit recomposition of the window Horner pass *)

Lemma tsd_length (n : nat) : List.length (tsd n) = n.
Proof. induction n; cbn [tsd List.length]; congruence. Qed.

Lemma firstn_snoc (m : nat) (ds : list Z) :
  (m < List.length ds)%nat ->
  List.firstn (S m) ds = List.firstn m ds ++ [List.nth m ds 0].
Proof.
  revert m. induction ds as [| d ds IH]; intros m Hm;
    [cbn in Hm; lia |].
  destruct m as [| m]; [reflexivity |].
  change (List.firstn (S (S m)) (d :: ds))
    with (d :: List.firstn (S m) ds).
  change (List.firstn (S m) (d :: ds)) with (d :: List.firstn m ds).
  change (List.nth (S m) (d :: ds) 0) with (List.nth m ds 0).
  rewrite <- app_comm_cons.
  f_equal.
  apply IH. cbn in Hm. lia.
Qed.

Lemma recomp_snoc (l : list Z) (d : Z) :
  recomp (l ++ [d]) = recomp l + d * 256 ^ Z.of_nat (List.length l).
Proof.
  induction l as [| x l IH].
  - cbn [recomp app List.length]. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r. ring.
  - cbn [recomp app List.length].
    rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.

Lemma pval_tsd (m : nat) (ds : list Z) :
  (m <= List.length ds)%nat ->
  pval (tsd m) ds 0 = recomp (List.firstn m ds).
Proof.
  induction m as [| m IH]; intros Hm.
  - reflexivity.
  - cbn [tsd pval].
    rewrite pval_affine.
    rewrite IH by lia.
    rewrite (firstn_snoc m ds) by lia.
    rewrite recomp_snoc.
    rewrite List.firstn_length_le by lia.
    rewrite tsd_length.
    ring.
Qed.

Lemma pval_digits (c : Z) :
  0 <= c < 2 ^ 256 ->
  pval (tsd 32) (digits32 c) 0 = c.
Proof.
  intros Hc.
  unfold digits32.
  rewrite (pval_tsd 32 (digits_go 32 c))
    by (rewrite digits_go_length; lia).
  rewrite List.firstn_all2 by (rewrite digits_go_length; lia).
  apply digits_go_recomp.
  assert (Heq : 256 ^ Z.of_nat 32 = 2 ^ 256)
    by (vm_compute; reflexivity).
  rewrite Heq. exact Hc.
Qed.

(** ** Pippenger correctness *)

Theorem pippenger_correct (cs : list Z) (gs : list point) :
  List.length cs = List.length gs ->
  Forall good gs ->
  Forall (fun c => 0 <= c < 2 ^ 256) cs ->
  msm_pippenger cs gs = msm cs gs.
Proof.
  intros Hlen Hgs Hcs.
  unfold msm_pippenger.
  rewrite (pip_go_spec (List.map digits32 cs) gs (tsd 32) identity);
    [ | rewrite List.length_map; exact Hlen
      | exact Hgs
      | exact good_identity
      | apply Forall_forall; intros ds Hds;
        apply in_map_iff in Hds; destruct Hds as (c & <- & _);
        apply digits_go_bound].
  rewrite vmul_identity, vadd_0_l.
  rewrite List.map_map.
  transitivity (msm (List.map (fun c => c) cs) gs).
  - f_equal. apply List.map_ext_in. intros c Hc.
    apply pval_digits.
    exact (proj1 (Forall_forall _ _) Hcs c Hc).
  - rewrite List.map_id. reflexivity.
Qed.

(** ** The packaged two-shard certificate introduction *)

Lemma Forall_firstn {A : Type} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (List.firstn n l).
Proof.
  revert n. induction l as [| x l IH]; intros n Hl;
    destruct n; cbn [List.firstn]; try constructor;
    inversion Hl; subst; [assumption | apply IH; assumption].
Qed.

Lemma Forall_skipn {A : Type} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (List.skipn n l).
Proof.
  revert n. induction l as [| x l IH]; intros n Hl;
    destruct n; cbn [List.skipn]; try constructor;
    inversion Hl; subst; try assumption.
  apply IH; assumption.
Qed.

(** One certificate instantiates this lemma with five [vm_compute]
    facts: the range scan on [v], the [intt] coefficient identity, the
    two Pippenger half-range checkpoints, and the final blind-and-compare
    step against the pinned coordinates. *)
Theorem commit_two_shards (v c : list Z) (cpa cpb : point)
    (px py : Z) :
  params_well_formed ->
  List.length v = 2048%nat ->
  List.forallb (fun s => (0 <=? s) && (s <? scalar_p)) v = true ->
  intt v = c ->
  msm_pippenger (List.firstn 1024 c) (List.firstn 1024 g_points) = cpa ->
  msm_pippenger (List.skipn 1024 c) (List.skipn 1024 g_points) = cpb ->
  padd (padd cpa cpb) w_point = Weierstrass.Affine px py ->
  commit_lagrange v = Weierstrass.Affine px py.
Proof.
  intros Hparams Hlen Hrange Hc Hcpa Hcpb Hfinal.
  assert (Hv : Forall (fun s => 0 <= s) v).
  { apply Forall_forall. intros s Hs.
    pose proof (proj1 (List.forallb_forall _ v) Hrange s Hs) as Hb.
    apply andb_prop in Hb. destruct Hb as [Hb _].
    apply Z.leb_le. exact Hb. }
  assert (Hclen : List.length c = 2048%nat)
    by (rewrite <- Hc; exact (intt_length v Hlen)).
  assert (Hcrange : Forall (fun x => 0 <= x < 2 ^ 256) c).
  { rewrite <- Hc.
    eapply Forall_impl; [| exact (intt_range v)].
    cbv beta. intros x [Hx1 Hx2].
    assert (Hp : scalar_p < 2 ^ 256) by (vm_compute; reflexivity).
    lia. }
  rewrite (commit_lagrange_intt v Hparams Hlen Hv).
  rewrite Hc.
  rewrite <- (List.firstn_skipn 1024 c).
  rewrite <- (List.firstn_skipn 1024 g_points).
  rewrite msm_app;
    [ | rewrite !List.firstn_length_le
          by (rewrite ?Hclen, ?g_points_length; lia);
        reflexivity
      | apply Forall_firstn; exact (g_points_good Hparams)
      | apply Forall_skipn; exact (g_points_good Hparams)].
  rewrite <- (pippenger_correct (List.firstn 1024 c)
                (List.firstn 1024 g_points));
    [ | rewrite !List.firstn_length_le
          by (rewrite ?Hclen, ?g_points_length; lia);
        reflexivity
      | apply Forall_firstn; exact (g_points_good Hparams)
      | apply Forall_firstn; exact Hcrange].
  rewrite <- (pippenger_correct (List.skipn 1024 c)
                (List.skipn 1024 g_points));
    [ | rewrite !List.length_skipn, Hclen, g_points_length; reflexivity
      | apply Forall_skipn; exact (g_points_good Hparams)
      | apply Forall_skipn; exact Hcrange].
  rewrite Hcpa, Hcpb.
  exact Hfinal.
Qed.

End VkMsm.
