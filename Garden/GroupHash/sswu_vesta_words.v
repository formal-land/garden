(** * Montgomery-word evaluation of the witnessed Vesta SSWU pipeline

    [SswuVesta] and [SswuVestaWitness] specify the witnessed hash-to-curve
    check with [Z] field arithmetic.  Under [vm_compute] each [Z] modular
    multiplication costs milliseconds, so a 64-point SRS shard certificate
    spends minutes in field arithmetic.  This module evaluates the same
    checks over the five-limb Montgomery representation of [PallasQ], where
    a multiplication is a microsecond-scale primitive-integer operation.

    Every definition mirrors its [Z]-level counterpart operation for
    operation, so each soundness lemma closes by structural descent over
    the [represents] relation between canonical words and [Z] residues.
    The exported [group_hash_checkb] implies the three [Z]-level boolean
    conjuncts consumed by [VkSrs.check_entry_for]: the witness/
    nonexceptionality checks, the reconstructed-point comparison, and the
    curve-membership test. *)

From Stdlib Require Import ZArith Bool.Bool.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.sswu_vesta.
Require Import Garden.GroupHash.sswu_vesta_witness.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaDenoteFacts.
Require Import Garden.Prim63.PastaModulusFacts.
Require Import Garden.Prim63.PastaEqualityFacts.
Require Import Garden.Prim63.PastaCanonicalFacts.

Local Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module SswuVestaWords.
  Module Q := PallasQ.

  (** ** Word-level helpers

      Isogeny and curve constants appear inline as [Q.from_Z] images so
      that every canonicality and denotation obligation is syntactically
      [from_Z]-headed for the opaque-matching hint database below. *)

  (** ** Precomputed Montgomery constants

      Each [Q.from_Z] application pays a [Z] modular reduction, and
      the mirrored accessors reference the isogeny constants many
      times per evaluation.  Evaluating each constant once at
      definition time makes every later reference a literal read. *)

  Definition a_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.a.
  Definition b_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.b.
  Definition z_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.z.
  Definition lambda_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.lambda.
  Definition theta_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.theta.
  Definition c1_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c1.
  Definition c2_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c2.
  Definition c3_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c3.
  Definition c4_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c4.
  Definition c5_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c5.
  Definition c6_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c6.
  Definition c7_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c7.
  Definition c8_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c8.
  Definition c9_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c9.
  Definition c10_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c10.
  Definition c11_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c11.
  Definition c12_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c12.
  Definition c13_c : Q.t := Eval vm_compute in Q.from_Z IsoVesta.c13.
  Definition va_c : Q.t := Eval vm_compute in Q.from_Z Vesta.a.
  Definition vb_c : Q.t := Eval vm_compute in Q.from_Z Vesta.b.

  Definition inverse_w (v : Q.t) : Q.t :=
    Q.from_Z (mod_inverse (Q.to_Z v) Primes.pallas_q).

  Definition div_w (n d : Q.t) : Q.t := Q.mul n (inverse_w d).

  Definition opp_w (v : Q.t) : Q.t := Q.sub Q.zero v.

  Definition odd_w (v : Q.t) : bool := Z.odd (Q.to_Z v).

  Definition nonzero_w (v : Q.t) : bool := negb (Q.equal v Q.zero).

  (** ** Mirrors of the [SswuVesta] accessors *)

  Definition z_u2_w (u : Q.t) : Q.t :=
    Q.mul z_c (Q.mul u u).

  Definition ta_w (u : Q.t) : Q.t :=
    Q.add (Q.mul (z_u2_w u) (z_u2_w u)) (z_u2_w u).

  Definition x1_num_w (u : Q.t) : Q.t :=
    Q.mul b_c (Q.add (ta_w u) Q.one).

  Definition x_div_w (u : Q.t) : Q.t :=
    if Q.equal (ta_w u) Q.zero
    then Q.mul a_c z_c
    else Q.mul a_c (opp_w (ta_w u)).

  Definition x_div3_w (u : Q.t) : Q.t :=
    Q.mul (Q.mul (x_div_w u) (x_div_w u)) (x_div_w u).

  Definition gx1_num_w (u : Q.t) : Q.t :=
    Q.add
      (Q.mul
        (Q.add (Q.mul (x1_num_w u) (x1_num_w u))
          (Q.mul a_c
            (Q.mul (x_div_w u) (x_div_w u))))
        (x1_num_w u))
      (Q.mul b_c (x_div3_w u)).

  Definition x2_num_w (u : Q.t) : Q.t := Q.mul (z_u2_w u) (x1_num_w u).

  Definition swu_nonexceptionalb_w (u : Q.t) : bool :=
    nonzero_w (gx1_num_w u) && nonzero_w (x_div3_w u).

  Definition swu_witness_okb_w (u : Q.t) (was_square : bool) (root : Q.t)
      : bool :=
    if was_square
    then Q.equal (Q.mul (Q.mul root root) (x_div3_w u)) (gx1_num_w u)
    else Q.equal (Q.mul (Q.mul root root) (x_div3_w u))
      (Q.mul lambda_c (gx1_num_w u)).

  Definition swu_x_w (u : Q.t) (was_square : bool) : Q.t :=
    div_w (if was_square then x1_num_w u else x2_num_w u) (x_div_w u).

  Definition swu_y_pre_w (u : Q.t) (was_square : bool) (root : Q.t) : Q.t :=
    if was_square then root
    else Q.mul (Q.mul (Q.mul theta_c (z_u2_w u)) u) root.

  Definition swu_y_w (u : Q.t) (was_square : bool) (root : Q.t) : Q.t :=
    let y' := swu_y_pre_w u was_square root in
    if xorb (odd_w u) (odd_w y') then opp_w y' else y'.

  (** ** Mirrors of the iso-curve secant addition and isogeny map *)

  Definition secant_lambda_w (x1 y1 x2 y2 : Q.t) : Q.t :=
    div_w (Q.sub y2 y1) (Q.sub x2 x1).

  Definition secant_x_w (x1 y1 x2 y2 : Q.t) : Q.t :=
    let lam := secant_lambda_w x1 y1 x2 y2 in
    Q.sub (Q.sub (Q.mul lam lam) x1) x2.

  Definition secant_y_w (x1 y1 x2 y2 : Q.t) : Q.t :=
    let lam := secant_lambda_w x1 y1 x2 y2 in
    Q.sub (Q.mul lam (Q.sub x1 (secant_x_w x1 y1 x2 y2))) y1.

  Definition iso_x_num_w (x : Q.t) : Q.t :=
    Q.add
      (Q.mul
        (Q.add
          (Q.mul (Q.add (Q.mul c1_c x)
            c2_c) x)
          c3_c) x)
      c4_c.

  Definition iso_x_den_w (x : Q.t) : Q.t :=
    Q.add (Q.mul (Q.add x c5_c) x)
      c6_c.

  Definition iso_y_num_w (x y : Q.t) : Q.t :=
    Q.mul
      (Q.add
        (Q.mul
          (Q.add
            (Q.mul (Q.add (Q.mul c7_c x)
              c8_c) x)
            c9_c) x)
        c10_c)
      y.

  Definition iso_y_den_w (x : Q.t) : Q.t :=
    Q.add
      (Q.mul
        (Q.add (Q.mul (Q.add x c11_c) x)
          c12_c) x)
      c13_c.

  Definition on_curvebw (x y : Q.t) : bool :=
    Q.equal (Q.mul y y)
      (Q.add
        (Q.add (Q.mul (Q.mul x x) x) (Q.mul va_c x))
        vb_c).

  (** ** The complete word-level entry check

      The conjuncts below are named definitions applied to the raw
      arguments rather than [let]-bound intermediates.  Decomposing the
      conjunction in the soundness proof then never asks the kernel to
      convert through the Montgomery arithmetic: every hypothesis type is
      a compact named application.  The executable cost of re-evaluating
      the shared map and secant points in several conjuncts is a handful
      of extra inversions per entry. *)

  Definition map_x_w (u : Z) (was_square : bool) : Q.t :=
    swu_x_w (Q.from_Z u) was_square.

  Definition map_y_w (u root : Z) (was_square : bool) : Q.t :=
    swu_y_w (Q.from_Z u) was_square (Q.from_Z root).

  Definition sum_x_w
      (u0 root0 : Z) (was_square0 : bool)
      (u1 root1 : Z) (was_square1 : bool) : Q.t :=
    secant_x_w
      (map_x_w u0 was_square0) (map_y_w u0 root0 was_square0)
      (map_x_w u1 was_square1) (map_y_w u1 root1 was_square1).

  Definition sum_y_w
      (u0 root0 : Z) (was_square0 : bool)
      (u1 root1 : Z) (was_square1 : bool) : Q.t :=
    secant_y_w
      (map_x_w u0 was_square0) (map_y_w u0 root0 was_square0)
      (map_x_w u1 was_square1) (map_y_w u1 root1 was_square1).

  Definition witnessesb
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    (swu_nonexceptionalb_w (Q.from_Z u0)
      && swu_witness_okb_w (Q.from_Z u0) was_square0 (Q.from_Z root0))
      && (swu_nonexceptionalb_w (Q.from_Z u1)
        && swu_witness_okb_w (Q.from_Z u1) was_square1 (Q.from_Z root1)).

  Definition guardb
      (u0 : Z) (was_square0 : bool) (u1 : Z) (was_square1 : bool) : bool :=
    negb (Q.equal
      (Q.sub (map_x_w u0 was_square0) (map_x_w u1 was_square1)) Q.zero).

  Definition densb
      (u0 root0 : Z) (was_square0 : bool)
      (u1 root1 : Z) (was_square1 : bool) : bool :=
    nonzero_w (iso_x_den_w
      (sum_x_w u0 root0 was_square0 u1 root1 was_square1))
      && nonzero_w (iso_y_den_w
        (sum_x_w u0 root0 was_square0 u1 root1 was_square1)).

  Definition x_eqb
      (u0 root0 : Z) (was_square0 : bool)
      (u1 root1 : Z) (was_square1 : bool) (x : Q.t) : bool :=
    Q.equal
      (div_w
        (iso_x_num_w (sum_x_w u0 root0 was_square0 u1 root1 was_square1))
        (iso_x_den_w (sum_x_w u0 root0 was_square0 u1 root1 was_square1)))
      x.

  Definition y_eqb
      (u0 root0 : Z) (was_square0 : bool)
      (u1 root1 : Z) (was_square1 : bool) (y : Q.t) : bool :=
    Q.equal
      (div_w
        (iso_y_num_w
          (sum_x_w u0 root0 was_square0 u1 root1 was_square1)
          (sum_y_w u0 root0 was_square0 u1 root1 was_square1))
        (iso_y_den_w (sum_x_w u0 root0 was_square0 u1 root1 was_square1)))
      y.

  Definition group_hash_checkb
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (x y : Q.t) : bool :=
    witnessesb u0 u1 was_square0 root0 was_square1 root1
      && (guardb u0 was_square0 u1 was_square1
        && (densb u0 root0 was_square0 u1 root1 was_square1
          && (x_eqb u0 root0 was_square0 u1 root1 was_square1 x
            && y_eqb u0 root0 was_square0 u1 root1 was_square1 y)))
      && on_curvebw x y.

  (** Kernel conversion between a named-conjunction application and its
      unfolding must expand the named definition, never the [andb] on the
      other side: reducing [andb] would force weak-head evaluation of a
      symbolic Montgomery term.  These levels direct the conversion oracle
      accordingly; virtual-machine evaluation is unaffected. *)
  Strategy expand
    [map_x_w map_y_w sum_x_w sum_y_w
     witnessesb guardb densb x_eqb y_eqb group_hash_checkb].

  (** ** Proof toolkit *)

  Lemma q_pos : 0 < Primes.pallas_q.
  Proof. vm_compute. reflexivity. Qed.

  Lemma q_neq : Primes.pallas_q <> 0.
  Proof. pose proof q_pos. lia. Qed.

  Create HintDb swu_cano discriminated.
  #[local] Hint Constants Opaque : swu_cano.
  #[local] Hint Variables Opaque : swu_cano.
  #[local] Hint Resolve
    PallasQCanonicalFacts.from_Z_canonical
    PallasQCanonicalFacts.zero_canonical
    PallasQCanonicalFacts.one_canonical
    PallasQCanonicalFacts.mul_canonical
    PallasQCanonicalFacts.add_canonical
    PallasQCanonicalFacts.sub_canonical : swu_cano.

  Ltac cano := solve [auto 40 with swu_cano].

  Lemma a_c_eq : a_c = Q.from_Z IsoVesta.a.
  Proof. vm_compute. reflexivity. Qed.

  Lemma a_c_canonical : Q.canonical a_c.
  Proof. rewrite a_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve a_c_canonical : swu_cano.

  Lemma b_c_eq : b_c = Q.from_Z IsoVesta.b.
  Proof. vm_compute. reflexivity. Qed.

  Lemma b_c_canonical : Q.canonical b_c.
  Proof. rewrite b_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve b_c_canonical : swu_cano.

  Lemma z_c_eq : z_c = Q.from_Z IsoVesta.z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma z_c_canonical : Q.canonical z_c.
  Proof. rewrite z_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve z_c_canonical : swu_cano.

  Lemma lambda_c_eq : lambda_c = Q.from_Z IsoVesta.lambda.
  Proof. vm_compute. reflexivity. Qed.

  Lemma lambda_c_canonical : Q.canonical lambda_c.
  Proof. rewrite lambda_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve lambda_c_canonical : swu_cano.

  Lemma theta_c_eq : theta_c = Q.from_Z IsoVesta.theta.
  Proof. vm_compute. reflexivity. Qed.

  Lemma theta_c_canonical : Q.canonical theta_c.
  Proof. rewrite theta_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve theta_c_canonical : swu_cano.

  Lemma c1_c_eq : c1_c = Q.from_Z IsoVesta.c1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c1_c_canonical : Q.canonical c1_c.
  Proof. rewrite c1_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c1_c_canonical : swu_cano.

  Lemma c2_c_eq : c2_c = Q.from_Z IsoVesta.c2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c2_c_canonical : Q.canonical c2_c.
  Proof. rewrite c2_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c2_c_canonical : swu_cano.

  Lemma c3_c_eq : c3_c = Q.from_Z IsoVesta.c3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c3_c_canonical : Q.canonical c3_c.
  Proof. rewrite c3_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c3_c_canonical : swu_cano.

  Lemma c4_c_eq : c4_c = Q.from_Z IsoVesta.c4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c4_c_canonical : Q.canonical c4_c.
  Proof. rewrite c4_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c4_c_canonical : swu_cano.

  Lemma c5_c_eq : c5_c = Q.from_Z IsoVesta.c5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c5_c_canonical : Q.canonical c5_c.
  Proof. rewrite c5_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c5_c_canonical : swu_cano.

  Lemma c6_c_eq : c6_c = Q.from_Z IsoVesta.c6.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c6_c_canonical : Q.canonical c6_c.
  Proof. rewrite c6_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c6_c_canonical : swu_cano.

  Lemma c7_c_eq : c7_c = Q.from_Z IsoVesta.c7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c7_c_canonical : Q.canonical c7_c.
  Proof. rewrite c7_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c7_c_canonical : swu_cano.

  Lemma c8_c_eq : c8_c = Q.from_Z IsoVesta.c8.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c8_c_canonical : Q.canonical c8_c.
  Proof. rewrite c8_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c8_c_canonical : swu_cano.

  Lemma c9_c_eq : c9_c = Q.from_Z IsoVesta.c9.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c9_c_canonical : Q.canonical c9_c.
  Proof. rewrite c9_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c9_c_canonical : swu_cano.

  Lemma c10_c_eq : c10_c = Q.from_Z IsoVesta.c10.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c10_c_canonical : Q.canonical c10_c.
  Proof. rewrite c10_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c10_c_canonical : swu_cano.

  Lemma c11_c_eq : c11_c = Q.from_Z IsoVesta.c11.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c11_c_canonical : Q.canonical c11_c.
  Proof. rewrite c11_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c11_c_canonical : swu_cano.

  Lemma c12_c_eq : c12_c = Q.from_Z IsoVesta.c12.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c12_c_canonical : Q.canonical c12_c.
  Proof. rewrite c12_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c12_c_canonical : swu_cano.

  Lemma c13_c_eq : c13_c = Q.from_Z IsoVesta.c13.
  Proof. vm_compute. reflexivity. Qed.

  Lemma c13_c_canonical : Q.canonical c13_c.
  Proof. rewrite c13_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve c13_c_canonical : swu_cano.

  Lemma va_c_eq : va_c = Q.from_Z Vesta.a.
  Proof. vm_compute. reflexivity. Qed.

  Lemma va_c_canonical : Q.canonical va_c.
  Proof. rewrite va_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve va_c_canonical : swu_cano.

  Lemma vb_c_eq : vb_c = Q.from_Z Vesta.b.
  Proof. vm_compute. reflexivity. Qed.

  Lemma vb_c_canonical : Q.canonical vb_c.
  Proof. rewrite vb_c_eq. apply PallasQCanonicalFacts.from_Z_canonical. Qed.
  #[local] Hint Resolve vb_c_canonical : swu_cano.



  (** Word terms produced by this module are canonical by construction;
      the case splits below mirror the executable branch structure. *)
  Lemma inverse_w_canonical (v : Q.t) : Q.canonical (inverse_w v).
  Proof. unfold inverse_w. cano. Qed.
  #[local] Hint Resolve inverse_w_canonical : swu_cano.

  Lemma div_w_canonical (n d : Q.t) : Q.canonical (div_w n d).
  Proof. unfold div_w. cano. Qed.
  #[local] Hint Resolve div_w_canonical : swu_cano.

  Lemma opp_w_canonical (v : Q.t) (Hv : Q.canonical v) :
    Q.canonical (opp_w v).
  Proof. unfold opp_w. cano. Qed.
  #[local] Hint Resolve opp_w_canonical : swu_cano.

  Lemma z_u2_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (z_u2_w u).
  Proof. unfold z_u2_w. cano. Qed.
  #[local] Hint Resolve z_u2_w_canonical : swu_cano.

  Lemma ta_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (ta_w u).
  Proof. unfold ta_w. cano. Qed.
  #[local] Hint Resolve ta_w_canonical : swu_cano.

  Lemma x1_num_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (x1_num_w u).
  Proof. unfold x1_num_w. cano. Qed.
  #[local] Hint Resolve x1_num_w_canonical : swu_cano.

  Lemma x_div_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (x_div_w u).
  Proof.
    unfold x_div_w. destruct (Q.equal (ta_w u) Q.zero); cano.
  Qed.
  #[local] Hint Resolve x_div_w_canonical : swu_cano.

  Lemma x_div3_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (x_div3_w u).
  Proof. unfold x_div3_w. cano. Qed.
  #[local] Hint Resolve x_div3_w_canonical : swu_cano.

  Lemma gx1_num_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (gx1_num_w u).
  Proof. unfold gx1_num_w. cano. Qed.
  #[local] Hint Resolve gx1_num_w_canonical : swu_cano.

  Lemma x2_num_w_canonical (u : Q.t) (Hu : Q.canonical u) :
    Q.canonical (x2_num_w u).
  Proof. unfold x2_num_w. cano. Qed.
  #[local] Hint Resolve x2_num_w_canonical : swu_cano.

  Lemma denote_range (v : Q.t) :
    0 <= Q.denote v < Primes.pallas_q.
  Proof.
    unfold Q.denote. rewrite PallasQ_modulus_eq.
    apply Z.mod_pos_bound. exact q_pos.
  Qed.

  Lemma denote_zero : Q.denote Q.zero = 0.
  Proof. exact PallasQRefinement.denote_zero. Qed.

  Lemma denote_one : Q.denote Q.one = 1.
  Proof. exact PallasQRefinement.denote_one. Qed.

  (** ** Value representation

      [represents w x] states that the canonical word [w] denotes the
      residue of the [Z]-level value [x].  One congruence rule mirrors one
      specification operation, so every accessor obligation below closes
      by structural descent with no rewrite search. *)

  Definition represents (w : Q.t) (x : Z) : Prop :=
    Q.canonical w /\ Q.denote w = x mod Primes.pallas_q.

  Lemma represents_canonical (w : Q.t) (x : Z) :
    represents w x -> Q.canonical w.
  Proof. intros [Hc _]. exact Hc. Qed.

  Lemma represents_denote (w : Q.t) (x : Z) :
    represents w x -> Q.denote w = x mod Primes.pallas_q.
  Proof. intros [_ Hd]. exact Hd. Qed.

  Lemma q_gt_1 : 1 < Primes.pallas_q.
  Proof. vm_compute. reflexivity. Qed.

  Lemma from_Z_repr (x : Z) : represents (Q.from_Z x) x.
  Proof.
    split; [apply PallasQCanonicalFacts.from_Z_canonical |].
    apply PallasQDenoteFacts.from_Z_denote.
  Qed.

  Lemma zero_repr : represents Q.zero 0.
  Proof.
    split; [exact PallasQCanonicalFacts.zero_canonical |].
    rewrite denote_zero. now rewrite Z.mod_0_l by exact q_neq.
  Qed.

  Lemma one_repr : represents Q.one 1.
  Proof.
    split; [exact PallasQCanonicalFacts.one_canonical |].
    rewrite denote_one. rewrite Z.mod_small; [reflexivity |].
    pose proof q_gt_1. lia.
  Qed.

  Lemma mul_repr (wa wb : Q.t) (a b : Z) :
    represents wa a -> represents wb b ->
    represents (Q.mul wa wb) (BinOp.mul a b).
  Proof.
    intros [Hca Hda] [Hcb Hdb].
    split; [now apply PallasQCanonicalFacts.mul_canonical |].
    rewrite PallasQDenoteFacts.mul_denote by exact Hcb.
    rewrite Hda, Hdb. unfold BinOp.mul.
    rewrite <- Z.mul_mod by exact q_neq.
    now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma add_repr (wa wb : Q.t) (a b : Z) :
    represents wa a -> represents wb b ->
    represents (Q.add wa wb) (BinOp.add a b).
  Proof.
    intros [Hca Hda] [Hcb Hdb].
    split; [now apply PallasQCanonicalFacts.add_canonical |].
    rewrite PallasQDenoteFacts.add_denote by assumption.
    rewrite Hda, Hdb. unfold BinOp.add.
    rewrite <- Z.add_mod by exact q_neq.
    now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma sub_repr (wa wb : Q.t) (a b : Z) :
    represents wa a -> represents wb b ->
    represents (Q.sub wa wb) (BinOp.sub a b).
  Proof.
    intros [Hca Hda] [Hcb Hdb].
    split; [now apply PallasQCanonicalFacts.sub_canonical |].
    rewrite PallasQDenoteFacts.sub_denote by assumption.
    rewrite Hda, Hdb. unfold BinOp.sub.
    rewrite <- Zminus_mod.
    now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma opp_repr (w : Q.t) (x : Z) :
    represents w x -> represents (opp_w w) (UnOp.opp x).
  Proof.
    intros [Hc Hd]. unfold opp_w.
    split; [cano |].
    rewrite PallasQDenoteFacts.sub_denote
      by first [exact PallasQCanonicalFacts.zero_canonical | exact Hc].
    rewrite denote_zero, Hd. unfold UnOp.opp.
    rewrite <- (Z.mod_0_l Primes.pallas_q q_neq) at 1.
    rewrite <- Zminus_mod. rewrite Z.sub_0_l.
    now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma mod_inverse_mod (a : Z) :
    mod_inverse (a mod Primes.pallas_q) Primes.pallas_q =
      mod_inverse a Primes.pallas_q.
  Proof.
    pose proof q_pos as Hq.
    unfold mod_inverse.
    destruct Primes.pallas_q as [| p | p]; [lia | | lia].
    now rewrite Z.mod_mod by lia.
  Qed.

  Lemma div_repr (wn wd : Q.t) (n d : Z) :
    represents wn n -> represents wd d ->
    represents (div_w wn wd) (BinOp.div n d).
  Proof.
    intros [Hcn Hdn] [Hcd Hdd]. unfold div_w, inverse_w.
    split; [cano |].
    rewrite PallasQDenoteFacts.mul_denote
      by apply PallasQCanonicalFacts.from_Z_canonical.
    rewrite PallasQDenoteFacts.from_Z_denote.
    rewrite PallasQDenoteFacts.to_Z_denote.
    rewrite Hdn, Hdd, mod_inverse_mod.
    unfold BinOp.div, BinOp.mul.
    rewrite Z.mul_mod_idemp_r by exact q_neq.
    rewrite Z.mul_mod_idemp_l by exact q_neq.
    now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma repr_from (w : Q.t) (x : Z) :
    represents w x -> represents w (UnOp.from x).
  Proof.
    intros [Hc Hd]. split; [exact Hc |].
    unfold UnOp.from. now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma a_c_repr : represents a_c IsoVesta.a.
  Proof. rewrite a_c_eq. apply from_Z_repr. Qed.

  Lemma b_c_repr : represents b_c IsoVesta.b.
  Proof. rewrite b_c_eq. apply from_Z_repr. Qed.

  Lemma z_c_repr : represents z_c IsoVesta.z.
  Proof. rewrite z_c_eq. apply from_Z_repr. Qed.

  Lemma lambda_c_repr : represents lambda_c IsoVesta.lambda.
  Proof. rewrite lambda_c_eq. apply from_Z_repr. Qed.

  Lemma theta_c_repr : represents theta_c IsoVesta.theta.
  Proof. rewrite theta_c_eq. apply from_Z_repr. Qed.

  Lemma c1_c_repr : represents c1_c IsoVesta.c1.
  Proof. rewrite c1_c_eq. apply from_Z_repr. Qed.

  Lemma c2_c_repr : represents c2_c IsoVesta.c2.
  Proof. rewrite c2_c_eq. apply from_Z_repr. Qed.

  Lemma c3_c_repr : represents c3_c IsoVesta.c3.
  Proof. rewrite c3_c_eq. apply from_Z_repr. Qed.

  Lemma c4_c_repr : represents c4_c IsoVesta.c4.
  Proof. rewrite c4_c_eq. apply from_Z_repr. Qed.

  Lemma c5_c_repr : represents c5_c IsoVesta.c5.
  Proof. rewrite c5_c_eq. apply from_Z_repr. Qed.

  Lemma c6_c_repr : represents c6_c IsoVesta.c6.
  Proof. rewrite c6_c_eq. apply from_Z_repr. Qed.

  Lemma c7_c_repr : represents c7_c IsoVesta.c7.
  Proof. rewrite c7_c_eq. apply from_Z_repr. Qed.

  Lemma c8_c_repr : represents c8_c IsoVesta.c8.
  Proof. rewrite c8_c_eq. apply from_Z_repr. Qed.

  Lemma c9_c_repr : represents c9_c IsoVesta.c9.
  Proof. rewrite c9_c_eq. apply from_Z_repr. Qed.

  Lemma c10_c_repr : represents c10_c IsoVesta.c10.
  Proof. rewrite c10_c_eq. apply from_Z_repr. Qed.

  Lemma c11_c_repr : represents c11_c IsoVesta.c11.
  Proof. rewrite c11_c_eq. apply from_Z_repr. Qed.

  Lemma c12_c_repr : represents c12_c IsoVesta.c12.
  Proof. rewrite c12_c_eq. apply from_Z_repr. Qed.

  Lemma c13_c_repr : represents c13_c IsoVesta.c13.
  Proof. rewrite c13_c_eq. apply from_Z_repr. Qed.

  Lemma va_c_repr : represents va_c Vesta.a.
  Proof. rewrite va_c_eq. apply from_Z_repr. Qed.

  Lemma vb_c_repr : represents vb_c Vesta.b.
  Proof. rewrite vb_c_eq. apply from_Z_repr. Qed.

  Create HintDb swu_repr discriminated.
  #[local] Hint Constants Opaque : swu_repr.
  #[local] Hint Variables Opaque : swu_repr.
  #[local] Hint Resolve
    from_Z_repr zero_repr one_repr
    mul_repr add_repr sub_repr opp_repr div_repr : swu_repr.
  #[local] Hint Resolve a_c_repr b_c_repr z_c_repr lambda_c_repr theta_c_repr c1_c_repr c2_c_repr c3_c_repr c4_c_repr c5_c_repr c6_c_repr c7_c_repr c8_c_repr c9_c_repr c10_c_repr c11_c_repr c12_c_repr c13_c_repr va_c_repr vb_c_repr : swu_repr.

  Ltac repr := solve [eauto 60 with swu_repr].

  (** ** Boolean bridges *)

  Lemma equal_link (wa wb : Q.t) (a b : Z) :
    represents wa a -> represents wb b ->
    Q.equal wa wb = ((a mod Primes.pallas_q) =? (b mod Primes.pallas_q)).
  Proof.
    intros [Hca Hda] [Hcb Hdb].
    destruct (Q.equal wa wb) eqn:He; symmetry.
    - apply Z.eqb_eq. rewrite <- Hda, <- Hdb.
      now apply (proj1 (PallasQEqualityFacts.equal_denote_iff wa wb Hca Hcb)).
    - apply Z.eqb_neq. rewrite <- Hda, <- Hdb.
      now apply (proj1
        (PallasQEqualityFacts.equal_denote_false_iff wa wb Hca Hcb)).
  Qed.

  Lemma nonzero_link (w : Q.t) (x : Z) :
    represents w x ->
    nonzero_w w = negb ((x mod Primes.pallas_q) =? 0).
  Proof.
    intros Hw. unfold nonzero_w.
    rewrite (equal_link w Q.zero x 0 Hw zero_repr).
    now rewrite Z.mod_0_l by exact q_neq.
  Qed.

  Lemma odd_link (w : Q.t) (x : Z) :
    represents w x -> odd_w w = Z.odd (x mod Primes.pallas_q).
  Proof.
    intros [_ Hd]. unfold odd_w.
    now rewrite PallasQDenoteFacts.to_Z_denote, Hd.
  Qed.

  (** Specification values built by a reducing field operation are fixed
      points of [mod]. *)
  Lemma binop_mul_reduced (a b : Z) :
    BinOp.mul a b mod Primes.pallas_q = BinOp.mul a b.
  Proof. unfold BinOp.mul. now rewrite Z.mod_mod by exact q_neq. Qed.

  Lemma binop_add_reduced (a b : Z) :
    BinOp.add a b mod Primes.pallas_q = BinOp.add a b.
  Proof. unfold BinOp.add. now rewrite Z.mod_mod by exact q_neq. Qed.

  Lemma binop_div_reduced (a b : Z) :
    BinOp.div a b mod Primes.pallas_q = BinOp.div a b.
  Proof. unfold BinOp.div. apply binop_mul_reduced. Qed.

  Lemma unop_from_reduced (a : Z) :
    UnOp.from a mod Primes.pallas_q = UnOp.from a.
  Proof. unfold UnOp.from. now rewrite Z.mod_mod by exact q_neq. Qed.

  (** ** Accessor representation lemmas *)

  Lemma z_u2_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (z_u2_w u) (SswuVesta.z_u2 uz).
  Proof. intros Hu. unfold z_u2_w, SswuVesta.z_u2. repr. Qed.
  #[local] Hint Resolve z_u2_w_repr : swu_repr.

  Lemma ta_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (ta_w u) (SswuVesta.ta uz).
  Proof. intros Hu. unfold ta_w, SswuVesta.ta. repr. Qed.
  #[local] Hint Resolve ta_w_repr : swu_repr.

  Lemma x1_num_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (x1_num_w u) (SswuVesta.x1_num uz).
  Proof. intros Hu. unfold x1_num_w, SswuVesta.x1_num. repr. Qed.
  #[local] Hint Resolve x1_num_w_repr : swu_repr.

  Lemma ta_zero_link (u : Q.t) (uz : Z) :
    represents u uz ->
    Q.equal (ta_w u) Q.zero = (SswuVesta.ta uz =? 0).
  Proof.
    intros Hu.
    rewrite (equal_link (ta_w u) Q.zero (SswuVesta.ta uz) 0
      (ta_w_repr u uz Hu) zero_repr).
    rewrite Z.mod_0_l by exact q_neq.
    unfold SswuVesta.ta. now rewrite binop_add_reduced.
  Qed.

  Lemma x_div_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (x_div_w u) (SswuVesta.x_div uz).
  Proof.
    intros Hu. unfold x_div_w, SswuVesta.x_div.
    rewrite (ta_zero_link u uz Hu).
    destruct (SswuVesta.ta uz =? 0); repr.
  Qed.
  #[local] Hint Resolve x_div_w_repr : swu_repr.

  Lemma x_div3_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (x_div3_w u) (SswuVesta.x_div3 uz).
  Proof. intros Hu. unfold x_div3_w, SswuVesta.x_div3. repr. Qed.
  #[local] Hint Resolve x_div3_w_repr : swu_repr.

  Lemma gx1_num_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (gx1_num_w u) (SswuVesta.gx1_num uz).
  Proof. intros Hu. unfold gx1_num_w, SswuVesta.gx1_num. repr. Qed.
  #[local] Hint Resolve gx1_num_w_repr : swu_repr.

  Lemma x2_num_w_repr (u : Q.t) (uz : Z) :
    represents u uz -> represents (x2_num_w u) (SswuVesta.x2_num uz).
  Proof. intros Hu. unfold x2_num_w, SswuVesta.x2_num. repr. Qed.
  #[local] Hint Resolve x2_num_w_repr : swu_repr.

  Lemma repr_self (w : Q.t) :
    Q.canonical w -> represents w (Q.to_Z w).
  Proof.
    intros Hc. split; [exact Hc |].
    rewrite PallasQDenoteFacts.to_Z_denote.
    now rewrite Z.mod_small by apply denote_range.
  Qed.
  #[local] Hint Resolve repr_self : swu_repr.
  #[local] Hint Resolve repr_from : swu_repr.

  (** ** Witness and nonexceptionality boolean links *)

  Lemma swu_nonexceptionalb_w_link (u : Q.t) (uz : Z) :
    represents u uz ->
    swu_nonexceptionalb_w u = SswuVestaWitness.swu_nonexceptionalb uz.
  Proof.
    intros Hu.
    unfold swu_nonexceptionalb_w, SswuVestaWitness.swu_nonexceptionalb,
      SswuVestaWitness.field_nonzerob.
    rewrite (nonzero_link _ _ (gx1_num_w_repr u uz Hu)).
    rewrite (nonzero_link _ _ (x_div3_w_repr u uz Hu)).
    unfold UnOp.from. reflexivity.
  Qed.

  Lemma swu_witness_okb_w_link
      (u root : Q.t) (uz rootz : Z) (ws : bool) :
    represents u uz -> represents root rootz ->
    swu_witness_okb_w u ws root = SswuVesta.swu_witness_ok uz ws rootz.
  Proof.
    intros Hu Hr.
    unfold swu_witness_okb_w, SswuVesta.swu_witness_ok,
      SswuVesta.sqrt_ratio_witness_ok.
    destruct ws.
    - rewrite (equal_link
        (Q.mul (Q.mul root root) (x_div3_w u)) (gx1_num_w u)
        (BinOp.mul (BinOp.mul rootz rootz) (SswuVesta.x_div3 uz))
        (SswuVesta.gx1_num uz)
        ltac:(repr) (gx1_num_w_repr u uz Hu)).
      rewrite binop_mul_reduced.
      unfold UnOp.from. reflexivity.
    - rewrite (equal_link
        (Q.mul (Q.mul root root) (x_div3_w u))
        (Q.mul lambda_c (gx1_num_w u))
        (BinOp.mul (BinOp.mul rootz rootz) (SswuVesta.x_div3 uz))
        (BinOp.mul IsoVesta.lambda (SswuVesta.gx1_num uz))
        ltac:(repr) ltac:(repr)).
      now rewrite !binop_mul_reduced.
  Qed.

  (** ** The witnessed SSWU map coordinates *)

  Definition spec_map_x (uz : Z) (ws : bool) : Z :=
    BinOp.div
      (if ws then SswuVesta.x1_num uz else SswuVesta.x2_num uz)
      (SswuVesta.x_div uz).

  Definition spec_y_pre (uz rootz : Z) (ws : bool) : Z :=
    if ws then rootz
    else
      BinOp.mul
        (BinOp.mul (BinOp.mul IsoVesta.theta (SswuVesta.z_u2 uz)) uz)
        rootz.

  Definition spec_map_y (uz rootz : Z) (ws : bool) : Z :=
    if xorb (SswuVesta.sgn0 uz) (SswuVesta.sgn0 (spec_y_pre uz rootz ws))
    then UnOp.opp (spec_y_pre uz rootz ws)
    else UnOp.from (spec_y_pre uz rootz ws).

  Lemma map_with_root_eq (uz rootz : Z) (ws : bool) :
    SswuVesta.map_to_curve_simple_swu_with_root uz ws rootz =
      Weierstrass.Affine (spec_map_x uz ws) (spec_map_y uz rootz ws).
  Proof.
    unfold SswuVesta.map_to_curve_simple_swu_with_root,
      spec_map_x, spec_map_y, spec_y_pre.
    destruct ws; reflexivity.
  Qed.

  Lemma sgn0_link (w : Q.t) (x : Z) :
    represents w x -> odd_w w = SswuVesta.sgn0 x.
  Proof.
    intros Hw. rewrite (odd_link w x Hw).
    unfold SswuVesta.sgn0, UnOp.from. reflexivity.
  Qed.

  Lemma swu_y_pre_w_repr (u root : Q.t) (uz rootz : Z) (ws : bool) :
    represents u uz -> represents root rootz ->
    represents (swu_y_pre_w u ws root) (spec_y_pre uz rootz ws).
  Proof.
    intros Hu Hr. unfold swu_y_pre_w, spec_y_pre.
    destruct ws; [assumption | repr].
  Qed.

  Lemma swu_x_w_repr (u : Q.t) (uz : Z) (ws : bool) :
    represents u uz -> represents (swu_x_w u ws) (spec_map_x uz ws).
  Proof.
    intros Hu. unfold swu_x_w, spec_map_x.
    destruct ws; repr.
  Qed.

  Lemma swu_y_w_repr (u root : Q.t) (uz rootz : Z) (ws : bool) :
    represents u uz -> represents root rootz ->
    represents (swu_y_w u ws root) (spec_map_y uz rootz ws).
  Proof.
    intros Hu Hr. unfold swu_y_w, spec_map_y.
    pose proof (swu_y_pre_w_repr u root uz rootz ws Hu Hr) as Hpre.
    rewrite (sgn0_link u uz Hu), (sgn0_link _ _ Hpre).
    destruct (xorb _ _).
    - now apply opp_repr.
    - now apply repr_from.
  Qed.

  (** ** Secant addition and the isogeny map *)

  Definition spec_secant_x (xa ya xb yb : Z) : Z :=
    let lam := BinOp.div (BinOp.sub yb ya) (BinOp.sub xb xa) in
    BinOp.sub (BinOp.sub (BinOp.mul lam lam) xa) xb.

  Definition spec_secant_y (xa ya xb yb : Z) : Z :=
    let lam := BinOp.div (BinOp.sub yb ya) (BinOp.sub xb xa) in
    BinOp.sub (BinOp.mul lam (BinOp.sub xa (spec_secant_x xa ya xb yb))) ya.

  Lemma add_guard_link (wxa wxb : Q.t) (xa xb : Z) :
    represents wxa xa -> represents wxb xb ->
    Q.equal (Q.sub wxa wxb) Q.zero = (BinOp.sub xa xb =? 0).
  Proof.
    intros Ha Hb.
    rewrite (equal_link (Q.sub wxa wxb) Q.zero (BinOp.sub xa xb) 0
      ltac:(repr) zero_repr).
    rewrite Z.mod_0_l by exact q_neq.
    unfold BinOp.sub. now rewrite Z.mod_mod by exact q_neq.
  Qed.

  Lemma iso_add_secant (xa ya xb yb : Z) :
    (BinOp.sub xa xb =? 0) = false ->
    IsoVesta.add (Weierstrass.Affine xa ya) (Weierstrass.Affine xb yb) =
      Weierstrass.Affine
        (spec_secant_x xa ya xb yb) (spec_secant_y xa ya xb yb).
  Proof.
    intros Hguard.
    unfold IsoVesta.add, Weierstrass.add.
    change ((xa -F xb) =? 0) with (BinOp.sub xa xb =? 0).
    rewrite Hguard.
    unfold spec_secant_x, spec_secant_y. cbv zeta. reflexivity.
  Qed.

  Lemma secant_x_w_repr
      (wxa wya wxb wyb : Q.t) (xa ya xb yb : Z) :
    represents wxa xa -> represents wya ya ->
    represents wxb xb -> represents wyb yb ->
    represents (secant_x_w wxa wya wxb wyb) (spec_secant_x xa ya xb yb).
  Proof.
    intros. unfold secant_x_w, secant_lambda_w, spec_secant_x.
    cbv zeta. repr.
  Qed.

  Lemma secant_y_w_repr
      (wxa wya wxb wyb : Q.t) (xa ya xb yb : Z) :
    represents wxa xa -> represents wya ya ->
    represents wxb xb -> represents wyb yb ->
    represents (secant_y_w wxa wya wxb wyb) (spec_secant_y xa ya xb yb).
  Proof.
    intros.
    unfold secant_y_w, secant_lambda_w, secant_x_w, spec_secant_y,
      spec_secant_x.
    cbv zeta.
    apply sub_repr; [| assumption].
    apply mul_repr.
    - apply div_repr; repr.
    - apply sub_repr; [assumption |].
      apply sub_repr; [| assumption].
      apply sub_repr; [| assumption].
      apply mul_repr; apply div_repr; repr.
  Qed.

  Definition spec_iso_x_num (x : Z) : Z :=
    BinOp.add
      (BinOp.mul
        (BinOp.add
          (BinOp.mul (BinOp.add (BinOp.mul IsoVesta.c1 x) IsoVesta.c2) x)
          IsoVesta.c3) x)
      IsoVesta.c4.

  Definition spec_iso_x_den (x : Z) : Z :=
    BinOp.add (BinOp.mul (BinOp.add x IsoVesta.c5) x) IsoVesta.c6.

  Definition spec_iso_y_num (x y : Z) : Z :=
    BinOp.mul
      (BinOp.add
        (BinOp.mul
          (BinOp.add
            (BinOp.mul (BinOp.add (BinOp.mul IsoVesta.c7 x) IsoVesta.c8) x)
            IsoVesta.c9) x)
        IsoVesta.c10)
      y.

  Definition spec_iso_y_den (x : Z) : Z :=
    BinOp.add
      (BinOp.mul
        (BinOp.add (BinOp.mul (BinOp.add x IsoVesta.c11) x) IsoVesta.c12)
        x)
      IsoVesta.c13.

  Lemma iso_map_eq (x y : Z) :
    (spec_iso_x_den x =? 0) = false ->
    (spec_iso_y_den x =? 0) = false ->
    SswuVesta.iso_map (Weierstrass.Affine x y) =
      Weierstrass.Affine
        (BinOp.div (spec_iso_x_num x) (spec_iso_x_den x))
        (BinOp.div (spec_iso_y_num x y) (spec_iso_y_den x)).
  Proof.
    intros Hx Hy.
    unfold SswuVesta.iso_map. cbv zeta.
    change ((x +F IsoVesta.c5) *F x +F IsoVesta.c6) with (spec_iso_x_den x).
    change (((x +F IsoVesta.c11) *F x +F IsoVesta.c12) *F x
      +F IsoVesta.c13) with (spec_iso_y_den x).
    rewrite Hx, Hy. cbn [orb]. reflexivity.
  Qed.

  Lemma iso_x_num_w_repr (wx : Q.t) (x : Z) :
    represents wx x -> represents (iso_x_num_w wx) (spec_iso_x_num x).
  Proof. intros. unfold iso_x_num_w, spec_iso_x_num. repr. Qed.

  Lemma iso_x_den_w_repr (wx : Q.t) (x : Z) :
    represents wx x -> represents (iso_x_den_w wx) (spec_iso_x_den x).
  Proof. intros. unfold iso_x_den_w, spec_iso_x_den. repr. Qed.

  Lemma iso_y_num_w_repr (wx wy : Q.t) (x y : Z) :
    represents wx x -> represents wy y ->
    represents (iso_y_num_w wx wy) (spec_iso_y_num x y).
  Proof. intros. unfold iso_y_num_w, spec_iso_y_num. repr. Qed.

  Lemma iso_y_den_w_repr (wx : Q.t) (x : Z) :
    represents wx x -> represents (iso_y_den_w wx) (spec_iso_y_den x).
  Proof. intros. unfold iso_y_den_w, spec_iso_y_den. repr. Qed.

  Lemma den_nonzero_link (wd : Q.t) (d : Z) :
    represents wd d ->
    (d mod Primes.pallas_q) = d ->
    nonzero_w wd = negb (d =? 0).
  Proof.
    intros Hd Hred. rewrite (nonzero_link wd d Hd). now rewrite Hred.
  Qed.

  Lemma spec_iso_x_den_reduced (x : Z) :
    spec_iso_x_den x mod Primes.pallas_q = spec_iso_x_den x.
  Proof. unfold spec_iso_x_den. apply binop_add_reduced. Qed.

  Lemma spec_iso_y_den_reduced (x : Z) :
    spec_iso_y_den x mod Primes.pallas_q = spec_iso_y_den x.
  Proof. unfold spec_iso_y_den. apply binop_add_reduced. Qed.

  (** ** Final coordinate comparison and curve membership *)

  Lemma checked_value_eq (ww wexp : Q.t) (v : Z) :
    represents ww v -> Q.canonical wexp ->
    Q.equal ww wexp = true ->
    v mod Primes.pallas_q = UnOp.from (Q.to_Z wexp).
  Proof.
    intros [Hc Hd] Hcexp He.
    apply (proj1 (PallasQEqualityFacts.equal_denote_iff ww wexp Hc Hcexp))
      in He.
    rewrite <- Hd, He.
    unfold UnOp.from.
    rewrite PallasQDenoteFacts.to_Z_denote.
    now rewrite Z.mod_small by apply denote_range.
  Qed.

  Lemma on_curvebw_link (wx wy : Q.t) :
    Q.canonical wx -> Q.canonical wy ->
    on_curvebw wx wy = true ->
    Vesta.on_curveb (Vesta.affine (Q.to_Z wx) (Q.to_Z wy)) = true.
  Proof.
    intros Hcx Hcy Hcheck.
    unfold on_curvebw in Hcheck.
    unfold Vesta.on_curveb, Vesta.affine.
    rewrite (equal_link
      (Q.mul wy wy)
      (Q.add
        (Q.add (Q.mul (Q.mul wx wx) wx) (Q.mul va_c wx))
        vb_c)
      (BinOp.mul (UnOp.from (Q.to_Z wy)) (UnOp.from (Q.to_Z wy)))
      (BinOp.add
        (BinOp.add
          (BinOp.mul
            (BinOp.mul (UnOp.from (Q.to_Z wx)) (UnOp.from (Q.to_Z wx)))
            (UnOp.from (Q.to_Z wx)))
          (BinOp.mul Vesta.a (UnOp.from (Q.to_Z wx))))
        Vesta.b)
      ltac:(repr) ltac:(repr)) in Hcheck.
    exact Hcheck.
  Qed.

  (** ** Soundness of the complete word-level check *)

  Lemma witnesses_part
      (u0 u1 root0 root1 : Z) (ws0 ws1 : bool)
      (Hwits : witnessesb u0 u1 ws0 root0 ws1 root1 = true) :
    SswuVestaWitness.canonical_witnesses_ok_for
      u0 u1 ws0 root0 ws1 root1 = true.
  Proof.
    unfold witnessesb in Hwits.
    apply andb_prop in Hwits as [Hwit0 Hwit1].
    apply andb_prop in Hwit0 as [Hnon0 Hok0].
    apply andb_prop in Hwit1 as [Hnon1 Hok1].
    pose proof (from_Z_repr u0) as Hu0.
    pose proof (from_Z_repr u1) as Hu1.
    pose proof (from_Z_repr root0) as Hr0.
    pose proof (from_Z_repr root1) as Hr1.
    unfold SswuVestaWitness.canonical_witnesses_ok_for.
    rewrite <- (swu_nonexceptionalb_w_link _ _ Hu0).
    rewrite <- (swu_witness_okb_w_link _ _ _ _ ws0 Hu0 Hr0).
    rewrite <- (swu_nonexceptionalb_w_link _ _ Hu1).
    rewrite <- (swu_witness_okb_w_link _ _ _ _ ws1 Hu1 Hr1).
    now rewrite Hnon0, Hok0, Hnon1, Hok1.
  Qed.

  Lemma point_part
      (u0 u1 root0 root1 : Z) (ws0 ws1 : bool) (wx wy : Q.t)
      (Hcx : Q.canonical wx) (Hcy : Q.canonical wy)
      (Hguard : guardb u0 ws0 u1 ws1 = true)
      (Hdens : densb u0 root0 ws0 u1 root1 ws1 = true)
      (Hxeq : x_eqb u0 root0 ws0 u1 root1 ws1 wx = true)
      (Hyeq : y_eqb u0 root0 ws0 u1 root1 ws1 wy = true) :
    GroupHashVesta.point_eqb
      (SswuVestaWitness.group_hash_from_field_with_witness
        u0 u1 ws0 root0 ws1 root1)
      (Vesta.affine (Q.to_Z wx) (Q.to_Z wy)) = true.
  Proof.
    unfold guardb, map_x_w in Hguard.
    unfold densb, sum_x_w, map_x_w, map_y_w in Hdens.
    apply andb_prop in Hdens as [Hxden Hyden].
    unfold x_eqb, sum_x_w, map_x_w, map_y_w in Hxeq.
    unfold y_eqb, sum_x_w, sum_y_w, map_x_w, map_y_w in Hyeq.
    pose proof (from_Z_repr u0) as Hu0.
    pose proof (from_Z_repr u1) as Hu1.
    pose proof (from_Z_repr root0) as Hr0.
    pose proof (from_Z_repr root1) as Hr1.
    pose proof (swu_x_w_repr _ u0 ws0 Hu0) as Hxa.
    pose proof (swu_y_w_repr _ _ u0 root0 ws0 Hu0 Hr0) as Hya.
    pose proof (swu_x_w_repr _ u1 ws1 Hu1) as Hxb.
    pose proof (swu_y_w_repr _ _ u1 root1 ws1 Hu1 Hr1) as Hyb.
    pose proof (secant_x_w_repr _ _ _ _ _ _ _ _ Hxa Hya Hxb Hyb) as Hx3.
    pose proof (secant_y_w_repr _ _ _ _ _ _ _ _ Hxa Hya Hxb Hyb) as Hy3.
    unfold SswuVestaWitness.group_hash_from_field_with_witness.
    rewrite !map_with_root_eq.
    rewrite iso_add_secant.
    2: {
      rewrite <- (add_guard_link _ _ _ _ Hxa Hxb).
      apply negb_true_iff. exact Hguard.
    }
    rewrite iso_map_eq.
    2: {
      apply negb_true_iff.
      rewrite <- (den_nonzero_link _ _
        (iso_x_den_w_repr _ _ Hx3) (spec_iso_x_den_reduced _)).
      exact Hxden.
    }
    2: {
      apply negb_true_iff.
      rewrite <- (den_nonzero_link _ _
        (iso_y_den_w_repr _ _ Hx3)
        (spec_iso_y_den_reduced _)).
      exact Hyden.
    }
    unfold Vesta.affine, GroupHashVesta.point_eqb.
    apply andb_true_intro. split; apply Z.eqb_eq.
    - rewrite <- (binop_div_reduced
        (spec_iso_x_num _) (spec_iso_x_den _)).
      apply (checked_value_eq _ wx _
        (div_repr _ _ _ _
          (iso_x_num_w_repr _ _ Hx3) (iso_x_den_w_repr _ _ Hx3))
        Hcx Hxeq).
    - rewrite <- (binop_div_reduced
        (spec_iso_y_num _ _) (spec_iso_y_den _)).
      apply (checked_value_eq _ wy _
        (div_repr _ _ _ _
          (iso_y_num_w_repr _ _ _ _ Hx3 Hy3) (iso_y_den_w_repr _ _ Hx3))
        Hcy Hyeq).
  Qed.

  Theorem group_hash_checkb_sound
      (u0 u1 root0 root1 : Z) (ws0 ws1 : bool) (wx wy : Q.t) :
    Q.canonical wx -> Q.canonical wy ->
    group_hash_checkb u0 u1 ws0 root0 ws1 root1 wx wy = true ->
    SswuVestaWitness.canonical_witnesses_ok_for
      u0 u1 ws0 root0 ws1 root1 = true /\
    GroupHashVesta.point_eqb
      (SswuVestaWitness.group_hash_from_field_with_witness
        u0 u1 ws0 root0 ws1 root1)
      (Vesta.affine (Q.to_Z wx) (Q.to_Z wy)) = true /\
    Vesta.on_curveb (Vesta.affine (Q.to_Z wx) (Q.to_Z wy)) = true.
  Proof.
    intros Hcx Hcy Hcheck.
    unfold group_hash_checkb in Hcheck.
    apply andb_prop in Hcheck as [Hcheck Hcurve].
    apply andb_prop in Hcheck as [Hwits Hpoint].
    apply andb_prop in Hpoint as [Hguard Hpoint].
    apply andb_prop in Hpoint as [Hdens Hcoords].
    apply andb_prop in Hcoords as [Hxeq Hyeq].
    split; [| split].
    - exact (witnesses_part u0 u1 root0 root1 ws0 ws1 Hwits).
    - exact (point_part u0 u1 root0 root1 ws0 ws1 wx wy Hcx Hcy
        Hguard Hdens Hxeq Hyeq).
    - exact (on_curvebw_link wx wy Hcx Hcy Hcurve).
  Qed.
  (** ** Shared-evaluation form for certificates

      The named-conjunction [group_hash_checkb] re-evaluates the map and
      secant points in several conjuncts; each re-evaluation pays modular
      inversions.  This form binds the intermediate points once, so the
      virtual machine evaluates each inversion once per entry.  Both forms
      are definitionally equal. *)
  Definition group_hash_checkb_exec
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (x y : Q.t) : bool :=
    let u0w := Q.from_Z u0 in
    let u1w := Q.from_Z u1 in
    let root0w := Q.from_Z root0 in
    let root1w := Q.from_Z root1 in
    let xa := swu_x_w u0w was_square0 in
    let ya := swu_y_w u0w was_square0 root0w in
    let xb := swu_x_w u1w was_square1 in
    let yb := swu_y_w u1w was_square1 root1w in
    let x3 := secant_x_w xa ya xb yb in
    let y3 := secant_y_w xa ya xb yb in
    ((swu_nonexceptionalb_w u0w
        && swu_witness_okb_w u0w was_square0 root0w)
      && (swu_nonexceptionalb_w u1w
        && swu_witness_okb_w u1w was_square1 root1w))
      && (negb (Q.equal (Q.sub xa xb) Q.zero)
        && ((nonzero_w (iso_x_den_w x3) && nonzero_w (iso_y_den_w x3))
          && (Q.equal (div_w (iso_x_num_w x3) (iso_x_den_w x3)) x
            && Q.equal (div_w (iso_y_num_w x3 y3) (iso_y_den_w x3)) y)))
      && on_curvebw x y.

  Lemma group_hash_checkb_exec_eq
      (u0 u1 : Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z)
      (x y : Q.t) :
    group_hash_checkb_exec u0 u1 was_square0 root0 was_square1 root1 x y =
      group_hash_checkb u0 u1 was_square0 root0 was_square1 root1 x y.
  Proof. reflexivity. Qed.
End SswuVestaWords.
