(** * ⊥-carrying Sinsemilla specification variants

    §4.18.4 'Action Statement (Orchard)' of the Zcash protocol specification
    ([docs/protocol.pdf]) states its commitment clauses disjunctively —
    'New note commitment integrity' reads
    [Extract⊥_P(NoteCommit^Orchard_rcm(…)) ∈ {cm_x, ⊥}], 'Old note commitment
    integrity' reads [NoteCommit^Orchard_rcm(…) ∈ {cm_old, ⊥}], and
    'Diversified address integrity' reads [ivk = ⊥ ∨ pk_d = [ivk] g_d] —
    because §5.4.1.9 'Sinsemilla Hash Function' defines the hash through the
    partial incomplete addition [⊞], which returns [⊥] on the exceptional
    operand pairs the circuit's gates do not constrain.

    [Garden/Orchard/protocol_spec.v] transcribes those functions as total
    functions (on the exceptional cases they compute the chip's chord-formula
    value); the theorems consuming them select the non-⊥ branch through
    [SinsemillaHash.nondegenerate] hypotheses.  This file carries the
    ⊥-carrying ([option]-valued) variants, so the disjunctive protocol
    clauses can be stated and proved without nondegeneracy hypotheses.

    The entire ⊥ surface of the §4.18.4 output functions is one operation:
    [EccSpec.point_add_incomplete], reached only through
    [SinsemillaSpec.round] and [SinsemillaSpec.sinsemilla_hash_to_point].
    The spend-authority, value-commitment and nullifier functions use
    complete addition and total group multiples and need no variants; the
    variants here cover the Sinsemilla chain only — the hash-to-point fold,
    and the [NoteCommit^Orchard] / [Commit^ivk] / [Extract⊥_P] commitment
    layers above it ([option_map] shells).

    Design invariant: [round_bot]'s two guards are verbatim the negated
    conjuncts of [SinsemillaHash.nondegenerate]
    ([sinsemilla/hash_to_point_proof.v]), so definedness of the ⊥-carrying
    fold is *equivalent* to nondegeneracy ([hash_to_point_bot_iff]) and
    every nondegeneracy-conditioned theorem of the total layer is reusable
    verbatim on the tracking branch.  [protocol_spec.v],
    [internal_spec.v] and the gadget spec files keep their total
    functions; the variants live alongside them. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardProtocolSpecBot.

  (** ** The ⊥-carrying hash-to-point fold

      §5.4.1.9 defines incomplete addition
      [⊞ : (P ∪ {⊥}) × (P ∪ {⊥}) → P ∪ {⊥}] with
      [(x, y) ⊞ (x′, y′) = ⊥ if x = x′], propagates [⊥] through both
      operand positions, and folds it as
      [Acc ← (Acc ⊞ 𝒮(m_i)) ⊞ Acc] from [Acc = 𝒬(D)].  [None] is the
      protocol's [⊥]. *)

  (** One Sinsemilla round, ⊥-carrying: [Acc ← (Acc ⊞ 𝒮(m)) ⊞ Acc]
      (§5.4.1.9).  The first guard is the exceptional case of
      [Acc ⊞ 𝒮(m)] (equal x-coordinates), the second that of
      [(Acc + 𝒮(m)) ⊞ Acc]; they are spelled as the negations of the two
      conjuncts of [SinsemillaHash.nondegenerate], which is what makes
      [hash_to_point_bot_iff] an equivalence.  The three identity-operand
      [⊥] clauses of [⊞] ([𝒪_P ⊞ 𝒪_P], [𝒪_P ⊞ (x′,y′)], [(x,y) ⊞ 𝒪_P])
      are not spelled here; see [round_bot_no_identity] for why they are
      unreachable. *)
  Definition round_bot (acc : option Point.t) (word : Z) : option Point.t :=
    match acc with
    | None => None
    | Some acc =>
        if Point.x acc =? Point.x (SinsemillaSpec.generator word)
        then None
        else if Point.x acc =?
          Point.x (EccSpec.point_add_incomplete acc (SinsemillaSpec.generator word))
        then None
        else
          Some
            (EccSpec.point_add_incomplete
              (EccSpec.point_add_incomplete acc (SinsemillaSpec.generator word))
              acc)
    end.

  (** §5.4.1.9 [SinsemillaHashToPoint(D, M) → P ∪ {⊥}]: the left fold of
      [round_bot] over the message words, seeded by the domain point [Q]. *)
  Definition sinsemilla_hash_to_point_bot (Q : Point.t) (words : list Z)
      : option Point.t :=
    Stdlib.Lists.List.fold_left round_bot words (Some Q).

  (** §5.4.1.9 [SinsemillaHash(D, M) := Extract⊥_P(SinsemillaHashToPoint(D, M))],
      with §5.4.9.7 [Extract⊥_P(⊥) = ⊥]. *)
  Definition sinsemilla_hash_bot (Q : Point.t) (words : list Z) : option Z :=
    option_map EccSpec.extract_x (sinsemilla_hash_to_point_bot Q words).

  (** ** Fold algebra: [None] is absorbing, the fold decomposes at the tail *)

  Lemma round_bot_none (word : Z) : round_bot None word = None.
  Proof. reflexivity. Qed.

  Lemma round_bot_fold_none (words : list Z) :
    Stdlib.Lists.List.fold_left round_bot words None = None.
  Proof.
    induction words as [| w ws IH]; cbn; [reflexivity | exact IH].
  Qed.

  Lemma hash_to_point_bot_nil (Q : Point.t) :
    sinsemilla_hash_to_point_bot Q [] = Some Q.
  Proof. reflexivity. Qed.

  Lemma hash_to_point_bot_app (Q : Point.t) (words : list Z) (word : Z) :
    sinsemilla_hash_to_point_bot Q (words ++ [word]) =
      round_bot (sinsemilla_hash_to_point_bot Q words) word.
  Proof.
    unfold sinsemilla_hash_to_point_bot.
    now rewrite Stdlib.Lists.List.fold_left_app.
  Qed.

  (** Definedness of the fold is inherited by every prefix — the [None]
      absorber read backwards. *)
  Lemma hash_to_point_bot_defined_prefix (Q : Point.t) (ws1 ws2 : list Z) :
    sinsemilla_hash_to_point_bot Q (ws1 ++ ws2) <> None ->
    sinsemilla_hash_to_point_bot Q ws1 <> None.
  Proof.
    unfold sinsemilla_hash_to_point_bot.
    rewrite Stdlib.Lists.List.fold_left_app.
    intros Hdef Hnone.
    apply Hdef.
    rewrite Hnone.
    apply round_bot_fold_none.
  Qed.

  (** ** §5.4.1.9 fidelity: the identity-operand [⊥] clauses are unreachable

      [round_bot] omits the three [⊞] clauses with an [𝒪_P] operand.  The
      protocol's own argument (the proof of Theorem 5.4.4, §5.4.1.9): "Since
      none of 𝒬(D) or {𝒮(j) | j ∈ {0 .. 2^k − 1}} are 𝒪_P, no intermediate
      results can be 𝒪_P unless one of the preceding conditions occurs" —
      the preceding conditions being [Acc = ±𝒮(m)] and [Acc + 𝒮(m) = ±Acc],
      which on the curve are exactly the equal-x guards of [round_bot]
      ([x(P) = x(Q) ↔ P = ±Q]).  In-model the identity is the [(0, 0)]
      sentinel ([EccSpec.identity]) and no point satisfying the Pallas curve
      equation has [x = 0] ([EccSpec.pallas_curve_x_nonzero], from [b = 5]
      being a quadratic non-residue, §5.4.9.7 note): every on-curve operand
      — the domain point, every table generator, and every on-curve
      intermediate accumulator — is distinct from the sentinel
      ([round_bot_no_identity] below is that step), so the omitted clauses
      cannot fire on the tracking branch, where every operand stays on the
      curve. *)
  Lemma round_bot_no_identity (P : Point.t)
      (Hcurve :
        Point.y P *F Point.y P -F (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0) :
    Point.x P <> 0 /\ P <> EccSpec.identity.
  Proof.
    pose proof (EccSpec.pallas_curve_x_nonzero (Point.x P) (Point.y P) Hcurve)
      as Hfrom.
    assert (Hx : Point.x P <> 0).
    { intros Hx0. apply Hfrom. rewrite Hx0. reflexivity. }
    split; [exact Hx |].
    intros Hid. apply Hx. rewrite Hid. reflexivity.
  Qed.

  (** ** List helpers for the bridge inductions *)

  Lemma firstn_succ_nth {A : Type} (d : A) :
    forall (l : list A) (k : nat),
      (k < List.length l)%nat ->
      List.firstn (S k) l = List.firstn k l ++ [List.nth k l d].
  Proof.
    induction l as [| x l IH]; intros k Hk; cbn in Hk; [lia |].
    destruct k as [| k]; cbn.
    - reflexivity.
    - f_equal. apply IH. lia.
  Qed.

  (** [nondegenerate] restricts along a tail extension: the first
      [length words] rounds of [words ++ [word]] are those of [words]. *)
  Lemma nondegenerate_app_inv (Q : Point.t) (words : list Z) (word : Z) :
    SinsemillaHash.nondegenerate Q (words ++ [word]) ->
    SinsemillaHash.nondegenerate Q words.
  Proof.
    intros Hnd k Hk.
    assert (Hk' : (k < List.length (words ++ [word]))%nat)
      by (rewrite List.length_app; cbn; lia).
    specialize (Hnd k Hk').
    cbn zeta in Hnd |- *.
    rewrite List.firstn_app in Hnd.
    replace (k - List.length words)%nat with 0%nat in Hnd by lia.
    cbn [List.firstn] in Hnd.
    rewrite List.app_nil_r in Hnd.
    rewrite List.app_nth1 in Hnd by exact Hk.
    exact Hnd.
  Qed.

  (** ** The nondegenerate-branch bridge

      On a defined fold, the ⊥-carrying and total layers compute the same
      point; definedness is equivalent to [SinsemillaHash.nondegenerate].
      These three lemmas are the whole interface between the ⊥-carrying
      spec and the nondegeneracy-conditioned theorem surface. *)

  Lemma hash_to_point_bot_some_eq
      (Q : Point.t) (words : list Z) (acc : Point.t) :
    sinsemilla_hash_to_point_bot Q words = Some acc ->
    SinsemillaSpec.sinsemilla_hash_to_point Q words = acc.
  Proof.
    revert acc.
    induction words as [| w ws IH] using List.rev_ind; intros acc Hacc.
    - cbn in Hacc. injection Hacc as Hacc. subst acc. reflexivity.
    - rewrite hash_to_point_bot_app in Hacc.
      rewrite SinsemillaSpec.sinsemilla_hash_to_point_app.
      destruct (sinsemilla_hash_to_point_bot Q ws) as [b |] eqn:Hb.
      2: { cbn in Hacc. discriminate. }
      rewrite (IH b eq_refl).
      unfold round_bot in Hacc.
      destruct (Point.x b =? Point.x (SinsemillaSpec.generator w));
        [discriminate |].
      destruct (Point.x b =?
          Point.x (EccSpec.point_add_incomplete b (SinsemillaSpec.generator w)));
        [discriminate |].
      injection Hacc as Hacc. subst acc.
      reflexivity.
  Qed.

  Lemma hash_to_point_bot_some (Q : Point.t) (words : list Z) :
    SinsemillaHash.nondegenerate Q words ->
    sinsemilla_hash_to_point_bot Q words =
      Some (SinsemillaSpec.sinsemilla_hash_to_point Q words).
  Proof.
    induction words as [| w ws IH] using List.rev_ind; intros Hnd.
    - reflexivity.
    - rewrite hash_to_point_bot_app.
      rewrite (IH (nondegenerate_app_inv Q ws w Hnd)).
      rewrite SinsemillaSpec.sinsemilla_hash_to_point_app.
      assert (Hlen : (List.length ws < List.length (ws ++ [w]))%nat)
        by (rewrite List.length_app; cbn; lia).
      specialize (Hnd (List.length ws) Hlen).
      cbn zeta in Hnd.
      rewrite List.firstn_app, List.app_nth2, Nat.sub_diag in Hnd by lia.
      cbn [List.firstn List.nth] in Hnd.
      rewrite List.app_nil_r, List.firstn_all in Hnd.
      destruct Hnd as [Hg1 Hg2].
      set (a := SinsemillaSpec.sinsemilla_hash_to_point Q ws) in *.
      unfold round_bot.
      destruct (Z.eqb_spec (Point.x a) (Point.x (SinsemillaSpec.generator w)))
        as [E | _]; [exfalso; exact (Hg1 E) |].
      destruct (Z.eqb_spec (Point.x a)
          (Point.x (EccSpec.point_add_incomplete a (SinsemillaSpec.generator w))))
        as [E | _]; [exfalso; exact (Hg2 E) |].
      unfold SinsemillaSpec.round.
      reflexivity.
  Qed.

  Lemma hash_to_point_bot_iff (Q : Point.t) (words : list Z) :
    sinsemilla_hash_to_point_bot Q words <> None <->
    SinsemillaHash.nondegenerate Q words.
  Proof.
    split.
    - intros Hdef k Hk.
      assert (Hpre :
          sinsemilla_hash_to_point_bot Q (List.firstn (S k) words) <> None).
      { apply (hash_to_point_bot_defined_prefix Q
          (List.firstn (S k) words) (List.skipn (S k) words)).
        rewrite List.firstn_skipn.
        exact Hdef. }
      rewrite (firstn_succ_nth 0 words k Hk) in Hpre.
      rewrite hash_to_point_bot_app in Hpre.
      destruct (sinsemilla_hash_to_point_bot Q (List.firstn k words))
        as [b |] eqn:Hb.
      2: { exfalso. apply Hpre. reflexivity. }
      pose proof (hash_to_point_bot_some_eq Q (List.firstn k words) b Hb)
        as Hb_eq.
      cbn zeta.
      rewrite Hb_eq.
      unfold round_bot in Hpre.
      revert Hpre.
      destruct (Z.eqb_spec (Point.x b)
          (Point.x (SinsemillaSpec.generator (List.nth k words 0))))
        as [E1 | Hne1].
      { intros Hpre. exfalso. apply Hpre. reflexivity. }
      destruct (Z.eqb_spec (Point.x b)
          (Point.x (EccSpec.point_add_incomplete b
            (SinsemillaSpec.generator (List.nth k words 0)))))
        as [E2 | Hne2].
      { intros Hpre. exfalso. apply Hpre. reflexivity. }
      intros _.
      exact (conj Hne1 Hne2).
    - intros Hnd.
      rewrite (hash_to_point_bot_some Q words Hnd).
      discriminate.
  Qed.

  (** The ⊥ branch is a concrete statement about the witnessed word list:
      the fold is [None] exactly when some round meets an exceptional
      operand pair. *)
  Lemma hash_to_point_bot_none_iff (Q : Point.t) (words : list Z) :
    sinsemilla_hash_to_point_bot Q words = None <->
    ~ SinsemillaHash.nondegenerate Q words.
  Proof.
    split.
    - intros Hnone Hnd.
      rewrite (hash_to_point_bot_some Q words Hnd) in Hnone.
      discriminate.
    - intros Hnnd.
      destruct (sinsemilla_hash_to_point_bot Q words) as [b |] eqn:Hb;
        [| reflexivity].
      exfalso.
      apply Hnnd.
      apply (proj1 (hash_to_point_bot_iff Q words)).
      rewrite Hb.
      discriminate.
  Qed.

  (** ** The commitment layers — [option_map] shells over the fold

      Each is the corresponding [OrchardProtocolSpec] function with the
      total hash-to-point replaced by the ⊥-carrying one; the layers above
      the fold (complete addition of the blinding multiple, [Extract_P])
      are total, so [⊥] only propagates ([option_map]).  The blinding term
      is the group multiple ([OrchardProtocolSpec.mul_note_commit_r] /
      [mul_commit_ivk_r]) — the §4.18.4 specification-of-record shape, not
      the circuit-structured [EccSpec.scalar_mul]. *)

  (** §5.4.8.4 [NoteCommit^Orchard_rcm(g⋆_d, pk⋆_d, v, ρ, ψ)], ⊥-carrying:
      [⊥] if the [SinsemillaHashToPoint] of the 109-word note message is
      [⊥], else the hash point blinded by [[rcm] GroupHash^P(D || "-r", "")].
      Consumed by §4.18.4 'Old note commitment integrity'
      ([… ∈ {cm_old, ⊥}]). *)
  Definition note_commit_bot
      (prm : OrchardSpec.Params) (g_d pk_d : Point.t) (v rho psi rcm : Z)
      : option Point.t :=
    option_map
      (fun M =>
        EccSpec.point_add M (OrchardProtocolSpec.mul_note_commit_r rcm))
      (sinsemilla_hash_to_point_bot (OrchardSpec.note_commit_q prm)
        (OrchardSpec.note_commit_message g_d pk_d v rho psi)).

  (** §5.4.8.4 [Commit^ivk_rivk(ak, nk)] ([SinsemillaShortCommit]),
      ⊥-carrying.  Consumed by §4.18.4 'Diversified address integrity'
      ([ivk = ⊥ ∨ pk_d = [ivk] g_d]). *)
  Definition commit_ivk_bot
      (prm : OrchardSpec.Params) (ak nk rivk : Z) : option Z :=
    option_map
      (fun M =>
        EccSpec.extract_x
          (EccSpec.point_add M (OrchardProtocolSpec.mul_commit_ivk_r rivk)))
      (sinsemilla_hash_to_point_bot (OrchardSpec.commit_ivk_q prm)
        (OrchardSpec.commit_ivk_message ak nk)).

  (** §4.18.4 'New note commitment integrity':
      [Extract⊥_P(NoteCommit^Orchard_rcm_new(…)) ∈ {cm_x, ⊥}] — the
      ⊥-carrying new-note commitment x-coordinate, with §5.4.9.7
      [Extract⊥_P(⊥) = ⊥]. *)
  Definition OrchardCmx_bot
      (prm : OrchardSpec.Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) : option Z :=
    option_map EccSpec.extract_x
      (note_commit_bot prm g_d_new pk_d_new v_new rho_new psi_new rcm_new).

  (** ** Shell bridges: on the nondegenerate branch each shell computes
      [Some] of its total counterpart, and definedness of each shell is
      definedness of its fold *)

  Lemma option_map_defined_iff {A B : Type} (f : A -> B) (o : option A) :
    option_map f o <> None <-> o <> None.
  Proof.
    destruct o; cbn; split; intros H Hn; congruence.
  Qed.

  Lemma sinsemilla_hash_bot_some (Q : Point.t) (words : list Z)
      (Hnd : SinsemillaHash.nondegenerate Q words) :
    sinsemilla_hash_bot Q words =
      Some (SinsemillaSpec.sinsemilla_hash Q words).
  Proof.
    unfold sinsemilla_hash_bot.
    rewrite (hash_to_point_bot_some Q words Hnd).
    cbn [option_map].
    unfold SinsemillaSpec.sinsemilla_hash.
    reflexivity.
  Qed.

  Lemma sinsemilla_hash_bot_defined_iff (Q : Point.t) (words : list Z) :
    sinsemilla_hash_bot Q words <> None <->
    SinsemillaHash.nondegenerate Q words.
  Proof.
    unfold sinsemilla_hash_bot.
    exact (iff_trans
      (option_map_defined_iff EccSpec.extract_x
        (sinsemilla_hash_to_point_bot Q words))
      (hash_to_point_bot_iff Q words)).
  Qed.

  (** The gating bridge: the ⊥-carrying note commitment
      agrees with [OrchardProtocolSpec.note_commit] whenever its 109-word
      fold is nondegenerate. *)
  Lemma note_commit_bot_some
      (prm : OrchardSpec.Params) (g_d pk_d : Point.t) (v rho psi rcm : Z)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.note_commit_q prm)
        (OrchardSpec.note_commit_message g_d pk_d v rho psi)) :
    note_commit_bot prm g_d pk_d v rho psi rcm =
      Some (OrchardProtocolSpec.note_commit prm g_d pk_d v rho psi rcm).
  Proof.
    unfold note_commit_bot.
    rewrite (hash_to_point_bot_some _ _ Hnd).
    cbn [option_map].
    unfold OrchardProtocolSpec.note_commit.
    reflexivity.
  Qed.

  Lemma note_commit_bot_defined_iff
      (prm : OrchardSpec.Params) (g_d pk_d : Point.t) (v rho psi rcm : Z) :
    note_commit_bot prm g_d pk_d v rho psi rcm <> None <->
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q prm)
      (OrchardSpec.note_commit_message g_d pk_d v rho psi).
  Proof.
    unfold note_commit_bot.
    exact (iff_trans
      (option_map_defined_iff _ _)
      (hash_to_point_bot_iff _ _)).
  Qed.

  Lemma commit_ivk_bot_some
      (prm : OrchardSpec.Params) (ak nk rivk : Z)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.commit_ivk_q prm)
        (OrchardSpec.commit_ivk_message ak nk)) :
    commit_ivk_bot prm ak nk rivk =
      Some (OrchardProtocolSpec.commit_ivk prm ak nk rivk).
  Proof.
    unfold commit_ivk_bot.
    rewrite (hash_to_point_bot_some _ _ Hnd).
    cbn [option_map].
    unfold OrchardProtocolSpec.commit_ivk.
    reflexivity.
  Qed.

  Lemma commit_ivk_bot_defined_iff
      (prm : OrchardSpec.Params) (ak nk rivk : Z) :
    commit_ivk_bot prm ak nk rivk <> None <->
    SinsemillaHash.nondegenerate
      (OrchardSpec.commit_ivk_q prm)
      (OrchardSpec.commit_ivk_message ak nk).
  Proof.
    unfold commit_ivk_bot.
    exact (iff_trans
      (option_map_defined_iff _ _)
      (hash_to_point_bot_iff _ _)).
  Qed.

  Lemma OrchardCmx_bot_some
      (prm : OrchardSpec.Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z)
      (Hnd : SinsemillaHash.nondegenerate
        (OrchardSpec.note_commit_q prm)
        (OrchardSpec.note_commit_message g_d_new pk_d_new v_new rho_new psi_new)) :
    OrchardCmx_bot prm g_d_new pk_d_new v_new rho_new psi_new rcm_new =
      Some (OrchardProtocolSpec.OrchardCmx prm g_d_new pk_d_new
        v_new rho_new psi_new rcm_new).
  Proof.
    unfold OrchardCmx_bot.
    rewrite (note_commit_bot_some prm g_d_new pk_d_new
      v_new rho_new psi_new rcm_new Hnd).
    cbn [option_map].
    unfold OrchardProtocolSpec.OrchardCmx.
    reflexivity.
  Qed.

  Lemma OrchardCmx_bot_defined_iff
      (prm : OrchardSpec.Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) :
    OrchardCmx_bot prm g_d_new pk_d_new v_new rho_new psi_new rcm_new <> None <->
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q prm)
      (OrchardSpec.note_commit_message g_d_new pk_d_new v_new rho_new psi_new).
  Proof.
    unfold OrchardCmx_bot.
    exact (iff_trans
      (option_map_defined_iff _ _)
      (note_commit_bot_defined_iff prm g_d_new pk_d_new
        v_new rho_new psi_new rcm_new)).
  Qed.

End OrchardProtocolSpecBot.
