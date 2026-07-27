(** * Open witness facts: the [bits]-column group

    The 38 non-self-copy witness facts of the synthesis program whose two
    cell addresses are (a) a [bits]-column cell of a Sinsemilla hash region
    — [A2] under the first configuration variant ([Commit^ivk], the old
    [NoteCommit]), [A7] under the second (the new [NoteCommit]) — and (b) a
    div/mod slice of the packed §5.4.8.4 message held by the
    [tables_nc.v] cell layer (a witnessed message piece, a message-piece
    gate row, or an input-decomposition gate row).

    Neither side reduces to the other: the hash-region cell is
    [List.nth j (bits_column (split_pieces lens (words_le n X))) 0], a fold
    over the 10-bit word list, while the decomposition cell is a raw integer
    div/mod of the packed message [X].  The bridge is one closed form
    ([bits_run]): inside the piece spanning the word range [[j, j+m)], the
    running-sum column reads [(X / 2^(10 j)) mod 2^(10 m)].  The 38 facts are
    then syntactic instances of that closed form against the
    [tables_nc.v] slice constants, up to the two power-of-two slice
    identities [mod_div] and [slice_shift].

    Exports [orchardwitnessbitscolumn_facts] (the group's fact literals,
    copied verbatim from the residue list) and
    [orchardwitnessbitscolumn_ok]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_completeness.forward.arith.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardWitnessBitsColumn.
  Import OrchardWitnessInput.

  Module OCT := OrchardCompletenessTables.
  Module AMS := OrchardAdviceMerkleSinsemilla.
  Module FS := OrchardForwardSinsemilla.
  Module NC := OrchardNoteCommitCells.

  Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** The hoisted derivation record stays a stuck atom: a reduction that
      unfolds [tables_of] on symbolic input normalizes the Sinsemilla,
      ladder and Poseidon folds it carries (docs/compile-performance.md). *)
  #[local] Strategy opaque
    [OrchardCompletenessTables.tables_of
     BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** ** Power-of-two slice arithmetic *)

  (** A [mod] of a power of two, divided down: the low part drops. *)
  Lemma mod_div (X u v s : Z) : 0 <= u -> 0 <= v -> s = u + v ->
    (X mod 2 ^ s) / 2 ^ u = (X / 2 ^ u) mod 2 ^ v.
  Proof.
    intros Hu Hv Hs.
    pose proof (OrchardForwardArith.pow2_pos u Hu) as Hpu.
    pose proof (OrchardForwardArith.pow2_pos v Hv) as Hpv.
    subst s.
    rewrite OrchardForwardArith.pow2_split by lia.
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ u)).
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (X mod 2 ^ u) (2 ^ u))
      by (apply Z.mod_pos_bound; lia).
    lia.
  Qed.

  (** The same, with a leading shift already applied. *)
  Lemma slice_shift (X d s u v a : Z) : 0 <= d -> 0 <= u -> 0 <= v ->
    s = u + v -> a = d + u ->
    ((X / 2 ^ d) mod 2 ^ s) / 2 ^ u = (X / 2 ^ a) mod 2 ^ v.
  Proof.
    intros Hd Hu Hv Hs Ha.
    rewrite (mod_div (X / 2 ^ d) u v s Hu Hv Hs).
    rewrite OrchardForwardArith.div_div_pow by lia.
    rewrite <- Ha.
    reflexivity.
  Qed.

  (** The [j = 0] slice of a piece: a bare [mod]. *)
  Lemma slice_whole (P s : Z) : (P / 2 ^ 0) mod 2 ^ s = P mod 2 ^ s.
  Proof. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. Qed.

  (** One step of the running-sum telescoping, at the integer level. *)
  Lemma slice_cons (Y u v : Z) : 0 <= u -> 0 <= v ->
    Y mod 2 ^ u + 2 ^ u * ((Y / 2 ^ u) mod 2 ^ v) = Y mod 2 ^ (u + v).
  Proof.
    intros Hu Hv.
    pose proof (OrchardForwardArith.pow2_pos u Hu).
    pose proof (OrchardForwardArith.pow2_pos v Hv).
    rewrite OrchardForwardArith.pow2_split by lia.
    rewrite Z.rem_mul_r by lia.
    reflexivity.
  Qed.

  (** ** The 10-bit word list

      [words_le] is the little-endian 10-bit decomposition, so its [j]-th
      entry is the [j]-th 10-bit digit. *)

  Lemma words_le_nth (c : nat) :
    forall (j : nat) (X a : Z),
      (j < c)%nat -> a = 10 * Z.of_nat j ->
      List.nth j (SinsemillaSpec.words_le c X) 0 = (X / 2 ^ a) mod 2 ^ 10.
  Proof.
    induction c as [| c IH]; intros j X a Hj Ha; [lia |].
    destruct j as [| j].
    - cbn [SinsemillaSpec.words_le List.nth].
      unfold SinsemillaSpec.sinsemilla_k.
      subst a. cbn [Z.of_nat Z.mul].
      rewrite Z.pow_0_r, Z.div_1_r.
      reflexivity.
    - cbn [SinsemillaSpec.words_le List.nth].
      unfold SinsemillaSpec.sinsemilla_k.
      rewrite (IH j (X / 2 ^ 10) (10 * Z.of_nat j)) by lia.
      rewrite OrchardForwardArith.div_div_pow by lia.
      rewrite Ha, Nat2Z.inj_succ.
      replace (10 + 10 * Z.of_nat j) with (10 * Z.succ (Z.of_nat j)) by lia.
      reflexivity.
  Qed.

  (** ** The [bits] column telescopes inside a piece

      [suffix_digit_sums] is the per-piece running sum and [bits_column]
      concatenates the per-piece columns, so the column steps by one 10-bit
      word except at a piece boundary, where it restarts. *)

  Lemma sds_step (l : list Z) :
    forall i : nat,
      (i < List.length l)%nat ->
      List.nth i (AMS.suffix_digit_sums l) 0 =
        List.nth i l 0 + 2 ^ 10 * List.nth (S i) (AMS.suffix_digit_sums l) 0.
  Proof.
    induction l as [| x l IH]; intros i Hi; cbn [List.length] in Hi; [lia |].
    destruct i as [| i].
    - cbn [AMS.suffix_digit_sums List.nth].
      destruct (AMS.suffix_digit_sums l) as [| y r]; reflexivity.
    - cbn [AMS.suffix_digit_sums List.nth].
      apply IH. lia.
  Qed.

  (** The last index of a piece, computed from the piece-length layout. *)
  Fixpoint bnd_lens (lens : list nat) (j : nat) : bool :=
    match lens with
    | [] => false
    | a :: lens' =>
        if (S j =? a)%nat then true
        else if (j <? a)%nat then false
        else bnd_lens lens' (j - a)
    end.

  Lemma nth_firstn_lt {A : Type} (d : A) (n : nat) (l : list A) :
    forall i : nat,
      (i < n)%nat -> List.nth i (List.firstn n l) d = List.nth i l d.
  Proof.
    revert l; induction n as [| n IH]; intros l i Hi; [lia |].
    destruct l as [| x l]; cbn [List.firstn].
    - destruct i; reflexivity.
    - destruct i as [| i]; cbn [List.nth]; [reflexivity |].
      apply IH. lia.
  Qed.

  Lemma split_cons (a : nat) (lens : list nat) (l : list Z) :
    AMS.split_pieces (a :: lens) l =
      List.firstn a l :: AMS.split_pieces lens (List.skipn a l).
  Proof. reflexivity. Qed.

  Lemma bits_cons (p : list Z) (ps : list (list Z)) :
    AMS.bits_column (p :: ps) = AMS.suffix_digit_sums p ++ AMS.bits_column ps.
  Proof. reflexivity. Qed.

  Lemma bits_step (lens : list nat) :
    forall (l : list Z) (j : nat),
      FS.lens_sum lens = List.length l ->
      (j < List.length l)%nat ->
      List.nth j (AMS.bits_column (AMS.split_pieces lens l)) 0 =
        List.nth j l 0 +
        (if bnd_lens lens j
         then 0
         else 2 ^ 10 *
           List.nth (S j) (AMS.bits_column (AMS.split_pieces lens l)) 0).
  Proof.
    induction lens as [| a lens IH]; intros l j Hlen Hj;
      cbn [FS.lens_sum] in Hlen.
    - cbn [List.length] in Hj. lia.
    - rewrite split_cons, bits_cons.
      assert (Ha : (a <= List.length l)%nat) by lia.
      assert (Hp : List.length (AMS.suffix_digit_sums (List.firstn a l)) = a).
      { rewrite AMS.suffix_digit_sums_length, List.length_firstn. lia. }
      cbn [bnd_lens].
      destruct (Nat.lt_ge_cases j a) as [Hlt | Hge].
      + rewrite List.app_nth1 by lia.
        rewrite sds_step
          by (rewrite List.length_firstn; lia).
        rewrite nth_firstn_lt by lia.
        destruct (Nat.eq_dec (S j) a) as [Heq | Hne].
        * rewrite (proj2 (Nat.eqb_eq (S j) a) Heq).
          assert (Hz : List.nth (S j)
            (AMS.suffix_digit_sums (List.firstn a l)) 0 = 0)
            by (apply List.nth_overflow; lia).
          rewrite Hz.
          lazy beta iota.
          lia.
        * rewrite (proj2 (Nat.eqb_neq (S j) a) Hne).
          rewrite (proj2 (Nat.ltb_lt j a) Hlt).
          lazy beta iota.
          rewrite List.app_nth1 by lia.
          reflexivity.
      + rewrite (proj2 (Nat.eqb_neq (S j) a)) by lia.
        rewrite (proj2 (Nat.ltb_ge j a) Hge).
        lazy beta iota.
        rewrite List.app_nth2 by lia.
        rewrite Hp.
        rewrite (IH (List.skipn a l) (j - a)%nat)
          by (rewrite List.length_skipn; lia).
        rewrite List.nth_skipn.
        replace (a + (j - a))%nat with j by lia.
        destruct (bnd_lens lens (j - a)%nat).
        * reflexivity.
        * rewrite List.app_nth2 by lia.
          rewrite Hp.
          replace (S j - a)%nat with (S (j - a))%nat by lia.
          reflexivity.
  Qed.

  (** ** The closed form of a [bits] cell

      Index [j] lies inside a piece ending at [j + m] (no piece boundary
      strictly before it), so the running sum telescopes over exactly the
      [m] words [j .. j+m-1]: the cell is the [10 m]-bit slice of the packed
      message starting at bit [10 j]. *)

  Definition run_ok (lens : list nat) (n j m : nat) : bool :=
    Nat.ltb 0 m && Nat.leb (j + m) n &&
    List.forallb (fun i => negb (bnd_lens lens i)) (List.seq j (m - 1)) &&
    bnd_lens lens (j + m - 1).

  Lemma run_ok_inv (lens : list nat) (n j m : nat) :
    run_ok lens n j m = true ->
    (0 < m)%nat /\ (j + m <= n)%nat /\
    List.forallb (fun i => negb (bnd_lens lens i)) (List.seq j (m - 1)) = true /\
    bnd_lens lens (j + m - 1)%nat = true.
  Proof.
    unfold run_ok. intros H.
    apply andb_true_iff in H as [H H4].
    apply andb_true_iff in H as [H H3].
    apply andb_true_iff in H as [H1 H2].
    apply Nat.ltb_lt in H1. apply Nat.leb_le in H2.
    repeat split; assumption.
  Qed.

  Lemma bits_run_aux (lens : list nat) (n : nat) (X : Z)
      (Hlens : FS.lens_sum lens = n) :
    forall (m j : nat) (a b : Z),
      (0 < m)%nat -> (j + m <= n)%nat ->
      List.forallb (fun i => negb (bnd_lens lens i))
        (List.seq j (m - 1)) = true ->
      bnd_lens lens (j + m - 1)%nat = true ->
      a = 10 * Z.of_nat j -> b = 10 * Z.of_nat m ->
      List.nth j (AMS.bits_column (AMS.split_pieces lens
        (SinsemillaSpec.words_le n X))) 0 = (X / 2 ^ a) mod 2 ^ b.
  Proof.
    assert (Hlw : FS.lens_sum lens =
      List.length (SinsemillaSpec.words_le n X))
      by (rewrite FS.words_le_length; exact Hlens).
    induction m as [| m IH]; intros j a b Hm Hjm Hf He Ha Hb; [lia |].
    assert (Hjn : (j < List.length (SinsemillaSpec.words_le n X))%nat)
      by (rewrite FS.words_le_length; lia).
    rewrite (bits_step lens _ j Hlw Hjn).
    assert (Hidx : (j + S m - 1)%nat = (j + m)%nat) by lia.
    rewrite Hidx in He.
    destruct m as [| m].
    - (* the last word of the piece: the column stops here *)
      rewrite Nat.add_0_r in He.
      rewrite He.
      rewrite (words_le_nth n j X a ltac:(lia) Ha).
      subst b.
      replace (10 * Z.of_nat 1%nat) with 10 by reflexivity.
      lia.
    - (* an interior word: one telescoping step *)
      assert (Hnb : bnd_lens lens j = false).
      { replace (S (S m) - 1)%nat with (S m) in Hf by lia.
        cbn [List.seq List.forallb] in Hf.
        apply andb_true_iff in Hf as [Hf1 _].
        destruct (bnd_lens lens j); [discriminate | reflexivity]. }
      rewrite Hnb.
      rewrite (words_le_nth n j X a ltac:(lia) Ha).
      rewrite (IH (S j) (a + 10) (b - 10)).
      + rewrite <- (OrchardForwardArith.div_div_pow X a 10) by lia.
        rewrite slice_cons by lia.
        replace (10 + (b - 10)) with b by lia.
        lia.
      + lia.
      + lia.
      + replace (S m - 1)%nat with m by lia.
        replace (S (S m) - 1)%nat with (S m) in Hf by lia.
        cbn [List.seq List.forallb] in Hf.
        apply andb_true_iff in Hf as [_ Hf2].
        exact Hf2.
      + replace (S j + S m - 1)%nat with (j + S m)%nat by lia.
        exact He.
      + rewrite Ha, Nat2Z.inj_succ. lia.
      + rewrite Hb, !Nat2Z.inj_succ. lia.
  Qed.

  Lemma bits_run (lens : list nat) (n : nat) (X : Z)
      (Hlens : FS.lens_sum lens = n) (m j : nat) (a b : Z)
      (Hok : run_ok lens n j m = true)
      (Ha : a = 10 * Z.of_nat j) (Hb : b = 10 * Z.of_nat m) :
    List.nth j (AMS.bits_column (AMS.split_pieces lens
      (SinsemillaSpec.words_le n X))) 0 = (X / 2 ^ a) mod 2 ^ b.
  Proof.
    destruct (run_ok_inv lens n j m Hok) as [H1 [H2 [H3 H4] ] ].
    exact (bits_run_aux lens n X Hlens m j a b H1 H2 H3 H4 Ha Hb).
  Qed.

  (** ** The hash region's [bits] cell *)

  Definition bits_col (second : bool) : Advice.t :=
    if second then Advice.A7 else Advice.A2.

  Lemma hd_bits_of (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_bits (OCT.hash_data_of Q pieces) = AMS.bits_column pieces.
  Proof.
    unfold OCT.hash_data_of.
    destruct (OCT.hash_go Q (Stdlib.Lists.List.concat pieces)) as [rows out].
    reflexivity.
  Qed.

  Lemma logical_bits (second : bool) :
    AMS.logical_col second (bits_col second) = Some 2%nat.
  Proof. destruct second; reflexivity. Qed.

  Lemma hash_cell_bits (Q : Point.t) (pieces : list (list Z)) (second : bool)
      (j : nat) :
    OCT.hash_region_advice_t (OCT.hash_data_of Q pieces) second
      (bits_col second) (Z.of_nat j) = List.nth j (AMS.bits_column pieces) 0.
  Proof.
    unfold OCT.hash_region_advice_t.
    rewrite logical_bits, hd_bits_of.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
    rewrite Nat2Z.id.
    reflexivity.
  Qed.

  (** ** The three packed messages *)

  Definition civk_pk (w : HonestInput) : Z :=
    NC.civk_packed (EccSpec.extract_x (hi_ak w)) (hi_nk w).

  Definition nco_pk (w : HonestInput) : Z :=
    NC.nc_packed (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w)
      (hi_rho_old w) (hi_psi_old w).

  Definition ncn_pk (w : HonestInput) : Z :=
    NC.nc_packed (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (rho_new w) (hi_psi_new w).

  (** The new note's [ρ] is the old note's nullifier, which the hoisted
      record carries as [t_nf_spec]. *)
  Lemma ncn_pk_read (w : HonestInput) :
    NC.nc_packed (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w) = ncn_pk w.
  Proof.
    unfold ncn_pk, rho_new.
    rewrite FS.t_nf_spec_of.
    reflexivity.
  Qed.

  Lemma civk_msg (w : HonestInput) :
    commit_ivk_words w = SinsemillaSpec.words_le 51 (civk_pk w).
  Proof. reflexivity. Qed.

  Lemma nco_msg (w : HonestInput) :
    note_commit_old_words w = SinsemillaSpec.words_le 109 (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma ncn_msg (w : HonestInput) :
    note_commit_new_words w = SinsemillaSpec.words_le 109 (ncn_pk w).
  Proof. reflexivity. Qed.

  (** ** The three hash regions' [bits] cells, in closed form *)

  Lemma civk_cell (w : HonestInput) (j m : nat) (r a b : Z)
      (Hr : r = Z.of_nat j) (Ha : a = 10 * Z.of_nat j)
      (Hb : b = 10 * Z.of_nat m)
      (Hok : run_ok AMS.commit_ivk_lens 51 j m = true) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) r =
    (civk_pk w / 2 ^ a) mod 2 ^ b.
  Proof.
    subst r.
    change (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint)
      with FS.civk_h2p.
    rewrite FS.civk_hash_adv.
    change Advice.A2 with (bits_col false).
    rewrite hash_cell_bits.
    rewrite civk_msg.
    exact (bits_run AMS.commit_ivk_lens 51%nat (civk_pk w) eq_refl m j a b
      Hok Ha Hb).
  Qed.

  Lemma nco_cell (w : HonestInput) (j m : nat) (r a b : Z)
      (Hr : r = Z.of_nat j) (Ha : a = 10 * Z.of_nat j)
      (Hb : b = 10 * Z.of_nat m)
      (Hok : run_ok AMS.note_commit_lens 109 j m = true) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) r =
    (nco_pk w / 2 ^ a) mod 2 ^ b.
  Proof.
    subst r.
    change (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.HashToPoint)
      with (FS.nc_h2p RegionId.NoteCommit.Which.Old).
    rewrite FS.nc_old_hash_adv.
    change Advice.A2 with (bits_col false).
    rewrite hash_cell_bits.
    rewrite nco_msg.
    exact (bits_run AMS.note_commit_lens 109%nat (nco_pk w) eq_refl m j a b
      Hok Ha Hb).
  Qed.

  Lemma ncn_cell (w : HonestInput) (j m : nat) (r a b : Z)
      (Hr : r = Z.of_nat j) (Ha : a = 10 * Z.of_nat j)
      (Hb : b = 10 * Z.of_nat m)
      (Hok : run_ok AMS.note_commit_lens 109 j m = true) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint) r =
    (ncn_pk w / 2 ^ a) mod 2 ^ b.
  Proof.
    subst r.
    change (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.HashToPoint)
      with (FS.nc_h2p RegionId.NoteCommit.Which.New).
    rewrite FS.nc_new_hash_adv.
    change Advice.A7 with (bits_col true).
    rewrite hash_cell_bits.
    rewrite ncn_msg.
    exact (bits_run AMS.note_commit_lens 109%nat (ncn_pk w) eq_refl m j a b
      Hok Ha Hb).
  Qed.

  (** ** The decomposition cells

      Each is a definitional reading of the advice dispatch at one address:
      the region routing is on a concrete constructor, and the
      [tables_nc.v] leaf is a pure div/mod slice. *)

  Notation civkr r := (RegionId.CommitIvk r).
  Notation ncor r := (RegionId.NoteCommit RegionId.NoteCommit.Which.Old r).
  Notation ncnr r := (RegionId.NoteCommit RegionId.NoteCommit.Which.New r).

  Lemma r_civk_wa (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessA) 0 = NC.civk_a (civk_pk w).
  Proof. reflexivity. Qed.

  Lemma r_civk_wb (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessB) 0 = NC.civk_b (civk_pk w).
  Proof. reflexivity. Qed.

  Lemma r_civk_wc (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessC) 0 = NC.civk_c (civk_pk w).
  Proof. reflexivity. Qed.

  Lemma r_civk_wd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessD) 0 = NC.civk_d (civk_pk w).
  Proof. reflexivity. Qed.

  Lemma r_civk_can0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.CanonicityGate) 0 =
    NC.civk_a (civk_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_civk_can1 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.CanonicityGate) 1 =
    NC.civk_c (civk_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_nco_wa (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessA) 0 = NC.nc_a (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wb (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessB) 0 = NC.nc_b (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wc (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessC) 0 = NC.nc_c (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessD) 0 = NC.nc_d (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_we (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessE) 0 = NC.nc_e (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wf (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessF) 0 = NC.nc_f (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wg (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessG) 0 = NC.nc_g (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_wh (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessH) 0 = NC.nc_h (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_mpd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.MessagePieceD) 1 = NC.nc_d3 (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_mpg (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncor RegionId.NoteCommit.MessagePieceG) 1 = NC.nc_g2 (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_igd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputGD) 0 = NC.nc_a (nco_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_nco_ipkd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputPkD) 0 = NC.nc_c (nco_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_nco_ival (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.InputValue) 0 = NC.nc_d3 (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_irho (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputRho) 0 = NC.nc_f (nco_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_nco_ipsi8 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.InputPsi) 0 = NC.nc_g2 (nco_pk w).
  Proof. reflexivity. Qed.

  Lemma r_nco_ipsi9 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputPsi) 0 = NC.nc_g (nco_pk w) / 2 ^ 130.
  Proof. reflexivity. Qed.

  Lemma r_ncn_wa (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessA) 0 = NC.nc_a (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wb (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessB) 0 = NC.nc_b (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wc (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessC) 0 = NC.nc_c (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessD) 0 = NC.nc_d (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_we (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessE) 0 = NC.nc_e (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wf (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessF) 0 = NC.nc_f (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wg (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessG) 0 = NC.nc_g (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_wh (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessH) 0 = NC.nc_h (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_mpd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.MessagePieceD) 1 = NC.nc_d3 (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_mpg (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.MessagePieceG) 1 = NC.nc_g2 (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_igd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputGD) 0 = NC.nc_a (ncn_pk w) / 2 ^ 130.
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_ipkd (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputPkD) 0 = NC.nc_c (ncn_pk w) / 2 ^ 130.
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_ival (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.InputValue) 0 = NC.nc_d3 (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_irho (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputRho) 0 = NC.nc_f (ncn_pk w) / 2 ^ 130.
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_ipsi8 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.InputPsi) 0 = NC.nc_g2 (ncn_pk w).
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  Lemma r_ncn_ipsi9 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputPsi) 0 = NC.nc_g (ncn_pk w) / 2 ^ 130.
  Proof. rewrite <- ncn_pk_read. reflexivity. Qed.

  (** ** The slice identities

      Each [tables_nc.v] constant, rewritten as the closed form of the
      corresponding [bits] cell. *)

  Lemma s_civk_a (P : Z) : NC.civk_a P = (P / 2 ^ 0) mod 2 ^ 250.
  Proof. unfold NC.civk_a. rewrite slice_whole. reflexivity. Qed.

  Lemma s_civk_b (P : Z) : NC.civk_b P = (P / 2 ^ 250) mod 2 ^ 10.
  Proof. reflexivity. Qed.

  Lemma s_civk_c (P : Z) : NC.civk_c P = (P / 2 ^ 260) mod 2 ^ 240.
  Proof. reflexivity. Qed.

  Lemma s_civk_d (P : Z) : NC.civk_d P = (P / 2 ^ 500) mod 2 ^ 10.
  Proof. reflexivity. Qed.

  Lemma s_civk_a130 (P : Z) :
    NC.civk_a P / 2 ^ 130 = (P / 2 ^ 130) mod 2 ^ 120.
  Proof. unfold NC.civk_a. apply (mod_div P 130 120 250); lia. Qed.

  Lemma s_civk_c130 (P : Z) :
    NC.civk_c P / 2 ^ 130 = (P / 2 ^ 390) mod 2 ^ 110.
  Proof. unfold NC.civk_c. apply (slice_shift P 260 240 130 110 390); lia. Qed.

  Lemma s_nc_a (P : Z) : NC.nc_a P = (P / 2 ^ 0) mod 2 ^ 250.
  Proof. unfold NC.nc_a. rewrite slice_whole. reflexivity. Qed.

  Lemma s_nc_b (P : Z) : NC.nc_b P = (P / 2 ^ 250) mod 2 ^ 10.
  Proof. reflexivity. Qed.

  Lemma s_nc_c (P : Z) : NC.nc_c P = (P / 2 ^ 260) mod 2 ^ 250.
  Proof. reflexivity. Qed.

  Lemma s_nc_d (P : Z) : NC.nc_d P = (P / 2 ^ 510) mod 2 ^ 60.
  Proof. reflexivity. Qed.

  Lemma s_nc_e (P : Z) : NC.nc_e P = (P / 2 ^ 570) mod 2 ^ 10.
  Proof. reflexivity. Qed.

  Lemma s_nc_f (P : Z) : NC.nc_f P = (P / 2 ^ 580) mod 2 ^ 250.
  Proof. reflexivity. Qed.

  Lemma s_nc_g (P : Z) : NC.nc_g P = (P / 2 ^ 830) mod 2 ^ 250.
  Proof. reflexivity. Qed.

  Lemma s_nc_h (P : Z) : NC.nc_h P = (P / 2 ^ 1080) mod 2 ^ 10.
  Proof. reflexivity. Qed.

  Lemma s_nc_d3 (P : Z) : NC.nc_d3 P = (P / 2 ^ 520) mod 2 ^ 50.
  Proof.
    unfold NC.nc_d3, NC.nc_d.
    apply (slice_shift P 510 60 10 50 520); lia.
  Qed.

  Lemma s_nc_g2 (P : Z) : NC.nc_g2 P = (P / 2 ^ 840) mod 2 ^ 240.
  Proof.
    unfold NC.nc_g2, NC.nc_g.
    apply (slice_shift P 830 250 10 240 840); lia.
  Qed.

  Lemma s_nc_a130 (P : Z) : NC.nc_a P / 2 ^ 130 = (P / 2 ^ 130) mod 2 ^ 120.
  Proof. unfold NC.nc_a. apply (mod_div P 130 120 250); lia. Qed.

  Lemma s_nc_c130 (P : Z) : NC.nc_c P / 2 ^ 130 = (P / 2 ^ 390) mod 2 ^ 120.
  Proof. unfold NC.nc_c. apply (slice_shift P 260 250 130 120 390); lia. Qed.

  Lemma s_nc_f130 (P : Z) : NC.nc_f P / 2 ^ 130 = (P / 2 ^ 710) mod 2 ^ 120.
  Proof. unfold NC.nc_f. apply (slice_shift P 580 250 130 120 710); lia. Qed.

  Lemma s_nc_g130 (P : Z) : NC.nc_g P / 2 ^ 130 = (P / 2 ^ 960) mod 2 ^ 120.
  Proof. unfold NC.nc_g. apply (slice_shift P 830 250 130 120 960); lia. Qed.

  (** ** The 38 facts *)

  Lemma f14 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 0 =
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessA) 0.
  Proof.
    rewrite (civk_cell w 0%nat 25%nat 0 0 250 eq_refl eq_refl eq_refl eq_refl).
    rewrite r_civk_wa, s_civk_a. reflexivity.
  Qed.

  Lemma f15 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 25 =
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessB) 0.
  Proof.
    rewrite (civk_cell w 25%nat 1%nat 25 250 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_civk_wb, s_civk_b. reflexivity.
  Qed.

  Lemma f16 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 26 =
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessC) 0.
  Proof.
    rewrite (civk_cell w 26%nat 24%nat 26 260 240 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_civk_wc, s_civk_c. reflexivity.
  Qed.

  Lemma f17 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 50 =
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.WitnessD) 0.
  Proof.
    rewrite (civk_cell w 50%nat 1%nat 50 500 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_civk_wd, s_civk_d. reflexivity.
  Qed.

  Lemma f20 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.CanonicityGate) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 13.
  Proof.
    rewrite (civk_cell w 13%nat 12%nat 13 130 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_civk_can0, s_civk_a130. reflexivity.
  Qed.

  Lemma f22 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (civkr RegionId.CommitIvk.CanonicityGate) 1 =
    (Γw w).(Assignment.advice) Advice.A2
      (civkr RegionId.CommitIvk.HashToPoint) 39.
  Proof.
    rewrite (civk_cell w 39%nat 11%nat 39 390 110 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_civk_can1, s_civk_c130. reflexivity.
  Qed.

  Lemma f37 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 0 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessA) 0.
  Proof.
    rewrite (nco_cell w 0%nat 25%nat 0 0 250 eq_refl eq_refl eq_refl eq_refl).
    rewrite r_nco_wa, s_nc_a. reflexivity.
  Qed.

  Lemma f38 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 25 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessB) 0.
  Proof.
    rewrite (nco_cell w 25%nat 1%nat 25 250 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wb, s_nc_b. reflexivity.
  Qed.

  Lemma f39 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 26 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessC) 0.
  Proof.
    rewrite (nco_cell w 26%nat 25%nat 26 260 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wc, s_nc_c. reflexivity.
  Qed.

  Lemma f40 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 51 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessD) 0.
  Proof.
    rewrite (nco_cell w 51%nat 6%nat 51 510 60 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wd, s_nc_d. reflexivity.
  Qed.

  Lemma f41 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 57 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessE) 0.
  Proof.
    rewrite (nco_cell w 57%nat 1%nat 57 570 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_we, s_nc_e. reflexivity.
  Qed.

  Lemma f42 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 58 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessF) 0.
  Proof.
    rewrite (nco_cell w 58%nat 25%nat 58 580 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wf, s_nc_f. reflexivity.
  Qed.

  Lemma f43 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 83 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessG) 0.
  Proof.
    rewrite (nco_cell w 83%nat 25%nat 83 830 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wg, s_nc_g. reflexivity.
  Qed.

  Lemma f44 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 108 =
    (Γw w).(Assignment.advice) Advice.A6
      (ncor RegionId.NoteCommit.WitnessH) 0.
  Proof.
    rewrite (nco_cell w 108%nat 1%nat 108 1080 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_wh, s_nc_h. reflexivity.
  Qed.

  Lemma f49 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.MessagePieceD) 1 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 52.
  Proof.
    rewrite (nco_cell w 52%nat 5%nat 52 520 50 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_mpd, s_nc_d3. reflexivity.
  Qed.

  Lemma f50 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncor RegionId.NoteCommit.MessagePieceG) 1 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 84.
  Proof.
    rewrite (nco_cell w 84%nat 24%nat 84 840 240 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_mpg, s_nc_g2. reflexivity.
  Qed.

  Lemma f52 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputGD) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 13.
  Proof.
    rewrite (nco_cell w 13%nat 12%nat 13 130 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_igd, s_nc_a130. reflexivity.
  Qed.

  Lemma f55 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputPkD) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 39.
  Proof.
    rewrite (nco_cell w 39%nat 12%nat 39 390 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_ipkd, s_nc_c130. reflexivity.
  Qed.

  Lemma f56 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.InputValue) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 52.
  Proof.
    rewrite (nco_cell w 52%nat 5%nat 52 520 50 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_ival, s_nc_d3. reflexivity.
  Qed.

  Lemma f58 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputRho) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 71.
  Proof.
    rewrite (nco_cell w 71%nat 12%nat 71 710 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_irho, s_nc_f130. reflexivity.
  Qed.

  Lemma f59 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncor RegionId.NoteCommit.InputPsi) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 84.
  Proof.
    rewrite (nco_cell w 84%nat 24%nat 84 840 240 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_ipsi8, s_nc_g2. reflexivity.
  Qed.

  Lemma f61 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncor RegionId.NoteCommit.InputPsi) 0 =
    (Γw w).(Assignment.advice) Advice.A2
      (ncor RegionId.NoteCommit.HashToPoint) 96.
  Proof.
    rewrite (nco_cell w 96%nat 12%nat 96 960 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_nco_ipsi9, s_nc_g130. reflexivity.
  Qed.

  Lemma f70 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessA) 0.
  Proof.
    rewrite (ncn_cell w 0%nat 25%nat 0 0 250 eq_refl eq_refl eq_refl eq_refl).
    rewrite r_ncn_wa, s_nc_a. reflexivity.
  Qed.

  Lemma f71 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 25 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessB) 0.
  Proof.
    rewrite (ncn_cell w 25%nat 1%nat 25 250 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wb, s_nc_b. reflexivity.
  Qed.

  Lemma f72 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 26 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessC) 0.
  Proof.
    rewrite (ncn_cell w 26%nat 25%nat 26 260 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wc, s_nc_c. reflexivity.
  Qed.

  Lemma f73 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 51 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessD) 0.
  Proof.
    rewrite (ncn_cell w 51%nat 6%nat 51 510 60 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wd, s_nc_d. reflexivity.
  Qed.

  Lemma f74 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 57 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessE) 0.
  Proof.
    rewrite (ncn_cell w 57%nat 1%nat 57 570 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_we, s_nc_e. reflexivity.
  Qed.

  Lemma f75 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 58 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessF) 0.
  Proof.
    rewrite (ncn_cell w 58%nat 25%nat 58 580 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wf, s_nc_f. reflexivity.
  Qed.

  Lemma f76 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 83 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessG) 0.
  Proof.
    rewrite (ncn_cell w 83%nat 25%nat 83 830 250 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wg, s_nc_g. reflexivity.
  Qed.

  Lemma f77 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 108 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.WitnessH) 0.
  Proof.
    rewrite (ncn_cell w 108%nat 1%nat 108 1080 10 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_wh, s_nc_h. reflexivity.
  Qed.

  Lemma f82 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.MessagePieceD) 1 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 52.
  Proof.
    rewrite (ncn_cell w 52%nat 5%nat 52 520 50 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_mpd, s_nc_d3. reflexivity.
  Qed.

  Lemma f83 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.MessagePieceG) 1 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 84.
  Proof.
    rewrite (ncn_cell w 84%nat 24%nat 84 840 240 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_mpg, s_nc_g2. reflexivity.
  Qed.

  Lemma f85 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputGD) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 13.
  Proof.
    rewrite (ncn_cell w 13%nat 12%nat 13 130 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_igd, s_nc_a130. reflexivity.
  Qed.

  Lemma f87 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputPkD) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 39.
  Proof.
    rewrite (ncn_cell w 39%nat 12%nat 39 390 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_ipkd, s_nc_c130. reflexivity.
  Qed.

  Lemma f88 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.InputValue) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 52.
  Proof.
    rewrite (ncn_cell w 52%nat 5%nat 52 520 50 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_ival, s_nc_d3. reflexivity.
  Qed.

  Lemma f91 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputRho) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 71.
  Proof.
    rewrite (ncn_cell w 71%nat 12%nat 71 710 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_irho, s_nc_f130. reflexivity.
  Qed.

  Lemma f92 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A8
      (ncnr RegionId.NoteCommit.InputPsi) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 84.
  Proof.
    rewrite (ncn_cell w 84%nat 24%nat 84 840 240 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_ipsi8, s_nc_g2. reflexivity.
  Qed.

  Lemma f94 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (ncnr RegionId.NoteCommit.InputPsi) 0 =
    (Γw w).(Assignment.advice) Advice.A7
      (ncnr RegionId.NoteCommit.HashToPoint) 96.
  Proof.
    rewrite (ncn_cell w 96%nat 12%nat 96 960 120 eq_refl eq_refl eq_refl
      eq_refl).
    rewrite r_ncn_ipsi9, s_nc_g130. reflexivity.
  Qed.

  (** ** The group's fact list *)

  Definition orchardwitnessbitscolumn_facts : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 26 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 50 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 39 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 26 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 51 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 57 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessE; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 58 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessF; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 83 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 108 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 39 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 71 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 96 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 26 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 51 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 57 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessE; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 58 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessF; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 83 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 108 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 39 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 71 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 96 |}].

  (** The head of a witness-fact goal: the two cell addresses, with the
      advice dispatch left folded. *)
  Ltac wf_head :=
    cbn [interpret_fact eval_cell Cell.column Cell.region Cell.row_offset].

  Lemma orchardwitnessbitscolumn_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w)
    : interpret_facts (OrchardHonestAssignment.honest_assignment w)
        orchardwitnessbitscolumn_facts.
  Proof.
    unfold orchardwitnessbitscolumn_facts.
    cbn [interpret_facts].
    repeat apply conj;
      [ wf_head; exact (f14 w)
      | wf_head; exact (f15 w)
      | wf_head; exact (f16 w)
      | wf_head; exact (f17 w)
      | wf_head; exact (f20 w)
      | wf_head; exact (f22 w)
      | wf_head; exact (f37 w)
      | wf_head; exact (f38 w)
      | wf_head; exact (f39 w)
      | wf_head; exact (f40 w)
      | wf_head; exact (f41 w)
      | wf_head; exact (f42 w)
      | wf_head; exact (f43 w)
      | wf_head; exact (f44 w)
      | wf_head; exact (f49 w)
      | wf_head; exact (f50 w)
      | wf_head; exact (f52 w)
      | wf_head; exact (f55 w)
      | wf_head; exact (f56 w)
      | wf_head; exact (f58 w)
      | wf_head; exact (f59 w)
      | wf_head; exact (f61 w)
      | wf_head; exact (f70 w)
      | wf_head; exact (f71 w)
      | wf_head; exact (f72 w)
      | wf_head; exact (f73 w)
      | wf_head; exact (f74 w)
      | wf_head; exact (f75 w)
      | wf_head; exact (f76 w)
      | wf_head; exact (f77 w)
      | wf_head; exact (f82 w)
      | wf_head; exact (f83 w)
      | wf_head; exact (f85 w)
      | wf_head; exact (f87 w)
      | wf_head; exact (f88 w)
      | wf_head; exact (f91 w)
      | wf_head; exact (f92 w)
      | wf_head; exact (f94 w)
      | exact I ].
  Qed.

End OrchardWitnessBitsColumn.
