(** * The old-note short-lookup range facts from operational acceptance

    The [Which.Old] instance of the closure proved for the new note in
    [circuit_proof/lookup_closure.v].  The eleven short-range sites of
    [OldNoteWords.old_note_short_lookup_ok] have the same three-row shape
    as the [Which.New] ones — [QLookup] at offsets [0] and [1], [QBitshift]
    at offset [1], the [A9] cell at offset [2] pinned to the inverse of
    [2 ^ bits], and [QRunning] enabled nowhere — so the whole derivation is
    an instantiation of [OrchardShortLookupClosure.site_short_bound] at a
    site list carrying the [Which.Old] regions and their placement rows.

    The file adds no machinery: the extraction lemma
    ([short_range_bound]), the ten-bit lookup bound, the bitshift gate, the
    selector-absence transport ([realized_selector_unset]) and the
    membership reflection all come from [lookup_closure.v]; what is new is
    the pinned site data, its four [vm_compute] certificates, and the
    assembly of the eleven conjuncts. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_proof.lookup_closure.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardOldNoteLookupClosure.
  Import OrchardShortLookupClosure.

  (** ** The old-note family sites

      Region, bit width, pinned inverse constant and absolute placement
      row, one entry per conjunct of [old_note_short_lookup_ok]. *)

  Definition site_old_b0 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeB0;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 655;
  |}.

  Definition site_old_b3 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeB3;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 1688;
  |}.

  Definition site_old_d2 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeD2;
    ss_bits := 8;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_8;
    ss_start := 1685;
  |}.

  Definition site_old_e0 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeE0;
    ss_bits := 6;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_6;
    ss_start := 1661;
  |}.

  Definition site_old_e1 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeE1;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 745;
  |}.

  Definition site_old_g1 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeG1;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 718;
  |}.

  Definition site_old_h0 : ShortSite := {|
    ss_region := OldNoteWords.ncr RegionId.NoteCommit.RangeH0;
    ss_bits := 5;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5;
    ss_start := 685;
  |}.

  Definition site_old_gd_k0 : ShortSite := {|
    ss_region :=
      OldNoteWords.nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK0;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 673;
  |}.

  Definition site_old_gd_k2 : ShortSite := {|
    ss_region :=
      OldNoteWords.nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK2;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 634;
  |}.

  Definition site_old_pkd_k0 : ShortSite := {|
    ss_region :=
      OldNoteWords.nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK0;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 631;
  |}.

  Definition site_old_pkd_k2 : ShortSite := {|
    ss_region :=
      OldNoteWords.nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK2;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 628;
  |}.

  Definition old_note_sites : list ShortSite := [
    site_old_b0;
    site_old_b3;
    site_old_d2;
    site_old_e0;
    site_old_e1;
    site_old_g1;
    site_old_h0;
    site_old_gd_k0;
    site_old_gd_k2;
    site_old_pkd_k0;
    site_old_pkd_k2
  ].

  (** ** The certificates

      The four checkers of [lookup_closure.v], at the old-note site list:
      the four synthesis facts per site, the placement row, the inverse
      identity with the width bound, and the absence of [QRunning] enables
      at the two lookup rows over the whole pinned event stream. *)

  Lemma old_note_facts_cert :
    List.forallb site_facts_ok old_note_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma old_note_start_cert :
    List.forallb site_start_ok old_note_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma old_note_inv_cert :
    List.forallb site_inv_ok old_note_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma old_note_qrunning_cert :
    List.forallb site_qrunning_ok old_note_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** ** The family, from operational acceptance

      [orchard_operational_sound] carries replay success and ideal
      acceptance to the relational [circuit_holds] of the realized
      assignment; [site_short_bound] turns the certificates at each site
      into the range bound the relational model leaves free. *)

  Lemma old_note_site_bound
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (site : ShortSite) (Hin : List.In site old_note_sites) :
    0 <=
      UnOp.from
        (eval_cell (realize Index.indices region_start_of grid)
          (Garden.Halo2.Synthesis.Cell.advice site.(ss_region) Advice.A9 0)) <
      2 ^ site.(ss_bits).
  Proof.
    exact (site_short_bound advice instance_ grid Hreplay
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      old_note_sites old_note_facts_cert old_note_start_cert
      old_note_inv_cert old_note_qrunning_cert site Hin).
  Qed.

  Theorem old_note_short_lookup_ok_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    OldNoteWords.old_note_short_lookup_ok
      (realize Index.indices region_start_of grid).
  Proof.
    unfold OldNoteWords.old_note_short_lookup_ok, OldNoteWords.short_ok,
      OldNoteWords.val, OldNoteWords.adv.
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_b0
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_b3
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_d2
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_e0
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_e1
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_g1
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_h0
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_gd_k0
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_gd_k2
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (old_note_site_bound advice instance_ grid Hreplay Hmock
        site_old_pkd_k0
        ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))) |].
    exact (old_note_site_bound advice instance_ grid Hreplay Hmock
      site_old_pkd_k2
      ltac:(unfold old_note_sites; repeat (first [left; reflexivity | right]))).
  Qed.
End OrchardOldNoteLookupClosure.
