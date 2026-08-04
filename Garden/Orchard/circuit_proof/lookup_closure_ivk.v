(** * The CommitIvk short-lookup range facts from operational acceptance

    [CommitIvkHash.commit_ivk_short_lookup_ok]
    ([circuit_proof/ownership/commit_ivk_hash.v]) bounds the three
    range-checked cells of the [Commit^ivk] message decomposition.  Like
    the note-commit families it is underivable from [Holds] alone: the
    halo2 short lookup constrains its cell only where [QRunning] is zero,
    and the relational selector model leaves that selector free at the
    short-range rows.

    The three sites are instances of the shape the circuit's single
    range-check lookup argument is used at everywhere, so the file adds no
    new machinery: it pins the three sites as [ShortSite] records, checks
    them against the reified synthesis facts, the region placement, the
    inverse-constant identity and the pinned event stream, and feeds them
    to [OrchardShortLookupClosure.site_short_bound].

    The premises of [commit_ivk_short_lookup_ok_operational] are those of
    [orchard_operational_sound]: replay success of the serialized Orchard
    circuit and ideal acceptance of the resulting grid. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.lookup_closure.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.circuit_proof.note_commit.words.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardCommitIvkLookupClosure.
  Import OrchardShortLookupClosure.

  (** ** The three CommitIvk short-range sites

      Each region occupies three rows from its placement start: [QLookup]
      at offsets [0] and [1], [QBitshift] at offset [1], and the [A9] cell
      at offset [2] pinned to the inverse of [2 ^ bits]. *)

  Definition site_civk_b0 : ShortSite := {|
    ss_region := CommitIvkHash.cir RegionId.CommitIvk.RangeB0;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 1700;
  |}.

  Definition site_civk_b2 : ShortSite := {|
    ss_region := CommitIvkHash.cir RegionId.CommitIvk.RangeB2;
    ss_bits := 5;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5;
    ss_start := 1703;
  |}.

  Definition site_civk_d0 : ShortSite := {|
    ss_region := CommitIvkHash.cir RegionId.CommitIvk.RangeD0;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 1764;
  |}.

  Definition commit_ivk_sites : list ShortSite := [
    site_civk_b0;
    site_civk_b2;
    site_civk_d0
  ].

  (** ** The certificates

      [site_facts_ok] reads the four synthesis facts of each region,
      [site_start_ok] its placement row, [site_inv_ok] the width bound and
      the field identity [2 ^ 10 * inv = 2 ^ (10 - bits)], and
      [site_qrunning_ok] the absence of a [QRunning] enable at the two
      lookup rows over the whole pinned event stream. *)

  Lemma commit_ivk_facts_cert :
    List.forallb site_facts_ok commit_ivk_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma commit_ivk_start_cert :
    List.forallb site_start_ok commit_ivk_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma commit_ivk_inv_cert :
    List.forallb site_inv_ok commit_ivk_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma commit_ivk_qrunning_cert :
    List.forallb site_qrunning_ok commit_ivk_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** ** The per-site bound

      [orchard_operational_sound] carries replay success and ideal
      acceptance to the relational [circuit_holds] of the realized
      assignment, and
      the generic site derivation supplies the range bound the relational
      model leaves free. *)

  Lemma commit_ivk_site_bound
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (site : ShortSite) (Hin : List.In site commit_ivk_sites) :
    0 <=
      UnOp.from
        (eval_cell (realize Index.indices region_start_of grid)
          (Garden.Halo2.Synthesis.Cell.advice site.(ss_region) Advice.A9 0)) <
      2 ^ site.(ss_bits).
  Proof.
    exact (site_short_bound advice instance_ grid Hreplay
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      commit_ivk_sites commit_ivk_facts_cert commit_ivk_start_cert
      commit_ivk_inv_cert commit_ivk_qrunning_cert site Hin).
  Qed.

  (** ** The CommitIvk family, from operational acceptance *)

  Theorem commit_ivk_short_lookup_ok_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    CommitIvkHash.commit_ivk_short_lookup_ok
      (realize Index.indices region_start_of grid).
  Proof.
    unfold CommitIvkHash.commit_ivk_short_lookup_ok,
      NoteCommitNewWords.short_ok, NoteCommitNewWords.val,
      NoteCommitNewWords.adv.
    split;
      [exact (commit_ivk_site_bound advice instance_ grid Hreplay Hmock
        site_civk_b0
        ltac:(unfold commit_ivk_sites;
          repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (commit_ivk_site_bound advice instance_ grid Hreplay Hmock
        site_civk_b2
        ltac:(unfold commit_ivk_sites;
          repeat (first [left; reflexivity | right]))) |].
    exact (commit_ivk_site_bound advice instance_ grid Hreplay Hmock
      site_civk_d0
      ltac:(unfold commit_ivk_sites;
        repeat (first [left; reflexivity | right]))).
  Qed.
End OrchardCommitIvkLookupClosure.
