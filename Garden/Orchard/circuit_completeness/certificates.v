(** * Orchard-instance completeness certificates

    The three Boolean checks that [Garden.Halo2.complete]'s
    [circuit_holds_intro] consumes, instantiated for the whole Orchard action
    circuit and closed by [vm_compute]:

    - [selector_guarded_certificate]: every gate constraint of the configured
      constraint system has [Constraint.Select] as its top constructor, so gate
      satisfaction is vacuous off the enabled selector points;
    - [no_conflicting_writes_certificate]: every fixed-cell write of the
      synthesis program agrees with the first write to the same cell, and each
      loaded lookup column resolves to a single table content — so the honest
      fixed and lookup planes are well defined;
    - [lookup_defaults_certificate]: each of the three configured lookup
      arguments (the two Sinsemilla generator-table lookups and the range-check
      lookup) collapses, when all its selectors are [0], to table row [0].

    Together with [layouter_table_rows_eq] ([nb_table_rows = 1024]) and the
    [enabled_points_sound] well-formedness lemma, these are the finite,
    program-level facts the honest-witness generator phase applies through
    [Complete.circuit_holds_intro] with the same [OrchardDecidableEq]
    equalities. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Garden.Orchard.circuit.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompletenessCertificates.
  (** The configured Orchard constraint system and the reified facts of the
      Orchard synthesis program, at the concrete Pallas prime. *)
  Definition system : ConstraintSystem.t columns :=
    𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty.

  Definition facts : list (Fact.t columns RegionId.t) :=
    layouter_facts Garden.Orchard.circuit.synthesize.

  (** The three Boolean equalities used to instantiate the completeness
      section for Orchard: the fixed, lookup and region column enumerations. *)
  Definition fixed_eqb := OrchardDecidableEq.fixed_eqb.
  Definition lookup_eqb := OrchardDecidableEq.lookup_eqb.
  Definition region_eqb := OrchardDecidableEq.region_id_eqb.

  (** ** Certificate 1: every gate constraint is selector-guarded.

      Small check over the configured constraint system alone. *)
  Lemma selector_guarded_certificate :
    Complete.selector_guarded system = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Certificate 2: no conflicting fixed or table writes.

      The heavy check: it materializes [layouter_facts] of the whole synthesis
      program and scans the fixed writes for value agreement (quadratic in the
      write count) and each loaded lookup column for a single content. *)
  Lemma no_conflicting_writes_certificate :
    Complete.no_conflicting_writes fixed_eqb lookup_eqb region_eqb facts = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Certificate 3: the lookup padding tuples equal table row 0.

      Checked against the loaded generator table, with the table size read off
      the program ([layouter_table_rows], [= 1024]). *)
  Lemma lookup_defaults_certificate :
    Complete.lookup_defaults_ok lookup_eqb system facts
      (layouter_table_rows Garden.Orchard.circuit.synthesize) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** ** Registered consequences for the generator phase *)

  (** The loaded lookup table has [1024 = 2 ^ sinsemilla_k] rows, so the
      [nb_table_rows] argument of [circuit_holds_intro] is a concrete positive
      literal. *)
  Lemma layouter_table_rows_eq :
    layouter_table_rows Garden.Orchard.circuit.synthesize = 1024.
  Proof. vm_cast_no_check (@eq_refl Z 1024). Qed.

  (** The enabled-points list is well formed: every point it lists arises from
      a genuine [SelectorOn] synthesis fact (the converse,
      [Complete.enabled_points_In], is generic).  Structural, so no synthesis
      replay is paid. *)
  Lemma enabled_points_sound
      (fs : list (Fact.t columns RegionId.t))
      (selector : Selector.t) (region : RegionId.t) (offset : Z) :
    List.In (selector, region, offset) (Complete.enabled_points fs) ->
    List.In (Fact.SelectorOn selector region offset) fs.
  Proof.
    induction fs as [| fact fs IH]; intros Hin; [contradiction |].
    destruct fact as
      [ selector' region' offset' | | | | | ];
      cbn [Complete.enabled_points] in Hin.
    - destruct Hin as [Heq | Hin].
      + injection Heq as -> -> ->. left. reflexivity.
      + right. exact (IH Hin).
    - right. exact (IH Hin).
    - right. exact (IH Hin).
    - right. exact (IH Hin).
    - right. exact (IH Hin).
    - right. exact (IH Hin).
  Qed.
End OrchardCompletenessCertificates.
