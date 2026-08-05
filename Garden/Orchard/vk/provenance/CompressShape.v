(** * Structural facts about selector-compression output

    These lemmas keep shape proofs symbolic.  In particular, proving that
    combination columns have the domain length does not evaluate their
    entries. *)

From Stdlib Require Import ZArith Lists.List Lia.
Require Import Garden.Halo2.plonkish.main.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module CompressShape.
  Definition description_rows (n_rows : nat)
      (description : SelectorDescription.t) : Prop :=
    List.length description.(SelectorDescription.activations) = n_rows.

  Definition indexed_description_rows (n_rows : nat)
      (indexed : nat * SelectorDescription.t) : Prop :=
    description_rows n_rows (snd indexed).

  Definition values_rows (n_rows : nat) (values : list Z) : Prop :=
    List.length values = n_rows.

  Lemma Forall_filter_preserve {A : Type} (P : A -> Prop)
      (test : A -> bool) (values : list A) :
    List.Forall P values -> List.Forall P (List.filter test values).
  Proof.
    induction values as [|value values IH]; cbn; intros Hvalues.
    - constructor.
    - inversion Hvalues as [|? ? Hvalue Htail]; subst.
      destruct (test value); cbn.
      + constructor; [exact Hvalue | now apply IH].
      + now apply IH.
  Qed.

  Lemma enumerate_preserves_rows (n_rows : nat)
      (descriptions : list SelectorDescription.t) :
    List.Forall (description_rows n_rows) descriptions ->
    List.Forall
      (indexed_description_rows n_rows)
      (enumerate descriptions).
  Proof.
    intros Hrows.
    apply List.Forall_forall.
    intros [index description] Hin.
    apply (proj1 (List.Forall_forall _ _) Hrows).
    exact (List.in_combine_r _ _ _ _ Hin).
  Qed.

  Lemma apply_activation_length (root : Z)
      (activations : list bool) (values : list Z) (n_rows : nat) :
    List.length activations = n_rows ->
    List.length values = n_rows ->
    List.length (Compress.apply_activation root activations values) = n_rows.
  Proof.
    intros Hactivations Hvalues.
    unfold Compress.apply_activation.
    rewrite List.map_length, List.length_combine,
      Hactivations, Hvalues, Nat.min_id.
    reflexivity.
  Qed.

  Lemma combination_values_from_length
      (descriptions : list SelectorDescription.t)
      (root : Z) (values : list Z) (n_rows : nat) :
    List.Forall (description_rows n_rows) descriptions ->
    List.length values = n_rows ->
    List.length
      (snd
        (List.fold_left
          (fun state description =>
            let '(next_root, current_values) := state in
            (next_root + 1,
              Compress.apply_activation
                next_root
                description.(SelectorDescription.activations)
                current_values))
          descriptions
          (root, values))) = n_rows.
  Proof.
    revert root values.
    induction descriptions as [|description descriptions IH];
      intros root values Hdescriptions Hvalues.
    - exact Hvalues.
    - inversion Hdescriptions as [|? ? Hdescription Htail]; subst.
      cbn [List.fold_left].
      apply IH; [exact Htail |].
      eapply apply_activation_length; eauto.
  Qed.

  Lemma combination_values_length (n_rows : nat)
      (descriptions : list SelectorDescription.t) :
    List.Forall (description_rows n_rows) descriptions ->
    List.length (Compress.combination_values n_rows descriptions) = n_rows.
  Proof.
    intros Hdescriptions.
    unfold Compress.combination_values.
    apply combination_values_from_length; [exact Hdescriptions |].
    apply List.repeat_length.
  Qed.

  Lemma scan_candidates_preserves_rows
      (n_rows : nat)
      (candidates : list (nat * SelectorDescription.t))
      (max_degree d : nat)
      (combination : list (nat * SelectorDescription.t))
      (added : list bool)
      (d' : nat)
      (combination' : list (nat * SelectorDescription.t))
      (added' : list bool) :
    List.Forall (indexed_description_rows n_rows) candidates ->
    List.Forall (indexed_description_rows n_rows) combination ->
    Compress.scan_candidates candidates max_degree d combination added =
      (d', combination', added') ->
    List.Forall (indexed_description_rows n_rows) combination'.
  Proof.
    revert max_degree d combination added d' combination' added'.
    induction candidates as [|[index description] candidates IH];
      intros max_degree d combination added d' combination' added'
        Hcandidates Hcombination Hscan.
    - cbn in Hscan.
      assert (combination' = combination) by congruence.
      subst combination'. exact Hcombination.
    - inversion Hcandidates as [|? ? Hdescription Htail]; subst.
      cbn [Compress.scan_candidates] in Hscan.
      destruct (Nat.eqb (d + List.length combination) max_degree) eqn:Hfull.
      + assert (combination' = combination) by congruence.
        subst combination'. exact Hcombination.
      + destruct (List.nth index added false) eqn:Hadded.
        * eapply IH; [exact Htail | exact Hcombination | exact Hscan].
        * destruct
            (List.existsb
              (fun member : nat * SelectorDescription.t =>
                Compress.rows_conflict
                  description.(SelectorDescription.activations)
                  (snd member).(SelectorDescription.activations))
              combination) eqn:Hconflict.
          -- eapply IH; [exact Htail | exact Hcombination | exact Hscan].
          -- destruct
              (Nat.ltb max_degree
                (Nat.max d
                  (description.(SelectorDescription.max_degree) - 1) +
                  List.length combination + 1)) eqn:Hdegree.
             ++ eapply IH; [exact Htail | exact Hcombination | exact Hscan].
             ++ eapply IH; [exact Htail | | exact Hscan].
                apply (proj2 (List.Forall_app _ _ _)).
                split; [exact Hcombination |].
                constructor; [exact Hdescription | constructor].
  Qed.

  Lemma pack_simple_preserves_rows
      (n_rows : nat)
      (todo : list (nat * SelectorDescription.t))
      (max_degree : nat)
      (first_new_column : Z)
      (added : list bool)
      (combinations : list (list Z))
      (assignments : list SelectorAssignment.t) :
    List.Forall (indexed_description_rows n_rows) todo ->
    List.Forall (values_rows n_rows) combinations ->
    List.Forall
      (values_rows n_rows)
      (fst
        (Compress.pack_simple todo max_degree n_rows first_new_column
          added combinations assignments)).
  Proof.
    revert max_degree first_new_column added combinations assignments.
    induction todo as [|[index description] todo IH];
      intros max_degree first_new_column added combinations assignments
        Htodo Hcombinations.
    - exact Hcombinations.
    - inversion Htodo as [|? ? Hdescription Htail]; subst.
      cbn [Compress.pack_simple].
      destruct (List.nth index added false) eqn:Hadded.
      + now apply IH.
      + remember (list_set added index true) as added1.
        remember
          (description.(SelectorDescription.max_degree) - 1)%nat as d.
        destruct
          (Compress.scan_candidates todo max_degree d
            [(index, description)] added1)
          as [[d' combination] added'] eqn:Hscan.
        apply IH; [exact Htail |].
        apply (proj2 (List.Forall_app _ _ _)).
        split; [exact Hcombinations |].
        constructor; [|constructor].
        unfold values_rows.
        apply combination_values_length.
        apply (proj2 (List.Forall_map _ _ _)).
        eapply scan_candidates_preserves_rows;
          [exact Htail | | exact Hscan].
        constructor; [exact Hdescription | constructor].
  Qed.

  Lemma process_preserves_rows
      (selectors : list SelectorDescription.t)
      (max_degree : nat)
      (first_new_column : Z)
      (n_rows : nat) :
    List.Forall (description_rows n_rows) selectors ->
    List.Forall
      (values_rows n_rows)
      (fst (Compress.process selectors max_degree first_new_column)).
  Proof.
    intros Hselectors.
    destruct selectors as [|first selectors].
    - constructor.
    - inversion Hselectors as [|? ? Hfirst Htail]; subst.
      unfold description_rows in Hfirst.
      cbn [Compress.process].
      rewrite Hfirst.
      apply pack_simple_preserves_rows.
      + apply enumerate_preserves_rows.
        apply Forall_filter_preserve.
        constructor; assumption.
      + apply (proj2 (List.Forall_map _ _ _)).
        eapply List.Forall_impl.
        * intros description Hdescription.
          unfold values_rows, description_rows in *.
          rewrite List.map_length.
          exact Hdescription.
        * apply Forall_filter_preserve.
          constructor; assumption.
  Qed.

  Lemma compile_combination_lengths
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z) :
    List.length
      (Compile.compile system infos num_fixed_columns permutation_columns
        constants).(CompiledSystem.combination_columns) =
    List.length
      (Compile.compile system infos num_fixed_columns permutation_columns
        constants).(CompiledSystem.combination_assignments).
  Proof.
    unfold Compile.compile.
    destruct (Compress.process _ _ _) as [combinations assignments].
    cbn.
    now rewrite List.map_length, List.length_seq.
  Qed.

  Lemma compile_combination_assignments_eq_process
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z) :
    (Compile.compile system infos num_fixed_columns permutation_columns
      constants).(CompiledSystem.combination_assignments) =
    fst
      (Compress.process
        (Compile.selector_descriptions system infos)
        (system_degree system)
        num_fixed_columns).
  Proof.
    unfold Compile.compile.
    destruct (Compress.process _ _ _); reflexivity.
  Qed.

  Lemma compile_combination_columns_eq_process
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z) :
    (Compile.compile system infos num_fixed_columns permutation_columns
      constants).(CompiledSystem.combination_columns) =
    List.map
      (fun index => num_fixed_columns + Z.of_nat index)
      (List.seq 0
        (List.length
          (fst
            (Compress.process
              (Compile.selector_descriptions system infos)
              (system_degree system)
              num_fixed_columns)))).
  Proof.
    unfold Compile.compile.
    destruct (Compress.process _ _ _); reflexivity.
  Qed.

  Lemma selector_descriptions_preserve_rows
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (n_rows : nat) :
    List.Forall
      (fun info =>
        List.length info.(Compile.SelectorInfo.activations) = n_rows)
      infos ->
    List.Forall
      (description_rows n_rows)
      (Compile.selector_descriptions system infos).
  Proof.
    intros Hinfos.
    unfold Compile.selector_descriptions.
    apply (proj2 (List.Forall_map _ _ _)).
    apply List.Forall_forall.
    intros [index info] Hin.
    unfold description_rows; cbn.
    apply (proj1 (List.Forall_forall _ _) Hinfos).
    exact (List.in_combine_r _ _ _ _ Hin).
  Qed.

  Lemma compile_combination_assignments_rows
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z)
      (n_rows : nat) :
    List.Forall
      (fun info =>
        List.length info.(Compile.SelectorInfo.activations) = n_rows)
      infos ->
    List.Forall
      (values_rows n_rows)
      (Compile.compile system infos num_fixed_columns permutation_columns
        constants).(CompiledSystem.combination_assignments).
  Proof.
    intros Hinfos.
    unfold Compile.compile.
    remember (Compile.selector_descriptions system infos) as descriptions.
    destruct (Compress.process descriptions _ _) as [combinations assignments]
      eqn:Hprocess.
    cbn.
    pose proof
      (process_preserves_rows descriptions (system_degree system)
        num_fixed_columns n_rows) as Hrows.
    rewrite Hprocess in Hrows; cbn in Hrows.
    apply Hrows.
    subst descriptions.
    now apply selector_descriptions_preserve_rows.
  Qed.

  Lemma compile_combination_columns_range
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z) :
    List.Forall
      (fun column =>
        num_fixed_columns <= column <
          num_fixed_columns +
            Z.of_nat
              (List.length
                (Compile.compile system infos num_fixed_columns
                  permutation_columns constants)
                  .(CompiledSystem.combination_assignments)))
      (Compile.compile system infos num_fixed_columns permutation_columns
        constants).(CompiledSystem.combination_columns).
  Proof.
    unfold Compile.compile.
    destruct (Compress.process _ _ _) as [combinations assignments].
    cbn.
    apply List.Forall_forall.
    intros column Hin.
    apply List.in_map_iff in Hin as [index [<- Hin]].
    apply List.in_seq in Hin.
    lia.
  Qed.

  Corollary compile_combination_columns_bounded_14_15
      (system : Garden.Halo2.main.ConstraintSystem.t
        Garden.Halo2.serialize.Configure.indexed_columns)
      (infos : list Compile.SelectorInfo.t)
      (permutation_columns : list Garden.Halo2.serialize.Raw.ColumnRef.t)
      (constants : list Z)
      (Hcount :
        List.length
          (Compile.compile system infos 14 permutation_columns constants)
            .(CompiledSystem.combination_assignments) = 15%nat) :
    List.Forall
      (fun column => 0 <= column < 29)
      (Compile.compile system infos 14 permutation_columns constants)
        .(CompiledSystem.combination_columns).
  Proof.
    pose proof
      (compile_combination_columns_range system infos 14 permutation_columns
        constants) as Hrange.
    rewrite Hcount in Hrange.
    eapply List.Forall_impl; [|exact Hrange].
    intros column Hcolumn. cbn in Hcolumn. lia.
  Qed.
End CompressShape.
