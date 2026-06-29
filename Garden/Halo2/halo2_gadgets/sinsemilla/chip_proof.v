Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Definition x_r {p : Z} `{Prime p}
    (x_a x_p lambda_1 : Z)
    : Z :=
  Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_1 -F x_a -F x_p.

Definition y_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  (lambda_1 +F lambda_2) *F
    (x_a -F x_r x_a x_p lambda_1).

Module InitialYQ.
  Record t : Set := {
    y_a : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (y_q : Z)
      : t := {|
    y_a := y_q *F UnOp.from 2;
  |}.

  (* The running ordinate [y_a] at the start of a message (the derived
     combination of the current-row cells) is forced to twice the fixed seed
     [y_q] by the single "init_y_q_check" constraint of [initial_y_q_gate]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_sinsemilla4 : Selector.t)
      (fixed_y_q : Fixed.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_sinsemilla4 ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .initial_y_q_gate q_sinsemilla4 fixed_y_q x_a x_p lambda_1 lambda_2 ⟧ (region, row)) :
      {|
        y_a :=
          Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
              .y_a x_a x_p lambda_1 lambda_2 Rotation.cur ⟧ (region, row);
      |} =
        output (Γ ⊢ ⟦ Expression.Fixed fixed_y_q Rotation.cur ⟧ (region, row)).
  Proof.
    (* The single "init_y_q_check" constraint states [y_q * 2 = y_a_cur], which
       is exactly the (flipped) record equality to prove. *)
    unfold output, x_r, Garden.Halo2.halo2_gadgets.utilities_proof.square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    specialize (Hgate Hselector).
    f_equal.
    symmetry.
    exact Hgate.
  Qed.

  (* Chip-level determinism (admitted): [chip.synthesize_instance] enables
     [q_sinsemilla4] at offset 0 of region [SinsemillaInitialY], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic].
     Parameterised over the selectors/columns [configure_instance]/
     [synthesize_instance] take.  See [CompleteAddition.synthesize_correct]
     (add_proof.v) for the proved template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_sinsemilla1 q_sinsemilla4 : Selector.t)
      (q_sinsemilla2 fixed_y_q : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_instance
            q_sinsemilla1 q_sinsemilla4)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_instance
              q_sinsemilla1 q_sinsemilla4 q_sinsemilla2 fixed_y_q
              x_a x_p bits lambda_1 lambda_2)
            ConstraintSystem.empty)) :
      {|
        y_a :=
          Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
              .y_a x_a x_p lambda_1 lambda_2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaInitialY, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Fixed fixed_y_q Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaInitialY, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    cbn in Hfacts.
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaInitialY) 0
      q_sinsemilla4 fixed_y_q x_a x_p lambda_1 lambda_2).
    - (* [q_sinsemilla4] enabled at offset 0 of region [SinsemillaInitialY]. *)
      destruct Hfacts as (H1 & H4 & Htrivial).
      exact (enabled_nonzero Γ q_sinsemilla4
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaInitialY) 0 H4).
    - (* The [initial_y_q] gate is one of the configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_instance
            q_sinsemilla1 q_sinsemilla4 q_sinsemilla2 fixed_y_q
            x_a x_p bits lambda_1 lambda_2)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          q_sinsemilla4 fixed_y_q x_a x_p lambda_1 lambda_2)
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaInitialY) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End InitialYQ.

Module Sinsemilla.
  Record t : Set := {
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_cur x_p_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_a_next :=
      Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_2_cur -F
        x_r x_a_cur x_p_cur lambda_1_cur -F
        x_a_cur;
  |}.

  (* The next-row accumulator [x_a] is uniquely determined by the current row:
     the "Secant line" constraint of [sinsemilla_gate] gives
     [x_a_next = lambda_2^2 - x_r - x_a] directly (no division, no precondition),
     where [x_r = lambda_1^2 - x_a - x_p]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_sinsemilla1 : Selector.t)
      (q_sinsemilla2 : Fixed.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_sinsemilla1 ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧ (region, row)) :
      {|
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧ (region, row)).
  Proof.
    (* The "Secant line" constraint gives [lambda_2^2 = x_a_next + x_r + x_a]
       directly; solving for [x_a_next] needs no division and no precondition. *)
    unfold output, x_r, Garden.Halo2.halo2_gadgets.utilities_proof.square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as [Hc1 Hc2].
    specialize (Hc1 Hselector).
    clear Hc2.
    f_equal.
    field_solve.
  Qed.

  (* Chip-level determinism (admitted): [chip.synthesize_instance] enables
     [q_sinsemilla1] at offset 0 of region [SinsemillaGate], so [circuit_holds]
     discharges the [Hselector]/[Hgate] of [deterministic].  Parameterised over
     the selectors/columns [configure_instance]/[synthesize_instance] take. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_sinsemilla1 q_sinsemilla4 : Selector.t)
      (q_sinsemilla2 fixed_y_q : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_instance
            q_sinsemilla1 q_sinsemilla4)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_instance
              q_sinsemilla1 q_sinsemilla4 q_sinsemilla2 fixed_y_q
              x_a x_p bits lambda_1 lambda_2)
            ConstraintSystem.empty)) :
      {|
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate, 0))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    cbn in Hfacts.
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate) 0
      q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2).
    - (* [q_sinsemilla1] enabled at offset 0 of region [SinsemillaGate]. *)
      destruct Hfacts as (H1 & H4 & Htrivial).
      exact (enabled_nonzero Γ q_sinsemilla1
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate) 0 H1).
    - (* The [sinsemilla] gate is one of the configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_instance
            q_sinsemilla1 q_sinsemilla4 q_sinsemilla2 fixed_y_q
            x_a x_p bits lambda_1 lambda_2)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2)
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaGate) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End Sinsemilla.

Module GeneratorTable.
  (* The concrete Sinsemilla generator table loaded by [load_generator_table]:
     column [TableIdx] holds the row index, and [TableX]/[TableY] hold the
     [SINSEMILLA_S] generator coordinates at that index. This is the value model
     read by the lookup [Prop] semantics ([Assignment.lookup]). *)
  Definition lookup (column : Lookup.t) (table_row : Z) : Z :=
    match column with
    | Lookup.TableIdx => table_row
    | Lookup.TableX =>
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_x table_row
    | Lookup.TableY =>
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_y table_row
    end.

  (* The table-row count derived by running [load_generator_table], rather than
     a free parameter: the largest loaded column length, [2 ^ sinsemilla_k]. *)
  Definition table_rows : Z :=
    layouter_table_rows
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table.

  Lemma table_rows_eq :
    table_rows = 2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k.
  Proof.
    unfold table_rows,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table.
    cbn [layouter_table_rows List.map
      Garden.Halo2.Synthesis.LookupTableColumn.values].
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes.
    rewrite !List.length_map, !List.length_seq.
    unfold List.list_max.
    cbn [fold_right].
    rewrite Nat.max_0_r, !Nat.max_id.
    rewrite Z2Nat.id by (apply Z.pow_nonneg; lia).
    reflexivity.
  Qed.

  (* The table carried by [Γ] agrees with the concrete [lookup] model on every
     loaded row [0 <= i < 2 ^ sinsemilla_k], derived from the synthesis facts of
     running [load_generator_table] — no longer assumed as a free hypothesis. *)
  Lemma loaded
      (Γ : Assignment.t columns RegionId.t)
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (col : Lookup.t) (i : Z)
      (Hi : 0 <= i < 2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k) :
      Γ.(Assignment.lookup) col i = lookup col i.
  Proof.
    assert (Hk : (Z.to_nat i <
        Z.to_nat (2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k))%nat).
    { apply Z2Nat.inj_lt; [lia | apply Z.pow_nonneg; lia | lia]. }
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table
      in Hload.
    cbn [layouter_facts List.map interpret_facts
      Garden.Halo2.Synthesis.LookupTableColumn.lookup
      Garden.Halo2.Synthesis.LookupTableColumn.values
      Garden.Halo2.Synthesis.LookupTableColumn.default_value] in Hload.
    destruct Hload as (Hidx & Hx & Hy & _).
    cbn [interpret_fact] in Hidx, Hx, Hy.
    destruct col; cbn [lookup].
    - rewrite Hidx. unfold value_at_row,
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes.
      rewrite nth_map_seq by exact Hk.
      apply Z2Nat.id; lia.
    - rewrite Hx. unfold value_at_row,
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes.
      rewrite List.map_map.
      rewrite nth_map_seq by exact Hk.
      now rewrite Z2Nat.id by lia.
    - rewrite Hy. unfold value_at_row,
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes.
      rewrite List.map_map.
      rewrite nth_map_seq by exact Hk.
      now rewrite Z2Nat.id by lia.
  Qed.

  (* Soundness of the generator-table lookup: on an active row
     ([q_sinsemilla1 = 1]), the three queried slots collapse to the bare
     [word]/[x_p]/[y_p] field values, so the lookup pins them to a row of the
     concrete generator table — the witnessed point is the [SINSEMILLA_S]
     generator for the message word. The looked-up index [table_row] is the word
     itself (bounded by [nb_table_rows]), and the witnessed coordinates equal
     that generator's coordinates. *)
  Theorem sound
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (row : Z)
      (q_sinsemilla1 : Selector.t)
      (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hactive :
        Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, row) = 1)
      (Hlookup :
        eval_lookup_argument Γ (region, row) table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .generator_table_argument
              q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2)) :
      exists table_row,
        0 <= table_row < 2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k /\
        (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .generator_table_word q_sinsemilla2 bits ⟧ (region, row)) = table_row /\
        (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧ (region, row)) =
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_x table_row /\
        (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .generator_table_y_p x_a x_p lambda_1 lambda_2 ⟧ (region, row)) =
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_y table_row.
  Proof.
    assert (Hsub : BinOp.sub 1 1 = 0).
    { unfold BinOp.sub. now rewrite Z.sub_diag, Zmod_0_l. }
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from table_rows
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_x
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_y]
      cbn in Hlookup, Hactive |- *.
    destruct Hlookup as (table_row & Hbound & Hpairs).
    rewrite table_rows_eq in Hbound.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
      in Hpairs.
    cbn [LookupArgument.pairs] in Hpairs.
    rewrite !Forall_cons_iff in Hpairs.
    destruct Hpairs as (Hidx & Hx & Hy & _).
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_x
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_y]
      cbn in Hidx, Hx, Hy.
    (* Replace the abstract table reads by the concrete generator-table model,
       using the loaded-table facts at the in-range witnessed [table_row]. *)
    rewrite (loaded Γ Hload Lookup.TableIdx table_row Hbound) in Hidx.
    rewrite (loaded Γ Hload Lookup.TableX table_row Hbound) in Hx.
    rewrite (loaded Γ Hload Lookup.TableY table_row Hbound) in Hy.
    cbn [lookup] in Hidx, Hx, Hy.
    rewrite !Hactive in Hidx, Hx, Hy.
    exists table_row.
    repeat split.
    - exact (proj1 Hbound).
    - exact (proj2 Hbound).
    - (* TableIdx slot: [1 *F word] collapses to the evaluated [word]; the outer
         [UnOp.from] is absorbed since [eval] already reduces modulo [p]. *)
      rewrite FieldRewrite.mul_one_left, FieldRewrite.from_sub in Hidx.
      exact Hidx.
    - (* TableX slot: the [(1 - 1) *F s0_x] padding term vanishes, leaving the
         witnessed [x_p]. *)
      FieldRewrite.run.
      setoid_rewrite Hsub in Hx.
      FieldRewrite.run.
      exact Hx.
    - (* TableY slot: same collapse for the derived [y_p]. *)
      FieldRewrite.run.
      setoid_rewrite Hsub in Hy.
      FieldRewrite.run.
      exact Hy.
  Qed.
End GeneratorTable.
