Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.utilities.cond_swap.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module CondSwap.
  Record t : Set := {
    a_swapped : Z;
    b_swapped : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b swap : Z)
      : t := {|
    a_swapped := Garden.Halo2.halo2_gadgets.utilities_proof.ternary swap b a;
    b_swapped := Garden.Halo2.halo2_gadgets.utilities_proof.ternary swap a b;
  |}.

  (* The "a check"/"b check" constraints of [cond_swap_gate] force the
     [a_swapped]/[b_swapped] cells to the ternary selection of [a]/[b] on
     [swap], exactly [output]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (q_swap : Selector.t)
      (a b a_swapped b_swapped swap : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_swap ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap
            .cond_swap_gate q_swap a b a_swapped b_swapped swap ⟧ (region, row)) :
      {|
        a_swapped := Γ ⊢ ⟦ Expression.Advice a_swapped Rotation.cur ⟧ (region, row);
        b_swapped := Γ ⊢ ⟦ Expression.Advice b_swapped Rotation.cur ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice a Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice b Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice swap Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output, Garden.Halo2.halo2_gadgets.utilities_proof.ternary.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as [Ha [Hb _] ].
    specialize (Ha Hselector).
    specialize (Hb Hselector).
    f_equal.
    - exact Ha.
    - exact Hb.
  Qed.

  (* The "swap is bool" constraint of [cond_swap_gate] forces the [swap] cell
     to be boolean. *)
  Theorem swap_is_bool
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (q_swap : Selector.t)
      (a b a_swapped b_swapped swap : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_swap ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap
            .cond_swap_gate q_swap a b a_swapped b_swapped swap ⟧ (region, row)) :
      IsBool.t (Γ ⊢ ⟦ Expression.Advice swap Rotation.cur ⟧ (region, row)).
  Proof.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as [_ [_ Hbool] ].
    exact (Hbool Hselector).
  Qed.

  (* Chip-level determinism: [cond_swap.synthesize_instance] enables [q_swap]
     at offset 0 of region [RegionId.GadgetLocal.CondSwap], so [circuit_holds]
     against the matching [cond_swap.configure_instance] discharges the
     [Hselector]/[Hgate] hypotheses of [deterministic]. The proof follows the
     same structure as [Addition.synthesize_correct] (add_chip_proof.v). *)
  Theorem synthesize_correct
      (q_swap : Selector.t)
      (a b a_swapped b_swapped swap : Advice.t)
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.utilities.cond_swap
            .synthesize_instance q_swap)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.utilities.cond_swap
              .configure_instance q_swap a b a_swapped b_swapped swap)
            ConstraintSystem.empty)) :
      {|
        a_swapped := Γ ⊢ ⟦ Expression.Advice a_swapped Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap, 0);
        b_swapped := Γ ⊢ ⟦ Expression.Advice b_swapped Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice a Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap, 0))
          (Γ ⊢ ⟦ Expression.Advice b Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap, 0))
          (Γ ⊢ ⟦ Expression.Advice swap Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    eapply deterministic.
    - cbn in Hfacts.
      destruct Hfacts as [Hselector _].
      exact (enabled_nonzero Γ q_swap
        (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap) 0 Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.utilities.cond_swap
            .configure_instance q_swap a b a_swapped b_swapped swap)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.cond_swap
          .cond_swap_gate q_swap a b a_swapped b_swapped swap)
        (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap) 0);
        [cbn; left; reflexivity | exact Hgates].
  Qed.
End CondSwap.
