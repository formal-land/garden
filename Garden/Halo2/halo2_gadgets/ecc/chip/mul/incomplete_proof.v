Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
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
  ((lambda_1 +F lambda_2) *F
    (x_a -F x_r x_a x_p lambda_1)) *F
    UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv.

Definition next_x_a {p : Z} `{Prime p}
    (x_a x_p lambda_1 lambda_2 : Z)
    : Z :=
  Garden.Halo2.halo2_gadgets.utilities_proof.square lambda_2 -F
    x_r x_a x_p lambda_1 -F
    x_a.

Module QMul1Checks.
  Record t : Set := {
    y_a_witnessed : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_next x_p_next lambda_1_next lambda_2_next : Z)
      : t := {|
    y_a_witnessed :=
      y_a x_a_next x_p_next lambda_1_next lambda_2_next;
  |}.

  (* The witnessed [y_a] on the current row (read off [lambda_1]) is uniquely
     determined by the next-row coordinates and gradients, via the "init y_a"
     constraint of [q_mul_1_checks_gate]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_mul_1 : Selector.t)
      (x_a x_p lambda_1 lambda_2 : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_mul_1 ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_1_checks_gate q_mul_1 x_a x_p lambda_1 lambda_2 ⟧ (region, row)) :
      {|
        y_a_witnessed := Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.next ⟧ (region, row)).
  Proof.
    unfold output, y_a, x_r, square.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from Primes.pallas_p]
      cbn in *.
    f_equal.
    exact (Hgate Hselector).
  Qed.

  (* Chip-level determinism: [incomplete.synthesize] enables [q_mul_1]
     at offset 0 of region [EccMulIncomplete1]; [circuit_holds] discharges
     [deterministic]'s [Hselector]/[Hgate].  Parameterised over the same
     selectors/columns [incomplete.configure]/[synthesize] take.  See
     [CompleteAddition.synthesize_correct] (add_proof.v) for the
     template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.synthesize
            q_mul_1 q_mul_2 q_mul_3)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
              q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
            ConstraintSystem.empty)) :
      {|
        y_a_witnessed := Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1, 0))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    cbn in Hfacts.
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1) 0
      q_mul_1 x_a x_p lambda_1 lambda_2).
    - (* [q_mul_1] enabled at offset 0 of region [EccMulIncomplete1]. *)
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ q_mul_1
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1) 0 H1).
    - (* The [q_mul_1] checks gate is the first of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
            q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_1_checks_gate
          q_mul_1 x_a x_p lambda_1 lambda_2)
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End QMul1Checks.

Module QMul2Checks.
  Record t : Set := {
    x_p_next : Z;
    y_p_next : Z;
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_p_cur y_p_cur x_a_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_p_next := x_p_cur;
    y_p_next := y_p_cur;
    x_a_next := next_x_a x_a_cur x_p_cur lambda_1_cur lambda_2_cur;
  |}.

  (* The next-row base point is copied unchanged ([x_p_check]/[y_p_check]) and the
     next accumulator [x_a] is the secant-line image of the current row, so the
     three next-row cells are uniquely determined by the current row. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_mul_2 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_mul_2 ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_2_checks_gate q_mul_2 z x_a x_p y_p lambda_1 lambda_2 ⟧ (region, row)) :
      {|
        x_p_next := Γ ⊢ ⟦ Expression.Advice x_p Rotation.next ⟧ (region, row);
        y_p_next := Γ ⊢ ⟦ Expression.Advice y_p Rotation.next ⟧ (region, row);
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice y_p Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output, next_x_a, x_r, square.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (hxp & hyp & _ & _ & hsec & _).
    specialize (hxp Hselector).
    specialize (hyp Hselector).
    specialize (hsec Hselector).
    f_equal.
    - (* [x_p] is copied unchanged. *) now symmetry.
    - (* [y_p] is copied unchanged. *) now symmetry.
    - (* [x_a] on the next row is the secant-line image. *) field_solve.
  Qed.

  (* Chip-level determinism: [incomplete.synthesize] enables [q_mul_2]
     at offset 0 of region [EccMulIncomplete2]; [circuit_holds] discharges
     [deterministic]'s [Hselector]/[Hgate]. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.synthesize
            q_mul_1 q_mul_2 q_mul_3)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
              q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
            ConstraintSystem.empty)) :
      {|
        x_p_next := Γ ⊢ ⟦ Expression.Advice x_p Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0);
        y_p_next := Γ ⊢ ⟦ Expression.Advice y_p Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0);
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0))
          (Γ ⊢ ⟦ Expression.Advice y_p Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0))
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    cbn in Hfacts.
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2) 0
      q_mul_2 z x_a x_p y_p lambda_1 lambda_2).
    - (* [q_mul_2] enabled at offset 0 of region [EccMulIncomplete2]. *)
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ q_mul_2
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2) 0 H2).
    - (* The [q_mul_2] checks gate is the second of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
            q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_2_checks_gate
          q_mul_2 z x_a x_p y_p lambda_1 lambda_2)
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End QMul2Checks.

Module QMul3Checks.
  Record t : Set := {
    x_a_next : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (x_a_cur x_p_cur lambda_1_cur lambda_2_cur : Z)
      : t := {|
    x_a_next := next_x_a x_a_cur x_p_cur lambda_1_cur lambda_2_cur;
  |}.

  (* The final iteration's next accumulator [x_a] is the secant-line image of the
     current row, uniquely determined by the current-row coordinates and
     gradients via [q_mul_3_checks_gate]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_mul_3 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_mul_3 ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete
            .q_mul_3_checks_gate q_mul_3 z x_a x_p y_p lambda_1 lambda_2 ⟧ (region, row)) :
      {|
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output, next_x_a, x_r, square.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (_ & _ & hsec & _).
    specialize (hsec Hselector).
    f_equal.
    field_solve.
  Qed.

  (* Chip-level determinism: [incomplete.synthesize] enables [q_mul_3]
     at offset 0 of region [EccMulIncomplete3]; [circuit_holds] discharges
     [deterministic]'s [Hselector]/[Hgate]. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
      (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.synthesize
            q_mul_1 q_mul_2 q_mul_3)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
              q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
            ConstraintSystem.empty)) :
      {|
        x_a_next := Γ ⊢ ⟦ Expression.Advice x_a Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3, 0))
          (Γ ⊢ ⟦ Expression.Advice x_p Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3, 0))
          (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    cbn in Hfacts.
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3) 0
      q_mul_3 z x_a x_p y_p lambda_1 lambda_2).
    - (* [q_mul_3] enabled at offset 0 of region [EccMulIncomplete3]. *)
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ q_mul_3
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3) 0 H3).
    - (* The [q_mul_3] checks gate is the third of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.configure
            q_mul_1 q_mul_2 q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.incomplete.q_mul_3_checks_gate
          q_mul_3 z x_a x_p y_p lambda_1 lambda_2)
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End QMul3Checks.
