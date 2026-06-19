Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module DecompositionCheck.
  Record t : Set := {
    l_whole : Z;
    left_node : Z;
    right_node : Z;
    z1_b : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a_whole b_whole c_whole a_1 b_1 b_2 : Z)
      : t :=
    let l_whole := a_whole -F a_1 *F UnOp.from (2 ^ 10) in
    let z1_b := b_1 +F b_2 *F UnOp.from (2 ^ 5) in
    let b_0 := b_whole -F z1_b *F UnOp.from (2 ^ 10) in
    {|
      l_whole := l_whole;
      left_node :=
        a_1 +F
          (b_0 +F b_1 *F UnOp.from (2 ^ 10)) *F
            UnOp.from (2 ^ 240);
      right_node := b_2 +F c_whole *F UnOp.from (2 ^ 5);
      z1_b := z1_b;
    |}.

  (* The four reconstruction cells are uniquely determined by the six input
     cells of the current/next rows via the constraints of
     [decomposition_check_gate] ("l_check", "left_check", "right_check",
     "b1_b2_check"). The inputs are read as:
       a_whole = a_col.cur,  b_whole = b_col.cur,  c_whole = c_col.cur,
       a_1     = a_col.next, b_1     = c_col.next, b_2     = left_col.next. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (q_decompose : Selector.t)
      (a_col b_col c_col left_col right_col : Advice.t)
      (Hselector : ⟦ q_decompose ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
              q_decompose a_col b_col c_col left_col right_col ⟧ ρ) :
      {|
        l_whole := ⟦ Expression.Advice right_col Rotation.next ⟧ ρ;
        left_node := ⟦ Expression.Advice left_col Rotation.cur ⟧ ρ;
        right_node := ⟦ Expression.Advice right_col Rotation.cur ⟧ ρ;
        z1_b := ⟦ Expression.Advice b_col Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice a_col Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice b_col Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice c_col Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice a_col Rotation.next ⟧ ρ)
          (⟦ Expression.Advice c_col Rotation.next ⟧ ρ)
          (⟦ Expression.Advice left_col Rotation.next ⟧ ρ).
  Proof.
  Admitted.
End DecompositionCheck.
