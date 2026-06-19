Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
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
      (Γ : Assignment.t columns) (row : Z)
      (q_decompose : Selector.t)
      (a_col b_col c_col left_col right_col : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_decompose ⟧ row <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
              q_decompose a_col b_col c_col left_col right_col ⟧ row) :
      {|
        l_whole := Γ ⊢ ⟦ Expression.Advice right_col Rotation.next ⟧ row;
        left_node := Γ ⊢ ⟦ Expression.Advice left_col Rotation.cur ⟧ row;
        right_node := Γ ⊢ ⟦ Expression.Advice right_col Rotation.cur ⟧ row;
        z1_b := Γ ⊢ ⟦ Expression.Advice b_col Rotation.next ⟧ row;
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice b_col Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.next ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.next ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice left_col Rotation.next ⟧ row).
  Proof.
    (* Each of the four reconstruction cells is fixed by one constraint, all
       linear once the radix constants [2^5], [2^10], [2^240] are exposed:
       "l_check" pins [l_whole], "left_check" pins [left_node] (using
       "b1_b2_check" to rewrite the [b] decomposition), "right_check" pins
       [right_node], "b1_b2_check" pins [z1_b]. *)
    unfold output.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as (Hc1 & Hc2 & Hc3 & Hc4).
    specialize (Hc1 Hselector).
    specialize (Hc2 Hselector).
    specialize (Hc3 Hselector).
    specialize (Hc4 Hselector).
    f_equal; field_solve.
  Qed.
End DecompositionCheck.
