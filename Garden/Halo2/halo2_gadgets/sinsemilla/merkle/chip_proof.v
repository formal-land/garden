Require Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.
Require Import Garden.Plonky3.M.

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
End DecompositionCheck.
