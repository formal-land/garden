Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module CommitIvkCanonicityCheck.
  Record t : Set := {
    b_whole : Z;
    d_whole : Z;
    ak : Z;
    nk : Z;
    a_prime : Z;
    b2_c_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b_0 b_1 b_2 c d_0 d_1 : Z)
      : t := {|
    b_whole := b_0 +F b_1 *F UnOp.from (2 ^ 4) +F
      b_2 *F UnOp.from (2 ^ 5);
    d_whole := d_0 +F d_1 *F UnOp.from (2 ^ 9);
    ak := a +F b_0 *F UnOp.from (2 ^ 250) +F
      b_1 *F UnOp.from (2 ^ 254);
    nk := b_2 +F c *F UnOp.from (2 ^ 5) +F
      d_0 *F UnOp.from (2 ^ 245) +F
      d_1 *F UnOp.from (2 ^ 254);
    a_prime :=
      a +F UnOp.from (2 ^ 130) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
    b2_c_prime :=
      b_2 +F c *F UnOp.from (2 ^ 5) +F
        UnOp.from (2 ^ 140) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
  |}.
End CommitIvkCanonicityCheck.
