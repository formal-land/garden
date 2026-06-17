Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module CanonicityChecks.
  Record t : Set := {
    z_84_alpha : Z;
    alpha_0 : Z;
    alpha_0_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (alpha alpha_1 alpha_2 : Z)
      : t :=
    let z_84_alpha := alpha_1 +F alpha_2 *F UnOp.from (2 ^ 2) in
    let alpha_0 := alpha -F z_84_alpha *F UnOp.from (2 ^ 252) in
    {|
      z_84_alpha := z_84_alpha;
      alpha_0 := alpha_0;
      alpha_0_prime :=
        alpha_0 +F UnOp.from (2 ^ 130) -F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
    |}.
End CanonicityChecks.
