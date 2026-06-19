Require Garden.Orchard.circuit.note_commit.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module MessagePieceB.
  Record t : Set := {
    b : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (b_0 b_1 b_2 b_3 : Z)
      : t := {|
    b :=
      b_0 +F b_1 *F UnOp.from (2 ^ 4) +F
      b_2 *F UnOp.from (2 ^ 5) +F
      b_3 *F UnOp.from (2 ^ 6);
  |}.
End MessagePieceB.

Module MessagePieceD.
  Record t : Set := {
    d : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (d_0 d_1 d_2 d_3 : Z)
      : t := {|
    d :=
      d_0 +F d_1 *F UnOp.from 2 +F
      d_2 *F UnOp.from (2 ^ 2) +F
      d_3 *F UnOp.from (2 ^ 10);
  |}.
End MessagePieceD.

Module MessagePieceE.
  Record t : Set := {
    e : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (e_0 e_1 : Z)
      : t := {|
    e := e_0 +F e_1 *F UnOp.from (2 ^ 6);
  |}.
End MessagePieceE.

Module MessagePieceG.
  Record t : Set := {
    g : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (g_0 g_1 g_2 : Z)
      : t := {|
    g := g_0 +F g_1 *F UnOp.from 2 +F
      g_2 *F UnOp.from (2 ^ 10);
  |}.
End MessagePieceG.

Module MessagePieceH.
  Record t : Set := {
    h : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (h_0 h_1 : Z)
      : t := {|
    h := h_0 +F h_1 *F UnOp.from (2 ^ 5);
  |}.
End MessagePieceH.

Module InputGD.
  Record t : Set := {
    gd_x : Z;
    a_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b_0 b_1 : Z)
      : t := {|
    gd_x :=
      a +F b_0 *F UnOp.from (2 ^ 250) +F
      b_1 *F UnOp.from (2 ^ 254);
    a_prime :=
      a +F UnOp.from (2 ^ 130) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
  |}.
End InputGD.

Module InputPKD.
  Record t : Set := {
    pkd_x : Z;
    b3_c_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (b_3 c d_0 : Z)
      : t := {|
    pkd_x :=
      b_3 +F c *F UnOp.from (2 ^ 4) +F
      d_0 *F UnOp.from (2 ^ 254);
    b3_c_prime :=
      b_3 +F c *F UnOp.from (2 ^ 4) +F
        UnOp.from (2 ^ 140) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
  |}.
End InputPKD.

Module InputValue.
  Record t : Set := {
    value : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (d_2 z1_d e_0 : Z)
      : t := {|
    value :=
      d_2 +F z1_d *F UnOp.from (2 ^ 8) +F
      e_0 *F UnOp.from (2 ^ 58);
  |}.
End InputValue.

Module InputRho.
  Record t : Set := {
    rho : Z;
    e1_f_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (e_1 f g_0 : Z)
      : t := {|
    rho :=
      e_1 +F f *F UnOp.from (2 ^ 4) +F
      g_0 *F UnOp.from (2 ^ 254);
    e1_f_prime :=
      e_1 +F f *F UnOp.from (2 ^ 4) +F
        UnOp.from (2 ^ 140) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
  |}.
End InputRho.

Module InputPsi.
  Record t : Set := {
    psi : Z;
    g1_g2_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (g_1 g_2 h_0 h_1 : Z)
      : t := {|
    psi :=
      g_1 +F g_2 *F UnOp.from (2 ^ 9) +F
      h_0 *F UnOp.from (2 ^ 249) +F
      h_1 *F UnOp.from (2 ^ 254);
    g1_g2_prime :=
      g_1 +F g_2 *F UnOp.from (2 ^ 9) +F
        UnOp.from (2 ^ 130) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
  |}.
End InputPsi.

Module YCoordinateChecks.
  Record t : Set := {
    j : Z;
    y : Z;
    j_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (lsb k_0 z1_j k_2 k_3 : Z)
      : t :=
    let j := lsb +F k_0 *F UnOp.from 2 +F
      z1_j *F UnOp.from (2 ^ 10) in
    {|
      j := j;
      y :=
        j +F k_2 *F UnOp.from (2 ^ 250) +F
        k_3 *F UnOp.from (2 ^ 254);
      j_prime :=
        j +F UnOp.from (2 ^ 130) -F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
    |}.
End YCoordinateChecks.
