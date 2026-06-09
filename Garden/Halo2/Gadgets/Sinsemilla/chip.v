Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.
Require Garden.Halo2.Gadgets.Sinsemilla.SConstants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition sinsemilla_k : Z := 10.

Definition sinsemilla_s0_x : Z :=
  6200097879647205583499851243213148560621730003917924543823561700220554504799.

Definition sinsemilla_s0_y : Z :=
  21285653556795296467031706491948305595095309413618206259690549906869937136771.

Definition x_r
    (x_a x_p lambda_1 : Advice.t)
    (rotation : Rotation.t)
    : Expression.t columns :=
  let x_a := Expression.Advice x_a rotation in
  let x_p := Expression.Advice x_p rotation in
  let lambda_1 := Expression.Advice lambda_1 rotation in
  Garden.Halo2.Gadgets.Utilities.square lambda_1 ➖ x_a ➖ x_p.

Definition y_a
    (x_a x_p lambda_1 lambda_2 : Advice.t)
    (rotation : Rotation.t)
    : Expression.t columns :=
  let x_a_expr := Expression.Advice x_a rotation in
  let lambda_1_expr := Expression.Advice lambda_1 rotation in
  let lambda_2_expr := Expression.Advice lambda_2 rotation in
  (lambda_1_expr ➕ lambda_2_expr)
    ✖️ (x_a_expr ➖ x_r x_a x_p lambda_1 rotation).

Definition q_s3
    (q_sinsemilla2 : Fixed.t)
    : Expression.t columns :=
  let q_s2 := Expression.Fixed q_sinsemilla2 Rotation.cur in
  q_s2 ✖️ (q_s2 ➖ Expression.Constant 1).

Definition configure_generator_table
    (meta : ConstraintSystem.t columns)
    (q_sinsemilla1 : Selector.t)
    (q_sinsemilla2 : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_lookup meta {|
    LookupArgument.pairs :=
      let q_s1 := Expression.Selector q_sinsemilla1 in
      let q_s2 := Expression.Fixed q_sinsemilla2 Rotation.cur in
      let q_s3 := q_s3 q_sinsemilla2 in
      let q_run := q_s2 ➖ q_s3 in
      let z_cur := Expression.Advice bits Rotation.cur in
      let z_next := Expression.Advice bits Rotation.next in
      let word := z_cur ➖ (q_run ✖️ z_next ● (2 ^ sinsemilla_k)) in
      let x_p_expr := Expression.Advice x_p Rotation.cur in
      let lambda1 := Expression.Advice lambda_1 Rotation.cur in
      let x_a_expr := Expression.Advice x_a Rotation.cur in
      let y_p :=
        (y_a x_a x_p lambda_1 lambda_2 Rotation.cur
          ● Garden.Halo2.Gadgets.Ecc.chip.constants.two_inv)
          ➖ (lambda1 ✖️ (x_a_expr ➖ x_p_expr)) in
      let not_q_s1 := Expression.Constant 1 ➖ q_s1 in
      [
        (q_s1 ✖️ word, Fixed.Lookup Lookup.TableIdx);
        (q_s1 ✖️ x_p_expr ➕ (not_q_s1 ● sinsemilla_s0_x),
          Fixed.Lookup Lookup.TableX);
        (q_s1 ✖️ y_p ➕ (not_q_s1 ● sinsemilla_s0_y),
          Fixed.Lookup Lookup.TableY)
      ];
  |} in
  meta.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    (q_sinsemilla2 fixed_y_q : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    : ConstraintSystem.t columns :=
  let meta :=
    configure_generator_table
      meta
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2 in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Initial y_Q";
    Gate.constraints :=
      let y_q := Expression.Fixed fixed_y_q Rotation.cur in
      let y_a_cur := y_a x_a x_p lambda_1 lambda_2 Rotation.cur in
      Constraints.with_selector q_sinsemilla4 [
        (Some "init_y_q_check",
          Constraint.EqualZeroToPrecise (y_q ● 2 ➖ y_a_cur))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Sinsemilla gate";
    Gate.constraints :=
      let q_s3 := q_s3 q_sinsemilla2 in
      let lambda_1_next := Expression.Advice lambda_1 Rotation.next in
      let lambda_2_cur := Expression.Advice lambda_2 Rotation.cur in
      let x_a_cur := Expression.Advice x_a Rotation.cur in
      let x_a_next := Expression.Advice x_a Rotation.next in
      let x_r_cur := x_r x_a x_p lambda_1 Rotation.cur in
      let y_a_cur := y_a x_a x_p lambda_1 lambda_2 Rotation.cur in
      let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
      let secant_line :=
        Garden.Halo2.Gadgets.Utilities.square lambda_2_cur
          ➖ (x_a_next ➕ x_r_cur ➕ x_a_cur) in
      let lhs := lambda_2_cur ● 4 ✖️ (x_a_cur ➖ x_a_next) in
      let rhs :=
        (y_a_cur ● 2)
          ➕ ((Expression.Constant 2 ➖ q_s3) ✖️ y_a_next)
          ➕ ((q_s3 ● 2) ✖️ lambda_1_next) in
      let y_check := lhs ➖ rhs in
      Constraints.with_selector q_sinsemilla1 [
        (Some "Secant line", Constraint.EqualZeroToPrecise secant_line);
        (Some "y check", Constraint.EqualZeroToPrecise y_check)
      ];
  |} in
  meta.

Definition configure_1
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QSinsemilla1_1
    Selector.QSinsemilla4_1
    Fixed.QSinsemilla2_1
    Fixed.LagrangeCoeffs0
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4.

Definition configure_2
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QSinsemilla1_2
    Selector.QSinsemilla4_2
    Fixed.QSinsemilla2_2
    Fixed.LagrangeCoeffs1
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.

Definition sinsemilla_s_x (index : Z) : Z :=
  Garden.Halo2.Gadgets.Sinsemilla.SConstants.x index.

Definition sinsemilla_s_y (index : Z) : Z :=
  Garden.Halo2.Gadgets.Sinsemilla.SConstants.y index.

Definition generator_table_row (index : nat) : list Raw.Event.t :=
  let index := Z.of_nat index in
  [
    Raw.Event.AssignFixed 0 index "table_idx" index;
    Raw.Event.AssignFixed 1 index "table_x" (sinsemilla_s_x index);
    Raw.Event.AssignFixed 2 index "table_y" (sinsemilla_s_y index)
  ].

Definition generator_table_events : list Raw.Event.t :=
  List.flat_map
    generator_table_row
    (List.seq 0 (Z.to_nat (2 ^ sinsemilla_k))).

Definition generator_table_fills : list Raw.Event.t :=
  [
    Raw.Event.FillFromRow 0 (2 ^ sinsemilla_k) 0;
    Raw.Event.FillFromRow 1 (2 ^ sinsemilla_k) sinsemilla_s0_x;
    Raw.Event.FillFromRow 2 (2 ^ sinsemilla_k) sinsemilla_s0_y
  ].

Definition load_generator_table
    : Layouter.t columns unit :=
  Layouter.assign_table_with_fills
    "generator_table"
    generator_table_events
    generator_table_fills.

Module HashResult.
  Record t : Set := {
    x : Cell.t columns;
    y : Cell.t columns;
    z1_a : Cell.t columns;
    z1_b : Cell.t columns;
    z1_d : Cell.t columns;
    z1_g : Cell.t columns;
    z13_a : Cell.t columns;
    z13_c : Cell.t columns;
    z13_f : Cell.t columns;
    z13_g : Cell.t columns;
  }.
End HashResult.

Fixpoint enable_selector_rows
    (selector : Selector.t)
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ := Region.enable_selector selector offset "" in
      enable_selector_rows selector (offset + 1) count
  end.

Fixpoint assign_q_s2_rows
    (q_sinsemilla2 : Fixed.t)
    (offset : Z)
    (count : nat)
    (final_piece : bool)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S O =>
      let_ℛ _ :=
        Region.assign_fixed
          (if final_piece
           then "q_s2 for final piece"
           else "q_s2 between pieces")
          q_sinsemilla2
          offset
          (Value.Known (if final_piece then 2 else 0)) in
      return_ℛ tt
  | S count =>
      let_ℛ _ :=
        Region.assign_fixed
          "q_s2 = 1"
          q_sinsemilla2
          offset
          (Value.Known 1) in
      assign_q_s2_rows q_sinsemilla2 (offset + 1) count final_piece
  end.

Fixpoint assign_intermediate_zs
    (bits : Advice.t)
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ :=
        Region.assign_advice "z" bits offset Value.Unknown in
      assign_intermediate_zs bits (offset + 1) count
  end.

Fixpoint assign_double_and_add_rows
    (x_a x_p lambda_1 lambda_2 : Advice.t)
    (offset : Z)
    (count : nat)
    : Region.t columns (Cell.t columns) :=
  match count with
  | O => Region.assign_advice "x_a" x_a offset Value.Unknown
  | S O =>
      let_ℛ _ := Region.assign_advice "x_p" x_p offset Value.Unknown in
      let_ℛ _ :=
        Region.assign_advice "lambda_1" lambda_1 offset Value.Unknown in
      let_ℛ _ :=
        Region.assign_advice "lambda_2" lambda_2 offset Value.Unknown in
      Region.assign_advice "x_a" x_a (offset + 1) Value.Unknown
  | S count =>
      let_ℛ _ := Region.assign_advice "x_p" x_p offset Value.Unknown in
      let_ℛ _ :=
        Region.assign_advice "lambda_1" lambda_1 offset Value.Unknown in
      let_ℛ _ :=
        Region.assign_advice "lambda_2" lambda_2 offset Value.Unknown in
      let_ℛ _ := Region.assign_advice "x_a" x_a (offset + 1) Value.Unknown in
      assign_double_and_add_rows
        x_a
        x_p
        lambda_1
        lambda_2
        (offset + 1)
        count
  end.

Definition synthesize_hash_piece
    (q_sinsemilla1 : Selector.t)
    (q_sinsemilla2 : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    (piece : Cell.t columns)
    (offset : Z)
    (num_words : nat)
    (final_piece : bool)
    : Region.t columns (Cell.t columns * Cell.t columns) :=
  let_ℛ _ := enable_selector_rows q_sinsemilla1 offset num_words in
  let_ℛ _ := assign_q_s2_rows q_sinsemilla2 offset num_words final_piece in
  let_ℛ _ :=
    Region.copy_advice
      "z_0 (copy of message piece)"
      piece
      bits
      offset
      Value.Unknown in
  let_ℛ z1 :=
    Region.assign_advice "z_1" bits (offset + 1) Value.Unknown in
  let_ℛ _ :=
    assign_intermediate_zs
      bits
      (offset + 2)
      (Nat.pred (Nat.pred num_words)) in
  let_ℛ x :=
    assign_double_and_add_rows x_a x_p lambda_1 lambda_2 offset num_words in
  return_ℛ (x, z1).

Definition synthesize_hash_to_point_region
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    (q_sinsemilla2 fixed_y_q : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    (q_x q_y : Z)
    (a b c : Cell.t columns)
    : Region.t columns HashResult.t :=
  let_ℛ _ := Region.enable_selector q_sinsemilla4 0 "" in
  let_ℛ _ :=
    Region.assign_fixed "fixed y_q" fixed_y_q 0 (Value.Known q_y) in
  let_ℛ _ :=
    Region.assign_advice_from_constant "variable x_q" x_a 0 q_x in
  let_ℛ a_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      a
      0
      25%nat
      false in
  let '(x, z1_a) := a_result in
  let _ := x in
  let_ℛ b_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      b
      25
      2%nat
      false in
  let '(x, z1_b) := b_result in
  let _ := x in
  let_ℛ c_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      c
      27
      25%nat
      true in
  let '(x, _) := c_result in
  let_ℛ y :=
    Region.assign_advice "y_a" lambda_1 52 Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "dummy lambda2" lambda_2 52 Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "dummy x_p" x_p 52 Value.Unknown in
  return_ℛ {|
    HashResult.x := x;
    HashResult.y := y;
    HashResult.z1_a := z1_a;
    HashResult.z1_b := z1_b;
    HashResult.z1_d := z1_b;
    HashResult.z1_g := z1_b;
    HashResult.z13_a := z1_a;
    HashResult.z13_c := z1_b;
    HashResult.z13_f := z1_b;
    HashResult.z13_g := z1_b;
  |}.

Definition synthesize_hash_to_point_commit_ivk_region
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    (q_sinsemilla2 fixed_y_q : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    (q_x q_y : Z)
    (a b c d : Cell.t columns)
    : Region.t columns HashResult.t :=
  let_ℛ _ := Region.enable_selector q_sinsemilla4 0 "" in
  let_ℛ _ :=
    Region.assign_fixed "fixed y_q" fixed_y_q 0 (Value.Known q_y) in
  let_ℛ _ :=
    Region.assign_advice_from_constant "variable x_q" x_a 0 q_x in
  let_ℛ a_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      a
      0
      25%nat
      false in
  let '(x, z1_a) := a_result in
  let_ℛ z13_a :=
    Region.assign_advice "z_13" bits 13 Value.Unknown in
  let _ := x in
  let_ℛ b_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      b
      25
      1%nat
      false in
  let '(x, z1_b) := b_result in
  let _ := x in
  let_ℛ c_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      c
      26
      24%nat
      false in
  let '(x, _) := c_result in
  let_ℛ z13_c :=
    Region.assign_advice "z_13" bits 39 Value.Unknown in
  let _ := x in
  let_ℛ d_result :=
    synthesize_hash_piece
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2
      d
      50
      1%nat
      true in
  let '(x, _) := d_result in
  let_ℛ y :=
    Region.assign_advice "y_a" lambda_1 51 Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "dummy lambda2" lambda_2 51 Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "dummy x_p" x_p 51 Value.Unknown in
  return_ℛ {|
    HashResult.x := x;
    HashResult.y := y;
    HashResult.z1_a := z1_a;
    HashResult.z1_b := z1_b;
    HashResult.z1_d := z1_b;
    HashResult.z1_g := z1_b;
    HashResult.z13_a := z13_a;
    HashResult.z13_c := z13_c;
    HashResult.z13_f := z13_c;
    HashResult.z13_g := z13_c;
  |}.

Definition synthesize_hash_to_point_1
    (q_x q_y : Z)
    (a b c : Cell.t columns)
    : Layouter.t columns HashResult.t :=
  Layouter.assign_region "hash_to_point" (
    synthesize_hash_to_point_region
      Selector.QSinsemilla1_1
      Selector.QSinsemilla4_1
      Fixed.QSinsemilla2_1
      Fixed.LagrangeCoeffs0
      Advice.A0
      Advice.A1
      Advice.A2
      Advice.A3
      Advice.A4
      q_x
      q_y
      a
      b
      c).

Definition synthesize_hash_to_point_2
    (q_x q_y : Z)
    (a b c : Cell.t columns)
    : Layouter.t columns HashResult.t :=
  Layouter.assign_region "hash_to_point" (
    synthesize_hash_to_point_region
      Selector.QSinsemilla1_2
      Selector.QSinsemilla4_2
      Fixed.QSinsemilla2_2
      Fixed.LagrangeCoeffs1
      Advice.A5
      Advice.A6
      Advice.A7
      Advice.A8
      Advice.A9
      q_x
      q_y
      a
      b
      c).

Definition synthesize_hash_to_point_commit_ivk
    (q_x q_y : Z)
    (a b c d : Cell.t columns)
    : Layouter.t columns HashResult.t :=
  Layouter.assign_region "hash_to_point" (
    synthesize_hash_to_point_commit_ivk_region
      Selector.QSinsemilla1_1
      Selector.QSinsemilla4_1
      Fixed.QSinsemilla2_1
      Fixed.LagrangeCoeffs0
      Advice.A0
      Advice.A1
      Advice.A2
      Advice.A3
      Advice.A4
      q_x
      q_y
      a
      b
      c
      d).

Definition synthesize_hash_to_point_note_commit_region
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    (q_sinsemilla2 fixed_y_q : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    (q_x q_y : Z)
    (a b c d e f g h : Cell.t columns)
    : Region.t columns HashResult.t :=
  let_ℛ _ := Region.enable_selector q_sinsemilla4 0 "" in
  let_ℛ _ :=
    Region.assign_fixed "fixed y_q" fixed_y_q 0 (Value.Known q_y) in
  let_ℛ _ :=
    Region.assign_advice_from_constant "variable x_q" x_a 0 q_x in
  let_ℛ a_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      a 0 25%nat false in
  let '(x, z1_a) := a_result in
  let_ℛ z13_a := Region.assign_advice "z_13" bits 13 Value.Unknown in
  let _ := x in
  let_ℛ b_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      b 25 1%nat false in
  let '(x, z1_b) := b_result in
  let _ := x in
  let_ℛ c_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      c 26 25%nat false in
  let '(x, _) := c_result in
  let_ℛ z13_c := Region.assign_advice "z_13" bits 39 Value.Unknown in
  let _ := x in
  let_ℛ d_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      d 51 6%nat false in
  let '(x, z1_d) := d_result in
  let _ := x in
  let_ℛ e_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      e 57 1%nat false in
  let '(x, _) := e_result in
  let _ := x in
  let_ℛ f_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      f 58 25%nat false in
  let '(x, _) := f_result in
  let_ℛ z13_f := Region.assign_advice "z_13" bits 71 Value.Unknown in
  let _ := x in
  let_ℛ g_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      g 83 25%nat false in
  let '(x, z1_g) := g_result in
  let_ℛ z13_g := Region.assign_advice "z_13" bits 96 Value.Unknown in
  let _ := x in
  let_ℛ h_result :=
    synthesize_hash_piece
      q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2
      h 108 1%nat true in
  let '(x, _) := h_result in
  let_ℛ y := Region.assign_advice "y_a" lambda_1 109 Value.Unknown in
  let_ℛ _ := Region.assign_advice "dummy lambda2" lambda_2 109 Value.Unknown in
  let_ℛ _ := Region.assign_advice "dummy x_p" x_p 109 Value.Unknown in
  return_ℛ {|
    HashResult.x := x;
    HashResult.y := y;
    HashResult.z1_a := z1_a;
    HashResult.z1_b := z1_b;
    HashResult.z1_d := z1_d;
    HashResult.z1_g := z1_g;
    HashResult.z13_a := z13_a;
    HashResult.z13_c := z13_c;
    HashResult.z13_f := z13_f;
    HashResult.z13_g := z13_g;
  |}.

Definition synthesize_hash_to_point_note_commit
    (q_x q_y : Z)
    (a b c d e f g h : Cell.t columns)
    : Layouter.t columns HashResult.t :=
  Layouter.assign_region "hash_to_point" (
    synthesize_hash_to_point_note_commit_region
      Selector.QSinsemilla1_1
      Selector.QSinsemilla4_1
      Fixed.QSinsemilla2_1
      Fixed.LagrangeCoeffs0
      Advice.A0
      Advice.A1
      Advice.A2
      Advice.A3
      Advice.A4
      q_x
      q_y
      a
      b
      c
      d
      e
      f
      g
      h).

Definition synthesize_hash_to_point_note_commit_2
    (q_x q_y : Z)
    (a b c d e f g h : Cell.t columns)
    : Layouter.t columns HashResult.t :=
  Layouter.assign_region "hash_to_point" (
    synthesize_hash_to_point_note_commit_region
      Selector.QSinsemilla1_2
      Selector.QSinsemilla4_2
      Fixed.QSinsemilla2_2
      Fixed.LagrangeCoeffs1
      Advice.A5
      Advice.A6
      Advice.A7
      Advice.A8
      Advice.A9
      q_x
      q_y
      a
      b
      c
      d
      e
      f
      g
      h).

Definition synthesize_instance
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    : Layouter.t columns unit :=
  let_ℒ _ :=
    Layouter.assign_region "Sinsemilla gate" (
      Region.enable_selector q_sinsemilla1 0 "") in
  Layouter.assign_region "Initial y_Q" (
    Region.enable_selector q_sinsemilla4 0 "").

Definition synthesize_1
    : Layouter.t columns unit :=
  synthesize_instance Selector.QSinsemilla1_1 Selector.QSinsemilla4_1.

Definition synthesize_2
    : Layouter.t columns unit :=
  synthesize_instance Selector.QSinsemilla1_2 Selector.QSinsemilla4_2.
