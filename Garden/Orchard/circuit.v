Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Halo2.Gadgets.LookupRangeCheck.
Require Garden.Halo2.Gadgets.Ecc.chip.
Require Garden.Halo2.Gadgets.Poseidon.Pow5.
Require Garden.Halo2.Gadgets.Sinsemilla.chip.
Require Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.FixedBases.NullifierK.
Require Garden.Orchard.FixedBases.SpendAuthG.
Require Garden.Orchard.FixedBases.ValueCommitR.
Require Garden.Orchard.FixedBases.ValueCommitV.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.circuit.gadget.add_chip.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit_synthesis_constants.
Require Garden.Orchard.circuit_synthesis_layout.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition ANCHOR : Z := 0.
Definition CV_NET_X : Z := 1.
Definition CV_NET_Y : Z := 2.
Definition NF_OLD : Z := 3.
Definition RK_X : Z := 4.
Definition RK_Y : Z := 5.
Definition CMX : Z := 6.
Definition ENABLE_SPEND : Z := 7.
Definition ENABLE_OUTPUT : Z := 8.

Module AssignedPoint.
  Record t : Set := {
    x : Cell.t columns;
    y : Cell.t columns;
  }.
End AssignedPoint.

Module ShortFixedResult.
  Record t : Set := {
    acc : AssignedPoint.t;
    mul_b : AssignedPoint.t;
    last_window : Cell.t columns;
  }.
End ShortFixedResult.

Module FullFixedResult.
  Record t : Set := {
    acc : AssignedPoint.t;
    mul_b : AssignedPoint.t;
  }.
End FullFixedResult.

Module BaseFieldFixedResult.
  Record t : Set := {
    acc : AssignedPoint.t;
    mul_b : AssignedPoint.t;
    alpha : Cell.t columns;
    z_43_alpha : Cell.t columns;
    z_44_alpha : Cell.t columns;
    z_84_alpha : Cell.t columns;
  }.
End BaseFieldFixedResult.

Module LookupResult.
  Record t : Set := {
    z_0 : Cell.t columns;
    z_13 : Cell.t columns;
  }.
End LookupResult.

Module AssignedPair.
  Record t : Set := {
    left : Cell.t columns;
    right : Cell.t columns;
  }.
End AssignedPair.

Fixpoint emit_raw_events
    (events : list Raw.Event.t)
    : Layouter.t columns unit :=
  match events with
  | [] => return_ℒ tt
  | event :: events =>
      let_ℒ _ := Layouter.emit event in
      emit_raw_events events
  end.

Definition merkle_q_x : Z :=
  9991206725476878888751475603038274618448000607209514551456795194094072219296.

Definition merkle_q_y : Z :=
  24209798415301550423396126020228723009317736024280831393239261884225294625378.

Definition merkle_crh_name (layer : Z) : string :=
  match layer with
  | 0 => "MerkleCRH(0, left, right)"
  | 1 => "MerkleCRH(1, left, right)"
  | 2 => "MerkleCRH(2, left, right)"
  | 3 => "MerkleCRH(3, left, right)"
  | 4 => "MerkleCRH(4, left, right)"
  | 5 => "MerkleCRH(5, left, right)"
  | 6 => "MerkleCRH(6, left, right)"
  | 7 => "MerkleCRH(7, left, right)"
  | 8 => "MerkleCRH(8, left, right)"
  | 9 => "MerkleCRH(9, left, right)"
  | 10 => "MerkleCRH(10, left, right)"
  | 11 => "MerkleCRH(11, left, right)"
  | 12 => "MerkleCRH(12, left, right)"
  | 13 => "MerkleCRH(13, left, right)"
  | 14 => "MerkleCRH(14, left, right)"
  | 15 => "MerkleCRH(15, left, right)"
  | 16 => "MerkleCRH(16, left, right)"
  | 17 => "MerkleCRH(17, left, right)"
  | 18 => "MerkleCRH(18, left, right)"
  | 19 => "MerkleCRH(19, left, right)"
  | 20 => "MerkleCRH(20, left, right)"
  | 21 => "MerkleCRH(21, left, right)"
  | 22 => "MerkleCRH(22, left, right)"
  | 23 => "MerkleCRH(23, left, right)"
  | 24 => "MerkleCRH(24, left, right)"
  | 25 => "MerkleCRH(25, left, right)"
  | 26 => "MerkleCRH(26, left, right)"
  | 27 => "MerkleCRH(27, left, right)"
  | 28 => "MerkleCRH(28, left, right)"
  | 29 => "MerkleCRH(29, left, right)"
  | 30 => "MerkleCRH(30, left, right)"
  | 31 => "MerkleCRH(31, left, right)"
  | _ => "MerkleCRH(?, left, right)"
  end.

Definition hash_at_l_name (layer : Z) : string :=
  match layer with
  | 0 => "hash at l = 0"
  | 1 => "hash at l = 1"
  | 2 => "hash at l = 2"
  | 3 => "hash at l = 3"
  | 4 => "hash at l = 4"
  | 5 => "hash at l = 5"
  | 6 => "hash at l = 6"
  | 7 => "hash at l = 7"
  | 8 => "hash at l = 8"
  | 9 => "hash at l = 9"
  | 10 => "hash at l = 10"
  | 11 => "hash at l = 11"
  | 12 => "hash at l = 12"
  | 13 => "hash at l = 13"
  | 14 => "hash at l = 14"
  | 15 => "hash at l = 15"
  | 16 => "hash at l = 16"
  | 17 => "hash at l = 17"
  | 18 => "hash at l = 18"
  | 19 => "hash at l = 19"
  | 20 => "hash at l = 20"
  | 21 => "hash at l = 21"
  | 22 => "hash at l = 22"
  | 23 => "hash at l = 23"
  | 24 => "hash at l = 24"
  | 25 => "hash at l = 25"
  | 26 => "hash at l = 26"
  | 27 => "hash at l = 27"
  | 28 => "hash at l = 28"
  | 29 => "hash at l = 29"
  | 30 => "hash at l = 30"
  | 31 => "hash at l = 31"
  | _ => "hash at l = ?"
  end.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Orchard circuit checks";
    Gate.constraints :=
      let v_old := Expression.Advice Advice.A0 Rotation.cur in
      let v_new := Expression.Advice Advice.A1 Rotation.cur in
      let magnitude := Expression.Advice Advice.A2 Rotation.cur in
      let sign := Expression.Advice Advice.A3 Rotation.cur in
      let root := Expression.Advice Advice.A4 Rotation.cur in
      let anchor := Expression.Advice Advice.A5 Rotation.cur in
      let enable_spends := Expression.Advice Advice.A6 Rotation.cur in
      let enable_outputs := Expression.Advice Advice.A7 Rotation.cur in
      Constraints.with_selector Selector.QOrchard [
        (Some "v_old - v_new = magnitude * sign",
          Constraint.EqualZeroToPrecise
            (v_old ➖ v_new ➖ (magnitude ✖️ sign)));
        (Some "Either v_old = 0, or root = anchor",
          Constraint.EqualZeroToPrecise (v_old ✖️ (root ➖ anchor)));
        (Some "v_old = 0 or enable_spends = 1",
          Constraint.EqualZeroToPrecise
            (v_old ✖️ (Expression.Constant 1 ➖ enable_spends)));
        (Some "v_new = 0 or enable_outputs = 1",
          Constraint.EqualZeroToPrecise
            (v_new ✖️ (Expression.Constant 1 ➖ enable_outputs)))
      ];
  |} in
  let meta :=
    Garden.Orchard.circuit.gadget.add_chip.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.LookupRangeCheck.configure
      10
      meta
      Selector.QLookup
      Selector.QRunning
      Selector.QBitshift
      Advice.A9
      (Fixed.Lookup Lookup.TableIdx) in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Poseidon.Pow5.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.chip.configure_1
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.configure_1
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.chip.configure_2
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.configure_2
      meta in
  let meta :=
    Garden.Orchard.circuit.commit_ivk.configure
      meta in
  let meta :=
    Garden.Orchard.circuit.note_commit.configure_old
      meta in
  let meta :=
    Garden.Orchard.circuit.note_commit.configure_new
      meta in
  meta.

Definition synthesize_range_check
    : Layouter.t columns unit :=
  Garden.Halo2.Gadgets.LookupRangeCheck.synthesize.

Definition assign_free_advice
    (name : string)
    (column : Advice.t)
    (value : Value.t)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace name (
    Layouter.assign_region "load private" (
      Region.assign_advice "load private" column 0 value)).

Definition witness_point_region
    (selector : Selector.t)
    : Region.t columns AssignedPoint.t :=
  let_ℛ x := Region.assign_advice "x" Advice.A0 0 Value.Unknown in
  let_ℛ y := Region.assign_advice "y" Advice.A1 0 Value.Unknown in
  let_ℛ _ := Region.enable_selector selector 0 "" in
  return_ℛ {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition witness_point
    (name : string)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.namespace name (
    Layouter.assign_region "witness point" (
      witness_point_region Selector.QWitnessPoint)).

Definition witness_non_identity_point
    (name : string)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.namespace name (
    Layouter.assign_region "witness non-identity point" (
      witness_point_region Selector.QWitnessPointNonId)).

Definition witness_message_piece
    (name : string)
    (witness_pieces : Advice.t)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace name (
    Layouter.assign_region "witness message piece" (
      Region.assign_advice
        "witness message piece" witness_pieces 0 Value.Unknown)).

Definition synthesize_witness_inputs
    : Layouter.t columns
        (Cell.t columns
          * Cell.t columns
          * AssignedPoint.t
          * AssignedPoint.t
          * AssignedPoint.t
          * Cell.t columns
          * Cell.t columns
          * Cell.t columns) :=
  let_ℒ psi_old :=
    assign_free_advice "witness psi_old" Advice.A0 Value.Unknown in
  let_ℒ rho_old :=
    assign_free_advice "witness rho_old" Advice.A0 Value.Unknown in
  let_ℒ cm_old := witness_point "cm_old" in
  let_ℒ g_d_old := witness_non_identity_point "gd_old" in
  let_ℒ ak_P := witness_non_identity_point "witness ak_P" in
  let_ℒ nk :=
    assign_free_advice "witness nk" Advice.A0 Value.Unknown in
  let_ℒ v_old :=
    assign_free_advice "witness v_old" Advice.A0 Value.Unknown in
  let_ℒ v_new :=
    assign_free_advice "witness v_new" Advice.A0 Value.Unknown in
  return_ℒ (psi_old, rho_old, cm_old, g_d_old, ak_P, nk, v_old, v_new).

Definition synthesize_node_position_instance
    (q_swap : Selector.t)
    (a b a_swapped b_swapped swap : Advice.t)
    (leaf : Cell.t columns)
    : Layouter.t columns AssignedPair.t :=
  Layouter.namespace "node position" (
    Layouter.assign_region "swap" (
      let_ℛ _ := Region.enable_selector q_swap 0 "" in
      let_ℛ _ :=
        Region.copy_advice "load private" leaf a 0 Value.Unknown in
      let_ℛ _ := Region.assign_advice "sibling" b 0 Value.Unknown in
      let_ℛ left :=
        Region.assign_advice "left" a_swapped 0 Value.Unknown in
      let_ℛ right :=
        Region.assign_advice "right" b_swapped 0 Value.Unknown in
      let_ℛ _ := Region.assign_advice "swap" swap 0 Value.Unknown in
      return_ℛ {| AssignedPair.left := left; AssignedPair.right := right |})).

Definition synthesize_node_position_1
    (leaf : Cell.t columns)
    : Layouter.t columns AssignedPair.t :=
  synthesize_node_position_instance
    Selector.QCondSwap1
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4
    leaf.

Definition synthesize_node_position_2
    (leaf : Cell.t columns)
    : Layouter.t columns AssignedPair.t :=
  synthesize_node_position_instance
    Selector.QCondSwap2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9
    leaf.

Definition synthesize_merkle_decomposition_instance
    (q_decompose : Selector.t)
    (a_col b_col c_col left_col right_col : Advice.t)
    (layer : Z)
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns)
    : Layouter.t columns unit :=
  Layouter.assign_region "Check piece decomposition" (
    let_ℛ _ := Region.enable_selector q_decompose 0 "" in
    let_ℛ _ :=
      Region.assign_advice_from_constant "l" right_col 1 layer in
    let_ℛ _ := Region.copy_advice "copy a" a a_col 0 Value.Unknown in
    let_ℛ _ := Region.copy_advice "copy b" b b_col 0 Value.Unknown in
    let_ℛ _ := Region.copy_advice "copy c" c c_col 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "copy left" left left_col 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "copy right" right right_col 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "copy z1_a" z1_a a_col 1 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "copy z1_b" z1_b b_col 1 Value.Unknown in
    let_ℛ _ := Region.copy_advice "copy b_1" b1 c_col 1 Value.Unknown in
    let_ℛ _ := Region.copy_advice "copy b_2" b2 left_col 1 Value.Unknown in
    return_ℛ tt).

Definition synthesize_merkle_decomposition_1
    (layer : Z)
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns)
    : Layouter.t columns unit :=
  synthesize_merkle_decomposition_instance
    Selector.QMerkleDecompose1
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4
    layer
    a
    b
    c
    left
    right
    b1
    b2
    z1_a
    z1_b.

Definition synthesize_merkle_decomposition_2
    (layer : Z)
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns)
    : Layouter.t columns unit :=
  synthesize_merkle_decomposition_instance
    Selector.QMerkleDecompose2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9
    layer
    a
    b
    c
    left
    right
    b1
    b2
    z1_a
    z1_b.

Definition synthesize_merkle_hash_layer_1
    (layer : Z)
    (pair : AssignedPair.t)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace (merkle_crh_name layer) (
    let_ℒ a :=
      witness_message_piece "Witness a = a_0 || a_1" Advice.A6 in
    let_ℒ b1 :=
      Layouter.namespace "b_1" (
        Garden.Halo2.Gadgets.LookupRangeCheck.synthesize_short
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9) in
    let_ℒ b2 :=
      Layouter.namespace "b_2" (
        Garden.Halo2.Gadgets.LookupRangeCheck.synthesize_short
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9) in
    let_ℒ b :=
      witness_message_piece "Witness b = b_0 || b_1 || b_2" Advice.A6 in
    let_ℒ c := witness_message_piece "Witness c" Advice.A6 in
    let_ℒ hash :=
      Layouter.namespace (hash_at_l_name layer) (
        Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_1
          merkle_q_x
          merkle_q_y
          a
          b
          c) in
    let_ℒ _ :=
      synthesize_merkle_decomposition_1
        layer
        a
        b
        c
        pair.(AssignedPair.left)
        pair.(AssignedPair.right)
        b1
        b2
        hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_a)
        hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_b) in
    return_ℒ hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.x)).

Definition synthesize_merkle_hash_layer_2
    (layer : Z)
    (pair : AssignedPair.t)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace (merkle_crh_name layer) (
    let_ℒ a :=
      witness_message_piece "Witness a = a_0 || a_1" Advice.A7 in
    let_ℒ b1 :=
      Layouter.namespace "b_1" (
        Garden.Halo2.Gadgets.LookupRangeCheck.synthesize_short
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9) in
    let_ℒ b2 :=
      Layouter.namespace "b_2" (
        Garden.Halo2.Gadgets.LookupRangeCheck.synthesize_short
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9) in
    let_ℒ b :=
      witness_message_piece "Witness b = b_0 || b_1 || b_2" Advice.A7 in
    let_ℒ c := witness_message_piece "Witness c" Advice.A7 in
    let_ℒ hash :=
      Layouter.namespace (hash_at_l_name layer) (
        Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_2
          merkle_q_x
          merkle_q_y
          a
          b
          c) in
    let_ℒ _ :=
      synthesize_merkle_decomposition_2
        layer
        a
        b
        c
        pair.(AssignedPair.left)
        pair.(AssignedPair.right)
        b1
        b2
        hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_a)
        hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_b) in
    return_ℒ hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.x)).

Definition synthesize_merkle_layer
    (layer : Z)
    (node : Cell.t columns)
    : Layouter.t columns (Cell.t columns) :=
  if layer <? 16
  then
    let_ℒ pair := synthesize_node_position_1 node in
    synthesize_merkle_hash_layer_1 layer pair
  else
    let_ℒ pair := synthesize_node_position_2 node in
    synthesize_merkle_hash_layer_2 layer pair.

Fixpoint synthesize_merkle_layers
    (fuel : nat)
    (layer : Z)
    (node : Cell.t columns)
    : Layouter.t columns (Cell.t columns) :=
  match fuel with
  | O => return_ℒ node
  | S fuel =>
      let_ℒ node := synthesize_merkle_layer layer node in
      synthesize_merkle_layers fuel (layer + 1) node
  end.

Definition synthesize_merkle_path
    (leaf : Cell.t columns)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace "Merkle path" (
    synthesize_merkle_layers 32%nat 0 leaf).

Fixpoint enable_mul_fixed_running_sum_rows
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ :=
        Region.enable_selector Selector.QMulFixedRunningSum offset "" in
      enable_mul_fixed_running_sum_rows (offset + 1) count
  end.

Definition fixed_base_row : Set :=
  list (Fixed.t * string * Z).

Fixpoint assign_fixed_row
    (offset : Z)
    (row : fixed_base_row)
    : Region.t columns unit :=
  match row with
  | [] => return_ℛ tt
  | (column, annotation, value) :: row =>
      let_ℛ _ :=
        Region.assign_fixed annotation column offset (Value.Known value) in
      assign_fixed_row offset row
  end.

Fixpoint assign_fixed_rows_with_selector
    (selector : Selector.t)
    (offset : Z)
    (rows : list fixed_base_row)
    : Region.t columns unit :=
  match rows with
  | [] => return_ℛ tt
  | row :: rows =>
      let_ℛ _ :=
        Region.enable_selector selector offset "" in
      let_ℛ _ :=
        assign_fixed_row offset row in
      assign_fixed_rows_with_selector selector (offset + 1) rows
  end.

Definition assign_mul_fixed_window
    (offset : Z)
    : Region.t columns AssignedPoint.t :=
  let_ℛ x :=
    Region.assign_advice "mul_b_x" Advice.A0 offset Value.Unknown in
  let_ℛ y :=
    Region.assign_advice "mul_b_y" Advice.A1 offset Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "u" Advice.A5 offset Value.Unknown in
  return_ℛ {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition assign_add_incomplete
    (offset : Z)
    (p q : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  let_ℛ _ := Region.enable_selector Selector.QAddIncomplete offset "" in
  let_ℛ _ :=
    Region.copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 offset Value.Unknown in
  let_ℛ x_r :=
    Region.assign_advice "x_r" Advice.A2 (offset + 1) Value.Unknown in
  let_ℛ y_r :=
    Region.assign_advice "y_r" Advice.A3 (offset + 1) Value.Unknown in
  return_ℛ {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Fixpoint assign_incomplete_additions
    (offset : Z)
    (count : nat)
    (acc : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  match count with
  | O => return_ℛ acc
  | S count =>
      let_ℛ mul_b := assign_mul_fixed_window offset in
      let_ℛ acc := assign_add_incomplete offset mul_b acc in
      assign_incomplete_additions (offset + 1) count acc
  end.

Definition synthesize_short_fixed_base_mul_incomplete_region
    (magnitude : Cell.t columns)
    : Layouter.t columns ShortFixedResult.t :=
  Layouter.assign_region "Short fixed-base mul (incomplete addition)" (
    let_ℛ _ :=
      Region.copy_advice "z_0" magnitude Advice.A4 0 Value.Unknown in
    let_ℛ last_window :=
      Region.assign_advice "z_21" Advice.A4 21 Value.Unknown in
    let_ℛ _ := enable_mul_fixed_running_sum_rows 0 22%nat in
    let_ℛ _ :=
      assign_fixed_rows_with_selector
        Selector.QMulFixedRunningSum
        0
        Garden.Orchard.FixedBases.ValueCommitV.short_fixed_rows in
    let_ℛ acc := assign_mul_fixed_window 0 in
    let_ℛ acc := assign_incomplete_additions 1 20%nat acc in
    let_ℛ mul_b := assign_mul_fixed_window 21 in
    return_ℛ {|
      ShortFixedResult.acc := acc;
      ShortFixedResult.mul_b := mul_b;
      ShortFixedResult.last_window := last_window;
    |}).

Definition assign_complete_add
    (p q : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 0 "" in
  let_ℛ _ :=
    Region.copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "alpha" Advice.A5 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "beta" Advice.A6 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "gamma" Advice.A7 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "delta" Advice.A8 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "lambda" Advice.A4 0 Value.Unknown in
  let_ℛ x_r := Region.assign_advice "x_r" Advice.A2 1 Value.Unknown in
  let_ℛ y_r := Region.assign_advice "y_r" Advice.A3 1 Value.Unknown in
  return_ℛ {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Definition synthesize_short_fixed_base_mul_msb_region
    (sign last_window : Cell.t columns)
    (acc mul_b : AssignedPoint.t)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.assign_region "Short fixed-base mul (most significant word)" (
    let_ℛ magnitude_mul := assign_complete_add mul_b acc in
    let_ℛ _ :=
      Region.copy_advice "sign" sign Advice.A4 1 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "last_window" last_window Advice.A5 1 Value.Unknown in
    let_ℛ _ := Region.enable_selector Selector.QMulFixedShort 1 "" in
    let_ℛ y_var :=
      Region.assign_advice "y_var" Advice.A1 1 Value.Unknown in
    return_ℛ {|
      AssignedPoint.x := magnitude_mul.(AssignedPoint.x);
      AssignedPoint.y := y_var;
    |}).

Definition synthesize_short_fixed_base_mul
    (magnitude sign : Cell.t columns)
    : Layouter.t columns AssignedPoint.t :=
  let_ℒ result :=
    synthesize_short_fixed_base_mul_incomplete_region magnitude in
  synthesize_short_fixed_base_mul_msb_region
    sign
    result.(ShortFixedResult.last_window)
    result.(ShortFixedResult.acc)
    result.(ShortFixedResult.mul_b).

Fixpoint assign_full_window_witnesses
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ :=
        Region.enable_selector Selector.QMulFixedFull offset "" in
      let_ℛ _ :=
        Region.assign_advice "k" Advice.A4 offset Value.Unknown in
      assign_full_window_witnesses (offset + 1) count
  end.

Definition synthesize_full_fixed_base_mul_incomplete_region_with_rows
    (rows : list fixed_base_row)
    : Layouter.t columns FullFixedResult.t :=
  Layouter.assign_region "Full-width fixed-base mul (incomplete addition)" (
    let_ℛ _ := assign_full_window_witnesses 0 85%nat in
    let_ℛ _ :=
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        rows in
    let_ℛ acc := assign_mul_fixed_window 0 in
    let_ℛ acc := assign_incomplete_additions 1 83%nat acc in
    let_ℛ mul_b := assign_mul_fixed_window 84 in
    return_ℛ {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_last_region
    (result : FullFixedResult.t)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.assign_region "Full-width fixed-base mul (last window, complete addition)" (
    assign_complete_add
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synthesize_full_fixed_base_mul_value_commit_r
    : Layouter.t columns AssignedPoint.t :=
  let_ℒ result :=
    synthesize_full_fixed_base_mul_incomplete_region_with_rows
      Garden.Orchard.FixedBases.ValueCommitR.full_fixed_rows in
  synthesize_full_fixed_base_mul_last_region result.

Definition synthesize_full_fixed_base_mul_spend_auth_g
    : Layouter.t columns AssignedPoint.t :=
  let_ℒ result :=
    synthesize_full_fixed_base_mul_incomplete_region_with_rows
      Garden.Orchard.FixedBases.SpendAuthG.full_fixed_rows in
  synthesize_full_fixed_base_mul_last_region result.

Definition synthesize_complete_point_add
    (name : string)
    (p q : AssignedPoint.t)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.namespace name (
    Layouter.assign_region "complete point addition" (
      assign_complete_add p q)).

Definition synthesize_base_field_fixed_base_mul_incomplete_region
    (scalar : Cell.t columns)
    : Layouter.t columns BaseFieldFixedResult.t :=
  Layouter.assign_region
    "Base-field elem fixed-base mul (incomplete addition)"
    (
      let_ℛ alpha :=
        Region.copy_advice
          "z_0" scalar Advice.A4 0 Value.Unknown in
      let_ℛ z_43_alpha :=
        Region.assign_advice "z_43_alpha" Advice.A4 43 Value.Unknown in
      let_ℛ z_44_alpha :=
        Region.assign_advice "z_44_alpha" Advice.A4 44 Value.Unknown in
      let_ℛ z_84_alpha :=
        Region.assign_advice "z_84_alpha" Advice.A4 84 Value.Unknown in
      let_ℛ _ := enable_mul_fixed_running_sum_rows 0 85%nat in
      let_ℛ _ :=
        assign_fixed_rows_with_selector
          Selector.QMulFixedRunningSum
          0
          Garden.Orchard.FixedBases.NullifierK.base_field_fixed_rows in
      let_ℛ acc := assign_mul_fixed_window 0 in
      let_ℛ acc := assign_incomplete_additions 1 83%nat acc in
      let_ℛ mul_b := assign_mul_fixed_window 84 in
      return_ℛ {|
        BaseFieldFixedResult.acc := acc;
        BaseFieldFixedResult.mul_b := mul_b;
        BaseFieldFixedResult.alpha := alpha;
        BaseFieldFixedResult.z_43_alpha := z_43_alpha;
        BaseFieldFixedResult.z_44_alpha := z_44_alpha;
        BaseFieldFixedResult.z_84_alpha := z_84_alpha;
      |}).

Definition synthesize_base_field_fixed_base_mul_complete_region
    (result : BaseFieldFixedResult.t)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.assign_region "Base-field elem fixed-base mul (complete addition)" (
    assign_complete_add
      result.(BaseFieldFixedResult.mul_b)
      result.(BaseFieldFixedResult.acc)).

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ := Region.enable_selector Selector.QLookup offset "" in
      let_ℛ _ := Region.enable_selector Selector.QRunning offset "" in
      let_ℛ _ :=
        Region.assign_advice "z" Advice.A9 offset Value.Unknown in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition synthesize_alpha_lookup
    : Layouter.t columns LookupResult.t :=
  Layouter.namespace "Lookup range check alpha_0 + 2^130 - t_p" (
    Layouter.assign_region "Witness element" (
      let_ℛ z_0 :=
        Region.assign_advice "z_0" Advice.A9 0 Value.Unknown in
      let_ℛ _ := enable_lookup_running_rows 0 13%nat in
      let_ℛ z_13 :=
        Region.assign_advice "z_13" Advice.A9 13 Value.Unknown in
      return_ℛ {|
        LookupResult.z_0 := z_0;
        LookupResult.z_13 := z_13;
      |})).

Definition synthesize_canonicity_checks
    (result : BaseFieldFixedResult.t)
    (lookup : LookupResult.t)
    : Layouter.t columns unit :=
  Layouter.assign_region "Canonicity checks" (
    let_ℛ _ := Region.enable_selector Selector.QMulFixedBaseField 1 "" in
    let_ℛ _ :=
      Region.copy_advice
        "Copy alpha"
        result.(BaseFieldFixedResult.alpha)
        Advice.A6
        0
        Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "Copy z_84_alpha"
        result.(BaseFieldFixedResult.z_84_alpha)
        Advice.A8
        0
        Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "Copy alpha_0_prime"
        lookup.(LookupResult.z_0)
        Advice.A6
        1
        Value.Unknown in
    let_ℛ _ :=
      Region.assign_advice "alpha_1" Advice.A7 1 Value.Unknown in
    let_ℛ _ :=
      Region.assign_advice "alpha_2" Advice.A8 1 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "Copy z_13_alpha_0_prime"
        lookup.(LookupResult.z_13)
        Advice.A6
        2
        Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "Copy z_44_alpha"
        result.(BaseFieldFixedResult.z_44_alpha)
        Advice.A7
        2
        Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "Copy z_43_alpha"
        result.(BaseFieldFixedResult.z_43_alpha)
        Advice.A8
        2
        Value.Unknown in
    return_ℛ tt).

Definition synthesize_base_field_fixed_base_mul_nullifier_k
    (scalar : Cell.t columns)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.namespace "base-field elem fixed-base mul of NullifierK" (
    let_ℒ result :=
      synthesize_base_field_fixed_base_mul_incomplete_region scalar in
    let_ℒ product :=
      synthesize_base_field_fixed_base_mul_complete_region result in
    let_ℒ lookup := synthesize_alpha_lookup in
    let_ℒ _ := synthesize_canonicity_checks result lookup in
    return_ℒ product).

Definition synthesize_value_commit_orchard
    (magnitude sign : Cell.t columns)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.namespace "cv_net = ValueCommit^Orchard_rcv(v_net)" (
    let_ℒ value_commit_v :=
      Layouter.namespace "[v] ValueCommitV" (
        Layouter.namespace "short fixed-base mul of ValueCommitV" (
          synthesize_short_fixed_base_mul magnitude sign)) in
    let_ℒ blind :=
      Layouter.namespace "[rcv] ValueCommitR" (
        Layouter.namespace "fixed-base mul of ValueCommitR" (
          synthesize_full_fixed_base_mul_value_commit_r)) in
    synthesize_complete_point_add "cv" value_commit_v blind).

Definition synthesize_value_commitment
    : Layouter.t columns (Cell.t columns * Cell.t columns) :=
  let_ℒ magnitude :=
    assign_free_advice "v_net magnitude" Advice.A9 Value.Unknown in
  let_ℒ sign :=
    assign_free_advice "v_net sign" Advice.A9 Value.Unknown in
  let_ℒ _ :=
    Layouter.namespace "v_net" (return_ℒ tt) in
  let_ℒ _ :=
    Layouter.namespace "rcv" (return_ℒ tt) in
  let_ℒ cv_net :=
    synthesize_value_commit_orchard magnitude sign in
  let_ℒ _ :=
    Layouter.constrain_instance cv_net.(AssignedPoint.x) Instance_.Primary CV_NET_X in
  let_ℒ _ :=
    Layouter.constrain_instance cv_net.(AssignedPoint.y) Instance_.Primary CV_NET_Y in
  return_ℒ (magnitude, sign).

Definition synthesize_scalar_add
    (name : string)
    (a b : Cell.t columns)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace name (
    Layouter.assign_region "c = a + b" (
      let_ℛ _ := Region.enable_selector Selector.QAdd 0 "" in
      let_ℛ _ :=
        Region.copy_advice "a" a Advice.A7 0 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice "b" b Advice.A8 0 Value.Unknown in
      Region.assign_advice "c" Advice.A6 0 Value.Unknown)).

Definition synthesize_nullifier
    (rho psi nk : Cell.t columns)
    (cm : AssignedPoint.t)
    : Layouter.t columns (Cell.t columns) :=
  let_ℒ nf_old :=
    Layouter.namespace "nf_old = DeriveNullifier_nk(rho_old, psi_old, cm_old)" (
      let_ℒ poseidon_output :=
        Garden.Halo2.Gadgets.Poseidon.Pow5.synthesize_hash nk rho in
      let_ℒ scalar :=
        synthesize_scalar_add
          "scalar = poseidon_hash(nk, rho) + psi"
          poseidon_output
          psi in
      let_ℒ product :=
        Layouter.namespace "[poseidon_output + psi] NullifierK" (
          synthesize_base_field_fixed_base_mul_nullifier_k scalar) in
      let_ℒ nf := synthesize_complete_point_add "nf" cm product in
      return_ℒ nf.(AssignedPoint.x)) in
  let_ℒ _ :=
    Layouter.constrain_instance nf_old Instance_.Primary NF_OLD in
  return_ℒ nf_old.

Definition synthesize_spend_authority
    (ak_P : AssignedPoint.t)
    : Layouter.t columns unit :=
  let_ℒ _ :=
    Layouter.namespace "alpha" (return_ℒ tt) in
  let_ℒ alpha_commitment :=
    Layouter.namespace "[alpha] SpendAuthG" (
      Layouter.namespace "fixed-base mul of SpendAuthG" (
        synthesize_full_fixed_base_mul_spend_auth_g)) in
  let_ℒ rk := synthesize_complete_point_add "rk" alpha_commitment ak_P in
  let_ℒ _ :=
    Layouter.constrain_instance rk.(AssignedPoint.x) Instance_.Primary RK_X in
  Layouter.constrain_instance rk.(AssignedPoint.y) Instance_.Primary RK_Y.

Definition synthesize_address_integrity
    (ak nk : Cell.t columns)
    (g_d_old : AssignedPoint.t)
    : Layouter.t columns AssignedPoint.t :=
  let_ℒ _ :=
    Layouter.namespace "rivk" (return_ℒ tt) in
  let_ℒ _ :=
    Layouter.namespace "CommitIvk" (
      Garden.Orchard.circuit.commit_ivk.synthesize ak nk) in
  let_ℒ _ :=
    Layouter.namespace "ivk" (return_ℒ tt) in
  let_ℒ pk_d_calculated :=
    Layouter.namespace "[ivk] g_d_old" (
      Garden.Halo2.Gadgets.Ecc.chip.mul.synthesize
        g_d_old.(AssignedPoint.x)
        g_d_old.(AssignedPoint.y)) in
  let_ℒ pk_d_old := witness_non_identity_point "witness pk_d_old" in
  let_ℒ _ :=
    Layouter.namespace "pk_d_old equality" (
      Layouter.assign_region "constrain equal" (
        let_ℛ _ :=
          Region.copy
            pk_d_calculated.(Garden.Halo2.Gadgets.Ecc.chip.mul.MulResult.x)
            pk_d_old.(AssignedPoint.x) in
        let_ℛ _ :=
          Region.copy
            pk_d_calculated.(Garden.Halo2.Gadgets.Ecc.chip.mul.MulResult.y)
            pk_d_old.(AssignedPoint.y) in
        return_ℛ tt)) in
  return_ℒ pk_d_old.

Definition synthesize_note_commit_old
    (g_d_old pk_d_old : AssignedPoint.t)
    (v_old rho_old psi_old : Cell.t columns)
    (cm_old : AssignedPoint.t)
    : Layouter.t columns unit :=
  let_ℒ _ :=
    Layouter.namespace "rcm_old" (return_ℒ tt) in
  let_ℒ cm :=
    Layouter.namespace
      "g★_d || pk★_d || i2lebsp_{64}(v) || i2lebsp_{255}(rho) || i2lebsp_{255}(psi)"
      (Garden.Orchard.circuit.note_commit.synthesize_old
        g_d_old.(AssignedPoint.x)
        g_d_old.(AssignedPoint.y)
        pk_d_old.(AssignedPoint.x)
        pk_d_old.(AssignedPoint.y)
        v_old
        rho_old
        psi_old) in
  Layouter.namespace "cm_old equality" (
    Layouter.assign_region "constrain equal" (
      let_ℛ _ :=
        Region.copy
          cm.(Garden.Orchard.circuit.note_commit.AssignedPoint.x)
          cm_old.(AssignedPoint.x) in
      let_ℛ _ :=
        Region.copy
          cm.(Garden.Orchard.circuit.note_commit.AssignedPoint.y)
          cm_old.(AssignedPoint.y) in
      return_ℛ tt)).

Definition synthesize_note_commit_new
    (v_new rho_new : Cell.t columns)
    : Layouter.t columns unit :=
  let_ℒ g_d_new_star := witness_non_identity_point "witness g_d_new_star" in
  let_ℒ pk_d_new := witness_non_identity_point "witness pk_d_new" in
  let_ℒ psi_new :=
    assign_free_advice "witness psi_new" Advice.A0 Value.Unknown in
  let_ℒ _ :=
    Layouter.namespace "rcm_new" (return_ℒ tt) in
  let_ℒ cm_new :=
    Layouter.namespace
      "g★_d || pk★_d || i2lebsp_{64}(v) || i2lebsp_{255}(rho) || i2lebsp_{255}(psi)"
      (Garden.Orchard.circuit.note_commit.synthesize_new
        g_d_new_star.(AssignedPoint.x)
        g_d_new_star.(AssignedPoint.y)
        pk_d_new.(AssignedPoint.x)
        pk_d_new.(AssignedPoint.y)
        v_new
        rho_new
        psi_new) in
  Layouter.constrain_instance
    cm_new.(Garden.Orchard.circuit.note_commit.AssignedPoint.x)
    Instance_.Primary
    CMX.

Definition synthesize_orchard_gate
    (v_old v_new magnitude sign root : Cell.t columns)
    : Layouter.t columns unit :=
  Layouter.assign_region "Orchard circuit checks" (
    let_ℛ _ :=
      Region.copy_advice "v_old" v_old Advice.A0 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "v_new" v_new Advice.A1 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice
        "v_net magnitude" magnitude Advice.A2 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "v_net sign" sign Advice.A3 0 Value.Unknown in
    let_ℛ _ :=
      Region.copy_advice "calculated root" root Advice.A4 0 Value.Unknown in
    let_ℛ _ :=
      Region.assign_advice_from_instance
        "pub input anchor" Instance_.Primary ANCHOR Advice.A5 0 in
    let_ℛ _ :=
      Region.assign_advice_from_instance
        "enable spends" Instance_.Primary ENABLE_SPEND Advice.A6 0 in
    let_ℛ _ :=
      Region.assign_advice_from_instance
        "enable outputs" Instance_.Primary ENABLE_OUTPUT Advice.A7 0 in
    Region.enable_selector Selector.QOrchard 0 "").

Definition synthesize
    : Layouter.t columns unit :=
  let_ℒ _ := Garden.Halo2.Gadgets.Sinsemilla.chip.load_generator_table in
  let_ℒ witnesses := synthesize_witness_inputs in
  let
    '(psi_old, rho_old, cm_old, g_d_old, ak_P, nk, v_old, v_new) :=
      witnesses in
  let_ℒ root := synthesize_merkle_path cm_old.(AssignedPoint.x) in
  let_ℒ v_net_magnitude_sign := synthesize_value_commitment in
  let '(magnitude, sign) := v_net_magnitude_sign in
  let_ℒ rho_new := synthesize_nullifier rho_old psi_old nk cm_old in
  let_ℒ _ := synthesize_spend_authority ak_P in
  let_ℒ pk_d_old := synthesize_address_integrity ak_P.(AssignedPoint.x) nk g_d_old in
  let_ℒ _ :=
    synthesize_note_commit_old
      g_d_old
      pk_d_old
      v_old
      rho_old
      psi_old
      cm_old in
  let_ℒ _ := synthesize_note_commit_new v_new rho_new in
  let_ℒ _ := synthesize_orchard_gate v_old v_new magnitude sign root in
  emit_raw_events Garden.Orchard.circuit_synthesis_constants.events.

Definition synthesize_events
    (indices : Indices.t columns)
    : list Raw.Event.t :=
  let '(_, events) :=
    V1.run_with_region_start
      indices
      Garden.Orchard.circuit_synthesis_layout.region_start_of
      synthesize in
  events.
