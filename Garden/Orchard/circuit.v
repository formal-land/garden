Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Halo2.serialize.
Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Garden.Halo2.halo2_gadgets.ecc.chip.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.poseidon.pow5.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.configure_metadata.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Garden.Orchard.constants.fixed_bases.spend_auth_g.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
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
Definition DISABLE_CROSS_ADDRESS : Z := 9.

Definition witness_input_region (region : RegionId.WitnessInput.t) : RegionId.t :=
  RegionId.WitnessInput region.

Definition merkle_region
    (layer : Z)
    (region : RegionId.Merkle.Region.t) : RegionId.t :=
  RegionId.Merkle (RegionId.Merkle.Layer.of_index layer) region.

Definition value_commitment_region
    (region : RegionId.ValueCommitment.t) : RegionId.t :=
  RegionId.ValueCommitment region.

Definition nullifier_region (region : RegionId.Nullifier.t) : RegionId.t :=
  RegionId.Nullifier region.

Definition spend_authority_region
    (region : RegionId.SpendAuthority.t) : RegionId.t :=
  RegionId.SpendAuthority region.

Definition address_integrity_region
    (region : RegionId.AddressIntegrity.t) : RegionId.t :=
  RegionId.AddressIntegrity region.

Definition address_integrity_mul_region
    (region : RegionId.AddressIntegrity.Mul.t) : RegionId.t :=
  address_integrity_region (RegionId.AddressIntegrity.Mul region).

Module AssignedPoint.
  Record t : Set := {
    x : Cell.t columns RegionId.t;
    y : Cell.t columns RegionId.t;
  }.
End AssignedPoint.

(** The four address points retained by the shared Action synthesis.  Orchard
    versions before NU6.3 did not use these cells after note commitment and
    ownership checks.  The post-NU6.3 circuit reuses them in the final
    cross-address restriction region. *)
Module AddressPoints.
  Record t : Set := {
    g_d_old : AssignedPoint.t;
    pk_d_old : AssignedPoint.t;
    g_d_new : AssignedPoint.t;
    pk_d_new : AssignedPoint.t;
  }.
End AddressPoints.

Module ShortFixedResult.
  Record t : Set := {
    acc : AssignedPoint.t;
    mul_b : AssignedPoint.t;
    last_window : Cell.t columns RegionId.t;
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
    alpha : Cell.t columns RegionId.t;
    z_43_alpha : Cell.t columns RegionId.t;
    z_44_alpha : Cell.t columns RegionId.t;
    z_84_alpha : Cell.t columns RegionId.t;
  }.
End BaseFieldFixedResult.

Module LookupResult.
  Record t : Set := {
    z_0 : Cell.t columns RegionId.t;
    z_13 : Cell.t columns RegionId.t;
  }.
End LookupResult.

Module AssignedPair.
  Record t : Set := {
    left : Cell.t columns RegionId.t;
    right : Cell.t columns RegionId.t;
  }.
End AssignedPair.

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

Definition orchard_circuit_checks_gate : Gate.t columns := {|
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
        Constraint.Equal (v_old ➖ v_new) (magnitude ✖️ sign));
      (Some "Either v_old = 0, or root = anchor",
        Constraint.Either
          (Constraint.EqualZeroToPrecise v_old)
          (Constraint.Equal root anchor));
      (Some "v_old = 0 or enable_spend = 1",
        Constraint.Either
          (Constraint.EqualZeroToPrecise v_old)
          (Constraint.Equal (Expression.Constant 1) enable_spends));
      (Some "v_new = 0 or enable_output = 1",
        Constraint.Either
          (Constraint.EqualZeroToPrecise v_new)
          (Constraint.Equal (Expression.Constant 1) enable_outputs))
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.Metadata OrchardConfigureMetadata.operations in
  do🞵 𝓒.CreateGate orchard_circuit_checks_gate in
  do🞵 Garden.Orchard.circuit.gadget.add_chip.configure in
  do🞵
    Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.configure
      10
      Selector.QLookup
      Selector.QRunning
      Selector.QBitshift
      Advice.A9
      Lookup.TableIdx in
  do🞵 Garden.Halo2.halo2_gadgets.ecc.chip.configure in
  do🞵 Garden.Halo2.halo2_gadgets.poseidon.pow5.configure in
  do🞵 Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_1 in
  do🞵 Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.configure_1 in
  do🞵 Garden.Halo2.halo2_gadgets.sinsemilla.chip.configure_2 in
  do🞵 Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.configure_2 in
  do🞵 Garden.Orchard.circuit.commit_ivk.configure in
  do🞵 Garden.Orchard.circuit.note_commit.configure_old in
  do🞵 Garden.Orchard.circuit.note_commit.configure_new in
  return🞵 tt.

Definition synthesize_range_check
    : 𝓛 columns RegionId.t unit :=
  Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.synthesize.

Definition assign_free_advice
    (region : RegionId.t)
    (name : string)
    (column : Advice.t)
    (value : Z)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "load private" (fun region =>
      return🞵 (Cell.advice region column 0))).

Definition witness_point_region
    (region : RegionId.t)
    (selector : Selector.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let x := Cell.advice region Advice.A0 0 in
  let y := Cell.advice region Advice.A1 0 in
  do🞵 𝓡.EnableSelector selector 0 "" in
  return🞵 {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition witness_point
    (region : RegionId.t)
    (name : string)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "witness point" (fun region =>
      witness_point_region region Selector.QWitnessPoint)).

Definition witness_non_identity_point
    (region : RegionId.t)
    (name : string)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "witness non-identity point" (fun region =>
      witness_point_region region Selector.QWitnessPointNonId)).

Definition witness_message_piece
    (region : RegionId.t)
    (name : string)
    (witness_pieces : Advice.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "witness message piece" (fun region =>
      return🞵 (Cell.advice region witness_pieces 0))).

Definition synthesize_witness_inputs
    : 𝓛 columns RegionId.t
        (Cell.t columns RegionId.t
          * Cell.t columns RegionId.t
          * AssignedPoint.t
          * AssignedPoint.t
          * AssignedPoint.t
          * Cell.t columns RegionId.t
          * Cell.t columns RegionId.t
          * Cell.t columns RegionId.t) :=
  let🞵 psi_old :=
    assign_free_advice
      (witness_input_region RegionId.WitnessInput.PsiOld)
      "witness psi_old"
      Advice.A0
      0 in
  let🞵 rho_old :=
    assign_free_advice
      (witness_input_region RegionId.WitnessInput.RhoOld)
      "witness rho_old"
      Advice.A0
      0 in
  let🞵 cm_old :=
    witness_point (witness_input_region RegionId.WitnessInput.CmOld) "cm_old" in
  let🞵 g_d_old :=
    witness_non_identity_point
      (witness_input_region RegionId.WitnessInput.GDOld)
      "gd_old" in
  let🞵 ak_P :=
    witness_non_identity_point
      (witness_input_region RegionId.WitnessInput.AkP)
      "witness ak_P" in
  let🞵 nk :=
    assign_free_advice
      (witness_input_region RegionId.WitnessInput.Nk)
      "witness nk"
      Advice.A0
      0 in
  let🞵 v_old :=
    assign_free_advice
      (witness_input_region RegionId.WitnessInput.VOld)
      "witness v_old"
      Advice.A0
      0 in
  let🞵 v_new :=
    assign_free_advice
      (witness_input_region RegionId.WitnessInput.VNew)
      "witness v_new"
      Advice.A0
      0 in
  return🞵 (psi_old, rho_old, cm_old, g_d_old, ak_P, nk, v_old, v_new).

Definition synthesize_node_position_instance
    (region : RegionId.t)
    (q_swap : Selector.t)
    (a b a_swapped b_swapped swap : Advice.t)
    (leaf : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPair.t :=
  𝓛.InNamespace "node position" (
    𝓛.AddRegion region "swap" (fun region =>
      do🞵 𝓡.EnableSelector q_swap 0 "" in
      let leaf_target := Cell.advice region a 0 in
      do🞵 𝓡.Copy leaf_target leaf in
      let left := Cell.advice region a_swapped 0 in
      let right := Cell.advice region b_swapped 0 in
      return🞵 {| AssignedPair.left := left; AssignedPair.right := right |})).

Definition synthesize_node_position_1
    (layer : Z)
    (leaf : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPair.t :=
  synthesize_node_position_instance
    (merkle_region layer RegionId.Merkle.Region.NodePosition)
    Selector.QCondSwap1
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4
    leaf.

Definition synthesize_node_position_2
    (layer : Z)
    (leaf : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPair.t :=
  synthesize_node_position_instance
    (merkle_region layer RegionId.Merkle.Region.NodePosition)
    Selector.QCondSwap2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9
    leaf.

Definition synthesize_merkle_decomposition_instance
    (region : RegionId.t)
    (q_decompose : Selector.t)
    (a_col b_col c_col left_col right_col : Advice.t)
    (layer : Z)
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion region "Check piece decomposition" (fun region =>
    do🞵 𝓡.EnableSelector q_decompose 0 "" in
    let a_target := Cell.advice region a_col 0 in
    do🞵 𝓡.Copy a_target a in
    let b_target := Cell.advice region b_col 0 in
    do🞵 𝓡.Copy b_target b in
    let c_target := Cell.advice region c_col 0 in
    do🞵 𝓡.Copy c_target c in
    let left_target := Cell.advice region left_col 0 in
    do🞵 𝓡.Copy left_target left in
    let right_target := Cell.advice region right_col 0 in
    do🞵 𝓡.Copy right_target right in
    let z1_a_target := Cell.advice region a_col 1 in
    do🞵 𝓡.Copy z1_a_target z1_a in
    let z1_b_target := Cell.advice region b_col 1 in
    do🞵 𝓡.Copy z1_b_target z1_b in
    let b1_target := Cell.advice region c_col 1 in
    do🞵 𝓡.Copy b1_target b1 in
    let b2_target := Cell.advice region left_col 1 in
    do🞵 𝓡.Copy b2_target b2 in
    do🞵
      𝓡.ConstrainConstant (Cell.advice region right_col 1) layer in
    return🞵 tt).

Definition synthesize_merkle_decomposition_1
    (layer : Z)
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t unit :=
  synthesize_merkle_decomposition_instance
    (merkle_region layer RegionId.Merkle.Region.Decomposition)
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
    (a b c left right b1 b2 z1_a z1_b : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t unit :=
  synthesize_merkle_decomposition_instance
    (merkle_region layer RegionId.Merkle.Region.Decomposition)
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
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace (merkle_crh_name layer) (
    let🞵 a :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessA)
        "Witness a = a_0 || a_1"
        Advice.A6 in
    let🞵 b1 :=
      𝓛.InNamespace "b_1" (
        Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.synthesize_short
          (merkle_region layer RegionId.Merkle.Region.RangeB1)
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5) in
    let🞵 b2 :=
      𝓛.InNamespace "b_2" (
        Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.synthesize_short
          (merkle_region layer RegionId.Merkle.Region.RangeB2)
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5) in
    let🞵 b :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessB)
        "Witness b = b_0 || b_1 || b_2"
        Advice.A6 in
    let🞵 c :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessC)
        "Witness c"
        Advice.A6 in
    let🞵 hash :=
      𝓛.InNamespace (hash_at_l_name layer) (
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_1
          (merkle_region layer RegionId.Merkle.Region.HashToPoint)
          merkle_q_x
          merkle_q_y
          a
          b
          c) in
    do🞵
      synthesize_merkle_decomposition_1
        layer
        a
        b
        c
        pair.(AssignedPair.left)
        pair.(AssignedPair.right)
        b1
        b2
        hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.z1_a)
        hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.z1_b) in
    return🞵 hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.x)).

Definition synthesize_merkle_hash_layer_2
    (layer : Z)
    (pair : AssignedPair.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace (merkle_crh_name layer) (
    let🞵 a :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessA)
        "Witness a = a_0 || a_1"
        Advice.A7 in
    let🞵 b1 :=
      𝓛.InNamespace "b_1" (
        Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.synthesize_short
          (merkle_region layer RegionId.Merkle.Region.RangeB1)
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5) in
    let🞵 b2 :=
      𝓛.InNamespace "b_2" (
        Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.synthesize_short
          (merkle_region layer RegionId.Merkle.Region.RangeB2)
          "Range check 5 bits"
          Selector.QLookup
          Selector.QBitshift
          Advice.A9
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5) in
    let🞵 b :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessB)
        "Witness b = b_0 || b_1 || b_2"
        Advice.A7 in
    let🞵 c :=
      witness_message_piece
        (merkle_region layer RegionId.Merkle.Region.WitnessC)
        "Witness c"
        Advice.A7 in
    let🞵 hash :=
      𝓛.InNamespace (hash_at_l_name layer) (
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_2
          (merkle_region layer RegionId.Merkle.Region.HashToPoint)
          merkle_q_x
          merkle_q_y
          a
          b
          c) in
    do🞵
      synthesize_merkle_decomposition_2
        layer
        a
        b
        c
        pair.(AssignedPair.left)
        pair.(AssignedPair.right)
        b1
        b2
        hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.z1_a)
        hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.z1_b) in
    return🞵 hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.MerkleHashResult.x)).

Definition synthesize_merkle_layer
    (layer : Z)
    (node : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  if layer <? 16
  then
    let🞵 pair := synthesize_node_position_1 layer node in
    synthesize_merkle_hash_layer_1 layer pair
  else
    let🞵 pair := synthesize_node_position_2 layer node in
    synthesize_merkle_hash_layer_2 layer pair.

Fixpoint synthesize_merkle_layers
    (fuel : nat)
    (layer : Z)
    (node : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  match fuel with
  | O => return🞵 node
  | S fuel =>
      let🞵 node := synthesize_merkle_layer layer node in
      synthesize_merkle_layers fuel (layer + 1) node
  end.

Definition synthesize_merkle_path
    (leaf : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace "Merkle path" (
    synthesize_merkle_layers 32%nat 0 leaf).

Fixpoint enable_mul_fixed_running_sum_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵
        𝓡.EnableSelector Selector.QMulFixedRunningSum offset "" in
      enable_mul_fixed_running_sum_rows (offset + 1) count
  end.

Definition fixed_base_row : Set :=
  list (Fixed.t * string * Z).

Fixpoint assign_fixed_row
    (offset : Z)
    (row : fixed_base_row)
    : 𝓡 columns RegionId.t unit :=
  match row with
  | [] => return🞵 tt
  | (column, annotation, value) :: row =>
      do🞵
        𝓡.AssignFixed annotation column offset value in
      assign_fixed_row offset row
  end.

Fixpoint assign_fixed_rows_with_selector
    (selector : Selector.t)
    (offset : Z)
    (rows : list fixed_base_row)
    : 𝓡 columns RegionId.t unit :=
  match rows with
  | [] => return🞵 tt
  | row :: rows =>
      do🞵
        𝓡.EnableSelector selector offset "" in
      do🞵
        assign_fixed_row offset row in
      assign_fixed_rows_with_selector selector (offset + 1) rows
  end.

Definition assign_mul_fixed_window
    (region : RegionId.t)
    (offset : Z)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let x := Cell.advice region Advice.A0 offset in
  let y := Cell.advice region Advice.A1 offset in
  return🞵 {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition assign_add_incomplete
    (region : RegionId.t)
    (offset : Z)
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  do🞵 𝓡.EnableSelector Selector.QAddIncomplete offset "" in
  let x_p := Cell.advice region Advice.A0 offset in
  do🞵 𝓡.Copy x_p p.(AssignedPoint.x) in
  let y_p := Cell.advice region Advice.A1 offset in
  do🞵 𝓡.Copy y_p p.(AssignedPoint.y) in
  let x_q := Cell.advice region Advice.A2 offset in
  do🞵 𝓡.Copy x_q q.(AssignedPoint.x) in
  let y_q := Cell.advice region Advice.A3 offset in
  do🞵 𝓡.Copy y_q q.(AssignedPoint.y) in
  let x_r := Cell.advice region Advice.A2 (offset + 1) in
  let y_r := Cell.advice region Advice.A3 (offset + 1) in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Fixpoint assign_incomplete_additions
    (region : RegionId.t)
    (offset : Z)
    (count : nat)
    (acc : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  match count with
  | O => return🞵 acc
  | S count =>
      let🞵 mul_b := assign_mul_fixed_window region offset in
      let🞵 acc := assign_add_incomplete region offset mul_b acc in
      assign_incomplete_additions region (offset + 1) count acc
  end.

Definition synth_short_mul_incomplete
    (region : RegionId.t)
    (magnitude : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t ShortFixedResult.t :=
  𝓛.AddRegion region "Short fixed-base mul (incomplete addition)" (fun region =>
    let z_0 := Cell.advice region Advice.A4 0 in
    do🞵 𝓡.Copy z_0 magnitude in
    let last_window := Cell.advice region Advice.A4 21 in
    (* Strict running-sum decomposition: the tail [z_22] is pinned to zero
       ([decompose_running_sum.rs] with [strict = true]). *)
    do🞵 𝓡.ConstrainConstant (Cell.advice region Advice.A4 22) 0 in
    do🞵 enable_mul_fixed_running_sum_rows 0 22%nat in
    do🞵
      assign_fixed_rows_with_selector
        Selector.QMulFixedRunningSum
        0
        Garden.Orchard.constants.fixed_bases.value_commit_v.short_fixed_rows in
    let🞵 acc := assign_mul_fixed_window region 0 in
    let🞵 acc := assign_incomplete_additions region 1 20%nat acc in
    let🞵 mul_b := assign_mul_fixed_window region 21 in
    return🞵 {|
      ShortFixedResult.acc := acc;
      ShortFixedResult.mul_b := mul_b;
      ShortFixedResult.last_window := last_window;
    |}).

Definition assign_complete_add
    (region : RegionId.t)
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  do🞵 𝓡.EnableSelector Selector.QEccAdd 0 "" in
  let x_p := Cell.advice region Advice.A0 0 in
  do🞵 𝓡.Copy x_p p.(AssignedPoint.x) in
  let y_p := Cell.advice region Advice.A1 0 in
  do🞵 𝓡.Copy y_p p.(AssignedPoint.y) in
  let x_q := Cell.advice region Advice.A2 0 in
  do🞵 𝓡.Copy x_q q.(AssignedPoint.x) in
  let y_q := Cell.advice region Advice.A3 0 in
  do🞵 𝓡.Copy y_q q.(AssignedPoint.y) in
  let x_r := Cell.advice region Advice.A2 1 in
  let y_r := Cell.advice region Advice.A3 1 in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Definition synthesize_short_fixed_base_mul_msb_region
    (region : RegionId.t)
    (sign last_window : Cell.t columns RegionId.t)
    (acc mul_b : AssignedPoint.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.AddRegion region "Short fixed-base mul (most significant word)" (fun region =>
    let🞵 magnitude_mul := assign_complete_add region mul_b acc in
    let sign_target := Cell.advice region Advice.A4 1 in
    do🞵 𝓡.Copy sign_target sign in
    let last_window_target := Cell.advice region Advice.A5 1 in
    do🞵 𝓡.Copy last_window_target last_window in
    do🞵 𝓡.EnableSelector Selector.QMulFixedShort 1 "" in
    let y_var := Cell.advice region Advice.A1 1 in
    return🞵 {|
      AssignedPoint.x := magnitude_mul.(AssignedPoint.x);
      AssignedPoint.y := y_var;
    |}).

Definition synthesize_short_fixed_base_mul
    (magnitude sign : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synth_short_mul_incomplete
      (value_commitment_region RegionId.ValueCommitment.ValueCommitVIncomplete)
      magnitude in
  synthesize_short_fixed_base_mul_msb_region
    (value_commitment_region RegionId.ValueCommitment.ValueCommitVMsb)
    sign
    result.(ShortFixedResult.last_window)
    result.(ShortFixedResult.acc)
    result.(ShortFixedResult.mul_b).

Fixpoint assign_full_window_witnesses
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵
        𝓡.EnableSelector Selector.QMulFixedFull offset "" in
      assign_full_window_witnesses (offset + 1) count
  end.

Definition synth_full_mul_incomplete_with_rows
    (region : RegionId.t)
    (rows : list fixed_base_row)
    : 𝓛 columns RegionId.t FullFixedResult.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (incomplete addition)" (fun region =>
    do🞵 assign_full_window_witnesses 0 85%nat in
    do🞵
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        rows in
    let🞵 acc := assign_mul_fixed_window region 0 in
    let🞵 acc := assign_incomplete_additions region 1 83%nat acc in
    let🞵 mul_b := assign_mul_fixed_window region 84 in
    return🞵 {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_last_region
    (region : RegionId.t)
    (result : FullFixedResult.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (last window, complete addition)" (fun region =>
    assign_complete_add
      region
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synth_value_commit_r_mul
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synth_full_mul_incomplete_with_rows
      (value_commitment_region RegionId.ValueCommitment.ValueCommitRIncomplete)
      Garden.Orchard.constants.fixed_bases.value_commit_r.full_fixed_rows in
  synthesize_full_fixed_base_mul_last_region
    (value_commitment_region RegionId.ValueCommitment.ValueCommitRLast)
    result.

Definition synthesize_full_fixed_base_mul_spend_auth_g
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synth_full_mul_incomplete_with_rows
      (spend_authority_region RegionId.SpendAuthority.FullFixedIncomplete)
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows in
  synthesize_full_fixed_base_mul_last_region
    (spend_authority_region RegionId.SpendAuthority.FullFixedLast)
    result.

Definition synthesize_complete_point_add
    (region : RegionId.t)
    (name : string)
    (p q : AssignedPoint.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "complete point addition" (fun region =>
      assign_complete_add region p q)).

Definition synth_base_field_mul_incomplete
    (region : RegionId.t)
    (scalar : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t BaseFieldFixedResult.t :=
  𝓛.AddRegion region "Base-field elem fixed-base mul (incomplete addition)"
    (fun region =>
      let alpha := Cell.advice region Advice.A4 0 in
      do🞵 𝓡.Copy alpha scalar in
      let z_43_alpha := Cell.advice region Advice.A4 43 in
      let z_44_alpha := Cell.advice region Advice.A4 44 in
      let z_84_alpha := Cell.advice region Advice.A4 84 in
      (* Strict running-sum decomposition: the tail [z_85] is pinned to zero
         ([decompose_running_sum.rs] with [strict = true]). *)
      do🞵 𝓡.ConstrainConstant (Cell.advice region Advice.A4 85) 0 in
      do🞵 enable_mul_fixed_running_sum_rows 0 85%nat in
      do🞵
        assign_fixed_rows_with_selector
          Selector.QMulFixedRunningSum
          0
          Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows in
      let🞵 acc := assign_mul_fixed_window region 0 in
      let🞵 acc := assign_incomplete_additions region 1 83%nat acc in
      let🞵 mul_b := assign_mul_fixed_window region 84 in
      return🞵 {|
        BaseFieldFixedResult.acc := acc;
        BaseFieldFixedResult.mul_b := mul_b;
        BaseFieldFixedResult.alpha := alpha;
        BaseFieldFixedResult.z_43_alpha := z_43_alpha;
        BaseFieldFixedResult.z_44_alpha := z_44_alpha;
        BaseFieldFixedResult.z_84_alpha := z_84_alpha;
      |}).

Definition synth_base_field_mul_complete
    (region : RegionId.t)
    (result : BaseFieldFixedResult.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.AddRegion region "Base-field elem fixed-base mul (complete addition)" (fun region =>
    assign_complete_add
      region
      result.(BaseFieldFixedResult.mul_b)
      result.(BaseFieldFixedResult.acc)).

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵 𝓡.EnableSelector Selector.QLookup offset "" in
      do🞵 𝓡.EnableSelector Selector.QRunning offset "" in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition synthesize_alpha_lookup
    (region : RegionId.t)
    : 𝓛 columns RegionId.t LookupResult.t :=
  𝓛.InNamespace "Lookup range check alpha_0 + 2^130 - t_p" (
    𝓛.AddRegion region "Witness element" (fun region =>
      let z_0 := Cell.advice region Advice.A9 0 in
      do🞵 enable_lookup_running_rows 0 13%nat in
      let z_13 := Cell.advice region Advice.A9 13 in
      return🞵 {|
        LookupResult.z_0 := z_0;
        LookupResult.z_13 := z_13;
      |})).

Definition synthesize_canonicity_checks
    (region : RegionId.t)
    (result : BaseFieldFixedResult.t)
    (lookup : LookupResult.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion region "Canonicity checks" (fun region =>
    do🞵 𝓡.EnableSelector Selector.QMulFixedBaseField 1 "" in
    let alpha_target := Cell.advice region Advice.A6 0 in
    do🞵
      𝓡.Copy alpha_target result.(BaseFieldFixedResult.alpha) in
    let z_84_alpha_target := Cell.advice region Advice.A8 0 in
    do🞵
      𝓡.Copy z_84_alpha_target result.(BaseFieldFixedResult.z_84_alpha) in
    let alpha_0_prime_target := Cell.advice region Advice.A6 1 in
    do🞵 𝓡.Copy alpha_0_prime_target lookup.(LookupResult.z_0) in
    let z_13_alpha_0_prime_target := Cell.advice region Advice.A6 2 in
    do🞵
      𝓡.Copy z_13_alpha_0_prime_target lookup.(LookupResult.z_13) in
    let z_44_alpha_target := Cell.advice region Advice.A7 2 in
    do🞵
      𝓡.Copy z_44_alpha_target result.(BaseFieldFixedResult.z_44_alpha) in
    let z_43_alpha_target := Cell.advice region Advice.A8 2 in
    do🞵
      𝓡.Copy z_43_alpha_target result.(BaseFieldFixedResult.z_43_alpha) in
    return🞵 tt).

Definition synth_nullifier_k_mul
    (scalar : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.InNamespace "base-field elem fixed-base mul of NullifierK" (
    let🞵 result :=
      synth_base_field_mul_incomplete
        (nullifier_region RegionId.Nullifier.BaseFieldIncomplete)
        scalar in
    let🞵 product :=
      synth_base_field_mul_complete
        (nullifier_region RegionId.Nullifier.BaseFieldComplete)
        result in
    let🞵 lookup :=
      synthesize_alpha_lookup (nullifier_region RegionId.Nullifier.AlphaLookup) in
    do🞵
      synthesize_canonicity_checks
        (nullifier_region RegionId.Nullifier.CanonicityChecks)
        result
        lookup in
    return🞵 product).

Definition synthesize_value_commit_orchard
    (magnitude sign : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.InNamespace "cv_net = ValueCommit^Orchard_rcv(v_net)" (
    let🞵 value_commit_v :=
      𝓛.InNamespace "[v] ValueCommitV" (
        𝓛.InNamespace "short fixed-base mul of ValueCommitV" (
          synthesize_short_fixed_base_mul magnitude sign)) in
    let🞵 blind :=
      𝓛.InNamespace "[rcv] ValueCommitR" (
        𝓛.InNamespace "fixed-base mul of ValueCommitR" (
          synth_value_commit_r_mul)) in
    synthesize_complete_point_add
      (value_commitment_region RegionId.ValueCommitment.CompletePointAdd)
      "cv"
      value_commit_v
      blind).

Definition synthesize_value_commitment
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t * Cell.t columns RegionId.t) :=
  let🞵 magnitude :=
    assign_free_advice
      (value_commitment_region RegionId.ValueCommitment.MagnitudeRangeCheck)
      "v_net magnitude"
      Advice.A9
      0 in
  let🞵 sign :=
    assign_free_advice
      (value_commitment_region RegionId.ValueCommitment.SignRangeCheck)
      "v_net sign"
      Advice.A9
      0 in
  do🞵
    𝓛.InNamespace "v_net" (return🞵 tt) in
  do🞵
    𝓛.InNamespace "rcv" (return🞵 tt) in
  let🞵 cv_net :=
    synthesize_value_commit_orchard magnitude sign in
  do🞵
    𝓛.ConstrainInstance cv_net.(AssignedPoint.x) Instance_.Primary CV_NET_X in
  do🞵
    𝓛.ConstrainInstance cv_net.(AssignedPoint.y) Instance_.Primary CV_NET_Y in
  return🞵 (magnitude, sign).

Definition synthesize_scalar_add
    (region : RegionId.t)
    (name : string)
    (a b : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "c = a + b" (fun region =>
      do🞵 𝓡.EnableSelector Selector.QAdd 0 "" in
      let a_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy a_target a in
      let b_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy b_target b in
      return🞵 (Cell.advice region Advice.A6 0))).

Definition synthesize_nullifier
    (rho psi nk : Cell.t columns RegionId.t)
    (cm : AssignedPoint.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 nf_old :=
    𝓛.InNamespace "nf_old = DeriveNullifier_nk(rho_old, psi_old, cm_old)" (
      let🞵 poseidon_output :=
        Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash nk rho in
      let🞵 scalar :=
        synthesize_scalar_add
          (nullifier_region RegionId.Nullifier.ScalarAdd)
          "scalar = poseidon_hash(nk, rho) + psi"
          poseidon_output
          psi in
      let🞵 product :=
        𝓛.InNamespace "[poseidon_output + psi] NullifierK" (
          synth_nullifier_k_mul scalar) in
      let🞵 nf :=
        synthesize_complete_point_add
          (nullifier_region RegionId.Nullifier.CompletePointAdd)
          "nf"
          cm
          product in
      return🞵 nf.(AssignedPoint.x)) in
  return🞵 nf_old.

Definition synthesize_spend_authority
    (ak_P : AssignedPoint.t)
    : 𝓛 columns RegionId.t unit :=
  do🞵
    𝓛.InNamespace "alpha" (return🞵 tt) in
  let🞵 alpha_commitment :=
    𝓛.InNamespace "[alpha] SpendAuthG" (
      𝓛.InNamespace "fixed-base mul of SpendAuthG" (
        synthesize_full_fixed_base_mul_spend_auth_g)) in
  let🞵 rk :=
    synthesize_complete_point_add
      (spend_authority_region RegionId.SpendAuthority.CompletePointAdd)
      "rk"
      alpha_commitment
      ak_P in
  do🞵
    𝓛.ConstrainInstance rk.(AssignedPoint.x) Instance_.Primary RK_X in
  do🞵
    𝓛.ConstrainInstance rk.(AssignedPoint.y) Instance_.Primary RK_Y in
  return🞵 tt.

Definition synthesize_address_integrity
    (ak nk : Cell.t columns RegionId.t)
    (g_d_old : AssignedPoint.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  do🞵
    𝓛.InNamespace "rivk" (return🞵 tt) in
  let🞵 ivk :=
    𝓛.InNamespace "CommitIvk" (
      Garden.Orchard.circuit.commit_ivk.synthesize ak nk) in
  do🞵
    𝓛.InNamespace "ivk" (return🞵 tt) in
  let🞵 pk_d_calculated :=
    𝓛.InNamespace "[ivk] g_d_old" (
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize
        (address_integrity_mul_region
          RegionId.AddressIntegrity.Mul.VariableBase)
        (address_integrity_mul_region
          RegionId.AddressIntegrity.Mul.OverflowS)
        (address_integrity_mul_region
          RegionId.AddressIntegrity.Mul.OverflowLookup)
        (address_integrity_mul_region
          RegionId.AddressIntegrity.Mul.OverflowCheck)
        ivk.(Garden.Orchard.circuit.commit_ivk.AssignedPoint.x)
        g_d_old.(AssignedPoint.x)
        g_d_old.(AssignedPoint.y)) in
  let🞵 pk_d_old :=
    witness_non_identity_point
      (address_integrity_region RegionId.AddressIntegrity.WitnessPkD)
      "witness pk_d_old" in
  do🞵
    𝓛.InNamespace "pk_d_old equality" (
      𝓛.AddRegion
        (address_integrity_region RegionId.AddressIntegrity.Equality)
        "constrain equal" (fun _ =>
        do🞵
          𝓡.Copy
            pk_d_calculated.(Garden.Halo2.halo2_gadgets.ecc.chip.mul.MulResult.x)
            pk_d_old.(AssignedPoint.x) in
        do🞵
          𝓡.Copy
            pk_d_calculated.(Garden.Halo2.halo2_gadgets.ecc.chip.mul.MulResult.y)
            pk_d_old.(AssignedPoint.y) in
        return🞵 tt)) in
  return🞵 pk_d_old.

Definition synthesize_note_commit_old
    (g_d_old pk_d_old : AssignedPoint.t)
    (v_old rho_old psi_old : Cell.t columns RegionId.t)
    (cm_old : AssignedPoint.t)
    : 𝓛 columns RegionId.t unit :=
  do🞵
    𝓛.InNamespace "rcm_old" (return🞵 tt) in
  let🞵 cm :=
    𝓛.InNamespace
      "g★_d || pk★_d || i2lebsp_{64}(v) || i2lebsp_{255}(rho) || i2lebsp_{255}(psi)"
      (Garden.Orchard.circuit.note_commit.synthesize_old
        g_d_old.(AssignedPoint.x)
        g_d_old.(AssignedPoint.y)
        pk_d_old.(AssignedPoint.x)
        pk_d_old.(AssignedPoint.y)
        v_old
        rho_old
        psi_old) in
  𝓛.InNamespace "cm_old equality" (
    𝓛.AddRegion RegionId.NoteCommitOldEquality "constrain equal" (fun _ =>
      do🞵
        𝓡.Copy
          cm.(Garden.Orchard.circuit.note_commit.AssignedPoint.x)
          cm_old.(AssignedPoint.x) in
      do🞵
        𝓡.Copy
          cm.(Garden.Orchard.circuit.note_commit.AssignedPoint.y)
          cm_old.(AssignedPoint.y) in
      return🞵 tt)).

Definition synthesize_note_commit_new
    (v_new rho_new : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (AssignedPoint.t * AssignedPoint.t) :=
  let🞵 g_d_new_star :=
    witness_non_identity_point
      RegionId.NoteCommitNewWitnessGD
      "witness g_d_new_star" in
  let🞵 pk_d_new :=
    witness_non_identity_point
      RegionId.NoteCommitNewWitnessPkD
      "witness pk_d_new" in
  let🞵 psi_new :=
    assign_free_advice
      RegionId.NoteCommitNewWitnessPsi
      "witness psi_new"
      Advice.A0
      0 in
  do🞵
    𝓛.InNamespace "rcm_new" (return🞵 tt) in
  let🞵 cm_new :=
    𝓛.InNamespace
      "g★_d || pk★_d || i2lebsp_{64}(v) || i2lebsp_{255}(rho) || i2lebsp_{255}(psi)"
      (Garden.Orchard.circuit.note_commit.synthesize_new
        g_d_new_star.(AssignedPoint.x)
        g_d_new_star.(AssignedPoint.y)
        pk_d_new.(AssignedPoint.x)
        pk_d_new.(AssignedPoint.y)
        v_new
        rho_new
        psi_new) in
  do🞵
    𝓛.ConstrainInstance
      cm_new.(Garden.Orchard.circuit.note_commit.AssignedPoint.x)
      Instance_.Primary
      CMX in
  return🞵 (g_d_new_star, pk_d_new).

Definition synthesize_orchard_gate
    (v_old v_new magnitude sign root : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion RegionId.OrchardCircuitChecks "Orchard circuit checks" (fun region =>
    let v_old_target := Cell.advice region Advice.A0 0 in
    do🞵 𝓡.Copy v_old_target v_old in
    let v_new_target := Cell.advice region Advice.A1 0 in
    do🞵 𝓡.Copy v_new_target v_new in
    let magnitude_target := Cell.advice region Advice.A2 0 in
    do🞵 𝓡.Copy magnitude_target magnitude in
    let sign_target := Cell.advice region Advice.A3 0 in
    do🞵 𝓡.Copy sign_target sign in
    let root_target := Cell.advice region Advice.A4 0 in
    do🞵 𝓡.Copy root_target root in
    let anchor_target := Cell.advice region Advice.A5 0 in
    let anchor_instance := Cell.instance region Instance_.Primary ANCHOR in
    do🞵 𝓡.Copy anchor_target anchor_instance in
    let enable_spends_target := Cell.advice region Advice.A6 0 in
    let enable_spends_instance :=
      Cell.instance region Instance_.Primary ENABLE_SPEND in
    do🞵 𝓡.Copy enable_spends_target enable_spends_instance in
    let enable_outputs_target := Cell.advice region Advice.A7 0 in
    let enable_outputs_instance :=
      Cell.instance region Instance_.Primary ENABLE_OUTPUT in
    do🞵 𝓡.Copy enable_outputs_target enable_outputs_instance in
    𝓡.EnableSelector Selector.QOrchard 0 "").

(** One coordinate row of the post-NU6.3 cross-address restriction.

    The existing [QOrchard] gate is deliberately reused.  Setting
    [A1 = 0], [A2 = disableCrossAddress], and [A3 = 1] makes its value-balance
    equation tautological.  Setting [A6 = A7 = 1] neutralizes the two enable
    checks.  Its remaining product is therefore

      [disableCrossAddress * (old_coordinate - new_coordinate) = 0].

    [A8] and [A9] are occupied with copies of the flag exactly as in Rust so
    that the V1 floor planner cannot overlap another selector-enabled region
    with these rows. *)
Definition synthesize_cross_address_check_row
    (region : RegionId.t)
    (offset : Z)
    (old_coordinate new_coordinate : Cell.t columns RegionId.t)
    : 𝓡 columns RegionId.t unit :=
  let disable_cross_address := Cell.advice region Advice.A0 offset in
  let disable_cross_address_instance :=
    Cell.instance region Instance_.Primary DISABLE_CROSS_ADDRESS in
  do🞵 𝓡.Copy disable_cross_address disable_cross_address_instance in
  do🞵
    𝓡.ConstrainConstant (Cell.advice region Advice.A1 offset) 0 in
  do🞵
    𝓡.Copy (Cell.advice region Advice.A2 offset) disable_cross_address in
  do🞵
    𝓡.ConstrainConstant (Cell.advice region Advice.A3 offset) 1 in
  do🞵
    𝓡.Copy (Cell.advice region Advice.A4 offset) old_coordinate in
  do🞵
    𝓡.Copy (Cell.advice region Advice.A5 offset) new_coordinate in
  do🞵
    𝓡.ConstrainConstant (Cell.advice region Advice.A6 offset) 1 in
  do🞵
    𝓡.ConstrainConstant (Cell.advice region Advice.A7 offset) 1 in
  do🞵
    𝓡.Copy (Cell.advice region Advice.A8 offset) disable_cross_address in
  do🞵
    𝓡.Copy (Cell.advice region Advice.A9 offset) disable_cross_address in
  𝓡.EnableSelector Selector.QOrchard offset "".

(** The four coordinate checks are ordered exactly like Orchard's Rust
    implementation: [g_d.x], [g_d.y], [pk_d.x], [pk_d.y]. *)
Definition synthesize_cross_address_checks
    (addresses : AddressPoints.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    RegionId.PostNu63CrossAddressChecks
    "post-NU 6.3 cross-address checks"
    (fun region =>
      do🞵
        synthesize_cross_address_check_row region 0
          addresses.(AddressPoints.g_d_old).(AssignedPoint.x)
          addresses.(AddressPoints.g_d_new).(AssignedPoint.x) in
      do🞵
        synthesize_cross_address_check_row region 1
          addresses.(AddressPoints.g_d_old).(AssignedPoint.y)
          addresses.(AddressPoints.g_d_new).(AssignedPoint.y) in
      do🞵
        synthesize_cross_address_check_row region 2
          addresses.(AddressPoints.pk_d_old).(AssignedPoint.x)
          addresses.(AddressPoints.pk_d_new).(AssignedPoint.x) in
      synthesize_cross_address_check_row region 3
        addresses.(AddressPoints.pk_d_old).(AssignedPoint.y)
        addresses.(AddressPoints.pk_d_new).(AssignedPoint.y)).

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  do🞵 Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table in
  let🞵 '(psi_old, rho_old, cm_old, g_d_old, ak_P, nk, v_old, v_new) :=
    synthesize_witness_inputs in
  let🞵 root := synthesize_merkle_path cm_old.(AssignedPoint.x) in
  let🞵 '(magnitude, sign) := synthesize_value_commitment in
  let🞵 rho_new := synthesize_nullifier rho_old psi_old nk cm_old in
  do🞵 𝓛.ConstrainInstance rho_new Instance_.Primary NF_OLD in
  do🞵 synthesize_spend_authority ak_P in
  let🞵 pk_d_old := synthesize_address_integrity ak_P.(AssignedPoint.x) nk g_d_old in
  do🞵
    synthesize_note_commit_old
      g_d_old
      pk_d_old
      v_old
      rho_old
      psi_old
      cm_old in
  let🞵 '(g_d_new, pk_d_new) := synthesize_note_commit_new v_new rho_new in
  do🞵 synthesize_orchard_gate v_old v_new magnitude sign root in
  synthesize_cross_address_checks {|
    AddressPoints.g_d_old := g_d_old;
    AddressPoints.pk_d_old := pk_d_old;
    AddressPoints.g_d_new := g_d_new;
    AddressPoints.pk_d_new := pk_d_new;
  |}.

(** The usable-row bound of the Orchard proving system: [n - (blinding_factors
    + 1)] for [n = 2^k = 2048] ([k = 11]) and [blinding_factors = 5], so the
    lookup-table default fill stops at row [2042], leaving the [l_last] row and
    the five blinding rows at [0] — matching the keygen-stored fixed column.
    The domain lives downstream ([Domain.usable_rows] in [compiled/main.v]),
    so the literal is introduced here and tied to the domain by a parity fact at
    that layer. *)
Definition orchard_usable_rows : Z := 2042.

Definition synthesize_events
    (indices : Garden.Halo2.serialize.Indices.t columns)
    : list Garden.Halo2.serialize.Raw.Event.t :=
  let '(_, events) :=
    Garden.Halo2.serialize.V1.run_with_region_start
      indices
      Garden.Orchard.circuit_synthesis_layout.region_start_of
      orchard_usable_rows
      synthesize in
  events ++ Garden.Orchard.circuit_synthesis_constants.events.
