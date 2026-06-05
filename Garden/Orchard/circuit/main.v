Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.Ecc.
Require Import Garden.Halo2.Gadgets.LookupRangeCheck.
Require Import Garden.Halo2.Gadgets.Merkle.
Require Import Garden.Halo2.Gadgets.Poseidon.
Require Import Garden.Halo2.Gadgets.Sinsemilla.
Require Import Garden.Orchard.constants.
Require Import Garden.Orchard.circuit.commit_ivk.
Require Import Garden.Orchard.circuit.gadget.
Require Import Garden.Orchard.circuit.gadget.add_chip.
Require Import Garden.Orchard.circuit.note_commit.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition advice0 : Column.t := Column.advice 0 "advices[0]".
Definition advice1 : Column.t := Column.advice 1 "advices[1]".
Definition advice2 : Column.t := Column.advice 2 "advices[2]".
Definition advice3 : Column.t := Column.advice 3 "advices[3]".
Definition advice4 : Column.t := Column.advice 4 "advices[4]".
Definition advice5 : Column.t := Column.advice 5 "advices[5]".
Definition advice6 : Column.t := Column.advice 6 "advices[6]".
Definition advice7 : Column.t := Column.advice 7 "advices[7]".
Definition advice8 : Column.t := Column.advice 8 "advices[8]".
Definition advice9 : Column.t := Column.advice 9 "advices[9]".

Definition advices : list Column.t :=
  [advice0; advice1; advice2; advice3; advice4; advice5; advice6; advice7; advice8; advice9].

Definition table_idx : Column.t := Column.lookup_table 0 "table_idx".
Definition table_x : Column.t := Column.lookup_table 1 "table_x".
Definition table_y : Column.t := Column.lookup_table 2 "table_y".
Definition primary : Column.t := Column.instance 0 "primary".

Definition lagrange0 : Column.t := Column.fixed 0 "lagrange_coeffs[0]".
Definition lagrange1 : Column.t := Column.fixed 1 "lagrange_coeffs[1]".
Definition lagrange2 : Column.t := Column.fixed 2 "lagrange_coeffs[2]".
Definition lagrange3 : Column.t := Column.fixed 3 "lagrange_coeffs[3]".
Definition lagrange4 : Column.t := Column.fixed 4 "lagrange_coeffs[4]".
Definition lagrange5 : Column.t := Column.fixed 5 "lagrange_coeffs[5]".
Definition lagrange6 : Column.t := Column.fixed 6 "lagrange_coeffs[6]".
Definition lagrange7 : Column.t := Column.fixed 7 "lagrange_coeffs[7]".

Definition lagrange_coeffs : list Column.t :=
  [lagrange0; lagrange1; lagrange2; lagrange3; lagrange4; lagrange5; lagrange6; lagrange7].

Definition q_orchard : Selector.t := Selector.make 0 "q_orchard".

Module OrchardCircuitVersion.
  Inductive t : Set :=
  | InsecurePreNu6_2
  | FixedPostNu6_2.

  Definition halo2_version (self : t) : Ecc.CircuitVersion.t :=
    match self with
    | InsecurePreNu6_2 => Ecc.CircuitVersion.InsecureUnanchoredBase
    | FixedPostNu6_2 => Ecc.CircuitVersion.AnchoredBase
    end.

  Definition to_string (self : t) : string :=
    match self with
    | InsecurePreNu6_2 => "InsecurePreNu6_2"
    | FixedPostNu6_2 => "FixedPostNu6_2"
    end.
End OrchardCircuitVersion.

Module ActionConfig.
  Record t : Set := {
    primary : Column.t;
    constant : Column.t;
    q_orchard : Selector.t;
    advices : list Column.t;
    add_config : AddConfig.t;
    ecc_config : EccConfig.t;
    poseidon_config : Pow5Config.t;
    merkle_config_1 : MerkleConfig.t;
    merkle_config_2 : MerkleConfig.t;
    sinsemilla_config_1 : SinsemillaConfig.t;
    sinsemilla_config_2 : SinsemillaConfig.t;
    commit_ivk_config : CommitIvkConfig.t;
    old_note_commit_config : NoteCommitConfig.t;
    new_note_commit_config : NoteCommitConfig.t;
  }.
End ActionConfig.

Definition orchard_checks_gate : Gate.t :=
  let v_old := Expr.advice advice0 Rotation.Cur in
  let v_new := Expr.advice advice1 Rotation.Cur in
  let magnitude := Expr.advice advice2 Rotation.Cur in
  let sign := Expr.advice advice3 Rotation.Cur in
  let root := Expr.advice advice4 Rotation.Cur in
  let anchor := Expr.advice advice5 Rotation.Cur in
  let enable_spends := Expr.advice advice6 Rotation.Cur in
  let enable_outputs := Expr.advice advice7 Rotation.Cur in
  Gate.make
    "Orchard circuit checks"
    (Some q_orchard)
    [
      GateConstraint.make
        "v_old - v_new = magnitude * sign"
        (v_old -H v_new -H (magnitude *H sign));
      GateConstraint.make
        "Either v_old = 0, or root = anchor"
        (v_old *H (root -H anchor));
      GateConstraint.make
        "v_old = 0 or enable_spends = 1"
        (v_old *H (Expr.one -H enable_spends));
      GateConstraint.make
        "v_new = 0 or enable_outputs = 1"
        (v_new *H (Expr.one -H enable_outputs))
    ].

Definition column_events : Config.Trace :=
  List.map Config.Event.AdviceColumn advices ++
  List.map Config.Event.FixedColumn lagrange_coeffs ++
  [
    Config.Event.LookupTableColumn table_idx;
    Config.Event.LookupTableColumn table_x;
    Config.Event.LookupTableColumn table_y;
    Config.Event.InstanceColumn primary;
    Config.Event.Selector q_orchard;
    Config.Event.EnableEquality primary;
    Config.Event.EnableConstant lagrange0
  ] ++
  List.map Config.Event.EnableEquality advices.

Definition configure : ActionConfig.t * Config.Trace :=
  let '(range_config, range_trace) :=
    LookupRangeCheck.configure 10 advice9 table_idx 1 in
  let '(add_config, add_trace) :=
    AddChip.configure 2 advice7 advice8 advice6 in
  let '(ecc_config, ecc_trace) :=
    Ecc.configure
      advices
      lagrange_coeffs
      range_config
      Ecc.CircuitVersion.AnchoredBase in
  let '(poseidon_config, poseidon_trace) :=
    Poseidon.configure
      [advice6; advice7; advice8]
      advice5
      [lagrange2; lagrange3; lagrange4]
      [lagrange5; lagrange6; lagrange7]
      3
      2 in
  let '(sinsemilla_config_1, sinsemilla_trace_1) :=
    Sinsemilla.configure
      [advice0; advice1; advice2; advice3; advice4]
      table_idx
      table_x
      table_y
      range_config
      lagrange0
      20
      false in
  let '(merkle_config_1, merkle_trace_1) :=
    Merkle.configure sinsemilla_config_1 22 MERKLE_DEPTH_ORCHARD in
  let '(sinsemilla_config_2, sinsemilla_trace_2) :=
    Sinsemilla.configure
      [advice5; advice6; advice7; advice8; advice9]
      table_idx
      table_x
      table_y
      range_config
      lagrange1
      30
      false in
  let '(merkle_config_2, merkle_trace_2) :=
    Merkle.configure sinsemilla_config_2 32 MERKLE_DEPTH_ORCHARD in
  let '(commit_ivk_config, commit_ivk_trace) :=
    CommitIvkChip.configure 40 advices in
  let '(old_note_commit_config, old_note_commit_trace) :=
    NoteCommitChip.configure 50 advices "sinsemilla_config_1" in
  let '(new_note_commit_config, new_note_commit_trace) :=
    NoteCommitChip.configure 70 advices "sinsemilla_config_2" in
  ({|
    ActionConfig.primary := primary;
    ActionConfig.constant := lagrange0;
    ActionConfig.q_orchard := q_orchard;
    ActionConfig.advices := advices;
    ActionConfig.add_config := add_config;
    ActionConfig.ecc_config := ecc_config;
    ActionConfig.poseidon_config := poseidon_config;
    ActionConfig.merkle_config_1 := merkle_config_1;
    ActionConfig.merkle_config_2 := merkle_config_2;
    ActionConfig.sinsemilla_config_1 := sinsemilla_config_1;
    ActionConfig.sinsemilla_config_2 := sinsemilla_config_2;
    ActionConfig.commit_ivk_config := commit_ivk_config;
    ActionConfig.old_note_commit_config := old_note_commit_config;
    ActionConfig.new_note_commit_config := new_note_commit_config;
  |},
  column_events ++
  [
    Config.Event.CreateGate orchard_checks_gate
  ] ++
  add_trace ++
  [
    Config.Event.LookupTableColumn table_idx;
    Config.Event.LookupTableColumn table_x;
    Config.Event.LookupTableColumn table_y
  ] ++
  range_trace ++
  ecc_trace ++
  poseidon_trace ++
  sinsemilla_trace_1 ++
  merkle_trace_1 ++
  sinsemilla_trace_2 ++
  merkle_trace_2 ++
  commit_ivk_trace ++
  old_note_commit_trace ++
  new_note_commit_trace).

Definition default_config : ActionConfig.t := fst configure.
Definition configure_trace : Config.Trace := snd configure.

Definition witness_private_inputs (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Witness private inputs used across checks" [
    assign_free_advice "witness psi_old" advice0;
    assign_free_advice "witness rho_old" advice0;
    Ecc.witness_point "cm_old";
    Ecc.witness_non_identity_point "gd_old";
    Ecc.witness_non_identity_point "witness ak_P";
    assign_free_advice "witness nk" advice0;
    assign_free_advice "witness v_old" advice0;
    assign_free_advice "witness v_new" advice0
  ].

Definition value_commitment_integrity (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Value commitment integrity" [
    assign_free_advice "v_net magnitude" advice9;
    assign_free_advice "v_net sign" advice9;
    Ecc.scalar_fixed_short "v_net";
    Ecc.scalar_fixed "rcv";
    value_commit_orchard;
    Synth.Event.ConstrainInstance
      "cv_net.x == public input"
      (CellRef.named "cv_net.x")
      cfg.(ActionConfig.primary)
      PublicInput.CV_NET_X;
    Synth.Event.ConstrainInstance
      "cv_net.y == public input"
      (CellRef.named "cv_net.y")
      cfg.(ActionConfig.primary)
      PublicInput.CV_NET_Y;
    Synth.Event.Return "v_net magnitude/sign"
  ].

Definition nullifier_integrity (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Nullifier integrity" [
    derive_nullifier cfg.(ActionConfig.add_config);
    Synth.Event.ConstrainInstance
      "nf_old == public input"
      (CellRef.named "nf_old")
      cfg.(ActionConfig.primary)
      PublicInput.NF_OLD;
    Synth.Event.Return "nf_old"
  ].

Definition spend_authority (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Spend authority" [
    Ecc.scalar_fixed "alpha";
    Ecc.fixed_mul "[alpha] SpendAuthG" FixedBase.SpendAuthG "alpha";
    Ecc.add "rk" "[alpha] SpendAuthG" "ak_P";
    Synth.Event.ConstrainInstance
      "rk.x == public input"
      (CellRef.named "rk.x")
      cfg.(ActionConfig.primary)
      PublicInput.RK_X;
    Synth.Event.ConstrainInstance
      "rk.y == public input"
      (CellRef.named "rk.y")
      cfg.(ActionConfig.primary)
      PublicInput.RK_Y
  ].

Definition diversified_address_integrity (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Diversified address integrity" [
    Ecc.scalar_fixed "rivk";
    commit_ivk cfg.(ActionConfig.commit_ivk_config);
    Ecc.scalar_var_from_base "ivk";
    Ecc.variable_mul "[ivk] g_d_old" "g_d_old" "ivk";
    Ecc.witness_non_identity_point "witness pk_d_old";
    Synth.Event.ConstrainEqual
      "pk_d_old equality"
      (CellRef.named "derived_pk_d_old")
      (CellRef.named "pk_d_old");
    Synth.Event.Return "pk_d_old"
  ].

Definition old_note_commitment_integrity (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "Old note commitment integrity" [
    Ecc.scalar_fixed "rcm_old";
    note_commit cfg.(ActionConfig.old_note_commit_config);
    Synth.Event.ConstrainEqual
      "cm_old equality"
      (CellRef.named "derived_cm_old")
      (CellRef.named "cm_old")
  ].

Definition new_note_commitment_integrity (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "New note commitment integrity" [
    Ecc.witness_non_identity_point "witness g_d_new_star";
    Ecc.witness_non_identity_point "witness pk_d_new";
    Synth.Event.Note "rho_new is constrained to nf_old";
    assign_free_advice "witness psi_new" advice0;
    Ecc.scalar_fixed "rcm_new";
    note_commit cfg.(ActionConfig.new_note_commit_config);
    Synth.Event.ConstrainInstance
      "cmx == public input"
      (CellRef.named "cm_new.extract_p")
      cfg.(ActionConfig.primary)
      PublicInput.CMX
  ].

Definition remaining_orchard_checks (cfg : ActionConfig.t) : Synth.Event.t :=
  Synth.Event.Region "Orchard circuit checks" [
    RegionEvent.EnableSelector cfg.(ActionConfig.q_orchard) 0;
    RegionEvent.CopyAdvice "v_old" (CellRef.named "v_old") advice0 0;
    RegionEvent.CopyAdvice "v_new" (CellRef.named "v_new") advice1 0;
    RegionEvent.CopyAdvice "v_net magnitude" (CellRef.named "v_net magnitude") advice2 0;
    RegionEvent.CopyAdvice "v_net sign" (CellRef.named "v_net sign") advice3 0;
    RegionEvent.CopyAdvice "calculated root" (CellRef.named "calculated root") advice4 0;
    RegionEvent.AssignAdviceFromInstance
      "pub input anchor"
      cfg.(ActionConfig.primary)
      PublicInput.ANCHOR
      advice5
      0;
    RegionEvent.AssignAdviceFromInstance
      "enable spends"
      cfg.(ActionConfig.primary)
      PublicInput.ENABLE_SPEND
      advice6
      0;
    RegionEvent.AssignAdviceFromInstance
      "enable outputs"
      cfg.(ActionConfig.primary)
      PublicInput.ENABLE_OUTPUT
      advice7
      0
  ].

Definition synthesize
    (cfg : ActionConfig.t)
    (version : OrchardCircuitVersion.t)
    : Synth.Trace :=
  Sinsemilla.load cfg.(ActionConfig.sinsemilla_config_1) ++
  [
    Synth.Event.Note (OrchardCircuitVersion.to_string version);
    Ecc.construct cfg.(ActionConfig.ecc_config);
    witness_private_inputs cfg;
    Merkle.calculate_root
      cfg.(ActionConfig.merkle_config_1)
      "Merkle path"
      "cm_old.extract_p";
    value_commitment_integrity cfg;
    nullifier_integrity cfg;
    spend_authority cfg;
    diversified_address_integrity cfg;
    old_note_commitment_integrity cfg;
    new_note_commitment_integrity cfg;
    remaining_orchard_checks cfg
  ].

Definition action_circuit : Circuit.t := {|
  Circuit.name := "Orchard Action circuit";
  Circuit.dependencies := [
    "halo2_proofs::plonk::Circuit";
    "halo2_proofs::circuit::Chip";
    "halo2_gadgets::ecc";
    "halo2_gadgets::poseidon";
    "halo2_gadgets::sinsemilla";
    "halo2_gadgets::utilities::lookup_range_check";
    "orchard::circuit::commit_ivk";
    "orchard::circuit::note_commit";
    "orchard::circuit::gadget::add_chip"
  ];
  Circuit.configure := configure_trace;
  Circuit.synthesize := synthesize default_config OrchardCircuitVersion.FixedPostNu6_2;
|}.
