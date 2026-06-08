Require Import Garden.Halo2.main.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit_generated.
Require Import Garden.Orchard.columns.

Import ListNotations.
Global Open Scope Z_scope.

Module Generated := Garden.Orchard.circuit_generated.

Definition map_advice (advice : Advice.t) : Z :=
  match advice with
  | Advice.A0 => 0
  | Advice.A1 => 1
  | Advice.A2 => 2
  | Advice.A3 => 3
  | Advice.A4 => 4
  | Advice.A5 => 5
  | Advice.A6 => 6
  | Advice.A7 => 7
  | Advice.A8 => 8
  | Advice.A9 => 9
  end.

Definition map_lookup (lookup : Lookup.t) : Z :=
  match lookup with
  | Lookup.TableIdx => 0
  | Lookup.TableX => 1
  | Lookup.TableY => 2
  end.

Definition map_fixed (fixed : Fixed.t) : Z :=
  match fixed with
  | Fixed.Lookup lookup => map_lookup lookup
  | Fixed.LagrangeCoeffs0 => 3
  | Fixed.LagrangeCoeffs1 => 4
  | Fixed.LagrangeCoeffs2 => 5
  | Fixed.LagrangeCoeffs3 => 6
  | Fixed.LagrangeCoeffs4 => 7
  | Fixed.LagrangeCoeffs5 => 8
  | Fixed.LagrangeCoeffs6 => 9
  | Fixed.LagrangeCoeffs7 => 10
  | Fixed.FixedZ => 11
  | Fixed.QSinsemilla2_1 => 12
  | Fixed.QSinsemilla2_2 => 13
  end.

Definition map_instance (instance : Instance_.t) : Z :=
  match instance with
  | Instance_.Primary => 0
  end.

Definition map_selector (selector : Selector.t) : Z :=
  match selector with
  | Selector.QOrchard => 0
  | Selector.QAdd => 1
  | Selector.QLookup => 2
  | Selector.QRunning => 3
  | Selector.QBitshift => 4
  | Selector.QWitnessPoint => 5
  | Selector.QWitnessPointNonId => 6
  | Selector.QAddIncomplete => 7
  | Selector.QEccAdd => 8
  | Selector.QMulIncompleteHi1 => 9
  | Selector.QMulIncompleteHi2 => 10
  | Selector.QMulIncompleteHi3 => 11
  | Selector.QMulIncompleteLo1 => 12
  | Selector.QMulIncompleteLo2 => 13
  | Selector.QMulIncompleteLo3 => 14
  | Selector.QMulDecomposeVar => 15
  | Selector.QMulOverflow => 16
  | Selector.QMulLsb => 17
  | Selector.QMulFixedRunningSum => 18
  | Selector.QMulFixedFull => 19
  | Selector.QMulFixedShort => 20
  | Selector.QMulFixedBaseField => 21
  | Selector.QPoseidonFull => 22
  | Selector.QPoseidonPartial => 23
  | Selector.QPoseidonPadAndAdd => 24
  | Selector.QSinsemilla1_1 => 25
  | Selector.QSinsemilla4_1 => 26
  | Selector.QCondSwap1 => 27
  | Selector.QMerkleDecompose1 => 28
  | Selector.QSinsemilla1_2 => 29
  | Selector.QSinsemilla4_2 => 30
  | Selector.QCondSwap2 => 31
  | Selector.QMerkleDecompose2 => 32
  | Selector.QCommitIvk => 33
  | Selector.QNoteCommitOldB => 34
  | Selector.QNoteCommitOldD => 35
  | Selector.QNoteCommitOldE => 36
  | Selector.QNoteCommitOldG => 37
  | Selector.QNoteCommitOldH => 38
  | Selector.QNoteCommitOldGd => 39
  | Selector.QNoteCommitOldPkd => 40
  | Selector.QNoteCommitOldValue => 41
  | Selector.QNoteCommitOldRho => 42
  | Selector.QNoteCommitOldPsi => 43
  | Selector.QNoteCommitOldYCanon => 44
  | Selector.QNoteCommitNewB => 45
  | Selector.QNoteCommitNewD => 46
  | Selector.QNoteCommitNewE => 47
  | Selector.QNoteCommitNewG => 48
  | Selector.QNoteCommitNewH => 49
  | Selector.QNoteCommitNewGd => 50
  | Selector.QNoteCommitNewPkd => 51
  | Selector.QNoteCommitNewValue => 52
  | Selector.QNoteCommitNewRho => 53
  | Selector.QNoteCommitNewPsi => 54
  | Selector.QNoteCommitNewYCanon => 55
  end.

Definition column_map : Columns.map columns Generated.indexed_columns :=
  @Columns.Build_map
    columns
    Generated.indexed_columns
    map_selector
    map_fixed
    map_advice
    map_instance.

Definition configure : ConstraintSystem.t Generated.indexed_columns :=
  ConstraintSystem.map
    column_map
    (Garden.Orchard.circuit.configure (@ConstraintSystem.empty columns)).

Theorem configure_eq_generated :
    configure = Generated.configure.
Proof.
  vm_compute.
  reflexivity.
Qed.
