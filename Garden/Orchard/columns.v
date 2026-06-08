Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.

Module Advice.
  Inductive t : Set :=
  | A0
  | A1
  | A2
  | A3
  | A4
  | A5
  | A6
  | A7
  | A8
  | A9.
End Advice.

Module Lookup.
  Inductive t : Set :=
  | TableIdx
  | TableX
  | TableY.
End Lookup.

Module Fixed.
  Inductive t : Set :=
  | LagrangeCoeffs0
  | LagrangeCoeffs1
  | LagrangeCoeffs2
  | LagrangeCoeffs3
  | LagrangeCoeffs4
  | LagrangeCoeffs5
  | LagrangeCoeffs6
  | LagrangeCoeffs7
  | FixedZ
  | QSinsemilla2_1
  | QSinsemilla2_2
  | Lookup (lookup : Lookup.t).
End Fixed.

Module Instance_.
  Inductive t : Set :=
  | Primary.
End Instance_.

Module Selector.
  Inductive t : Set :=
  | QOrchard
  | QAdd
  | QLookup
  | QRunning
  | QBitshift
  | QWitnessPoint
  | QWitnessPointNonId
  | QAddIncomplete
  | QEccAdd
  | QMulIncompleteHi1
  | QMulIncompleteHi2
  | QMulIncompleteHi3
  | QMulIncompleteLo1
  | QMulIncompleteLo2
  | QMulIncompleteLo3
  | QMulDecomposeVar
  | QMulOverflow
  | QMulLsb
  | QMulFixedRunningSum
  | QMulFixedFull
  | QMulFixedShort
  | QMulFixedBaseField
  | QPoseidonFull
  | QPoseidonPartial
  | QPoseidonPadAndAdd
  | QSinsemilla1_1
  | QSinsemilla4_1
  | QSinsemilla1_2
  | QSinsemilla4_2
  | QCondSwap1
  | QCondSwap2
  | QMerkleDecompose1
  | QMerkleDecompose2
  | QCommitIvk
  | QNoteCommitOldB
  | QNoteCommitOldD
  | QNoteCommitOldE
  | QNoteCommitOldG
  | QNoteCommitOldH
  | QNoteCommitOldGd
  | QNoteCommitOldPkd
  | QNoteCommitOldValue
  | QNoteCommitOldRho
  | QNoteCommitOldPsi
  | QNoteCommitOldYCanon
  | QNoteCommitNewB
  | QNoteCommitNewD
  | QNoteCommitNewE
  | QNoteCommitNewG
  | QNoteCommitNewH
  | QNoteCommitNewGd
  | QNoteCommitNewPkd
  | QNoteCommitNewValue
  | QNoteCommitNewRho
  | QNoteCommitNewPsi
  | QNoteCommitNewYCanon.
End Selector.

Definition columns : Columns.t := {|
  Columns.Selector := Selector.t;
  Columns.Fixed := Fixed.t;
  Columns.Advice := Advice.t;
  Columns.Instance_ := Instance_.t;
|}.
Canonical columns.

Module Index.
  Definition advice (advice : Advice.t) : Z :=
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

  Definition lookup (lookup : Lookup.t) : Z :=
    match lookup with
    | Lookup.TableIdx => 0
    | Lookup.TableX => 1
    | Lookup.TableY => 2
    end.

  Definition fixed (fixed : Fixed.t) : Z :=
    match fixed with
    | Fixed.Lookup lookup_column => lookup lookup_column
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

  Definition instance_ (instance : Instance_.t) : Z :=
    match instance with
    | Instance_.Primary => 0
    end.

  Definition selector (selector : Selector.t) : Z :=
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

  Definition indices : Indices.t columns := {|
    Indices.selector := selector;
    Indices.fixed := fixed;
    Indices.advice := advice;
    Indices.instance_ := instance_;
  |}.
End Index.
