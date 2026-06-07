Require Import Garden.Halo2.main.

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
  | QMerkleDecompose2.
End Selector.

Definition columns : Columns.t := {|
  Columns.Selector := Selector.t;
  Columns.Fixed := Fixed.t;
  Columns.Advice := Advice.t;
  Columns.Instance_ := Instance_.t;
|}.
Canonical columns.
