Require Export Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

Module RegionId.
  Module WitnessInput.
    Inductive t : Set :=
    | PsiOld
    | RhoOld
    | CmOld
    | GDOld
    | AkP
    | Nk
    | VOld
    | VNew.
  End WitnessInput.

  Module Merkle.
    Module Layer.
      Inductive t : Set :=
      | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7
      | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15
      | L16 | L17 | L18 | L19 | L20 | L21 | L22 | L23
      | L24 | L25 | L26 | L27 | L28 | L29 | L30 | L31.

      Definition to_index (layer : t) : Z :=
        match layer with
        | L0 => 0 | L1 => 1 | L2 => 2 | L3 => 3
        | L4 => 4 | L5 => 5 | L6 => 6 | L7 => 7
        | L8 => 8 | L9 => 9 | L10 => 10 | L11 => 11
        | L12 => 12 | L13 => 13 | L14 => 14 | L15 => 15
        | L16 => 16 | L17 => 17 | L18 => 18 | L19 => 19
        | L20 => 20 | L21 => 21 | L22 => 22 | L23 => 23
        | L24 => 24 | L25 => 25 | L26 => 26 | L27 => 27
        | L28 => 28 | L29 => 29 | L30 => 30 | L31 => 31
        end.

      Definition of_index (index : Z) : t :=
        match index with
        | 0 => L0 | 1 => L1 | 2 => L2 | 3 => L3
        | 4 => L4 | 5 => L5 | 6 => L6 | 7 => L7
        | 8 => L8 | 9 => L9 | 10 => L10 | 11 => L11
        | 12 => L12 | 13 => L13 | 14 => L14 | 15 => L15
        | 16 => L16 | 17 => L17 | 18 => L18 | 19 => L19
        | 20 => L20 | 21 => L21 | 22 => L22 | 23 => L23
        | 24 => L24 | 25 => L25 | 26 => L26 | 27 => L27
        | 28 => L28 | 29 => L29 | 30 => L30 | _ => L31
        end.
    End Layer.

    Module Region.
      Inductive t : Set :=
      | NodePosition
      | WitnessA
      | RangeB1
      | RangeB2
      | WitnessB
      | WitnessC
      | HashToPoint
      | Decomposition.
    End Region.
  End Merkle.

  Module Poseidon.
    Inductive t : Set :=
    | InitialState
    | AddInput
    | PermuteState
    | FullRound
    | PartialRounds
    | PadAndAdd.
  End Poseidon.

  Module ValueCommitment.
    Inductive t : Set :=
    | MagnitudeRangeCheck
    | SignRangeCheck
    | ValueCommitVIncomplete
    | ValueCommitVMsb
    | ValueCommitRIncomplete
    | ValueCommitRLast
    | CompletePointAdd.
  End ValueCommitment.

  Module Nullifier.
    Inductive t : Set :=
    | ScalarAdd
    | BaseFieldIncomplete
    | BaseFieldComplete
    | AlphaLookup
    | CanonicityChecks
    | CompletePointAdd.
  End Nullifier.

  Module SpendAuthority.
    Inductive t : Set :=
    | FullFixedIncomplete
    | FullFixedLast
    | CompletePointAdd.
  End SpendAuthority.

  Module AddressIntegrity.
    Module Mul.
      Inductive t : Set :=
      | VariableBase
      | OverflowS
      | OverflowLookup
      | OverflowCheck.
    End Mul.

    Inductive t : Set :=
    | Mul (region : Mul.t)
    | WitnessPkD
    | Equality.
  End AddressIntegrity.

  Module CommitIvk.
    Inductive t : Set :=
    | WitnessA
    | RangeB0
    | RangeB2
    | WitnessB
    | WitnessC
    | RangeD0
    | WitnessD
    | FixedBaseIncomplete
    | FixedBaseLast
    | HashToPoint
    | CompletePointAdd
    | AkLookup
    | NkLookup
    | CanonicityGate.
  End CommitIvk.

  Module NoteCommit.
    Module Which.
      Inductive t : Set :=
      | Old
      | New.
    End Which.

    Module YSubject.
      Inductive t : Set :=
      | GD
      | PkD.
    End YSubject.

    Module YCanonicity.
      Inductive t : Set :=
      | RangeK0
      | RangeK2
      | JLookup
      | JPrimeLookup
      | Gate.
    End YCanonicity.

    Inductive t : Set :=
    | WitnessA
    | RangeB0
    | RangeB3
    | WitnessB
    | WitnessC
    | RangeD2
    | WitnessD
    | RangeE0
    | RangeE1
    | WitnessE
    | WitnessF
    | RangeG1
    | WitnessG
    | RangeH0
    | WitnessH
    | YCanonicity (subject : YSubject.t) (region : YCanonicity.t)
    | FixedBaseIncomplete
    | FixedBaseLast
    | HashToPoint
    | CompletePointAdd
    | XGDLookup
    | XPKDLookup
    | RhoLookup
    | PsiLookup
    | MessagePieceB
    | MessagePieceD
    | MessagePieceE
    | MessagePieceG
    | MessagePieceH
    | InputGD
    | InputPkD
    | InputValue
    | InputRho
    | InputPsi.
  End NoteCommit.

  Module GadgetLocal.
    Inductive t : Set :=
    | AddChip
    | CondSwap
    | SinsemillaGate
    | SinsemillaInitialY
    | SinsemillaMerkleDecomposition
    | PoseidonFullRound
    | PoseidonPartialRounds
    | PoseidonPadAndAdd
    | EccChipDummyBase
    | EccWitnessPoint
    | EccWitnessNonIdentityPoint
    | EccAdd
    | EccAddIncomplete
    | EccMulVariableBase
    | EccMulOverflowS
    | EccMulOverflowLookup
    | EccMulOverflowCheck
    | EccMulIncomplete1
    | EccMulIncomplete2
    | EccMulIncomplete3
    | EccMulComplete
    | EccMulFixed
    | EccMulFixedShort
    | EccMulFixedFullWidth
    | EccMulFixedBaseField.
  End GadgetLocal.

  Inductive t : Set :=
  | WitnessInput (region : WitnessInput.t)
  | Merkle (layer : Merkle.Layer.t) (region : Merkle.Region.t)
  | Poseidon (region : Poseidon.t)
  | ValueCommitment (region : ValueCommitment.t)
  | Nullifier (region : Nullifier.t)
  | SpendAuthority (region : SpendAuthority.t)
  | AddressIntegrity (region : AddressIntegrity.t)
  | CommitIvk (region : CommitIvk.t)
  | NoteCommit (which : NoteCommit.Which.t) (region : NoteCommit.t)
  | NoteCommitOldEquality
  | NoteCommitNewWitnessGD
  | NoteCommitNewWitnessPkD
  | NoteCommitNewWitnessPsi
  | OrchardCircuitChecks
  | GadgetLocal (region : GadgetLocal.t).
End RegionId.
