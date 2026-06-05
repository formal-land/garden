Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.

Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module PublicInput.
  Definition ANCHOR : Z := 0.
  Definition CV_NET_X : Z := 1.
  Definition CV_NET_Y : Z := 2.
  Definition NF_OLD : Z := 3.
  Definition RK_X : Z := 4.
  Definition RK_Y : Z := 5.
  Definition CMX : Z := 6.
  Definition ENABLE_SPEND : Z := 7.
  Definition ENABLE_OUTPUT : Z := 8.
End PublicInput.

Module FixedBase.
  Definition ValueCommitV : string := "ValueCommitV".
  Definition ValueCommitR : string := "ValueCommitR".
  Definition NullifierK : string := "NullifierK".
  Definition SpendAuthG : string := "SpendAuthG".
  Definition CommitIvkR : string := "CommitIvkR".
  Definition NoteCommitR : string := "NoteCommitR".
End FixedBase.

Module Domain.
  Definition OrchardHashDomains : string := "OrchardHashDomains".
  Definition OrchardCommitDomains : string := "OrchardCommitDomains".
  Definition MerkleCrh : string := "OrchardHashDomains::MerkleCrh".
  Definition NoteCommit : string := "OrchardCommitDomains::NoteCommit".
  Definition CommitIvk : string := "OrchardCommitDomains::CommitIvk".
End Domain.

Definition MERKLE_DEPTH_ORCHARD : Z := 32.
