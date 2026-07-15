(** * Generator-blocked shard certificates of the completeness instance

    The four region families whose advice sub-generators are incomplete, so
    their [check_point] certificates compute [false] on the stubbed cells
    and are Admitted pending the sub-generator completion (the C2 assembly
    step).  The failing points are exactly the stubbed-cell rows — every
    other enabled point of these families passes:

    - family 37 ([AddressIntegrity]): the variable-base ladder's boundary
      rows and the overflow z-copies — [(QEccAdd, Mul.VariableBase, 0)],
      [(QMulLsb, Mul.VariableBase, 135)], [(QEccAdd, Mul.VariableBase, 135)]
      and [(QMulOverflow, Mul.OverflowCheck, 1)]; the double-and-add
      interior rows and running sums are left at [0] by [vb_advice_t];
    - family 38 ([Commit^ivk]): [(QCommitIvk, CanonicityGate, 0)] — the
      canonicity-gate row awaits the [b_0]/[b_1]/[b_2]/[d_0]/[d_1]
      decomposition and the [Ak]/[Nk] lookup running sums;
    - families 39/40 (old/new [NoteCommit]): per note, the two y-canonicity
      gate rows [(QNoteCommit*YCanon, YCanonicity _ Gate, 0)] and the four
      input-decomposition rows [(QNoteCommit*Gd, InputGD, 0)],
      [(QNoteCommit*Pkd, InputPkD, 0)], [(QNoteCommit*Rho, InputRho, 0)],
      [(QNoteCommit*Psi, InputPsi, 0)]. *)

Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

Module OrchardCompletenessInstanceShardsBlocked.
  Import OrchardCompletenessInstanceDefs.

  (** [AddressIntegrity]: the variable-base ladder boundary rows. *)
  Lemma shard_37_ok :
    List.forallb check_point (shard_in [37]) = true.
  Admitted.

  (** [Commit^ivk]: the canonicity-gate row. *)
  Lemma shard_38_ok :
    List.forallb check_point (shard_in [38]) = true.
  Admitted.

  (** Old [NoteCommit]: the y-canonicity and input-decomposition rows. *)
  Lemma shard_39_ok :
    List.forallb check_point (shard_in [39]) = true.
  Admitted.

  (** New [NoteCommit]: the y-canonicity and input-decomposition rows. *)
  Lemma shard_40_ok :
    List.forallb check_point (shard_in [40]) = true.
  Admitted.

End OrchardCompletenessInstanceShardsBlocked.
