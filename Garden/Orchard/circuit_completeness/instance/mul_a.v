(** * Variable-base nondegeneracy certificate: indices [4 .. 39]

    One range of the variable-base mul nondegeneracy check of the concrete
    completeness instance ([mul_step_w], one accumulator multiple per bit
    index); the four ranges compile in parallel and are joined by
    [OrchardCompletenessInstanceDefs.mul_ranges_sound].  They are sized by
    cost rather than by index count — the step at index [i] multiplies by a
    [256 − i]-bit scalar — so this is the shortest of the four. *)

Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Global Open Scope Z_scope.

Module OrchardCompletenessInstanceMulA.
  Import OrchardCompletenessInstanceDefs.

  Lemma mul_range_a_cert :
    List.forallb (mul_step_w test_input) (List.seq 4 36) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceMulA.
