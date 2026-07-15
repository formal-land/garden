(** * Variable-base nondegeneracy certificate: indices [4 .. 66]

    One range of the variable-base mul nondegeneracy check of the concrete
    completeness instance ([mul_step_b], one accumulator multiple per bit
    index); the four ranges compile in parallel and are joined by
    [OrchardCompletenessInstanceDefs.mul_ranges_sound]. *)

Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Global Open Scope Z_scope.

Module OrchardCompletenessInstanceMulA.
  Import OrchardCompletenessInstanceDefs.

  Lemma mul_range_a_cert :
    List.forallb (mul_step_b test_input) (List.seq 4 63) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceMulA.
