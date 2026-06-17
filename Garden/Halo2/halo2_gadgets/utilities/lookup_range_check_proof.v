Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module ShortLookupBitshift.
  Record t : Set := {
    shifted_word : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (k word inv_two_pow_s : Z)
      : t := {|
    shifted_word := word *F UnOp.from (2 ^ k) *F inv_two_pow_s;
  |}.
End ShortLookupBitshift.
