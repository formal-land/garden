Require Export Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

Module RegionId.
  Inductive t : Set :=
  | OfIndex (index : Z).

  Definition of_index (index : Z) : t :=
    OfIndex index.
End RegionId.
