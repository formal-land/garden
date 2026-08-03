(** * Column names shared by the sharded VK provenance checkers *)

Module VkColumnKinds.
  Inductive column_kind : Set := Fixed | Permutation.
End VkColumnKinds.
