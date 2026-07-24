(** * Entry shape of the Halo2 Vesta SRS literal tables

    One entry per SRS generator: the index, the two [sqrt_ratio] witnesses
    (an is-square flag and a root per [hash_to_field] output), and the affine
    coordinates — [(i, was_square0, root0, was_square1, root1, x, y)].  The
    applicative constructor [E] keeps the pasted tables
    ([Orchard/vk_srs_data_{0..15}.v]) cheap to elaborate: each argument is
    checked against a fixed expected type, with no per-entry unification
    through the nested pair notation. *)

Require Import Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

Module VkSrsEntry.
  Definition t : Set := (Z * bool * Z * bool * Z * Z * Z)%type.

  Definition E (i : Z) (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) (x y : Z) : t :=
    (i, was_square0, root0, was_square1, root1, x, y).

  (** The entry's SRS index. *)
  Definition index (e : t) : Z :=
    let '(i, _, _, _, _, _, _) := e in i.

  (** The entry's affine coordinate pair. *)
  Definition point (e : t) : Z * Z :=
    let '(_, _, _, _, _, x, y) := e in (x, y).
End VkSrsEntry.
