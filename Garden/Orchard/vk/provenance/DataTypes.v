(** * Compact witness-data shapes for Orchard VK provenance *)

From Stdlib Require Import ZArith Lists.List Bool.Bool.
Require Import Garden.Prim63.Words.

Import ListNotations.

Module VkProvenanceDataTypes.
  Import Prim63Words.

  (** A non-identity affine point represented by Montgomery coordinate
      words.  The coordinate field is fixed by the consumer (Vesta/PallasQ). *)
  Record affine_words : Set := {
    x_words : words5;
    y_words : words5;
  }.

  (** Exact Jacobian coordinates.  Unlike [affine_words], this preserves the
      concrete representative produced by the executable Pippenger fold, so
      a shard can export an ordinary Rocq equality rather than merely a
      projective-equivalence test. *)
  Record point_words : Set := {
    jacobian_x_words : words5;
    jacobian_y_words : words5;
    jacobian_z_words : words5;
  }.

  (** One deterministic [Params::new] hash-to-curve entry.  The roots are
      untrusted SSWU square-root witnesses and are checked in the kernel. *)
  Record srs_entry : Set := {
    message : list Z;
    coordinates : affine_words;
    was_square0 : bool;
    root0 : Z;
    was_square1 : bool;
    root1 : Z;
  }.
End VkProvenanceDataTypes.
