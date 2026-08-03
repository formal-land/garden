(** * Deterministic [Params::new(11)] SRS checker and executable view *)

From Stdlib Require Import ZArith Lists.List Bool.Bool Strings.String Arith.PeanoNat.
Require Import Garden.Prim63.Pasta.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu_vesta.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.GroupHash.sswu_vesta_witness.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.
Local Open Scope Z_scope.

(** Keep the conversion oracle from unfolding the full BLAKE2b/XMD pipeline
    while checking symbolic soundness lemmas.  Closed [vm_compute]
    certificates still evaluate this transparent definition explicitly. *)
Strategy opaque
  [GroupHashVesta.hash_to_field_vesta].

Module VkSrs.
  Import VkProvenanceDataTypes.

  Definition domain_prefix : list Z :=
    Xmd.bytes_of_string "Halo2-Parameters"%string.

  Definition affine_of_words (coordinates : affine_words)
      : VkJacobian.affine :=
    {| VkJacobian.affine_x := coordinates.(x_words);
       VkJacobian.affine_y := coordinates.(y_words) |}.

  Definition expected_point (coordinates : affine_words) : Vesta.point :=
    Vesta.affine
      (PallasQ.to_Z coordinates.(x_words))
      (PallasQ.to_Z coordinates.(y_words)).

  Definition point_from_field_with_witnesses
      (u0 u1 : Z) (entry : srs_entry) : Vesta.point :=
    SswuVestaWitness.group_hash_from_field_with_witness
      u0 u1
      entry.(was_square0) entry.(root0)
      entry.(was_square1) entry.(root1).

  Definition point_with_witnesses (entry : srs_entry) : Vesta.point :=
    let '(u0, u1) :=
      GroupHashVesta.hash_to_field_vesta domain_prefix entry.(message) in
    point_from_field_with_witnesses u0 u1 entry.

  Definition canonical_witnesses_ok_for
      (u0 u1 : Z) (entry : srs_entry) : bool :=
    SswuVestaWitness.canonical_witnesses_ok_for
      u0 u1
      entry.(was_square0) entry.(root0)
      entry.(was_square1) entry.(root1).

  Definition coordinates_canonical (value : affine_words) : bool :=
    PallasQ.equal value.(x_words)
      (PallasQ.from_Z (PallasQ.to_Z value.(x_words)))
      && PallasQ.equal value.(y_words)
        (PallasQ.from_Z (PallasQ.to_Z value.(y_words))).

  Definition check_entry_for
      (u0 u1 : Z) (entry : srs_entry) : bool :=
    coordinates_canonical entry.(coordinates)
      && SswuVestaWitness.canonical_point_eqb
        u0 u1
        entry.(was_square0) entry.(root0)
        entry.(was_square1) entry.(root1)
        (expected_point entry.(coordinates)).

  (** Executable one-pass entry checker.  In particular, the expensive XMD
      hash-to-field computation occurs once; both SSWU witness checks and the
      witnessed point reconstruction consume the resulting [u0]/[u1]. *)
  Definition check_entry (entry : srs_entry) : bool :=
    let '(u0, u1) :=
      GroupHashVesta.hash_to_field_vesta domain_prefix entry.(message) in
    check_entry_for u0 u1 entry.

  Definition check_entries (entries : list srs_entry) : bool :=
    List.forallb check_entry entries.

  Fixpoint bytes_eqb (xs ys : list Z) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => (x =? y) && bytes_eqb xs' ys'
    | _, _ => false
    end.

  Definition index_byte (index divisor : nat) : Z :=
    Z.of_nat ((index / divisor) mod 256).

  (** The exact message schedule in
      [halo2_proofs::poly::commitment::Params::new]:
      [0x00 || LE32(i)] for [g_i], followed by [0x01] and [0x02]. *)
  Definition g_message (index : nat) : list Z :=
    [0; index_byte index 1; index_byte index 256;
        index_byte index 65536; index_byte index 16777216].

  Definition affine_words_eqb (left right : affine_words) : bool :=
    PallasQ.equal left.(x_words) right.(x_words)
      && PallasQ.equal left.(y_words) right.(y_words).

  Fixpoint check_g_entries_from (index : nat) (entries : list srs_entry)
      (coordinates : list affine_words) : bool :=
    match entries, coordinates with
    | [], [] => true
    | entry :: entries, coordinate :: coordinates =>
        bytes_eqb entry.(message) (g_message index)
          && affine_words_eqb entry.(VkProvenanceDataTypes.coordinates)
            coordinate
          && check_entry entry
          && check_g_entries_from (S index) entries coordinates
    | _, _ => false
    end.

  Definition check_g_shard (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) : bool :=
    (List.length entries =? 64)%nat
      && (List.length coordinates =? 64)%nat
      && check_g_entries_from start entries coordinates.

  Definition check_extra_entries (w_entry u_entry : srs_entry)
      (w_coordinates u_coordinates : affine_words) : bool :=
    bytes_eqb w_entry.(message) [1]
      && bytes_eqb u_entry.(message) [2]
      && affine_words_eqb w_entry.(VkProvenanceDataTypes.coordinates)
        w_coordinates
      && affine_words_eqb u_entry.(VkProvenanceDataTypes.coordinates)
        u_coordinates
      && check_entry w_entry && check_entry u_entry.

  Lemma check_entry_for_canonical_witnesses_ok
      (u0 u1 : Z) (entry : srs_entry) :
    check_entry_for u0 u1 entry = true ->
    canonical_witnesses_ok_for u0 u1 entry = true.
  Proof.
    unfold check_entry_for. intros Hcheck.
    apply andb_prop in Hcheck as [_ Hcertified].
    unfold canonical_witnesses_ok_for.
    exact (SswuVestaWitness.canonical_point_eqb_witnesses_ok
      u0 u1
      entry.(was_square0) entry.(root0)
      entry.(was_square1) entry.(root1)
      (expected_point entry.(coordinates)) Hcertified).
  Qed.

  Lemma check_entry_for_coordinates_canonical
      (u0 u1 : Z) (entry : srs_entry) :
    check_entry_for u0 u1 entry = true ->
    coordinates_canonical entry.(coordinates) = true.
  Proof.
    unfold check_entry_for. intros Hcheck.
    apply andb_prop in Hcheck as [Hcanonical _].
    exact Hcanonical.
  Qed.

  Lemma check_entry_for_sound
      (u0 u1 : Z) (entry : srs_entry) :
    check_entry_for u0 u1 entry = true ->
    SswuVestaWitness.group_hash_from_field u0 u1 =
      expected_point entry.(coordinates).
  Proof.
    unfold check_entry_for. intros Hcheck.
    apply andb_prop in Hcheck as [_ Hcertified].
    exact (SswuVestaWitness.canonical_point_eqb_sound
      u0 u1
      entry.(was_square0) entry.(root0)
      entry.(was_square1) entry.(root1)
      (expected_point entry.(coordinates)) Hcertified).
  Qed.

  Lemma check_entry_pair_sound
      (inputs : Z * Z) (entry : srs_entry) :
    (let '(u0, u1) := inputs in check_entry_for u0 u1 entry) = true ->
    (let '(u0, u1) := inputs in
       SswuVestaWitness.group_hash_from_field u0 u1) =
      expected_point entry.(coordinates).
  Proof.
    destruct inputs as [u0 u1].
    apply check_entry_for_sound.
  Qed.

  Lemma check_entry_coordinates_canonical (entry : srs_entry) :
    check_entry entry = true ->
    coordinates_canonical entry.(coordinates) = true.
  Proof.
    unfold check_entry.
    destruct (GroupHashVesta.hash_to_field_vesta
      domain_prefix entry.(message)) as [u0 u1].
    intros Hcheck.
    exact (check_entry_for_coordinates_canonical u0 u1 entry Hcheck).
  Qed.

  (** End-to-end SRS-entry provenance: an accepted entry is the canonical
      [GroupHashVesta.group_hash] point, not merely the witnessed evaluator's
      output. *)
  Lemma check_entry_sound (entry : srs_entry) :
    check_entry entry = true ->
    GroupHashVesta.group_hash domain_prefix entry.(message) =
      expected_point entry.(coordinates).
  Proof.
    intros Hcheck.
    unfold check_entry in Hcheck.
    pose proof
      (check_entry_pair_sound
        (GroupHashVesta.hash_to_field_vesta domain_prefix entry.(message))
        entry Hcheck) as Hsound.
    unfold GroupHashVesta.group_hash.
    unfold SswuVestaWitness.group_hash_from_field in Hsound.
    exact Hsound.
  Qed.

End VkSrs.
