(** * Deterministic [Params::new(11)] SRS checker and executable view *)

From Stdlib Require Import ZArith Lists.List Bool.Bool Strings.String Arith.PeanoNat Lia
  Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Field.Field.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu_vesta.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.GroupHash.sswu_vesta_witness.
Require Import Garden.GroupHash.sswu_vesta_words.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.
Local Open Scope Z_scope.

(** This opacity barrier prevents conversion from unfolding the full
    BLAKE2b/XMD pipeline while checking symbolic soundness lemmas. Closed
    [vm_compute] certificates evaluate the transparent definition explicitly. *)
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

  (** Structural normalization is the exact proposition established by the
      executable equality checks.  Keeping this boundary independent of the
      (much larger) Montgomery refinement functor makes every generated SRS
      shard cheap to elaborate; consumers can turn these equalities into
      canonicality once, at the Jacobian refinement boundary. *)
  Definition affine_words_normalized (value : affine_words) : Prop :=
    value.(x_words) =
      PallasQ.from_Z (PallasQ.to_Z value.(x_words)) /\
    value.(y_words) =
      PallasQ.from_Z (PallasQ.to_Z value.(y_words)).

  Definition check_entry_for
      (u0 u1 : Z) (entry : srs_entry) : bool :=
    coordinates_canonical entry.(coordinates)
      && (Vesta.on_curveb (expected_point entry.(coordinates))
        && SswuVestaWitness.canonical_point_eqb
          u0 u1
          entry.(was_square0) entry.(root0)
          entry.(was_square1) entry.(root1)
          (expected_point entry.(coordinates))).

  (** Executable one-pass entry checker.  In particular, the expensive XMD
      hash-to-field computation occurs once; both SSWU witness checks and the
      witnessed point reconstruction consume the resulting [u0]/[u1]. *)
  Definition check_entry (entry : srs_entry) : bool :=
    let '(u0, u1) :=
      GroupHashVesta.hash_to_field_vesta domain_prefix entry.(message) in
    check_entry_for u0 u1 entry.

  (** Montgomery-word evaluation of the same per-entry check.  The XMD
      hash-to-field computation still runs over [Z] bytes; every field
      operation afterwards runs on five-limb [PallasQ] words.
      [check_entry_fast_sound] below transfers acceptance to
      [check_entry], so the certificate lemma surface is unchanged. *)
  Definition check_entry_fast (entry : srs_entry) : bool :=
    let '(u0, u1) :=
      GroupHashVesta.hash_to_field_vesta domain_prefix entry.(message) in
    coordinates_canonical entry.(coordinates)
      && SswuVestaWords.group_hash_checkb_exec u0 u1
        entry.(was_square0) entry.(root0)
        entry.(was_square1) entry.(root1)
        entry.(coordinates).(x_words) entry.(coordinates).(y_words).

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
          && (affine_words_eqb entry.(VkProvenanceDataTypes.coordinates)
              coordinate
            && (check_entry_fast entry
              && check_g_entries_from (S index) entries coordinates))
    | _, _ => false
    end.

  Definition check_g_shard (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) : bool :=
    (List.length entries =? 64)%nat
      && ((List.length coordinates =? 64)%nat
        && check_g_entries_from start entries coordinates).

  Definition check_extra_entries (w_entry u_entry : srs_entry)
      (w_coordinates u_coordinates : affine_words) : bool :=
    bytes_eqb w_entry.(message) [1]
      && (bytes_eqb u_entry.(message) [2]
        && (affine_words_eqb w_entry.(VkProvenanceDataTypes.coordinates)
            w_coordinates
          && (affine_words_eqb u_entry.(VkProvenanceDataTypes.coordinates)
              u_coordinates
            && (check_entry_fast w_entry && check_entry_fast u_entry)))).

  Lemma check_entry_for_canonical_witnesses_ok
      (u0 u1 : Z) (entry : srs_entry) :
    check_entry_for u0 u1 entry = true ->
    canonical_witnesses_ok_for u0 u1 entry = true.
  Proof.
    unfold check_entry_for. intros Hcheck.
    apply andb_prop in Hcheck as [_ Hcheck].
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
    apply andb_prop in Hcheck as [_ Hcheck].
    apply andb_prop in Hcheck as [_ Hcertified].
    exact (SswuVestaWitness.canonical_point_eqb_sound
      u0 u1
      entry.(was_square0) entry.(root0)
      entry.(was_square1) entry.(root1)
      (expected_point entry.(coordinates)) Hcertified).
  Qed.

  Lemma check_entry_for_on_curve
      (u0 u1 : Z) (entry : srs_entry) :
    check_entry_for u0 u1 entry = true ->
    Vesta.on_curve (expected_point entry.(coordinates)).
  Proof.
    unfold check_entry_for. intros Hcheck.
    apply andb_prop in Hcheck as [_ Hcheck].
    apply andb_prop in Hcheck as [Hon_curve _].
    now apply Vesta.on_curveb_sound.
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

  Lemma check_entry_on_curve (entry : srs_entry) :
    check_entry entry = true ->
    Vesta.on_curve (expected_point entry.(coordinates)).
  Proof.
    unfold check_entry.
    destruct (GroupHashVesta.hash_to_field_vesta
      domain_prefix entry.(message)) as [u0 u1].
    apply check_entry_for_on_curve.
  Qed.

  Lemma expected_point_reduced (coordinates : affine_words) :
    Vesta.reduced (expected_point coordinates).
  Proof.
    cbn [expected_point Vesta.affine Vesta.reduced Weierstrass.reduced
      UnOp.from].
    split; apply Z.mod_mod; pose proof Vesta.three_lt_p; lia.
  Qed.

  Lemma check_entry_reduced (entry : srs_entry) :
    check_entry entry = true ->
    Vesta.reduced (expected_point entry.(coordinates)).
  Proof. intros _. apply expected_point_reduced. Qed.

  (** End-to-end SRS-entry provenance: an accepted entry equals the canonical
      [GroupHashVesta.group_hash] point. *)
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

  Lemma bytes_eqb_eq (xs ys : list Z) :
    bytes_eqb xs ys = true -> xs = ys.
  Proof.
    revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn;
      try discriminate; auto.
    intros Hcheck. apply andb_prop in Hcheck as [Hxy Hrest].
    apply Z.eqb_eq in Hxy. f_equal; auto.
  Qed.

  Lemma pallas_q_equal_eq (left right : PallasQ.t) :
    PallasQ.equal left right = true -> left = right.
  Proof.
    destruct left as [l0 l1 l2 l3 l4].
    destruct right as [r0 r1 r2 r3 r4].
    intros Hcheck. unfold PallasQ.equal in Hcheck.
    apply andb_prop in Hcheck as [H0 Hcheck].
    apply andb_prop in Hcheck as [H1 Hcheck].
    apply andb_prop in Hcheck as [H2 Hcheck].
    apply andb_prop in Hcheck as [H3 H4].
    change ((l0 =? r0)%uint63 = true) in H0.
    change ((l1 =? r1)%uint63 = true) in H1.
    change ((l2 =? r2)%uint63 = true) in H2.
    change ((l3 =? r3)%uint63 = true) in H3.
    change ((l4 =? r4)%uint63 = true) in H4.
    apply Uint63.eqb_spec in H0. apply Uint63.eqb_spec in H1.
    apply Uint63.eqb_spec in H2. apply Uint63.eqb_spec in H3.
    apply Uint63.eqb_spec in H4.
    subst. reflexivity.
  Qed.

  Lemma affine_words_eqb_eq (left right : affine_words) :
    affine_words_eqb left right = true -> left = right.
  Proof.
    destruct left as [left_x left_y], right as [right_x right_y].
    cbn [affine_words_eqb x_words y_words]. intros Hcheck.
    apply andb_prop in Hcheck as [Hx Hy].
    change (PallasQ.equal left_x right_x = true) in Hx.
    change (PallasQ.equal left_y right_y = true) in Hy.
    apply pallas_q_equal_eq in Hx. apply pallas_q_equal_eq in Hy.
    subst. reflexivity.
  Qed.

  Lemma coordinates_normalized_sound (value : affine_words) :
    coordinates_canonical value = true ->
    affine_words_normalized value.
  Proof.
    unfold coordinates_canonical, affine_words_normalized.
    intros Hcheck.
    apply andb_prop in Hcheck as [Hx Hy].
    apply pallas_q_equal_eq in Hx.
    apply pallas_q_equal_eq in Hy.
    exact (conj Hx Hy).
  Qed.

  Record entry_refinement
      (expected_message : list Z) (entry : srs_entry)
      (coordinate : affine_words) : Prop := {
    entry_message_exact : entry.(message) = expected_message;
    entry_coordinate_exact : entry.(coordinates) = coordinate;
    entry_group_hash_exact :
      GroupHashVesta.group_hash domain_prefix expected_message =
        expected_point coordinate;
    entry_point_on_curve : Vesta.on_curve (expected_point coordinate);
    entry_point_reduced : Vesta.reduced (expected_point coordinate);
    entry_coordinate_normalized : affine_words_normalized coordinate
  }.

  Lemma checked_entry_refinement
      (expected_message : list Z) (entry : srs_entry)
      (coordinate : affine_words) :
    bytes_eqb entry.(message) expected_message = true ->
    affine_words_eqb entry.(coordinates) coordinate = true ->
    check_entry entry = true ->
    entry_refinement expected_message entry coordinate.
  Proof.
    intros Hmessage Hcoordinate Hentry.
    apply bytes_eqb_eq in Hmessage.
    apply affine_words_eqb_eq in Hcoordinate.
    constructor; try assumption.
    - pose proof (check_entry_sound entry Hentry) as Hsound.
      now rewrite Hmessage, Hcoordinate in Hsound.
    - pose proof (check_entry_on_curve entry Hentry) as Hon_curve.
      now rewrite Hcoordinate in Hon_curve.
    - apply expected_point_reduced.
    - pose proof (check_entry_coordinates_canonical entry Hentry)
        as Hcanonical.
      apply coordinates_normalized_sound in Hcanonical.
      now rewrite Hcoordinate in Hcanonical.
  Qed.

  Lemma coordinates_canonical_words (value : affine_words) :
    coordinates_canonical value = true ->
    PallasQ.canonical value.(x_words) /\ PallasQ.canonical value.(y_words).
  Proof.
    intros Hcheck. apply andb_prop in Hcheck as [Hx Hy].
    apply pallas_q_equal_eq in Hx. apply pallas_q_equal_eq in Hy.
    split; [rewrite Hx | rewrite Hy];
      apply PallasQRefinement.from_Z_canonical.
  Qed.

  Lemma check_entry_fast_sound (entry : srs_entry) :
    check_entry_fast entry = true -> check_entry entry = true.
  Proof.
    unfold check_entry_fast, check_entry.
    destruct (GroupHashVesta.hash_to_field_vesta domain_prefix
      entry.(message)) as [u0 u1].
    intros Hfast. apply andb_prop in Hfast as [Hcanonical Hfast].
    rewrite SswuVestaWords.group_hash_checkb_exec_eq in Hfast.
    pose proof (coordinates_canonical_words _ Hcanonical) as [Hcx Hcy].
    destruct (SswuVestaWords.group_hash_checkb_sound
      u0 u1 entry.(root0) entry.(root1)
      entry.(was_square0) entry.(was_square1)
      entry.(coordinates).(x_words) entry.(coordinates).(y_words)
      Hcx Hcy Hfast) as (Hwitnesses & Hpoint & Hcurve).
    unfold check_entry_for, expected_point.
    rewrite Hcanonical, Hcurve.
    unfold SswuVestaWitness.canonical_point_eqb, canonical_witnesses_ok_for.
    now rewrite Hwitnesses, Hpoint.
  Qed.

  Lemma checked_entry_refinement_fast
      (expected_message : list Z) (entry : srs_entry)
      (coordinate : affine_words) :
    bytes_eqb entry.(message) expected_message = true ->
    affine_words_eqb entry.(coordinates) coordinate = true ->
    check_entry_fast entry = true ->
    entry_refinement expected_message entry coordinate.
  Proof.
    intros Hmessage Hcoordinate Hentry.
    apply checked_entry_refinement; try assumption.
    now apply check_entry_fast_sound.
  Qed.

  Inductive g_entries_refine_from :
      nat -> list srs_entry -> list affine_words -> Prop :=
  | g_entries_refine_nil (index : nat) :
      g_entries_refine_from index [] []
  | g_entries_refine_cons
      (index : nat) (entry : srs_entry) (coordinate : affine_words)
      (entries : list srs_entry) (coordinates : list affine_words) :
      entry_refinement (g_message index) entry coordinate ->
      g_entries_refine_from (S index) entries coordinates ->
      g_entries_refine_from index
        (entry :: entries) (coordinate :: coordinates).

  Lemma check_g_entries_from_sound
      (index : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    check_g_entries_from index entries coordinates = true ->
    g_entries_refine_from index entries coordinates.
  Proof.
    revert index coordinates.
    induction entries as [|entry entries IH]; intros index [|coordinate coordinates];
      cbn [check_g_entries_from]; try discriminate.
    - constructor.
    - intros Hcheck. apply andb_prop in Hcheck as [Hmessage Hcheck].
      apply andb_prop in Hcheck as [Hcoordinate Hcheck].
      apply andb_prop in Hcheck as [Hentry Htail].
      constructor.
      + now apply checked_entry_refinement_fast.
      + now apply IH.
  Qed.

  Record g_shard_refinement
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) : Prop := {
    shard_entries_length : List.length entries = 64%nat;
    shard_coordinates_length : List.length coordinates = 64%nat;
    shard_entries_refine :
      g_entries_refine_from start entries coordinates
  }.

  Lemma check_g_shard_sound
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    check_g_shard start entries coordinates = true ->
    g_shard_refinement start entries coordinates.
  Proof.
    unfold check_g_shard. intros Hcheck.
    apply andb_prop in Hcheck as [Hentries Hcheck].
    apply andb_prop in Hcheck as [Hcoordinates Hrefinement].
    constructor.
    - now apply Nat.eqb_eq.
    - now apply Nat.eqb_eq.
    - now apply check_g_entries_from_sound.
  Qed.

  Lemma g_entries_refine_from_app
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    forall trailing_entries trailing_coordinates,
      g_entries_refine_from (start + List.length entries)
        trailing_entries trailing_coordinates ->
      g_entries_refine_from start
        (entries ++ trailing_entries)
        (coordinates ++ trailing_coordinates).
  Proof.
    intros Hrefinement.
    induction Hrefinement as
      [index | index entry coordinate entries coordinates Hentry Htail IH];
      intros trailing_entries trailing_coordinates Htrailing.
    - cbn in Htrailing |- *. now rewrite Nat.add_0_r in Htrailing.
    - cbn [List.length List.app]. constructor; [exact Hentry |].
      apply IH. cbn in Htrailing.
      replace (index + S (List.length entries))%nat
        with (S index + List.length entries)%nat in Htrailing by lia.
      exact Htrailing.
  Qed.

  Lemma checked_g_shard_cons
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words)
      (trailing_entries : list srs_entry)
      (trailing_coordinates : list affine_words) :
    check_g_shard start entries coordinates = true ->
    g_entries_refine_from (start + 64)%nat
      trailing_entries trailing_coordinates ->
    g_entries_refine_from start
      (entries ++ trailing_entries)
      (coordinates ++ trailing_coordinates).
  Proof.
    intros Hshard Htrailing.
    pose proof (check_g_shard_sound start entries coordinates Hshard)
      as Hrefinement.
    destruct Hrefinement as [Hentries _ Hchecked].
    eapply g_entries_refine_from_app; [exact Hchecked |].
    now rewrite Hentries.
  Qed.

  Lemma checked_g_shard_refines
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    check_g_shard start entries coordinates = true ->
    g_entries_refine_from start entries coordinates.
  Proof.
    intros Hcheck.
    exact (shard_entries_refine start entries coordinates
      (check_g_shard_sound start entries coordinates Hcheck)).
  Qed.

  Definition hash_points_from (start count : nat) : list Vesta.point :=
    List.map
      (fun index =>
        GroupHashVesta.group_hash domain_prefix (g_message index))
      (List.seq start count).

  Definition coordinate_points (coordinates : list affine_words)
      : list Vesta.point :=
    List.map expected_point coordinates.

  Lemma g_entries_refine_from_lengths
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    List.length entries = List.length coordinates.
  Proof. intros H; induction H; cbn; congruence. Qed.

  Lemma g_entries_refine_from_hashes
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    coordinate_points coordinates =
      hash_points_from start (List.length coordinates).
  Proof.
    intros Hrefinement.
    induction Hrefinement as
      [index | index entry coordinate entries coordinates Hentry Htail IH];
      cbn [coordinate_points hash_points_from List.length List.seq List.map].
    - reflexivity.
    - destruct Hentry as [_ _ Hhash _ _ _]. f_equal.
      + symmetry. exact Hhash.
      + exact IH.
  Qed.

  Lemma g_entries_refine_from_on_curve
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    List.Forall Vesta.on_curve (coordinate_points coordinates).
  Proof.
    intros Hrefinement.
    induction Hrefinement as
      [index | index entry coordinate entries coordinates Hentry Htail IH];
      cbn [coordinate_points List.map].
    - constructor.
    - destruct Hentry as [_ _ _ Hon_curve _ _]. constructor; assumption.
  Qed.

  Lemma g_entries_refine_from_reduced
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    List.Forall Vesta.reduced (coordinate_points coordinates).
  Proof.
    intros Hrefinement.
    induction Hrefinement as
      [index | index entry coordinate entries coordinates Hentry Htail IH];
      cbn [coordinate_points List.map].
    - constructor.
    - destruct Hentry as [_ _ _ _ Hreduced _]. constructor; assumption.
  Qed.

  Lemma g_entries_refine_from_normalized
      (start : nat) (entries : list srs_entry)
      (coordinates : list affine_words) :
    g_entries_refine_from start entries coordinates ->
    List.Forall affine_words_normalized coordinates.
  Proof.
    intros Hrefinement.
    induction Hrefinement as
      [index | index entry coordinate entries coordinates Hentry Htail IH].
    - constructor.
    - destruct Hentry as [_ _ _ _ _ Hcanonical].
      constructor; assumption.
  Qed.

  Record extra_entries_refinement
      (w_entry u_entry : srs_entry)
      (w_coordinate u_coordinate : affine_words) : Prop := {
    w_entry_refines : entry_refinement [1] w_entry w_coordinate;
    u_entry_refines : entry_refinement [2] u_entry u_coordinate
  }.

  Lemma check_extra_entries_sound
      (w_entry u_entry : srs_entry)
      (w_coordinate u_coordinate : affine_words) :
    check_extra_entries w_entry u_entry w_coordinate u_coordinate = true ->
    extra_entries_refinement
      w_entry u_entry w_coordinate u_coordinate.
  Proof.
    unfold check_extra_entries. intros Hcheck.
    apply andb_prop in Hcheck as [Hw_message Hcheck].
    apply andb_prop in Hcheck as [Hu_message Hcheck].
    apply andb_prop in Hcheck as [Hw_coordinate Hcheck].
    apply andb_prop in Hcheck as [Hu_coordinate Hcheck].
    apply andb_prop in Hcheck as [Hw_entry Hu_entry].
    constructor; now apply checked_entry_refinement_fast.
  Qed.

End VkSrs.
