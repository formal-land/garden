(** * The full hash-to-Vesta pipeline and the Halo2 SRS domain

    Composition of the Vesta [hash_to_curve] stages ([hash_to_curve] in the
    pinned pasta_curves [src/curves.rs], via [src/hashtocurve.rs]):

    - [DST = domain_prefix || "-" || "vesta" || "_XMD:BLAKE2b_SSWU_RO_"]
      and [hash_to_field] — two field elements [u_0, u_1] of [F_{pallas_q}]
      from the BLAKE2b-512 XMD expansion ([Garden/GroupHash/xmd.v], whose
      [hash_to_field] is generic in the modulus and curve id);
    - [map_to_curve_simple_swu] on each [u_i], onto iso-Vesta
      ([Garden/GroupHash/sswu_vesta.v]);
    - addition of the two iso-Vesta points (the complete [Weierstrass.add]
      at [a := a_iso-V]);
    - [iso_map], the degree-3 isogeny to Vesta.  No cofactor clearing
      (Vesta has cofactor 1).

    Two forms, mirroring [Garden/GroupHash/group_hash.v]: [group_hash] is
    self-contained ([field_sqrt] in place); [group_hash_with_witness] takes
    the two [sqrt_ratio] outputs — an is-square flag and a root per [u_i] —
    as untrusted parameters, for certificate use: a checker validates a
    claimed witness pair with [witnesses_ok] (one squaring and one
    multiplication per root, no in-kernel square-root computation) and
    recomputes everything else.  Because [λ_V] is a nonsquare, a valid
    witness pins the flag, and the SSWU sign normalization makes the output
    independent of the root's sign, so a valid witness determines the point.

    The SRS instantiation: Halo2's [Params::<vesta::Affine>::new(k)]
    ([halo2_proofs/src/poly/commitment.rs]) derives its generators with the
    domain prefix ["Halo2-Parameters"] — [g_i] from the 5-byte message
    [[0x00, le32(i)]] and the blind generator [w] from [[0x01]].  The
    per-generator provenance checkers live in
    [Orchard/vk_srs_cert_{0..15}.v] / [Orchard/vk_srs_cert.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Strings.String.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu_vesta.
Require Import Garden.GroupHash.group_hash.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

(** [field_sqrt] (through [SswuVesta.map_to_curve_simple_swu]) and
    [is_square] appear in [group_hash]'s body over the concrete modulus;
    keep them away from the conversion oracle (performance notes,
    [Strategy opaque] rule). *)
Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module GroupHashVesta.
  (** The Vesta curve id of the DST ([Eq::CURVE_ID = "vesta"]). *)
  Definition curve_id_vesta : list Z := Xmd.bytes_of_string "vesta"%string.

  (** [hash_to_field] over the Vesta base field [F_{pallas_q}]. *)
  Definition hash_to_field_vesta (domain_prefix msg : list Z) : Z * Z :=
    Xmd.hash_to_field Primes.pallas_q curve_id_vesta domain_prefix msg.

  (** The witnessed form: [was_square_i]/[root_i] are the claimed
      [sqrt_ratio] outputs for [u_i]; validity is [witnesses_ok] below. *)
  Definition group_hash_with_witness
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : Vesta.point :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu_with_root u0 was_square0 root0)
        (SswuVesta.map_to_curve_simple_swu_with_root u1 was_square1 root1)).

  (** Validity of a witness quadruple: each [(was_square_i, root_i)] pair
      satisfies the [sqrt_ratio] defining equation at [u_i]
      ([SswuVesta.swu_witness_ok]). *)
  Definition witnesses_ok
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.swu_witness_ok u0 was_square0 root0
      && SswuVesta.swu_witness_ok u1 was_square1 root1.

  (** The self-contained form: square roots computed in place. *)
  Definition group_hash (domain_prefix msg : list Z) : Vesta.point :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu u0)
        (SswuVesta.map_to_curve_simple_swu u1)).

  (** ** The Halo2 SRS domain and messages ([Params::new]) *)

  (** The SRS domain prefix (["Halo2-Parameters"],
      [poly/commitment.rs:52,102]). *)
  Definition halo2_parameters_prefix : list Z :=
    Xmd.bytes_of_string "Halo2-Parameters"%string.

  (** The 5-byte message of generator [g_i]: [[0x00, le32(i)]]
      ([commitment.rs:57-58]; valid for [0 <= i < 2^32]). *)
  Definition srs_message (i : Z) : list Z :=
    [0; i mod 256; i / 256 mod 256; i / 65536 mod 256; i / 16777216 mod 256].

  (** The message of the blind generator [w] ([commitment.rs:103]). *)
  Definition w_message : list Z := [1].
End GroupHashVesta.

(** ** Reference vector

    The [test_hash_to_curve] vector committed in the pinned pasta_curves
    checkout's [src/vesta.rs]: [hash_to_curve("z.cash:test")(b"hello")], in
    witnessed form; the expected affine point is the [x/z², y/z³]
    normalization of the Jacobian coordinates the Rust test asserts.  The
    vector is chosen (by the reference implementation) so that the first
    SSWU map takes the non-square branch and the second the square branch,
    and the [b_0] input spans multiple BLAKE2b blocks, so it exercises the
    multi-block chaining, both [sqrt_ratio] branches, the iso-curve
    addition, and [iso_map] end to end over the Vesta DST. *)

Lemma group_hash_vesta_reference_vector_witnesses :
  GroupHashVesta.witnesses_ok
    (Xmd.bytes_of_string "z.cash:test"%string)
    (Xmd.bytes_of_string "hello"%string)
    false
    24408416501631715600243103592971009151617793630368866367062018993049307468795
    true
    6083485149375595409555182314360721691649798757692285245852695945046706376770
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma group_hash_vesta_reference_vector :
  GroupHashVesta.group_hash_with_witness
    (Xmd.bytes_of_string "z.cash:test"%string)
    (Xmd.bytes_of_string "hello"%string)
    false
    24408416501631715600243103592971009151617793630368866367062018993049307468795
    true
    6083485149375595409555182314360721691649798757692285245852695945046706376770
  = Weierstrass.Affine
      21075379713479047553564266640866527200848352330298207685531992063597154177540
      22191108764351731276605087184101827634272305989561712051868454664194139283718.
Proof. vm_compute. reflexivity. Qed.
