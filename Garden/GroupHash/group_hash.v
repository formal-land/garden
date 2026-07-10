(** * [GroupHash^P]: the full hash-to-Pallas pipeline

    Composition of the [GroupHash^P] stages (protocol §5.4.9.8, "Group Hash
    into Pallas and Vesta"; [hash_to_curve] in the vendored pasta_curves
    sources, [curves_pallas_excerpt.rs]):

    - [DST = domain_prefix || "-" || "pallas" || "_XMD:BLAKE2b_SSWU_RO_"]
      and [hash_to_field] — two field elements [u_0, u_1] from the BLAKE2b-512
      XMD expansion ([Garden/GroupHash/xmd.v]);
    - [map_to_curve_simple_swu] on each [u_i], onto iso-Pallas
      ([Garden/GroupHash/sswu.v]);
    - addition of the two iso-Pallas points (the complete [Weierstrass.add]
      at [a := a_iso-P]);
    - [iso_map], the degree-3 isogeny to Pallas.  No cofactor clearing
      (Pallas has cofactor 1).

    Two forms.  [group_hash] is self-contained: its square roots are computed
    in place by [field_sqrt] (Tonelli–Shanks) inside
    [Sswu.map_to_curve_simple_swu].  [group_hash_with_witness] takes the two
    [sqrt_ratio] outputs — an is-square flag and a root per [u_i] — as
    untrusted parameters, for certificate use: a checker validates a claimed
    witness pair with [witnesses_ok] (one squaring and one multiplication per
    root, no in-kernel square-root computation) and recomputes everything
    else.  Because [λ_P] is a nonsquare, a valid witness pins the flag, and
    the SSWU sign normalization makes the output independent of the root's
    sign, so a valid witness determines the point [GroupHash^P] specifies.

    The provenance checkers over the Orchard fixed-base generators and
    Sinsemilla [Q] points live in [Orchard/Pallas/generators_provenance.v]
    and [Orchard/Pallas/q_points_provenance.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

(** [field_sqrt] (through [Sswu.map_to_curve_simple_swu]) and [is_square]
    appear in [group_hash]'s body over the concrete Pallas modulus; keep them
    away from the conversion oracle (performance notes, [Strategy opaque]
    rule). *)
Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module GroupHash.
  (** Boolean equality on Weierstrass points (coordinates as reduced
      integers — the pipeline outputs and all compared literals are
      reduced modulo [pallas_p]). *)
  Definition point_eqb (P Q : Weierstrass.point) : bool :=
    match P, Q with
    | Weierstrass.Infinity, Weierstrass.Infinity => true
    | Weierstrass.Affine x1 y1, Weierstrass.Affine x2 y2 =>
        (x1 =? x2) && (y1 =? y2)
    | _, _ => false
    end.

  Lemma point_eqb_eq (P Q : Weierstrass.point) :
    point_eqb P Q = true -> P = Q.
  Proof.
    destruct P as [| x1 y1], Q as [| x2 y2]; cbn; try discriminate.
    - reflexivity.
    - intros Hb. apply andb_prop in Hb as [Hx Hy].
      apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy. congruence.
  Qed.

  (** The witnessed form: [was_square_i]/[root_i] are the claimed
      [sqrt_ratio] outputs for [u_i]; validity is [witnesses_ok] below. *)
  Definition group_hash_with_witness
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : Pallas.point :=
    let '(u0, u1) := Xmd.hash_to_field_pallas domain_prefix msg in
    Sswu.iso_map
      (IsoPallas.add
        (Sswu.map_to_curve_simple_swu_with_root u0 was_square0 root0)
        (Sswu.map_to_curve_simple_swu_with_root u1 was_square1 root1)).

  (** Validity of a witness quadruple: each [(was_square_i, root_i)] pair
      satisfies the [sqrt_ratio] defining equation at [u_i]
      ([Sswu.swu_witness_ok]). *)
  Definition witnesses_ok
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    let '(u0, u1) := Xmd.hash_to_field_pallas domain_prefix msg in
    Sswu.swu_witness_ok u0 was_square0 root0
      && Sswu.swu_witness_ok u1 was_square1 root1.

  (** The self-contained form: square roots computed in place. *)
  Definition group_hash (domain_prefix msg : list Z) : Pallas.point :=
    let '(u0, u1) := Xmd.hash_to_field_pallas domain_prefix msg in
    Sswu.iso_map
      (IsoPallas.add
        (Sswu.map_to_curve_simple_swu u0)
        (Sswu.map_to_curve_simple_swu u1)).
End GroupHash.
