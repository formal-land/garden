(** * [GroupHash^V]: the full hash-to-Vesta pipeline *)

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

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module GroupHashVesta.
  Definition curve_id_vesta : list Z := Xmd.bytes_of_string "vesta"%string.

  Definition hash_to_field_vesta
      (domain_prefix msg : list Z) : Z * Z :=
    Xmd.hash_to_field Primes.pallas_q curve_id_vesta domain_prefix msg.

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

  Definition group_hash_with_witness
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : Vesta.point :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu_with_root
           u0 was_square0 root0)
        (SswuVesta.map_to_curve_simple_swu_with_root
           u1 was_square1 root1)).

  Definition witnesses_ok
      (domain_prefix msg : list Z)
      (was_square0 : bool) (root0 : Z)
      (was_square1 : bool) (root1 : Z) : bool :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.swu_witness_ok u0 was_square0 root0
      && SswuVesta.swu_witness_ok u1 was_square1 root1.

  Definition group_hash (domain_prefix msg : list Z) : Vesta.point :=
    let '(u0, u1) := hash_to_field_vesta domain_prefix msg in
    SswuVesta.iso_map
      (IsoVesta.add
        (SswuVesta.map_to_curve_simple_swu u0)
        (SswuVesta.map_to_curve_simple_swu u1)).
End GroupHashVesta.

(** Affine form of [pasta_curves::vesta::test_hash_to_curve].  The Rust
    fixture records the same point in Jacobian coordinates. *)
Lemma group_hash_vesta_reference_vector :
  GroupHashVesta.group_hash
    (Xmd.bytes_of_string "z.cash:test"%string)
    (Xmd.bytes_of_string "hello"%string) =
  Weierstrass.Affine
    21075379713479047553564266640866527200848352330298207685531992063597154177540
    22191108764351731276605087184101827634272305989561712051868454664194139283718.
Proof. vm_compute. reflexivity. Qed.
