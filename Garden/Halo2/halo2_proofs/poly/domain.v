(** * Evaluation domain helpers used at verify time

    Transcription of [rotate_omega] and [l_i_range] from
    [halo2_proofs/src/poly/domain.rs], specialized to the Pallas-base
    scalar field. [barycentric_weight] is [n^{-1}], the inverted
    [F::from(n)] the Rust constructor writes after the batch invert. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.

Import List.ListNotations.
Global Open Scope Z_scope.

Module EvaluationDomain.

  Record t : Set := {
    n : u64;
    k : u32;
    omega : Z;
    omega_inv : Z;
    quotient_poly_degree : u64;
    barycentric_weight : Z;
  }.

  Definition get_quotient_poly_degree (d : t) : nat :=
    Integer.to_nat d.(quotient_poly_degree).

  Definition pow_omega (base exp : Z) : Z :=
    Fp.pow_vartime base exp.

  Definition rotate_omega (d : t) (value : Z) (rotation : Z) : Z :=
    if 0 <=? rotation then
      value *s pow_omega d.(omega) rotation
    else
      value *s pow_omega d.(omega_inv) (- rotation).

  Definition invert_list (xs : list Z) : list Z :=
    List.map (fun z => match Fp.invert z with Some i => i | None => 0 end) xs.

  (** [l_i_range x xn rotations] evaluates [l_i] at [x] for each rotation
      [i] in [rotations], with [xn = x^n]. *)
  Definition l_i_range (d : t) (x xn : Z) (rotations : list Z) : list Z :=
    let diffs :=
      List.map (fun rot => x -s rotate_omega d 1 rot) rotations in
    let invs := invert_list diffs in
    let common := (xn -s 1) *s d.(barycentric_weight) in
    List.map (fun '(rot, inv) => rotate_omega d (inv *s common) rot)
      (List.combine rotations invs).

  Definition make (k : u32) (omega : Z) (quotient_poly_degree : u64) : t :=
    let n_z := 2 ^ k.(Integer.value) in
    let omega := Fp.from omega in
    let omega_inv :=
      match Fp.invert omega with Some i => i | None => 0 end in
    let barycentric_weight :=
      match Fp.invert n_z with Some i => i | None => 0 end in
    {|
      n := u64_of n_z;
      k := k;
      omega := omega;
      omega_inv := omega_inv;
      quotient_poly_degree := quotient_poly_degree;
      barycentric_weight := barycentric_weight;
    |}.
End EvaluationDomain.
