(** * In-place inverse FFT over the Pallas scalar field

    The transform is specialized to Orchard's 2048-row domain.  Generated
    data supplies a bit-reversal table and the first 1024 inverse powers of
    [omega], all as primitive words.  Eleven unrolled radix-2 stages avoid
    exponentiation and keep every update on the latest primitive-array
    version. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Lists.List Bool.Bool ZArith.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.
Local Open Scope uint63_scope.

Module VkIFFT.
  Module F := PallasP.
  Import Prim63Words.

  Definition size_nat : nat := 2048.

  Definition load_evaluations (evaluation : nat -> Z)
      : PrimArray.array F.t :=
    Prim63Loop.foldi_from size_nat O
      (fun index array =>
        PrimArray.set array (ArrayLinear.index index)
          (F.from_Z (evaluation index)))
      (PrimArray.make ArrayLinear.vector_size F.zero).

  Definition load_field_evaluations (evaluation : nat -> F.t)
      : PrimArray.array F.t :=
    Prim63Loop.foldi_from size_nat O
      (fun index array =>
        PrimArray.set array (ArrayLinear.index index) (evaluation index))
      (PrimArray.make ArrayLinear.vector_size F.zero).

  Definition swap (array : PrimArray.array F.t) (i j : PrimInt63.int)
      : PrimArray.array F.t :=
    if PrimInt63.eqb i j then array else
    let left := PrimArray.get array i in
    let right := PrimArray.get array j in
    PrimArray.set (PrimArray.set array i right) j left.

  Definition bit_reverse (table : PrimArray.array PrimInt63.int)
      (array : PrimArray.array F.t) : PrimArray.array F.t :=
    Prim63Loop.foldi_u63 size_nat 0
      (fun index array =>
        let reversed := PrimArray.get table index in
        if PrimInt63.ltb index reversed then swap array index reversed
        else array)
      array.

  Definition butterfly_step (inverse_roots : PrimArray.array F.t)
      (length half stride index : nat) (array : PrimArray.array F.t)
      : PrimArray.array F.t :=
    let offset := index mod half in
    let base := (index / half) * length in
    let left_index := base + offset in
    let right_index := left_index + half in
    let left := PrimArray.get array (ArrayLinear.index left_index) in
    let right :=
      F.mul (PrimArray.get array (ArrayLinear.index right_index))
        (PrimArray.get inverse_roots (ArrayLinear.index (offset * stride))) in
    PrimArray.set
      (PrimArray.set array (ArrayLinear.index left_index) (F.add left right))
      (ArrayLinear.index right_index) (F.sub left right).

  Definition stage (inverse_roots : PrimArray.array F.t) (length : nat)
      (array : PrimArray.array F.t) : PrimArray.array F.t :=
    let half := length / 2 in
    let stride := size_nat / length in
    Prim63Loop.foldi_from (size_nat / 2) O
      (butterfly_step inverse_roots length half stride) array.

  Definition stages (inverse_roots : PrimArray.array F.t)
      (array : PrimArray.array F.t) : PrimArray.array F.t :=
    let a := stage inverse_roots 2 array in
    let a := stage inverse_roots 4 a in
    let a := stage inverse_roots 8 a in
    let a := stage inverse_roots 16 a in
    let a := stage inverse_roots 32 a in
    let a := stage inverse_roots 64 a in
    let a := stage inverse_roots 128 a in
    let a := stage inverse_roots 256 a in
    let a := stage inverse_roots 512 a in
    let a := stage inverse_roots 1024 a in
    stage inverse_roots 2048 a.

  Definition scale (n_inverse : F.t) (array : PrimArray.array F.t)
      : PrimArray.array F.t :=
    Prim63Loop.foldi_u63 size_nat 0
      (fun index array =>
        PrimArray.set array index (F.mul (PrimArray.get array index) n_inverse))
      array.

  Definition inverse_fft (bit_reverse_table : PrimArray.array PrimInt63.int)
      (inverse_roots : PrimArray.array F.t) (n_inverse : F.t)
      (evaluations : PrimArray.array F.t) : PrimArray.array F.t :=
    scale n_inverse (stages inverse_roots (bit_reverse bit_reverse_table evaluations)).

  Definition standard_coefficients_array (coefficients : list words5)
      : PrimArray.array words5 :=
    VkJacobian.array_of_list zero5 coefficients.

  Definition coefficients_match_array (computed : PrimArray.array F.t)
      (expected : PrimArray.array words5) : bool :=
    Prim63Loop.foldi_u63 size_nat 0
      (fun index ok =>
        ok && F.equal (F.decode (PrimArray.get computed index))
          (PrimArray.get expected index))
      true.

  Definition coefficients_match
      (bit_reverse_table : PrimArray.array PrimInt63.int)
      (inverse_roots : PrimArray.array F.t) (n_inverse : F.t)
      (evaluation : nat -> Z) (coefficients : list words5) : bool :=
    (List.length coefficients =? size_nat)%nat
      && coefficients_match_array
        (inverse_fft bit_reverse_table inverse_roots n_inverse
          (load_evaluations evaluation))
        (standard_coefficients_array coefficients).

  Definition coefficients_match_field
      (bit_reverse_table : PrimArray.array PrimInt63.int)
      (inverse_roots : PrimArray.array F.t) (n_inverse : F.t)
      (evaluation : nat -> F.t) (coefficients : list words5) : bool :=
    (List.length coefficients =? size_nat)%nat
      && coefficients_match_array
        (inverse_fft bit_reverse_table inverse_roots n_inverse
          (load_field_evaluations evaluation))
        (standard_coefficients_array coefficients).

End VkIFFT.
