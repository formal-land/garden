(** * Primitive-array Pippenger MSM on Vesta

    Coordinates are five-word radix-[2^63] Montgomery values in the Vesta
    base field.  Scalars are kept as five *standard* words: this lets the
    8-bit window extractor read digits without decoding a Montgomery value
    once per point and window.  The inverse FFT certificate separately checks
    those standard words against the decoded transform output.

    The group formulas are total.  [add] handles identities, equal points and
    inverses explicitly before entering the usual Jacobian formula; [double]
    naturally returns a [Z=0] representative for identity and 2-torsion.
    Projective-to-affine comparison uses cross products and performs no field
    inversion. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Lists.List Bool.Bool.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Montgomery.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.

Import ListNotations.
Local Open Scope uint63_scope.

Module VkJacobian.
  Module F := PallasQ.
  Import Prim63Words.

  Record affine : Set := {
    affine_x : F.t;
    affine_y : F.t;
  }.

  Record point : Set := {
    x : F.t;
    y : F.t;
    z : F.t;
  }.

  Definition identity : point :=
    {| x := F.zero; y := F.one; z := F.zero |}.

  Definition of_affine (p : affine) : point :=
    {| x := p.(affine_x); y := p.(affine_y); z := F.one |}.

  Definition is_identity (p : point) : bool := F.equal p.(z) F.zero.

  Definition twice (a : F.t) : F.t := F.add a a.
  Definition thrice (a : F.t) : F.t := F.add a (twice a).
  Definition eight_times (a : F.t) : F.t := twice (twice (twice a)).

  (** [dbl-2007-bl], specialized to [a=0]. *)
  Definition double (p : point) : point :=
    if is_identity p then identity else
    let xx := F.square p.(x) in
    let yy := F.square p.(y) in
    let yyyy := F.square yy in
    let s := twice (F.sub (F.sub (F.square (F.add p.(x) yy)) xx) yyyy) in
    let m := thrice xx in
    let x3 := F.sub (F.square m) (twice s) in
    let y3 := F.sub (F.mul m (F.sub s x3)) (eight_times yyyy) in
    let z3 := twice (F.mul p.(y) p.(z)) in
    {| x := x3; y := y3; z := z3 |}.

  (** Complete dispatch around [add-2007-bl]. *)
  Definition add (p q : point) : point :=
    if is_identity p then q else
    if is_identity q then p else
    let z1z1 := F.square p.(z) in
    let z2z2 := F.square q.(z) in
    let u1 := F.mul p.(x) z2z2 in
    let u2 := F.mul q.(x) z1z1 in
    let s1 := F.mul p.(y) (F.mul q.(z) z2z2) in
    let s2 := F.mul q.(y) (F.mul p.(z) z1z1) in
    if F.equal u1 u2 then
      if F.equal s1 s2 then double p else identity
    else
      let h := F.sub u2 u1 in
      let i := F.square (twice h) in
      let j := F.mul h i in
      let r := twice (F.sub s2 s1) in
      let v := F.mul u1 i in
      let x3 := F.sub (F.sub (F.square r) j) (twice v) in
      let y3 := F.sub (F.mul r (F.sub v x3)) (twice (F.mul s1 j)) in
      let z3 :=
        F.mul (F.sub (F.sub (F.square (F.add p.(z) q.(z))) z1z1) z2z2) h in
      {| x := x3; y := y3; z := z3 |}.

  Fixpoint double_n (count : nat) (p : point) : point :=
    match count with
    | O => p
    | S count => double_n count (double p)
    end.

  Definition equal (p q : point) : bool :=
    if is_identity p then is_identity q else
    if is_identity q then false else
    let z1z1 := F.square p.(z) in
    let z2z2 := F.square q.(z) in
    F.equal (F.mul p.(x) z2z2) (F.mul q.(x) z1z1)
      && F.equal
        (F.mul p.(y) (F.mul q.(z) z2z2))
        (F.mul q.(y) (F.mul p.(z) z1z1)).

  Definition equal_affine (p : point) (q : affine) : bool :=
    if is_identity p then false else
    let z2 := F.square p.(z) in
    let z3 := F.mul p.(z) z2 in
    F.equal p.(x) (F.mul q.(affine_x) z2)
      && F.equal p.(y) (F.mul q.(affine_y) z3).

  (** ** List-to-array loading

      Generated files stay pleasant to inspect as lists; the heavy path
      immediately loads them into primitive arrays and thereafter threads
      only the latest array version. *)

  Fixpoint load_list_from {A : Type} (values : list A) (index : nat)
      (array : PrimArray.array A) : PrimArray.array A :=
    match values with
    | [] => array
    | value :: values =>
        load_list_from values (S index)
          (PrimArray.set array (ArrayLinear.index index) value)
    end.

  Definition array_of_list {A : Type} (default : A) (values : list A)
      : PrimArray.array A :=
    load_list_from values O
      (PrimArray.make (ArrayLinear.index (List.length values)) default).

  (** ** Window-sharded Pippenger *)

  Definition bucket_step (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) (window index : PrimInt63.int)
      (buckets : PrimArray.array point) : PrimArray.array point :=
    let digit :=
      PallasP.window8_standard (PrimArray.get scalars index) window in
    if PrimInt63.eqb digit 0 then buckets else
    let bucket := PrimInt63.sub digit 1 in
    PrimArray.set buckets bucket
      (add (PrimArray.get buckets bucket)
        (of_affine (PrimArray.get bases index))).

  Definition fill_buckets (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) (window : PrimInt63.int)
      : PrimArray.array point :=
    Prim63Loop.foldi_u63 ArrayLinear.vector_size_nat 0
      (bucket_step scalars bases window)
      (PrimArray.make ArrayLinear.pippenger_bucket_count identity).

  Definition bucket_sum_state : Set := (point * point)%type.

  Definition bucket_sum_step (buckets : PrimArray.array point)
      (ascending_index : PrimInt63.int) (state : bucket_sum_state)
      : bucket_sum_state :=
    let index := PrimInt63.sub 254 ascending_index in
    let running := add (fst state) (PrimArray.get buckets index) in
    (running, add (snd state) running).

  Definition window_sum (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) (window : PrimInt63.int) : point :=
    snd
      (Prim63Loop.foldi_u63 ArrayLinear.pippenger_bucket_count_nat 0
        (bucket_sum_step (fill_buckets scalars bases window))
        (identity, identity)).

  Definition window_range_step (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) (range_start range_count index : nat)
      (acc : point) : point :=
    let descending := range_start + range_count - 1 - index in
    add (double_n ArrayLinear.pippenger_window_bits_nat acc)
      (window_sum scalars bases (ArrayLinear.index descending)).

  Definition window_range (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) (range_start range_count : nat)
      : point :=
    Prim63Loop.foldi_from range_count O
      (window_range_step scalars bases range_start range_count) identity.

  Definition low_half (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) : point :=
    window_range scalars bases 0 16.

  Definition high_half (scalars : PrimArray.array words5)
      (bases : PrimArray.array affine) : point :=
    window_range scalars bases 16 16.

  Definition assemble_halves (low high : point) (w : affine) : point :=
    add (add low (double_n 128 high)) (of_affine w).

End VkJacobian.
