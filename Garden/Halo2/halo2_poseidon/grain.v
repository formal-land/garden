(** * Grain LFSR in self-shrinking mode, and Cauchy MDS generation

    Executable transcription of the Poseidon parameter-generation pipeline
    vendored in this directory, mirrored function-for-function so it can be
    audited side by side with the Rust sources:

    - [Grain]: [grain.rs] — the 80-bit Grain LFSR in self-shrinking mode
      (state in [Msb0] bit order, 6-tap feedback [62^51^38^23^13^0], seeded
      with the field-type/S-box tags and the [num_bits]/[t]/[R_F]/[R_P]
      parameters, then 160 discarded bits), with [next_field_element]
      (rejection sampling against the field modulus) and
      [next_field_element_without_rejection] (reduction of the raw bit
      string modulo the field order, the [from_uniform_bytes] path);
    - [Mds]: [mds.rs] — the Cauchy matrix [a_ij = 1/(x_i + y_j)] over two
      Grain-sampled arrays [xs], [ys] of unique elements, and its inverse
      via Lagrange polynomials (Schechter 1959, Theorem 1, adapted to the
      positive formulation by negating [ys]);
    - [Generation.generate_constants]: [lib.rs] [generate_constants] — the
      round-constant sequence ([R_F + R_P] rows of [t] rejection-sampled
      elements) followed by the MDS pair drawn from the same Grain state.

    Field elements are plain [Z] residues modulo a prime [p] passed
    explicitly; the LFSR state is a [list bool] indexed exactly like the
    Rust [BitArr!(for 80, in u8, Msb0)] (index 0 is the Rust index 0).
    Unbounded Rust loops — the self-shrinking iterator, rejection sampling,
    and the unique-sample/secure-MDS selection loop — take explicit fuel
    and return [option]: callers instantiate the fuel large enough for the
    concrete run, and a checker consuming the output fails if any fuel runs
    out.  Modular inversion is [mod_inverse] (extended Euclid,
    [Garden.Field.Field]), the same inverse the circuit semantics uses. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Field.Field.

Import ListNotations.

Global Open Scope Z_scope.

Module Grain.
  (** [STATE] in [grain.rs]: the LFSR is 80 bits wide. *)
  Definition state_bits : nat := 80.

  (** [FieldType::PrimeOrder.tag()]. *)
  Definition field_type_prime_order_tag : Z := 1.

  (** [SboxType::Pow.tag()] ([x^alpha]). *)
  Definition sbox_pow_tag : Z := 0.

  (** [Grain<F>]: the 80 state bits in [Msb0] order plus the read cursor
      [next_bit] (an index into [state]; [state_bits] means "no unread
      bits"). *)
  Record t : Set := {
    state : list bool;
    next_bit : nat;
  }.

  (** Functional update of position [i] of a list (out-of-range writes are
      dropped, matching in-bounds Rust indexing on the 80-bit array). *)
  Fixpoint list_set {A : Set} (l : list A) (i : nat) (v : A) : list A :=
    match l, i with
    | [], _ => []
    | _ :: rest, O => v :: rest
    | b :: rest, S i => b :: list_set rest i v
    end.

  (** The [set_bits] closure of [Grain::new]: write the [len] low bits of
      [value] at [offset..offset+len] in MSB-first order
      ([state[offset + len - 1 - i] = (value >> i) & 1]). *)
  Definition set_bits (st : list bool) (offset len : nat) (value : Z) :
      list bool :=
    List.fold_left
      (fun st i =>
        list_set st (offset + len - 1 - i)%nat (Z.testbit value (Z.of_nat i)))
      (List.seq 0 len)
      st.

  (** The 6-tap feedback [state[i+62] ^ state[i+51] ^ state[i+38] ^
      state[i+23] ^ state[i+13] ^ state[i]] of [load_next_8_bits]. *)
  Definition feedback_bit (st : list bool) (i : nat) : bool :=
    xorb
      (xorb
        (xorb
          (xorb
            (xorb (nth (i + 62)%nat st false) (nth (i + 51)%nat st false))
            (nth (i + 38)%nat st false))
          (nth (i + 23)%nat st false))
        (nth (i + 13)%nat st false))
      (nth i st false).

  (** [Grain::load_next_8_bits]: compute the eight feedback bits from the
      current state, rotate the state left by 8, move the cursor back by 8,
      and write the new bits at the cursor (bit [i] of the [new_bits] byte
      lands at [next_bit + i]). *)
  Definition load_next_8_bits (g : t) : t :=
    let new_bits := List.map (feedback_bit g.(state)) (List.seq 0 8) in
    let rotated := List.skipn 8 g.(state) ++ List.firstn 8 g.(state) in
    let cursor := (g.(next_bit) - 8)%nat in
    let st :=
      List.fold_left
        (fun st i => list_set st (cursor + i)%nat (nth i new_bits false))
        (List.seq 0 8)
        rotated in
    {| state := st; next_bit := cursor |}.

  (** [Grain::new]: all-ones state, the six seeded parameter fields in MSB
      order (field-type tag, S-box tag, [num_bits], [t], [R_F], [R_P]),
      then 160 discarded bits (20 byte loads with the cursor reset). *)
  Definition new (sbox_tag arity r_f r_p num_bits : Z) : t :=
    let st := List.repeat true state_bits in
    let st := set_bits st 0 2 field_type_prime_order_tag in
    let st := set_bits st 2 4 sbox_tag in
    let st := set_bits st 6 12 num_bits in
    let st := set_bits st 18 12 arity in
    let st := set_bits st 30 10 r_f in
    let st := set_bits st 40 10 r_p in
    let g := {| state := st; next_bit := state_bits |} in
    List.fold_left
      (fun g _ =>
        let g := load_next_8_bits g in
        {| state := g.(state); next_bit := state_bits |})
      (List.seq 0 20)
      g.

  (** [Grain::get_next_bit]: reload eight bits when the cursor is
      exhausted, then read the bit under the cursor and advance it. *)
  Definition get_next_bit (g : t) : bool * t :=
    let g :=
      if Nat.eqb g.(next_bit) state_bits then load_next_8_bits g else g in
    (nth g.(next_bit) g.(state) false,
     {| state := g.(state); next_bit := S g.(next_bit) |}).

  (** [Iterator::next] (self-shrinking): evaluate raw bits in pairs — a
      pair starting with 1 outputs its second bit, a pair starting with 0
      is discarded.  [fuel] bounds the number of discarded pairs. *)
  Fixpoint next (fuel : nat) (g : t) : option (bool * t) :=
    match fuel with
    | O => None
    | S fuel =>
      let '(b, g) := get_next_bit g in
      if b then
        Some (get_next_bit g)
      else
        let '(_, g) := get_next_bit g in
        next fuel g
    end.

  (** [self.take(n)]: the next [n] self-shrunken bits, first bit first. *)
  Fixpoint take (bit_fuel n : nat) (g : t) : option (list bool * t) :=
    match n with
    | O => Some ([], g)
    | S n =>
      match next bit_fuel g with
      | None => None
      | Some (b, g) =>
        match take bit_fuel n g with
        | None => None
        | Some (bits, g) => Some (b :: bits, g)
        end
      end
    end.

  (** The bit-to-integer assembly shared by both sampling modes: bit [i] of
      the stream is written at repr position [num_bits - 1 - i], and the
      little-endian repr is read back as an integer — so the first stream
      bit is the most significant. *)
  Definition bits_to_repr (bits : list bool) : Z :=
    List.fold_left
      (fun (acc : Z) (b : bool) => 2 * acc + (if b then 1 else 0)) bits 0.

  (** [Grain::next_field_element]: take [num_bits] shrunken bits and accept
      the value when it is a canonical representative ([< p], the
      [from_repr_vartime] check); otherwise resample.  [attempt_fuel]
      bounds the rejection loop. *)
  Fixpoint next_field_element (attempt_fuel : nat) (bit_fuel num_bits : nat)
      (p : Z) (g : t) : option (Z * t) :=
    match attempt_fuel with
    | O => None
    | S attempt_fuel =>
      match take bit_fuel num_bits g with
      | None => None
      | Some (bits, g) =>
        let v := bits_to_repr bits in
        if v <? p then Some (v, g)
        else next_field_element attempt_fuel bit_fuel num_bits p g
      end
    end.

  (** [Grain::next_field_element_without_rejection]: the same [num_bits]
      bits assembled into a 64-byte buffer and reduced through
      [from_uniform_bytes] — only positions [0..num_bits] are populated, so
      the result is the assembled integer modulo [p]. *)
  Definition next_field_element_without_rejection (bit_fuel num_bits : nat)
      (p : Z) (g : t) : option (Z * t) :=
    match take bit_fuel num_bits g with
    | None => None
    | Some (bits, g) => Some ((bits_to_repr bits) mod p, g)
    end.
End Grain.

Module Mds.
  (** Field helpers over the explicit modulus: [Z.modulo] keeps residues in
      [0, p). *)
  Definition fadd (p x y : Z) : Z := (x + y) mod p.
  Definition fsub (p x y : Z) : Z := (x - y) mod p.
  Definition fmul (p x y : Z) : Z := (x * y) mod p.
  Definition fneg (p x : Z) : Z := (- x) mod p.

  (** The uniqueness check of [generate_mds] (Rust sorts and deduplicates;
      pairwise distinctness is the same condition). *)
  Fixpoint all_distinct (l : list Z) : bool :=
    match l with
    | [] => true
    | x :: rest => negb (List.existsb (Z.eqb x) rest) && all_distinct rest
    end.

  (** [2*T] elements sampled with [next_field_element_without_rejection]. *)
  Fixpoint sample_vals (count : nat) (bit_fuel num_bits : nat) (p : Z)
      (g : Grain.t) : option (list Z * Grain.t) :=
    match count with
    | O => Some ([], g)
    | S count =>
      match Grain.next_field_element_without_rejection bit_fuel num_bits p g
      with
      | None => None
      | Some (v, g) =>
        match sample_vals count bit_fuel num_bits p g with
        | None => None
        | Some (vs, g) => Some (v :: vs, g)
        end
      end
    end.

  (** The sampling loop of [generate_mds]: resample until the [2*T] values
      are unique (without consuming [select]); each unique sample with
      [select <> 0] decrements the secure-MDS selection counter and
      resamples; the sample reached at [select = 0] is split into
      [(xs, ys)].  [loop_fuel] bounds the resampling. *)
  Fixpoint generate_xs_ys (loop_fuel select : nat)
      (width bit_fuel num_bits : nat) (p : Z) (g : Grain.t) :
      option ((list Z * list Z) * Grain.t) :=
    match loop_fuel with
    | O => None
    | S loop_fuel =>
      match sample_vals (2 * width)%nat bit_fuel num_bits p g with
      | None => None
      | Some (vals, g) =>
        if all_distinct vals then
          match select with
          | O => Some ((List.firstn width vals, List.skipn width vals), g)
          | S select =>
            generate_xs_ys loop_fuel select width bit_fuel num_bits p g
          end
        else generate_xs_ys loop_fuel select width bit_fuel num_bits p g
      end
    end.

  (** The [assert!(!sum.is_zero_vartime())] guard: every Cauchy denominator
      [x_i + y_j] is nonzero. *)
  Definition cauchy_sums_nonzero (p : Z) (width : nat) (xs ys : list Z) :
      bool :=
    List.forallb
      (fun i =>
        List.forallb
          (fun j => negb (fadd p (nth i xs 0) (nth j ys 0) =? 0))
          (List.seq 0 width))
      (List.seq 0 width).

  (** The Cauchy matrix [mds[i][j] = (x_i + y_j)^{-1}]. *)
  Definition cauchy_matrix (p : Z) (width : nat) (xs ys : list Z) :
      list (list Z) :=
    List.map
      (fun i =>
        List.map
          (fun j => mod_inverse (fadd p (nth i xs 0) (nth j ys 0)) p)
          (List.seq 0 width))
      (List.seq 0 width).

  (** The Lagrange-polynomial fold [l(zs, j, x)]: the product over [m <> j]
      of [(x - z_m) / (z_j - z_m)]. *)
  Definition lagrange (p : Z) (zs : list Z) (j : nat) (x : Z) : Z :=
    List.fold_left
      (fun acc m =>
        if Nat.eqb m j then acc
        else
          let z_m := nth m zs 0 in
          fmul p (fmul p acc (fsub p x z_m))
            (mod_inverse (fsub p (nth j zs 0) z_m) p))
      (List.seq 0 (List.length zs))
      1.

  (** The inverse matrix [mds_inv[i][j] = (x_j - y'_i) * l(xs, j, y'_i) *
      l(ys', i, x_j)] over the negated array [ys' = map (-) ys]. *)
  Definition mds_inv_matrix (p : Z) (width : nat) (xs ys : list Z) :
      list (list Z) :=
    let neg_ys := List.map (fneg p) ys in
    List.map
      (fun i =>
        List.map
          (fun j =>
            fmul p
              (fmul p
                (fsub p (nth j xs 0) (nth i neg_ys 0))
                (lagrange p xs j (nth i neg_ys 0)))
              (lagrange p neg_ys i (nth j xs 0)))
          (List.seq 0 width))
      (List.seq 0 width).

  (** [generate_mds]: the sampled [(xs, ys)] at selection counter [select],
      the Cauchy matrix, and its Lagrange inverse.  Fails (like the Rust
      assert) if some denominator [x_i + y_j] vanishes. *)
  Definition generate_mds (loop_fuel select : nat)
      (width bit_fuel num_bits : nat) (p : Z) (g : Grain.t) :
      option ((list (list Z) * list (list Z)) * Grain.t) :=
    match generate_xs_ys loop_fuel select width bit_fuel num_bits p g with
    | None => None
    | Some ((xs, ys), g) =>
      if cauchy_sums_nonzero p width xs ys then
        Some ((cauchy_matrix p width xs ys, mds_inv_matrix p width xs ys), g)
      else None
    end.
End Mds.

Module Generation.
  (** One row of [t] rejection-sampled round constants. *)
  Fixpoint round_constant_row (width : nat)
      (attempt_fuel bit_fuel num_bits : nat) (p : Z) (g : Grain.t) :
      option (list Z * Grain.t) :=
    match width with
    | O => Some ([], g)
    | S width =>
      match Grain.next_field_element attempt_fuel bit_fuel num_bits p g with
      | None => None
      | Some (v, g) =>
        match round_constant_row width attempt_fuel bit_fuel num_bits p g
        with
        | None => None
        | Some (vs, g) => Some (v :: vs, g)
        end
      end
    end.

  (** The [R_F + R_P] rows of round constants of [generate_constants]. *)
  Fixpoint round_constant_rows (rounds width : nat)
      (attempt_fuel bit_fuel num_bits : nat) (p : Z) (g : Grain.t) :
      option (list (list Z) * Grain.t) :=
    match rounds with
    | O => Some ([], g)
    | S rounds =>
      match round_constant_row width attempt_fuel bit_fuel num_bits p g with
      | None => None
      | Some (row, g) =>
        match
          round_constant_rows rounds width attempt_fuel bit_fuel num_bits p g
        with
        | None => None
        | Some (rows, g) => Some (row :: rows, g)
        end
      end
    end.

  (** [lib.rs] [generate_constants]: a fresh Grain instance seeded with
      [(SboxType::Pow, t, R_F, R_P)], the [(R_F + R_P) x t] round-constant
      matrix, then the MDS pair from the continued Grain state at
      secure-MDS index [secure_mds]. *)
  Definition generate_constants
      (loop_fuel attempt_fuel bit_fuel secure_mds : nat)
      (arity r_f r_p num_bits p : Z) :
      option (list (list Z) * (list (list Z) * list (list Z))) :=
    let g := Grain.new Grain.sbox_pow_tag arity r_f r_p num_bits in
    match
      round_constant_rows (Z.to_nat (r_f + r_p)) (Z.to_nat arity)
        attempt_fuel bit_fuel (Z.to_nat num_bits) p g
    with
    | None => None
    | Some (rc, g) =>
      match
        Mds.generate_mds loop_fuel secure_mds (Z.to_nat arity) bit_fuel
          (Z.to_nat num_bits) p g
      with
      | None => None
      | Some (mats, _) => Some (rc, mats)
      end
    end.
End Generation.
