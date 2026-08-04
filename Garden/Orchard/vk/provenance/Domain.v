(** * Executable provenance checks for the primitive FFT/domain tables

    [generated/DomainData.v] is an untrusted cache.  The checks below tie
    every cached entry back to the domain constants already used by Garden's
    compiled-system model.  In particular, the inverse-FFT checker cannot be
    made to accept arbitrary coefficients by changing its twiddle table. *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Bool.Bool ZArith.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.

Local Open Scope uint63_scope.

Module VkDomain.
  Module F := PallasP.

  (** High-universe views of the generated primitive arrays.  These are
      definitionally the same runtime values, but keep every array operation
      at the universe where Corelib's array laws are available. *)
  Definition bit_reversed_array : VkIFFT.index_array :=
    VkDomainData.bit_reversed_array.
  Definition inverse_roots_array : VkIFFT.field_array :=
    VkDomainData.inverse_roots_array.
  Definition omega_powers_array : VkIFFT.field_array :=
    VkDomainData.omega_powers_array.
  Definition delta_powers_array : VkIFFT.field_array :=
    VkDomainData.delta_powers_array.

  Definition length_is {A : Set}
      (array : PrimArray.array@{VkIFFT.array_u} A)
      (length : PrimInt63.int) : bool :=
    PrimInt63.eqb
      (PrimArray.length@{VkIFFT.array_u} array) length.

  (** The original executable spelling used primitive shifts and masks.  Keep
      it as an independently executable parity oracle while exposing a
      natural-number spelling whose range and splitting laws can be used by
      the FFT refinement proof. *)
  Fixpoint reverse_bits_aux_primitive
      (count : nat) (input output : PrimInt63.int)
      : PrimInt63.int :=
    match count with
    | O => output
    | S count =>
        reverse_bits_aux_primitive count (PrimInt63.lsr input 1)
          (PrimInt63.lor (PrimInt63.lsl output 1)
            (PrimInt63.land input 1))
    end.

  Fixpoint reverse_nat (count input : nat) : nat :=
    match count with
    | O => O
    | S count =>
        2 * reverse_nat count (input mod (2 ^ count))
          + input / (2 ^ count)
    end.

  Definition reverse_11 (input : PrimInt63.int) : PrimInt63.int :=
    ArrayLinear.index (reverse_nat 11 (ArrayLinear.index_nat input)).

  Definition reverse_11_primitive (input : PrimInt63.int) : PrimInt63.int :=
    reverse_bits_aux_primitive 11 input 0.

  (** Closed parity check for the only input range consumed by the 2048-row
      inverse FFT.  This protects the refactor above independently of the
      generated bit-reversal table. *)
  Definition reverse_11_parity_check : bool :=
    Prim63Loop.foldi_u63 2048 0
      (fun index ok =>
        ok && PrimInt63.eqb (reverse_11 index) (reverse_11_primitive index))
      true.

  Lemma reverse_11_parity_checked : reverse_11_parity_check = true.
  Proof. vm_compute. reflexivity. Qed.

  Definition bit_reversal_check : bool :=
    length_is bit_reversed_array 2048
      && Prim63Loop.foldi_u63 2048 0
        (fun index ok =>
          ok && PrimInt63.eqb
            (PrimArray.get@{VkIFFT.array_u} bit_reversed_array index)
            (reverse_11 index)) true.

  Definition recurrence_state : Set := (bool * F.t)%type.

  Definition powers_check (array : VkIFFT.field_array)
      (length : PrimInt63.int) (count : nat) (ratio : F.t) : bool :=
    length_is array length
      && F.equal (PrimArray.get@{VkIFFT.array_u} array 0) F.one
      && fst
        (Prim63Loop.foldi_u63 count 1
          (fun index state =>
            let previous := snd state in
            let current := PrimArray.get@{VkIFFT.array_u} array index in
            (fst state && F.equal current (F.mul previous ratio), current))
          (true, PrimArray.get@{VkIFFT.array_u} array 0)).

  Definition omega : F.t := F.from_Z PolyDomain.omega.
  Definition delta : F.t := F.from_Z OrchardCompiledAlgebraic.delta.
  Definition inverse_omega : F.t :=
    PrimArray.get@{VkIFFT.array_u} inverse_roots_array 1.

  Definition inverse_roots_check : bool :=
    F.equal (F.mul omega inverse_omega) F.one
      && powers_check inverse_roots_array 1024 1023 inverse_omega.

  Definition omega_powers_check : bool :=
    powers_check omega_powers_array 2048 2047 omega.

  Definition delta_powers_check : bool :=
    powers_check delta_powers_array 15 14 delta.

  Definition n_inverse_check : bool :=
    F.equal (F.mul VkDomainData.n_inverse (F.from_Z 2048%Z)) F.one.

  Record certificate : Prop := {
    bit_reversal_checked : bit_reversal_check = true;
    inverse_roots_checked : inverse_roots_check = true;
    omega_powers_checked : omega_powers_check = true;
    delta_powers_checked : delta_powers_check = true;
    n_inverse_checked : n_inverse_check = true;
  }.
End VkDomain.
