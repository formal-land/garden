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
Require Import Garden.Orchard.vk.provenance.generated.DomainData.

Local Open Scope uint63_scope.

Module VkDomain.
  Module F := PallasP.

  Definition length_is {A : Type} (array : PrimArray.array A)
      (length : PrimInt63.int) : bool :=
    PrimInt63.eqb (PrimArray.length array) length.

  Fixpoint reverse_bits_aux (count : nat) (input output : PrimInt63.int)
      : PrimInt63.int :=
    match count with
    | O => output
    | S count =>
        reverse_bits_aux count (PrimInt63.lsr input 1)
          (PrimInt63.lor (PrimInt63.lsl output 1)
            (PrimInt63.land input 1))
    end.

  Definition reverse_11 (input : PrimInt63.int) : PrimInt63.int :=
    reverse_bits_aux 11 input 0.

  Definition bit_reversal_check : bool :=
    length_is VkDomainData.bit_reversed_array 2048
      && Prim63Loop.foldi_u63 2048 0
        (fun index ok =>
          ok && PrimInt63.eqb
            (PrimArray.get VkDomainData.bit_reversed_array index)
            (reverse_11 index)) true.

  Definition recurrence_state : Set := (bool * F.t)%type.

  Definition powers_check (array : PrimArray.array F.t)
      (length : PrimInt63.int) (count : nat) (ratio : F.t) : bool :=
    length_is array length
      && F.equal (PrimArray.get array 0) F.one
      && fst
        (Prim63Loop.foldi_u63 count 1
          (fun index state =>
            let previous := snd state in
            let current := PrimArray.get array index in
            (fst state && F.equal current (F.mul previous ratio), current))
          (true, PrimArray.get array 0)).

  Definition omega : F.t := F.from_Z PolyDomain.omega.
  Definition delta : F.t := F.from_Z OrchardCompiledAlgebraic.delta.
  Definition inverse_omega : F.t :=
    PrimArray.get VkDomainData.inverse_roots_array 1.

  Definition inverse_roots_check : bool :=
    F.equal (F.mul omega inverse_omega) F.one
      && powers_check VkDomainData.inverse_roots_array 1024 1023 inverse_omega.

  Definition omega_powers_check : bool :=
    powers_check VkDomainData.omega_powers_array 2048 2047 omega.

  Definition delta_powers_check : bool :=
    powers_check VkDomainData.delta_powers_array 15 14 delta.

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
