(** * Fixed Post-NU6.3 gate, permutation, and lookup evaluation

    This file turns the values read by [Reference.read_plonk_prefix] into the
    vanishing expressions are evaluated in Rust order.  The transparent
    executable layer is split from commitment allocation and query assembly so
    Rocq can serialize it without copying one monolithic environment. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Permutation.
Require Import Garden.Halo2.Verifier.Lookup.
Require Import Garden.Halo2.Verifier.Vanishing.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Reference.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.vk_msm.
Require Import Garden.Orchard.Verifier.PostNu6_3.
Require Import Garden.Orchard.Verifier.AssemblyData.
Require Import Garden.Orchard.Verifier.AssemblyPermutation.
Require Import Garden.Orchard.Verifier.AssemblyLookup.
Require Import Garden.Orchard.Verifier.AssemblyProof.
Require Import Garden.Orchard.Verifier.AssemblyProofExpressions.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.
Definition rotation_values : list Z := [-6; -5; -4; -3; -2; -1; 0].

Definition lagrange_eval (x xn : VerifierField.t) (rotation : Z) : VerifierField.t :=
  let root :=
    match PlonkVerifier.rotate_omega PolyDomain.omega VerifierField.one rotation with
    | Some root => root | None => VerifierField.zero
    end in
  let inverse :=
    match VerifierField.invert (VerifierField.sub x root) with
    | Some inverse => inverse | None => VerifierField.zero
    end in
  let common := VerifierField.mul (VerifierField.sub xn VerifierField.one) VkMsm.n_inv in
  match PlonkVerifier.rotate_omega PolyDomain.omega (VerifierField.mul inverse common) rotation with
  | Some value => value | None => VerifierField.zero
  end.

Definition lagrange_values (x xn : VerifierField.t) : list VerifierField.t :=
  map (lagrange_eval x xn) rotation_values.

Definition l_values (x xn : VerifierField.t) : VerifierField.t * VerifierField.t * VerifierField.t :=
  let values := lagrange_values x xn in
  (nth 6 values VerifierField.zero,
   nth 0 values VerifierField.zero,
   VerifierField.sum (firstn 5 (skipn 1 values))).
