(** * Generic fixed-base window-table builders

    [FixedBaseTableDefs] hosts the parametric table builders every fixed-base
    table leaf ([circuit_proof/<base>/table.v]) instantiates at its own
    generator — the per-window multiples [[2]B .. [9]B], the window rows, the
    [[8^n] B] octupling, the last-row reconciliation.  Factored out of the
    per-base leaves so they share one upstream definition site and compile in
    parallel ([make -j]).

    This file's dependency closure is kept deliberately small (Weierstrass,
    Pallas, and the generic list lemmas): the per-base table leaves carry
    expensive [vm_compute] certificates, and a lean closure keeps them out of
    the rebuild footprint of the frequently-edited proof-utility files.  The
    shared certificate scaffolding lives in
    [circuit_proof/cert_defs.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Export Garden.Field.ListLemmas.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Import ListNotations.

Global Open Scope Z_scope.

Module FixedBaseTableDefs.
  (** The window radix [8 = 2^3] (mirrors [FixedBaseLadder.window_radix]). *)
  Definition window_radix : Z := 8.

  (** Accumulated per-window offset [sum_{j=0}^{m-1} 2 * 8^j] (mirrors
      [FixedBaseLadder.window_offset_sum]; same Fixpoint, kept local so this
      file does not depend on the ladder). *)
  Fixpoint window_offset_sum (m : nat) : Z :=
    match m with
    | O => 0
    | S m' => 2 * window_radix ^ Z.of_nat m' + window_offset_sum m'
    end.

  (** [[2]B; [3]B; ...; [(k+1)]B] built incrementally from [acc = [2]B] by
      repeated [+ B]. *)
  Fixpoint mults_aux (B acc : Pallas.point) (k : nat) : list Pallas.point :=
    match k with
    | O => []
    | S k' => acc :: mults_aux B (Pallas.add acc B) k'
    end.

  (** The eight window points for a base [B]: [[2]B; [3]B; ...; [9]B].  The 7th
      entry (index 6) is [[8]B], reused as the next window's base. *)
  Definition window_row (B : Pallas.point) : list Pallas.point :=
    mults_aux B (Pallas.add B B) 8.

  (** The first [n] non-last windows starting from base [B]: window [w]'s row is
      [window_row ([8^w] B)], threaded incrementally through [[8]B = nth 6]. *)
  Fixpoint nonlast_points (n : nat) (B : Pallas.point) : list (list Pallas.point) :=
    match n with
    | O => []
    | S n' =>
        let r := window_row B in
        r :: nonlast_points n' (List.nth 6 r Pallas.identity)
    end.

  (** [[8^n] B] by [n] octuplings. *)
  Fixpoint base_pow8 (n : nat) (B : Pallas.point) : Pallas.point :=
    match n with
    | O => B
    | S n' => base_pow8 n' (Pallas.mul 8 B)
    end.

  (** The last window's eight points: [[d * 8^w - C] B = [d] Bw - [C] B] for
      [d = 0..7], with [b84 = [8^w] B] and [c = [C] B]. *)
  Definition last_row (b84 c : Pallas.point) : list Pallas.point :=
    List.map
      (fun d => Pallas.add (Pallas.mul (Z.of_nat d) b84) (Pallas.neg c))
      (List.seq 0 8).
End FixedBaseTableDefs.
