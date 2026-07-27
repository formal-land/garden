(** * Shared fixed-base certificate scaffolding

    The checker definitions and per-entry extraction lemmas shared by the
    per-base certificate files ([circuit_proof/<base>/x_cert.v]
    and [circuit_proof/<base>/sign_cert.v]).  Each is a section over
    the circuit table, the materialised multiple table, the witness data,
    and the window count; the whole-table boolean certificate is a section
    hypothesis stated as the raw [forallb] term, so a per-base file supplies
    only its data and one [vm_compute] and the extraction type-checks
    syntactically against it (a named-constant wrapper around the checker
    would instead send the conversion oracle into lazy-machine evaluation of
    the whole checker).  Every [vm_compute] certificate stays in its
    per-base leaf file; this file proves only abstract lemmas.

    Kept separate from [circuit_proof/table_defs.v] so the heavy
    per-base table leaves ([circuit_proof/<base>/table.v]) depend only
    on the lean builder file and are not invalidated by edits to
    [Field/Sqrt.v] or [Halo2/lemmas.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Field.ListLemmas.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.PallasModel.
Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** ** Shared x-coordinate certificate scaffolding

    Per window [w] and digit [i], the circuit fixed-base table's
    Lagrange-interpolated x-coordinate equals the x-coordinate of the computed
    Weierstrass multiple, read from the table leaf's materialised
    [full_table_reduced] literal.  A per-base certificate file instantiates
    the section at its table and closes the [x_check] hypothesis by one
    [vm_compute]; [x_check_entry] then yields the per-entry fact against the
    builder-form [full_table], rewriting through [full_table_reduced_eq]. *)
Module FixedBaseXCert.
  Section WithTable.
    Variable table : EccSpec.fixed_table.
    Variable default : EccSpec.fixed_window.
    Variable full_table full_table_reduced : list (list Pallas.point).
    Variable windows : nat.

    (** The per-entry x-coordinate agreement of window [w], digit [i].  The
        table side is phrased through [fixed_window_point] (with the
        irrelevant witness [u := 0], since [Point.x] ignores it) so the
        ambient field prime instance matches the one baked into
        [fixed_window_point] in the consuming goal — avoiding a spurious
        [UnOp.from 1] instance mismatch. *)
    Definition check_fn (w i : nat) : bool :=
      Z.eqb
        (Point.x (EccSpec.fixed_window_point (List.nth w table default)
                    (Z.of_nat i) 0))
        (Point.x (PallasModel.repr
           (List.nth i (List.nth w full_table_reduced [])
              Pallas.identity))).

    Hypothesis full_table_reduced_eq : full_table = full_table_reduced.

    (** The whole-table certificate, as the raw [forallb] term. *)
    Hypothesis x_check_true :
      List.forallb (fun w : nat => List.forallb (check_fn w) (List.seq 0 8))
        (List.seq 0 windows) = true.

    (** Per-entry extraction of the x-coordinate agreement. *)
    Lemma x_check_entry (w i : nat) (Hw : (w < windows)%nat) (Hi : (i < 8)%nat) :
      Point.x (EccSpec.fixed_window_point (List.nth w table default) (Z.of_nat i) 0)
      = Point.x (PallasModel.repr
           (List.nth i (List.nth w full_table [])
              Pallas.identity)).
    Proof.
      rewrite full_table_reduced_eq.
      pose proof (forallb_nested_entry check_fn (List.seq 0 windows) (List.seq 0 8)
                    w i x_check_true
                    ltac:(apply in_seq; lia) ltac:(apply in_seq; lia)) as H.
      unfold check_fn in H.
      apply Z.eqb_eq in H.
      exact H.
    Qed.
  End WithTable.
End FixedBaseXCert.

(** ** Shared window-sign (positive QR) certificate scaffolding

    Per window [w] and digit [i], the true Weierstrass multiple's
    y-coordinate, shifted by the window's [fw_z], is a quadratic residue —
    the fact that pins the witnessed window-point sign to the canonical one.
    A per-base certificate file supplies [root_table] (a precomputed modular
    square root of each entry's argument [fw_z w +F Point.y (multiple w i)])
    and closes the [root_check_true] hypothesis by one [vm_compute] of one
    field multiplication per entry over the table leaf's [full_table_reduced]
    literal; [y_check_entry] then reads each [is_square = true] off its root
    witness through [is_square_sq].  The roots' generation is untrusted: were
    any entry not a residue, no root could exist and the checker would return
    [false] — the certificate fails rather than lies. *)
Module FixedBaseSignCert.
  Section WithTable.
    Variable table : EccSpec.fixed_table.
    Variable default : EccSpec.fixed_window.
    Variable full_table full_table_reduced : list (list Pallas.point).
    Variable root_table : list (list Z).
    Variable windows : nat.

    Definition root (w i : nat) : Z :=
      List.nth i (List.nth w root_table []) 0.

    (** The per-entry root-witness check: the entry's root squares to the
        entry's argument [fw_z w +F Point.y (multiple w i)]. *)
    Definition root_check_fn (w i : nat) : bool :=
      Z.eqb
        (root w i *F root w i)
        (UnOp.from
           (EccSpec.fw_z (List.nth w table default)
            +F Point.y
                 (PallasModel.repr
                    (List.nth i (List.nth w full_table_reduced [])
                       Pallas.identity)))).

    Hypothesis full_table_reduced_eq : full_table = full_table_reduced.

    (** The whole-table certificate, as the raw [forallb] term. *)
    Hypothesis root_check_true :
      List.forallb (fun w : nat => List.forallb (root_check_fn w) (List.seq 0 8))
        (List.seq 0 windows) = true.

    (** Per-entry extraction of the positive QR fact, against the builder-form
        [full_table]. *)
    Lemma y_check_entry (w i : nat) (Hw : (w < windows)%nat) (Hi : (i < 8)%nat) :
      is_square
        (UnOp.from
           (EccSpec.fw_z (List.nth w table default)
            +F Point.y
                 (PallasModel.repr
                    (List.nth i (List.nth w full_table [])
                       Pallas.identity)))) = true.
    Proof.
      pose proof (forallb_nested_entry root_check_fn (List.seq 0 windows)
                    (List.seq 0 8) w i root_check_true
                    ltac:(apply in_seq; lia) ltac:(apply in_seq; lia)) as Hr.
      unfold root_check_fn in Hr. apply Z.eqb_eq in Hr.
      rewrite full_table_reduced_eq.
      rewrite <- Hr. apply is_square_sq.
    Qed.
  End WithTable.
End FixedBaseSignCert.
