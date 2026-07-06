Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.

(** * The per-window quadratic-residue discriminant [window_disc]

    Wave-0 keystone of the [action_spec_us_free] / [spend_auth_g_full_window_correct]
    track (see [docs/action-spec-us-free.md]).  A fixed-base window point has its
    x fixed by Lagrange interpolation and recovers [y] as [u^2 - z] from a
    witnessed square root [u].  Both on-curve roots [+/-Y] satisfy [Y^2 = x^3 + b];
    the [z]-table's quadratic-residue branch selects the unique root with
    [y + z] a square.  The finite obligation that makes this selection
    unambiguous — that not both [+/-Y + z] are squares — is discharged, per
    window/digit, by the boolean

      [is_square (window_disc w digit) = false].

    Here [window_disc w digit = z^2 - (x^3 + b)] is the discriminant
    [(r + z)(z - r)] where [r] is either on-curve root, so [r^2 = x^3 + b].  With
    [is_square (z - r) = is_square (u^2) = true] and QR-multiplicativity,
    [is_square (window_disc) = false] forces [is_square (r + z) = false], which
    is exactly what pins the witnessed sign to the canonical one.  It is
    computable directly from the concrete coeffs, [z], and digit (one [modpow],
    no Tonelli-Shanks in the certificate).

    This file holds ONLY [window_disc] and the pinned certificate shapes, and
    depends only on [ecc/chip/spec.v], [ecc/chip/constants.v], [Field/Field.v]
    and [Field/Sqrt.v] — NOT on [fixed_window_canonical.v] — so the certificate
    lanes (C, F-cert) can depend on a stable [window_disc.vo] that the forcing
    lemma's lane (B, in [fixed_window_canonical.v]) never edits. *)

#[local] Existing Instance Primes.PallasPIsPrime.
Global Open Scope Z_scope.

(** The per-window discriminant [z^2 - (x^3 + b)], where [x] is the window's
    interpolated x-coordinate and [b = pallas_b].  Equal to [(r + z)(z - r)] for
    any on-curve root [r] (with [r^2 = x^3 + b]). *)
Definition window_disc (w : EccSpec.fixed_window) (digit : Z) : Z :=
  let x := EccSpec.fixed_interp (EccSpec.fw_coeffs w) digit (UnOp.from 1) in
  UnOp.from (EccSpec.fw_z w *F EccSpec.fw_z w -F (x *F x *F x +F UnOp.from pallas_b)).

(** ** Pinned certificate shapes

    Fixing the exact terms up front decouples the forcing lemma (lane B) from the
    certificate lanes: lane B takes [Hdisc] as a hypothesis, and the certificate
    lanes produce it per concrete window/digit. *)

(** [Hdisc] shape (lane C — the negative discriminant certificate).  Lane C
    instantiates [w := List.nth k (EccSpec.fixed_table_of_rows <rows>) w0] and
    [digit := d], and discharges this by [vm_compute] for every [(window, digit)]
    across the five fixed-base tables.  A successful certificate also implies
    [window_disc w digit <> 0] (since [is_square 0 = true]), so the [disc = 0]
    edge needs no separate handling. *)
Definition Hdisc_shape (w : EccSpec.fixed_window) (digit : Z) : Prop :=
  is_square (window_disc w digit) = false.

(** F-cert shape (lane F — the positive spend_auth_g QR certificate).  Because
    this file may not depend on the Weierstrass / Pallas theory or the ladder's
    [window_scalar], the F-cert term is pinned here only as a comment; lane F
    (in [circuit_proof_spend_auth_g_window_sign_cert.v]) states it against
    [SpendAuthGFixedWindowCert.full_table], whose entries are definitionally the
    multiples
    [PallasModel.repr
      (Pallas.mul (window_scalar 85 w d) PallasGenerators.spend_auth_g_G)]:

      is_square
        (UnOp.from
          (EccSpec.fw_z <window> +F
            Point.y (PallasModel.repr
              (Pallas.mul (FixedBaseLadder.window_scalar 85 w d)
                PallasGenerators.spend_auth_g_G)))) = true

    where [<window> = List.nth w OrchardActionFixedBase.spend_auth_g_fixed_table
    OrchardActionFixedBase.fixed_window_default].  It is the [Hqr] that turns
    [window_y_forced_of_disc] into "canonical = multiple" for the RK path.  The
    F-cert side ranges over the spend_auth_g table only; its multiples are
    already materialised in [SpendAuthGFixedWindowCert.full_table] (the x-cert's
    table), so it reuses that table rather than recomputing. *)
