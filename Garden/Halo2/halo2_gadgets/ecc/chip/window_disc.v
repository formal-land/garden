Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.ListLemmas.
Require Import Garden.Field.Sqrt.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

(** * The per-window quadratic-residue discriminant [window_disc]

    The discriminant whose non-squareness pins the witnessed window-point sign
    in the fixed-base ladders, consumed by the forcing lemma
    [window_y_forced_of_disc] ([fixed_window_canonical.v]) and, through it, by
    the ladder correctness lemmas such as [spend_auth_g_full_window_correct].
    A fixed-base window point has its
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
    and [Field/Sqrt.v] — NOT on [fixed_window_canonical.v] — so the per-table
    certificate files depend on a stable [window_disc.vo] that edits to the
    forcing lemma in [fixed_window_canonical.v] never invalidate. *)

#[local] Existing Instance Primes.PallasPIsPrime.
Global Open Scope Z_scope.

(** The per-window discriminant [z^2 - (x^3 + b)], where [x] is the window's
    interpolated x-coordinate and [b = pallas_b].  Equal to [(r + z)(z - r)] for
    any on-curve root [r] (with [r^2 = x^3 + b]). *)
Definition window_disc (w : EccSpec.fixed_window) (digit : Z) : Z :=
  let x := EccSpec.fixed_interp (EccSpec.fw_coeffs w) digit (UnOp.from 1) in
  UnOp.from (EccSpec.fw_z w *F EccSpec.fw_z w -F (x *F x *F x +F UnOp.from pallas_b)).

(** ** Pinned certificate shapes

    Fixing the exact terms up front decouples the forcing lemma from the
    certificate files: [window_y_forced_of_disc] takes [Hdisc] as a hypothesis,
    and the per-table certificate files produce it per concrete window/digit. *)

(** [Hdisc] shape — the negative discriminant certificate.  A per-table
    certificate file ([Orchard/circuit_proof/<base>_disc_cert.v])
    instantiates [w := List.nth k (EccSpec.fixed_table_of_rows <rows>) w0] and
    [digit := d], and discharges this by [vm_compute] for every [(window, digit)]
    across the five fixed-base tables.  A successful certificate also implies
    [window_disc w digit <> 0] (since [is_square 0 = true]), so the [disc = 0]
    edge needs no separate handling. *)
Definition Hdisc_shape (w : EccSpec.fixed_window) (digit : Z) : Prop :=
  is_square (window_disc w digit) = false.

(** ** The witness route for the discriminant certificates

    A per-table certificate file discharges [Hdisc_shape] per entry NOT by running
    Euler's criterion (one ~253-squaring [modpow] per entry) but from a pasted
    witness [r] with [window_disc w digit = pallas_b *F (r *F r)] and [r <> 0]:
    since [pallas_b] is a proven non-residue and [r *F r] a nonzero residue,
    the product is a non-residue ([is_square_mul_nonres_l]).  Checking the
    witness is one multiplication per entry.  The soundness gate is preserved:
    were any discriminant actually a square, [X *F pallas_b⁻¹] would be a
    non-residue, no witness [r] could exist, and the certificate's [vm_compute]
    would return [false] rather than lie. *)

(** [pallas_b] is a quadratic non-residue, in [is_square] form (derived from
    the root-free statement [EccSpec.pallas_b_quadratic_nonresidue] via the
    Tonelli–Shanks soundness of [field_sqrt]). *)
Lemma pallas_b_nonsquare : is_square pallas_b = false.
Proof.
  destruct (is_square pallas_b) eqn:Hs; [exfalso | reflexivity].
  apply (EccSpec.pallas_b_quadratic_nonresidue (field_sqrt pallas_b)).
  rewrite (field_sqrt_sound pallas_b Hs).
  apply from_idem.
Qed.

(** The per-entry bridge: a checked witness equation pins the non-residue
    fact.  [x] instantiates to [window_disc <window> <digit>] (already reduced),
    and both hypotheses are closed by the certificate file's single
    [vm_compute]. *)
Lemma window_disc_nonres_of_root (x r : Z)
    (Hr : (UnOp.from r =? 0) = false)
    (Hx : x = BinOp.mul pallas_b (BinOp.mul r r)) :
  is_square x = false.
Proof.
  subst x. apply Z.eqb_neq in Hr.
  apply is_square_mul_nonres_l.
  - vm_compute. reflexivity.
  - exact pallas_b_nonsquare.
  - apply is_square_sq.
  - intro Hz.
    assert (Hp1 : 1 < Primes.pallas_p) by (vm_compute; reflexivity).
    assert (Hz' : BinOp.mul r r = 0).
    { unfold UnOp.from in Hz. unfold BinOp.mul in *.
      rewrite Z.mod_mod in Hz by lia. exact Hz. }
    apply mul_zero_implies_zero in Hz'. destruct Hz'; contradiction.
Qed.

(** ** Table-wide non-residue certificate scaffolding

    The checker definitions and per-entry extraction shared by the per-table
    certificate files ([Orchard/circuit_proof/<base>_disc_cert.v]).
    A per-table file supplies its fixed-base table, [nth] default, a
    [root_table] of witness roots (entry [w][d] is a square root of
    [window_disc (List.nth w table default) d] divided by the non-residue
    [pallas_b]), and closes the [nonres_check_true] hypothesis by one
    [vm_compute]: one field multiplication per entry, no Euler [modpow].  The
    hypothesis is stated as the raw [forallb] term so the per-entry extraction
    type-checks syntactically against the per-table certificate (a
    named-constant wrapper would instead send the conversion oracle into
    lazy-machine evaluation of the whole checker).  The roots' generation is
    untrusted: were any discriminant a square, [disc / pallas_b] would be a
    non-residue, no witness root could exist, and the checker would return
    [false] — the certificate fails rather than lies. *)
Section WindowDiscNonresTable.
  Variable table : EccSpec.fixed_table.
  Variable default : EccSpec.fixed_window.
  Variable root_table : list (list Z).
  Variable windows : nat.

  Definition window_disc_nonres_root (i d : nat) : Z :=
    List.nth d (List.nth i root_table nil) 0.

  (** The per-entry witness check: a nonzero root with
      [disc = pallas_b *F (root *F root)]. *)
  Definition window_disc_nonres_check_fn (i d : nat) : bool :=
    (negb (UnOp.from (window_disc_nonres_root i d) =? 0))
    && (window_disc (List.nth i table default) (Z.of_nat d)
        =? BinOp.mul pallas_b
             (BinOp.mul (window_disc_nonres_root i d)
                (window_disc_nonres_root i d))).

  (** The whole-table certificate, as the raw [forallb] term. *)
  Hypothesis nonres_check_true :
    List.forallb
      (fun i => List.forallb (window_disc_nonres_check_fn i) (List.seq 0 8))
      (List.seq 0 windows) = true.

  (** Per-entry extraction, digit as a [nat]. *)
  Lemma window_disc_nonres_entry (i d : nat)
      (Hi : (i < windows)%nat) (Hd : (d < 8)%nat) :
    is_square (window_disc (List.nth i table default) (Z.of_nat d)) = false.
  Proof.
    pose proof (forallb_nested_entry window_disc_nonres_check_fn
                  (List.seq 0 windows) (List.seq 0 8) i d nonres_check_true
                  ltac:(apply in_seq; lia) ltac:(apply in_seq; lia)) as Hc.
    unfold window_disc_nonres_check_fn in Hc.
    apply andb_true_iff in Hc. destruct Hc as [Hr Hx].
    apply negb_true_iff in Hr. apply Z.eqb_eq in Hx.
    exact (window_disc_nonres_of_root _ _ Hr Hx).
  Qed.

  (** Per-entry extraction, digit as a plain [Z] in [[0, 8)]. *)
  Lemma window_disc_nonres_entry_Z (w : nat) (digit : Z)
      (Hw : (w < windows)%nat) (Hdig : 0 <= digit < 8) :
    is_square (window_disc (List.nth w table default) digit) = false.
  Proof.
    rewrite <- (Z2Nat.id digit) by lia.
    apply window_disc_nonres_entry; lia.
  Qed.
End WindowDiscNonresTable.

(** The shape of the positive QR (window-sign) certificate, in its
    spend_auth_g instance.  Because this file may not depend on the
    Weierstrass / Pallas theory or the ladder's [window_scalar], the term is
    pinned here only as a comment;
    [circuit_proof/spend_auth_g_sign_cert.v] states it against
    [SpendAuthGFullTable.full_table]
    ([circuit_proof/spend_auth_g_table.v]), whose entries are the
    multiples [Pallas.mul (window_scalar 85 w d) PallasGenerators.spend_auth_g_G]:

      is_square
        (UnOp.from
          (EccSpec.fw_z <window> +F
            Point.y (PallasModel.repr
              (Pallas.mul (FixedBaseLadder.window_scalar 85 w d)
                PallasGenerators.spend_auth_g_G)))) = true

    where [<window> = List.nth w OrchardActionFixedBase.spend_auth_g_fixed_table
    OrchardActionFixedBase.fixed_window_default].  It is the [Hqr] that turns
    [window_y_forced_of_disc] into "canonical = multiple" for the RK path.  The
    multiples are already materialised in [SpendAuthGFullTable.full_table] (the
    table leaf shared with the x-coordinate certificate), so the window-sign
    certificate reuses that table rather than recomputing.  The other four
    fixed-base tables have analogous certificates
    ([circuit_proof/<base>_sign_cert.v]). *)
