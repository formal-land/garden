(** * Forward gate lemmas: the [Commit^ivk] and [NoteCommit] canonicity,
    y-canonicity and input-decomposition gates

    The symbolic per-gate forward lemmas of the C2 completeness campaign for
    the region families [38] ([Commit^ivk]), [39] and [40] ([NoteCommit] old
    and new): for every valid, nondegenerate honest input, the generator's
    cells ([tables_nc.v] — pure bit slices of the packed §5.4.8.4 messages)
    satisfy every constraint of

    - the [NoteCommit MessagePiece b/d/e/g/h] decomposition gates,
    - the [NoteCommit input g_d/pk_d/value/rho/psi] gates (decomposition,
      prime offset, and the conditional canonicity clauses),
    - the [y coordinate checks] gate (both subjects, both notes),
    - the [CommitIvk canonicity check] gate,
    - the [Short lookup bitshift] gate at the short range-check subregions
      of these families,

    together with the vacuity of the [QLookup]/[QRunning] points (no gate
    constraint is guarded by them).  The algebra mirrors the soundness layer
    ([circuit_proof/note_commit/pieces.v], [circuit_proof/
    base_field_canonicity.v]) in the forward direction: the honest cells are
    the canonical slices, so each field equation is an exact integer
    identity, and the conditional clauses follow from the input's field
    range ([x < p = 2^254 + t_P] pins the low bits below [t_P] whenever the
    top bit is set).

    The family-level obligation [family_gates_ok [38; 39; 40]] of
    [forward/api.v] is assembled at the end; the points of the Sinsemilla
    hash regions and of the ECC sub-generator regions inside these families
    ([QSinsemilla*], [QMulFixedFull], [QAddIncomplete], [QEccAdd]) belong to
    the Sinsemilla and fixed-base forward lanes and remain as the tracked
    [residual_gates_forward] obligation. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Orchard.circuit_completeness.tables_nc.
Require Import Garden.Orchard.circuit_completeness.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.tables.
Require Import Garden.Orchard.circuit_completeness.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.certificates.
Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.commit_ivk.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCanonicityForward.
  Import OrchardWitnessInput.
  Import OrchardNoteCommitCells.
  Import OrchardCompletenessInstanceDefs.

  Module NC := Garden.Orchard.circuit.note_commit.
  Module CIVK := Garden.Orchard.circuit.commit_ivk.
  Module Constants := Garden.Halo2.halo2_gadgets.ecc.chip.constants.

  (** ** Power-of-two slice arithmetic *)

  Lemma pow2_pos (a : Z) : 0 <= a -> 0 < 2 ^ a.
  Proof. intros Ha. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma pow2_nz (a : Z) : 0 <= a -> 2 ^ a <> 0.
  Proof. intros Ha. pose proof (pow2_pos a Ha). lia. Qed.

  Lemma pow2_split (a b : Z) : 0 <= a -> 0 <= b ->
    2 ^ (a + b) = 2 ^ a * 2 ^ b.
  Proof. intros. apply Z.pow_add_r; lia. Qed.

  Lemma div_div_pow (x a b : Z) : 0 <= a -> 0 <= b ->
    x / 2 ^ a / 2 ^ b = x / 2 ^ (a + b).
  Proof.
    intros Ha Hb.
    pose proof (pow2_pos a Ha).
    pose proof (pow2_pos b Hb).
    rewrite Z.div_div by lia.
    rewrite <- pow2_split by lia.
    reflexivity.
  Qed.

  Lemma mod_mod_low (x a b : Z) : 0 <= a <= b ->
    (x mod 2 ^ b) mod 2 ^ a = x mod 2 ^ a.
  Proof.
    intros [Ha Hab].
    apply Z.mod_mod_divide.
    exists (2 ^ (b - a)).
    rewrite <- pow2_split by lia.
    f_equal; lia.
  Qed.

  Lemma mod_mod_two (x b : Z) : 1 <= b -> (x mod 2 ^ b) mod 2 = x mod 2.
  Proof.
    intros Hb.
    pose proof (mod_mod_low x 1 b ltac:(lia)) as H.
    change (2 ^ 1) with 2 in H.
    exact H.
  Qed.

  Lemma div_of_mod (x a b : Z) : 0 <= a <= b ->
    (x mod 2 ^ b) / 2 ^ a = x / 2 ^ a mod 2 ^ (b - a).
  Proof.
    intros [Ha Hab].
    pose proof (pow2_pos a Ha).
    pose proof (pow2_pos (b - a) ltac:(lia)).
    pose proof (pow2_pos b ltac:(lia)).
    rewrite (Z.mod_eq x (2 ^ b)) by lia.
    replace (x - 2 ^ b * (x / 2 ^ b))
      with (x + - (x / 2 ^ b) * 2 ^ (b - a) * 2 ^ a)
      by (rewrite <- Z.mul_assoc, <- pow2_split by lia;
          replace (b - a + a) with b by lia; ring).
    rewrite Z.div_add by lia.
    rewrite (Z.mod_eq (x / 2 ^ a) (2 ^ (b - a))) by lia.
    rewrite div_div_pow by lia.
    replace (a + (b - a)) with b by lia.
    ring.
  Qed.

  Lemma slice_of_view (C K n j m : Z) :
    0 <= j -> 0 <= m -> j + m <= n ->
    (C + K * 2 ^ n) / 2 ^ j mod 2 ^ m = C / 2 ^ j mod 2 ^ m.
  Proof.
    intros Hj Hm Hjm.
    pose proof (pow2_pos j Hj).
    pose proof (pow2_pos m Hm).
    assert (Hn : 2 ^ n = 2 ^ (n - j - m) * 2 ^ m * 2 ^ j)
      by (rewrite <- !pow2_split by lia; f_equal; lia).
    replace (K * 2 ^ n) with (K * 2 ^ (n - j - m) * 2 ^ m * 2 ^ j)
      by (rewrite Hn; ring).
    rewrite Z.div_add by lia.
    rewrite Z.mod_add by lia.
    reflexivity.
  Qed.

  Lemma slice_of_view_two (C K n j : Z) :
    0 <= j -> j + 1 <= n ->
    (C + K * 2 ^ n) / 2 ^ j mod 2 = C / 2 ^ j mod 2.
  Proof.
    intros Hj Hjn.
    pose proof (slice_of_view C K n j 1 Hj ltac:(lia) Hjn) as H.
    change (2 ^ 1) with 2 in H.
    exact H.
  Qed.

  Lemma mod_of_view (C K n m : Z) : 0 <= m -> m <= n ->
    (C + K * 2 ^ n) mod 2 ^ m = C mod 2 ^ m.
  Proof.
    intros Hm Hn.
    pose proof (slice_of_view C K n 0 m ltac:(lia) Hm ltac:(lia)) as H.
    rewrite Z.pow_0_r in H.
    rewrite !Z.div_1_r in H.
    exact H.
  Qed.

  Lemma view_shift (LOW M b : Z) : 0 <= b -> 0 <= LOW < 2 ^ b ->
    (LOW + M * 2 ^ b) / 2 ^ b = M.
  Proof.
    intros Hb HL.
    pose proof (pow2_pos b Hb).
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    apply Z.add_0_l.
  Qed.

  Lemma split_lohi (x a : Z) : 0 <= a ->
    x = x mod 2 ^ a + x / 2 ^ a * 2 ^ a.
  Proof.
    intros Ha.
    pose proof (pow2_pos a Ha).
    pose proof (Z.div_mod x (2 ^ a) ltac:(lia)).
    lia.
  Qed.

  Lemma split_mid (x a b : Z) : 0 <= a <= b ->
    x mod 2 ^ b = x mod 2 ^ a + x / 2 ^ a mod 2 ^ (b - a) * 2 ^ a.
  Proof.
    intros Hab.
    pose proof (split_lohi (x mod 2 ^ b) a ltac:(lia)) as H1.
    rewrite mod_mod_low in H1 by lia.
    rewrite div_of_mod in H1 by lia.
    exact H1.
  Qed.

  Lemma div_bound_lt (x a q : Z) : 0 <= a -> 0 <= x < q * 2 ^ a ->
    0 <= x / 2 ^ a < q.
  Proof.
    intros Ha Hx.
    pose proof (pow2_pos a Ha).
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma mod_bound (x m : Z) : 0 <= m -> 0 <= x mod 2 ^ m < 2 ^ m.
  Proof. intros Hm. apply Z.mod_pos_bound, pow2_pos, Hm. Qed.

  Lemma mod2_cases (x : Z) : x mod 2 = 0 \/ x mod 2 = 1.
  Proof. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia. Qed.

  (** ** Pallas modulus facts *)

  Lemma pallas_p_big : 2 ^ 141 < Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pallas_p_lt : Primes.pallas_p < 2 ^ 255.
  Proof. vm_compute. reflexivity. Qed.

  Lemma t_p_small : 0 < Primes.t_p < 2 ^ 126.
  Proof. split; vm_compute; reflexivity. Qed.

  Lemma t_p_constants_eq : Constants.t_p = Primes.t_p.
  Proof. reflexivity. Qed.

  Lemma pallas_p_split : Primes.pallas_p = 2 ^ 254 + Primes.t_p.
  Proof. reflexivity. Qed.

  (** ** Field-operation helpers *)

  Lemma from_small (x : Z) : 0 <= x < Primes.pallas_p -> UnOp.from x = x.
  Proof. intros. unfold UnOp.from. apply Z.mod_small. assumption. Qed.

  Lemma from_zero : UnOp.from 0 = 0.
  Proof. apply from_small. pose proof pallas_p_big. lia. Qed.

  Lemma isbool_from (x : Z) : x = 0 \/ x = 1 -> IsBool.t (UnOp.from x).
  Proof.
    intros [Hx | Hx]; subst x.
    - rewrite from_zero. reflexivity.
    - rewrite (from_small 1) by (pose proof pallas_p_big; lia).
      reflexivity.
  Qed.

  (** Strip every field reduction from a reduced-form equality: after
      unfolding the operations both sides are outermost [mod p]; congruence
      modulo [p] removes the inner reductions, and [f_equal] leaves the
      underlying integer identity (exact for the canonical slice cells). *)
  Ltac strip_field :=
    unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from;
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q =>
        change (Zdiv.eqm q x y);
        repeat setoid_rewrite (Zdiv.Zmod_eqm q)
    end;
    unfold Zdiv.eqm;
    f_equal.

  (** ** Views of the packed note message

      [nc_packed] regrouped at each component boundary: the packed value is
      the component plus a shifted remainder, so the slice lemmas above
      project any window of the packed message onto the component that owns
      those bits. *)

  Lemma nc_view_0 (gd pkd : Point.t) (v rho psi : Z) :
    nc_packed gd pkd v rho psi =
    EccSpec.extract_x gd +
    (Point.y gd mod 2 + EccSpec.extract_x pkd * 2 +
     Point.y pkd mod 2 * 2 ^ 256 + v * 2 ^ 257 + rho * 2 ^ 321 +
     psi * 2 ^ 576) * 2 ^ 255.
  Proof. unfold nc_packed. ring. Qed.

  Lemma nc_view_256 (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255) :
    nc_packed gd pkd v rho psi / 2 ^ 256 =
    EccSpec.extract_x pkd +
    (Point.y pkd mod 2 + v * 2 + rho * 2 ^ 65 + psi * 2 ^ 320) * 2 ^ 255.
  Proof.
    replace (nc_packed gd pkd v rho psi)
      with ((EccSpec.extract_x gd + Point.y gd mod 2 * 2 ^ 255) +
            (EccSpec.extract_x pkd +
             (Point.y pkd mod 2 + v * 2 + rho * 2 ^ 65 + psi * 2 ^ 320) *
             2 ^ 255) * 2 ^ 256)
      by (unfold nc_packed; ring).
    apply view_shift; [lia |].
    pose proof (Z.mod_pos_bound (Point.y gd) 2 ltac:(lia)).
    lia.
  Qed.

  Lemma nc_view_512 (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255)
      (Hxp : 0 <= EccSpec.extract_x pkd < 2 ^ 255) :
    nc_packed gd pkd v rho psi / 2 ^ 512 =
    v + (rho + psi * 2 ^ 255) * 2 ^ 64.
  Proof.
    replace (nc_packed gd pkd v rho psi)
      with ((EccSpec.extract_x gd + Point.y gd mod 2 * 2 ^ 255 +
             EccSpec.extract_x pkd * 2 ^ 256 +
             Point.y pkd mod 2 * 2 ^ 511) +
            (v + (rho + psi * 2 ^ 255) * 2 ^ 64) * 2 ^ 512)
      by (unfold nc_packed; ring).
    apply view_shift; [lia |].
    pose proof (Z.mod_pos_bound (Point.y gd) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Point.y pkd) 2 ltac:(lia)).
    lia.
  Qed.

  Lemma nc_view_576 (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255)
      (Hxp : 0 <= EccSpec.extract_x pkd < 2 ^ 255)
      (Hv : 0 <= v < 2 ^ 64) :
    nc_packed gd pkd v rho psi / 2 ^ 576 = rho + psi * 2 ^ 255.
  Proof.
    transitivity (nc_packed gd pkd v rho psi / 2 ^ 512 / 2 ^ 64);
      [ rewrite div_div_pow by lia; reflexivity |].
    rewrite nc_view_512 by assumption.
    apply view_shift; [lia | exact Hv].
  Qed.

  Lemma nc_view_831 (gd pkd : Point.t) (v rho psi : Z)
      (Hxg : 0 <= EccSpec.extract_x gd < 2 ^ 255)
      (Hxp : 0 <= EccSpec.extract_x pkd < 2 ^ 255)
      (Hv : 0 <= v < 2 ^ 64)
      (Hrho : 0 <= rho < 2 ^ 255) :
    nc_packed gd pkd v rho psi / 2 ^ 831 = psi.
  Proof.
    transitivity (nc_packed gd pkd v rho psi / 2 ^ 576 / 2 ^ 255);
      [ rewrite div_div_pow by lia; reflexivity |].
    rewrite nc_view_576 by assumption.
    apply view_shift; [lia | exact Hrho].
  Qed.

  Lemma civk_view_255 (akx nk : Z) (Hakx : 0 <= akx < 2 ^ 255) :
    civk_packed akx nk / 2 ^ 255 = nk.
  Proof. unfold civk_packed. apply view_shift; [lia | exact Hakx]. Qed.

  (** ** Cell projections: the note-message slices land on their components *)

  Section NoteCells.
    Context (gd pkd : Point.t) (v rho psi : Z).

    Local Notation P := (nc_packed gd pkd v rho psi).
    Local Notation xg := (EccSpec.extract_x gd).
    Local Notation xp := (EccSpec.extract_x pkd).

    Lemma nc_a_eq : nc_a P = xg mod 2 ^ 250.
    Proof.
      unfold nc_a. rewrite nc_view_0. apply mod_of_view; lia.
    Qed.

    Lemma nc_b0_eq : nc_b0 P = xg / 2 ^ 250 mod 2 ^ 4.
    Proof.
      unfold nc_b0, nc_b.
      rewrite mod_mod_low by lia.
      rewrite nc_view_0.
      apply slice_of_view; lia.
    Qed.

    Lemma nc_b1_eq : nc_b1 P = xg / 2 ^ 254 mod 2.
    Proof.
      unfold nc_b1, nc_b.
      rewrite div_of_mod by lia.
      rewrite mod_mod_two by lia.
      rewrite div_div_pow by lia.
      replace (250 + 4) with 254 by lia.
      rewrite nc_view_0.
      apply slice_of_view_two; lia.
    Qed.

    Lemma nc_b3_eq (Hxg : 0 <= xg < 2 ^ 255) : nc_b3 P = xp mod 2 ^ 4.
    Proof.
      unfold nc_b3, nc_b.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (250 + 6) with 256 by lia.
      replace (10 - 6) with 4 by lia.
      rewrite (nc_view_256 gd pkd v rho psi Hxg).
      apply mod_of_view; lia.
    Qed.

    Lemma nc_c_eq (Hxg : 0 <= xg < 2 ^ 255) : nc_c P = xp / 2 ^ 4 mod 2 ^ 250.
    Proof.
      unfold nc_c.
      transitivity (P / 2 ^ 256 / 2 ^ 4 mod 2 ^ 250);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_256 gd pkd v rho psi Hxg).
      apply slice_of_view; lia.
    Qed.

    Lemma nc_d0_eq (Hxg : 0 <= xg < 2 ^ 255) : nc_d0 P = xp / 2 ^ 254 mod 2.
    Proof.
      unfold nc_d0, nc_d.
      rewrite mod_mod_two by lia.
      transitivity (P / 2 ^ 256 / 2 ^ 254 mod 2);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_256 gd pkd v rho psi Hxg).
      apply slice_of_view_two; lia.
    Qed.

    Lemma nc_d2_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255) :
      nc_d2 P = v mod 2 ^ 8.
    Proof.
      unfold nc_d2, nc_d.
      rewrite div_of_mod by lia.
      rewrite mod_mod_low by lia.
      rewrite div_div_pow by lia.
      replace (510 + 2) with 512 by lia.
      rewrite (nc_view_512 gd pkd v rho psi Hxg Hxp).
      apply mod_of_view; lia.
    Qed.

    Lemma nc_d3_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255) :
      nc_d3 P = v / 2 ^ 8 mod 2 ^ 50.
    Proof.
      unfold nc_d3, nc_d.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (510 + 10) with 520 by lia.
      replace (60 - 10) with 50 by lia.
      transitivity (P / 2 ^ 512 / 2 ^ 8 mod 2 ^ 50);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_512 gd pkd v rho psi Hxg Hxp).
      apply slice_of_view; lia.
    Qed.

    Lemma nc_e0_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255) :
      nc_e0 P = v / 2 ^ 58 mod 2 ^ 6.
    Proof.
      unfold nc_e0, nc_e.
      rewrite mod_mod_low by lia.
      transitivity (P / 2 ^ 512 / 2 ^ 58 mod 2 ^ 6);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_512 gd pkd v rho psi Hxg Hxp).
      apply slice_of_view; lia.
    Qed.

    Lemma nc_e1_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) :
      nc_e1 P = rho mod 2 ^ 4.
    Proof.
      unfold nc_e1, nc_e.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (570 + 6) with 576 by lia.
      replace (10 - 6) with 4 by lia.
      rewrite (nc_view_576 gd pkd v rho psi Hxg Hxp Hv).
      apply mod_of_view; lia.
    Qed.

    Lemma nc_f_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) :
      nc_f P = rho / 2 ^ 4 mod 2 ^ 250.
    Proof.
      unfold nc_f.
      transitivity (P / 2 ^ 576 / 2 ^ 4 mod 2 ^ 250);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_576 gd pkd v rho psi Hxg Hxp Hv).
      apply slice_of_view; lia.
    Qed.

    Lemma nc_g0_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) :
      nc_g0 P = rho / 2 ^ 254 mod 2.
    Proof.
      unfold nc_g0, nc_g.
      rewrite mod_mod_two by lia.
      transitivity (P / 2 ^ 576 / 2 ^ 254 mod 2);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_576 gd pkd v rho psi Hxg Hxp Hv).
      apply slice_of_view_two; lia.
    Qed.

    Lemma nc_g1_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) (Hrho : 0 <= rho < 2 ^ 255) :
      nc_g1 P = psi mod 2 ^ 9.
    Proof.
      unfold nc_g1, nc_g.
      transitivity
        (nc_packed gd pkd v rho psi / 2 ^ 830 mod 2 ^ 250 / 2 ^ 1
           mod 2 ^ 9);
        [ reflexivity |].
      rewrite div_of_mod by lia.
      rewrite mod_mod_low by lia.
      rewrite div_div_pow by lia.
      replace (830 + 1) with 831 by lia.
      rewrite (nc_view_831 gd pkd v rho psi Hxg Hxp Hv Hrho).
      reflexivity.
    Qed.

    Lemma nc_g2_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) (Hrho : 0 <= rho < 2 ^ 255) :
      nc_g2 P = psi / 2 ^ 9 mod 2 ^ 240.
    Proof.
      unfold nc_g2, nc_g.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (830 + 10) with 840 by lia.
      replace (250 - 10) with 240 by lia.
      transitivity (P / 2 ^ 831 / 2 ^ 9 mod 2 ^ 240);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_831 gd pkd v rho psi Hxg Hxp Hv Hrho).
      reflexivity.
    Qed.

    Lemma nc_h0_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) (Hrho : 0 <= rho < 2 ^ 255) :
      nc_h0 P = psi / 2 ^ 249 mod 2 ^ 5.
    Proof.
      unfold nc_h0, nc_h.
      rewrite mod_mod_low by lia.
      transitivity (P / 2 ^ 831 / 2 ^ 249 mod 2 ^ 5);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_831 gd pkd v rho psi Hxg Hxp Hv Hrho).
      reflexivity.
    Qed.

    Lemma nc_h1_eq (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) (Hrho : 0 <= rho < 2 ^ 255) :
      nc_h1 P = psi / 2 ^ 254 mod 2 ^ 5.
    Proof.
      unfold nc_h1, nc_h.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (1080 + 5) with 1085 by lia.
      replace (10 - 5) with 5 by lia.
      transitivity (P / 2 ^ 831 / 2 ^ 254 mod 2 ^ 5);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_831 gd pkd v rho psi Hxg Hxp Hv Hrho).
      reflexivity.
    Qed.

    (** The whole [g] piece under the [ρ] bound: the top bit of [ρ] and the
        low 249 bits of [ψ], as the conditional [z13_g] clause reads it. *)
    Lemma nc_g_low (Hxg : 0 <= xg < 2 ^ 255) (Hxp : 0 <= xp < 2 ^ 255)
        (Hv : 0 <= v < 2 ^ 64) (Hrho : 0 <= rho < 2 ^ 255) :
      nc_g P = rho / 2 ^ 254 + psi mod 2 ^ 249 * 2.
    Proof.
      unfold nc_g.
      transitivity (P / 2 ^ 576 / 2 ^ 254 mod 2 ^ 250);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (nc_view_576 gd pkd v rho psi Hxg Hxp Hv).
      replace (rho + psi * 2 ^ 255) with (rho + psi * 2 * 2 ^ 254) by ring.
      rewrite Z.div_add by (pose proof (pow2_pos 254 ltac:(lia)); lia).
      assert (Hbit : 0 <= rho / 2 ^ 254 < 2)
        by (split;
            [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
            | (apply Z.div_lt_upper_bound;
               [apply pow2_pos; lia | lia]) ]).
      pose proof (split_lohi psi 249 ltac:(lia)) as Hpsi.
      replace (rho / 2 ^ 254 + psi * 2)
        with (rho / 2 ^ 254 + psi mod 2 ^ 249 * 2 + psi / 2 ^ 249 * 2 ^ 250)
        by lia.
      rewrite Z.mod_add by (pose proof (pow2_pos 250 ltac:(lia)); lia).
      apply Z.mod_small.
      pose proof (mod_bound psi 249 ltac:(lia)).
      lia.
    Qed.
  End NoteCells.

  (** ** Cell projections for the [Commit^ivk] message *)

  Section CivkCells.
    Context (akx nk : Z).

    Local Notation Q := (civk_packed akx nk).

    Lemma civk_packed_view : Q = akx + nk * 2 ^ 255.
    Proof. reflexivity. Qed.

    Lemma civk_a_eq : civk_a Q = akx mod 2 ^ 250.
    Proof.
      unfold civk_a, civk_packed. apply mod_of_view; lia.
    Qed.

    Lemma civk_b0_eq : civk_b0 Q = akx / 2 ^ 250 mod 2 ^ 4.
    Proof.
      unfold civk_b0, civk_b, civk_packed.
      rewrite mod_mod_low by lia.
      apply slice_of_view; lia.
    Qed.

    Lemma civk_b1_eq : civk_b1 Q = akx / 2 ^ 254 mod 2.
    Proof.
      unfold civk_b1, civk_b, civk_packed.
      rewrite div_of_mod by lia.
      rewrite mod_mod_two by lia.
      rewrite div_div_pow by lia.
      replace (250 + 4) with 254 by lia.
      apply slice_of_view_two; lia.
    Qed.

    Lemma civk_b2_eq (Hakx : 0 <= akx < 2 ^ 255) :
      civk_b2 Q = nk mod 2 ^ 5.
    Proof.
      unfold civk_b2, civk_b.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (250 + 5) with 255 by lia.
      replace (10 - 5) with 5 by lia.
      rewrite (civk_view_255 akx nk Hakx).
      reflexivity.
    Qed.

    Lemma civk_c_eq (Hakx : 0 <= akx < 2 ^ 255) :
      civk_c Q = nk / 2 ^ 5 mod 2 ^ 240.
    Proof.
      unfold civk_c.
      transitivity (Q / 2 ^ 255 / 2 ^ 5 mod 2 ^ 240);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (civk_view_255 akx nk Hakx).
      reflexivity.
    Qed.

    Lemma civk_d0_eq (Hakx : 0 <= akx < 2 ^ 255) :
      civk_d0 Q = nk / 2 ^ 245 mod 2 ^ 9.
    Proof.
      unfold civk_d0, civk_d.
      rewrite mod_mod_low by lia.
      transitivity (Q / 2 ^ 255 / 2 ^ 245 mod 2 ^ 9);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (civk_view_255 akx nk Hakx).
      reflexivity.
    Qed.

    Lemma civk_d1_eq (Hakx : 0 <= akx < 2 ^ 255) :
      civk_d1 Q = nk / 2 ^ 254 mod 2.
    Proof.
      unfold civk_d1, civk_d.
      rewrite div_of_mod by lia.
      rewrite div_div_pow by lia.
      replace (500 + 9) with 509 by lia.
      replace (10 - 9) with 1 by lia.
      change (2 ^ 1) with 2.
      transitivity (Q / 2 ^ 255 / 2 ^ 254 mod 2);
        [ rewrite div_div_pow by lia; reflexivity |].
      rewrite (civk_view_255 akx nk Hakx).
      reflexivity.
    Qed.
  End CivkCells.

  (** ** Recombination identities *)

  Lemma recomb_b_piece (y : Z) :
    y = y mod 2 ^ 4 + y / 2 ^ 4 mod 2 * 2 ^ 4 + y / 2 ^ 5 mod 2 * 2 ^ 5 +
        y / 2 ^ 6 * 2 ^ 6.
  Proof.
    pose proof (split_mid y 4 5 ltac:(lia)) as H1.
    pose proof (split_mid y 5 6 ltac:(lia)) as H2.
    pose proof (split_lohi y 6 ltac:(lia)) as H3.
    replace (5 - 4) with 1 in H1 by lia.
    replace (6 - 5) with 1 in H2 by lia.
    change (2 ^ 1) with 2 in H1, H2.
    lia.
  Qed.

  Lemma recomb_d_piece (y : Z) :
    y = y mod 2 + y / 2 mod 2 * 2 + y / 2 ^ 2 mod 2 ^ 8 * 2 ^ 2 +
        y / 2 ^ 10 * 2 ^ 10.
  Proof.
    pose proof (split_mid y 1 2 ltac:(lia)) as H1.
    pose proof (split_mid y 2 10 ltac:(lia)) as H2.
    pose proof (split_lohi y 10 ltac:(lia)) as H3.
    replace (2 - 1) with 1 in H1 by lia.
    replace (10 - 2) with 8 in H2 by lia.
    change (2 ^ 1) with 2 in H1.
    lia.
  Qed.

  Lemma recomb_e_piece (y : Z) : y = y mod 2 ^ 6 + y / 2 ^ 6 * 2 ^ 6.
  Proof. exact (split_lohi y 6 ltac:(lia)). Qed.

  Lemma recomb_g_piece (y : Z) :
    y = y mod 2 + y / 2 mod 2 ^ 9 * 2 + y / 2 ^ 10 * 2 ^ 10.
  Proof.
    pose proof (split_mid y 1 10 ltac:(lia)) as H1.
    pose proof (split_lohi y 10 ltac:(lia)) as H2.
    replace (10 - 1) with 9 in H1 by lia.
    change (2 ^ 1) with 2 in H1.
    lia.
  Qed.

  Lemma recomb_h_piece (y : Z) : y = y mod 2 ^ 5 + y / 2 ^ 5 * 2 ^ 5.
  Proof. exact (split_lohi y 5 ltac:(lia)). Qed.

  Lemma recomb_civk_b (y : Z) :
    y = y mod 2 ^ 4 + y / 2 ^ 4 mod 2 * 2 ^ 4 + y / 2 ^ 5 * 2 ^ 5.
  Proof.
    pose proof (split_mid y 4 5 ltac:(lia)) as H1.
    pose proof (split_lohi y 5 ltac:(lia)) as H2.
    replace (5 - 4) with 1 in H1 by lia.
    change (2 ^ 1) with 2 in H1.
    lia.
  Qed.

  Lemma recomb_civk_d (y : Z) : y = y mod 2 ^ 9 + y / 2 ^ 9 * 2 ^ 9.
  Proof. exact (split_lohi y 9 ltac:(lia)). Qed.

  Lemma recomb_250_4_1 (x : Z) (Hx : 0 <= x < 2 ^ 255) :
    x mod 2 ^ 250 + x / 2 ^ 250 mod 2 ^ 4 * 2 ^ 250 +
    x / 2 ^ 254 mod 2 * 2 ^ 254 = x.
  Proof.
    pose proof (split_mid x 250 254 ltac:(lia)) as H1.
    replace (254 - 250) with 4 in H1 by lia.
    pose proof (split_lohi x 254 ltac:(lia)) as H2.
    assert (Hq : x / 2 ^ 254 mod 2 = x / 2 ^ 254).
    { apply Z.mod_small.
      split;
        [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
        | (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]) ]. }
    lia.
  Qed.

  Lemma recomb_4_250_1 (x : Z) (Hx : 0 <= x < 2 ^ 255) :
    x mod 2 ^ 4 + x / 2 ^ 4 mod 2 ^ 250 * 2 ^ 4 +
    x / 2 ^ 254 mod 2 * 2 ^ 254 = x.
  Proof.
    pose proof (split_mid x 4 254 ltac:(lia)) as H1.
    replace (254 - 4) with 250 in H1 by lia.
    pose proof (split_lohi x 254 ltac:(lia)) as H2.
    assert (Hq : x / 2 ^ 254 mod 2 = x / 2 ^ 254).
    { apply Z.mod_small.
      split;
        [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
        | (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]) ]. }
    lia.
  Qed.

  Lemma recomb_value (x : Z) (Hx : 0 <= x < 2 ^ 64) :
    x mod 2 ^ 8 + x / 2 ^ 8 mod 2 ^ 50 * 2 ^ 8 +
    x / 2 ^ 58 mod 2 ^ 6 * 2 ^ 58 = x.
  Proof.
    pose proof (split_mid x 8 58 ltac:(lia)) as H1.
    replace (58 - 8) with 50 in H1 by lia.
    pose proof (split_lohi x 58 ltac:(lia)) as H2.
    assert (Hq : x / 2 ^ 58 mod 2 ^ 6 = x / 2 ^ 58).
    { apply Z.mod_small.
      split;
        [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
        | (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]) ]. }
    lia.
  Qed.

  Lemma recomb_9_240_5_1 (x : Z) (Hx : 0 <= x < 2 ^ 255) :
    x mod 2 ^ 9 + x / 2 ^ 9 mod 2 ^ 240 * 2 ^ 9 +
    x / 2 ^ 249 mod 2 ^ 5 * 2 ^ 249 + x / 2 ^ 254 mod 2 * 2 ^ 254 = x.
  Proof.
    pose proof (split_mid x 9 249 ltac:(lia)) as H1.
    replace (249 - 9) with 240 in H1 by lia.
    pose proof (split_mid x 249 254 ltac:(lia)) as H2.
    replace (254 - 249) with 5 in H2 by lia.
    pose proof (split_lohi x 254 ltac:(lia)) as H3.
    assert (Hq : x / 2 ^ 254 mod 2 = x / 2 ^ 254).
    { apply Z.mod_small.
      split;
        [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
        | (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]) ]. }
    lia.
  Qed.

  Lemma recomb_5_240_9_1 (x : Z) (Hx : 0 <= x < 2 ^ 255) :
    x mod 2 ^ 5 + x / 2 ^ 5 mod 2 ^ 240 * 2 ^ 5 +
    x / 2 ^ 245 mod 2 ^ 9 * 2 ^ 245 + x / 2 ^ 254 mod 2 * 2 ^ 254 = x.
  Proof.
    pose proof (split_mid x 5 245 ltac:(lia)) as H1.
    replace (245 - 5) with 240 in H1 by lia.
    pose proof (split_mid x 245 254 ltac:(lia)) as H2.
    replace (254 - 245) with 9 in H2 by lia.
    pose proof (split_lohi x 254 ltac:(lia)) as H3.
    assert (Hq : x / 2 ^ 254 mod 2 = x / 2 ^ 254).
    { apply Z.mod_small.
      split;
        [ (apply Z.div_pos; [lia | apply pow2_pos; lia])
        | (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]) ]. }
    lia.
  Qed.

  Lemma recomb_j (y : Z) :
    y mod 2 ^ 250 =
    y mod 2 + y / 2 mod 2 ^ 9 * 2 + y mod 2 ^ 250 / 2 ^ 10 * 2 ^ 10.
  Proof.
    rewrite (div_of_mod y 10 250) by lia.
    replace (250 - 10) with 240 by lia.
    pose proof (split_mid y 1 10 ltac:(lia)) as H1.
    replace (10 - 1) with 9 in H1 by lia.
    change (2 ^ 1) with 2 in H1.
    pose proof (split_mid y 10 250 ltac:(lia)) as H2.
    replace (250 - 10) with 240 in H2 by lia.
    lia.
  Qed.

  Lemma recomb_y (y : Z) (Hy : 0 <= y < 2 ^ 255) :
    y = y mod 2 ^ 250 + y / 2 ^ 250 mod 2 ^ 4 * 2 ^ 250 +
        y / 2 ^ 254 * 2 ^ 254.
  Proof.
    pose proof (split_mid y 250 254 ltac:(lia)) as H1.
    replace (254 - 250) with 4 in H1 by lia.
    pose proof (split_lohi y 254 ltac:(lia)) as H2.
    lia.
  Qed.

  (** ** Canonicity core: a set top bit pins the low bits below [t_P] *)

  Lemma top1_low (x : Z) (Hx : 0 <= x < Primes.pallas_p)
      (Htop : x / 2 ^ 254 mod 2 = 1) :
    x mod 2 ^ 254 < Primes.t_p.
  Proof.
    pose proof pallas_p_split as Hp.
    pose proof t_p_small as Ht.
    assert (Hlt : x < 2 ^ 255) by lia.
    assert (Hq : x / 2 ^ 254 = 1).
    { assert (H0 : 0 <= x / 2 ^ 254)
        by (apply Z.div_pos; [lia | apply pow2_pos; lia]).
      assert (H2 : x / 2 ^ 254 < 2)
        by (apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]).
      rewrite Z.mod_small in Htop by lia.
      exact Htop. }
    pose proof (split_lohi x 254 ltac:(lia)).
    lia.
  Qed.

  Lemma top1_slice_zero (x j m : Z) (Hx : 0 <= x < Primes.pallas_p)
      (Htop : x / 2 ^ 254 mod 2 = 1)
      (Hj : 130 <= j) (Hm : 0 <= m) (Hjm : j + m <= 254) :
    x / 2 ^ j mod 2 ^ m = 0.
  Proof.
    pose proof (top1_low x Hx Htop) as Hlow.
    pose proof t_p_small as Ht.
    assert (H130 : 2 ^ 130 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    assert (Hslice : x / 2 ^ j mod 2 ^ m = x mod 2 ^ 254 / 2 ^ j mod 2 ^ m).
    { rewrite div_of_mod by lia.
      rewrite mod_mod_low by lia.
      reflexivity. }
    rewrite Hslice.
    pose proof (mod_bound x 254 ltac:(lia)).
    rewrite (Z.div_small (x mod 2 ^ 254)) by lia.
    apply Z.mod_0_l, pow2_nz, Hm.
  Qed.

  Lemma top1_mod_low (x c : Z) (Hx : 0 <= x < Primes.pallas_p)
      (Htop : x / 2 ^ 254 mod 2 = 1) (Hc : 130 <= c <= 254) :
    0 <= x mod 2 ^ c < Primes.t_p.
  Proof.
    pose proof (top1_low x Hx Htop) as Hlow.
    pose proof t_p_small as Ht.
    assert (Hcl : 2 ^ 130 <= 2 ^ c) by (apply Z.pow_le_mono_r; lia).
    rewrite <- (mod_mod_low x c 254) by lia.
    pose proof (mod_bound x 254 ltac:(lia)).
    rewrite (Z.mod_small (x mod 2 ^ 254)) by lia.
    lia.
  Qed.

  Lemma prime_of_zero (low k : Z) (Hk : 130 <= k <= 140)
      (Hlow : 0 <= low < Primes.t_p) :
    prime_of low k / 2 ^ k = 0.
  Proof.
    unfold prime_of.
    pose proof t_p_small as Ht.
    pose proof pallas_p_big as Hp.
    assert (Hkl : 2 ^ 130 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
    assert (Hkh : 2 ^ k <= 2 ^ 140) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.mod_small by lia.
    apply Z.div_small.
    lia.
  Qed.

  (** ** Decidable equality on constraint bodies

      Used by the [vm_compute] classification certificates below: every
      constraint body guarded by one of this file's selectors is pinned to
      its literal. *)

  Definition rotation_eq_dec (x y : Rotation.t) : {x = y} + {x <> y}.
  Proof. decide equality; apply Z.eq_dec. Defined.

  Definition expression_eq_dec (x y : Expression.t columns)
      : {x = y} + {x <> y}.
  Proof.
    decide equality;
      first
        [ apply Z.eq_dec
        | apply rotation_eq_dec
        | apply OrchardDecidableEq.selector_eq_dec
        | apply OrchardDecidableEq.fixed_eq_dec
        | apply OrchardDecidableEq.advice_eq_dec
        | apply OrchardDecidableEq.instance_eq_dec ].
  Defined.

  Definition constraint_eq_dec (x y : Constraint.t columns)
      : {x = y} + {x <> y}.
  Proof.
    decide equality;
      first
        [ apply expression_eq_dec
        | apply OrchardDecidableEq.selector_eq_dec
        | apply Nat.eq_dec ].
  Defined.

  Definition constraint_eqb
      : Constraint.t columns -> Constraint.t columns -> bool :=
    OrchardDecidableEq.dec_to_eqb constraint_eq_dec.
  Definition constraint_eqb_eq (x y : Constraint.t columns) :
      constraint_eqb x y = true <-> x = y :=
    OrchardDecidableEq.dec_to_eqb_eq constraint_eq_dec x y.

  (** ** Rotation arithmetic *)

  Lemma rot0c : rotated_row 0 Rotation.cur = 0.
  Proof. reflexivity. Qed.

  Lemma rot0n : rotated_row 0 Rotation.next = 1.
  Proof. reflexivity. Qed.

  Lemma rot1p : rotated_row 1 Rotation.prev = 0.
  Proof. reflexivity. Qed.

  Lemma rot1c : rotated_row 1 Rotation.cur = 1.
  Proof. reflexivity. Qed.

  Lemma rot1n : rotated_row 1 Rotation.next = 2.
  Proof. reflexivity. Qed.

  (** ** The advice plane of the honest assignment *)

  Module OCT := OrchardCompletenessTables.

  Lemma advice_eq (w : HonestInput) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.advice) =
    OCT.advice_t w (OCT.tables_of w).
  Proof. reflexivity. Qed.

  (** ** Coordinate ranges

      The typed points of the completeness domain have reduced coordinates,
      and every derived point of the hoisted table record keeps them reduced
      (the chord formulas end in a field reduction); this pins the packed
      new-note [ρ] (the spec nullifier of the old note) below [p]. *)

  Lemma point_ok_coords (P : Point.t) :
    point_ok P ->
    0 <= Point.x P < Primes.pallas_p /\ 0 <= Point.y P < Primes.pallas_p.
  Proof.
    pose proof pallas_p_big as Hp.
    intros (Hred & _ & Hid).
    unfold Pallas.reduced, Weierstrass.reduced, PallasModel.unrepr in Hred.
    destruct ((Point.x P =? 0) && (Point.y P =? 0))%bool eqn:Hz.
    - exfalso.
      apply Bool.andb_true_iff in Hz.
      destruct Hz as [Hx Hy].
      apply Z.eqb_eq in Hx.
      apply Z.eqb_eq in Hy.
      apply Hid.
      destruct P as [x y].
      cbn in Hx, Hy.
      subst.
      reflexivity.
    - destruct Hred as [Hx Hy].
      unfold UnOp.from in Hx, Hy.
      split; [rewrite <- Hx | rewrite <- Hy]; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma padd_coords (P Q : Point.t) :
    0 <= Point.x P < Primes.pallas_p ->
    0 <= Point.y P < Primes.pallas_p ->
    0 <= Point.x Q < Primes.pallas_p ->
    0 <= Point.y Q < Primes.pallas_p ->
    0 <= Point.x (EccSpec.point_add P Q) < Primes.pallas_p /\
    0 <= Point.y (EccSpec.point_add P Q) < Primes.pallas_p.
  Proof.
    pose proof pallas_p_big as Hp.
    intros HxP HyP HxQ HyQ.
    unfold EccSpec.point_add,
      Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.CompleteAddition.output.
    destruct (Point.x P =? 0); [cbn; auto |].
    destruct (Point.x Q =? 0); [cbn; auto |].
    destruct (_ && _)%bool; [cbn; lia |].
    cbn [Point.x Point.y].
    unfold BinOp.sub, BinOp.mul.
    split; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma hash_go_coords (ws : list Z) :
    forall acc : Point.t,
      0 <= Point.x acc < Primes.pallas_p ->
      0 <= Point.y acc < Primes.pallas_p ->
      0 <= Point.x (snd (OCT.hash_go acc ws)) < Primes.pallas_p /\
      0 <= Point.y (snd (OCT.hash_go acc ws)) < Primes.pallas_p.
  Proof.
    pose proof pallas_p_big as Hp.
    induction ws as [| wd ws' IH]; intros acc Hx Hy.
    - cbn. auto.
    - cbn [OCT.hash_go].
      lazymatch goal with
      | |- context [OCT.hash_go ?X ws'] =>
          pose proof (IH X) as IHX;
          destruct (OCT.hash_go X ws') as [rows out] eqn:Hgo
      end.
      cbn [snd].
      rewrite Hgo in IHX.
      cbn [snd Point.x Point.y] in IHX.
      apply IHX; cbn [Point.x Point.y]; unfold BinOp.sub, BinOp.mul;
        apply Z.mod_pos_bound; lia.
  Qed.

  Lemma hd_out_hash_data_of (Q : Point.t) (pieces : list (list Z)) :
    OCT.hd_out (OCT.hash_data_of Q pieces) =
    snd (OCT.hash_go Q (List.concat pieces)).
  Proof.
    unfold OCT.hash_data_of.
    destruct (OCT.hash_go Q (List.concat pieces)).
    reflexivity.
  Qed.

  Lemma repr_coords (P : Weierstrass.point) :
    Pallas.reduced P ->
    0 <= Point.x (PallasModel.repr P) < Primes.pallas_p /\
    0 <= Point.y (PallasModel.repr P) < Primes.pallas_p.
  Proof.
    pose proof pallas_p_big as Hp.
    unfold Pallas.reduced, Weierstrass.reduced.
    destruct P as [| x y]; intros Hred.
    - cbn. lia.
    - destruct Hred as [Hx Hy].
      cbn [PallasModel.repr Point.x Point.y].
      unfold UnOp.from in Hx, Hy.
      split; [rewrite <- Hx | rewrite <- Hy]; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma mul_gen_coords (k : Z) (G : Pallas.point) (HG : Pallas.reduced G) :
    0 <= Point.x (PallasModel.repr (Pallas.mul k G)) < Primes.pallas_p /\
    0 <= Point.y (PallasModel.repr (Pallas.mul k G)) < Primes.pallas_p.
  Proof.
    apply repr_coords.
    unfold Pallas.mul, Pallas.reduced.
    apply Weierstrass.mul_reduced.
    exact HG.
  Qed.

  Lemma note_commit_Q_coords :
    0 <= Point.x OrchardAdviceMerkleSinsemilla.note_commit_Q
      < Primes.pallas_p /\
    0 <= Point.y OrchardAdviceMerkleSinsemilla.note_commit_Q
      < Primes.pallas_p.
  Proof. repeat split; vm_compute; discriminate. Qed.

  (** The new note's [ρ] read off the table-record literal — stated with the
      let-bound bodies spelled out, so the conversion stays syntactic and no
      symbolic hash fold is ever forced. *)

  Module PState := Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.State.

  Lemma t_nf_spec_eq (w : HonestInput) :
    OCT.t_nf_spec (OCT.tables_of w) =
    EccSpec.extract_x
      (EccSpec.point_add
        (OrchardProtocolSpec.mul_nullifier_k
          (BinOp.add
            (PState.x0 (List.nth 36 (OCT.pose_states_of w) OCT.state0))
            (hi_psi_old w)))
        (EccSpec.point_add
          (OCT.hd_out
            (OCT.hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
              (OrchardAdviceMerkleSinsemilla.split_pieces
                OrchardAdviceMerkleSinsemilla.note_commit_lens
                (note_commit_old_words w))))
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)))).
  Proof. reflexivity. Qed.

  Lemma t_nf_spec_range (w : HonestInput) :
    0 <= OCT.t_nf_spec (OCT.tables_of w) < Primes.pallas_p.
  Proof.
    rewrite t_nf_spec_eq.
    unfold EccSpec.extract_x.
    destruct note_commit_Q_coords as [HQx HQy].
    destruct
      (hash_go_coords
        (List.concat
          (OrchardAdviceMerkleSinsemilla.split_pieces
            OrchardAdviceMerkleSinsemilla.note_commit_lens
            (note_commit_old_words w)))
        OrchardAdviceMerkleSinsemilla.note_commit_Q HQx HQy) as [Hhx Hhy].
    destruct
      (mul_gen_coords (hi_rcm_old w) PallasGenerators.note_commit_r_G
        PallasGenerators.note_commit_r_reduced) as [Hmr_x Hmr_y].
    destruct
      (mul_gen_coords
        (BinOp.add
          (PState.x0 (List.nth 36 (OCT.pose_states_of w) OCT.state0))
          (hi_psi_old w))
        PallasGenerators.nullifier_k_G PallasGenerators.nullifier_k_reduced)
      as [Hmk_x Hmk_y].
    assert (Hcm :
      0 <= Point.x
        (EccSpec.point_add
          (OCT.hd_out
            (OCT.hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
              (OrchardAdviceMerkleSinsemilla.split_pieces
                OrchardAdviceMerkleSinsemilla.note_commit_lens
                (note_commit_old_words w))))
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)))
        < Primes.pallas_p /\
      0 <= Point.y
        (EccSpec.point_add
          (OCT.hd_out
            (OCT.hash_data_of OrchardAdviceMerkleSinsemilla.note_commit_Q
              (OrchardAdviceMerkleSinsemilla.split_pieces
                OrchardAdviceMerkleSinsemilla.note_commit_lens
                (note_commit_old_words w))))
          (OrchardProtocolSpec.mul_note_commit_r (hi_rcm_old w)))
        < Primes.pallas_p).
    { unfold OrchardProtocolSpec.mul_note_commit_r.
      apply padd_coords; rewrite ?hd_out_hash_data_of; assumption. }
    destruct Hcm as [Hcm_x Hcm_y].
    unfold OrchardProtocolSpec.mul_nullifier_k.
    exact (proj1 (padd_coords _ _ Hmk_x Hmk_y Hcm_x Hcm_y)).
  Qed.

End OrchardCanonicityForward.
