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
    - the [CommitIvk canonicity check] gate.

    The algebra mirrors the soundness layer
    ([circuit_proof/note_commit/pieces.v], [circuit_proof/
    base_field_canonicity.v]) in the forward direction: the honest cells are
    the canonical slices, so each field equation is an exact integer
    identity, and the conditional clauses follow from the input's field
    range ([x < p = 2^254 + t_P] pins the low bits below [t_P] whenever the
    top bit is set).

    The family-level obligation [canonicity_gates_ok : family_gates_ok
    [38; 39; 40]] of [forward/api.v] is assembled at the end.  One
    [vm_compute] certificate ([shard_classify]) splits the 1711 enabled
    points of the three families into the 25 canonicity gate rows proved
    here and the points whose guarding selector belongs to another forward
    lane: [QEccAdd]/[QAddIncomplete] ([forward/ecc_add.v]),
    [QMulFixedFull] ([forward/fixed_base.v]),
    [QLookup]/[QRunning]/[QBitshift] ([forward/running_sums.v]), and the
    four [QSinsemilla] selectors of the hash regions
    ([forward/sinsemilla.v]). *)

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
Require Import Garden.Orchard.circuit_completeness.forward.ecc_add.
Require Import Garden.Orchard.circuit_completeness.forward.fixed_base.
Require Import Garden.Orchard.circuit_completeness.forward.running_sums.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
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

  (** The sibling forward lanes keep the complete-addition chord opaque to
      the conversion oracle; the coordinate projection below reads it
      through its two [=? 0] guards, so it is transparent for this proof
      only ([docs/compile-performance.md]). *)
  Strategy transparent
    [Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.CompleteAddition.output
     Pallas.mul Weierstrass.mul].

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
    (* Keep the field division ([mod_inverse]) opaque: reduce only the
       [Point.x]/[Point.y] projection through each [=? 0] branch so the dead
       chord-formula branch is never normalized (see
       [docs/compile-performance.md]). *)
    destruct (Point.x P =? 0); [cbn [Point.x Point.y]; auto |].
    destruct (Point.x Q =? 0); [cbn [Point.x Point.y]; auto |].
    destruct (_ && _)%bool; [cbn [Point.x Point.y]; lia |].
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
    (* Reduce only the [hash_go] base case and [snd]; a bare [cbn] unfolds
       [Primes.pallas_p] to its literal and sends [auto] into a search over
       the giant numeral (see [docs/compile-performance.md]). *)
    - cbn [OCT.hash_go snd]. split; assumption.
    - cbn [OCT.hash_go].
      (* Bind the recursive accumulator to a variable so [destruct] rewrites
         its occurrence uniformly in the goal and the induction hypothesis;
         the [snd (rows, out)] projection is then read directly. *)
      lazymatch goal with
      | |- context [OCT.hash_go ?X ws'] =>
          set (nextacc := X);
          pose proof (IH nextacc) as IHX;
          destruct (OCT.hash_go nextacc ws') as [rows out]
      end.
      cbn [snd].
      cbn [snd Point.x Point.y] in IHX.
      apply IHX; subst nextacc; cbn [Point.x Point.y];
        unfold BinOp.sub, BinOp.mul; apply Z.mod_pos_bound; lia.
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
  Proof.
    (* Project [t_nf_spec] out of the hoisted record by delta/zeta/proj only,
       leaving [extract_x]/[point_add]/[pose_states_of] folded — a bare
       [reflexivity] would whnf-reduce the addition guard and force the 36th
       Poseidon state (see [docs/compile-performance.md]). *)
    cbn [OCT.tables_of OCT.t_nf_spec].
    reflexivity.
  Qed.

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

  (** Restore the sibling lanes' opacity discipline: from here on the
      field division, the modular inverse, the complete-addition chord and
      the scalar multiplications stay stuck atoms for the conversion oracle
      ([docs/compile-performance.md]). *)
  Strategy opaque
    [BinOp.div mod_inverse
     Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** ** The constraint bodies guarded by each selector

      [guarded sel] collects, over the whole configured system, the bodies
      of the constraints guarded by [sel]; the [vm_compute] certificates
      below pin each canonicity selector's list to its gate's bodies. *)

  Import OrchardCompletenessForward.

  Definition guarded (sel : Selector.t) : list (Constraint.t columns) :=
    List.flat_map (fun gate =>
      List.flat_map (fun '(_, c) =>
        match c with
        | Constraint.Select s body =>
            if OrchardDecidableEq.selector_eqb s sel then [body] else []
        | _ => []
        end) gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma guarded_complete (sel : Selector.t) (gate : Gate.t columns)
      (name : option string) (body : Constraint.t columns)
      (Hgate : List.In gate system.(ConstraintSystem.gates))
      (Hbody : List.In (name, Constraint.Select sel body)
        gate.(Gate.constraints)) :
    List.In body (guarded sel).
  Proof.
    unfold guarded.
    apply List.in_flat_map. exists gate. split; [exact Hgate |].
    apply List.in_flat_map. exists (name, Constraint.Select sel body).
    split; [exact Hbody |].
    cbn. rewrite OrchardDecidableEq.selector_eqb_refl. now left.
  Qed.

  (** ** The gate bodies

      The cell expressions of the [NoteCommit] decomposition,
      y-canonicity and [Commit^ivk] gates, spelled once (the gates are
      selector-parameterized, so the old and new instances share every
      body list). *)

  Definition ac (c : Advice.t) : Expression.t columns :=
    Expression.Advice c Rotation.cur.
  Definition an (c : Advice.t) : Expression.t columns :=
    Expression.Advice c Rotation.next.
  Definition tp_e : Expression.t columns :=
    Expression.Constant Constants.t_p.

  (** [NoteCommit MessagePiece b]: [b = b_0 ‖ b_1 ‖ b_2 ‖ b_3]. *)
  Definition mpb_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A8);
    Constraint.Boolean (an Advice.A7);
    Constraint.Equal (ac Advice.A6)
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A7)
            (Expression.Scaled (ac Advice.A8) (2 ^ 4)))
          (Expression.Scaled (an Advice.A7) (2 ^ 5)))
        (Expression.Scaled (an Advice.A8) (2 ^ 6)))
  ].

  (** [NoteCommit MessagePiece d]: [d = d_0 ‖ d_1 ‖ d_2 ‖ d_3]. *)
  Definition mpd_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A7);
    Constraint.Boolean (ac Advice.A8);
    Constraint.Equal (ac Advice.A6)
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A7)
            (Expression.Scaled (ac Advice.A8) 2))
          (Expression.Scaled (an Advice.A7) (2 ^ 2)))
        (Expression.Scaled (an Advice.A8) (2 ^ 10)))
  ].

  (** [NoteCommit MessagePiece e]: [e = e_0 ‖ e_1]. *)
  Definition mpe_bodies : list (Constraint.t columns) := [
    Constraint.Equal (ac Advice.A6)
      (Expression.Sum (ac Advice.A7)
        (Expression.Scaled (ac Advice.A8) (2 ^ 6)))
  ].

  (** [NoteCommit MessagePiece g]: [g = g_0 ‖ g_1 ‖ g_2]. *)
  Definition mpg_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A7);
    Constraint.Equal (ac Advice.A6)
      (Expression.Sum
        (Expression.Sum (ac Advice.A7)
          (Expression.Scaled (an Advice.A6) 2))
        (Expression.Scaled (an Advice.A7) (2 ^ 10)))
  ].

  (** [NoteCommit MessagePiece h]: [h = h_0 ‖ h_1]. *)
  Definition mph_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A8);
    Constraint.Equal (ac Advice.A6)
      (Expression.Sum (ac Advice.A7)
        (Expression.Scaled (ac Advice.A8) (2 ^ 5)))
  ].

  (** [NoteCommit input g_d]: the 250/4/1 decomposition of [x(g_d)], its
      prime offset, and the three clauses conditioned on the top bit. *)
  Definition gd_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A8)
          (Expression.Scaled (ac Advice.A7) (2 ^ 250)))
        (Expression.Scaled (an Advice.A7) (2 ^ 254)))
      (ac Advice.A6);
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A8)
          (Expression.Constant (2 ^ 130)))
        (Expression.Negated tp_e))
      (an Advice.A8);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (ac Advice.A7));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (ac Advice.A9));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (an Advice.A9))
  ].

  (** [NoteCommit input pk_d] and [NoteCommit input rho]: the two gates
      read the same cells with the same coefficients (the 4/250/1
      decomposition, the [2^140] prime offset, and the two clauses
      conditioned on the top bit), so they share one body list. *)
  Definition pkd_rho_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A7)
          (Expression.Scaled (ac Advice.A8) (2 ^ 4)))
        (Expression.Scaled (an Advice.A7) (2 ^ 254)))
      (ac Advice.A6);
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A7)
            (Expression.Scaled (ac Advice.A8) (2 ^ 4)))
          (Expression.Constant (2 ^ 140)))
        (Expression.Negated tp_e))
      (an Advice.A8);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (ac Advice.A9));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (an Advice.A9))
  ].

  (** [NoteCommit input value]: the 8/50/6 split of the 64-bit value. *)
  Definition value_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A7)
          (Expression.Scaled (ac Advice.A8) (2 ^ 8)))
        (Expression.Scaled (ac Advice.A9) (2 ^ 58)))
      (ac Advice.A6)
  ].

  (** [NoteCommit input psi]: the 9/240/5/1 decomposition of [ψ]. *)
  Definition psi_bodies : list (Constraint.t columns) := [
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A7)
            (Expression.Scaled (ac Advice.A8) (2 ^ 9)))
          (Expression.Scaled (an Advice.A6) (2 ^ 249)))
        (Expression.Scaled (an Advice.A7) (2 ^ 254)))
      (ac Advice.A6);
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A7)
            (Expression.Scaled (ac Advice.A8) (2 ^ 9)))
          (Expression.Constant (2 ^ 130)))
        (Expression.Negated tp_e))
      (an Advice.A8);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (an Advice.A6));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (ac Advice.A9));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A7))
      (Constraint.EqualZeroToPrecise (an Advice.A9))
  ].

  (** [y coordinate checks]: the [ỹ]-against-[y] decomposition and its
      canonicity clauses. *)
  Definition ycanon_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A9);
    Constraint.Equal (an Advice.A5)
      (Expression.Sum
        (Expression.Sum (ac Advice.A6)
          (Expression.Scaled (ac Advice.A7) 2))
        (Expression.Scaled (an Advice.A6) (2 ^ 10)));
    Constraint.Equal (ac Advice.A5)
      (Expression.Sum
        (Expression.Sum (an Advice.A5)
          (Expression.Scaled (ac Advice.A8) (2 ^ 250)))
        (Expression.Scaled (ac Advice.A9) (2 ^ 254)));
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (an Advice.A5)
          (Expression.Constant (2 ^ 130)))
        (Expression.Negated tp_e))
      (an Advice.A8);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A9))
      (Constraint.EqualZeroToPrecise (ac Advice.A8));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A9))
      (Constraint.EqualZeroToPrecise (an Advice.A7));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A9))
      (Constraint.EqualZeroToPrecise (an Advice.A9))
  ].

  (** [CommitIvk canonicity check]: the [ak]/[nk] decompositions, their
      prime offsets, and the six clauses conditioned on the two top
      bits. *)
  Definition civk_bodies : list (Constraint.t columns) := [
    Constraint.Boolean (ac Advice.A4);
    Constraint.Boolean (an Advice.A4);
    Constraint.Equal (ac Advice.A2)
      (Expression.Sum
        (Expression.Sum (ac Advice.A3)
          (Expression.Scaled (ac Advice.A4) (2 ^ 4)))
        (Expression.Scaled (ac Advice.A5) (2 ^ 5)));
    Constraint.Equal (an Advice.A2)
      (Expression.Sum (an Advice.A3)
        (Expression.Scaled (an Advice.A4) (2 ^ 9)));
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A1)
          (Expression.Scaled (ac Advice.A3) (2 ^ 250)))
        (Expression.Scaled (ac Advice.A4) (2 ^ 254)))
      (ac Advice.A0);
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A5)
            (Expression.Scaled (an Advice.A1) (2 ^ 5)))
          (Expression.Scaled (an Advice.A3) (2 ^ 245)))
        (Expression.Scaled (an Advice.A4) (2 ^ 254)))
      (an Advice.A0);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A4))
      (Constraint.EqualZeroToPrecise (ac Advice.A3));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A4))
      (Constraint.EqualZeroToPrecise (ac Advice.A6));
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum (ac Advice.A1)
          (Expression.Constant (2 ^ 130)))
        (Expression.Negated tp_e))
      (ac Advice.A7);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (ac Advice.A4))
      (Constraint.EqualZeroToPrecise (ac Advice.A8));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A4))
      (Constraint.EqualZeroToPrecise (an Advice.A3));
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A4))
      (Constraint.EqualZeroToPrecise (an Advice.A6));
    Constraint.Equal
      (Expression.Sum
        (Expression.Sum
          (Expression.Sum (ac Advice.A5)
            (Expression.Scaled (an Advice.A1) (2 ^ 5)))
          (Expression.Constant (2 ^ 140)))
        (Expression.Negated tp_e))
      (an Advice.A7);
    Constraint.Either
      (Constraint.EqualZeroToPrecise (an Advice.A4))
      (Constraint.EqualZeroToPrecise (an Advice.A8))
  ].

  (** ** The gate-classification certificates

      Every constraint of the configured system guarded by one of the 23
      canonicity selectors is a body of that selector's gate. *)

  Lemma guarded_civk_eq : guarded Selector.QCommitIvk = civk_bodies.
  Proof.
    vm_cast_no_check
      (@eq_refl (list (Constraint.t columns)) (guarded Selector.QCommitIvk)).
  Qed.

  Lemma guarded_old_b : guarded Selector.QNoteCommitOldB = mpb_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldB)).
  Qed.

  Lemma guarded_new_b : guarded Selector.QNoteCommitNewB = mpb_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewB)).
  Qed.

  Lemma guarded_old_d : guarded Selector.QNoteCommitOldD = mpd_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldD)).
  Qed.

  Lemma guarded_new_d : guarded Selector.QNoteCommitNewD = mpd_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewD)).
  Qed.

  Lemma guarded_old_e : guarded Selector.QNoteCommitOldE = mpe_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldE)).
  Qed.

  Lemma guarded_new_e : guarded Selector.QNoteCommitNewE = mpe_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewE)).
  Qed.

  Lemma guarded_old_g : guarded Selector.QNoteCommitOldG = mpg_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldG)).
  Qed.

  Lemma guarded_new_g : guarded Selector.QNoteCommitNewG = mpg_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewG)).
  Qed.

  Lemma guarded_old_h : guarded Selector.QNoteCommitOldH = mph_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldH)).
  Qed.

  Lemma guarded_new_h : guarded Selector.QNoteCommitNewH = mph_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewH)).
  Qed.

  Lemma guarded_old_gd : guarded Selector.QNoteCommitOldGd = gd_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldGd)).
  Qed.

  Lemma guarded_new_gd : guarded Selector.QNoteCommitNewGd = gd_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewGd)).
  Qed.

  Lemma guarded_old_pkd :
    guarded Selector.QNoteCommitOldPkd = pkd_rho_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldPkd)).
  Qed.

  Lemma guarded_new_pkd :
    guarded Selector.QNoteCommitNewPkd = pkd_rho_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewPkd)).
  Qed.

  Lemma guarded_old_rho :
    guarded Selector.QNoteCommitOldRho = pkd_rho_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldRho)).
  Qed.

  Lemma guarded_new_rho :
    guarded Selector.QNoteCommitNewRho = pkd_rho_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewRho)).
  Qed.

  Lemma guarded_old_value :
    guarded Selector.QNoteCommitOldValue = value_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldValue)).
  Qed.

  Lemma guarded_new_value :
    guarded Selector.QNoteCommitNewValue = value_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewValue)).
  Qed.

  Lemma guarded_old_psi : guarded Selector.QNoteCommitOldPsi = psi_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldPsi)).
  Qed.

  Lemma guarded_new_psi : guarded Selector.QNoteCommitNewPsi = psi_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewPsi)).
  Qed.

  Lemma guarded_old_ycanon :
    guarded Selector.QNoteCommitOldYCanon = ycanon_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitOldYCanon)).
  Qed.

  Lemma guarded_new_ycanon :
    guarded Selector.QNoteCommitNewYCanon = ycanon_bodies.
  Proof.
    vm_cast_no_check (@eq_refl (list (Constraint.t columns))
      (guarded Selector.QNoteCommitNewYCanon)).
  Qed.

  (** ** Evaluation helpers *)

  (** Strip the field reductions from a reduced-form equality: after
      unfolding the operations both sides are outermost [mod p]; congruence
      modulo [p] removes the inner reductions and [f_equal] leaves the
      underlying integer identity, exact for the canonical slice cells. *)
  Ltac field_int :=
    cbv [BinOp.add BinOp.sub BinOp.mul UnOp.from UnOp.opp];
    lazymatch goal with
    | |- ?x mod ?q = ?y mod ?q => change (Zdiv.eqm q x y)
    end;
    repeat setoid_rewrite (Zdiv.Zmod_eqm Primes.pallas_p);
    unfold Zdiv.eqm;
    f_equal.

  (** Expose the constraint body over the honest cells: reduce the
      evaluator and the cell expression wrappers, then collapse the two
      literal row offsets. *)
  Ltac ev_cells :=
    cbn [eval_constraint eval_expression ac an tp_e];
    rewrite ?rot0c, ?rot0n.

  Lemma from_eq_zero (x : Z) : x = 0 -> UnOp.from x = 0.
  Proof. intros ->. exact from_zero. Qed.

  Lemma pow2_ge_one (k : Z) (Hk : 0 <= k) : 1 <= 2 ^ k.
  Proof.
    replace 1 with (2 ^ 0) by reflexivity.
    apply Z.pow_le_mono_r; lia.
  Qed.

  (** A shift never leaves the [t_P] window. *)
  Lemma div_tp (x k : Z) (Hk : 0 <= k) (Hx : 0 <= x < Primes.t_p) :
    0 <= x / 2 ^ k < Primes.t_p.
  Proof.
    pose proof (pow2_pos k Hk) as Hp.
    pose proof (pow2_ge_one k Hk) as H1.
    split; [apply Z.div_pos; lia |].
    apply Z.le_lt_trans with (m := x); [| lia].
    apply Z.div_le_upper_bound; [lia |].
    clear -H1 Hx. nia.
  Qed.

  (** Anything below [t_P] vanishes under a shift of at least 126 bits. *)
  Lemma div_small_tp (x k : Z) (Hk : 126 <= k) (Hx : 0 <= x < Primes.t_p) :
    x / 2 ^ k = 0.
  Proof.
    pose proof t_p_small.
    assert (H126 : 2 ^ 126 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
    apply Z.div_small. lia.
  Qed.

  Lemma p_lt_2_255 (x : Z) : 0 <= x < Primes.pallas_p -> 0 <= x < 2 ^ 255.
  Proof. pose proof pallas_p_lt. lia. Qed.

  (** ** The message-piece decomposition gates *)

  (** [NoteCommit MessagePiece b] at row 0. *)
  Lemma mpb_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (P : Z)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = nc_b P)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = nc_b0 P)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = nc_b1 P)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = nc_b2 P)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 = nc_b3 P) :
    forall body, List.In body mpb_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [<- | [<- | [] ] ] ]; ev_cells.
    - rewrite H8. apply isbool_from. unfold nc_b1. apply mod2_cases.
    - rewrite H7n. apply isbool_from. unfold nc_b2. apply mod2_cases.
    - rewrite H6, H7, H8, H7n, H8n.
      field_int.
      unfold nc_b0, nc_b1, nc_b2, nc_b3.
      apply recomb_b_piece.
  Qed.

  (** [NoteCommit MessagePiece d] at row 0. *)
  Lemma mpd_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (P : Z)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = nc_d P)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = nc_d0 P)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = nc_d1 P)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = nc_d2 P)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 = nc_d3 P) :
    forall body, List.In body mpd_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [<- | [<- | [] ] ] ]; ev_cells.
    - rewrite H7. apply isbool_from. unfold nc_d0. apply mod2_cases.
    - rewrite H8. apply isbool_from. unfold nc_d1. apply mod2_cases.
    - rewrite H6, H7, H8, H7n, H8n.
      field_int.
      unfold nc_d0, nc_d1, nc_d2, nc_d3.
      apply recomb_d_piece.
  Qed.

  (** [NoteCommit MessagePiece e] at row 0. *)
  Lemma mpe_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (P : Z)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = nc_e P)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = nc_e0 P)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = nc_e1 P) :
    forall body, List.In body mpe_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [] ]; ev_cells.
    rewrite H6, H7, H8.
    field_int.
    unfold nc_e0, nc_e1.
    apply recomb_e_piece.
  Qed.

  (** [NoteCommit MessagePiece g] at row 0. *)
  Lemma mpg_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (P : Z)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = nc_g P)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = nc_g0 P)
      (H6n : Gamma.(Assignment.advice) Advice.A6 region 1 = nc_g1 P)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = nc_g2 P) :
    forall body, List.In body mpg_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [<- | [] ] ]; ev_cells.
    - rewrite H7. apply isbool_from. unfold nc_g0. apply mod2_cases.
    - rewrite H6, H7, H6n, H7n.
      field_int.
      unfold nc_g0, nc_g1, nc_g2.
      apply recomb_g_piece.
  Qed.

  (** [NoteCommit MessagePiece h] at row 0.  The top sub-piece is a single
      bit because [ψ] is a reduced field element. *)
  Lemma mph_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (P : Z)
      (Hh1 : nc_h1 P = 0 \/ nc_h1 P = 1)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = nc_h P)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = nc_h0 P)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = nc_h1 P) :
    forall body, List.In body mph_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [<- | [] ] ]; ev_cells.
    - rewrite H8. apply isbool_from. exact Hh1.
    - rewrite H6, H7, H8.
      field_int.
      unfold nc_h0, nc_h1.
      apply recomb_h_piece.
  Qed.

  (** ** The input-decomposition gates *)

  (** [NoteCommit input g_d]: the 250/4/1 decomposition of a reduced field
      element [X] with the canonicity clauses under a set top bit. *)
  Lemma gd_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (X A L T AP : Z)
      (HX : 0 <= X < Primes.pallas_p)
      (HA : A = X mod 2 ^ 250)
      (HL : L = X / 2 ^ 250 mod 2 ^ 4)
      (HT : T = X / 2 ^ 254 mod 2)
      (HAP : AP = prime_of A 130)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = X)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = L)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = A)
      (H9 : Gamma.(Assignment.advice) Advice.A9 region 0 = A / 2 ^ 130)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = T)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 = AP)
      (H9n : Gamma.(Assignment.advice) Advice.A9 region 1 = AP / 2 ^ 130) :
    forall body, List.In body gd_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    pose proof (p_lt_2_255 X HX) as HX255.
    assert (Hcases : T = 0 \/ X / 2 ^ 254 mod 2 = 1).
    { subst T. destruct (mod2_cases (X / 2 ^ 254)) as [H | H]; auto. }
    intros body [<- | [<- | [<- | [<- | [<- | [] ] ] ] ] ]; ev_cells.
    - rewrite H6, H7, H8, H7n.
      field_int.
      subst A L T.
      apply recomb_250_4_1. exact HX255.
    - rewrite H8, H8n.
      subst AP. unfold prime_of.
      field_int; try reflexivity.
    - destruct Hcases as [HT0 | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HT0.
      + right. rewrite H7. apply from_eq_zero.
        subst L. exact (top1_slice_zero X 250 4 HX Htop ltac:(lia)
          ltac:(lia) ltac:(lia)).
    - destruct Hcases as [HT0 | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HT0.
      + right. rewrite H9. apply from_eq_zero.
        pose proof (top1_mod_low X 250 HX Htop ltac:(lia)) as Hlow.
        rewrite <- HA in Hlow.
        exact (div_small_tp A 130 ltac:(lia) Hlow).
    - destruct Hcases as [HT0 | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HT0.
      + right. rewrite H9n. apply from_eq_zero.
        pose proof (top1_mod_low X 250 HX Htop ltac:(lia)) as Hlow.
        rewrite <- HA in Hlow.
        subst AP. exact (prime_of_zero A 130 ltac:(lia) Hlow).
  Qed.

  (** [NoteCommit input pk_d] / [NoteCommit input rho]: the 4/250/1
      decomposition of a reduced field element [X] with the [2^140] prime
      offset. *)
  Lemma pkd_rho_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (X L M T PR : Z)
      (HX : 0 <= X < Primes.pallas_p)
      (HL : L = X mod 2 ^ 4)
      (HM : M = X / 2 ^ 4 mod 2 ^ 250)
      (HT : T = X / 2 ^ 254 mod 2)
      (HPR : PR = prime_of (L + M * 2 ^ 4) 140)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = X)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = L)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = M)
      (H9 : Gamma.(Assignment.advice) Advice.A9 region 0 = M / 2 ^ 130)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = T)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 = PR)
      (H9n : Gamma.(Assignment.advice) Advice.A9 region 1 = PR / 2 ^ 140) :
    forall body, List.In body pkd_rho_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    pose proof (p_lt_2_255 X HX) as HX255.
    assert (Hcases : T = 0 \/ X / 2 ^ 254 mod 2 = 1).
    { subst T. destruct (mod2_cases (X / 2 ^ 254)) as [H | H]; auto. }
    (* Under a set top bit the low 254 bits are the whole element and lie
       below [t_P]; the two window cells are its shifts. *)
    assert (Hwin : X / 2 ^ 254 mod 2 = 1 -> 0 <= L + M * 2 ^ 4 < Primes.t_p).
    { intros Htop.
      pose proof (top1_mod_low X 254 HX Htop ltac:(lia)) as Hlow.
      pose proof (split_mid X 4 254 ltac:(lia)) as Hsplit.
      replace (254 - 4) with 250 in Hsplit by lia.
      subst L M. lia. }
    intros body [<- | [<- | [<- | [<- | [] ] ] ] ]; ev_cells.
    - rewrite H6, H7, H8, H7n.
      field_int.
      subst L M T.
      apply recomb_4_250_1. exact HX255.
    - rewrite H7, H8, H8n.
      subst PR. unfold prime_of.
      field_int; try reflexivity.
    - destruct Hcases as [HT0 | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HT0.
      + right. rewrite H9. apply from_eq_zero.
        pose proof (Hwin Htop) as Hlow.
        assert (HM0 : 0 <= M < Primes.t_p).
        { pose proof (mod_bound X 4 ltac:(lia)).
          pose proof (pow2_pos 4 ltac:(lia)).
          assert (0 <= M) by (subst M; apply Z.mod_pos_bound, pow2_pos; lia).
          subst L. lia. }
        exact (div_small_tp M 130 ltac:(lia) HM0).
    - destruct Hcases as [HT0 | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HT0.
      + right. rewrite H9n. apply from_eq_zero.
        subst PR.
        exact (prime_of_zero (L + M * 2 ^ 4) 140 ltac:(lia) (Hwin Htop)).
  Qed.

  (** [NoteCommit input value]: the 8/50/6 split of the 64-bit value. *)
  Lemma value_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (V D2 D3 E0 : Z)
      (HV : 0 <= V < 2 ^ 64)
      (HD2 : D2 = V mod 2 ^ 8)
      (HD3 : D3 = V / 2 ^ 8 mod 2 ^ 50)
      (HE0 : E0 = V / 2 ^ 58 mod 2 ^ 6)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = V)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = D2)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = D3)
      (H9 : Gamma.(Assignment.advice) Advice.A9 region 0 = E0) :
    forall body, List.In body value_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    intros body [<- | [] ]; ev_cells.
    rewrite H6, H7, H8, H9.
    field_int.
    subst D2 D3 E0.
    apply recomb_value. exact HV.
  Qed.

  (** [NoteCommit input psi]: the 9/240/5/1 decomposition of [ψ].  The
      [z13] cell of the [g] piece carries the top bit of [ρ] above the low
      249 bits of [ψ] ([nc_g_low]), so it vanishes with them. *)
  Lemma psi_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (X G1 G2 H0 H1 GP ZG TB : Z)
      (HX : 0 <= X < Primes.pallas_p)
      (HG1 : G1 = X mod 2 ^ 9)
      (HG2 : G2 = X / 2 ^ 9 mod 2 ^ 240)
      (HH0 : H0 = X / 2 ^ 249 mod 2 ^ 5)
      (HH1 : H1 = X / 2 ^ 254 mod 2)
      (HGP : GP = prime_of (G1 + G2 * 2 ^ 9) 130)
      (HTB : 0 <= TB < 2)
      (HZG : ZG = (TB + X mod 2 ^ 249 * 2) / 2 ^ 130)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = X)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = G1)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 = G2)
      (H9 : Gamma.(Assignment.advice) Advice.A9 region 0 = ZG)
      (H6n : Gamma.(Assignment.advice) Advice.A6 region 1 = H0)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 = H1)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 = GP)
      (H9n : Gamma.(Assignment.advice) Advice.A9 region 1 = GP / 2 ^ 130) :
    forall body, List.In body psi_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    pose proof (p_lt_2_255 X HX) as HX255.
    assert (Hcases : H1 = 0 \/ X / 2 ^ 254 mod 2 = 1).
    { subst H1. destruct (mod2_cases (X / 2 ^ 254)) as [H | H]; auto. }
    (* Under a set top bit the low 249 bits are the whole element. *)
    assert (Hwin : X / 2 ^ 254 mod 2 = 1 -> 0 <= X mod 2 ^ 249 < Primes.t_p)
      by (intros Htop; exact (top1_mod_low X 249 HX Htop ltac:(lia))).
    assert (Hg12 : G1 + G2 * 2 ^ 9 = X mod 2 ^ 249).
    { pose proof (split_mid X 9 249 ltac:(lia)) as Hsplit.
      replace (249 - 9) with 240 in Hsplit by lia.
      subst G1 G2. lia. }
    intros body [<- | [<- | [<- | [<- | [<- | [] ] ] ] ] ]; ev_cells.
    - rewrite H6, H7, H8, H6n, H7n.
      field_int.
      subst G1 G2 H0 H1.
      apply recomb_9_240_5_1. exact HX255.
    - rewrite H7, H8, H8n.
      subst GP. unfold prime_of.
      field_int; try reflexivity.
    - destruct Hcases as [HH1z | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HH1z.
      + right. rewrite H6n. apply from_eq_zero.
        subst H0. exact (top1_slice_zero X 249 5 HX Htop ltac:(lia)
          ltac:(lia) ltac:(lia)).
    - destruct Hcases as [HH1z | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HH1z.
      + right. rewrite H9. apply from_eq_zero.
        pose proof (Hwin Htop) as Hlow.
        pose proof t_p_small as Htp.
        assert (H2130 : 2 * Primes.t_p + 2 <= 2 ^ 130).
        { assert (2 ^ 127 <= 2 ^ 130) by (apply Z.pow_le_mono_r; lia).
          assert (2 * 2 ^ 126 = 2 ^ 127) by reflexivity.
          lia. }
        subst ZG. apply Z.div_small. lia.
    - destruct Hcases as [HH1z | Htop].
      + left. rewrite H7n. apply from_eq_zero. exact HH1z.
      + right. rewrite H9n. apply from_eq_zero.
        subst GP. rewrite Hg12.
        exact (prime_of_zero (X mod 2 ^ 249) 130 ltac:(lia) (Hwin Htop)).
  Qed.

  (** ** The y-canonicity gate *)

  (** [y coordinate checks] at row 0, for either compressed subject. *)
  Lemma ycanon_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (Y : Z)
      (HY : 0 <= Y < Primes.pallas_p)
      (H5 : Gamma.(Assignment.advice) Advice.A5 region 0 = Y)
      (H6 : Gamma.(Assignment.advice) Advice.A6 region 0 = Y mod 2)
      (H7 : Gamma.(Assignment.advice) Advice.A7 region 0 = Y / 2 mod 2 ^ 9)
      (H8 : Gamma.(Assignment.advice) Advice.A8 region 0 =
        Y / 2 ^ 250 mod 2 ^ 4)
      (H9 : Gamma.(Assignment.advice) Advice.A9 region 0 = Y / 2 ^ 254)
      (H5n : Gamma.(Assignment.advice) Advice.A5 region 1 = Y mod 2 ^ 250)
      (H6n : Gamma.(Assignment.advice) Advice.A6 region 1 =
        Y mod 2 ^ 250 / 2 ^ 10)
      (H7n : Gamma.(Assignment.advice) Advice.A7 region 1 =
        Y mod 2 ^ 250 / 2 ^ 130)
      (H8n : Gamma.(Assignment.advice) Advice.A8 region 1 =
        prime_of (Y mod 2 ^ 250) 130)
      (H9n : Gamma.(Assignment.advice) Advice.A9 region 1 =
        prime_of (Y mod 2 ^ 250) 130 / 2 ^ 130) :
    forall body, List.In body ycanon_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    pose proof (p_lt_2_255 Y HY) as HY255.
    assert (Hk3 : 0 <= Y / 2 ^ 254 < 2).
    { split.
      - apply Z.div_pos; [lia | apply pow2_pos; lia].
      - apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia]. }
    assert (Hcases : Y / 2 ^ 254 = 0 \/ Y / 2 ^ 254 mod 2 = 1).
    { destruct (Z.eq_dec (Y / 2 ^ 254) 0) as [H | H]; [now left |].
      right. replace (Y / 2 ^ 254) with 1 by lia. reflexivity. }
    intros body [<- | [<- | [<- | [<- | [<- | [<- | [<- | [] ] ] ] ] ] ] ];
      ev_cells.
    - rewrite H9. apply isbool_from. lia.
    - rewrite H5n, H6, H7, H6n.
      field_int.
      apply recomb_j.
    - rewrite H5, H5n, H8, H9.
      field_int.
      apply recomb_y. exact HY255.
    - rewrite H5n, H8n.
      unfold prime_of.
      field_int; try reflexivity.
    - destruct Hcases as [Hz | Htop].
      + left. rewrite H9. apply from_eq_zero. exact Hz.
      + right. rewrite H8. apply from_eq_zero.
        exact (top1_slice_zero Y 250 4 HY Htop ltac:(lia) ltac:(lia)
          ltac:(lia)).
    - destruct Hcases as [Hz | Htop].
      + left. rewrite H9. apply from_eq_zero. exact Hz.
      + right. rewrite H7n. apply from_eq_zero.
        exact (div_small_tp (Y mod 2 ^ 250) 130 ltac:(lia)
          (top1_mod_low Y 250 HY Htop ltac:(lia))).
    - destruct Hcases as [Hz | Htop].
      + left. rewrite H9. apply from_eq_zero. exact Hz.
      + right. rewrite H9n. apply from_eq_zero.
        exact (prime_of_zero (Y mod 2 ^ 250) 130 ltac:(lia)
          (top1_mod_low Y 250 HY Htop ltac:(lia))).
  Qed.

  (** ** The [Commit^ivk] canonicity gate *)

  (** [CommitIvk canonicity check] at row 0: the [ak] face on the gate row
      and the [nk] face on the next row. *)
  Lemma civk_gate_eval (Gamma : Assignment.t columns RegionId.t)
      (region : RegionId.t) (AK NK A B B0 B1 B2 C D D0 D1 AP BCP : Z)
      (HAK : 0 <= AK < Primes.pallas_p)
      (HNK : 0 <= NK < Primes.pallas_p)
      (HA : A = AK mod 2 ^ 250)
      (HB0 : B0 = AK / 2 ^ 250 mod 2 ^ 4)
      (HB1 : B1 = AK / 2 ^ 254 mod 2)
      (HB2 : B2 = NK mod 2 ^ 5)
      (HB : B = B0 + B1 * 2 ^ 4 + B2 * 2 ^ 5)
      (HC : C = NK / 2 ^ 5 mod 2 ^ 240)
      (HD0 : D0 = NK / 2 ^ 245 mod 2 ^ 9)
      (HD1 : D1 = NK / 2 ^ 254 mod 2)
      (HD : D = D0 + D1 * 2 ^ 9)
      (HAP : AP = prime_of A 130)
      (HBCP : BCP = prime_of (B2 + C * 2 ^ 5) 140)
      (C0 : Gamma.(Assignment.advice) Advice.A0 region 0 = AK)
      (C1 : Gamma.(Assignment.advice) Advice.A1 region 0 = A)
      (C2 : Gamma.(Assignment.advice) Advice.A2 region 0 = B)
      (C3 : Gamma.(Assignment.advice) Advice.A3 region 0 = B0)
      (C4 : Gamma.(Assignment.advice) Advice.A4 region 0 = B1)
      (C5 : Gamma.(Assignment.advice) Advice.A5 region 0 = B2)
      (C6 : Gamma.(Assignment.advice) Advice.A6 region 0 = A / 2 ^ 130)
      (C7 : Gamma.(Assignment.advice) Advice.A7 region 0 = AP)
      (C8 : Gamma.(Assignment.advice) Advice.A8 region 0 = AP / 2 ^ 130)
      (N0 : Gamma.(Assignment.advice) Advice.A0 region 1 = NK)
      (N1 : Gamma.(Assignment.advice) Advice.A1 region 1 = C)
      (N2 : Gamma.(Assignment.advice) Advice.A2 region 1 = D)
      (N3 : Gamma.(Assignment.advice) Advice.A3 region 1 = D0)
      (N4 : Gamma.(Assignment.advice) Advice.A4 region 1 = D1)
      (N6 : Gamma.(Assignment.advice) Advice.A6 region 1 = C / 2 ^ 130)
      (N7 : Gamma.(Assignment.advice) Advice.A7 region 1 = BCP)
      (N8 : Gamma.(Assignment.advice) Advice.A8 region 1 = BCP / 2 ^ 140) :
    forall body, List.In body civk_bodies ->
      eval_constraint Gamma (region, 0) body.
  Proof.
    pose proof (p_lt_2_255 AK HAK) as HAK255.
    pose proof (p_lt_2_255 NK HNK) as HNK255.
    assert (Hak : B1 = 0 \/ AK / 2 ^ 254 mod 2 = 1).
    { subst B1. destruct (mod2_cases (AK / 2 ^ 254)) as [H | H]; auto. }
    assert (Hnk : D1 = 0 \/ NK / 2 ^ 254 mod 2 = 1).
    { subst D1. destruct (mod2_cases (NK / 2 ^ 254)) as [H | H]; auto. }
    assert (Halow : AK / 2 ^ 254 mod 2 = 1 -> 0 <= A < Primes.t_p).
    { intros Htop. subst A. exact (top1_mod_low AK 250 HAK Htop
        ltac:(lia)). }
    assert (Hnlow : NK / 2 ^ 254 mod 2 = 1 ->
      0 <= B2 + C * 2 ^ 5 < Primes.t_p).
    { intros Htop.
      pose proof (top1_mod_low NK 245 HNK Htop ltac:(lia)) as Hlow.
      pose proof (split_mid NK 5 245 ltac:(lia)) as Hsplit.
      replace (245 - 5) with 240 in Hsplit by lia.
      subst B2 C. lia. }
    intros body
      [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- |
       [<- | [<- | [<- | [] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; ev_cells.
    - rewrite C4. apply isbool_from. subst B1. apply mod2_cases.
    - rewrite N4. apply isbool_from. subst D1. apply mod2_cases.
    - rewrite C2, C3, C4, C5.
      field_int.
      exact HB.
    - rewrite N2, N3, N4.
      field_int.
      exact HD.
    - rewrite C0, C1, C3, C4.
      field_int.
      subst A B0 B1.
      apply recomb_250_4_1. exact HAK255.
    - rewrite N0, N1, N3, N4, C5.
      field_int.
      subst B2 C D0 D1.
      apply recomb_5_240_9_1. exact HNK255.
    - destruct Hak as [Hz | Htop].
      + left. rewrite C4. apply from_eq_zero. exact Hz.
      + right. rewrite C3. apply from_eq_zero.
        subst B0. exact (top1_slice_zero AK 250 4 HAK Htop ltac:(lia)
          ltac:(lia) ltac:(lia)).
    - destruct Hak as [Hz | Htop].
      + left. rewrite C4. apply from_eq_zero. exact Hz.
      + right. rewrite C6. apply from_eq_zero.
        exact (div_small_tp A 130 ltac:(lia) (Halow Htop)).
    - rewrite C1, C7.
      subst AP. unfold prime_of.
      field_int; try reflexivity.
    - destruct Hak as [Hz | Htop].
      + left. rewrite C4. apply from_eq_zero. exact Hz.
      + right. rewrite C8. apply from_eq_zero.
        subst AP. exact (prime_of_zero A 130 ltac:(lia) (Halow Htop)).
    - destruct Hnk as [Hz | Htop].
      + left. rewrite N4. apply from_eq_zero. exact Hz.
      + right. rewrite N3. apply from_eq_zero.
        subst D0. exact (top1_slice_zero NK 245 9 HNK Htop ltac:(lia)
          ltac:(lia) ltac:(lia)).
    - destruct Hnk as [Hz | Htop].
      + left. rewrite N4. apply from_eq_zero. exact Hz.
      + right. rewrite N6. apply from_eq_zero.
        pose proof (Hnlow Htop) as Hlow.
        assert (HC0 : 0 <= C < Primes.t_p).
        { assert (0 <= B2) by (subst B2; apply Z.mod_pos_bound; lia).
          assert (0 <= C) by (subst C; apply Z.mod_pos_bound, pow2_pos;
            lia).
          lia. }
        exact (div_small_tp C 130 ltac:(lia) HC0).
    - rewrite C5, N1, N7.
      subst BCP. unfold prime_of.
      field_int; try reflexivity.
    - destruct Hnk as [Hz | Htop].
      + left. rewrite N4. apply from_eq_zero. exact Hz.
      + right. rewrite N8. apply from_eq_zero.
        subst BCP.
        exact (prime_of_zero (B2 + C * 2 ^ 5) 140 ltac:(lia)
          (Hnlow Htop)).
  Qed.

  (** ** The generator's packed messages *)

  (** The packed §5.4.8.4 message of each note ([ρ] of the new note is the
      old note's spec nullifier, read from the hoisted record) and the
      packed [Commit^ivk] message. *)
  Definition nc_pk_old (w : HonestInput) : Z :=
    nc_packed (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
      (hi_psi_old w).
  Definition nc_pk_new (w : HonestInput) : Z :=
    nc_packed (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w).
  Definition civk_pk (w : HonestInput) : Z :=
    civk_packed (EccSpec.extract_x (hi_ak w)) (hi_nk w).

  (** ** The completeness domain's ranges *)

  Definition note_ranges (gd pkd : Point.t) (v rho psi : Z) : Prop :=
    0 <= EccSpec.extract_x gd < Primes.pallas_p /\
    0 <= Point.y gd < Primes.pallas_p /\
    0 <= EccSpec.extract_x pkd < Primes.pallas_p /\
    0 <= Point.y pkd < Primes.pallas_p /\
    0 <= v < 2 ^ 64 /\
    0 <= rho < Primes.pallas_p /\
    0 <= psi < Primes.pallas_p.

  Lemma wt_parts (w : HonestInput) (Hv : valid w) :
    (0 <= hi_v_old w < 2 ^ 64) /\ (0 <= hi_v_new w < 2 ^ 64) /\
    (0 <= hi_nk w < Primes.pallas_p) /\
    (0 <= hi_rho_old w < Primes.pallas_p) /\
    (0 <= hi_psi_old w < Primes.pallas_p) /\
    (0 <= hi_psi_new w < Primes.pallas_p) /\
    point_ok (hi_ak w) /\ point_ok (hi_g_d_old w) /\
    point_ok (hi_pk_d_old w) /\ point_ok (hi_g_d_new w) /\
    point_ok (hi_pk_d_new w).
  Proof.
    destruct Hv as (Hwt & _).
    unfold well_typed in Hwt.
    destruct Hwt as (A1 & A2 & _ & _ & _ & _ & _ & A8 & A9 & A10 & A11 & _ &
      A13 & A14 & A15 & A16 & A17 & _).
    split; [exact A1 |]. split; [exact A2 |]. split; [exact A8 |].
    split; [exact A9 |]. split; [exact A10 |]. split; [exact A11 |].
    split; [exact A13 |]. split; [exact A14 |]. split; [exact A15 |].
    split; [exact A16 |]. exact A17.
  Qed.

  Lemma note_ranges_old (w : HonestInput) (Hv : valid w) :
    note_ranges (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
      (hi_psi_old w).
  Proof.
    destruct (wt_parts w Hv) as (Hvo & _ & _ & Hrho & Hpsi & _ & _ & Hgd &
      Hpkd & _).
    destruct (point_ok_coords _ Hgd) as [Hgx Hgy].
    destruct (point_ok_coords _ Hpkd) as [Hpx Hpy].
    unfold note_ranges, EccSpec.extract_x.
    split; [exact Hgx |]. split; [exact Hgy |].
    split; [exact Hpx |]. split; [exact Hpy |].
    split; [exact Hvo |]. split; [exact Hrho |]. exact Hpsi.
  Qed.

  Lemma note_ranges_new (w : HonestInput) (Hv : valid w) :
    note_ranges (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w).
  Proof.
    destruct (wt_parts w Hv) as (_ & Hvn & _ & _ & _ & Hpsi & _ & _ & _ &
      Hgd & Hpkd).
    destruct (point_ok_coords _ Hgd) as [Hgx Hgy].
    destruct (point_ok_coords _ Hpkd) as [Hpx Hpy].
    unfold note_ranges, EccSpec.extract_x.
    split; [exact Hgx |]. split; [exact Hgy |].
    split; [exact Hpx |]. split; [exact Hpy |].
    split; [exact Hvn |]. split; [exact (t_nf_spec_range w) |]. exact Hpsi.
  Qed.

  Lemma ak_range (w : HonestInput) (Hv : valid w) :
    0 <= EccSpec.extract_x (hi_ak w) < Primes.pallas_p.
  Proof.
    destruct (wt_parts w Hv) as (_ & _ & _ & _ & _ & _ & Hak & _).
    exact (proj1 (point_ok_coords _ Hak)).
  Qed.

  Lemma nk_range (w : HonestInput) (Hv : valid w) :
    0 <= hi_nk w < Primes.pallas_p.
  Proof.
    destruct (wt_parts w Hv) as (_ & _ & Hnk & _). exact Hnk.
  Qed.

  (** A reduced field element's top bit, read at either window width. *)
  Lemma top_bit_lt (x : Z) (Hx : 0 <= x < Primes.pallas_p) :
    0 <= x / 2 ^ 254 < 2.
  Proof.
    pose proof (p_lt_2_255 x Hx).
    split.
    - apply Z.div_pos; [lia | apply pow2_pos; lia].
    - apply Z.div_lt_upper_bound; [apply pow2_pos; lia | lia].
  Qed.

  (** ** The generator's slices are the canonical slices *)

  Section NoteSlices.
    Context {gd pkd : Point.t} {v rho psi : Z}.
    Context (HR : note_ranges gd pkd v rho psi).

    Local Notation P := (nc_packed gd pkd v rho psi).

    Lemma s_xg : 0 <= EccSpec.extract_x gd < 2 ^ 255.
    Proof. apply p_lt_2_255. exact (proj1 HR). Qed.

    Lemma s_xp : 0 <= EccSpec.extract_x pkd < 2 ^ 255.
    Proof.
      apply p_lt_2_255. exact (proj1 (proj2 (proj2 HR))).
    Qed.

    Lemma s_v : 0 <= v < 2 ^ 64.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))). Qed.

    Lemma s_rho : 0 <= rho < Primes.pallas_p.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))). Qed.

    Lemma s_psi : 0 <= psi < Primes.pallas_p.
    Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))). Qed.

    Lemma s_rho255 : 0 <= rho < 2 ^ 255.
    Proof. apply p_lt_2_255. exact s_rho. Qed.

    Lemma s_b3 : nc_b3 P = EccSpec.extract_x pkd mod 2 ^ 4.
    Proof. apply nc_b3_eq. exact s_xg. Qed.

    Lemma s_c : nc_c P = EccSpec.extract_x pkd / 2 ^ 4 mod 2 ^ 250.
    Proof. apply nc_c_eq. exact s_xg. Qed.

    Lemma s_d0 : nc_d0 P = EccSpec.extract_x pkd / 2 ^ 254 mod 2.
    Proof. apply nc_d0_eq. exact s_xg. Qed.

    Lemma s_d2 : nc_d2 P = v mod 2 ^ 8.
    Proof. apply nc_d2_eq; [exact s_xg | exact s_xp]. Qed.

    Lemma s_d3 : nc_d3 P = v / 2 ^ 8 mod 2 ^ 50.
    Proof. apply nc_d3_eq; [exact s_xg | exact s_xp]. Qed.

    Lemma s_e0 : nc_e0 P = v / 2 ^ 58 mod 2 ^ 6.
    Proof. apply nc_e0_eq; [exact s_xg | exact s_xp]. Qed.

    Lemma s_e1 : nc_e1 P = rho mod 2 ^ 4.
    Proof. apply nc_e1_eq; [exact s_xg | exact s_xp | exact s_v]. Qed.

    Lemma s_f : nc_f P = rho / 2 ^ 4 mod 2 ^ 250.
    Proof. apply nc_f_eq; [exact s_xg | exact s_xp | exact s_v]. Qed.

    Lemma s_g0 : nc_g0 P = rho / 2 ^ 254 mod 2.
    Proof. apply nc_g0_eq; [exact s_xg | exact s_xp | exact s_v]. Qed.

    Lemma s_g1 : nc_g1 P = psi mod 2 ^ 9.
    Proof.
      apply nc_g1_eq;
        [exact s_xg | exact s_xp | exact s_v | exact s_rho255].
    Qed.

    Lemma s_g2 : nc_g2 P = psi / 2 ^ 9 mod 2 ^ 240.
    Proof.
      apply nc_g2_eq;
        [exact s_xg | exact s_xp | exact s_v | exact s_rho255].
    Qed.

    Lemma s_h0 : nc_h0 P = psi / 2 ^ 249 mod 2 ^ 5.
    Proof.
      apply nc_h0_eq;
        [exact s_xg | exact s_xp | exact s_v | exact s_rho255].
    Qed.

    (** The top sub-piece of [h] is the top bit of [ψ]: reduced elements
        leave the remaining four bits of the slice zero. *)
    Lemma s_h1 : nc_h1 P = psi / 2 ^ 254 mod 2.
    Proof.
      pose proof (top_bit_lt psi s_psi) as Hb.
      rewrite (nc_h1_eq gd pkd v rho psi s_xg s_xp s_v s_rho255).
      rewrite (Z.mod_small (psi / 2 ^ 254) (2 ^ 5))
        by (change (2 ^ 5) with 32; lia).
      rewrite Z.mod_small by lia.
      reflexivity.
    Qed.

    Lemma s_h1_bool : nc_h1 P = 0 \/ nc_h1 P = 1.
    Proof.
      pose proof (top_bit_lt psi s_psi) as Hb.
      rewrite s_h1.
      rewrite Z.mod_small by lia.
      lia.
    Qed.

    Lemma s_glow : nc_g P = rho / 2 ^ 254 + psi mod 2 ^ 249 * 2.
    Proof.
      apply nc_g_low;
        [exact s_xg | exact s_xp | exact s_v | exact s_rho255].
    Qed.

    Lemma s_tb : 0 <= rho / 2 ^ 254 < 2.
    Proof. exact (top_bit_lt rho s_rho). Qed.
  End NoteSlices.

  (** ** The cell-shape discharge

      Reduce the generator dispatch on the concrete region and cell address
      to the [tables_nc.v] slice reader, then compare syntactically; the
      hoisted record stays folded (the new note's [ρ] is one of its
      projections). *)
  Ltac nc_cell :=
    rewrite advice_eq;
    cbn [OCT.advice_t OrchardNoteCommitCells.nc_advice
         OrchardNoteCommitCells.civk_advice
         OrchardNoteCommitCells.ycanon_advice];
    cbv [nc_pk_old nc_pk_new civk_pk
         OrchardNoteCommitCells.ycanon_lsb OrchardNoteCommitCells.ycanon_k0
         OrchardNoteCommitCells.ycanon_k2 OrchardNoteCommitCells.ycanon_k3
         OrchardNoteCommitCells.ycanon_j
         OrchardNoteCommitCells.ycanon_j_prime];
    reflexivity.

  (** ** The per-point obligations of families 38, 39 and 40 *)

  (** The subregions of a note block whose cells the [tables_nc.v] slice
      layer owns and reads independently of the message-piece witness
      column: the hash region, the fixed-base blinding leg and the two
      complete additions are routed to sibling sub-generators, and the
      witnessed message pieces sit on a configuration-dependent column. *)
  Definition nc_dispatched (r : RegionId.NoteCommit.t) : bool :=
    match r with
    | RegionId.NoteCommit.HashToPoint
    | RegionId.NoteCommit.FixedBaseIncomplete
    | RegionId.NoteCommit.FixedBaseLast
    | RegionId.NoteCommit.CompletePointAdd
    | RegionId.NoteCommit.WitnessA | RegionId.NoteCommit.WitnessB
    | RegionId.NoteCommit.WitnessC | RegionId.NoteCommit.WitnessD
    | RegionId.NoteCommit.WitnessE | RegionId.NoteCommit.WitnessF
    | RegionId.NoteCommit.WitnessG | RegionId.NoteCommit.WitnessH => false
    | _ => true
    end.

  Lemma disp_old (w : HonestInput) (nregion : RegionId.NoteCommit.t)
      (Hd : nc_dispatched nregion = true) (col : Advice.t) (row : Z) :
    OCT.advice_t w (OCT.tables_of w) col
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old nregion) row =
    nc_advice (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
      (hi_psi_old w) false nregion col row.
  Proof. destruct nregion; try discriminate Hd; reflexivity. Qed.

  Lemma disp_new (w : HonestInput) (nregion : RegionId.NoteCommit.t)
      (Hd : nc_dispatched nregion = true) (col : Advice.t) (row : Z) :
    OCT.advice_t w (OCT.tables_of w) col
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New nregion) row =
    nc_advice (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w) false nregion col row.
  Proof. destruct nregion; try discriminate Hd; reflexivity. Qed.

  (** Reduce a cell of a note block to its slice through the block's
      dispatch equation. *)
  Ltac ncell H :=
    rewrite advice_eq, H;
    cbn [OrchardNoteCommitCells.nc_advice
         OrchardNoteCommitCells.ycanon_advice];
    cbv [OrchardNoteCommitCells.ycanon_lsb
         OrchardNoteCommitCells.ycanon_k0
         OrchardNoteCommitCells.ycanon_k2
         OrchardNoteCommitCells.ycanon_k3
         OrchardNoteCommitCells.ycanon_j
         OrchardNoteCommitCells.ycanon_j_prime];
    reflexivity.

  Lemma nc_pt_b (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.MessagePieceB col row) :
    forall body, List.In body mpb_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (mpb_gate_eval _ _ (nc_packed gd pkd v rho psi) _ _ _ _ _);
      ncell Hd.
  Qed.

  Lemma nc_pt_d (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.MessagePieceD col row) :
    forall body, List.In body mpd_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (mpd_gate_eval _ _ (nc_packed gd pkd v rho psi) _ _ _ _ _);
      ncell Hd.
  Qed.

  Lemma nc_pt_e (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.MessagePieceE col row) :
    forall body, List.In body mpe_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (mpe_gate_eval _ _ (nc_packed gd pkd v rho psi) _ _ _);
      ncell Hd.
  Qed.

  Lemma nc_pt_g (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.MessagePieceG col row) :
    forall body, List.In body mpg_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (mpg_gate_eval _ _ (nc_packed gd pkd v rho psi) _ _ _ _);
      ncell Hd.
  Qed.

  Lemma nc_pt_h (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.MessagePieceH col row) :
    forall body, List.In body mph_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (mph_gate_eval _ _ (nc_packed gd pkd v rho psi) (s_h1_bool HR)
      _ _ _);
      ncell Hd.
  Qed.

  Lemma nc_pt_gd (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.InputGD col row) :
    forall body, List.In body gd_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (gd_gate_eval _ _ (EccSpec.extract_x gd)
      (nc_a (nc_packed gd pkd v rho psi))
      (nc_b0 (nc_packed gd pkd v rho psi))
      (nc_b1 (nc_packed gd pkd v rho psi))
      (nc_a_prime (nc_packed gd pkd v rho psi))
      (proj1 HR) _ _ _ eq_refl _ _ _ _ _ _ _);
      [ apply nc_a_eq | apply nc_b0_eq | apply nc_b1_eq
      | ncell Hd .. ].
  Qed.

  Lemma nc_pt_pkd (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.InputPkD col row) :
    forall body, List.In body pkd_rho_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (pkd_rho_gate_eval _ _ (EccSpec.extract_x pkd)
      (nc_b3 (nc_packed gd pkd v rho psi))
      (nc_c (nc_packed gd pkd v rho psi))
      (nc_d0 (nc_packed gd pkd v rho psi))
      (nc_b3_c_prime (nc_packed gd pkd v rho psi))
      (proj1 (proj2 (proj2 HR))) _ _ _ eq_refl _ _ _ _ _ _ _);
      [ exact (s_b3 HR) | exact (s_c HR) | exact (s_d0 HR)
      | ncell Hd .. ].
  Qed.

  Lemma nc_pt_value (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.InputValue col row) :
    forall body, List.In body value_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (value_gate_eval _ _ v
      (nc_d2 (nc_packed gd pkd v rho psi))
      (nc_d3 (nc_packed gd pkd v rho psi))
      (nc_e0 (nc_packed gd pkd v rho psi))
      (s_v HR) _ _ _ _ _ _ _);
      [ exact (s_d2 HR) | exact (s_d3 HR) | exact (s_e0 HR)
      | ncell Hd .. ].
  Qed.

  Lemma nc_pt_rho (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.InputRho col row) :
    forall body, List.In body pkd_rho_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (pkd_rho_gate_eval _ _ rho
      (nc_e1 (nc_packed gd pkd v rho psi))
      (nc_f (nc_packed gd pkd v rho psi))
      (nc_g0 (nc_packed gd pkd v rho psi))
      (nc_e1_f_prime (nc_packed gd pkd v rho psi))
      (s_rho HR) _ _ _ eq_refl _ _ _ _ _ _ _);
      [ exact (s_e1 HR) | exact (s_f HR) | exact (s_g0 HR)
      | ncell Hd .. ].
  Qed.

  Lemma nc_pt_psi (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          RegionId.NoteCommit.InputPsi col row) :
    forall body, List.In body psi_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (psi_gate_eval _ _ psi
      (nc_g1 (nc_packed gd pkd v rho psi))
      (nc_g2 (nc_packed gd pkd v rho psi))
      (nc_h0 (nc_packed gd pkd v rho psi))
      (nc_h1 (nc_packed gd pkd v rho psi))
      (nc_g1_g2_prime (nc_packed gd pkd v rho psi))
      (nc_g (nc_packed gd pkd v rho psi) / 2 ^ 130) (rho / 2 ^ 254)
      (s_psi HR) _ _ _ _ eq_refl (s_tb HR) _ _ _ _ _ _ _ _ _);
      [ exact (s_g1 HR) | exact (s_g2 HR) | exact (s_h0 HR)
      | exact (s_h1 HR)
      | rewrite (s_glow HR); reflexivity
      | ncell Hd .. ].
  Qed.

  Lemma nc_pt_ygd (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
            RegionId.NoteCommit.YCanonicity.Gate) col row) :
    forall body, List.In body ycanon_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (ycanon_gate_eval _ _ (Point.y gd) (proj1 (proj2 HR))
      _ _ _ _ _ _ _ _ _ _); ncell Hd.
  Qed.

  Lemma nc_pt_ypkd (w : HonestInput) (region : RegionId.t)
      (gd pkd : Point.t) (v rho psi : Z)
      (HR : note_ranges gd pkd v rho psi)
      (Hd : forall (col : Advice.t) (row : Z),
        OCT.advice_t w (OCT.tables_of w) col region row =
        nc_advice gd pkd v rho psi false
          (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
            RegionId.NoteCommit.YCanonicity.Gate) col row) :
    forall body, List.In body ycanon_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (region, 0) body.
  Proof.
    refine (ycanon_gate_eval _ _ (Point.y pkd)
      (proj1 (proj2 (proj2 (proj2 HR)))) _ _ _ _ _ _ _ _ _ _); ncell Hd.
  Qed.

  (** The [Commit^ivk] canonicity gate row. *)
  Lemma civk_pt (w : HonestInput) (Hv : valid w) :
    forall body, List.In body civk_bodies ->
      eval_constraint (OrchardHonestAssignment.honest_assignment w)
        (RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate, 0) body.
  Proof.
    pose proof (ak_range w Hv) as Hak.
    pose proof (nk_range w Hv) as Hnk.
    pose proof (p_lt_2_255 _ Hak) as Hak255.
    refine (civk_gate_eval _ _ (EccSpec.extract_x (hi_ak w)) (hi_nk w)
      (civk_a (civk_pk w)) (civk_b (civk_pk w)) (civk_b0 (civk_pk w))
      (civk_b1 (civk_pk w)) (civk_b2 (civk_pk w)) (civk_c (civk_pk w))
      (civk_d (civk_pk w)) (civk_d0 (civk_pk w)) (civk_d1 (civk_pk w))
      (civk_a_prime (civk_pk w)) (civk_b2_c_prime (civk_pk w))
      Hak Hnk _ _ _ _ _ _ _ _ _ eq_refl eq_refl
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [ apply civk_a_eq
      | apply civk_b0_eq
      | apply civk_b1_eq
      | apply civk_b2_eq; exact Hak255
      | unfold civk_b0, civk_b1, civk_b2; apply recomb_civk_b
      | apply civk_c_eq; exact Hak255
      | apply civk_d0_eq; exact Hak255
      | apply civk_d1_eq; exact Hak255
      | unfold civk_d0, civk_d1; apply recomb_civk_d
      | nc_cell .. ].
  Qed.

  (** ** The family obligation

      Every enabled point of families 38, 39 and 40 is either one of the 25
      canonicity gate rows above or is guarded by a selector whose forward
      obligation belongs to another lane: the ecc-add group
      ([forward/ecc_add.v]), the full-width fixed-base windows
      ([forward/fixed_base.v]), the range-check and bitshift selectors
      ([forward/running_sums.v]), or the Sinsemilla hash rounds. *)

  Definition delegated_sel (s : Selector.t) : bool :=
    match s with
    | Selector.QLookup | Selector.QRunning | Selector.QBitshift
    | Selector.QAddIncomplete | Selector.QEccAdd
    | Selector.QMulFixedFull
    | Selector.QSinsemilla1_1 | Selector.QSinsemilla4_1
    | Selector.QSinsemilla1_2 | Selector.QSinsemilla4_2 => true
    | _ => false
    end.

  Definition is_sins_sel (s : Selector.t) : bool :=
    match s with
    | Selector.QSinsemilla1_1 | Selector.QSinsemilla4_1
    | Selector.QSinsemilla1_2 | Selector.QSinsemilla4_2 => true
    | _ => false
    end.

  (** The hash-round points of these families: the note-commitment and
      [Commit^ivk] hash regions, discharged by the Sinsemilla forward lane
      ([forward/sinsemilla.v], whose selector group is this one). *)
  Lemma sinsemilla_residual (w : HonestInput)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (sel : Selector.t) (region : RegionId.t) (row : Z)
      (Hin : List.In (sel, region, row) enabled)
      (Hsel : is_sins_sel sel = true)
      (gate : Gate.t columns)
      (Hgate : List.In gate system.(ConstraintSystem.gates))
      (name : option string) (body : Constraint.t columns)
      (Hbody : List.In (name, Constraint.Select sel body)
        gate.(Gate.constraints)) :
    eval_constraint (OrchardHonestAssignment.honest_assignment w)
      (region, row) body.
  Proof.
    refine (OrchardForwardSinsemilla.sinsemilla_gates_forward w Hvalid
      Hnondeg sel region row Hin _ gate Hgate name body Hbody).
    destruct sel; try discriminate Hsel; reflexivity.
  Qed.

  Definition pt_eqb (a b : Selector.t * RegionId.t * Z) : bool :=
    let '(s1, r1, o1) := a in
    let '(s2, r2, o2) := b in
    OrchardDecidableEq.selector_eqb s1 s2 &&
    OrchardDecidableEq.region_id_eqb r1 r2 && (o1 =? o2).

  Lemma pt_eqb_eq (a b : Selector.t * RegionId.t * Z) :
    pt_eqb a b = true -> a = b.
  Proof.
    destruct a as [ [s1 r1] o1].
    destruct b as [ [s2 r2] o2].
    cbn.
    intros H.
    apply andb_true_iff in H; destruct H as [H Ho].
    apply andb_true_iff in H; destruct H as [Hs Hr].
    apply OrchardDecidableEq.selector_eqb_eq in Hs.
    apply OrchardDecidableEq.region_id_eqb_eq in Hr.
    apply Z.eqb_eq in Ho.
    now subst.
  Qed.

  (** The 25 canonicity gate rows of the three families. *)
  Definition canon_points : list (Selector.t * RegionId.t * Z) := [
    (Selector.QCommitIvk,
      RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate, 0);
    (Selector.QNoteCommitOldB,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.MessagePieceB, 0);
    (Selector.QNoteCommitOldD,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.MessagePieceD, 0);
    (Selector.QNoteCommitOldE,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.MessagePieceE, 0);
    (Selector.QNoteCommitOldG,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.MessagePieceG, 0);
    (Selector.QNoteCommitOldH,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.MessagePieceH, 0);
    (Selector.QNoteCommitOldGd,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputGD, 0);
    (Selector.QNoteCommitOldPkd,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputPkD, 0);
    (Selector.QNoteCommitOldValue,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputValue, 0);
    (Selector.QNoteCommitOldRho,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputRho, 0);
    (Selector.QNoteCommitOldPsi,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputPsi, 0);
    (Selector.QNoteCommitOldYCanon,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.Gate), 0);
    (Selector.QNoteCommitOldYCanon,
      RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.Gate), 0);
    (Selector.QNoteCommitNewB,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.MessagePieceB, 0);
    (Selector.QNoteCommitNewD,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.MessagePieceD, 0);
    (Selector.QNoteCommitNewE,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.MessagePieceE, 0);
    (Selector.QNoteCommitNewG,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.MessagePieceG, 0);
    (Selector.QNoteCommitNewH,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.MessagePieceH, 0);
    (Selector.QNoteCommitNewGd,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputGD, 0);
    (Selector.QNoteCommitNewPkd,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputPkD, 0);
    (Selector.QNoteCommitNewValue,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputValue, 0);
    (Selector.QNoteCommitNewRho,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputRho, 0);
    (Selector.QNoteCommitNewPsi,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.InputPsi, 0);
    (Selector.QNoteCommitNewYCanon,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.Gate), 0);
    (Selector.QNoteCommitNewYCanon,
      RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.Gate), 0)
  ].

  (** Every enabled point of the three families is delegated or canonical. *)
  Lemma shard_classify :
    List.forallb (fun pt =>
      let '(sel, _, _) := pt in
      delegated_sel sel || List.existsb (pt_eqb pt) canon_points)
      (shard_in [38; 39; 40]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma canon_point_in (sel : Selector.t) (region : RegionId.t) (row : Z)
      (Hin : List.In (sel, region, row) enabled)
      (Hfam : List.In (family_index region) [38; 39; 40]) :
    List.In (sel, region, row) (shard_in [38; 39; 40]).
  Proof.
    apply List.filter_In.
    split; [exact Hin |].
    cbn.
    destruct Hfam as [Hf | [Hf | [Hf | Habs] ] ]; try destruct Habs;
      rewrite <- Hf;
      rewrite Z.eqb_refl;
      reflexivity.
  Qed.

  Theorem canonicity_gates_ok : family_gates_ok [38; 39; 40].
  Proof.
    intros w Hvalid Hnondeg sel region row Hin Hfam gate Hgate name body
      Hbody.
    pose proof (canon_point_in sel region row Hin Hfam) as Hpt.
    pose proof (proj1 (List.forallb_forall _ _) shard_classify _ Hpt)
      as Hcl.
    cbn beta iota in Hcl.
    apply orb_true_iff in Hcl.
    destruct Hcl as [Hdel | Hcanon].
    - (* Delegated selectors: the other forward lanes. *)
      destruct sel; try discriminate Hdel.
      + exact (OrchardForwardRunningSums.qlookup_gates_ok w Hvalid Hnondeg
          region row Hin gate Hgate name body Hbody).
      + exact (OrchardForwardRunningSums.qrunning_gates_ok w Hvalid Hnondeg
          region row Hin gate Hgate name body Hbody).
      + exact (OrchardForwardRunningSums.qbitshift_gates_ok w Hvalid Hnondeg
          region row Hin gate Hgate name body Hbody).
      + exact (OrchardCompletenessForwardEccAdd.ecc_add_gates_forward w
          Hvalid Hnondeg _ region row Hin eq_refl gate Hgate name body
          Hbody).
      + exact (OrchardCompletenessForwardEccAdd.ecc_add_gates_forward w
          Hvalid Hnondeg _ region row Hin eq_refl gate Hgate name body
          Hbody).
      + exact (OrchardForwardFixedBase.q_mul_fixed_full_gates_ok w Hvalid
          Hnondeg region row Hin gate Hgate name body Hbody).
      + exact (sinsemilla_residual w Hvalid Hnondeg _ region row Hin
          eq_refl gate Hgate name body Hbody).
      + exact (sinsemilla_residual w Hvalid Hnondeg _ region row Hin
          eq_refl gate Hgate name body Hbody).
      + exact (sinsemilla_residual w Hvalid Hnondeg _ region row Hin
          eq_refl gate Hgate name body Hbody).
      + exact (sinsemilla_residual w Hvalid Hnondeg _ region row Hin
          eq_refl gate Hgate name body Hbody).
    - (* The 25 canonicity gate rows. *)
      pose proof (guarded_complete sel gate name body Hgate Hbody) as Hb.
      clear Hgate Hbody Hpt Hin Hfam.
      apply List.existsb_exists in Hcanon.
      destruct Hcanon as [q [Hq Heq] ].
      apply pt_eqb_eq in Heq.
      subst q.
      pose proof (note_ranges_old w Hvalid) as HRo.
      pose proof (note_ranges_new w Hvalid) as HRn.
      cbn in Hq.
      destruct Hq as
        [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E |
        [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E |
        [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
        injection E as <- <- <-.
      + rewrite guarded_civk_eq in Hb. exact (civk_pt w Hvalid body Hb).
      + rewrite guarded_old_b in Hb.
        exact (nc_pt_b w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.MessagePieceB eq_refl) body Hb).
      + rewrite guarded_old_d in Hb.
        exact (nc_pt_d w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.MessagePieceD eq_refl) body Hb).
      + rewrite guarded_old_e in Hb.
        exact (nc_pt_e w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.MessagePieceE eq_refl) body Hb).
      + rewrite guarded_old_g in Hb.
        exact (nc_pt_g w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.MessagePieceG eq_refl) body Hb).
      + rewrite guarded_old_h in Hb.
        exact (nc_pt_h w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.MessagePieceH eq_refl) body Hb).
      + rewrite guarded_old_gd in Hb.
        exact (nc_pt_gd w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.InputGD eq_refl) body Hb).
      + rewrite guarded_old_pkd in Hb.
        exact (nc_pt_pkd w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.InputPkD eq_refl) body Hb).
      + rewrite guarded_old_value in Hb.
        exact (nc_pt_value w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.InputValue eq_refl) body Hb).
      + rewrite guarded_old_rho in Hb.
        exact (nc_pt_rho w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.InputRho eq_refl) body Hb).
      + rewrite guarded_old_psi in Hb.
        exact (nc_pt_psi w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w RegionId.NoteCommit.InputPsi eq_refl) body Hb).
      + rewrite guarded_old_ycanon in Hb.
        exact (nc_pt_ygd w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w (RegionId.NoteCommit.YCanonicity
            RegionId.NoteCommit.YSubject.GD
            RegionId.NoteCommit.YCanonicity.Gate) eq_refl) body Hb).
      + rewrite guarded_old_ycanon in Hb.
        exact (nc_pt_ypkd w _ (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
          (hi_psi_old w)
          HRo (disp_old w (RegionId.NoteCommit.YCanonicity
            RegionId.NoteCommit.YSubject.PkD
            RegionId.NoteCommit.YCanonicity.Gate) eq_refl) body Hb).
      + rewrite guarded_new_b in Hb.
        exact (nc_pt_b w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.MessagePieceB eq_refl) body Hb).
      + rewrite guarded_new_d in Hb.
        exact (nc_pt_d w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.MessagePieceD eq_refl) body Hb).
      + rewrite guarded_new_e in Hb.
        exact (nc_pt_e w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.MessagePieceE eq_refl) body Hb).
      + rewrite guarded_new_g in Hb.
        exact (nc_pt_g w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.MessagePieceG eq_refl) body Hb).
      + rewrite guarded_new_h in Hb.
        exact (nc_pt_h w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.MessagePieceH eq_refl) body Hb).
      + rewrite guarded_new_gd in Hb.
        exact (nc_pt_gd w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.InputGD eq_refl) body Hb).
      + rewrite guarded_new_pkd in Hb.
        exact (nc_pt_pkd w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.InputPkD eq_refl) body Hb).
      + rewrite guarded_new_value in Hb.
        exact (nc_pt_value w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.InputValue eq_refl) body Hb).
      + rewrite guarded_new_rho in Hb.
        exact (nc_pt_rho w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.InputRho eq_refl) body Hb).
      + rewrite guarded_new_psi in Hb.
        exact (nc_pt_psi w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w RegionId.NoteCommit.InputPsi eq_refl) body Hb).
      + rewrite guarded_new_ycanon in Hb.
        exact (nc_pt_ygd w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w (RegionId.NoteCommit.YCanonicity
            RegionId.NoteCommit.YSubject.GD
            RegionId.NoteCommit.YCanonicity.Gate) eq_refl) body Hb).
      + rewrite guarded_new_ycanon in Hb.
        exact (nc_pt_ypkd w _ (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
          (OCT.t_nf_spec (OCT.tables_of w)) (hi_psi_new w)
          HRn (disp_new w (RegionId.NoteCommit.YCanonicity
            RegionId.NoteCommit.YSubject.PkD
            RegionId.NoteCommit.YCanonicity.Gate) eq_refl) body Hb).
  Qed.

End OrchardCanonicityForward.
