(** * Forward witness facts: the variable-base multiplication block

    The "var-base" group of the open witness-fact residue: the seven facts of
    the synthesis program whose two cell addresses meet at the address-
    integrity variable-base ladder ([[ivk] g_d_old], §4.18.4 'Diversified
    address integrity') or at the witnessed [pk_d_old] point.

    - the ladder's top running-sum cell is pinned to [0] (the scalar
      [ivk + t_q] fits in 255 bits);
    - the overflow block's first running-sum row is the reduced [s] itself;
    - the lo half's first step row starts at the hi half's final
      accumulator;
    - the ladder's output row carries [[ivk] g_d_old], the same point the
      [WitnessPkD] region witnesses;
    - the old note's [pk_d] input and y-canonicity rows read that same
      witnessed point.

    None of them is a reduction: the two sides are different derivations of
    one value — a guarded index into a [ladder_go] fold against a record
    projection, or the ladder record's output against the specification
    multiple [repr ([ivk] g_d_old)].

    The bridge for the last shape is [vb_out_mul]: the ladder record's output
    is the specification scalar multiple.  [forward/var_base_ladder.v] proves
    that the two incomplete halves land on the accumulator [macc alpha B 4 =
    repr ([2^251 + 2·z_4 + 1] B)]; the three complete rounds absorb bits
    [3, 2, 1] as [acc_i = acc_{i+1} ⊞ ([2k_i − 1] B ⊞ acc_{i+1}) =
    repr ([2^(255−i) + 2·z_i + 1] B)], and the LSB round subtracts the
    [(0,0)] sentinel or [B], landing on [repr ([2^254 + ivk + t_q] B)] =
    [repr ([ivk + q_P] B)] = [repr ([ivk] B)] by the group-order theorem
    [PallasOrder.pallas_mul_q_on_curve].

    Exports: [orchardwitnessvarbase_facts] (the fact literals) and
    [orchardwitnessvarbase_ok] (they hold at [honest_assignment w] for every
    valid, nondegenerate input). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.EllipticCurve.PallasOrder.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Garden.Orchard.circuit_completeness.forward.var_base_ladder.
Require Garden.Orchard.circuit.
Require Garden.Orchard.protocol_spec.
Require Import Garden.Field.Div.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardWitnessVarBase.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.
  Import OrchardVarBaseForward.

  Module OCT := OrchardCompletenessTables.
  Module VBT := OrchardVarBaseTables.

  Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** The hoisted derivation record and the spec folds stay stuck atoms: a
      reduction that unfolds them on symbolic input normalizes the ladder and
      Sinsemilla folds they carry (docs/compile-performance.md). *)
  #[local] Strategy opaque
    [OrchardCompletenessTables.tables_of
     BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  (** ** The scalar-multiple reading of a witnessed base point

      Every point the complete rounds combine is [repr ([n] B)] for an
      explicit integer [n]; [mrep] names that reading so the rounds compose
      as scalar addition. *)

  Definition mrep (B : Point.t) (n : Z) : Point.t :=
    PallasModel.repr (Pallas.mul n (PallasModel.unrepr B)).

  (** Peel a multiple equation to its scalar by unification only, so a
      [Pallas.mul] is never forced through conversion. *)
  Lemma mrep_scalar_eq (B : Point.t) (n m : Z) :
    n = m -> mrep B n = mrep B m.
  Proof. intros ->. reflexivity. Qed.

  Lemma mrep_add (B : Point.t) (HB : point_ok B) (i j : Z) :
    EccSpec.point_add (mrep B i) (mrep B j) = mrep B (i + j).
  Proof.
    destruct HB as (Hred & Hoc & _).
    unfold mrep.
    rewrite (VarBaseDefs.pallas_mul_add i j (PallasModel.unrepr B) Hred Hoc).
    change
      (Pallas.add (Pallas.mul i (PallasModel.unrepr B))
         (Pallas.mul j (PallasModel.unrepr B)))
      with
      (PallasModel.wadd (Pallas.mul i (PallasModel.unrepr B))
         (Pallas.mul j (PallasModel.unrepr B))).
    rewrite (PallasModel.repr_add _ _
      (VarBaseDefs.pallas_mul_reduced i _ Hred)
      (VarBaseDefs.pallas_mul_reduced j _ Hred)
      (VarBaseDefs.pallas_mul_on_curve i _ Hoc)
      (VarBaseDefs.pallas_mul_on_curve j _ Hoc)).
    reflexivity.
  Qed.

  (* The zero multiple is the [(0, 0)] sentinel; the delta steps are cheap,
     but [Pallas.mul] / [Weierstrass.mul] are opaque to conversion for the
     rest of the file, so the transparency is restored only here. *)
  Strategy transparent [Pallas.mul Weierstrass.mul].
  Lemma pallas_mul_zero (P : Pallas.point) : Pallas.mul 0 P = Pallas.identity.
  Proof. reflexivity. Qed.
  Strategy opaque [Pallas.mul Weierstrass.mul].

  (** The signed base of a bit: [[2k − 1] B]. *)
  Lemma mrep_signed (B : Point.t) (HB : point_ok B) (bit : Z)
      (Hbit : bit = 0 \/ bit = 1) :
    VBT.signed_pt B bit = mrep B (2 * bit - 1).
  Proof.
    pose proof (point_ok_affine B HB) as (Haff & _ & _).
    destruct HB as (Hred & _ & _).
    unfold VBT.signed_pt, mrep.
    destruct Hbit as [-> | ->].
    - replace (0 =? 1) with false by reflexivity.
      replace (2 * 0 - 1) with (- (1)) by lia.
      rewrite (VarBaseDefs.pallas_mul_neg 1 (PallasModel.unrepr B) Hred).
      rewrite VarBaseDefs.pallas_mul_one.
      rewrite Haff.
      reflexivity.
    - replace (1 =? 1) with true by reflexivity.
      replace (2 * 1 - 1) with 1 by lia.
      rewrite VarBaseDefs.pallas_mul_one.
      exact (eq_sym (PallasModel.repr_unrepr B)).
  Qed.

  (** The LSB round's point: the identity sentinel on bit 1, [−B] on bit 0. *)
  Lemma mrep_lsb (B : Point.t) (HB : point_ok B) (bit : Z)
      (Hbit : bit = 0 \/ bit = 1) :
    VBT.lsb_pt B bit = mrep B (bit - 1).
  Proof.
    pose proof (point_ok_affine B HB) as (Haff & _ & _).
    destruct HB as (Hred & _ & _).
    unfold VBT.lsb_pt, mrep.
    destruct Hbit as [-> | ->].
    - replace (0 =? 1) with false by reflexivity.
      replace (0 - 1) with (- (1)) by lia.
      rewrite (VarBaseDefs.pallas_mul_neg 1 (PallasModel.unrepr B) Hred).
      rewrite VarBaseDefs.pallas_mul_one.
      rewrite Haff.
      reflexivity.
    - replace (1 =? 1) with true by reflexivity.
      replace (1 - 1) with 0 by lia.
      rewrite pallas_mul_zero.
      reflexivity.
  Qed.

  (** ** The complete rounds and the LSB round

      [macc] is already the [mrep] reading of its multiple, so one round is
      one scalar identity. *)

  Lemma macc_mrep (alpha : Z) (B : Point.t) (i : nat) :
    macc alpha B i =
    mrep B (2 ^ (255 - Z.of_nat i) + 2 * (mk alpha / 2 ^ Z.of_nat i) + 1).
  Proof. reflexivity. Qed.

  Lemma macc_round (alpha : Z) (B : Point.t) (HB : point_ok B) (i : nat)
      (Hi : (1 <= i <= 254)%nat) :
    EccSpec.point_add (macc alpha B (S i))
      (EccSpec.point_add
        (VBT.signed_pt B (scalar_bit (mk alpha) i))
        (macc alpha B (S i))) =
    macc alpha B i.
  Proof.
    rewrite (mrep_signed B HB _ (scalar_bit_01 (mk alpha) i)).
    rewrite !macc_mrep.
    rewrite (mrep_add B HB), (mrep_add B HB).
    apply mrep_scalar_eq.
    pose proof (bit_running_sum_step (mk alpha) i) as Hstep.
    unfold bit_running_sum in Hstep.
    assert (Hpow :
      2 ^ (255 - Z.of_nat i) = 2 * 2 ^ (255 - Z.of_nat (S i))).
    { replace (255 - Z.of_nat i) with (1 + (255 - Z.of_nat (S i)))
        by (clear -Hi; lia).
      rewrite Z.pow_add_r by (clear -Hi; lia).
      reflexivity. }
    rewrite Hpow, Hstep.
    set (N := 2 ^ (255 - Z.of_nat (S i))) in *.
    set (Z1 := mk alpha / 2 ^ Z.of_nat (S i)) in *.
    set (b := scalar_bit (mk alpha) i) in *.
    clearbody N Z1 b.
    clear -N Z1 b.
    lia.
  Qed.

  Lemma macc_lsb (alpha : Z) (B : Point.t) (HB : point_ok B) :
    EccSpec.point_add (VBT.lsb_pt B (scalar_bit (mk alpha) 0))
      (macc alpha B 1) =
    mrep B (2 ^ 254 + mk alpha).
  Proof.
    rewrite (mrep_lsb B HB _ (scalar_bit_01 (mk alpha) 0)).
    rewrite macc_mrep.
    rewrite (mrep_add B HB).
    apply mrep_scalar_eq.
    pose proof (bit_running_sum_step (mk alpha) 0) as Hstep.
    unfold bit_running_sum in Hstep.
    change (Z.of_nat 0) with 0 in Hstep.
    change (Z.of_nat 1) with 1 in Hstep.
    rewrite Z.pow_0_r, Z.div_1_r in Hstep.
    change (Z.of_nat 1) with 1.
    change (255 - 1) with 254.
    set (b := scalar_bit (mk alpha) 0) in *.
    set (Z1 := mk alpha / 2 ^ 1) in *.
    set (K := mk alpha) in *.
    set (N := 2 ^ 254) in *.
    clearbody b Z1 K N.
    clear -Hstep.
    lia.
  Qed.

  (** ** The ladder record's output is the specification multiple *)

  Lemma vb_out_mul (alpha : Z) (B : Point.t)
      (HB : point_ok B) (Hlad : ladder_ok alpha B)
      (Hk : 0 <= mk alpha < 2 ^ 255) :
    VBT.vb_out (VBT.vb_columns alpha B) =
    PallasModel.repr (Pallas.mul alpha (PallasModel.unrepr B)).
  Proof.
    assert (E4 : VBT.vb_acc4 (VBT.vb_columns alpha B) = macc alpha B 4)
      by exact (proj1 (lo_chain alpha B HB Hlad Hk)).
    assert (E3 : VBT.vb_acc3 (VBT.vb_columns alpha B) = macc alpha B 3).
    { rewrite vb_acc3_e, vb_mid3_e, vb_p3_e, E4.
      exact (macc_round alpha B HB 3%nat ltac:(clear; lia)). }
    assert (E2 : VBT.vb_acc2 (VBT.vb_columns alpha B) = macc alpha B 2).
    { rewrite vb_acc2_e, vb_mid2_e, vb_p2_e, E3.
      exact (macc_round alpha B HB 2%nat ltac:(clear; lia)). }
    assert (E1 : VBT.vb_acc1 (VBT.vb_columns alpha B) = macc alpha B 1).
    { rewrite vb_acc1_e, vb_mid1_e, vb_p1_e, E2.
      exact (macc_round alpha B HB 1%nat ltac:(clear; lia)). }
    rewrite vb_out_e, vb_p0_e, E1.
    rewrite (macc_lsb alpha B HB).
    unfold mrep.
    replace (2 ^ 254 + mk alpha) with (alpha + Pallas.pallas_q)
      by (unfold mk, Pallas.pallas_q, Primes.pallas_q; clear; lia).
    destruct HB as (Hred & Hoc & _).
    rewrite (VarBaseDefs.pallas_mul_add alpha Pallas.pallas_q
      (PallasModel.unrepr B) Hred Hoc).
    rewrite (PallasOrder.pallas_mul_q_on_curve _ Hred Hoc).
    unfold Pallas.add, Pallas.identity.
    rewrite (Weierstrass.add_Infinity_r (p := Primes.pallas_p)
      Pallas.a Pallas.b).
    reflexivity.
  Qed.

  Lemma vb_out_result (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) :
    VBT.vb_out (OCT.t_vb (OCT.tables_of w)) =
    OCT.t_vb_result (OCT.tables_of w).
  Proof.
    rewrite t_vb_ivk, t_vb_result_ivk.
    exact (vb_out_mul (ivk w) (hi_g_d_old w)
      (gd_point_ok w Hv) (ladder_ok_of_nondegenerate w Hnd)
      (mk_ivk_range w)).
  Qed.

  (** The first emitted lo-half step row starts at the hi-half boundary
      accumulator: [ladder_step] stores the accumulator's abscissa. *)
  Lemma vstep_xa (alpha : Z) (B : Point.t) (m : nat) :
    VBT.sr_xa (vstep alpha B m) = Point.x (macc alpha B (S m)).
  Proof. reflexivity. Qed.

  (** ** Cell readings

      Each is a definitional reading of the advice dispatch at one address,
      with the hoisted record held opaque so no spec fold is normalized. *)

  Lemma read_vb_a9_1 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase)) 1 =
    VBT.vb_scalar (OCT.t_vb (OCT.tables_of w)) / 2 ^ 255.
  Proof. reflexivity. Qed.

  Lemma read_vb_a7_2 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A7
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase)) 2 =
    VBT.sr_xa (VBT.lo_at (OCT.t_vb (OCT.tables_of w)) 2).
  Proof. reflexivity. Qed.

  Lemma read_vb_a3_127 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase)) 127 =
    Point.x (VBT.vb_acc130 (OCT.t_vb (OCT.tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_ovl_a9_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A9
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowLookup)) 0 =
    VBT.vb_s (OCT.t_vb (OCT.tables_of w)) / 1.
  Proof. reflexivity. Qed.

  Lemma read_ovs_a6_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowS)) 0 =
    VBT.vb_s (OCT.t_vb (OCT.tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_vb_a2_136 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A2
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase)) 136 =
    Point.x (VBT.vb_out (OCT.t_vb (OCT.tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_vb_a3_136 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A3
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.VariableBase)) 136 =
    Point.y (VBT.vb_out (OCT.t_vb (OCT.tables_of w))).
  Proof. reflexivity. Qed.

  Lemma read_wpkd_a0_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A0
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD) 0 =
    Point.x (OCT.t_vb_result (OCT.tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_wpkd_a1_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A1
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD) 0 =
    Point.y (OCT.t_vb_result (OCT.tables_of w)).
  Proof. reflexivity. Qed.

  Lemma read_ypkd_a5_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A5
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.Gate)) 0 =
    Point.y (hi_pk_d_old w).
  Proof. reflexivity. Qed.

  Lemma read_inpkd_a6_0 (w : HonestInput) :
    (Γw w).(Assignment.advice) Advice.A6
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.InputPkD) 0 =
    Point.x (hi_pk_d_old w).
  Proof. reflexivity. Qed.

  (** The witnessed [pk_d_old] is the ladder's result ([valid]'s
      'Diversified address integrity' conjunct). *)
  Lemma pkd_result (w : HonestInput) (Hv : valid w) :
    hi_pk_d_old w = OCT.t_vb_result (OCT.tables_of w).
  Proof.
    destruct Hv as (_ & _ & _ & Hpk).
    rewrite t_vb_result_ivk.
    exact Hpk.
  Qed.

  (** ** The group *)

  Definition orchardwitnessvarbase_facts
      : list (Fact.t columns RegionId.t) := [
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |} 0;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 127 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowLookup); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowS); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 136 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 136 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD; Cell.row_offset := 0 |}].

  (** The head of a witness-fact goal: the two cell addresses, with the
      advice dispatch left folded. *)
  Ltac vb_head :=
    cbn [interpret_fact eval_cell Cell.column Cell.region Cell.row_offset].

  Lemma orchardwitnessvarbase_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w)
    : interpret_facts (OrchardHonestAssignment.honest_assignment w)
        orchardwitnessvarbase_facts.
  Proof.
    pose proof (gd_point_ok w Hv) as HB.
    pose proof (ladder_ok_of_nondegenerate w Hnd) as Hlad.
    unfold orchardwitnessvarbase_facts.
    cbn [interpret_facts].
    repeat apply conj.
    - (* A9 @ VariableBase row 1 is 0: the scalar fits in 255 bits. *)
      vb_head.
      rewrite read_vb_a9_1, t_vb_ivk, vb_scalar_e.
      apply Z.div_small.
      exact (mk_ivk_range w).
    - (* the lo half's first step row starts at the hi half's boundary *)
      vb_head.
      rewrite read_vb_a7_2, read_vb_a3_127.
      assert (Hm : (4 <= 129 <= 129)%nat) by (clear; lia).
      assert (Hr : 2 = 131 - Z.of_nat 129) by reflexivity.
      rewrite (lo_row w 129%nat 2 HB Hlad Hm Hr).
      rewrite (acc130_eq w HB Hlad).
      apply vstep_xa.
    - (* the overflow lookup's row 0 is the reduced [s] itself *)
      vb_head.
      rewrite read_ovl_a9_0, read_ovs_a6_0.
      apply Z.div_1_r.
    - (* the ladder output's abscissa is the witnessed [pk_d_old]'s *)
      vb_head.
      rewrite read_vb_a2_136, read_wpkd_a0_0.
      rewrite (vb_out_result w Hv Hnd).
      reflexivity.
    - (* the ladder output's ordinate is the witnessed [pk_d_old]'s *)
      vb_head.
      rewrite read_vb_a3_136, read_wpkd_a1_0.
      rewrite (vb_out_result w Hv Hnd).
      reflexivity.
    - (* the old note's y-canonicity subject is that same point *)
      vb_head.
      rewrite read_ypkd_a5_0, read_wpkd_a1_0.
      rewrite (pkd_result w Hv).
      reflexivity.
    - (* the old note's [pk_d] input abscissa is that same point's *)
      vb_head.
      rewrite read_inpkd_a6_0, read_wpkd_a0_0.
      rewrite (pkd_result w Hv).
      reflexivity.
    - exact I.
  Qed.
End OrchardWitnessVarBase.
