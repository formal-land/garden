(** * NoteCommit message-piece and canonicity soundness

    The per-gate soundness family for the NoteCommit decomposition gates: each
    of [message_piece_{b,d,e,g,h}_gate], [input_{g_d,pk_d,value,rho,psi}_gate]
    and [y_coordinate_checks_gate] forces the corresponding
    [note_commit_proof.v] reconstruction [output] on the gate's cells, plus
    the boolean and canonicity ("MSB = 1 => ...") side facts the gate carries.

    On top of the gate layer, the pure-[Z] canonicity core: with the range
    facts (the RangeB0..RangeH0 short lookups, the running-sum lookups behind
    [z13_*], and the [+ 2^k - t_P] prime checks) every 255-bit input packing
    is below the Pallas modulus, so each field-level decomposition equation is
    an exact integer identity — the decomposition of each input is unique.
    The [+ 2^k - t_P] terms are load-bearing: without them one field element
    below [2^255 - p] would admit two digit strings.

    The capstone is the word-schedule theorem: the eight hashed pieces
    [a..h], read as their 10-bit Sinsemilla word lists, are exactly the
    little-endian word decomposition of

      [x(g_d) + ỹ(g_d)·2^255 + x(pk_d)·2^256 + ỹ(pk_d)·2^511 + v·2^512
        + rho·2^576 + psi·2^831]

    packed into 109 words — the note-commit message of the inputs.  (The
    [ỹ] bits are the [b_2]/[d_1] cells the y-canonicity checks pin to the
    parity of the reduced y-coordinates.) *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.note_commit_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NC := Garden.Orchard.circuit.note_commit.
Module NCP := Garden.Orchard.circuit.note_commit_proof.

Module NoteCommitMessagePieces.
  (** * Small helpers *)

  Lemma isbool_cases (x : Z) (Hx : IsBool.t x) : x = 0 \/ x = 1.
  Proof.
    cbv [IsBool.t IsBool.ZIsBool] in Hx.
    destruct (Z.odd x); cbn [Z.b2z] in Hx; [right | left]; exact Hx.
  Qed.

  Lemma t_p_range :
    2 ^ 125 < Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p < 2 ^ 126.
  Proof. split; vm_compute; reflexivity. Qed.

  Lemma pallas_p_eq :
    Primes.pallas_p =
      2 ^ 254 + Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p.
  Proof. reflexivity. Qed.

  (** A boolean cell copied into a message word is that word's parity: the
      strictly higher digits contribute only even amounts. *)
  Lemma lsb_parity (y lsb rest : Z)
      (Hlsb : lsb = 0 \/ lsb = 1)
      (Hy : y = lsb + 2 * rest) :
    lsb = y mod 2.
  Proof.
    subst y.
    replace (lsb + 2 * rest) with (lsb + rest * 2) by ring.
    rewrite Z_mod_plus_full.
    destruct Hlsb; subst; reflexivity.
  Qed.

  (** * Gate-level soundness

      Each lemma reads one decomposition gate at an active row and returns
      the [note_commit_proof.v] reconstruction equations on the gate's cells,
      together with the boolean and conditional canonicity facts. *)

  Lemma message_piece_b_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_b : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_b ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.message_piece_b_gate q_b ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) /\
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row)) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.MessagePieceB.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row))
      ).(NCP.MessagePieceB.b).
  Proof.
    unfold NCP.MessagePieceB.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hb1 & Hb2 & Hdec).
    specialize (Hb1 Hselector).
    specialize (Hb2 Hselector).
    specialize (Hdec Hselector).
    repeat split; assumption.
  Qed.

  Lemma message_piece_d_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_d : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_d ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.message_piece_d_gate q_d ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)) /\
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.MessagePieceD.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row))
      ).(NCP.MessagePieceD.d).
  Proof.
    unfold NCP.MessagePieceD.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hd0 & Hd1 & Hdec).
    specialize (Hd0 Hselector).
    specialize (Hd1 Hselector).
    specialize (Hdec Hselector).
    repeat split; assumption.
  Qed.

  Lemma message_piece_e_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_e : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_e ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.message_piece_e_gate q_e ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.MessagePieceE.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
      ).(NCP.MessagePieceE.e).
  Proof.
    unfold NCP.MessagePieceE.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    exact (Hgate Hselector).
  Qed.

  Lemma message_piece_g_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_g : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_g ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.message_piece_g_gate q_g ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.MessagePieceG.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.MessagePieceG.g).
  Proof.
    unfold NCP.MessagePieceG.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hg0 & Hdec).
    specialize (Hg0 Hselector).
    specialize (Hdec Hselector).
    repeat split; assumption.
  Qed.

  Lemma message_piece_h_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_h : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_h ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.message_piece_h_gate q_h ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.MessagePieceH.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
      ).(NCP.MessagePieceH.h).
  Proof.
    unfold NCP.MessagePieceH.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hh1 & Hdec).
    specialize (Hh1 Hselector).
    specialize (Hdec Hselector).
    repeat split; assumption.
  Qed.

  Lemma input_g_d_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_gd : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_gd ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.input_g_d_gate q_gd ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.InputGD.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputGD.gd_x) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row) =
      (NCP.InputGD.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputGD.a_prime) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row) = 0).
  Proof.
    unfold NCP.InputGD.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hdec & Hprime & He1 & He2 & He3).
    specialize (Hdec Hselector).
    specialize (Hprime Hselector).
    specialize (He1 Hselector).
    specialize (He2 Hselector).
    specialize (He3 Hselector).
    repeat split; try assumption; symmetry; assumption.
  Qed.

  Lemma input_pk_d_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_pkd : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_pkd ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.input_pk_d_gate q_pkd ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.InputPKD.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputPKD.pkd_x) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row) =
      (NCP.InputPKD.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputPKD.b3_c_prime) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row) = 0).
  Proof.
    unfold NCP.InputPKD.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hdec & Hprime & He1 & He2).
    specialize (Hdec Hselector).
    specialize (Hprime Hselector).
    specialize (He1 Hselector).
    specialize (He2 Hselector).
    repeat split; try assumption; symmetry; assumption.
  Qed.

  Lemma input_value_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_value : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_value ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.input_value_gate q_value ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.InputValue.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row))
      ).(NCP.InputValue.value).
  Proof.
    unfold NCP.InputValue.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    symmetry.
    exact (Hgate Hselector).
  Qed.

  Lemma input_rho_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_rho : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_rho ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.input_rho_gate q_rho ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.InputRho.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputRho.rho) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row) =
      (NCP.InputRho.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputRho.e1_f_prime) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row) = 0).
  Proof.
    unfold NCP.InputRho.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hdec & Hprime & He1 & He2).
    specialize (Hdec Hselector).
    specialize (Hprime Hselector).
    specialize (He1 Hselector).
    specialize (He2 Hselector).
    repeat split; try assumption; symmetry; assumption.
  Qed.

  Lemma input_psi_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_psi : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_psi ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.input_psi_gate q_psi ⟧ (region, row)) :
    Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
      (NCP.InputPsi.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputPsi.psi) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row) =
      (NCP.InputPsi.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row))
      ).(NCP.InputPsi.g1_g2_prime) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row) = 0).
  Proof.
    unfold NCP.InputPsi.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hdec & Hprime & He1 & He2 & He3).
    specialize (Hdec Hselector).
    specialize (Hprime Hselector).
    specialize (He1 Hselector).
    specialize (He2 Hselector).
    specialize (He3 Hselector).
    repeat split; try assumption; symmetry; assumption.
  Qed.

  Lemma y_coordinate_checks_sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q_y_canon : Selector.t) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ q_y_canon ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ NC.y_coordinate_checks_gate q_y_canon ⟧ (region, row)) :
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row)) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.next ⟧ (region, row) =
      (NCP.YCoordinateChecks.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row))
      ).(NCP.YCoordinateChecks.j) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row) =
      (NCP.YCoordinateChecks.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row))
      ).(NCP.YCoordinateChecks.y) /\
    Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row) =
      (NCP.YCoordinateChecks.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row))
      ).(NCP.YCoordinateChecks.j_prime) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row) = 0) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row) = 0 \/
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row) = 0).
  Proof.
    unfold NCP.YCoordinateChecks.output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (Hk3 & Hj & Hy & Hjprime & He1 & He2 & He3).
    specialize (Hk3 Hselector).
    specialize (Hj Hselector).
    specialize (Hy Hselector).
    specialize (Hjprime Hselector).
    specialize (He1 Hselector).
    specialize (He2 Hselector).
    specialize (He3 Hselector).
    split; [exact Hk3 |].
    split; [exact Hj |].
    split; [rewrite <- Hj; exact Hy |].
    split; [rewrite <- Hj; symmetry; exact Hjprime |].
    repeat split; assumption.
  Qed.

  (** * Canonicity core (pure [Z])

      The field-level decomposition equations become exact integer identities
      once the packed value is known to lie below the Pallas modulus.  The
      [+ 2^k - t_P] prime checks supply exactly that: when the top bit is
      set, the low bits are below [t_P], so [low + 2^254 < 2^254 + t_P = p]. *)

  (** One reduction step: a nonnegative summand plus a shifted bounded digit
      stays below [p], so the field sum is the integer sum. *)
  Lemma addF_mulF_exact (s x c : Z)
      (Hs : 0 <= s)
      (Hx : 0 <= x)
      (Hc : 0 <= c < Primes.pallas_p)
      (Htotal : s + x * c < Primes.pallas_p) :
    s +F x *F UnOp.from c = s + x * c.
  Proof.
    unfold BinOp.add, BinOp.mul, UnOp.from.
    rewrite (Z.mod_small c) by lia.
    rewrite (Z.mod_small (x * c)) by nia.
    apply Z.mod_small.
    nia.
  Qed.

  Lemma addF_from_exact (s c : Z)
      (Hs : 0 <= s)
      (Hc : 0 <= c < Primes.pallas_p)
      (Htotal : s + c < Primes.pallas_p) :
    s +F UnOp.from c = s + c.
  Proof.
    unfold BinOp.add, UnOp.from.
    rewrite (Z.mod_small c) by lia.
    apply Z.mod_small.
    lia.
  Qed.

  (** The prime check [low' = low + 2^k - t_P] with both sides ranged to [k]
      bits pins [low < t_P] — the load-bearing canonicity fact — and is
      itself an exact integer identity. *)
  Lemma prime_check_exact (k low low_prime : Z)
      (Hk : 126 <= k <= 140)
      (Hlow : 0 <= low < 2 ^ k)
      (Hfield :
        low_prime =
          low +F UnOp.from (2 ^ k) -F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
      (Hrange : 0 <= low_prime < 2 ^ k) :
    low < Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p /\
    low_prime =
      low + 2 ^ k - Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p.
  Proof.
    pose proof t_p_range as Htp.
    assert (H126 : 2 ^ 126 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
    assert (H140 : 2 ^ k <= 2 ^ 140) by (apply Z.pow_le_mono_r; lia).
    assert (Hp : 2 ^ 141 < Primes.pallas_p) by (vm_compute; reflexivity).
    rewrite (addF_from_exact low (2 ^ k)) in Hfield by lia.
    unfold BinOp.sub, UnOp.from in Hfield.
    rewrite (Z.mod_small
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p) in Hfield by lia.
    rewrite (Z.mod_small (low + 2 ^ k -
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)) in Hfield by lia.
    lia.
  Qed.

  (** [x(g_d)]-shaped decomposition ([a] 250 bits, [b_0] 4 bits, [b_1] one
      bit; also the [y]-canonicity shape with [j]/[k_2]/[k_3]): the field
      packing is the exact integer packing.  The [b_1 = 1] canonicity leg
      consumes the ranges the [z13] running sums and the prime check pin. *)
  Lemma decomposition_250_4_1
      (xv a b0 b1 a_prime : Z)
      (Hxv : xv = a +F b0 *F UnOp.from (2 ^ 250) +F b1 *F UnOp.from (2 ^ 254))
      (Haprime :
        a_prime =
          a +F UnOp.from (2 ^ 130) -F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
      (Ha : 0 <= a < 2 ^ 250)
      (Hb0 : 0 <= b0 < 2 ^ 4)
      (Hb1 : b1 = 0 \/ b1 = 1)
      (Hb1_b0 : b1 = 0 \/ b0 = 0)
      (Ha130 : b1 = 1 -> a < 2 ^ 130)
      (Haprime_range : b1 = 1 -> 0 <= a_prime < 2 ^ 130) :
    xv = a + b0 * 2 ^ 250 + b1 * 2 ^ 254 /\
    0 <= a + b0 * 2 ^ 250 + b1 * 2 ^ 254 < Primes.pallas_p.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    destruct Hb1 as [Hb1z | Hb1one].
    - subst b1 xv.
      rewrite (addF_mulF_exact a b0 (2 ^ 250)) by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (addF_mulF_exact (a + b0 * 2 ^ 250) 0 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
    - assert (Hb0z : b0 = 0) by lia.
      specialize (Ha130 Hb1one).
      specialize (Haprime_range Hb1one).
      destruct (prime_check_exact 130 a a_prime
        ltac:(lia) ltac:(lia) Haprime Haprime_range) as [Hatp _].
      subst b0 b1 xv.
      rewrite (addF_mulF_exact a 0 (2 ^ 250))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (addF_mulF_exact (a + 0 * 2 ^ 250) 1 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
  Qed.

  (** [x(pk_d)]/[rho]-shaped decomposition ([lo] 4 bits, [mid] 250 bits at
      shift 4, top bit at 254; prime check on the 140-bit low part). *)
  Lemma decomposition_4_250_1
      (xv lo mid top prime : Z)
      (Hxv : xv = lo +F mid *F UnOp.from (2 ^ 4) +F top *F UnOp.from (2 ^ 254))
      (Hprime :
        prime =
          lo +F mid *F UnOp.from (2 ^ 4) +F UnOp.from (2 ^ 140) -F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
      (Hlo : 0 <= lo < 2 ^ 4)
      (Hmid : 0 <= mid < 2 ^ 250)
      (Htop : top = 0 \/ top = 1)
      (Hmid130 : top = 1 -> mid < 2 ^ 130)
      (Hprime_range : top = 1 -> 0 <= prime < 2 ^ 140) :
    xv = lo + mid * 2 ^ 4 + top * 2 ^ 254 /\
    0 <= lo + mid * 2 ^ 4 + top * 2 ^ 254 < Primes.pallas_p.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    assert (Hinner : lo +F mid *F UnOp.from (2 ^ 4) = lo + mid * 2 ^ 4)
      by (apply addF_mulF_exact;
        cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite Hinner in Hxv, Hprime.
    destruct Htop as [Htopz | Htopone].
    - subst top xv.
      rewrite (addF_mulF_exact (lo + mid * 2 ^ 4) 0 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
    - specialize (Hmid130 Htopone).
      specialize (Hprime_range Htopone).
      destruct (prime_check_exact 140 (lo + mid * 2 ^ 4) prime
        ltac:(lia) ltac:(lia) Hprime Hprime_range) as [Hlowtp _].
      subst top xv.
      rewrite (addF_mulF_exact (lo + mid * 2 ^ 4) 1 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
  Qed.

  (** [psi]-shaped decomposition ([g_1] 9 bits, [g_2] 240 bits at shift 9,
      [h_0] 5 bits at shift 249, top bit at 254; prime check on the 130-bit
      low part). *)
  Lemma decomposition_9_240_5_1
      (xv g1 g2 h0 h1 prime : Z)
      (Hxv :
        xv =
          g1 +F g2 *F UnOp.from (2 ^ 9) +F h0 *F UnOp.from (2 ^ 249) +F
            h1 *F UnOp.from (2 ^ 254))
      (Hprime :
        prime =
          g1 +F g2 *F UnOp.from (2 ^ 9) +F UnOp.from (2 ^ 130) -F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
      (Hg1 : 0 <= g1 < 2 ^ 9)
      (Hg2 : 0 <= g2 < 2 ^ 240)
      (Hh0 : 0 <= h0 < 2 ^ 5)
      (Hh1 : h1 = 0 \/ h1 = 1)
      (Hh1_h0 : h1 = 0 \/ h0 = 0)
      (Hlow130 : h1 = 1 -> g1 + g2 * 2 ^ 9 < 2 ^ 130)
      (Hprime_range : h1 = 1 -> 0 <= prime < 2 ^ 130) :
    xv = g1 + g2 * 2 ^ 9 + h0 * 2 ^ 249 + h1 * 2 ^ 254 /\
    0 <= g1 + g2 * 2 ^ 9 + h0 * 2 ^ 249 + h1 * 2 ^ 254 < Primes.pallas_p.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    assert (Hinner : g1 +F g2 *F UnOp.from (2 ^ 9) = g1 + g2 * 2 ^ 9)
      by (apply addF_mulF_exact;
        cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite Hinner in Hxv, Hprime.
    destruct Hh1 as [Hh1z | Hh1one].
    - subst h1 xv.
      rewrite (addF_mulF_exact (g1 + g2 * 2 ^ 9) h0 (2 ^ 249))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (addF_mulF_exact (g1 + g2 * 2 ^ 9 + h0 * 2 ^ 249) 0 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
    - assert (Hh0z : h0 = 0) by lia.
      specialize (Hlow130 Hh1one).
      specialize (Hprime_range Hh1one).
      destruct (prime_check_exact 130 (g1 + g2 * 2 ^ 9) prime
        ltac:(lia) ltac:(lia) Hprime Hprime_range) as [Hlowtp _].
      subst h0 h1 xv.
      rewrite (addF_mulF_exact (g1 + g2 * 2 ^ 9) 0 (2 ^ 249))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      rewrite (addF_mulF_exact (g1 + g2 * 2 ^ 9 + 0 * 2 ^ 249) 1 (2 ^ 254))
        by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
      lia.
  Qed.

  (** [value]-shaped decomposition: 64 bits total, no canonicity needed. *)
  Lemma decomposition_value
      (xv d2 z1d e0 : Z)
      (Hxv : xv = d2 +F z1d *F UnOp.from (2 ^ 8) +F e0 *F UnOp.from (2 ^ 58))
      (Hd2 : 0 <= d2 < 2 ^ 8)
      (Hz1d : 0 <= z1d < 2 ^ 50)
      (He0 : 0 <= e0 < 2 ^ 6) :
    xv = d2 + z1d * 2 ^ 8 + e0 * 2 ^ 58 /\
    0 <= d2 + z1d * 2 ^ 8 + e0 * 2 ^ 58 < 2 ^ 64.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst xv.
    rewrite (addF_mulF_exact d2 z1d (2 ^ 8))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (d2 + z1d * 2 ^ 8) e0 (2 ^ 58))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  (** * Piece-level exactness

      The short message pieces are far below the modulus, so the piece gates'
      field decompositions are integer identities outright, with the piece
      bounds that the word schedule consumes. *)

  Lemma piece_b_exact (bv b0 b1 b2 b3 : Z)
      (Hbv :
        bv =
          b0 +F b1 *F UnOp.from (2 ^ 4) +F b2 *F UnOp.from (2 ^ 5) +F
            b3 *F UnOp.from (2 ^ 6))
      (Hb0 : 0 <= b0 < 2 ^ 4)
      (Hb1 : b1 = 0 \/ b1 = 1)
      (Hb2 : b2 = 0 \/ b2 = 1)
      (Hb3 : 0 <= b3 < 2 ^ 4) :
    bv = b0 + b1 * 2 ^ 4 + b2 * 2 ^ 5 + b3 * 2 ^ 6 /\ 0 <= bv < 2 ^ 10.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst bv.
    rewrite (addF_mulF_exact b0 b1 (2 ^ 4))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (b0 + b1 * 2 ^ 4) b2 (2 ^ 5))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (b0 + b1 * 2 ^ 4 + b2 * 2 ^ 5) b3 (2 ^ 6))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  Lemma piece_d_exact (dv d0 d1 d2 d3 : Z)
      (Hdv :
        dv =
          d0 +F d1 *F UnOp.from 2 +F d2 *F UnOp.from (2 ^ 2) +F
            d3 *F UnOp.from (2 ^ 10))
      (Hd0 : d0 = 0 \/ d0 = 1)
      (Hd1 : d1 = 0 \/ d1 = 1)
      (Hd2 : 0 <= d2 < 2 ^ 8)
      (Hd3 : 0 <= d3 < 2 ^ 50) :
    dv = d0 + d1 * 2 + d2 * 2 ^ 2 + d3 * 2 ^ 10 /\ 0 <= dv < 2 ^ 60.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst dv.
    rewrite (addF_mulF_exact d0 d1 2)
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (d0 + d1 * 2) d2 (2 ^ 2))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (d0 + d1 * 2 + d2 * 2 ^ 2) d3 (2 ^ 10))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  Lemma piece_e_exact (ev e0 e1 : Z)
      (Hev : ev = e0 +F e1 *F UnOp.from (2 ^ 6))
      (He0 : 0 <= e0 < 2 ^ 6)
      (He1 : 0 <= e1 < 2 ^ 4) :
    ev = e0 + e1 * 2 ^ 6 /\ 0 <= ev < 2 ^ 10.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst ev.
    rewrite (addF_mulF_exact e0 e1 (2 ^ 6))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  Lemma piece_g_exact (gv g0 g1 g2 : Z)
      (Hgv : gv = g0 +F g1 *F UnOp.from 2 +F g2 *F UnOp.from (2 ^ 10))
      (Hg0 : g0 = 0 \/ g0 = 1)
      (Hg1 : 0 <= g1 < 2 ^ 9)
      (Hg2 : 0 <= g2 < 2 ^ 240) :
    gv = g0 + g1 * 2 + g2 * 2 ^ 10 /\ 0 <= gv < 2 ^ 250.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst gv.
    rewrite (addF_mulF_exact g0 g1 2)
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    rewrite (addF_mulF_exact (g0 + g1 * 2) g2 (2 ^ 10))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  Lemma piece_h_exact (hv h0 h1 : Z)
      (Hhv : hv = h0 +F h1 *F UnOp.from (2 ^ 5))
      (Hh0 : 0 <= h0 < 2 ^ 5)
      (Hh1 : h1 = 0 \/ h1 = 1) :
    hv = h0 + h1 * 2 ^ 5 /\ 0 <= hv < 2 ^ 10.
  Proof.
    pose proof t_p_range as Htp.
    pose proof pallas_p_eq as Hpeq.
    subst hv.
    rewrite (addF_mulF_exact h0 h1 (2 ^ 5))
      by (cbv delta [Primes.pallas_p Primes.t_p] in *; lia).
    lia.
  Qed.

  (** The [j] word of a y-canonicity check ([lsb] one bit, [k_0] 9 bits,
      [z1_j] 240 bits at shift 10). *)
  Lemma piece_j_exact (jv lsb k0 z1j : Z)
      (Hjv : jv = lsb +F k0 *F UnOp.from 2 +F z1j *F UnOp.from (2 ^ 10))
      (Hlsb : lsb = 0 \/ lsb = 1)
      (Hk0 : 0 <= k0 < 2 ^ 9)
      (Hz1j : 0 <= z1j < 2 ^ 240) :
    jv = lsb + k0 * 2 + z1j * 2 ^ 10 /\ 0 <= jv < 2 ^ 250.
  Proof.
    exact (piece_g_exact jv lsb k0 z1j Hjv Hlsb Hk0 Hz1j).
  Qed.

  (** * Running-sum word algebra

      Helpers over [SinsemillaHash.digit_sum] for the [z13]-style bounds: a
      vanishing running-sum tail bounds the piece by the bits of the retained
      prefix. *)

  Lemma digit_sum_zero_tail_bound (xs ys : list Z)
      (Hxs : List.Forall (fun w => 0 <= w < 2 ^ 10) xs)
      (Hys : SinsemillaHash.digit_sum ys = 0) :
    0 <= SinsemillaHash.digit_sum (xs ++ ys) <
      2 ^ (10 * Z.of_nat (List.length xs)).
  Proof.
    rewrite SinsemillaHash.digit_sum_app, Hys.
    pose proof (SinsemillaHash.digit_sum_bound xs Hxs).
    lia.
  Qed.

  (** * Word schedule: the hashed pieces are the message words

      The circuit hashes the eight pieces [a..h] as 25, 1, 25, 6, 1, 25, 25
      and 1 ten-bit words (1090 bits, [psi]'s top word zero-padded).  Their
      concatenated word lists are the 109-word little-endian decomposition of
      the packed note-commitment message. *)

  Definition note_commit_packed
      (gd_x gd_y_lsb pkd_x pkd_y_lsb v rho psi : Z) : Z :=
    gd_x + gd_y_lsb * 2 ^ 255 + pkd_x * 2 ^ 256 + pkd_y_lsb * 2 ^ 511 +
      v * 2 ^ 512 + rho * 2 ^ 576 + psi * 2 ^ 831.

  (** The packed message regrouped along the piece boundaries. *)
  Lemma note_commit_packed_pieces
      (a b c d e f g h
        b0 b1 b2 b3 d0 d1 d2 d3 e0 e1 g0 g1 g2 h0 h1
        gd_x pkd_x v rho psi : Z)
      (Hb : b = b0 + b1 * 2 ^ 4 + b2 * 2 ^ 5 + b3 * 2 ^ 6)
      (Hd : d = d0 + d1 * 2 + d2 * 2 ^ 2 + d3 * 2 ^ 10)
      (He : e = e0 + e1 * 2 ^ 6)
      (Hg : g = g0 + g1 * 2 + g2 * 2 ^ 10)
      (Hh : h = h0 + h1 * 2 ^ 5)
      (Hgd : gd_x = a + b0 * 2 ^ 250 + b1 * 2 ^ 254)
      (Hpkd : pkd_x = b3 + c * 2 ^ 4 + d0 * 2 ^ 254)
      (Hv : v = d2 + d3 * 2 ^ 8 + e0 * 2 ^ 58)
      (Hrho : rho = e1 + f * 2 ^ 4 + g0 * 2 ^ 254)
      (Hpsi : psi = g1 + g2 * 2 ^ 9 + h0 * 2 ^ 249 + h1 * 2 ^ 254) :
    note_commit_packed gd_x b2 pkd_x d1 v rho psi =
      a + b * 2 ^ 250 + c * 2 ^ 260 + d * 2 ^ 510 + e * 2 ^ 570 +
        f * 2 ^ 580 + g * 2 ^ 830 + h * 2 ^ 1080.
  Proof.
    subst.
    unfold note_commit_packed.
    ring.
  Qed.

  Lemma words_le_split (m n : nat) (sh x y z : Z)
      (Hsh : sh = 2 ^ (10 * Z.of_nat m))
      (Hz : z = x + y * sh)
      (Hx : 0 <= x < sh)
      (Hy : 0 <= y) :
    SinsemillaSpec.words_le (m + n) z =
      SinsemillaSpec.words_le m x ++ SinsemillaSpec.words_le n y.
  Proof.
    subst sh z.
    apply SinsemillaHash.words_le_app; assumption.
  Qed.

  Lemma note_commit_words_schedule
      (a b c d e f g h : Z)
      (Ha : 0 <= a < 2 ^ 250)
      (Hb : 0 <= b < 2 ^ 10)
      (Hc : 0 <= c < 2 ^ 250)
      (Hd : 0 <= d < 2 ^ 60)
      (He : 0 <= e < 2 ^ 10)
      (Hf : 0 <= f < 2 ^ 250)
      (Hg : 0 <= g < 2 ^ 250)
      (Hh : 0 <= h < 2 ^ 10) :
    SinsemillaSpec.words_le 109
      (a + b * 2 ^ 250 + c * 2 ^ 260 + d * 2 ^ 510 + e * 2 ^ 570 +
        f * 2 ^ 580 + g * 2 ^ 830 + h * 2 ^ 1080) =
      SinsemillaSpec.words_le 25 a ++ SinsemillaSpec.words_le 1 b ++
      SinsemillaSpec.words_le 25 c ++ SinsemillaSpec.words_le 6 d ++
      SinsemillaSpec.words_le 1 e ++ SinsemillaSpec.words_le 25 f ++
      SinsemillaSpec.words_le 25 g ++ SinsemillaSpec.words_le 1 h.
  Proof.
    etransitivity.
    { apply (words_le_split 25 84 (2 ^ 250) a
        (b + c * 2 ^ 10 + d * 2 ^ 260 + e * 2 ^ 320 + f * 2 ^ 330 +
          g * 2 ^ 580 + h * 2 ^ 830));
        [reflexivity | ring | exact Ha | lia]. }
    apply f_equal.
    etransitivity.
    { apply (words_le_split 1 83 (2 ^ 10) b
        (c + d * 2 ^ 250 + e * 2 ^ 310 + f * 2 ^ 320 + g * 2 ^ 570 +
          h * 2 ^ 820));
        [reflexivity | ring | exact Hb | lia]. }
    apply f_equal.
    etransitivity.
    { apply (words_le_split 25 58 (2 ^ 250) c
        (d + e * 2 ^ 60 + f * 2 ^ 70 + g * 2 ^ 320 + h * 2 ^ 570));
        [reflexivity | ring | exact Hc | lia]. }
    apply f_equal.
    etransitivity.
    { apply (words_le_split 6 52 (2 ^ 60) d
        (e + f * 2 ^ 10 + g * 2 ^ 260 + h * 2 ^ 510));
        [reflexivity | ring | exact Hd | lia]. }
    apply f_equal.
    etransitivity.
    { apply (words_le_split 1 51 (2 ^ 10) e
        (f + g * 2 ^ 250 + h * 2 ^ 500));
        [reflexivity | ring | exact He | lia]. }
    apply f_equal.
    etransitivity.
    { apply (words_le_split 25 26 (2 ^ 250) f (g + h * 2 ^ 250));
        [reflexivity | ring | exact Hf | lia]. }
    apply f_equal.
    apply (words_le_split 25 1 (2 ^ 250) g h);
      [reflexivity | ring | exact Hg | lia].
  Qed.

  (** The capstone at the integer level: given the (already exact) piece and
      input decompositions with their range facts, the concatenated word
      lists of the hashed pieces are the 109-word decomposition of the packed
      note-commitment message of [g_d], [pk_d], [v], [rho], [psi] — with the
      [b_2]/[d_1] cells as the compressed-point sign bits. *)
  Theorem hashed_words_of_note_commit_pieces
      (a b c d e f g h
        b0 b1 b2 b3 d0 d1 d2 d3 e0 e1 g0 g1 g2 h0 h1
        gd_x pkd_x v rho psi : Z)
      (Ha : 0 <= a < 2 ^ 250)
      (Hc : 0 <= c < 2 ^ 250)
      (Hf : 0 <= f < 2 ^ 250)
      (Hb0 : 0 <= b0 < 2 ^ 4)
      (Hb1 : b1 = 0 \/ b1 = 1)
      (Hb2 : b2 = 0 \/ b2 = 1)
      (Hb3 : 0 <= b3 < 2 ^ 4)
      (Hd0 : d0 = 0 \/ d0 = 1)
      (Hd1 : d1 = 0 \/ d1 = 1)
      (Hd2 : 0 <= d2 < 2 ^ 8)
      (Hd3 : 0 <= d3 < 2 ^ 50)
      (He0 : 0 <= e0 < 2 ^ 6)
      (He1 : 0 <= e1 < 2 ^ 4)
      (Hg0 : g0 = 0 \/ g0 = 1)
      (Hg1 : 0 <= g1 < 2 ^ 9)
      (Hg2 : 0 <= g2 < 2 ^ 240)
      (Hh0 : 0 <= h0 < 2 ^ 5)
      (Hh1 : h1 = 0 \/ h1 = 1)
      (Hbv : b = b0 + b1 * 2 ^ 4 + b2 * 2 ^ 5 + b3 * 2 ^ 6)
      (Hdv : d = d0 + d1 * 2 + d2 * 2 ^ 2 + d3 * 2 ^ 10)
      (Hev : e = e0 + e1 * 2 ^ 6)
      (Hgv : g = g0 + g1 * 2 + g2 * 2 ^ 10)
      (Hhv : h = h0 + h1 * 2 ^ 5)
      (Hgd : gd_x = a + b0 * 2 ^ 250 + b1 * 2 ^ 254)
      (Hpkd : pkd_x = b3 + c * 2 ^ 4 + d0 * 2 ^ 254)
      (Hv : v = d2 + d3 * 2 ^ 8 + e0 * 2 ^ 58)
      (Hrho : rho = e1 + f * 2 ^ 4 + g0 * 2 ^ 254)
      (Hpsi : psi = g1 + g2 * 2 ^ 9 + h0 * 2 ^ 249 + h1 * 2 ^ 254) :
    SinsemillaSpec.words_le 25 a ++ SinsemillaSpec.words_le 1 b ++
    SinsemillaSpec.words_le 25 c ++ SinsemillaSpec.words_le 6 d ++
    SinsemillaSpec.words_le 1 e ++ SinsemillaSpec.words_le 25 f ++
    SinsemillaSpec.words_le 25 g ++ SinsemillaSpec.words_le 1 h =
      SinsemillaSpec.words_le 109
        (note_commit_packed gd_x b2 pkd_x d1 v rho psi).
  Proof.
    rewrite (note_commit_packed_pieces
      a b c d e f g h b0 b1 b2 b3 d0 d1 d2 d3 e0 e1 g0 g1 g2 h0 h1
      gd_x pkd_x v rho psi Hbv Hdv Hev Hgv Hhv Hgd Hpkd Hv Hrho Hpsi).
    symmetry.
    apply note_commit_words_schedule; lia.
  Qed.
End NoteCommitMessagePieces.
