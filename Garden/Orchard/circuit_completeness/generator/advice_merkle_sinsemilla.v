Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Advice sub-generator: the Merkle layers and the Sinsemilla regions

    The forward image of the Sinsemilla soundness bridges
    ([circuit_proof/merkle.v], [circuit_proof/note_commit/],
    [circuit_proof/commit_ivk/]) for the completeness witness generator: an
    [Advice.t -> RegionId.t -> Z -> Z] plane assigning every advice cell that a
    gate, copy, or lookup of these regions reads.  It covers the 32 Merkle
    layers and the three note/commitment Sinsemilla hashes (old / new
    [NoteCommit], [Commit^ivk]).

    The values are read off [witness_input.v]'s derived spec functions
    ([merkle_layer_words] / [note_commit_*_words] / [commit_ivk_words] and the
    accumulator fold [sinsemilla_acc]); the [NoteCommit] / [Commit^ivk]
    decomposition, canonicity, range-check and lookup subregions read the
    bit-slice cell layer of [tables_nc.v] at the notes' honest opening values
    (the new note's [ρ] is the old note's nullifier).  Nothing cryptographic
    is recomputed here.  Cells no gate/copy/lookup of these regions reads
    default to 0.

    The per-gate satisfaction proofs (that these cells satisfy the Sinsemilla
    and decomposition gates) are the C2 follow-up and are not attempted here;
    the obligation discharged is a total, layout-faithful generator. *)

Module OrchardAdviceMerkleSinsemilla.
  Import OrchardWitnessInput.
  Import OrchardActionInputs.

  (** ** The running-sum ([bits]) column

      Each Sinsemilla message piece is copied into the [bits] column at its
      first row; the running-sum cells below it telescope the piece's words,
      [z_t = w_t + 2¹⁰ · z_{t+1}].  [suffix_digit_sums] produces exactly that
      column for one piece (the head is [SinsemillaHash.digit_sum] of the
      piece), and [bits_column] concatenates the per-piece columns in row
      order. *)
  Fixpoint suffix_digit_sums (l : list Z) : list Z :=
    match l with
    | [] => []
    | w :: ws =>
        let r := suffix_digit_sums ws in
        (w + 2 ^ 10 * List.hd 0 r) :: r
    end.

  Lemma suffix_digit_sums_length (l : list Z) :
    List.length (suffix_digit_sums l) = List.length l.
  Proof.
    induction l as [| w ws IH]; cbn [suffix_digit_sums List.length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (** The head of a piece column is the piece's [digit_sum]: the value copied
      into the [bits] cell at the piece's first row (and witnessed in the
      piece's [Witness*] region). *)
  Lemma suffix_digit_sums_head (l : list Z) :
    List.hd 0 (suffix_digit_sums l) = SinsemillaHash.digit_sum l.
  Proof.
    induction l as [| w ws IH]; cbn [suffix_digit_sums SinsemillaHash.digit_sum].
    - reflexivity.
    - cbn [List.hd]. rewrite IH. reflexivity.
  Qed.

  Definition bits_column (pieces : list (list Z)) : list Z :=
    Stdlib.Lists.List.flat_map suffix_digit_sums pieces.

  (** Split a flat message into its pieces by the per-piece word counts. *)
  Fixpoint split_pieces (lens : list nat) (l : list Z) : list (list Z) :=
    match lens with
    | [] => []
    | len :: lens' => List.firstn len l :: split_pieces lens' (List.skipn len l)
    end.

  (** The three Sinsemilla message layouts, as piece-length lists. *)
  Definition merkle_lens : list nat := [25; 2; 25]%nat.
  Definition note_commit_lens : list nat := [25; 1; 25; 6; 1; 25; 25; 1]%nat.
  Definition commit_ivk_lens : list nat := [25; 1; 24; 1]%nat.

  (** ** The per-round incomplete-addition ladder

      One Sinsemilla round is [Acc ← (Acc ⊕ S(m)) ⊕ Acc] with incomplete
      addition; the chip witnesses, per round row, the accumulator's
      x-coordinate [x_a], the generator's x-coordinate [x_p], and the two
      secant gradients [λ₁] (chord [Acc → S(m)]) and [λ₂] (chord
      [Acc ⊕ S(m) → Acc]). *)

  (** The generator point [S(m_j)] absorbed at round [j]. *)
  Definition round_gen (words : list Z) (j : nat) : Point.t :=
    SinsemillaSpec.generator (List.nth j words 0).

  (** The accumulator before round [j] (the fold over the first [j] words). *)
  Definition round_acc (Q : Point.t) (words : list Z) (j : nat) : Point.t :=
    sinsemilla_acc Q words j.

  (** The intermediate partial sum [Acc ⊕ S(m_j)] of round [j]. *)
  Definition round_mid (Q : Point.t) (words : list Z) (j : nat) : Point.t :=
    EccSpec.point_add_incomplete (round_acc Q words j) (round_gen words j).

  (** The first secant gradient: [(y_acc − y_gen) / (x_acc − x_gen)]. *)
  Definition round_lambda1 (Q : Point.t) (words : list Z) (j : nat) : Z :=
    let acc := round_acc Q words j in
    let gen := round_gen words j in
    BinOp.div (Point.y acc -F Point.y gen) (Point.x acc -F Point.x gen).

  (** The second secant gradient: [(y_mid − y_acc) / (x_mid − x_acc)]. *)
  Definition round_lambda2 (Q : Point.t) (words : list Z) (j : nat) : Z :=
    let acc := round_acc Q words j in
    let mid := round_mid Q words j in
    BinOp.div (Point.y mid -F Point.y acc) (Point.x mid -F Point.x acc).

  (** ** Column roles

      Both Sinsemilla configuration variants place the five ladder columns
      contiguously: variant 1 on [A0..A4] (Merkle layers 0–15, old
      [NoteCommit], [Commit^ivk]), variant 2 on [A5..A9] (Merkle layers 16–31,
      new [NoteCommit]).  [logical_col second col] maps a physical column to its
      role index (0 = [x_a], 1 = [x_p], 2 = [bits], 3 = [λ₁], 4 = [λ₂]);
      the same map indexes the decomposition-region columns. *)
  Definition logical_col (second : bool) (col : Advice.t) : option nat :=
    match second, col with
    | false, Advice.A0 => Some 0%nat
    | false, Advice.A1 => Some 1%nat
    | false, Advice.A2 => Some 2%nat
    | false, Advice.A3 => Some 3%nat
    | false, Advice.A4 => Some 4%nat
    | true, Advice.A5 => Some 0%nat
    | true, Advice.A6 => Some 1%nat
    | true, Advice.A7 => Some 2%nat
    | true, Advice.A8 => Some 3%nat
    | true, Advice.A9 => Some 4%nat
    | _, _ => None
    end.

  (** ** The hash-to-point region generator

      For a hash region over domain [Q] with pieces [pieces] (message
      [concat pieces], [n = length]), the ladder cell at [(col, row)].  The
      accumulator x-coordinate runs rows [0..n] (row [n] is the output point's
      x); the generator and gradients run rows [0..n); [λ₁] additionally carries
      the output point's y at the final row (where the layout stores it).  Every
      other cell is 0. *)
  Definition hash_region_advice
      (Q : Point.t) (pieces : list (list Z)) (second : bool)
      (col : Advice.t) (row : Z) : Z :=
    let words := Stdlib.Lists.List.concat pieces in
    let nn := Z.of_nat (List.length words) in
    let j := Z.to_nat row in
    match logical_col second col with
    | Some 0%nat =>
        if (0 <=? row) && (row <=? nn)
        then Point.x (round_acc Q words j) else 0
    | Some 1%nat =>
        if (0 <=? row) && (row <? nn)
        then Point.x (round_gen words j) else 0
    | Some 2%nat =>
        if 0 <=? row then List.nth j (bits_column pieces) 0 else 0
    | Some 3%nat =>
        if (0 <=? row) && (row <? nn) then round_lambda1 Q words j
        else if row =? nn then Point.y (round_acc Q words j) else 0
    | Some 4%nat =>
        if (0 <=? row) && (row <? nn) then round_lambda2 Q words j else 0
    | _ => 0
    end.

  (** ** The Merkle layer regions

      Each layer's hash region absorbs [merkle_layer_words w i] under the
      [merkle_Q] domain, split into the pieces [a‖b‖c] = [25‖2‖25].  The
      sibling / node / position bit come from [witness_input.v]; the layer's
      children in position order are the cond-swap outputs. *)

  Definition merkle_words_i (w : HonestInput) (i : nat) : list Z :=
    merkle_layer_words w i.
  Definition merkle_pieces_i (w : HonestInput) (i : nat) : list (list Z) :=
    split_pieces merkle_lens (merkle_words_i w i).
  Definition merkle_bits_i (w : HonestInput) (i : nat) : list Z :=
    bits_column (merkle_pieces_i w i).

  (** The children in position order (§4.9): the node is the right child on a
      set position bit, the left child otherwise. *)
  Definition merkle_left (w : HonestInput) (i : nat) : Z :=
    if path_bit w i then List.nth i (hi_path w) 0 else merkle_node w i.
  Definition merkle_right (w : HonestInput) (i : nat) : Z :=
    if path_bit w i then merkle_node w i else List.nth i (hi_path w) 0.

  (** The position bit as the swap-cell value ([1] when the node is the right
      child). *)
  Definition merkle_position_bit (w : HonestInput) (i : nat) : Z :=
    if path_bit w i then 1 else 0.

  (** The cond-swap ([NodePosition]) region: at row 0, the running node on
      the [a] column, the witnessed sibling on the [b] column, the children
      in position order on the swap-output columns, and the position bit on
      the [swap] column — [A0..A4] for layers 0–15 ([QCondSwap1]),
      [A5..A9] for layers 16–31 ([QCondSwap2])
      ([synthesize_node_position_{1,2}], [cond_swap_gate]).  The node value
      is only computed in the branches that carry it, so sibling / bit reads
      (the [merkle_path_of] reader) stay cheap. *)
  Definition merkle_node_position_advice
      (w : HonestInput) (i : nat) (second : bool)
      (col : Advice.t) (row : Z) : Z :=
    if row =? 0 then
      match second, col with
      | false, Advice.A0 => merkle_node w i
      | false, Advice.A1 => List.nth i (hi_path w) 0
      | false, Advice.A2 => merkle_left w i
      | false, Advice.A3 => merkle_right w i
      | false, Advice.A4 => merkle_position_bit w i
      | true, Advice.A5 => merkle_node w i
      | true, Advice.A6 => List.nth i (hi_path w) 0
      | true, Advice.A7 => merkle_left w i
      | true, Advice.A8 => merkle_right w i
      | true, Advice.A9 => merkle_position_bit w i
      | _, _ => 0
      end
    else 0.

  (** The [b] piece's second word [b = b_1 ‖ b_2] with [b_1] the low 5 bits. *)
  Definition merkle_b_word (w : HonestInput) (i : nat) : Z :=
    List.nth 26 (merkle_words_i w i) 0.
  Definition merkle_b1 (w : HonestInput) (i : nat) : Z :=
    merkle_b_word w i mod 2 ^ 5.
  Definition merkle_b2 (w : HonestInput) (i : nat) : Z :=
    merkle_b_word w i / 2 ^ 5.

  (** The decomposition region ("Check piece decomposition"): the copied piece
      values and their [z₁] tails on rows 0/1 of the five ladder columns, with
      the middle-piece halves [b_1] / [b_2] and the constant layer index.  Its
      columns are the same variant-indexed [A0..A4] / [A5..A9] as the hash
      region, so [logical_col] indexes them. *)
  Definition merkle_decomposition_advice
      (w : HonestInput) (i : nat) (second : bool)
      (col : Advice.t) (row : Z) : Z :=
    let bits := merkle_bits_i w i in
    match logical_col second col, row with
    | Some 0%nat, 0 => List.nth 0 bits 0
    | Some 0%nat, 1 => List.nth 1 bits 0
    | Some 1%nat, 0 => List.nth 25 bits 0
    | Some 1%nat, 1 => List.nth 26 bits 0
    | Some 2%nat, 0 => List.nth 27 bits 0
    | Some 2%nat, 1 => merkle_b1 w i
    | Some 3%nat, 0 => merkle_left w i
    | Some 3%nat, 1 => merkle_b2 w i
    | Some 4%nat, 0 => merkle_right w i
    | Some 4%nat, 1 => Z.of_nat i
    | _, _ => 0
    end.

  (** The [a‖b‖c] message-piece witness regions: the piece's value at row 0 of
      the witness column ([A6] variant 1, [A7] variant 2). *)
  Definition advice_eqb (a b : Advice.t) : bool :=
    match a, b with
    | Advice.A0, Advice.A0 | Advice.A1, Advice.A1 | Advice.A2, Advice.A2
    | Advice.A3, Advice.A3 | Advice.A4, Advice.A4 | Advice.A5, Advice.A5
    | Advice.A6, Advice.A6 | Advice.A7, Advice.A7 | Advice.A8, Advice.A8
    | Advice.A9, Advice.A9 => true
    | _, _ => false
    end.

  Definition merkle_witness_col (second : bool) : Advice.t :=
    if second then Advice.A7 else Advice.A6.

  Definition merkle_witness_advice
      (w : HonestInput) (i : nat) (second : bool) (piece_start : nat)
      (col : Advice.t) (row : Z) : Z :=
    let bits := merkle_bits_i w i in
    if advice_eqb col (merkle_witness_col second) && (row =? 0)
    then List.nth piece_start bits 0 else 0.

  (** The two 5-bit range-check regions [RangeB1] / [RangeB2]: the checked value
      on [A9] at row 0 (the short-lookup running sum's leading cell). *)
  Definition merkle_range_advice (value : Z) (col : Advice.t) (row : Z) : Z :=
    match col, row with
    | Advice.A9, 0 => value
    | _, _ => 0
    end.

  (** ** The note / commitment Sinsemilla hash domains *)
  Definition note_commit_Q : Point.t :=
    OrchardSpec.note_commit_q orchard_circuit_params.
  Definition commit_ivk_Q : Point.t :=
    OrchardSpec.commit_ivk_q orchard_circuit_params.

  (** ** The dispatcher

      The advice plane for the covered regions; 0 elsewhere (those regions are
      owned by sibling sub-generators).  Within the note/commitment subtrees,
      the hash regions carry the incomplete-addition ladder, and every
      message-piece, input-decomposition, y-canonicity, range-check and
      canonicity-lookup subregion reads the [tables_nc.v] cell layer; the
      fixed-base blinding legs and the final complete additions are the ECC
      sub-generator's regions and read 0 here. *)
  Definition advice
      (w : HonestInput) (col : Advice.t) (region : RegionId.t) (row : Z) : Z :=
    match region with
    | RegionId.Merkle layer mregion =>
        let i := Z.to_nat (RegionId.Merkle.Layer.to_index layer) in
        let second := negb (RegionId.Merkle.Layer.to_index layer <? 16) in
        match mregion with
        | RegionId.Merkle.Region.NodePosition =>
            merkle_node_position_advice w i second col row
        | RegionId.Merkle.Region.HashToPoint =>
            hash_region_advice merkle_Q (merkle_pieces_i w i) second col row
        | RegionId.Merkle.Region.Decomposition =>
            merkle_decomposition_advice w i second col row
        | RegionId.Merkle.Region.WitnessA =>
            merkle_witness_advice w i second 0 col row
        | RegionId.Merkle.Region.WitnessB =>
            merkle_witness_advice w i second 25 col row
        | RegionId.Merkle.Region.WitnessC =>
            merkle_witness_advice w i second 27 col row
        | RegionId.Merkle.Region.RangeB1 =>
            merkle_range_advice (merkle_b1 w i) col row
        | RegionId.Merkle.Region.RangeB2 =>
            merkle_range_advice (merkle_b2 w i) col row
        end
    | RegionId.NoteCommit which nregion =>
        match nregion with
        | RegionId.NoteCommit.HashToPoint =>
            match which with
            | RegionId.NoteCommit.Which.Old =>
                hash_region_advice note_commit_Q
                  (split_pieces note_commit_lens (note_commit_old_words w))
                  false col row
            | RegionId.NoteCommit.Which.New =>
                hash_region_advice note_commit_Q
                  (split_pieces note_commit_lens (note_commit_new_words w))
                  true col row
            end
        | RegionId.NoteCommit.FixedBaseIncomplete
        | RegionId.NoteCommit.FixedBaseLast
        | RegionId.NoteCommit.CompletePointAdd => 0
        | _ =>
            match which with
            | RegionId.NoteCommit.Which.Old =>
                OrchardNoteCommitCells.nc_advice
                  (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w)
                  (hi_rho_old w) (hi_psi_old w) false nregion col row
            | RegionId.NoteCommit.Which.New =>
                OrchardNoteCommitCells.nc_advice
                  (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
                  (rho_new w) (hi_psi_new w) true nregion col row
            end
        end
    | RegionId.CommitIvk cregion =>
        match cregion with
        | RegionId.CommitIvk.HashToPoint =>
            hash_region_advice commit_ivk_Q
              (split_pieces commit_ivk_lens (commit_ivk_words w))
              false col row
        | RegionId.CommitIvk.FixedBaseIncomplete
        | RegionId.CommitIvk.FixedBaseLast
        | RegionId.CommitIvk.CompletePointAdd => 0
        | _ =>
            OrchardNoteCommitCells.civk_advice
              (EccSpec.extract_x (hi_ak w)) (hi_nk w) cregion col row
        end
    | _ => 0
    end.

End OrchardAdviceMerkleSinsemilla.
