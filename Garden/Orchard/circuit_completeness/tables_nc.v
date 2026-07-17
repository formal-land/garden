Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Cell values of the note-commitment and [Commit^ivk] decomposition,
    canonicity and range subregions

    The forward image of the [circuit_proof/note_commit/] and
    [circuit_proof/ownership/commit_ivk_hash.v] soundness layers for the
    completeness witness generator: per region, the advice cells that the
    [NoteCommit] message-piece / input-decomposition / y-canonicity gates
    ([circuit/note_commit.v]) and the [Commit^ivk] canonicity gate
    ([circuit/commit_ivk.v]) read, together with the short range-check and
    lookup running-sum columns they are copied from.

    Every value is a bit slice (div/mod at a fixed shift) of the packed
    Sinsemilla message of §5.4.8.4 —

      [x(g_d) + ỹ(g_d)·2^255 + x(pk_d)·2^256 + ỹ(pk_d)·2^511 + v·2^512
        + ρ·2^576 + ψ·2^831]

    for a note ([OrchardSpec.note_commit_message] hashes its 109-word
    little-endian decomposition), and [ak_x + nk·2^255] for [Commit^ivk] —
    so a piece value here equals the [digit_sum] head that the hash region's
    [bits] column carries at the piece's first row, and the [z_k] running
    sums equal the corresponding [bits] cells ([z_k = piece / 2^(10·k)]).
    No cryptography and no per-region fold is recomputed: every read costs a
    handful of integer divisions, so the readers are safe to call from both
    the per-read reference generator and the hoisted-table advice plane.

    The readers are parameterized by the note's input values (points and
    field elements), never by [HonestInput]: the caller chooses the honest
    instantiation (for the new note, [ρ] is the old note's nullifier; for
    the old note, [pk_d] is the variable-base product [[ivk] g_d]). *)

Module OrchardNoteCommitCells.
  (** ** Shared helpers *)

  (** The canonicity offset [low + 2^k − t_P], reduced to the field
      representative (the gate states the check with field arithmetic, so
      the copied running-sum head must carry the reduced value). *)
  Definition prime_of (low k : Z) : Z :=
    (low + 2 ^ k - Primes.t_p) mod Primes.pallas_p.

  (** A short [s]-bit range-check region ([synthesize_short]): the checked
      element at [A9] row 0, the bitshifted word [element · 2^(10−s)] at
      row 1 (the [q_bitshift] gate pins [word · 2^10 · inv_two_pow_s =
      shifted]), and the pinned constant [inv_two_pow_s] at row 2. *)
  Definition short_range_advice (value shifted_factor inv_const : Z)
      (col : Advice.t) (row : Z) : Z :=
    match col, row with
    | Advice.A9, 0 => value
    | Advice.A9, 1 => value * shifted_factor
    | Advice.A9, 2 => inv_const
    | _, _ => 0
    end.

  (** A running-sum lookup region ([synthesize_running_lookup]): the
      running sums [z_i = z_0 / 2^(10·i)] on [A9] rows [0 .. count] (each
      looked-up word is [z_i − 2^10·z_{i+1}], a 10-bit digit of [z_0]). *)
  Definition running_lookup_advice (z_0 count : Z)
      (col : Advice.t) (row : Z) : Z :=
    match col with
    | Advice.A9 =>
        if (0 <=? row) && (row <=? count) then z_0 / 2 ^ (10 * row) else 0
    | _ => 0
    end.

  (** ** The y-canonicity block (per note, per subject [g_d] / [pk_d])

      §5.4.8.4 compresses each point as [x ‖ ỹ]; the circuit checks the
      witnessed sign bit against the y-coordinate through the decomposition
      [y = j + k_2·2^250 + k_3·2^254] with [j = ỹ + k_0·2 + z1_j·2^10]
      ([circuit/note_commit.v], [y_coordinate_checks_gate]). *)

  Definition ycanon_j (y : Z) : Z := y mod 2 ^ 250.
  Definition ycanon_lsb (y : Z) : Z := y mod 2.
  Definition ycanon_k0 (y : Z) : Z := (y / 2) mod 2 ^ 9.
  Definition ycanon_k2 (y : Z) : Z := (y / 2 ^ 250) mod 2 ^ 4.
  Definition ycanon_k3 (y : Z) : Z := y / 2 ^ 254.
  Definition ycanon_j_prime (y : Z) : Z := prime_of (ycanon_j y) 130.

  (** The y-canonicity subregions: the two short range checks on [k_0] /
      [k_2], the strict 25-row [j] lookup, the 13-row [j'] lookup, and the
      gate rows — row 0 [(y, ỹ, k_0, k_2, k_3)] on [A5..A9], row 1
      [(j, z1_j, z13_j, j', z13_j')]. *)
  Definition ycanon_advice (y : Z)
      (region : RegionId.NoteCommit.YCanonicity.t)
      (col : Advice.t) (row : Z) : Z :=
    match region with
    | RegionId.NoteCommit.YCanonicity.RangeK0 =>
        short_range_advice (ycanon_k0 y) 2
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9 col row
    | RegionId.NoteCommit.YCanonicity.RangeK2 =>
        short_range_advice (ycanon_k2 y) (2 ^ 6)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 col row
    | RegionId.NoteCommit.YCanonicity.JLookup =>
        running_lookup_advice (ycanon_j y) 25 col row
    | RegionId.NoteCommit.YCanonicity.JPrimeLookup =>
        running_lookup_advice (ycanon_j_prime y) 13 col row
    | RegionId.NoteCommit.YCanonicity.Gate =>
        match col, row with
        | Advice.A5, 0 => y
        | Advice.A6, 0 => ycanon_lsb y
        | Advice.A7, 0 => ycanon_k0 y
        | Advice.A8, 0 => ycanon_k2 y
        | Advice.A9, 0 => ycanon_k3 y
        | Advice.A5, 1 => ycanon_j y
        | Advice.A6, 1 => ycanon_j y / 2 ^ 10
        | Advice.A7, 1 => ycanon_j y / 2 ^ 130
        | Advice.A8, 1 => ycanon_j_prime y
        | Advice.A9, 1 => ycanon_j_prime y / 2 ^ 130
        | _, _ => 0
        end
    end.

  (** ** The note-commitment message pieces

      The 1090-bit packed message, split as the eight hashed pieces
      [a‖b‖c‖d‖e‖f‖g‖h] of 250/10/250/60/10/250/250/10 bits
      ([circuit_proof/note_commit/pieces.v] fixes the boundaries), each
      piece further split into the gate sub-pieces. *)

  Definition nc_packed (gd pkd : Point.t) (v rho psi : Z) : Z :=
    EccSpec.extract_x gd
      + (Point.y gd mod 2) * 2 ^ 255
      + EccSpec.extract_x pkd * 2 ^ 256
      + (Point.y pkd mod 2) * 2 ^ 511
      + v * 2 ^ 512
      + rho * 2 ^ 576
      + psi * 2 ^ 831.

  Definition nc_a (packed : Z) : Z := packed mod 2 ^ 250.
  Definition nc_b (packed : Z) : Z := (packed / 2 ^ 250) mod 2 ^ 10.
  Definition nc_c (packed : Z) : Z := (packed / 2 ^ 260) mod 2 ^ 250.
  Definition nc_d (packed : Z) : Z := (packed / 2 ^ 510) mod 2 ^ 60.
  Definition nc_e (packed : Z) : Z := (packed / 2 ^ 570) mod 2 ^ 10.
  Definition nc_f (packed : Z) : Z := (packed / 2 ^ 580) mod 2 ^ 250.
  Definition nc_g (packed : Z) : Z := (packed / 2 ^ 830) mod 2 ^ 250.
  Definition nc_h (packed : Z) : Z := (packed / 2 ^ 1080) mod 2 ^ 10.

  (** [b = b_0 ‖ b_1 ‖ b_2 ‖ b_3] (4/1/1/4 bits). *)
  Definition nc_b0 (packed : Z) : Z := nc_b packed mod 2 ^ 4.
  Definition nc_b1 (packed : Z) : Z := (nc_b packed / 2 ^ 4) mod 2.
  Definition nc_b2 (packed : Z) : Z := (nc_b packed / 2 ^ 5) mod 2.
  Definition nc_b3 (packed : Z) : Z := nc_b packed / 2 ^ 6.

  (** [d = d_0 ‖ d_1 ‖ d_2 ‖ d_3] (1/1/8/50 bits). *)
  Definition nc_d0 (packed : Z) : Z := nc_d packed mod 2.
  Definition nc_d1 (packed : Z) : Z := (nc_d packed / 2) mod 2.
  Definition nc_d2 (packed : Z) : Z := (nc_d packed / 2 ^ 2) mod 2 ^ 8.
  Definition nc_d3 (packed : Z) : Z := nc_d packed / 2 ^ 10.

  (** [e = e_0 ‖ e_1] (6/4 bits). *)
  Definition nc_e0 (packed : Z) : Z := nc_e packed mod 2 ^ 6.
  Definition nc_e1 (packed : Z) : Z := nc_e packed / 2 ^ 6.

  (** [g = g_0 ‖ g_1 ‖ g_2] (1/9/240 bits). *)
  Definition nc_g0 (packed : Z) : Z := nc_g packed mod 2.
  Definition nc_g1 (packed : Z) : Z := (nc_g packed / 2) mod 2 ^ 9.
  Definition nc_g2 (packed : Z) : Z := nc_g packed / 2 ^ 10.

  (** [h = h_0 ‖ h_1] (5/1 bits; the piece's 10-bit word is zero-padded). *)
  Definition nc_h0 (packed : Z) : Z := nc_h packed mod 2 ^ 5.
  Definition nc_h1 (packed : Z) : Z := nc_h packed / 2 ^ 5.

  (** The four canonicity offsets of the input-decomposition gates. *)
  Definition nc_a_prime (packed : Z) : Z := prime_of (nc_a packed) 130.
  Definition nc_b3_c_prime (packed : Z) : Z :=
    prime_of (nc_b3 packed + nc_c packed * 2 ^ 4) 140.
  Definition nc_e1_f_prime (packed : Z) : Z :=
    prime_of (nc_e1 packed + nc_f packed * 2 ^ 4) 140.
  Definition nc_g1_g2_prime (packed : Z) : Z :=
    prime_of (nc_g1 packed + nc_g2 packed * 2 ^ 9) 130.

  (** The message-piece witness column: [A6] under the first Sinsemilla
      configuration (the old note), [A7] under the second (the new note). *)
  Definition nc_piece_col (second : bool) : Advice.t :=
    if second then Advice.A7 else Advice.A6.

  Definition col_eqb (a b : Advice.t) : bool :=
    match a, b with
    | Advice.A0, Advice.A0 | Advice.A1, Advice.A1 | Advice.A2, Advice.A2
    | Advice.A3, Advice.A3 | Advice.A4, Advice.A4 | Advice.A5, Advice.A5
    | Advice.A6, Advice.A6 | Advice.A7, Advice.A7 | Advice.A8, Advice.A8
    | Advice.A9, Advice.A9 => true
    | _, _ => false
    end.

  Definition nc_witness_piece (second : bool) (value : Z)
      (col : Advice.t) (row : Z) : Z :=
    if col_eqb col (nc_piece_col second) && (row =? 0) then value else 0.

  (** The per-note advice reader.  [gd]/[pkd]/[v]/[rho]/[psi] are the note's
      §4.18.4 opening values; [second] selects the message-piece witness
      column.  The hash region, the fixed-base blinding leg and the final
      complete addition are owned by sibling sub-generators and read 0
      here. *)
  Definition nc_advice (gd pkd : Point.t) (v rho psi : Z) (second : bool)
      (region : RegionId.NoteCommit.t) (col : Advice.t) (row : Z) : Z :=
    match region with
    | RegionId.NoteCommit.HashToPoint
    | RegionId.NoteCommit.FixedBaseIncomplete
    | RegionId.NoteCommit.FixedBaseLast
    | RegionId.NoteCommit.CompletePointAdd => 0
    (* The witnessed message pieces (the [bits]-column heads of the hash
       region). *)
    | RegionId.NoteCommit.WitnessA =>
        nc_witness_piece second (nc_a (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessB =>
        nc_witness_piece second (nc_b (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessC =>
        nc_witness_piece second (nc_c (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessD =>
        nc_witness_piece second (nc_d (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessE =>
        nc_witness_piece second (nc_e (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessF =>
        nc_witness_piece second (nc_f (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessG =>
        nc_witness_piece second (nc_g (nc_packed gd pkd v rho psi)) col row
    | RegionId.NoteCommit.WitnessH =>
        nc_witness_piece second (nc_h (nc_packed gd pkd v rho psi)) col row
    (* The short range checks on the sub-pieces. *)
    | RegionId.NoteCommit.RangeB0 =>
        short_range_advice (nc_b0 (nc_packed gd pkd v rho psi)) (2 ^ 6)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 col row
    | RegionId.NoteCommit.RangeB3 =>
        short_range_advice (nc_b3 (nc_packed gd pkd v rho psi)) (2 ^ 6)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 col row
    | RegionId.NoteCommit.RangeD2 =>
        short_range_advice (nc_d2 (nc_packed gd pkd v rho psi)) (2 ^ 2)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_8 col row
    | RegionId.NoteCommit.RangeE0 =>
        short_range_advice (nc_e0 (nc_packed gd pkd v rho psi)) (2 ^ 4)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_6 col row
    | RegionId.NoteCommit.RangeE1 =>
        short_range_advice (nc_e1 (nc_packed gd pkd v rho psi)) (2 ^ 6)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 col row
    | RegionId.NoteCommit.RangeG1 =>
        short_range_advice (nc_g1 (nc_packed gd pkd v rho psi)) 2
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9 col row
    | RegionId.NoteCommit.RangeH0 =>
        short_range_advice (nc_h0 (nc_packed gd pkd v rho psi)) (2 ^ 5)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5 col row
    (* The y-canonicity blocks of the two compressed points. *)
    | RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD y_region =>
        ycanon_advice (Point.y gd) y_region col row
    | RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD y_region =>
        ycanon_advice (Point.y pkd) y_region col row
    (* The canonicity lookup running sums of the four decomposed inputs. *)
    | RegionId.NoteCommit.XGDLookup =>
        running_lookup_advice (nc_a_prime (nc_packed gd pkd v rho psi)) 13
          col row
    | RegionId.NoteCommit.XPKDLookup =>
        running_lookup_advice (nc_b3_c_prime (nc_packed gd pkd v rho psi)) 14
          col row
    | RegionId.NoteCommit.RhoLookup =>
        running_lookup_advice (nc_e1_f_prime (nc_packed gd pkd v rho psi)) 14
          col row
    | RegionId.NoteCommit.PsiLookup =>
        running_lookup_advice (nc_g1_g2_prime (nc_packed gd pkd v rho psi)) 13
          col row
    (* The message-piece decomposition gate rows. *)
    | RegionId.NoteCommit.MessagePieceB =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => nc_b packed
        | Advice.A7, 0 => nc_b0 packed
        | Advice.A8, 0 => nc_b1 packed
        | Advice.A7, 1 => nc_b2 packed
        | Advice.A8, 1 => nc_b3 packed
        | _, _ => 0
        end
    | RegionId.NoteCommit.MessagePieceD =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => nc_d packed
        | Advice.A7, 0 => nc_d0 packed
        | Advice.A8, 0 => nc_d1 packed
        | Advice.A7, 1 => nc_d2 packed
        | Advice.A8, 1 => nc_d3 packed
        | _, _ => 0
        end
    | RegionId.NoteCommit.MessagePieceE =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => nc_e packed
        | Advice.A7, 0 => nc_e0 packed
        | Advice.A8, 0 => nc_e1 packed
        | _, _ => 0
        end
    | RegionId.NoteCommit.MessagePieceG =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => nc_g packed
        | Advice.A7, 0 => nc_g0 packed
        | Advice.A6, 1 => nc_g1 packed
        | Advice.A7, 1 => nc_g2 packed
        | _, _ => 0
        end
    | RegionId.NoteCommit.MessagePieceH =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => nc_h packed
        | Advice.A7, 0 => nc_h0 packed
        | Advice.A8, 0 => nc_h1 packed
        | _, _ => 0
        end
    (* The input-decomposition gate rows. *)
    | RegionId.NoteCommit.InputGD =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => EccSpec.extract_x gd
        | Advice.A7, 0 => nc_b0 packed
        | Advice.A7, 1 => nc_b1 packed
        | Advice.A8, 0 => nc_a packed
        | Advice.A8, 1 => nc_a_prime packed
        | Advice.A9, 0 => nc_a packed / 2 ^ 130
        | Advice.A9, 1 => nc_a_prime packed / 2 ^ 130
        | _, _ => 0
        end
    | RegionId.NoteCommit.InputPkD =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => EccSpec.extract_x pkd
        | Advice.A7, 0 => nc_b3 packed
        | Advice.A7, 1 => nc_d0 packed
        | Advice.A8, 0 => nc_c packed
        | Advice.A8, 1 => nc_b3_c_prime packed
        | Advice.A9, 0 => nc_c packed / 2 ^ 130
        | Advice.A9, 1 => nc_b3_c_prime packed / 2 ^ 140
        | _, _ => 0
        end
    | RegionId.NoteCommit.InputValue =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => v
        | Advice.A7, 0 => nc_d2 packed
        | Advice.A8, 0 => nc_d3 packed
        | Advice.A9, 0 => nc_e0 packed
        | _, _ => 0
        end
    | RegionId.NoteCommit.InputRho =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => rho
        | Advice.A7, 0 => nc_e1 packed
        | Advice.A7, 1 => nc_g0 packed
        | Advice.A8, 0 => nc_f packed
        | Advice.A8, 1 => nc_e1_f_prime packed
        | Advice.A9, 0 => nc_f packed / 2 ^ 130
        | Advice.A9, 1 => nc_e1_f_prime packed / 2 ^ 140
        | _, _ => 0
        end
    | RegionId.NoteCommit.InputPsi =>
        let packed := nc_packed gd pkd v rho psi in
        match col, row with
        | Advice.A6, 0 => psi
        | Advice.A6, 1 => nc_h0 packed
        | Advice.A7, 0 => nc_g1 packed
        | Advice.A7, 1 => nc_h1 packed
        | Advice.A8, 0 => nc_g2 packed
        | Advice.A8, 1 => nc_g1_g2_prime packed
        | Advice.A9, 0 => nc_g packed / 2 ^ 130
        | Advice.A9, 1 => nc_g1_g2_prime packed / 2 ^ 130
        | _, _ => 0
        end
    end.

  (** ** The [Commit^ivk] message pieces

      The 510-bit packed message [ak_x + nk·2^255], split as the four hashed
      pieces [a‖b‖c‖d] of 250/10/240/10 bits
      ([circuit_proof/ownership/commit_ivk_hash.v] fixes the boundaries):
      [ak_x = a + b_0·2^250 + b_1·2^254] and
      [nk = b_2 + c·2^5 + d_0·2^245 + d_1·2^254]. *)

  Definition civk_packed (ak_x nk : Z) : Z := ak_x + nk * 2 ^ 255.

  Definition civk_a (packed : Z) : Z := packed mod 2 ^ 250.
  Definition civk_b (packed : Z) : Z := (packed / 2 ^ 250) mod 2 ^ 10.
  Definition civk_c (packed : Z) : Z := (packed / 2 ^ 260) mod 2 ^ 240.
  Definition civk_d (packed : Z) : Z := (packed / 2 ^ 500) mod 2 ^ 10.

  (** [b = b_0 ‖ b_1 ‖ b_2] (4/1/5 bits), [d = d_0 ‖ d_1] (9/1 bits). *)
  Definition civk_b0 (packed : Z) : Z := civk_b packed mod 2 ^ 4.
  Definition civk_b1 (packed : Z) : Z := (civk_b packed / 2 ^ 4) mod 2.
  Definition civk_b2 (packed : Z) : Z := civk_b packed / 2 ^ 5.
  Definition civk_d0 (packed : Z) : Z := civk_d packed mod 2 ^ 9.
  Definition civk_d1 (packed : Z) : Z := civk_d packed / 2 ^ 9.

  Definition civk_a_prime (packed : Z) : Z := prime_of (civk_a packed) 130.
  Definition civk_b2_c_prime (packed : Z) : Z :=
    prime_of (civk_b2 packed + civk_c packed * 2 ^ 5) 140.

  (** The per-instance advice reader over [ak_x = Extract_P(ak)] and [nk].
      The hash region, the fixed-base blinding leg and the final complete
      addition are owned by sibling sub-generators and read 0 here. *)
  Definition civk_advice (ak_x nk : Z)
      (region : RegionId.CommitIvk.t) (col : Advice.t) (row : Z) : Z :=
    match region with
    | RegionId.CommitIvk.HashToPoint
    | RegionId.CommitIvk.FixedBaseIncomplete
    | RegionId.CommitIvk.FixedBaseLast
    | RegionId.CommitIvk.CompletePointAdd => 0
    (* The witnessed message pieces (the [bits]-column heads of the hash
       region), on the first configuration's witness column [A6]. *)
    | RegionId.CommitIvk.WitnessA =>
        nc_witness_piece false (civk_a (civk_packed ak_x nk)) col row
    | RegionId.CommitIvk.WitnessB =>
        nc_witness_piece false (civk_b (civk_packed ak_x nk)) col row
    | RegionId.CommitIvk.WitnessC =>
        nc_witness_piece false (civk_c (civk_packed ak_x nk)) col row
    | RegionId.CommitIvk.WitnessD =>
        nc_witness_piece false (civk_d (civk_packed ak_x nk)) col row
    (* The short range checks on the sub-pieces. *)
    | RegionId.CommitIvk.RangeB0 =>
        short_range_advice (civk_b0 (civk_packed ak_x nk)) (2 ^ 6)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 col row
    | RegionId.CommitIvk.RangeB2 =>
        short_range_advice (civk_b2 (civk_packed ak_x nk)) (2 ^ 5)
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5 col row
    | RegionId.CommitIvk.RangeD0 =>
        short_range_advice (civk_d0 (civk_packed ak_x nk)) 2
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9 col row
    (* The canonicity lookup running sums. *)
    | RegionId.CommitIvk.AkLookup =>
        running_lookup_advice (civk_a_prime (civk_packed ak_x nk)) 13 col row
    | RegionId.CommitIvk.NkLookup =>
        running_lookup_advice (civk_b2_c_prime (civk_packed ak_x nk)) 14
          col row
    (* The canonicity gate rows: row 0 the [ak] face, row 1 the [nk] face
       ([circuit/commit_ivk.v], [assign_cells_used_in_canonicity_gate]). *)
    | RegionId.CommitIvk.CanonicityGate =>
        let packed := civk_packed ak_x nk in
        match col, row with
        | Advice.A0, 0 => ak_x
        | Advice.A1, 0 => civk_a packed
        | Advice.A2, 0 => civk_b packed
        | Advice.A3, 0 => civk_b0 packed
        | Advice.A4, 0 => civk_b1 packed
        | Advice.A5, 0 => civk_b2 packed
        | Advice.A6, 0 => civk_a packed / 2 ^ 130
        | Advice.A7, 0 => civk_a_prime packed
        | Advice.A8, 0 => civk_a_prime packed / 2 ^ 130
        | Advice.A0, 1 => nk
        | Advice.A1, 1 => civk_c packed
        | Advice.A2, 1 => civk_d packed
        | Advice.A3, 1 => civk_d0 packed
        | Advice.A4, 1 => civk_d1 packed
        | Advice.A6, 1 => civk_c packed / 2 ^ 130
        | Advice.A7, 1 => civk_b2_c_prime packed
        | Advice.A8, 1 => civk_b2_c_prime packed / 2 ^ 140
        | _, _ => 0
        end
    end.

End OrchardNoteCommitCells.
