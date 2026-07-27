Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Sinsemilla hash / commitment specification

    Fold the per-round Sinsemilla
    arithmetic into a hash-to-point, then build the commitment and the Merkle
    root on top of it.

    [sinsemilla_hash_to_point] is the canonical Sinsemilla incomplete-addition
    fold: starting from the domain point [Q], each [k]-bit message word [m]
    updates the accumulator by the doubling-and-add step
    [Acc <- (Acc + S(m)) + Acc], where [S] is the generator looked up in the
    [sinsemilla_s] table.  The chip proves the x-coordinate of this exact step
    per round ([Sinsemilla.deterministic]) and binds [S] to the table word
    ([GeneratorTable.sound]); composing them along the message is the
    hash-level soundness result of [hash_to_point_proof.v] /
    [hash_to_point_fold_proof.v].

    Protocol reference: §5.4.1.9 'Sinsemilla Hash Function' of the Zcash
    protocol specification defines
    [SinsemillaHashToPoint] as exactly this fold ([k = 10]; per word
    [Acc ← (Acc ⊕ 𝒮(m_i)) ⊕ Acc] with incomplete addition [⊕]), so the
    circuit-structured and protocol functions coincide on the honest
    (non-⊥) branch; the exceptional [⊥] cases of [⊕] (equal x-coordinates,
    identity operands) are where the protocol's functions return [⊥] while
    these total transcriptions compute the chip's unconstrained value.  The
    domain and per-word generators are [𝒬(D)]/[𝒮(j)] group hashes
    (§5.4.9.8); here they are the circuit's concrete constants — [Q] a
    parameter, [S] the [sinsemilla_s] lookup table. *)

Module SinsemillaSpec.
  Definition sinsemilla_k : Z := 10.

  (** Generator [S(m)] for a [k]-bit word [m], from the concrete
      [sinsemilla_s] table the lookup argument is proved against. *)
  Definition generator (word : Z) : Point.t := {|
    Point.x := Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.x word;
    Point.y := Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.y word;
  |}.

  (** One Sinsemilla round: [Acc <- (Acc ⊕ S(m)) ⊕ Acc] with incomplete
      addition [⊕].  This is the per-word step whose x-coordinate the chip
      gate computes ([λ₂² - λ₁² + x_p]). *)
  Definition round (acc : Point.t) (word : Z) : Point.t :=
    EccSpec.point_add_incomplete
      (EccSpec.point_add_incomplete acc (generator word))
      acc.

  (** Hash-to-point: left-fold of [round] over the message words, seeded by the
      domain point [Q]. *)
  Definition sinsemilla_hash_to_point (Q : Point.t) (words : list Z) : Point.t :=
    Stdlib.Lists.List.fold_left round words Q.

  (** Sinsemilla hash: the x-coordinate of the hash-to-point. *)
  Definition sinsemilla_hash (Q : Point.t) (words : list Z) : Z :=
    EccSpec.extract_x (sinsemilla_hash_to_point Q words).

  (** Sinsemilla commitment: blind the hash-to-point with [r]·[R], where [R] is
      the commitment-randomness base.  ([SinsemillaCommit] = hash-to-point in
      the commitment domain plus the [Pedersen]-style blinding term.)

      Protocol: §5.4.8.4 'Sinsemilla commitments',
      [SinsemillaCommit_r(D, M) = SinsemillaHashToPoint(D || "-M", M)
      + [r] GroupHash^P(D || "-r", "")]; [Q] and [R] are the two group-hash
      points, supplied here as concrete parameters. *)
  Definition sinsemilla_commit
      (Q : Point.t) (words : list Z) (r : Z) (R : Point.t) : Point.t :=
    EccSpec.point_add
      (sinsemilla_hash_to_point Q words)
      (EccSpec.scalar_mul r R).

  (** Short Sinsemilla commitment ([SinsemillaCommit] then [Extract_x]) — the
      shape used by [NoteCommit]/[CommitIvk] to produce a field element.

      Protocol: §5.4.8.4, [SinsemillaShortCommit_r(D, M) =
      Extract⊥_P(SinsemillaCommit_r(D, M))]. *)
  Definition sinsemilla_short_commit
      (Q : Point.t) (words : list Z) (r : Z) (R : Point.t) : Z :=
    EccSpec.extract_x (sinsemilla_commit Q words r R).

  (** Little-endian decomposition of [n] into [count] words of [k = 10] bits —
      the internal message encoding the running-sum decomposition gates check. *)
  Fixpoint words_le (count : nat) (n : Z) : list Z :=
    match count with
    | O => []
    | S c => (n mod (2 ^ sinsemilla_k)) :: words_le c (n / (2 ^ sinsemilla_k))
    end.

  (** Merkle layer message: the 10-bit layer index [l] followed by the two
      255-bit child hashes, packed into 52 ten-bit words (520 bits).

      Protocol: §5.4.1.3 'Merkle Tree Hash Function', the [MerkleCRH^Orchard]
      message [l⋆ || left⋆ || right⋆] with
      [l⋆ = I2LEBSP_10(MerkleDepth^Orchard − 1 − layer)] and 255-bit child
      encodings; the [layer] argument here is that already-flipped 10-bit
      prefix (0 at the layer above the leaves, 31 at the root), matching the
      leaf-upward fold of [merkle_root]. *)
  Definition merkle_message (layer left right : Z) : list Z :=
    words_le 52 (layer + left * 2 ^ sinsemilla_k + right * 2 ^ (sinsemilla_k + 255)).

  (** Orchard [MerkleCRH]: Sinsemilla-hash the layer-tagged child pair.

      Protocol: §5.4.1.3, [MerkleCRH^Orchard(layer, left, right) =
      SinsemillaHash("z.cash:Orchard-MerkleCRH", l⋆ || left⋆ || right⋆)],
      the [hash = ⊥ ↦ 0] escape hatch of that definition being the
      incomplete-addition slack the Action statement's notes sanction. *)
  Definition merkle_crh
      (Q : Point.t) (layer left right : Z) : Z :=
    sinsemilla_hash Q (merkle_message layer left right).

  (** Combine a node with its sibling at a layer, respecting the position bit
      ([node_is_right] swaps the two children before hashing). *)
  Definition merkle_layer
      (Q : Point.t) (layer node sibling : Z) (node_is_right : bool) : Z :=
    if node_is_right
    then merkle_crh Q layer sibling node
    else merkle_crh Q layer node sibling.

  (** Merkle root: fold [merkle_layer] up the authentication path from the leaf.
      Orchard uses a 32-layer tree, so [path] has length 32.

      Protocol: §4.9 'Merkle Path Validity' — verifying a Merkle path from a
      leaf to the root [rt = M⁰₀], the per-layer swap bit being the node's
      position parity at that layer. *)
  Definition merkle_root
      (Q : Point.t) (leaf : Z) (path : list (Z * Z * bool)) : Z :=
    Stdlib.Lists.List.fold_left
      (fun node '(layer, sibling, b) => merkle_layer Q layer node sibling b)
      path
      leaf.

  (** The empty message hashes to the domain point — base case of the fold. *)
  Lemma sinsemilla_hash_to_point_nil (Q : Point.t) :
    sinsemilla_hash_to_point Q [] = Q.
  Proof. reflexivity. Qed.

  (** One more word extends the fold by a single [round] — the inductive step
      the hash-level soundness composition runs on. *)
  Lemma sinsemilla_hash_to_point_app (Q : Point.t) (words : list Z) (word : Z) :
    sinsemilla_hash_to_point Q (words ++ [word]) =
      round (sinsemilla_hash_to_point Q words) word.
  Proof.
    unfold sinsemilla_hash_to_point.
    now rewrite Stdlib.Lists.List.fold_left_app.
  Qed.
End SinsemillaSpec.
