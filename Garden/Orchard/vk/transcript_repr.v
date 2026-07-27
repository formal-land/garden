(** * T2: the verifying key's Fiat–Shamir binding scalar, in-model.

    The second certificate of the [transcript_repr] byte channel: the
    scalar [keygen_vk] computes from the pinned circuit description
    ([halo2_proofs/src/plonk.rs], [VerifyingKey::from_parts]) —

      s      = format!("{:?}", vk.pinned())
      digest = BLAKE2b-512(le64(s.len()) || s)
                 with hash_length 64, no key, zero salt,
                 personalization b"Halo2-Verify-Key"
      transcript_repr = C::Scalar::from_uniform_bytes(digest)

    — computed over the compact rendering [VkPinnedPrint.vk_pinned_compact]
    of the verified printer, whose pretty rendering the T1 certificate
    ([vk/parity.v]) pins byte-for-byte to the deployed dump
    [circuit_description_fixed].  [C = vesta::Affine], so [C::Scalar] is
    the Pallas base field [Primes.pallas_p] (the circuit's own field; the
    dump's [scalar_modulus] string), and [from_uniform_bytes] reads the
    64-byte digest as a little-endian 512-bit integer reduced mod
    [pallas_p] ([pasta_curves] [src/fields/fp.rs], [from_u512]:
    [d0 * R2 + d1 * R3] over the two 256-bit halves, whose mathematical
    value is exactly that reduction).

    The BLAKE2b pipeline is [GroupHash/blake2b.v]'s [Blake2b.blake2b]
    with the 16-byte personalization; the parameter-block wiring is
    guarded by a personalized reference vector before the full fold.
    The 285,142-byte input (2,228 blocks) is sharded: [compress_run]
    re-expresses the non-final [compress_blocks] prefix, the
    [compress_blocks_chunk] lemma peels block ranges, and four
    state-threading certificates pin the 8-word chain values between
    ranges, so no single [vm_compute] pays the whole fold.

    The delivered scalar [transcript_repr] is the value [hash_into]
    absorbs into the verifier transcript before any proof data, binding
    every Fiat–Shamir challenge to the pinned description.  A future L0
    composition consumes it as the concrete anchor of the named
    transcript hypotheses ([Halo2.plonkish.boundary]): together with T1
    it identifies what the deployed verifier hashes with the compiled
    system the R2–R4 stack reasons about. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Field.Field.
Require Import Garden.GroupHash.blake2b.
Require Import Garden.Orchard.vk.print.
Require Import Garden.Orchard.vk.parity.

Import ListNotations.
Local Open Scope Z_scope.

Module VkTranscriptRepr.

(** ** The hashing parameters *)

(** ASCII bytes of the 16-byte personalization ["Halo2-Verify-Key"]. *)
Definition personal : list Z :=
  [0x48; 0x61; 0x6c; 0x6f; 0x32; 0x2d; 0x56; 0x65;
   0x72; 0x69; 0x66; 0x79; 0x2d; 0x4b; 0x65; 0x79].

(** Personalized reference vector: BLAKE2b-512 of ["abc"] with the
    ["Halo2-Verify-Key"] personalization, against an independent
    implementation (Python [hashlib.blake2b], [digest_size=64],
    [person=b"Halo2-Verify-Key"]) — guards the parameter-block
    personalization wiring, which the zero-personalization vectors of
    [blake2b.v] do not reach. *)
Lemma blake2b_personal_abc_vector :
  Blake2b.blake2b 64 Blake2b.zero16 personal [0x61; 0x62; 0x63] = [
    0xD9; 0x78; 0x05; 0x99; 0x1D; 0x6B; 0x44; 0x90;
    0x4E; 0x1E; 0x1C; 0x93; 0xE3; 0xFC; 0xCE; 0xD4;
    0x63; 0xD2; 0xE4; 0x5E; 0xFC; 0x76; 0x5D; 0x72;
    0x13; 0x51; 0xD0; 0x36; 0x25; 0x81; 0xBD; 0xFC;
    0x7D; 0x1F; 0xC8; 0xB7; 0xB2; 0x0D; 0xE3; 0xB6;
    0x2C; 0x89; 0xE0; 0xE2; 0x03; 0x24; 0xF4; 0xF0;
    0xFB; 0xA9; 0xA7; 0xA8; 0x6C; 0x99; 0x8E; 0xC1;
    0x4C; 0x73; 0xA5; 0x80; 0x03; 0x2E; 0x18; 0xD5
  ].
Proof. vm_compute. reflexivity. Qed.

(** ** Linear byte view of a primitive string

    [VkPinnedPrint.pstring_bytes] resolves every index through
    [Z.of_nat] on a unary [nat], which is quadratic in the string length
    on the VM (the 285 KB compact rendering is out of reach);
    [bytes_from] threads a [Z] index instead, converting per access, and
    is proved pointwise equal.  The index arithmetic stays entirely in
    [Z], so the proof needs no machine-integer semantics (no
    [Uint63Axioms] in the assumption cone). *)

Fixpoint bytes_from (s : PrimString.string) (z : Z) (fuel : nat) :
    list Z :=
  match fuel with
  | O => []
  | S f =>
      Uint63.to_Z (PrimString.get s (Uint63.of_Z z))
        :: bytes_from s (z + 1) f
  end.

Definition pstring_bytes_lin (s : PrimString.string) : list Z :=
  bytes_from s 0 (Z.to_nat (Uint63.to_Z (PrimString.length s))).

Lemma bytes_from_map (s : PrimString.string) (fuel : nat) :
  forall k : nat,
  bytes_from s (Z.of_nat k) fuel
  = List.map (VkPinnedPrint.byte_at s) (List.seq k fuel).
Proof.
  induction fuel as [|f IH]; intros k;
    cbn [bytes_from List.seq List.map]; [reflexivity|].
  unfold VkPinnedPrint.byte_at at 1.
  f_equal.
  replace (Z.of_nat k + 1) with (Z.of_nat (S k))
    by (rewrite Nat2Z.inj_succ; reflexivity).
  apply IH.
Qed.

Lemma pstring_bytes_lin_spec (s : PrimString.string) :
  pstring_bytes_lin s = VkPinnedPrint.pstring_bytes s.
Proof.
  unfold pstring_bytes_lin, VkPinnedPrint.pstring_bytes.
  change 0 with (Z.of_nat 0).
  apply bytes_from_map.
Qed.

(** ** The hash input: [le64(len s) || s] *)

Definition transcript_input (s : PrimString.string) : list Z :=
  Blake2b.le_bytes_of_word (Uint63.to_Z (PrimString.length s))
    ++ pstring_bytes_lin s.

(** The concrete input: the compact rendering of the pinned description,
    behind its 8-byte little-endian length prefix. *)
Definition t2_input : list Z :=
  transcript_input VkPinnedPrint.vk_pinned_compact.

(** The input in the byte-parity track's terms: the pinned compact
    length ([vk/parity.v]) and the track's byte view. *)
Lemma t2_input_eq :
  t2_input
  = Blake2b.le_bytes_of_word 285134
      ++ VkPinnedPrint.vk_pinned_compact_bytes.
Proof.
  unfold t2_input, transcript_input.
  (* Syntactic delta on the byte-view constant: handing the two 285k-byte
     appends to unification instead diverges into a pointwise
     comparison. *)
  unfold VkPinnedPrint.vk_pinned_compact_bytes.
  rewrite pstring_bytes_lin_spec.
  rewrite VkPinnedParity.vk_pinned_compact_length.
  change (Uint63.to_Z 285134%uint63) with 285134.
  reflexivity.
Qed.

Lemma t2_input_length : Z.of_nat (List.length t2_input) = 285142.
Proof. vm_cast_no_check (@eq_refl Z 285142). Qed.

(** ** The block decomposition *)

Definition t2_blocks : list (list Z) := Blake2b.blocks_of t2_input.
Definition t2_tail1 : list (list Z) := List.skipn 557 t2_blocks.
Definition t2_tail2 : list (list Z) := List.skipn 557 t2_tail1.
Definition t2_tail3 : list (list Z) := List.skipn 557 t2_tail2.

Lemma t2_blocks_length : Z.of_nat (List.length t2_blocks) = 2228.
Proof. vm_cast_no_check (@eq_refl Z 2228). Qed.

(** Shard-range length certificates, in boolean form: the pipeline
    theorem consumes them through [Nat.ltb_lt].  (Deriving the same
    facts by [lia] from [t2_blocks_length] diverges at [Qed]: the
    micromega proof puts the lengths of the heavy block constants in
    checked positions.) *)

Lemma t2_len_1 : (557 <? List.length t2_blocks)%nat = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma t2_len_2 : (557 <? List.length t2_tail1)%nat = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma t2_len_3 : (557 <? List.length t2_tail2)%nat = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma t2_len_4 : (556 <? List.length t2_tail3)%nat = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** Definitional equations, established by syntactic delta ([unfold])
    only — [fold]/[change] on these constants hands the underlying block
    computation to the tactic-level reduction machinery, which diverges;
    the rewrites in the pipeline theorem consume these instead. *)

Lemma t2_blocks_def : Blake2b.blocks_of t2_input = t2_blocks.
Proof. unfold t2_blocks. reflexivity. Qed.

Lemma t2_tail1_def : List.skipn 557 t2_blocks = t2_tail1.
Proof. unfold t2_tail1. reflexivity. Qed.

Lemma t2_tail2_def : List.skipn 557 t2_tail1 = t2_tail2.
Proof. unfold t2_tail2. reflexivity. Qed.

Lemma t2_tail3_def : List.skipn 557 t2_tail2 = t2_tail3.
Proof. unfold t2_tail3. reflexivity. Qed.

(** ** Sharding the compression fold

    [compress_run] is the non-final spine of [Blake2b.compress_blocks]:
    every block is compressed with the running byte counter and the
    final flag off.  [compress_blocks_chunk] peels a prefix of [n]
    blocks off a [compress_blocks] run (any [n] below the block count,
    so the last block — the only one compressed with the final flag and
    the total length — stays in the remainder). *)

Fixpoint compress_run (h : list Z) (blocks : list (list Z))
    (consumed : Z) : list Z :=
  match blocks with
  | [] => h
  | b :: rest =>
      compress_run
        (Blake2b.compress h (Blake2b.words_of_le_bytes 16 b)
           (consumed + 128) false)
        rest (consumed + 128)
  end.

Lemma compress_blocks_chunk (n : nat) :
  forall (blocks : list (list Z)) (h : list Z) (c c' ll : Z),
  (n < List.length blocks)%nat ->
  c' = c + 128 * Z.of_nat n ->
  Blake2b.compress_blocks h blocks c ll
  = Blake2b.compress_blocks
      (compress_run h (List.firstn n blocks) c)
      (List.skipn n blocks) c' ll.
Proof.
  induction n as [|m IH]; intros blocks h c c' ll Hlen Hc'.
  - cbn [List.firstn List.skipn compress_run] in *.
    replace c' with c by (clear -Hc'; lia). reflexivity.
  - destruct blocks as [|b rest]; [cbn in Hlen; lia|].
    destruct rest as [|b2 rest2]; [cbn in Hlen; clear -Hlen; lia|].
    cbn [List.firstn List.skipn compress_run].
    change (Blake2b.compress_blocks h (b :: b2 :: rest2) c ll)
      with (Blake2b.compress_blocks
              (Blake2b.compress h (Blake2b.words_of_le_bytes 16 b)
                 (c + 128) false)
              (b2 :: rest2) (c + 128) ll).
    apply IH; cbn [List.length] in Hlen |- *; clear -Hlen Hc'; lia.
Qed.

Lemma compress_blocks_last (h b : list Z) (c ll : Z) :
  Blake2b.compress_blocks h [b] c ll
  = Blake2b.compress h (Blake2b.words_of_le_bytes 16 b) ll true.
Proof. reflexivity. Qed.

(** ** The pinned chain values

    The 8-word BLAKE2b state after 0, 557, 1114, 1671 and 2227 absorbed
    blocks (untrusted witness input, certified by the state-threading
    shard certificates below), and the zero-padded final block. *)

Definition t2_h0 : list Z :=
  [7640891576939301192; 13503953896175478587;
   4354685564936845355; 11912009170470909681;
   5840696475078001361; 11170449401992604703;
   8851249583119784995; 2487541928868464651].

Definition t2_h1 : list Z :=
  [13360698652600109994; 11524361007301886524;
   15268395667591395617; 2461412640907569568;
   8240577805748201606; 961151782254720452;
   13132790789083827481; 3589723089218227673].

Definition t2_h2 : list Z :=
  [2106878949330481245; 8007445327978137696;
   10138797075189936245; 17719856235636545505;
   17758369585437349397; 6579057016825164013;
   6514614214940964585; 4125798149247046816].

Definition t2_h3 : list Z :=
  [15373044837065519440; 911840872349035861;
   6744729768789059432; 14559340161821038963;
   9510424778460563487; 11624941931562733835;
   8755878182933753706; 1762945789985778675].

Definition t2_h4 : list Z :=
  [17744594930357705393; 14011888567529858938;
   9839058526026674889; 13708995408678266895;
   3676873481295735552; 10577513954919524068;
   3720147958025806575; 16677615118707860199].

Definition t2_last_block : list Z :=
  [52; 98; 101; 98; 102; 98; 98; 52; 52; 53; 51; 102; 44; 32; 48; 120;
   50; 55; 49; 49; 57; 102; 101; 99; 51; 55; 51; 54; 100; 57; 57; 97;
   98; 101; 101; 101; 102; 49; 97; 100; 55; 98; 56; 53; 55; 100; 98; 55;
   101; 55; 53; 52; 101; 48; 99; 49; 53; 56; 55; 56; 48; 101; 100; 51;
   100; 100; 48; 99; 100; 100; 52; 100; 99; 50; 52; 53; 51; 101; 49; 48;
   41; 93; 32; 125; 32; 125; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Lemma t2_h0_eq : Blake2b.init_h 64 0 Blake2b.zero16 personal = t2_h0.
Proof. vm_compute. reflexivity. Qed.

(** The four shard certificates: each threads the previous pinned state
    through one block range of the input stream. *)

Lemma t2_shard_1 :
  compress_run t2_h0 (List.firstn 557 t2_blocks) 0 = t2_h1.
Proof. vm_cast_no_check (@eq_refl (list Z) t2_h1). Qed.

Lemma t2_shard_2 :
  compress_run t2_h1 (List.firstn 557 t2_tail1) 71296 = t2_h2.
Proof. vm_cast_no_check (@eq_refl (list Z) t2_h2). Qed.

Lemma t2_shard_3 :
  compress_run t2_h2 (List.firstn 557 t2_tail2) 142592 = t2_h3.
Proof. vm_cast_no_check (@eq_refl (list Z) t2_h3). Qed.

Lemma t2_shard_4 :
  compress_run t2_h3 (List.firstn 556 t2_tail3) 213888 = t2_h4.
Proof. vm_cast_no_check (@eq_refl (list Z) t2_h4). Qed.

Lemma t2_last_block_eq : List.skipn 556 t2_tail3 = [t2_last_block].
Proof. vm_cast_no_check (@eq_refl (list (list Z)) [t2_last_block]). Qed.

(** ** The binding scalar *)

Definition transcript_repr : Z :=
  0x0bf7d48f59be0bbef33c558826dffee0032deccb9a6d2ea23daf3812d32d5271.

(** The final compression (final flag, total byte length 285,142) and
    the [from_uniform_bytes] reduction of the 64-byte digest. *)
Lemma t2_final :
  Blake2b.word_of_le_bytes
    (List.firstn (Z.to_nat 64)
       (List.concat
          (List.map Blake2b.le_bytes_of_word
             (Blake2b.compress t2_h4
                (Blake2b.words_of_le_bytes 16 t2_last_block)
                285142 true))))
    mod Primes.pallas_p
  = transcript_repr.
Proof. vm_cast_no_check (@eq_refl Z transcript_repr). Qed.

(** ** The pipeline theorem

    The exact [from_parts] computation over the compact rendering: the
    64-byte personalized BLAKE2b-512 digest of the length-prefixed
    string, read little-endian and reduced into the Pallas base field,
    is the pinned scalar. *)
Theorem transcript_repr_spec :
  Blake2b.word_of_le_bytes
    (Blake2b.blake2b 64 Blake2b.zero16 personal t2_input)
    mod Primes.pallas_p
  = transcript_repr.
Proof.
  unfold Blake2b.blake2b. cbv zeta.
  rewrite t2_input_length, t2_h0_eq, t2_blocks_def.
  rewrite (compress_blocks_chunk 557 t2_blocks t2_h0 0 71296 285142
             (proj1 (Nat.ltb_lt _ _) t2_len_1) eq_refl).
  rewrite t2_shard_1, t2_tail1_def.
  rewrite (compress_blocks_chunk 557 t2_tail1 t2_h1 71296 142592 285142
             (proj1 (Nat.ltb_lt _ _) t2_len_2) eq_refl).
  rewrite t2_shard_2, t2_tail2_def.
  rewrite (compress_blocks_chunk 557 t2_tail2 t2_h2 142592 213888 285142
             (proj1 (Nat.ltb_lt _ _) t2_len_3) eq_refl).
  rewrite t2_shard_3, t2_tail3_def.
  rewrite (compress_blocks_chunk 556 t2_tail3 t2_h3 213888 285056 285142
             (proj1 (Nat.ltb_lt _ _) t2_len_4) eq_refl).
  rewrite t2_shard_4, t2_last_block_eq, compress_blocks_last.
  exact t2_final.
Qed.

(** The same pipeline stated over the byte-parity track's byte view of
    the compact rendering, with the pinned length as the [le64] prefix
    value — the statement mirroring [plonk.rs] verbatim:
    [le64(s.len()) || s], hashed and reduced. *)
Theorem transcript_repr_of_compact :
  Blake2b.word_of_le_bytes
    (Blake2b.blake2b 64 Blake2b.zero16 personal
       (Blake2b.le_bytes_of_word 285134
          ++ VkPinnedPrint.vk_pinned_compact_bytes))
    mod Primes.pallas_p
  = transcript_repr.
Proof. rewrite <- t2_input_eq. exact transcript_repr_spec. Qed.

End VkTranscriptRepr.
