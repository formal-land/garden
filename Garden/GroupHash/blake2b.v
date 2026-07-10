(** * Executable BLAKE2b (RFC 7693) over [Z] bit operations

    Transcription of the BLAKE2b hash function as specified in RFC 7693 and
    instantiated by [blake2b_simd::Params] in the vendored [hashtocurve.rs]
    (digest length 64, no key, zero salt, zero personalization).  The
    parameter block (BLAKE2 specification, table 2) is assembled in full —
    digest length, key length, fanout 1, depth 1, zero leaf length / node
    offset / node depth / inner length, then salt and personalization — and
    XORed word-wise into the IV, so the zero-personalization variant used by
    [GroupHash^P] is one instantiation rather than a special case.

    Representation: 64-bit words are nonnegative [Z] values kept below
    [2^64] by explicit masking; messages, salts, personalizations, and
    digests are [list Z] of bytes (each in [0, 255]).  Word indices into the
    16-word working vector are [Z] via [znth]/[zupd].  No machine integers
    are involved anywhere ([PrimInt63] is excluded from this tree).

    The RFC 7693 appendix A test vector (BLAKE2b-512 of "abc") and two
    multi-block reference digests close the file as [vm_compute] checks. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.

Import ListNotations.

Global Open Scope Z_scope.

Module Blake2b.
  (** ** 64-bit word arithmetic over [Z] *)

  Definition mask64 : Z := 2 ^ 64 - 1.

  Definition add64 (a b : Z) : Z := Z.land (a + b) mask64.

  Definition add64_3 (a b c : Z) : Z := Z.land (a + b + c) mask64.

  Definition xor64 (a b : Z) : Z := Z.lxor a b.

  (** Rotation right by [n] bits, [0 < n < 64], inputs below [2^64]. *)
  Definition rotr64 (x n : Z) : Z :=
    Z.lor (Z.shiftr x n) (Z.land (Z.shiftl x (64 - n)) mask64).

  (** ** Byte/word conversions (RFC 7693 §2.1: words are little-endian) *)

  (** A word from its (at most 8) little-endian bytes. *)
  Definition word_of_le_bytes (bs : list Z) : Z :=
    List.fold_right (fun b acc => b + 256 * acc) 0 bs.

  (** The 8 little-endian bytes of a word. *)
  Definition le_bytes_of_word (w : Z) : list Z :=
    List.map (fun i => Z.land (Z.shiftr w (8 * Z.of_nat i)) 255)
      (List.seq 0 8).

  (** The first [n] little-endian words of a byte string (zero-padded on
      the right when the string is short). *)
  Definition words_of_le_bytes (n : nat) (bs : list Z) : list Z :=
    List.map
      (fun i => word_of_le_bytes (List.firstn 8 (List.skipn (8 * i) bs)))
      (List.seq 0 n).

  (** ** [Z]-indexed list access and update *)

  Definition znth (i : Z) (l : list Z) : Z := List.nth (Z.to_nat i) l 0.

  Definition zupd (l : list Z) (i : Z) (x : Z) : list Z :=
    List.firstn (Z.to_nat i) l ++ x :: List.skipn (S (Z.to_nat i)) l.

  (** ** Constants *)

  (** Initialization vector (RFC 7693 §2.6). *)
  Definition iv : list Z := [
    0x6A09E667F3BCC908; 0xBB67AE8584CAA73B;
    0x3C6EF372FE94F82B; 0xA54FF53A5F1D36F1;
    0x510E527FADE682D1; 0x9B05688C2B3E6C1F;
    0x1F83D9ABFB41BD6B; 0x5BE0CD19137E2179
  ].

  (** Message schedule [SIGMA] (RFC 7693 §2.7): the 12 rounds of BLAKE2b,
      rows 10 and 11 repeating rows 0 and 1. *)
  Definition sigma : list (list Z) := [
    [ 0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15];
    [14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3];
    [11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4];
    [ 7;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8];
    [ 9;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13];
    [ 2; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9];
    [12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11];
    [13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10];
    [ 6; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5];
    [10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13;  0];
    [ 0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15];
    [14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3]
  ].

  (** ** Mixing function G (RFC 7693 §3.1) *)

  Definition g_mix (v : list Z) (ia ib ic id : Z) (x y : Z) : list Z :=
    let a := znth ia v in
    let b := znth ib v in
    let c := znth ic v in
    let d := znth id v in
    let a := add64_3 a b x in
    let d := rotr64 (xor64 d a) 32 in
    let c := add64 c d in
    let b := rotr64 (xor64 b c) 24 in
    let a := add64_3 a b y in
    let d := rotr64 (xor64 d a) 16 in
    let c := add64 c d in
    let b := rotr64 (xor64 b c) 63 in
    zupd (zupd (zupd (zupd v ia a) ib b) ic c) id d.

  (** One round of the compression function: eight G applications, columns
      then diagonals, message words selected by the round's [sigma] row. *)
  Definition round (m : list Z) (v : list Z) (s : list Z) : list Z :=
    let mi := fun i => znth (znth i s) m in
    let v := g_mix v 0 4  8 12 (mi  0) (mi  1) in
    let v := g_mix v 1 5  9 13 (mi  2) (mi  3) in
    let v := g_mix v 2 6 10 14 (mi  4) (mi  5) in
    let v := g_mix v 3 7 11 15 (mi  6) (mi  7) in
    let v := g_mix v 0 5 10 15 (mi  8) (mi  9) in
    let v := g_mix v 1 6 11 12 (mi 10) (mi 11) in
    let v := g_mix v 2 7  8 13 (mi 12) (mi 13) in
    g_mix v 3 4  9 14 (mi 14) (mi 15).

  (** ** Compression function F (RFC 7693 §3.2)

      [h] is the 8-word chain value, [m] the 16-word message block, [t] the
      byte offset counter (an unbounded [Z] split into two 64-bit words),
      [last] the final-block flag. *)
  Definition compress (h m : list Z) (t : Z) (last : bool) : list Z :=
    let v := h ++ iv in
    let v := zupd v 12 (xor64 (znth 12 v) (Z.land t mask64)) in
    let v := zupd v 13 (xor64 (znth 13 v) (Z.shiftr t 64)) in
    let v := if last then zupd v 14 (xor64 (znth 14 v) mask64) else v in
    let v := List.fold_left (round m) sigma v in
    List.map
      (fun i =>
        let iz := Z.of_nat i in
        xor64 (znth iz h) (xor64 (znth iz v) (znth (iz + 8) v)))
      (List.seq 0 8).

  (** ** Parameter block and state initialization

      The 64-byte BLAKE2b parameter block (BLAKE2 specification, table 2):
      digest length, key length, fanout 1, depth 1, then 4 bytes leaf
      length, 8 bytes node offset, node depth, inner length, 14 reserved
      bytes (all zero for sequential hashing), 16 bytes salt, 16 bytes
      personalization.  [h0 = IV XOR LE-words(parameter block)]
      (RFC 7693 §2.5 gives the keyless-parameter shortcut
      [h0 ^= 0x0101kknn]; the full block is assembled here). *)
  Definition param_block (outlen keylen : Z) (salt personal : list Z) :
      list Z :=
    [outlen; keylen; 1; 1] ++ List.repeat 0 28%nat ++ salt ++ personal.

  Definition init_h (outlen keylen : Z) (salt personal : list Z) : list Z :=
    List.map (fun p => xor64 (fst p) (snd p))
      (List.combine iv
         (words_of_le_bytes 8 (param_block outlen keylen salt personal))).

  (** ** Message splitting (RFC 7693 §3.3)

      [dd = max(1, ceil(ll / bb))] blocks of [bb = 128] bytes, the last one
      zero-padded; an empty message still yields one all-zero block. *)
  Definition blocks_of (msg : list Z) : list (list Z) :=
    let ll := List.length msg in
    let dd := Nat.max 1 (Nat.div (ll + 127) 128) in
    let padded := msg ++ List.repeat 0 (dd * 128 - ll)%nat in
    List.map (fun i => List.firstn 128 (List.skipn (128 * i) padded))
      (List.seq 0 dd).

  (** The main loop of RFC 7693 §3.3: each non-final block is compressed
      with the count of bytes consumed so far ([(i + 1) * 128]), the final
      block with the total unpadded length [ll] and the final flag. *)
  Fixpoint compress_blocks (h : list Z) (blocks : list (list Z))
      (consumed ll : Z) : list Z :=
    match blocks with
    | [] => h
    | [b] => compress h (words_of_le_bytes 16 b) ll true
    | b :: rest =>
        compress_blocks
          (compress h (words_of_le_bytes 16 b) (consumed + 128) false)
          rest (consumed + 128) ll
    end.

  (** ** BLAKE2b

      Unkeyed BLAKE2b with digest length [outlen] (in [1, 64]), 16-byte
      [salt] and [personal], over the byte string [msg]; the digest is the
      first [outlen] bytes of the little-endian encoding of the final chain
      value. *)
  Definition blake2b (outlen : Z) (salt personal msg : list Z) : list Z :=
    let h0 := init_h outlen 0 salt personal in
    let h := compress_blocks h0 (blocks_of msg) 0 (Z.of_nat (List.length msg)) in
    List.firstn (Z.to_nat outlen) (List.concat (List.map le_bytes_of_word h)).

  Definition zero16 : list Z := List.repeat 0 16%nat.

  (** BLAKE2b-512 with zero salt and zero personalization — the
      [blake2b_simd::Params::new().hash_length(64).personal(&[0u8; 16])]
      instance of the vendored [hashtocurve.rs]. *)
  Definition blake2b512 (msg : list Z) : list Z :=
    blake2b 64 zero16 zero16 msg.
End Blake2b.

(** ** Test vectors

    RFC 7693 appendix A: BLAKE2b-512 of the three-byte ASCII string "abc"
    (a single partial block, exercising the final-block padding and the
    keyless parameter block). *)
Lemma blake2b512_abc_vector :
  Blake2b.blake2b512 [0x61; 0x62; 0x63] = [
    0xBA; 0x80; 0xA5; 0x3F; 0x98; 0x1C; 0x4D; 0x0D;
    0x6A; 0x27; 0x97; 0xB6; 0x9F; 0x12; 0xF6; 0xE9;
    0x4C; 0x21; 0x2F; 0x14; 0x68; 0x5A; 0xC4; 0xB7;
    0x4B; 0x12; 0xBB; 0x6F; 0xDB; 0xFF; 0xA2; 0xD1;
    0x7D; 0x87; 0xC5; 0x39; 0x2A; 0xAB; 0x79; 0x2D;
    0xC2; 0x52; 0xD5; 0xDE; 0x45; 0x33; 0xCC; 0x95;
    0x18; 0xD3; 0x8A; 0xA8; 0xDB; 0xF1; 0x92; 0x5A;
    0xB9; 0x23; 0x86; 0xED; 0xD4; 0x00; 0x99; 0x23
  ].
Proof. vm_compute. reflexivity. Qed.

(** BLAKE2b-512 of the 256-byte string [0, 1, ..., 255] — two full blocks,
    exercising the non-final compression path (which the "abc" vector does
    not reach) and an unpadded final block.  Reference digest computed with
    an independent implementation (Python [hashlib.blake2b],
    [digest_size=64], zero personalization). *)
Lemma blake2b512_two_blocks_vector :
  Blake2b.blake2b512 (List.map Z.of_nat (List.seq 0 256)) = [
    0x1E; 0xCC; 0x89; 0x6F; 0x34; 0xD3; 0xF9; 0xCA;
    0xC4; 0x84; 0xC7; 0x3F; 0x75; 0xF6; 0xA5; 0xFB;
    0x58; 0xEE; 0x67; 0x84; 0xBE; 0x41; 0xB3; 0x5F;
    0x46; 0x06; 0x7B; 0x9C; 0x65; 0xC6; 0x3A; 0x67;
    0x94; 0xD3; 0xD7; 0x44; 0x11; 0x2C; 0x65; 0x3F;
    0x73; 0xDD; 0x7D; 0xEB; 0x66; 0x66; 0x20; 0x4C;
    0x5A; 0x9B; 0xFA; 0x5B; 0x46; 0x08; 0x1F; 0xC1;
    0x0F; 0xDB; 0xE7; 0x88; 0x4F; 0xA5; 0xCB; 0xF8
  ].
Proof. vm_compute. reflexivity. Qed.

(** BLAKE2b-512 of the 129-byte string [0, 1, ..., 128] — one full block
    plus a one-byte zero-padded final block.  Reference digest from the same
    independent implementation. *)
Lemma blake2b512_padded_final_block_vector :
  Blake2b.blake2b512 (List.map Z.of_nat (List.seq 0 129)) = [
    0xF5; 0x97; 0x11; 0xD4; 0x4A; 0x03; 0x1D; 0x5F;
    0x97; 0xA9; 0x41; 0x3C; 0x06; 0x5D; 0x1E; 0x61;
    0x4C; 0x41; 0x7E; 0xDE; 0x99; 0x85; 0x90; 0x32;
    0x5F; 0x49; 0xBA; 0xD2; 0xFD; 0x44; 0x4D; 0x3E;
    0x44; 0x18; 0xBE; 0x19; 0xAE; 0xC4; 0xE1; 0x14;
    0x49; 0xAC; 0x1A; 0x57; 0x20; 0x78; 0x98; 0xBC;
    0x57; 0xD7; 0x6A; 0x1B; 0xCF; 0x35; 0x66; 0x29;
    0x2C; 0x20; 0xC6; 0x83; 0xA5; 0xC4; 0x64; 0x8F
  ].
Proof. vm_compute. reflexivity. Qed.
