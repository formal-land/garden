(** * [expand_message_xmd] over BLAKE2b-512 and [hash_to_field] for [GroupHash^P]

    Transcription of [hash_to_field] from the vendored [hashtocurve.rs]
    (crate [pasta_curves]): the XMD expansion of [msg] under the domain
    separation tag [DST = domain_prefix || "-" || curve_id ||
    "_XMD:BLAKE2b_SSWU_RO_"] into 128 uniform bytes, and their reduction to
    two elements of the Pallas base field [F_{q_P}] (protocol §5.4.9.8,
    [hash_to_field] of the hash-to-curve draft with [H = BLAKE2b-512],
    [b_in_bytes = 64], [r_in_bytes = 128], [count = 2], [L = 64], so
    [len_in_bytes = 128] and [ell = 2]).

    Strings are ASCII [String.string]; [bytes_of_string] turns them into
    the [list Z] byte strings the hash consumes.  All DSTs used by
    [GroupHash^P] satisfy the length bounds asserted by the Rust source
    ([|domain_prefix| < 256] and [|DST| = 22 + |curve_id| +
    |domain_prefix| < 256]), under which the single length byte of [DST']
    matches [I2OSP(|DST|, 1)]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import Garden.GroupHash.blake2b.
Require Garden.Field.Field.

Import ListNotations.

Global Open Scope Z_scope.

Module Xmd.
  (** ASCII string to byte string. *)
  Fixpoint bytes_of_string (s : String.string) : list Z :=
    match s with
    | EmptyString => []
    | String c rest => Z.of_N (Ascii.N_of_ascii c) :: bytes_of_string rest
    end.

  (** Pointwise XOR of two byte strings of equal length. *)
  Definition xor_bytes (xs ys : list Z) : list Z :=
    List.map (fun p => Z.lxor (fst p) (snd p)) (List.combine xs ys).

  (** [expand_message_xmd] with [H = BLAKE2b-512] and [len_in_bytes = 128],
      block for block as in [hash_to_field] of [hashtocurve.rs]:

      - [DST' = DST || I2OSP(|DST|, 1)];
      - [b_0 = H([0]^128 || msg || I2OSP(128, 2) || I2OSP(0, 1) || DST')]
        (the Rust [update(&[0, 128, 0])]);
      - [b_1 = H(b_0 || I2OSP(1, 1) || DST')];
      - [b_2 = H((b_0 XOR b_1) || I2OSP(2, 1) || DST')];
      - output [b_1 || b_2]. *)
  Definition expand_message_xmd (msg dst : list Z) : list Z :=
    let dst_prime := dst ++ [Z.of_nat (List.length dst)] in
    let b_0 :=
      Blake2b.blake2b512
        (List.repeat 0 128 ++ msg ++ [0; 128; 0] ++ dst_prime) in
    let b_1 := Blake2b.blake2b512 (b_0 ++ [1] ++ dst_prime) in
    let b_2 :=
      Blake2b.blake2b512 (xor_bytes b_0 b_1 ++ [2] ++ dst_prime) in
    b_1 ++ b_2.

  (** Big-endian integer value of a byte string ([OS2IP]). *)
  Definition os2ip (bs : list Z) : Z :=
    List.fold_left (fun acc b => 256 * acc + b) bs 0.

  (** Field element from one 64-byte digest: [OS2IP(digest) mod p].

      Endianness reconciliation.  [hashtocurve.rs] copies each digest into
      [little], reverses it ([little.reverse()]), and calls
      [F::from_uniform_bytes(&little)]; the pasta [Fp] instance
      ([fields/fp.rs]) interprets its input as a little-endian 512-bit
      integer ([u64::from_le_bytes] limbs into [from_u512]).  Reversing a
      byte string and reading it little-endian equals reading the original
      string big-endian, so the Rust computes exactly [OS2IP(digest) mod p]
      — the big-endian interpretation the hash-to-curve draft and protocol
      §5.4.9.8 prescribe.  The big-endian fold below is therefore both what
      the specification states and what the hard-coded constants require;
      the little-endian assembly inside the Rust is an artifact of the
      digest reversal, not a deviation. *)
  Definition field_from_digest (p : Z) (digest : list Z) : Z :=
    os2ip digest mod p.

  (** [DST = domain_prefix || "-" || curve_id || "_XMD:BLAKE2b_SSWU_RO_"]. *)
  Definition dst (curve_id domain_prefix : list Z) : list Z :=
    domain_prefix ++ bytes_of_string "-"%string ++ curve_id
      ++ bytes_of_string "_XMD:BLAKE2b_SSWU_RO_"%string.

  (** [hash_to_field]: two field elements [u_0] (from [b_1]) and [u_1]
      (from [b_2]). *)
  Definition hash_to_field (p : Z) (curve_id domain_prefix msg : list Z) :
      Z * Z :=
    let uniform := expand_message_xmd msg (dst curve_id domain_prefix) in
    (field_from_digest p (List.firstn 64 uniform),
     field_from_digest p (List.skipn 64 uniform)).

  (** The Pallas instantiation: [curve_id = "pallas"], reduction modulo the
      base field order [q_P]. *)
  Definition pallas_p : Z := Garden.Field.Field.Primes.pallas_p.

  Definition curve_id_pallas : list Z := bytes_of_string "pallas"%string.

  Definition hash_to_field_pallas (domain_prefix msg : list Z) : Z * Z :=
    hash_to_field pallas_p curve_id_pallas domain_prefix msg.
End Xmd.

(** ** Reference vector

    [hash_to_field] for [curve_id = "pallas"], [domain_prefix =
    "z.cash:test"], message "Trans rights now!" — the hash-to-curve test
    input of the [pasta_curves] crate.  The expected pair was computed with
    an independent BLAKE2b implementation (Python [hashlib.blake2b])
    driving the same expansion and big-endian reduction.  The [b_0] input
    spans three BLAKE2b blocks, so the check also exercises the multi-block
    chaining of [Blake2b.blake2b512] beyond its in-file vectors. *)
Lemma hash_to_field_pallas_reference_vector :
  Xmd.hash_to_field_pallas
    (Xmd.bytes_of_string "z.cash:test"%string)
    (Xmd.bytes_of_string "Trans rights now!"%string)
  = (12603446364597782259514992439564338152701664187668818874396107041689701997167,
     6260292304014803632744546009239917598554248142901528624200490746891590624431).
Proof. vm_compute. reflexivity. Qed.
