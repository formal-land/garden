(** * T1: byte parity of the printed pinned description with the dump.

    The dump-parity certificate of the [transcript_repr] byte channel: the
    legacy/default printer instance ([vk/print.v]), run in pretty mode over
    the metadata-derived compiled Orchard system, setup computation, and
    deployed commitment-coordinate target, reproduces
    [orchard/src/circuit_data/circuit_description_post_nu6_3] — the
    [format!("{:#?}\n", vk.pinned())] Debug dump the orchard test suite
    asserts against the Post-NU6.3 verifying key
    ([orchard/src/circuit.rs], the pinned-description test) —
    byte-for-byte, all 1,285,701 bytes.

    This certifies as bytes produced from the model's compiled system:
    the 193 compiled gate polynomials with their selector-indicator
    factors and keygen query indices, the query tables, the permutation
    columns, the lookup arguments, the constants column, the domain
    constants, and the setup/domain values.  This legacy theorem uses the
    deployed 44 commitment pairs; [OrchardVkFullAbstract] transports T1 to an
    explicit generated coordinate view and separately proves that every view
    entry denotes the corresponding mathematical [commit_lagrange] result.

    The compact rendering [VkPinnedPrint.vk_pinned_compact] of the same
    printer is the string [s] whose BLAKE2b-512 hash (personalized
    ["Halo2-Verify-Key"], over [le64(len s) || s]) is the verifying key's
    Fiat–Shamir binding scalar [transcript_repr]
    ([halo2_proofs/src/plonk.rs], [from_parts]); its pinned length below
    is the value of the [le64] prefix.  The T2 certificate computes that
    hash over [vk_pinned_compact]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Orchard.vk.print.
Require Import Garden.Orchard.vk.bytes.

Module VkPinnedParity.

(** The imported dump has the documented byte count. *)
Lemma dump_length :
  PrimString.length VkPinnedBytes.dump = 1285701%uint63.
Proof. vm_cast_no_check (@eq_refl PrimInt63.int 1285701%uint63). Qed.

(** T1: the pretty rendering equals the dump byte-for-byte. *)
Lemma vk_pinned_dump_parity :
  VkPinnedPrint.vk_pretty_with
    VkPinnedPrint.pinned_commitment_coordinates = VkPinnedBytes.dump.
Proof.
  vm_cast_no_check (@eq_refl PrimString.string VkPinnedBytes.dump).
Qed.

Lemma vk_pinned_pretty_length :
  PrimString.length
    (VkPinnedPrint.vk_pretty_with
      VkPinnedPrint.pinned_commitment_coordinates) = 1285701%uint63.
Proof. now rewrite vk_pinned_dump_parity, dump_length. Qed.

(** The compact rendering's byte count: the value of the [le64] length
    prefix of the [transcript_repr] hash input ([285134 = 0x459ce]). *)
Lemma vk_pinned_compact_length :
  PrimString.length
    (VkPinnedPrint.vk_compact_with
      VkPinnedPrint.pinned_commitment_coordinates) = 285134%uint63.
Proof. vm_cast_no_check (@eq_refl PrimInt63.int 285134%uint63). Qed.

End VkPinnedParity.
