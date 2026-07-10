(** * Provenance of the three Sinsemilla [Q] points: [GroupHash^P]

    In-kernel derivation of the three Sinsemilla domain initial points
    [Q(D) = GroupHash^P("z.cash:SinsemillaQ", D)] (protocol §5.4.1.9) from
    the pipeline of [GroupHash/group_hash.v], each equated with its
    hard-coded circuit literal:

    - [D = "z.cash:Orchard-MerkleCRH"]     : [merkle_q_x/y]
      ([Orchard/circuit.v]);
    - [D = "z.cash:Orchard-NoteCommit-M"]  : [q_note_commit_m_x/y]
      ([Orchard/circuit/note_commit.v]);
    - [D = "z.cash:Orchard-CommitIvk-M"]   : [q_commit_ivk_m_x/y]
      ([Orchard/circuit/commit_ivk.v]).

    The two [sqrt_ratio] outputs per point are pasted untrusted witnesses
    from [scripts/generate_grouphash_witnesses.py], validated by
    [GroupHash.witnesses_ok] (one squaring and one multiplication per root);
    the BLAKE2b-512 XMD expansion, the SSWU field arithmetic, the iso-curve
    addition, and [iso_map] are recomputed by the checker's [vm_compute].
    See [Orchard/Pallas/generators_provenance.v] for the same argument over
    the fixed-base generators. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu.
Require Import Garden.GroupHash.group_hash.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.commit_ivk.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

(** Entry shape: [(D, M, was_square0, root0, was_square1, root1, Q)] — the
    domain prefix and message as byte strings, the two pasted [sqrt_ratio]
    witnesses, and the circuit's [Q] literal the recomputation must equal. *)
Lemma q_points_group_hash_provenance :
  List.forallb
    (fun e : list Z * list Z * bool * Z * bool * Z * Weierstrass.point =>
      let '(d, m, was_square0, root0, was_square1, root1, q) := e in
      GroupHash.witnesses_ok d m was_square0 root0 was_square1 root1
        && GroupHash.point_eqb
             (GroupHash.group_hash_with_witness
               d m was_square0 root0 was_square1 root1)
             q)
    [
      (Xmd.bytes_of_string "z.cash:SinsemillaQ"%string,
       Xmd.bytes_of_string "z.cash:Orchard-MerkleCRH"%string,
       false,
       2601917221567830630546498692840488533537790926201898056940912335405142486587,
       true,
       12829028803589176055869835248573272663684923464918941439067393357665326346249,
       Weierstrass.Affine
         Garden.Orchard.circuit.merkle_q_x
         Garden.Orchard.circuit.merkle_q_y);
      (Xmd.bytes_of_string "z.cash:SinsemillaQ"%string,
       Xmd.bytes_of_string "z.cash:Orchard-NoteCommit-M"%string,
       false,
       13233271398902967993639137423677833712268889974828274412747606427279951495391,
       false,
       26620840035719814278614604853784296647684743341974475772669267733021933208497,
       Weierstrass.Affine
         Garden.Orchard.circuit.note_commit.q_note_commit_m_x
         Garden.Orchard.circuit.note_commit.q_note_commit_m_y);
      (Xmd.bytes_of_string "z.cash:SinsemillaQ"%string,
       Xmd.bytes_of_string "z.cash:Orchard-CommitIvk-M"%string,
       false,
       11133061458502653584747425251575196919858629556440447049751196413227281561601,
       false,
       28223877556016708106630456743213936153426364840177461767650578657393798994893,
       Weierstrass.Affine
         Garden.Orchard.circuit.commit_ivk.q_commit_ivk_m_x
         Garden.Orchard.circuit.commit_ivk.q_commit_ivk_m_y)
    ]
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
