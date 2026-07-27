(** * Provenance of the six Orchard fixed-base generators: [GroupHash^P]

    In-kernel derivation of the six generator points of
    [Orchard/Pallas/Generators.v] from the protocol's own algorithm
    (§5.4.9.8): for each base, [GroupHash^P(D, M)] — BLAKE2b-512 XMD
    [hash_to_field], simplified SWU onto iso-Pallas, iso-curve addition,
    [iso_map] — recomputed by [vm_compute] and equated with the hard-coded
    literal.  The [(D, M)] pairs are the protocol's (§5.4.9.8; the Rust
    [orchard] crate's [src/constants/fixed_bases/<base>.rs]):

    - SpendAuthG   : [("z.cash:Orchard", "G")];
    - NullifierK   : [("z.cash:Orchard", "K")];
    - ValueCommitV : [("z.cash:Orchard-cv", "v")];
    - ValueCommitR : [("z.cash:Orchard-cv", "r")];
    - NoteCommitR  : [("z.cash:Orchard-NoteCommit-r", "")];
    - CommitIvkR   : [("z.cash:Orchard-CommitIvk-r", "")].

    The two [sqrt_ratio] outputs per point (an is-square flag and a root per
    field element [u_i]) are pasted untrusted witnesses, generated offline by
    [scripts/generate_grouphash_witnesses.py]; the checker validates each
    against its defining equation ([GroupHash.witnesses_ok] — one squaring
    and one multiplication per root) and recomputes every other stage
    in-kernel.  A valid witness pins the flag ([λ_P] is a nonsquare) and the
    SSWU sign normalization cancels the root's sign, so the checked equality
    pins the literal to the [GroupHash^P] output itself. *)

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
Require Import Garden.Orchard.Pallas.Generators.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

(** Entry shape: [(D, M, was_square0, root0, was_square1, root1, G)] —
    the domain prefix and message as byte strings, the two pasted
    [sqrt_ratio] witnesses, and the generator literal the recomputation
    must equal. *)
Lemma generators_group_hash_provenance :
  List.forallb
    (fun e : list Z * list Z * bool * Z * bool * Z * Weierstrass.point =>
      let '(d, m, was_square0, root0, was_square1, root1, g) := e in
      GroupHash.witnesses_ok d m was_square0 root0 was_square1 root1
        && GroupHash.point_eqb
             (GroupHash.group_hash_with_witness
               d m was_square0 root0 was_square1 root1)
             g)
    [
      (Xmd.bytes_of_string "z.cash:Orchard"%string,
       Xmd.bytes_of_string "G"%string,
       false,
       28930527611025010130380510039483840926278800525625834671023236096920970490654,
       true,
       25821929588847840039809614186438312339968518917185384557901301675465854960268,
       PallasGenerators.spend_auth_g_G);
      (Xmd.bytes_of_string "z.cash:Orchard"%string,
       Xmd.bytes_of_string "K"%string,
       false,
       4139314591300874489334160860887621184825787909530261995844643140427075029816,
       true,
       23871576267638524725211775572522322984851263488121880424601125244589078011299,
       PallasGenerators.nullifier_k_G);
      (Xmd.bytes_of_string "z.cash:Orchard-cv"%string,
       Xmd.bytes_of_string "v"%string,
       true,
       27687986118348010847522672158184180656955817220362140129643300060278159121029,
       false,
       6708269562272521306908952264383898984633581609966960253366035763990655571822,
       PallasGenerators.value_commit_v_G);
      (Xmd.bytes_of_string "z.cash:Orchard-cv"%string,
       Xmd.bytes_of_string "r"%string,
       false,
       7356511351360313657028186374490472373792083569423624494189798936609167415900,
       true,
       6428272994913216369379591956869513944369764168648661155759484012616303486680,
       PallasGenerators.value_commit_r_G);
      (Xmd.bytes_of_string "z.cash:Orchard-NoteCommit-r"%string,
       Xmd.bytes_of_string ""%string,
       true,
       23266501470526781486843442040761371538463691466105597210650554385598516814006,
       false,
       12906623150027353479974964163993467415891717989093051216374890730223182139651,
       PallasGenerators.note_commit_r_G);
      (Xmd.bytes_of_string "z.cash:Orchard-CommitIvk-r"%string,
       Xmd.bytes_of_string ""%string,
       true,
       22152415638538233668644112009418570625118649992775845133747092321120018651852,
       true,
       19127444693398468635382184103647782123870842013405584521463218782155292610376,
       PallasGenerators.commit_ivk_r_G)
    ]
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
