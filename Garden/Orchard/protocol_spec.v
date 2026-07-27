Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * The Orchard action specification

    The primary specification of the Zcash Orchard action circuit's public
    outputs, against §4.18.4 'Action Statement (Orchard)' of the Zcash
    protocol specification ([docs/protocol.pdf]); per-definition comments
    cite the section defining each primitive.

    Two layers share this file:

    - [OrchardSpec] — the action-level types ([Params], [ActionInputs],
      [ActionOutputs]) and the protocol-faithful shared components
      (Sinsemilla message packings, the Merkle-root anchor).
    - [OrchardProtocolSpec] — the specification of record: the §4.18.4
      output functions with every fixed-base multiplication written as the
      group multiple [Pallas.mul k G] of the base's affine generator (the
      six real-coordinate [PallasGenerators] points), and no witness record.

    The *circuit-structured* counterparts of the output functions — fixed-base
    multiplications as folds over the circuit's windowed Lagrange tables,
    threaded with per-window square-root witnesses — are proof-internal (the
    intermediate vocabulary the per-output bridge proofs land on) and live in
    [Garden/Orchard/circuit_proof/internal_spec.v] ([OrchardCircuitSpec]).

    The two layers are proved equal on protocol-typed inputs in
    [Garden/Orchard/circuit_proof/protocol_equiv.v]
    ([OrchardProtocolEquiv.output_protocol_eq], via the per-base bridges of
    [circuit_proof/protocol_mul/]); the theorem surface consuming them is
    [Garden/Orchard/circuit_proof/main.v]
    ([OrchardAction.satisfies_specification] and the derived
    [OrchardAction.deterministic]).

    Constants.  The protocol side is table-free: [Params] holds only the
    three affine Sinsemilla domain points, instantiated by a genuine
    [Definition] from the circuit constants
    ([Orchard/circuit_proof/inputs.v], [orchard_circuit_params]), nothing
    abstract left to quantify over.  The windowed Lagrange fixed-base tables
    are circuit representation detail and live in the proof-internal
    [OrchardCircuitSpec.Params] ([circuit_proof/internal_spec.v]).  Relating
    the domain points and generator coordinates to their §5.4.9.8 group-hash
    derivations is the constants-provenance track. *)

Module OrchardSpec.
  (** ** Action-level types and protocol-faithful shared components *)

  (** The public, fixed parameters of the Orchard action: the three affine
      Sinsemilla domain points.  The fixed-base generators appear on the
      protocol side as the [PallasGenerators] affine points directly; their
      windowed Lagrange table representations are circuit detail, carried by
      [OrchardCircuitSpec.Params] ([circuit_proof/internal_spec.v]) and
      related to the generators by the per-base certificates. *)
  Record Params : Set := {
    note_commit_q : Point.t;              (* NoteCommit Sinsemilla domain point *)
    commit_ivk_q : Point.t;               (* CommitIvk Sinsemilla domain point *)
    merkle_crh_q : Point.t;               (* MerkleCRH Sinsemilla domain point *)
  }.

  Definition point_y (P : Point.t) : Z := P.(Point.y).

  (** Note-commitment Sinsemilla message: the diversified base, the transmission
      key, the value, [ρ] and [ψ] packed little-endian into 10-bit words.  Each
      point contributes its full 256-bit compressed encoding — the x-coordinate
      plus the y-parity sign bit [y mod 2] at bits 255/511 (the circuit's
      [b_2]/[d_1] witness cells) — then the 64-bit value and the 255-bit [ρ]
      and [ψ]: 1086 bits, hashed as 109 ten-bit words (the packing of
      [NoteCommitMessagePieces.note_commit_packed]).

      Protocol: §5.4.8.4 'Sinsemilla commitments', the [NoteCommit^Orchard]
      message [g⋆_d || pk⋆_d || I2LEBSP_64(v) || I2LEBSP_255(ρ) ||
      I2LEBSP_255(ψ)]; each 256-bit compressed point encoding [P⋆ = repr_P(P)]
      is the 255-bit x-coordinate with the [ỹ] parity bit at bit 255
      (§5.4.9.6 'Pallas and Vesta'). *)
  Definition note_commit_message
      (g_d pk_d : Point.t) (v rho psi : Z) : list Z :=
    SinsemillaSpec.words_le 109
      (EccSpec.extract_x g_d
        + (g_d.(Point.y) mod 2) * 2 ^ 255
        + EccSpec.extract_x pk_d * 2 ^ 256
        + (pk_d.(Point.y) mod 2) * 2 ^ 511
        + v * 2 ^ 512
        + rho * 2 ^ 576
        + psi * 2 ^ 831).

  (** [CommitIvk] message: [ak] then [nk], packed into 10-bit words.

      Protocol: §5.4.8.4, the [Commit^ivk] message
      [I2LEBSP_255(ak) || I2LEBSP_255(nk)] — [nk] at bit 255, 510 bits, 51
      ten-bit words.  This matches the circuit's piece decomposition
      ([circuit/commit_ivk.v]: [ak = a + b_0·2²⁵⁰ + b_1·2²⁵⁴] and
      [nk = b_2 + c·2⁵ + d_0·2²⁴⁵ + d_1·2²⁵⁴] hashed as
      [a || b || c || d]), where [b = b_0 + b_1·2⁴ + b_2·2⁵] places the low
      bits of [nk] directly after bit 254 of [ak]. *)
  Definition commit_ivk_message (ak nk : Z) : list Z :=
    SinsemillaSpec.words_le 51 (ak + nk * 2 ^ 255).

  (** [anchor]: the Merkle root reached from the leaf along the path.
      Protocol-faithful as is (no fixed-base multiplication): shared verbatim
      by the circuit-structured and protocol layers.

      Protocol: §4.18.4 'Merkle path validity' via §4.9 'Merkle Path
      Validity' — the fold of [MerkleCRH^Orchard] (§5.4.1.3) from the leaf
      [Extract_P(cm_old)] up the 32-layer authentication path to the root
      [rt^Orchard]. *)
  Definition anchor
      (prm : Params) (leaf : Z) (path : list (Z * Z * bool)) : Z :=
    SinsemillaSpec.merkle_root (merkle_crh_q prm) leaf path.

  (** [ActionInputs] mirrors the auxiliary-input bundle of §4.18.4 (path,
      pos, g_d_old, pk_d_old, v_old, ρ_old, ψ_old, cm_old, α, ak_P, nk,
      rivk, g_d_new, pk_d_new, v_new, ψ_new, rcm_new, rcv), circuit-typed:
      points as affine coordinate records, the Merkle position as per-layer
      swap bits, scalars as the values reconstructed from their witnessed
      window decompositions, and the net value as the circuit's
      magnitude/sign pair for [v_old − v_new].  [rcm_old] does not appear:
      it feeds only the old-note commitment integrity condition, which
      constrains inputs rather than any public output. *)
  Record ActionInputs : Set := {
    (* old note and spend *)
    in_ak : Point.t;
    in_nk : Z;
    in_rho_old : Z;
    in_psi_old : Z;
    in_cm_old : Point.t;
    in_g_d_old : Point.t;
    in_pk_d_old : Point.t;
    in_v_old : Z;
    in_rivk : Z;
    in_alpha : Z;
    in_anchor_public : Z;  (* public anchor row; the spend's anchor on a dummy note *)
    (* value balance *)
    in_rcv : Z;
    in_magnitude : Z;
    in_sign : Z;
    (* merkle path *)
    in_leaf : Z;
    in_path : list (Z * Z * bool);
    (* new note *)
    in_g_d_new : Point.t;
    in_pk_d_new : Point.t;
    in_v_new : Z;
    in_psi_new : Z;
    in_rcm_new : Z;
  }.

  Record ActionOutputs : Set := {
    out_anchor : Z;
    out_cv_net : Point.t;
    out_nf_old : Z;
    out_rk : Point.t;
    out_cmx : Z;
  }.

End OrchardSpec.

(** * Protocol-aligned output functions — the specification of record

    The §4.18.4 output functions with every fixed-base scalar multiplication
    written as it appears in the protocol: the group multiple [Pallas.mul k G]
    of the affine generator point, instead of the circuit-structured fold
    over the windowed Lagrange table.  The generators are the six
    [PallasGenerators] points, which carry the real Zcash coordinates
    ([Garden/Orchard/Pallas/Generators.v]).

    Everything else is shared with [OrchardSpec] on purpose:

    - the Sinsemilla hash-to-point fold is the protocol's own definition of
      [SinsemillaHashToPoint] (§5.4.1.9), so [SinsemillaSpec] is used as is;
    - [EccSpec.point_add] is the affine-coordinate Pallas group law with the
      [(0, 0)] identity sentinel, related to [Pallas.add] by
      [PallasModel.repr];
    - the Sinsemilla domain points ([note_commit_q], [commit_ivk_q],
      [merkle_crh_q]) are still taken from [OrchardSpec.Params]: relating
      those concrete constants to their §5.4.9.8 group-hash derivations is
      the constants-provenance track, not the table-fold-vs-group-multiple
      distance this module closes.

    The equivalence with [OrchardSpec]'s circuit-structured functions at the
    concrete circuit tables is proved in
    [Garden/Orchard/circuit_proof/protocol_equiv.v]. *)

Module OrchardProtocolSpec.
  (** ** Fixed-base scalar multiples, one per Orchard base

      Each is [repr ([k] G)] for the base's affine generator: the protocol's
      scalar multiplication, landed in the chip's affine representation.
      Protocol bases: 𝒢^Orchard (§5.4.7.1), 𝒱^Orchard/ℛ^Orchard (§5.4.8.3),
      𝒦^Orchard (§4.16), and the [GroupHash^P(D || "-r", "")] blinding bases
      of [NoteCommit^Orchard]/[Commit^ivk] (§5.4.8.4). *)

  Definition mul_spend_auth_g (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.spend_auth_g_G).
  Definition mul_value_commit_v (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.value_commit_v_G).
  Definition mul_value_commit_r (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.value_commit_r_G).
  Definition mul_nullifier_k (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.nullifier_k_G).
  Definition mul_note_commit_r (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.note_commit_r_G).
  Definition mul_commit_ivk_r (k : Z) : Point.t :=
    PallasModel.repr (Pallas.mul k PallasGenerators.commit_ivk_r_G).

  (** ** Output functions, §4.18.4 clause by clause *)

  (** The signed net value committed by an action: [±magnitude] decoded from
      the circuit's sign field element ([1] or [pallas_p − 1] for [−1]).
      Protocol: the [v_old − v_new] argument of 'Value commitment integrity',
      ranging over [{−2⁶⁴+1 .. 2⁶⁴−1}] (§4.18.4 notes). *)
  Definition signed_net_value (magnitude sign : Z) : Z :=
    if sign =? 1 then magnitude else - magnitude.

  (** §4.18.4 'Spend authority': [rk = ak_P + [α] 𝒢^Orchard]
      ([SpendAuthSig^Orchard.RandomizePublic], §5.4.7.1). *)
  Definition spend_auth_randomize (ak : Point.t) (alpha : Z) : Point.t :=
    EccSpec.point_add ak (mul_spend_auth_g alpha).

  (** §4.18.4 'Value commitment integrity':
      [cv_net = ValueCommit^Orchard_rcv(v) = [v] 𝒱^Orchard + [rcv] ℛ^Orchard]
      (§5.4.8.3), [v] signed. *)
  Definition value_commit (v rcv : Z) : Point.t :=
    PallasModel.repr
      (Pallas.add
        (Pallas.mul v PallasGenerators.value_commit_v_G)
        (Pallas.mul rcv PallasGenerators.value_commit_r_G)).

  (** §4.18.4 'Nullifier integrity': [nf = DeriveNullifier_nk(ρ, ψ, cm) =
      Extract_P([(PRF^nfOrchard_nk(ρ) + ψ) mod q_P] 𝒦^Orchard + cm)]
      (§4.16; the PRF is [PoseidonHash(nk, ρ)], §5.4.2). *)
  Definition nullifier (nk rho psi : Z) (cm : Point.t) : Z :=
    let scalar := Poseidon.poseidon_hash2 nk rho +F psi in
    EccSpec.extract_x
      (EccSpec.point_add (mul_nullifier_k scalar) cm).

  (** §5.4.8.4 [NoteCommit^Orchard]: Sinsemilla hash-to-point of the 1086-bit
      note message, blinded by [[rcm] ℛ] with the group-multiple blinding
      term. *)
  Definition note_commit
      (prm : OrchardSpec.Params) (g_d pk_d : Point.t) (v rho psi rcm : Z)
      : Point.t :=
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q prm)
        (OrchardSpec.note_commit_message g_d pk_d v rho psi))
      (mul_note_commit_r rcm).

  (** §5.4.8.4 [Commit^ivk]: the short Sinsemilla commitment of
      [I2LEBSP_255(ak) || I2LEBSP_255(nk)], consumed by §4.18.4 'Diversified
      address integrity'.  (Not a public output.) *)
  Definition commit_ivk
      (prm : OrchardSpec.Params) (ak nk rivk : Z) : Z :=
    EccSpec.extract_x
      (EccSpec.point_add
        (SinsemillaSpec.sinsemilla_hash_to_point
          (OrchardSpec.commit_ivk_q prm)
          (OrchardSpec.commit_ivk_message ak nk))
        (mul_commit_ivk_r rivk)).

  (** §4.18.4 'New note commitment integrity', honest branch:
      [cm_x = Extract_P(NoteCommit^Orchard_rcm_new(…))] with
      [ρ_new = nf_old]. *)
  Definition OrchardCmx
      (prm : OrchardSpec.Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) : Z :=
    EccSpec.extract_x
      (note_commit prm g_d_new pk_d_new v_new rho_new psi_new rcm_new).

  (** ** The action-level protocol spec

      [inputs -> outputs], no square-root witness record: the witness has no
      protocol counterpart, which is the point of the alignment.  The anchor
      clause is [OrchardSpec.anchor] verbatim (it contains no fixed-base
      multiplication), including the §4.18.4 dummy-spend disjunction. *)
  Definition orchard_action_spec
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs)
      : OrchardSpec.ActionOutputs :=
    let nf_old :=
      nullifier
        (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp)
        (OrchardSpec.in_psi_old inp) (OrchardSpec.in_cm_old inp) in
    let rho_new := nf_old in {|
      OrchardSpec.out_anchor :=
        if OrchardSpec.in_v_old inp =? 0
        then OrchardSpec.in_anchor_public inp
        else OrchardSpec.anchor prm (OrchardSpec.in_leaf inp)
          (OrchardSpec.in_path inp);
      OrchardSpec.out_cv_net :=
        value_commit
          (signed_net_value
            (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp))
          (OrchardSpec.in_rcv inp);
      OrchardSpec.out_nf_old := nf_old;
      OrchardSpec.out_rk :=
        spend_auth_randomize
          (OrchardSpec.in_ak inp) (OrchardSpec.in_alpha inp);
      OrchardSpec.out_cmx :=
        OrchardCmx prm
          (OrchardSpec.in_g_d_new inp) (OrchardSpec.in_pk_d_new inp)
          (OrchardSpec.in_v_new inp) rho_new
          (OrchardSpec.in_psi_new inp) (OrchardSpec.in_rcm_new inp);
    |}.
End OrchardProtocolSpec.
