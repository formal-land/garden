Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Circuit-structured output functions (proof-internal)

    The intermediate spec layer the per-output bridge proofs land on: the
    same §4.18.4 output conditions as [OrchardProtocolSpec]
    ([Orchard/protocol_spec.v], the specification of record), but with every
    fixed-base scalar multiplication written as the circuit's own
    computation — the [EccSpec.fixed_scalar_mul] fold over the [Params]
    Lagrange table, consuming the per-window square-root witnesses
    ([us : list Z]) exactly as the circuit determines them.  Not a
    specification anyone should audit against the protocol: the two layers
    are proved equal (with canonical witnesses, on protocol-typed inputs)
    in [circuit_proof/protocol_equiv.v]. *)

Module OrchardCircuitSpec.

  (** The circuit-side parameters: the six windowed Lagrange fixed-base
      tables (the circuit's representation of the Orchard generators), plus
      the protocol-level [OrchardSpec.Params] domain points ([domain]) the
      shared Sinsemilla components consume. *)
  Record Params : Set := {
    spend_auth_g : EccSpec.fixed_table;   (* SpendAuthG *)
    value_commit_v : EccSpec.fixed_table; (* ValueCommitV (short base) *)
    value_commit_r : EccSpec.fixed_table; (* ValueCommitR *)
    nullifier_k : EccSpec.fixed_table;    (* K — base-field fixed base *)
    note_commit_r : EccSpec.fixed_table;  (* NoteCommitR blinding base *)
    commit_ivk_r : EccSpec.fixed_table;   (* CommitIvkR blinding base *)
    domain : OrchardSpec.Params;          (* Sinsemilla domain points *)
  }.

  (** The per-window square-root witnesses of each fixed-base multiplication.
      Kept separate from [OrchardSpec.ActionInputs] because they are benign prover
      nondeterminism — the public outputs depend on them only through [u²] — not
      genuine external inputs.  [OrchardSpec.ActionInputs] therefore names only the secrets. *)
  Record ActionWitness : Set := {
    w_us_alpha : list Z;  (* [α]·SpendAuthG *)
    w_us_v : list Z;      (* [v]·ValueCommitV *)
    w_us_rcv : list Z;    (* [rcv]·ValueCommitR *)
    w_us_k : list Z;      (* [scalar]·K *)
    w_us_rcm : list Z;    (* [rcm]·NoteCommitR *)
  }.

  (** [RK = ak + [α]·SpendAuthG] — the spend-authority randomization, the
      fixed-base mul folded over the [spend_auth_g] table with witnesses [us].

      Protocol: §4.18.4 'Spend authority',
      [rk = SpendAuthSig^Orchard.RandomizePublic(α, ak_P)], with
      [RandomizePublic(α, ak) = ak + [α] 𝒢^Orchard] (§4.18.4 notes;
      𝒢^Orchard as in §5.4.7.1 'Spend Authorization Signature'). *)
  Definition spend_auth_randomize
      (prm : Params) (ak : Point.t) (alpha : Z) (us : list Z) : Point.t :=
    EccSpec.point_add ak (EccSpec.fixed_scalar_mul (spend_auth_g prm) alpha us).

  (** [cv_net = [v]·ValueCommitV + [rcv]·ValueCommitR].  [v] is the signed
      magnitude/sign pair: the short fixed-base mul scales by [magnitude] and the
      [sign] flips the y-coordinate ([ShortFixedBaseMul]).

      Protocol: §4.18.4 'Value commitment integrity',
      [cv_net = ValueCommit^Orchard_rcv(v_old − v_new)], with
      [ValueCommit^Orchard_rcv(v) = [v] 𝒱^Orchard + [rcv] ℛ^Orchard]
      (§5.4.8.3 'Homomorphic Pedersen commitments').  The signed value is
      the magnitude/sign decomposition of [v_old − v_new] over the
      §4.18.4-noted range [{−2⁶⁴+1 .. 2⁶⁴−1}] (y-negation = point negation,
      so [sign = −1] yields [[−magnitude]·𝒱]); the binding of
      [magnitude·sign] to [v_old − v_new] is a separate circuit gate, not
      part of this output function. *)
  Definition value_commit
      (prm : Params) (magnitude sign rcv : Z) (us_v us_r : list Z) : Point.t :=
    let v_point := EccSpec.fixed_scalar_mul (value_commit_v prm) magnitude us_v in
    EccSpec.point_add
      {| Point.x := v_point.(Point.x); Point.y := sign *F v_point.(Point.y) |}
      (EccSpec.fixed_scalar_mul (value_commit_r prm) rcv us_r).

  (** [nf = Extract_x([ (PRF^{nf}_nk(ρ) + ψ) mod q_P ]·K + cm)], with the
      Poseidon PRF [PRF^{nf}_nk(ρ) = poseidon_hash2 nk ρ] and [K] the windowed
      base [us].  The scalar is the base-field sum ([+F], i.e. reduced mod
      [q_P] = the Pallas base-field modulus), as in the protocol spec: the
      circuit decomposes the reduced sum into its canonical 85-window base-8
      digit string, so the scalar seen by the windowed multiplication is the
      field element, not the unreduced integer sum.

      Protocol: §4.18.4 'Nullifier integrity',
      [nf_old = DeriveNullifier_nk(ρ_old, ψ_old, cm_old)], with
      [DeriveNullifier_nk(ρ, ψ, cm) =
        Extract_P([(PRF^nfOrchard_nk(ρ) + ψ) mod q_P] 𝒦^Orchard + cm)]
      (§4.16 'Computing ρ values and Nullifiers');
      [PRF^nfOrchard_nk(ρ) = PoseidonHash(nk, ρ)] (§5.4.2 'Pseudo Random
      Functions'); [Extract_P] as in §5.4.9.7 'Coordinate Extractor for
      Pallas'.  The canonical digit decomposition of the reduced scalar is
      the canonicity MUST of the §4.18.4 notes (non-canonical representation
      of the DeriveNullifier scalar would enable a double spend). *)
  Definition nullifier
      (prm : Params) (nk rho psi : Z) (cm : Point.t) (us : list Z) : Z :=
    let scalar := Poseidon.poseidon_hash2 nk rho +F psi in
    EccSpec.extract_x
      (EccSpec.point_add
        (EccSpec.fixed_scalar_mul (nullifier_k prm) scalar us) cm).

  (** [NoteCommit_{rcm}(g_d, pk_d, v, ρ, ψ)]: Sinsemilla hash-to-point in the
      [OrchardSpec.note_commit_q] domain, blinded by [rcm]·NoteCommitR (the windowed base
      [note_commit_r] with witnesses [us]).

      Protocol: §5.4.8.4, [NoteCommit^Orchard_rcm(…) =
      SinsemillaCommit_rcm("z.cash:Orchard-NoteCommit", …)], with
      [SinsemillaCommit_r(D, M) = SinsemillaHashToPoint(D || "-M", M)
      + [r] GroupHash^P(D || "-r", "")].  The domain point [OrchardSpec.note_commit_q]
      and the blinding base are the circuit's concrete constants for those
      two group hashes. *)
  Definition note_commit
      (prm : Params) (g_d pk_d : Point.t) (v rho psi rcm : Z) (us : list Z)
      : Point.t :=
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q (domain prm))
        (OrchardSpec.note_commit_message g_d pk_d v rho psi))
      (EccSpec.fixed_scalar_mul (note_commit_r prm) rcm us).

  (** [ivk = Extract_x(SinsemillaCommit_{rivk}(ak, nk))], blinded by the windowed
      [commit_ivk_r] base.  (Not a public output; kept for completeness.)

      Protocol: §5.4.8.4, [Commit^ivk_rivk(ak, nk) =
      SinsemillaShortCommit_rivk("z.cash:Orchard-CommitIvk", …)], i.e.
      [Extract⊥_P] of the [SinsemillaCommit]; consumed by §4.18.4
      'Diversified address integrity' ([pk_d_old = [ivk] g_d_old]), which is
      an input-side condition outside the public-output functions. *)
  Definition commit_ivk
      (prm : Params) (ak nk rivk : Z) (us : list Z) : Z :=
    EccSpec.extract_x
      (EccSpec.point_add
        (SinsemillaSpec.sinsemilla_hash_to_point
          (OrchardSpec.commit_ivk_q (domain prm))
          (OrchardSpec.commit_ivk_message ak nk))
        (EccSpec.fixed_scalar_mul (commit_ivk_r prm) rivk us)).

  (** [CMX = Extract_x(NoteCommit(new note))] — the capstone output.  Its
      [rho_new] is the old note's nullifier (threaded by [orchard_action_spec]),
      so it transitively depends on Poseidon, the fixed-base mul and Sinsemilla.

      Protocol: §4.18.4 'New note commitment integrity',
      [Extract⊥_P(NoteCommit^Orchard_rcm_new(g⋆_d_new, pk⋆_d_new, v_new,
      ρ_new, ψ_new)) ∈ {cm_x, ⊥}] with [ρ_new = nf_old (mod q_P)]; this
      function is the honest (non-⊥) branch of that condition. *)
  Definition OrchardCmx
      (prm : Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) (us : list Z) : Z :=
    EccSpec.extract_x
      (note_commit prm g_d_new pk_d_new v_new rho_new psi_new rcm_new us).

  (** The whole-action circuit-structured spec: every public output as a
      function of the witnessed inputs and the square-root witness record.
      Note [rho_new := OrchardSpec.out_nf_old]: the new note's [ρ] is the old note's
      nullifier, as the circuit constrains ([rho_new] to [NF_OLD]).

      Protocol: the five output-side conditions of §4.18.4 — Merkle path
      validity ([OrchardSpec.out_anchor]), value commitment integrity ([OrchardSpec.out_cv_net]),
      nullifier integrity ([OrchardSpec.out_nf_old]), spend authority ([OrchardSpec.out_rk]), and
      new note commitment integrity ([OrchardSpec.out_cmx], with [ρ_new = nf_old]).
      The input-side conditions of §4.18.4 (old note commitment integrity,
      diversified address integrity, the enable-spend/output flags) constrain
      inputs rather than outputs and are outside this function. *)
  Definition orchard_action_spec
      (prm : Params) (inp : OrchardSpec.ActionInputs) (wit : ActionWitness) : OrchardSpec.ActionOutputs :=
    let nf_old :=
      nullifier prm (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp) (OrchardSpec.in_psi_old inp)
        (OrchardSpec.in_cm_old inp) (w_us_k wit) in
    let rho_new := nf_old in {|
      (* The gate [orchard_circuit_checks_gate] binds the public OrchardSpec.anchor to the
         computed Merkle root only on a value-bearing spend (its constraint is
         [Either v_old = 0, or root = OrchardSpec.anchor]).  A dummy spend ([OrchardSpec.in_v_old = 0])
         leaves the OrchardSpec.anchor unconstrained, so the spec returns the public row
         verbatim ([OrchardSpec.in_anchor_public]).  Consequently the OrchardSpec.anchor output carries
         no Merkle-membership content on dummy spends: the determinism /
         correctness statements equate it with the same public row it is read
         from, which holds by construction and binds the prover to nothing.
         This disjunction is verbatim §4.18.4 'Merkle path validity':
         "Either v_old = 0; or (path, pos) is a valid Merkle path … to the
         OrchardSpec.anchor rt^Orchard". *)
      OrchardSpec.out_anchor :=
        if OrchardSpec.in_v_old inp =? 0
        then OrchardSpec.in_anchor_public inp
        else OrchardSpec.anchor (domain prm) (OrchardSpec.in_leaf inp) (OrchardSpec.in_path inp);
      OrchardSpec.out_cv_net :=
        value_commit prm (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp) (OrchardSpec.in_rcv inp)
          (w_us_v wit) (w_us_rcv wit);
      OrchardSpec.out_nf_old := nf_old;
      OrchardSpec.out_rk :=
        spend_auth_randomize prm (OrchardSpec.in_ak inp) (OrchardSpec.in_alpha inp) (w_us_alpha wit);
      OrchardSpec.out_cmx :=
        OrchardCmx prm
          (OrchardSpec.in_g_d_new inp) (OrchardSpec.in_pk_d_new inp)
          (OrchardSpec.in_v_new inp) rho_new (OrchardSpec.in_psi_new inp) (OrchardSpec.in_rcm_new inp)
          (w_us_rcm wit);
    |}.

  (** The capstone unfolds to the new-note commitment x-coordinate — definitional
      guard tying [OrchardCmx] to [note_commit]. *)
  Lemma OrchardCmx_unfold
      (prm : Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) (us : list Z) :
    OrchardCmx prm g_d_new pk_d_new v_new rho_new psi_new rcm_new us =
      EccSpec.extract_x
        (note_commit prm g_d_new pk_d_new v_new rho_new psi_new rcm_new us).
  Proof. reflexivity. Qed.

  (** The action's [nf_old] output is exactly the nullifier of the old-note
      inputs — and the same value is fed as the new note's [ρ] inside
      [OrchardSpec.out_cmx] (see [orchard_action_spec]), encoding the [CMX]-depends-on-the-
      nullifier link definitionally. *)
  Lemma action_nf_old_eq (prm : Params) (inp : OrchardSpec.ActionInputs) (wit : ActionWitness) :
    OrchardSpec.out_nf_old (orchard_action_spec prm inp wit) =
      nullifier prm (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp) (OrchardSpec.in_psi_old inp)
        (OrchardSpec.in_cm_old inp) (w_us_k wit).
  Proof. reflexivity. Qed.
End OrchardCircuitSpec.
