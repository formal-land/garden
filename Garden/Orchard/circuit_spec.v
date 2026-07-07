Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Orchard action output functions and action spec

    The five public outputs of the Orchard action circuit, each composed from
    the ECC/Sinsemilla/Poseidon spec primitives, plus the [orchard_action_spec : inputs ->
    outputs] that bundles them — culminating in [OrchardCmx], the capstone whose
    [rho_new] is the old note's nullifier.

    The fixed public Orchard parameters are bundled in [Params].  Crucially they
    are the circuit's *own concrete representations*: the Sinsemilla domain
    points are affine [Point.t] (the circuit stores their coordinates), and the
    fixed-base generators are the windowed Lagrange [EccSpec.fixed_table]s (the
    circuit has no affine form for them).  So [Params] can be instantiated by a
    genuine [Definition] from the circuit constants — see
    [Orchard/circuit_proof/main.v] ([orchard_circuit_params]) — with nothing abstract
    left to quantify over.  Each fixed-base multiplication additionally consumes
    the per-window square-root witnesses ([us : list Z]) the assignment carries,
    exactly as the circuit determines them. *)

Module OrchardSpec.
  (** The public, fixed parameters of the Orchard action.  Sinsemilla domain
      points are affine; fixed-base generators are windowed Lagrange tables. *)
  Record Params : Set := {
    spend_auth_g : EccSpec.fixed_table;   (* SpendAuthG *)
    value_commit_v : EccSpec.fixed_table; (* ValueCommitV (short base) *)
    value_commit_r : EccSpec.fixed_table; (* ValueCommitR *)
    nullifier_k : EccSpec.fixed_table;    (* K — base-field fixed base *)
    note_commit_q : Point.t;              (* NoteCommit Sinsemilla domain point *)
    note_commit_r : EccSpec.fixed_table;  (* NoteCommitR blinding base *)
    commit_ivk_q : Point.t;               (* CommitIvk Sinsemilla domain point *)
    commit_ivk_r : EccSpec.fixed_table;   (* CommitIvkR blinding base *)
    merkle_crh_q : Point.t;               (* MerkleCRH Sinsemilla domain point *)
  }.

  Definition point_y (P : Point.t) : Z := P.(Point.y).

  (** [RK = ak + [α]·SpendAuthG] — the spend-authority randomization, the
      fixed-base mul folded over the [spend_auth_g] table with witnesses [us]. *)
  Definition spend_auth_randomize
      (prm : Params) (ak : Point.t) (alpha : Z) (us : list Z) : Point.t :=
    EccSpec.point_add ak (EccSpec.fixed_scalar_mul (spend_auth_g prm) alpha us).

  (** [cv_net = [v]·ValueCommitV + [rcv]·ValueCommitR].  [v] is the signed
      magnitude/sign pair: the short fixed-base mul scales by [magnitude] and the
      [sign] flips the y-coordinate ([ShortFixedBaseMul]). *)
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
      field element, not the unreduced integer sum. *)
  Definition nullifier
      (prm : Params) (nk rho psi : Z) (cm : Point.t) (us : list Z) : Z :=
    let scalar := Poseidon.poseidon_hash2 nk rho +F psi in
    EccSpec.extract_x
      (EccSpec.point_add
        (EccSpec.fixed_scalar_mul (nullifier_k prm) scalar us) cm).

  (** Note-commitment Sinsemilla message: the diversified base, the transmission
      key, the value, [ρ] and [ψ] packed little-endian into 10-bit words.  Each
      point contributes its full 256-bit compressed encoding — the x-coordinate
      plus the y-parity sign bit [y mod 2] at bits 255/511 (the circuit's
      [b_2]/[d_1] witness cells) — then the 64-bit value and the 255-bit [ρ]
      and [ψ]: 1086 bits, hashed as 109 ten-bit words (the packing of
      [NoteCommitMessagePieces.note_commit_packed]). *)
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

  (** [NoteCommit_{rcm}(g_d, pk_d, v, ρ, ψ)]: Sinsemilla hash-to-point in the
      [note_commit_q] domain, blinded by [rcm]·NoteCommitR (the windowed base
      [note_commit_r] with witnesses [us]). *)
  Definition note_commit
      (prm : Params) (g_d pk_d : Point.t) (v rho psi rcm : Z) (us : list Z)
      : Point.t :=
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (note_commit_q prm)
        (note_commit_message g_d pk_d v rho psi))
      (EccSpec.fixed_scalar_mul (note_commit_r prm) rcm us).

  (** [CommitIvk] message: [ak] then [nk], packed into 10-bit words. *)
  Definition commit_ivk_message (ak nk : Z) : list Z :=
    SinsemillaSpec.words_le 52 (ak + nk * 2 ^ 256).

  (** [ivk = Extract_x(SinsemillaCommit_{rivk}(ak, nk))], blinded by the windowed
      [commit_ivk_r] base.  (Not a public output; kept for completeness.) *)
  Definition commit_ivk
      (prm : Params) (ak nk rivk : Z) (us : list Z) : Z :=
    EccSpec.extract_x
      (EccSpec.point_add
        (SinsemillaSpec.sinsemilla_hash_to_point
          (commit_ivk_q prm)
          (commit_ivk_message ak nk))
        (EccSpec.fixed_scalar_mul (commit_ivk_r prm) rivk us)).

  (** [anchor]: the Merkle root reached from the leaf along the path. *)
  Definition anchor
      (prm : Params) (leaf : Z) (path : list (Z * Z * bool)) : Z :=
    SinsemillaSpec.merkle_root (merkle_crh_q prm) leaf path.

  (** [CMX = Extract_x(NoteCommit(new note))] — the capstone output.  Its
      [rho_new] is the old note's nullifier (threaded by [orchard_action_spec]),
      so it transitively depends on Poseidon, the fixed-base mul and Sinsemilla. *)
  Definition OrchardCmx
      (prm : Params) (g_d_new pk_d_new : Point.t)
      (v_new rho_new psi_new rcm_new : Z) (us : list Z) : Z :=
    EccSpec.extract_x
      (note_commit prm g_d_new pk_d_new v_new rho_new psi_new rcm_new us).

  (** ** Action-level spec: inputs -> outputs *)

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

  (** The per-window square-root witnesses of each fixed-base multiplication.
      Kept separate from [ActionInputs] because they are benign prover
      nondeterminism — the public outputs depend on them only through [u²] — not
      genuine external inputs.  [ActionInputs] therefore names only the secrets. *)
  Record ActionWitness : Set := {
    w_us_alpha : list Z;  (* [α]·SpendAuthG *)
    w_us_v : list Z;      (* [v]·ValueCommitV *)
    w_us_rcv : list Z;    (* [rcv]·ValueCommitR *)
    w_us_k : list Z;      (* [scalar]·K *)
    w_us_rcm : list Z;    (* [rcm]·NoteCommitR *)
  }.

  Record ActionOutputs : Set := {
    out_anchor : Z;
    out_cv_net : Point.t;
    out_nf_old : Z;
    out_rk : Point.t;
    out_cmx : Z;
  }.

  (** The whole-action functional spec: every public output as a function of the
      witnessed inputs.  Note [rho_new := out_nf_old]: the new note's [ρ] is the
      old note's nullifier, as the circuit constrains ([rho_new] to [NF_OLD]). *)
  Definition orchard_action_spec
      (prm : Params) (inp : ActionInputs) (wit : ActionWitness) : ActionOutputs :=
    let nf_old :=
      nullifier prm (in_nk inp) (in_rho_old inp) (in_psi_old inp)
        (in_cm_old inp) (w_us_k wit) in
    let rho_new := nf_old in {|
      (* The gate [orchard_circuit_checks_gate] binds the public anchor to the
         computed Merkle root only on a value-bearing spend (its constraint is
         [Either v_old = 0, or root = anchor]).  A dummy spend ([in_v_old = 0])
         leaves the anchor unconstrained, so the spec returns the public row
         verbatim ([in_anchor_public]).  Consequently the anchor output carries
         no Merkle-membership content on dummy spends: the determinism /
         correctness statements equate it with the same public row it is read
         from, which holds by construction and binds the prover to nothing. *)
      out_anchor :=
        if in_v_old inp =? 0
        then in_anchor_public inp
        else anchor prm (in_leaf inp) (in_path inp);
      out_cv_net :=
        value_commit prm (in_magnitude inp) (in_sign inp) (in_rcv inp)
          (w_us_v wit) (w_us_rcv wit);
      out_nf_old := nf_old;
      out_rk :=
        spend_auth_randomize prm (in_ak inp) (in_alpha inp) (w_us_alpha wit);
      out_cmx :=
        OrchardCmx prm
          (in_g_d_new inp) (in_pk_d_new inp)
          (in_v_new inp) rho_new (in_psi_new inp) (in_rcm_new inp)
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
      [out_cmx] (see [orchard_action_spec]), encoding the [CMX]-depends-on-the-
      nullifier link definitionally. *)
  Lemma action_nf_old_eq (prm : Params) (inp : ActionInputs) (wit : ActionWitness) :
    out_nf_old (orchard_action_spec prm inp wit) =
      nullifier prm (in_nk inp) (in_rho_old inp) (in_psi_old inp)
        (in_cm_old inp) (w_us_k wit).
  Proof. reflexivity. Qed.

End OrchardSpec.
