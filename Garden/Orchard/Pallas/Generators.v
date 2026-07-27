(** * Orchard fixed-base generator points on the Pallas curve

    The six Orchard fixed-base generator points, instantiated on the generic
    Pallas curve of [EllipticCurve/Pallas.v], and the per-generator facts the
    Orchard fixed-base ladder argument consumes: [on_curve],
    [G <> identity], the prime-order certificate [[pallas_q] G = identity],
    the order characterisation [ord = pallas_q] (as the divisibility iff), and
    injectivity of [mul] modulo [pallas_q].

    This file, unlike [EllipticCurve/Pallas.v], is Orchard-specific: the six
    generator names and their concrete coordinates are
    Orchard's fixed-base set, not curve-generic data, so it lives under
    [Garden/Orchard/] rather than [Garden/EllipticCurve/].

    Proof structure. On-curve membership and reducedness are finite
    Pallas-field computations (closed by [vm_compute]); the [pallas_q]-fold
    double-and-add ladder is reduced once per generator
    in the [order_<base>.v] leaf files (a [vm_cast_no_check] each,
    [make -j] parallel); the order characterisation and injectivity live in
    [GeneratorsOrder.v] ([PallasGeneratorsOrder]), derived there from the
    leaf certificates and the generic [Weierstrass] order theory
    ([mul_eq_Infinity_iff] / [mul_injective_mod]) together with
    [Pallas.pallas_q_is_prime]. This file holds only the points and their
    cheap facts, so the fixed-base table leaves that consume the points
    never wait on the six ladder reductions.

    Generator coordinates. The six Orchard fixed bases are derived by Zcash
    hash-to-curve ([group_hash], Protocol: §5.4.9.8 'Group Hash into Pallas
    and Vesta') and exist in the circuit only as windowed
    Lagrange tables (no affine generator). All six carry their real Zcash
    affine coordinates: [spend_auth_g_G] was recovered offline from the
    circuit fixed-base table
    ([Garden/Orchard/constants/fixed_bases/spend_auth_g.v]) — the window-0
    digit-0 and digit-1 entries are the x-coordinates of [[2] G] and [[3] G]
    (the window scalar of window [w] digit [d] is [(d + 2) * 8^w]), so [G] is
    their point difference [[3] G - [2] G], the [y]-sign pinned by the
    window's [z] value via [y + z] being a square and cross-checked against
    [[2] G], [[3] G], [[4] G] — and the other five are the [GENERATOR]
    constants of the Rust [orchard] crate
    ([src/constants/fixed_bases/<base>.rs], little-endian byte pairs),
    validated offline the same way: each point is on the curve and the
    window-0 digit-0/1/2 x-coordinates computed from its Lagrange table
    ([Garden/Orchard/constants/fixed_bases/<base>.v]) equal
    [x([2] G)], [x([3] G)], [x([4] G)]. Because [#E_Pallas(F_p) = pallas_q]
    is prime, every non-identity point has order [pallas_q], so each base gets
    the same per-generator facts, with the [pallas_q]-ladder certificate
    provided per generator by its [order_<base>.v] leaf file. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module PallasGenerators.
  Import Pallas.

  (** ** The six Orchard fixed-base generator points

      All six carry their real Zcash affine coordinates: [spend_auth_g_G]
      recovered from the circuit fixed-base table, the other five taken from
      the Rust [orchard] crate's [GENERATOR] constants and cross-checked
      against the circuit Lagrange tables (see the file header). *)
  Definition spend_auth_g_G : point :=               (* SpendAuthG *)
    affine
      25027635063850382358429654596649554085117301901282348152423547104939793041763
      12128007492603938773365931378340937928001494939630793217712875072231079427017.
  Definition value_commit_v_G : point :=             (* ValueCommitV *)
    affine
      21457208314186520936880902219424053485005045883401337627148481900742711001959
      20379375922573002911833717643813254676246486412159279022689151936901102105230.
  Definition value_commit_r_G : point :=             (* ValueCommitR *)
    affine
      3597772235883004661259329170144280297379687592370687591147658848249887611537
      16317546749781193797530044795837656238506071957562073482938086095508632426954.
  Definition nullifier_k_G : point :=                (* NullifierK *)
    affine
      17144890976040313974462754624161095328261290075490099718273142830262355741301
      9661337292872073193100428608853316471968232023361741282759000480983323509196.
  Definition note_commit_r_G : point :=              (* NoteCommitR *)
    affine
      17502433695644481444785977856966854265310331039772160001849803703443502427667
      27531606546556235994383748883097777001194017792923801570415255878186539366371.
  Definition commit_ivk_r_G : point :=               (* CommitIvkR *)
    affine
      17022113834174368664964072539940476916905682548990455171271428285673934201112
      18912017636736613471143674001158885358143653198146604093009134371854861983145.

  (** Reducedness of the real SpendAuthG generator (its [affine] coordinates are
      already taken modulo [pallas_p]). *)
  Lemma spend_auth_g_reduced : reduced spend_auth_g_G.
  Proof. vm_compute. split; reflexivity. Qed.

  (** ** Per-generator facts

      For each fixed base [B] with generator [B_G]:
      - [B_on_curve]      : [B_G] lies on the curve;
      - [B_ne_identity]   : [B_G] is not the identity;
      - [B_order]         : [[pallas_q] B_G = identity] — the prime-order
        certificate (a finite [vm_compute] in the [order_<base>.v] leaves);
      - [B_order_eq]      : [ord(B_G) = pallas_q], phrased as
        [mul n B_G = identity <-> pallas_q | n] (from [mul_eq_Infinity_iff] +
        [pallas_q_prime]);
      - [B_mul_injective] : [mul] is injective on residues mod [pallas_q]
        (from [mul_injective_mod]). *)

  (** *** SpendAuthG (the RK base) *)
  Lemma spend_auth_g_on_curve : on_curve spend_auth_g_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma spend_auth_g_ne_identity : spend_auth_g_G <> identity.
  Proof. discriminate. Qed.

  (** *** ValueCommitV *)
  Lemma value_commit_v_reduced : reduced value_commit_v_G.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma value_commit_v_on_curve : on_curve value_commit_v_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_commit_v_ne_identity : value_commit_v_G <> identity.
  Proof. discriminate. Qed.

  (** *** ValueCommitR *)
  Lemma value_commit_r_reduced : reduced value_commit_r_G.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma value_commit_r_on_curve : on_curve value_commit_r_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_commit_r_ne_identity : value_commit_r_G <> identity.
  Proof. discriminate. Qed.

  (** *** NullifierK *)
  Lemma nullifier_k_reduced : reduced nullifier_k_G.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma nullifier_k_on_curve : on_curve nullifier_k_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nullifier_k_ne_identity : nullifier_k_G <> identity.
  Proof. discriminate. Qed.

  (** *** NoteCommitR *)
  Lemma note_commit_r_reduced : reduced note_commit_r_G.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma note_commit_r_on_curve : on_curve note_commit_r_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma note_commit_r_ne_identity : note_commit_r_G <> identity.
  Proof. discriminate. Qed.

  (** *** CommitIvkR *)
  Lemma commit_ivk_r_reduced : reduced commit_ivk_r_G.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma commit_ivk_r_on_curve : on_curve commit_ivk_r_G.
  Proof. vm_compute. reflexivity. Qed.

  Lemma commit_ivk_r_ne_identity : commit_ivk_r_G <> identity.
  Proof. discriminate. Qed.

End PallasGenerators.
