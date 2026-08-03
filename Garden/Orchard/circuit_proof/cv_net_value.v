(** * CV_NET value-balance composition

    The per-action value-soundness layer over the [CV_NET] public output:
    the value commitment of a satisfying assignment commits exactly the
    signed net value that the [QOrchard] balance gate ties to
    [v_old - v_new].

    - [CvNetValue.cv_net_value_balance_sound]: the [CV_NET] projection of
      functional correctness conjoined with the extracted balance gate
      ([OrchardValidActionInputs.value_balance_gate]) — a composed
      no-inflation statement inside the relational model: the public
      [CV_NET] is the deterministic value commitment to the same
      magnitude/sign pair the Orchard gate equates with [v_old - v_new].
    - [CvNetValue.cv_net_commits_net_value]: the §4.18.4 'Value commitment
      integrity' shape — [cv_net = ValueCommit^Orchard_rcv(v)] for the
      signed scalar [v = signed_net_value magnitude sign], together with
      [v ≡ v_old - v_new (mod pallas_p)] and [|v| < 8²²].  The sign case
      split and the magnitude bound come from
      [OrchardValidActionInputs.protocol_typed_inputs_of_holds]; the
      congruence from the balance gate.
    - [CvNetValue.cv_net_commits_net_value_Z]: the integer reading
      [cv_net = ValueCommit^Orchard_rcv(v_old - v_new)] over ℤ, with the
      64-bit ranges of the [v_old]/[v_new] cells circuit-derived
      ([TypedInputsValue64], via the note-commit value-slot decompositions)
      under the two short-lookup honesty predicates
      ([NoteCommitNewWords.note_commit_new_short_lookup_ok] and
      [OldNoteWords.old_note_short_lookup_ok]).

    The [CV_NET] row is one of the five ⊥-free public outputs: it uses
    complete addition and total group multiples only, so none of the three
    theorems carries a Merkle or nondegeneracy hypothesis — acceptance and
    the two short-lookup families are the whole premise set, and both
    families are discharged from acceptance of the pinned circuit
    ([circuit_proof/lookup_closure.v],
    [circuit_proof/lookup_closure_old_note.v]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.typed_inputs.value64.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Orchard.circuit_proof.us_free.nullifier_k.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.protocol_mul.signed.
Require Import Garden.Orchard.circuit_proof.main.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the conversion oracle: no
   up-to-conversion matching may evaluate [modpow] over the concrete Pallas
   [(p-1)/2] exponent (see [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module CvNetValue.
  Import OrchardActionInputs.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** Projection read-off of the protocol action spec at the [CV_NET]
      output, over variable inputs: both sides reduce to the identical
      [value_commit] application, so no fold is ever forced. *)
  Lemma out_cv_net_spec_proj
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs) :
    OrchardSpec.out_cv_net
      (OrchardProtocolSpec.orchard_action_spec prm inp) =
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value
        (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp))
      (OrchardSpec.in_rcv inp).
  Proof. reflexivity. Qed.

  (** ** The [CV_NET] output from acceptance alone

      [OrchardAction.satisfies_specification] carries the whole output
      record and therefore the Merkle and new-note witness-honesty
      conditions of the anchor and [CMX] rows.  The value-commitment row
      needs neither: [OrchardAction.cv_net_{x,y}_correct] are
      [Holds]-only, and the protocol reading of the circuit-structured spec
      is the same composition [satisfies_specification] performs
      internally — the square-root witness elimination followed by the
      protocol equivalence, whose typing premise is itself circuit-derived. *)

  Lemma point_eta (P : Point.t) :
    {| Point.x := Point.x P; Point.y := Point.y P |} = P.
  Proof. destruct P; reflexivity. Qed.

  Lemma out_cv_net_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.out_cv_net (read_action_outputs Γ) =
      {| Point.x := read_public_instance Γ Garden.Orchard.circuit.CV_NET_X;
         Point.y := read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y |}.
  Proof. reflexivity. Qed.

  Lemma action_spec_protocol
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    OrchardAction.action_spec_of Γ =
    OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
      (read_action_inputs Γ).
  Proof.
    exact (eq_trans
      (OrchardActionUsFreeNullifierK.action_spec_us_free Γ Hcircuit)
      (OrchardProtocolEquiv.output_protocol_eq (read_action_inputs Γ)
        (OrchardValidActionInputs.protocol_typed_inputs_of_holds
          Γ Hcircuit))).
  Qed.

  Lemma cv_net_output_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    OrchardSpec.out_cv_net (read_action_outputs Γ) =
      OrchardSpec.out_cv_net
        (OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
          (read_action_inputs Γ)).
  Proof.
    rewrite out_cv_net_read.
    rewrite (OrchardAction.cv_net_x_correct Γ Hcircuit).
    rewrite (OrchardAction.cv_net_y_correct Γ Hcircuit).
    rewrite (action_spec_protocol Γ Hcircuit).
    apply point_eta.
  Qed.

  (** The composition of [CV_NET] functional correctness with the balance
      gate: the public [CV_NET] output is the protocol value commitment of
      the witnessed magnitude/sign pair, and that same pair is equated with
      [v_old - v_new] by the [QOrchard] gate (field arithmetic).  Pure
      composition: the [out_cv_net] projection of
      [cv_net_output_of_holds] and
      [OrchardValidActionInputs.value_balance_gate]. *)
  Theorem cv_net_value_balance_sound
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardSpec.out_cv_net (read_action_outputs Γ) =
      OrchardSpec.out_cv_net
        (OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
          (read_action_inputs Γ)) /\
    OrchardSpec.in_v_old (read_action_inputs Γ) -F
      OrchardSpec.in_v_new (read_action_inputs Γ) =
    OrchardSpec.in_magnitude (read_action_inputs Γ) *F
      OrchardSpec.in_sign (read_action_inputs Γ).
  Proof.
    split.
    - exact (cv_net_output_of_holds Γ Hcircuit).
    - exact (OrchardValidActionInputs.value_balance_gate Γ Hcircuit).
  Qed.

  (** §4.18.4 'Value commitment integrity', verbatim shape: the [CV_NET]
      output is [ValueCommit^Orchard_rcv(v)] for a signed scalar [v] that is
      congruent to [v_old - v_new] mod [pallas_p] and bounded by the
      circuit's 22-window magnitude range.  [v] is
      [signed_net_value magnitude sign]; the sign case split
      ([sign ∈ {1, pallas_p - 1}]) and the [8²²] magnitude bound are
      circuit-extracted by
      [OrchardValidActionInputs.protocol_typed_inputs_of_holds], and the
      congruence is [OrchardValidActionInputs.value_balance_gate] read
      through [SignedValueAlgebra]'s [signed_net_value] evaluations. *)
  Theorem cv_net_commits_net_value
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let inp := read_action_inputs Γ in
    let v :=
      OrchardProtocolSpec.signed_net_value
        (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp) in
    OrchardSpec.out_cv_net (read_action_outputs Γ) =
      OrchardProtocolSpec.value_commit v (OrchardSpec.in_rcv inp) /\
    v mod Primes.pallas_p =
      (OrchardSpec.in_v_old inp - OrchardSpec.in_v_new inp)
        mod Primes.pallas_p /\
    Z.abs v < 8 ^ 22.
  Proof.
    cbv zeta.
    pose proof
      (OrchardValidActionInputs.protocol_typed_inputs_of_holds Γ Hcircuit)
      as (_ & _ & _ & Hmag & Hsign).
    pose proof (OrchardValidActionInputs.value_balance_gate Γ Hcircuit)
      as Hgate.
    unfold BinOp.sub, BinOp.mul in Hgate.
    refine (conj _ (conj _ _)).
    - (* cv_net = value_commit (signed_net_value magnitude sign) rcv *)
      rewrite (cv_net_output_of_holds Γ Hcircuit).
      exact
        (out_cv_net_spec_proj orchard_circuit_params (read_action_inputs Γ)).
    - (* signed_net_value magnitude sign ≡ v_old - v_new (mod pallas_p) *)
      destruct Hsign as [Hs | Hs]; rewrite Hs in Hgate |- *.
      + rewrite SignedValueAlgebra.signed_net_value_one.
        rewrite Z.mul_1_r in Hgate.
        symmetry; exact Hgate.
      + rewrite SignedValueAlgebra.signed_net_value_neg_one.
        replace
          (OrchardSpec.in_magnitude (read_action_inputs Γ) *
            (Primes.pallas_p - 1))
          with
            (- OrchardSpec.in_magnitude (read_action_inputs Γ) +
              OrchardSpec.in_magnitude (read_action_inputs Γ) *
                Primes.pallas_p)
          in Hgate by ring.
        rewrite Z_mod_plus_full in Hgate.
        symmetry; exact Hgate.
    - (* |signed_net_value magnitude sign| < 8^22 *)
      destruct Hsign as [Hs | Hs]; rewrite Hs.
      + rewrite SignedValueAlgebra.signed_net_value_one.
        clear -Hmag; lia.
      + rewrite SignedValueAlgebra.signed_net_value_neg_one.
        clear -Hmag; lia.
  Qed.

  (** The true-ℤ reading of the value binding:
      [cv_net = ValueCommit^Orchard_rcv(v_old - v_new)] with the subtraction
      over ℤ, not mod [pallas_p].  The two 64-bit ranges are exactly what
      the congruence of [cv_net_commits_net_value] is missing to pin the
      integer value: with [|signed_net_value| < 8²² = 2⁶⁶] and
      [|v_old - v_new| < 2⁶⁴], the two sides of the congruence differ by
      less than [pallas_p], so they are equal.

      The ranges are circuit-derived ([TypedInputsValue64.in_v_old_64] /
      [in_v_new_64]): each note-commit circuit packs its 64-bit value slot
      as [d_2 + z1_d·2^8 + e_0·2^58] and copies it to the [VOld]/[VNew]
      witness cell, so the bound follows from [Holds Γ] plus the
      short-lookup honesty predicate of the corresponding note-commit lane
      (the selector-plane idealization of the relational model; see the
      [old_note/words.v] file header).  Both enter as explicit hypotheses,
      and both are discharged from acceptance of the pinned circuit by the
      lookup-closure files ([circuit_proof/lookup_closure.v],
      [circuit_proof/lookup_closure_old_note.v]).  No nondegeneracy or
      Merkle condition is needed: the [CV_NET] row is ⊥-free. *)
  Theorem cv_net_commits_net_value_Z
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnew_short : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ)
      (Hold_short : OldNoteWords.old_note_short_lookup_ok Γ) :
    OrchardSpec.out_cv_net (read_action_outputs Γ) =
      OrchardProtocolSpec.value_commit
        (OrchardSpec.in_v_old (read_action_inputs Γ) -
          OrchardSpec.in_v_new (read_action_inputs Γ))
        (OrchardSpec.in_rcv (read_action_inputs Γ)).
  Proof.
    pose proof
      (TypedInputsValue64.in_v_old_64 Γ Hcircuit Hold_short) as Hv_old_64.
    pose proof
      (TypedInputsValue64.in_v_new_64 Γ Hcircuit Hnew_short)
      as Hv_new_64.
    pose proof (cv_net_commits_net_value Γ Hcircuit) as H.
    cbv zeta in H.
    destruct H as (Hcv & Hmod & Habs).
    assert (Hp :
        Primes.pallas_p =
        28948022309329048855892746252171976963363056481941560715954676764349967630337)
      by reflexivity.
    assert (Hpnz : Primes.pallas_p <> 0) by (rewrite Hp; discriminate).
    (* The difference of the two congruent values is a multiple of p. *)
    assert (Hdvd :
        (OrchardProtocolSpec.signed_net_value
           (OrchardSpec.in_magnitude (read_action_inputs Γ))
           (OrchardSpec.in_sign (read_action_inputs Γ)) -
         (OrchardSpec.in_v_old (read_action_inputs Γ) -
          OrchardSpec.in_v_new (read_action_inputs Γ)))
          mod Primes.pallas_p = 0).
    { rewrite Zminus_mod, Hmod, Z.sub_diag.
      apply Zmod_0_l. }
    pose proof (proj1 (Z.mod_divide _ _ Hpnz) Hdvd) as [k Hk].
    apply Z.abs_lt in Habs.
    (* A multiple of p smaller than 2⁶⁶ + 2⁶⁴ is zero. *)
    assert (H22 : 8 ^ 22 = 73786976294838206464) by reflexivity.
    assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite Hp in Hk.
    assert (Hveq :
        OrchardProtocolSpec.signed_net_value
          (OrchardSpec.in_magnitude (read_action_inputs Γ))
          (OrchardSpec.in_sign (read_action_inputs Γ)) =
        OrchardSpec.in_v_old (read_action_inputs Γ) -
          OrchardSpec.in_v_new (read_action_inputs Γ)).
    { clear -Hk Habs Hv_old_64 Hv_new_64 H22 H64. lia. }
    rewrite Hcv, Hveq.
    reflexivity.
  Qed.
End CvNetValue.
