(** * Halo inner-product opening verifier

    This is the executable core of [poly/commitment/verifier.rs] after proof
    values have been read from the transcript.  The guard deliberately omits
    the [-c]G'_0 term until [use_challenges], matching the Rust API. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Commitment.

Import ListNotations.
Local Open Scope Z_scope.

Module IpaVerifier.

Module F := VerifierField.
Module C := CommitmentVerifier.

Record round : Type := {
  round_l : C.point;
  round_r : C.point;
  round_u : F.t;
}.

Record proof : Type := {
  s_poly_commitment : C.point;
  xi : F.t;
  z : F.t;
  rounds : list round;
  c : F.t;
  f : F.t;
}.

Record guard : Type := {
  guard_msm : C.msm;
  guard_neg_c : F.t;
  guard_u : list F.t;
}.

Inductive ipa_panic : Type :=
| IpaMsmPanic (failure : C.msm_panic)
| EmptyChallengeVector.

Inductive verify_result : Type :=
| IpaGuard (value : guard)
| IpaPanicked (failure : ipa_panic).

Fixpoint compute_b_from (current accumulator : F.t) (reversed_u : list F.t) :
    F.t :=
  match reversed_u with
  | [] => accumulator
  | u :: reversed_u' =>
      compute_b_from (F.square current)
        (F.mul accumulator (F.add F.one (F.mul u current))) reversed_u'
  end.

Definition compute_b (x : F.t) (u : list F.t) : F.t :=
  compute_b_from x F.one (rev u).

Definition expand_s_step (u : F.t) (values : list F.t) : list F.t :=
  values ++ map (F.mul u) values.

Definition compute_s (u : list F.t) (initial : F.t) : option (list F.t) :=
  match u with
  | [] => None
  | _ => Some (fold_right expand_s_step [initial] u)
  end.

Definition inverse_or_zero (u : F.t) : F.t :=
  match F.invert u with Some inverse => inverse | None => F.zero end.

Fixpoint append_rounds (rounds : list round) (state : C.msm) : verify_result :=
  match rounds with
  | [] => IpaGuard {|
      guard_msm := state;
      guard_neg_c := F.zero;
      guard_u := []
    |}
  | round :: rounds' =>
      match C.append_term (inverse_or_zero round.(round_u)) round.(round_l) state with
      | C.MsmPanicked failure => IpaPanicked (IpaMsmPanic failure)
      | C.MsmOk with_l =>
          match C.append_term round.(round_u) round.(round_r) with_l with
          | C.MsmPanicked failure => IpaPanicked (IpaMsmPanic failure)
          | C.MsmOk with_r =>
              match append_rounds rounds' with_r with
              | IpaPanicked failure => IpaPanicked failure
              | IpaGuard tail => IpaGuard {|
                  guard_msm := tail.(guard_msm);
                  guard_neg_c := F.zero;
                  guard_u := round.(round_u) :: tail.(guard_u)
                |}
              end
          end
      end
  end.

Definition verify (x claimed_value : F.t) (opening : proof) (state : C.msm) :
    verify_result :=
  match C.add_constant_term (F.opp claimed_value) state with
  | C.MsmPanicked failure => IpaPanicked (IpaMsmPanic failure)
  | C.MsmOk with_value =>
      match C.append_term opening.(xi) opening.(s_poly_commitment) with_value with
      | C.MsmPanicked failure => IpaPanicked (IpaMsmPanic failure)
      | C.MsmOk with_s =>
          match append_rounds opening.(rounds) with_s with
          | IpaPanicked failure => IpaPanicked failure
          | IpaGuard partial =>
              let neg_c := F.opp opening.(c) in
              let b := compute_b x partial.(guard_u) in
              IpaGuard {|
                guard_msm :=
                  C.add_to_w_scalar (F.opp opening.(f))
                    (C.add_to_u_scalar
                      (F.mul (F.mul neg_c b) opening.(z)) partial.(guard_msm));
                guard_neg_c := neg_c;
                guard_u := partial.(guard_u)
              |}
          end
      end
  end.

Definition use_challenges (value : guard) : verify_result :=
  match compute_s value.(guard_u) value.(guard_neg_c) with
  | None => IpaPanicked EmptyChallengeVector
  | Some scalars =>
      match C.add_to_g_scalars scalars value.(guard_msm) with
      | C.MsmPanicked failure => IpaPanicked (IpaMsmPanic failure)
      | C.MsmOk state => IpaGuard {|
          guard_msm := state;
          guard_neg_c := value.(guard_neg_c);
          guard_u := value.(guard_u)
        |}
      end
  end.

End IpaVerifier.
