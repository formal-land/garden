(** * Inner-product argument verifier, specialized to Vesta

    Transcription of [halo2_proofs/src/poly/commitment/verifier.rs]:
    [compute_b], [compute_s], [Guard.use_challenges], and [verify_proof].
    The [k] IPA rounds and the [batch_invert] of the [u_j] are recursive
    functions; [compute_s] builds the coefficient vector without
    [split_at_mut]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Ipa.

  (** [prod_{i=0}^{k-1} (1 + u_{k-1-i} x^{2^i})]. *)
  Fixpoint compute_b_rec (tmp cur : Z) (u_rev : list Z) : Z :=
    match u_rev with
    | [] => tmp
    | u_j :: rest =>
      let tmp := tmp *s (1 +s (u_j *s cur)) in
      compute_b_rec tmp (cur *s cur) rest
    end.

  Definition compute_b (x : Z) (u : list Z) : Z :=
    compute_b_rec 1 x (List.rev u).

  (** Coefficients of [g(X) = prod (1 + u_{k-1-i} X^{2^i})], scaled by [init]. *)
  Fixpoint compute_s_rec (v : list Z) (u_rev : list Z) : list Z :=
    match u_rev with
    | [] => v
    | u_j :: rest =>
      let left := v in
      let right := List.map (fun x => x *s u_j) v in
      compute_s_rec (left ++ right) rest
    end.

  Definition compute_s (u : list Z) (init : Z) : list Z :=
    match u with
    | [] => []
    | _ => compute_s_rec [init] (List.rev u)
    end.

  Record Guard : Set := {
    msm : MSM.t;
    neg_c : Z;
    u : list Z;
  }.

  Definition use_challenges (g : Guard) : MSM.t :=
    let s := compute_s g.(u) g.(neg_c) in
    MSM.add_to_g_scalars g.(msm) s.

  Record Round : Set := {
    l : VestaCurve.point;
    r : VestaCurve.point;
    u_j : Z;
    u_j_inv : Z;
  }.

  Fixpoint read_rounds (tr : Blake2bRead.t) (k : nat) :
      Result.t (list (VestaCurve.point * VestaCurve.point * Z * Challenge255.t) * Blake2bRead.t)
               TranscriptError.t :=
    match k with
    | O => Result.Ok ([], tr)
    | S k =>
      Result.and_then (fun '(l, tr) =>
      Result.and_then (fun '(r, tr) =>
        let '(u_packed, tr) := Blake2bRead.squeeze_challenge tr in
        let u_j := Challenge255.get_scalar u_packed in
        Result.and_then (fun '(rest, tr) =>
          Result.Ok ((l, r, u_j, u_packed) :: rest, tr))
          (read_rounds tr k))
        (Blake2bRead.read_point tr))
        (Blake2bRead.read_point tr)
    end.

  Definition invert_u (rounds : list (VestaCurve.point * VestaCurve.point * Z * Challenge255.t)) :
      list Round :=
    List.map (fun '(l, r, u_j, _) =>
      {| l := l; r := r; u_j := u_j;
         u_j_inv := match Fp.invert u_j with Some i => i | None => 0 end |})
      rounds.

  Definition verify_proof (params : Params.t) (msm : MSM.t)
      (tr : Blake2bRead.t) (x v : Z) :
      Result.t (Guard * Blake2bRead.t) TranscriptError.t :=
    let k := Integer.to_nat params.(Params.k) in
    let msm := MSM.add_constant_term msm (Fp.opp v) in
    Result.and_then (fun '(s_poly_commitment, tr) =>
      let '(xi, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      let msm := MSM.append_term msm xi s_poly_commitment in
      let '(z, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      Result.and_then (fun '(rounds, tr) =>
        let rounds := invert_u rounds in
        let '(msm, u) :=
          List.fold_left (fun '(msm, u) rnd =>
            let msm := MSM.append_term msm rnd.(u_j_inv) rnd.(l) in
            let msm := MSM.append_term msm rnd.(u_j) rnd.(r) in
            (msm, u ++ [rnd.(u_j)]))
            rounds (msm, []) in
        Result.and_then (fun '(c, tr) =>
          let neg_c := Fp.opp c in
          Result.and_then (fun '(f, tr) =>
            let b := compute_b x u in
            let msm := MSM.add_to_u_scalar msm (neg_c *s b *s z) in
            let msm := MSM.add_to_w_scalar msm (Fp.opp f) in
            Result.Ok
              ({| msm := msm; neg_c := neg_c; u := u |}, tr))
            (Blake2bRead.read_scalar tr))
          (Blake2bRead.read_scalar tr))
        (read_rounds tr k))
      (Blake2bRead.read_point tr).
End Ipa.

Module IpaTests.
  Lemma compute_b_empty : Ipa.compute_b 3 [] = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma compute_s_one :
    Ipa.compute_s [2] 1 = [1; 2].
  Proof. vm_compute. reflexivity. Qed.

  Lemma compute_s_two :
    let s := Ipa.compute_s [3; 5] 1 in
    List.length s = 4%nat.
  Proof. vm_compute. reflexivity. Qed.
End IpaTests.
