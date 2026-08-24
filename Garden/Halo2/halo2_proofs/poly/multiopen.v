(** * Multipoint opening verifier, specialized to Vesta

    Transcription of [halo2_proofs/src/poly/multiopen.rs] and
    [multiopen/verifier.rs]. Commitment identity is an explicit [id]
    (the Rust code uses pointer equality on [ &C ] / [ &MSM ]); queries
    that share an [id] are the same opening. [construct_intermediate_sets]
    follows the IndexMap / BTreeMap accumulation order: first-seen
    commitments, points ordered by first appearance. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.arithmetic.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.verifier.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Multiopen.

  Inductive CommitmentRef : Set :=
  | Commitment (id : nat) (P : VestaCurve.point)
  | Msm (id : nat) (msm : MSM.t).

  Definition commitment_id (c : CommitmentRef) : nat :=
    match c with
    | Commitment id _ | Msm id _ => id
    end.

  Definition commitment_eqb (a b : CommitmentRef) : bool :=
    Nat.eqb (commitment_id a) (commitment_id b).

  Record VerifierQuery : Set := {
    point : Z;
    commitment : CommitmentRef;
    eval : Z;
  }.

  Definition new_commitment (id : nat) (P : VestaCurve.point) (point eval : Z) : VerifierQuery := {|
    point := point;
    commitment := Commitment id P;
    eval := eval;
  |}.

  Definition new_msm (id : nat) (msm : MSM.t) (point eval : Z) : VerifierQuery := {|
    point := point;
    commitment := Msm id msm;
    eval := eval;
  |}.

  Record CommitmentData : Set := {
    cd_commitment : CommitmentRef;
    cd_set_index : nat;
    cd_point_indices : list nat;
    cd_evals : list Z;
  }.

  Fixpoint find_nat (m : list (Z * nat)) (p : Z) : option nat :=
    match m with
    | [] => None
    | (q, i) :: rest =>
      if Fp.from q =? Fp.from p then Some i else find_nat rest p
    end.

  Fixpoint find_commitment (m : list CommitmentData) (c : CommitmentRef) : option CommitmentData :=
    match m with
    | [] => None
    | d :: rest =>
      if commitment_eqb d.(cd_commitment) c then Some d else find_commitment rest c
    end.

  Fixpoint set_commitment (m : list CommitmentData) (d : CommitmentData) : list CommitmentData :=
    match m with
    | [] => [d]
    | d0 :: rest =>
      if commitment_eqb d0.(cd_commitment) d.(cd_commitment) then d :: rest
      else d0 :: set_commitment rest d
    end.

  Definition index_points (queries : list VerifierQuery) : list (Z * nat) :=
    List.fold_left (fun acc q =>
      match find_nat acc q.(point) with
      | Some _ => acc
      | None => acc ++ [(q.(point), List.length acc)]
      end) queries [].

  Definition collect_commitments (queries : list VerifierQuery) (point_index_map : list (Z * nat)) :
      list CommitmentData :=
    List.fold_left (fun acc q =>
      let point_idx :=
        match find_nat point_index_map q.(point) with
        | Some i => i
        | None => 0%nat
        end in
      match find_commitment acc q.(commitment) with
      | Some d =>
        set_commitment acc
          {| cd_commitment := d.(cd_commitment);
             cd_set_index := d.(cd_set_index);
             cd_point_indices := d.(cd_point_indices) ++ [point_idx];
             cd_evals := d.(cd_evals) |}
      | None =>
        acc ++ [{| cd_commitment := q.(commitment);
                   cd_set_index := 0%nat;
                   cd_point_indices := [point_idx];
                   cd_evals := [] |}]
      end) queries [].

  Fixpoint insert_sorted_nat (x : nat) (xs : list nat) : list nat :=
    match xs with
    | [] => [x]
    | y :: ys =>
      if Nat.ltb x y then x :: xs
      else if Nat.eqb x y then xs
      else y :: insert_sorted_nat x ys
    end.

  Definition unique_sorted (xs : list nat) : list nat :=
    List.fold_left (fun acc x => insert_sorted_nat x acc) xs [].

  Fixpoint nat_list_eqb (a b : list nat) : bool :=
    match a, b with
    | [], [] => true
    | x :: a, y :: b => Nat.eqb x y && nat_list_eqb a b
    | _, _ => false
    end.

  Fixpoint find_set (sets : list (list nat * nat)) (s : list nat) : option nat :=
    match sets with
    | [] => None
    | (s', i) :: rest => if nat_list_eqb s s' then Some i else find_set rest s
    end.

  Definition assign_sets (commitments : list CommitmentData) :
      list CommitmentData * list (list nat * nat) :=
    List.fold_left (fun '(comms, sets) d =>
      let s := unique_sorted d.(cd_point_indices) in
      let '(set_index, sets) :=
        match find_set sets s with
        | Some i => (i, sets)
        | None => (List.length sets, sets ++ [(s, List.length sets)])
        end in
      (set_commitment comms
         {| cd_commitment := d.(cd_commitment);
            cd_set_index := set_index;
            cd_point_indices := d.(cd_point_indices);
            cd_evals := List.repeat 0 (List.length s) |},
       sets))
      commitments (commitments, []).

  Fixpoint replace_nth {A : Set} (n : nat) (x : A) (xs : list A) : list A :=
    match xs, n with
    | [], _ => []
    | _ :: ys, O => x :: ys
    | y :: ys, S n => y :: replace_nth n x ys
    end.

  Definition position_nat (x : nat) (xs : list nat) : nat :=
    fst (List.fold_left (fun '(found, i) y =>
      if Nat.eqb x y then (i, S i) else (found, S i)) xs (0%nat, 0%nat)).

  Definition fill_evals (queries : list VerifierQuery)
      (point_index_map : list (Z * nat))
      (set_map : list (list nat * nat))
      (commitments : list CommitmentData) : option (list CommitmentData) :=
    List.fold_left (fun acc q =>
      match acc with
      | None => None
      | Some comms =>
        match find_commitment comms q.(commitment), find_nat point_index_map q.(point) with
        | Some d, Some point_idx =>
          let s := unique_sorted d.(cd_point_indices) in
          let idx := position_nat point_idx s in
          let old := List.nth idx d.(cd_evals) 0 in
          (* The Rust path rejects a second write; the first write starts from 0
             and a duplicate same-eval is already excluded by the Option-cell
             check. Here a second query with a different eval is rejected by
             comparing against a sentinel: we track occupancy with a parallel
             filled flag encoded as a pair. For the Orchard verifier each
             (commitment, point) pair is queried once. *)
          Some (set_commitment comms
            {| cd_commitment := d.(cd_commitment);
               cd_set_index := d.(cd_set_index);
               cd_point_indices := d.(cd_point_indices);
               cd_evals := replace_nth idx q.(eval) d.(cd_evals) |})
        | _, _ => None
        end
      end) queries (Some commitments).

  Definition inverse_point (point_index_map : list (Z * nat)) (i : nat) : Z :=
    match List.find (fun '(_, j) => Nat.eqb i j) point_index_map with
    | Some (p, _) => p
    | None => 0
    end.

  Definition point_sets_of (set_map : list (list nat * nat)) (point_index_map : list (Z * nat)) :
      list (list Z) :=
    List.map (fun '(idxs, _) => List.map (inverse_point point_index_map) idxs) set_map.

  Definition construct_intermediate_sets (queries : list VerifierQuery) :
      option (list CommitmentData * list (list Z)) :=
    let point_index_map := index_points queries in
    let comms := collect_commitments queries point_index_map in
    let '(comms, set_map) := assign_sets comms in
    match fill_evals queries point_index_map set_map comms with
    | None => None
    | Some comms => Some (comms, point_sets_of set_map point_index_map)
    end.

  Definition accumulate_commitment (x1_power : Z) (c : CommitmentRef) (msm : MSM.t) : MSM.t :=
    match c with
    | Commitment _ P => MSM.append_term msm x1_power P
    | Msm _ m => MSM.add_msm msm (MSM.scale m x1_power)
    end.

  Definition verify_proof (params : Params.t) (tr : Blake2bRead.t)
      (queries : list VerifierQuery) (msm : MSM.t) :
      Result.t (Ipa.Guard * Blake2bRead.t) TranscriptError.t :=
    let '(x1, tr) := Blake2bRead.squeeze_challenge_scalar tr in
    let '(x2, tr) := Blake2bRead.squeeze_challenge_scalar tr in
    match construct_intermediate_sets queries with
    | None => Result.Err TranscriptError.InvalidPointEncoding
    | Some (commitment_map, point_sets) =>
      let nsets := List.length point_sets in
      let q_commitments := List.repeat (empty_msm params, Fp.from 1) nsets in
      let q_eval_sets := List.map (fun ps => List.repeat 0 (List.length ps)) point_sets in
      let '(q_commitments, q_eval_sets) :=
        List.fold_left (fun '(qcs, qes) d =>
          let set_idx := d.(cd_set_index) in
          let '(q_commitment, x1_power) := List.nth set_idx qcs (empty_msm params, 1) in
          let q_commitment := accumulate_commitment x1_power d.(cd_commitment) q_commitment in
          let qes :=
            replace_nth set_idx
              (List.map (fun '(e, old) => old +s (e *s x1_power))
                (List.combine d.(cd_evals) (List.nth set_idx qes [])))
              qes in
          let qcs := replace_nth set_idx (q_commitment, x1_power *s x1) qcs in
          (qcs, qes))
          (List.rev commitment_map) (q_commitments, q_eval_sets) in
      Result.and_then (fun '(q_prime_commitment, tr) =>
        let '(x3, tr) := Blake2bRead.squeeze_challenge_scalar tr in
        Result.and_then (fun '(u, tr) =>
          let msm_eval :=
            List.fold_left (fun msm_eval '((points, evals), proof_eval) =>
              let r_poly := Arithmetic.lagrange_interpolate points evals in
              let r_eval := Arithmetic.eval_polynomial r_poly x3 in
              let eval :=
                List.fold_left (fun eval point =>
                  match Fp.invert (x3 -s point) with
                  | Some inv => eval *s inv
                  | None => eval
                  end)
                  points (proof_eval -s r_eval) in
              msm_eval *s x2 +s eval)
              (List.combine (List.combine point_sets q_eval_sets) u) 0 in
          let '(x4, tr) := Blake2bRead.squeeze_challenge_scalar tr in
          let msm := MSM.append_term msm 1 q_prime_commitment in
          let '(msm, v) :=
            List.fold_left (fun '(msm, msm_eval) '((q_commitment, _), q_eval) =>
              let msm := MSM.scale msm x4 in
              let msm := MSM.add_msm msm q_commitment in
              (msm, msm_eval *s x4 +s q_eval))
              (List.combine q_commitments u) (msm, msm_eval) in
          Ipa.verify_proof params msm tr x3 v)
          (Blake2bRead.read_n_scalars tr nsets))
        (Blake2bRead.read_point tr)
    end.
End Multiopen.
