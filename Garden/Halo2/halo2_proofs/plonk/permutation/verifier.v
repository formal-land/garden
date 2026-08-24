(** * Permutation-argument verifier

    Transcription of [halo2_proofs/src/plonk/permutation/verifier.rs].
    Product-commitment chunks have length [cs_degree - 2]; expression
    and query lists follow the Rust iterator order. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.multiopen.
Require Import Garden.Halo2.halo2_proofs.plonk.

Import List.ListNotations.
Global Open Scope Z_scope.

Module PermutationVerifier.

  Record Committed : Set := {
    permutation_product_commitments : list VestaCurve.point;
  }.

  Record EvaluatedSet : Set := {
    permutation_product_commitment : VestaCurve.point;
    permutation_product_eval : Z;
    permutation_product_next_eval : Z;
    permutation_product_last_eval : option Z;
  }.

  Record CommonEvaluated : Set := {
    permutation_evals : list Z;
  }.

  Record Evaluated : Set := {
    sets : list EvaluatedSet;
  }.

  Fixpoint chunks_fuel {A : Set} (fuel n : nat) (l : list A) : list (list A) :=
    match fuel, l with
    | O, _ | _, [] =>
      match l with
      | [] => []
      | _ => [l]
      end
    | S fuel, _ =>
      match n with
      | O => [l]
      | S _ => List.firstn n l :: chunks_fuel fuel n (List.skipn n l)
      end
    end.

  Definition chunks {A : Set} (n : nat) (l : list A) : list (list A) :=
    chunks_fuel (List.length l) n l.

  Definition read_product_commitments (vk : VerifyingKey.t) (tr : Blake2bRead.t) :
      Result.t (Committed * Blake2bRead.t) TranscriptError.t :=
    let chunk_len := Nat.pred (Nat.pred (Integer.to_nat vk.(VerifyingKey.cs_degree))) in
    let n := List.length (chunks chunk_len vk.(VerifyingKey.cs).(ConstraintSystem.permutation).(PermutationArgument.columns)) in
    Result.and_then (fun '(ps, tr) =>
      Result.Ok ({| permutation_product_commitments := ps |}, tr))
      (Blake2bRead.read_n_points tr n).

  Definition evaluate_common (vk : VerifyingKey.t) (tr : Blake2bRead.t) :
      Result.t (CommonEvaluated * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(ss, tr) =>
      Result.Ok ({| permutation_evals := ss |}, tr))
      (Blake2bRead.read_n_scalars tr
        (List.length vk.(VerifyingKey.permutation).(PermutationVK.commitments))).

  Fixpoint evaluate_sets (comms : list VestaCurve.point) (tr : Blake2bRead.t) :
      Result.t (list EvaluatedSet * Blake2bRead.t) TranscriptError.t :=
    match comms with
    | [] => Result.Ok ([], tr)
    | c :: rest =>
      Result.and_then (fun '(pev, tr) =>
      Result.and_then (fun '(pnext, tr) =>
        let read_last :=
          match rest with
          | [] => Result.Ok (None, tr)
          | _ => Result.and_then (fun '(s, tr) => Result.Ok (Some s, tr))
                   (Blake2bRead.read_scalar tr)
          end in
        Result.and_then (fun '(plast, tr) =>
        Result.and_then (fun '(sets, tr) =>
          Result.Ok
            ({| permutation_product_commitment := c;
                permutation_product_eval := pev;
                permutation_product_next_eval := pnext;
                permutation_product_last_eval := plast |} :: sets, tr))
          (evaluate_sets rest tr))
          read_last)
        (Blake2bRead.read_scalar tr))
        (Blake2bRead.read_scalar tr)
    end.

  Definition evaluate (self : Committed) (tr : Blake2bRead.t) :
      Result.t (Evaluated * Blake2bRead.t) TranscriptError.t :=
    Result.and_then (fun '(sets, tr) =>
      Result.Ok ({| sets := sets |}, tr))
      (evaluate_sets self.(permutation_product_commitments) tr).

  Definition column_eval (vk : VerifyingKey.t)
      (advice_evals fixed_evals instance_evals : list Z) (column : Column.t) : Z :=
    let i := ConstraintSystem.get_any_query_index vk.(VerifyingKey.cs) column in
    match column.(Column.column_type) with
    | ColumnType.Advice => Vec.nth (A := Z) advice_evals i
    | ColumnType.Fixed => Vec.nth (A := Z) fixed_evals i
    | ColumnType.Instance => Vec.nth (A := Z) instance_evals i
    end.

  Definition expressions (self : Evaluated) (vk : VerifyingKey.t)
      (p : PermutationArgument.t) (common : CommonEvaluated)
      (advice_evals fixed_evals instance_evals : list Z)
      (l_0 l_last l_blind beta gamma x : Z) : list Z :=
    let chunk_len := Nat.pred (Nat.pred (Integer.to_nat vk.(VerifyingKey.cs_degree))) in
    let first :=
      match self.(sets) with
      | [] => []
      | s :: _ => [l_0 *s (1 -s s.(permutation_product_eval))]
      end in
    let last :=
      match List.rev self.(sets) with
      | [] => []
      | s :: _ =>
        [((s.(permutation_product_eval) *s s.(permutation_product_eval)
            -s s.(permutation_product_eval)) *s l_last)]
      end in
    let chaining :=
      match self.(sets) with
      | [] => []
      | s0 :: rest =>
        fst (List.fold_left (fun '(acc, prev) set =>
          let expr :=
            match prev.(permutation_product_last_eval) with
            | Some prev_last => (set.(permutation_product_eval) -s prev_last) *s l_0
            | None => 0
            end in
          (acc ++ [expr], set)) rest ([], s0))
      end in
    let column_chunks := chunks chunk_len p.(PermutationArgument.columns) in
    let eval_chunks := chunks chunk_len common.(permutation_evals) in
    let main :=
      fst (List.fold_left (fun '(acc, chunk_index) '((set, columns), permutation_evals) =>
        let left :=
          List.fold_left (fun left '(column, permutation_eval) =>
            let eval := column_eval vk advice_evals fixed_evals instance_evals column in
            left *s (eval +s (beta *s permutation_eval) +s gamma))
            (List.combine columns permutation_evals)
            set.(permutation_product_next_eval) in
        let current_delta0 :=
          (beta *s x) *s Fp.pow_vartime Fp.DELTA
            (Z.of_nat (chunk_index * chunk_len)%nat) in
        let '(_, rhs) :=
          List.fold_left (fun '(current_delta, rhs) column =>
            let eval := column_eval vk advice_evals fixed_evals instance_evals column in
            (current_delta *s Fp.DELTA,
             rhs *s (eval +s current_delta +s gamma)))
            columns (current_delta0, set.(permutation_product_eval)) in
        (acc ++ [(left -s rhs) *s (1 -s (l_last +s l_blind))], S chunk_index))
        (List.combine (List.combine self.(sets) column_chunks) eval_chunks)
        ([], 0%nat)) in
    first ++ last ++ chaining ++ main.

  Definition queries (self : Evaluated) (vk : VerifyingKey.t) (x : Z)
      (id_base : nat) : list Multiopen.VerifierQuery :=
    let blinding := Integer.to_nat vk.(VerifyingKey.cs).(ConstraintSystem.blinding_factors) in
    let x_next := EvaluationDomain.rotate_omega vk.(VerifyingKey.domain) x Rotation.next in
    let x_last := EvaluationDomain.rotate_omega vk.(VerifyingKey.domain) x
      (- Z.of_nat (S blinding)) in
    let at_x_and_next :=
      fst (List.fold_left (fun '(acc, i) set =>
        (acc ++
          [ Multiopen.new_commitment (id_base + i)
              set.(permutation_product_commitment) x set.(permutation_product_eval);
            Multiopen.new_commitment (id_base + i)
              set.(permutation_product_commitment) x_next set.(permutation_product_next_eval) ],
         S i)) self.(sets) ([], 0%nat)) in
    let numbered := List.combine (List.seq 0 (List.length self.(sets))) self.(sets) in
    let at_last :=
      List.fold_left (fun acc '(i, set) =>
        match set.(permutation_product_last_eval) with
        | Some last_eval =>
          acc ++ [Multiopen.new_commitment (id_base + i)
                    set.(permutation_product_commitment) x_last last_eval]
        | None => acc
        end)
        (List.tl (List.rev numbered)) [] in
    at_x_and_next ++ at_last.

  Definition common_queries (common : CommonEvaluated) (vk : VerifyingKey.t) (x : Z)
      (id_base : nat) : list Multiopen.VerifierQuery :=
    fst (List.fold_left (fun '(acc, i) '(commitment, eval) =>
      (acc ++ [Multiopen.new_commitment (id_base + i) commitment x eval], S i))
      (List.combine vk.(VerifyingKey.permutation).(PermutationVK.commitments)
         common.(permutation_evals))
      ([], 0%nat)).
End PermutationVerifier.
