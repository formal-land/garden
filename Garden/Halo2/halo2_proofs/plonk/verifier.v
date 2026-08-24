(** * Plonk [verify_proof], specialized to Vesta + Blake2b + SingleVerifier

    Transcription of [halo2_proofs/src/plonk/verifier.rs]. Instance
    commitments, Fiat–Shamir reads, the Horner combination of gate /
    permutation / lookup expressions, the vanishing check, the opening
    query set, and [SingleVerifier] (evaluate the IPA MSM). Loops over
    proofs and lookups are recursive functions. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.verifier.
Require Import Garden.Halo2.halo2_proofs.poly.multiopen.
Require Import Garden.Halo2.halo2_proofs.plonk.
Require Import Garden.Halo2.halo2_proofs.plonk.vanishing.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.permutation.verifier.
Require Import Garden.Halo2.halo2_proofs.plonk.lookup.verifier.

Import List.ListNotations.
Global Open Scope Z_scope.

Module PlonkVerifier.

  Definition map_result {A B E : Set} (f : A -> Result.t B E) :=
    fix go (xs : list A) : Result.t (list B) E :=
      match xs with
      | [] => Result.Ok []
      | x :: xs =>
        Result.and_then (fun y => Result.map (fun ys => y :: ys) (go xs)) (f x)
      end.

  Definition fold_result {A B E : Set} (f : B -> A -> Result.t B E) :=
    fix go (xs : list A) (acc : B) : Result.t B E :=
      match xs with
      | [] => Result.Ok acc
      | x :: xs => Result.and_then (go xs) (f acc x)
      end.

  Definition repeat_read {A : Set}
      (read : Blake2bRead.t -> Result.t (A * Blake2bRead.t) TranscriptError.t) :=
    fix go (k : nat) (tr : Blake2bRead.t) :
        Result.t (list A * Blake2bRead.t) TranscriptError.t :=
      match k with
      | O => Result.Ok ([], tr)
      | S k =>
        Result.and_then (fun '(x, tr) =>
          Result.map (fun '(xs, tr) => (x :: xs, tr)) (go k tr))
          (read tr)
      end.

  Definition of_tr {A : Set} (r : Result.t A TranscriptError.t) : Result.t A Error.t :=
    Result.map_err Error.of_transcript r.

  Definition pad_instance (n : nat) (instance : list Z) : Result.t (list Z) Error.t :=
    if Nat.ltb n (List.length instance) then Result.Err Error.InstanceTooLarge
    else Result.Ok (instance ++ List.repeat 0 (n - List.length instance)%nat).

  Definition commit_one_instance (params : Params.t) (cols : list (list Z)) :
      Result.t (list VestaCurve.point) Error.t :=
    let n := Integer.to_nat params.(Params.n) in
    map_result (fun col =>
      Result.map (fun padded => commit_lagrange params padded 0)
        (pad_instance n col)) cols.

  Definition commit_instances (params : Params.t) (instances : list (list (list Z))) :
      Result.t (list (list VestaCurve.point)) Error.t :=
    map_result (commit_one_instance params) instances.

  Definition hash_points (tr : Blake2bRead.t) (ps : list VestaCurve.point) :
      Result.t Blake2bRead.t TranscriptError.t :=
    fold_result (fun tr P => Blake2bRead.common_point tr P) ps tr.

  Definition hash_instance_commitments (tr : Blake2bRead.t)
      (instance_commitments : list (list VestaCurve.point)) :
      Result.t Blake2bRead.t TranscriptError.t :=
    fold_result hash_points instance_commitments tr.

  Definition check_instance_widths (vk : VerifyingKey.t)
      (instances : list (list (list Z))) : Result.t unit Error.t :=
    let expected := Integer.to_nat vk.(VerifyingKey.cs).(ConstraintSystem.num_instance_columns) in
    if List.forallb (fun inst => Nat.eqb (List.length inst) expected) instances
    then Result.Ok tt
    else Result.Err Error.InvalidInstances.

  Definition gate_expressions (gates : list (list Expression.t))
      (advice_evals fixed_evals instance_evals : list Z) : list Z :=
    List.flat_map (fun polys =>
      List.map (fun e => Expression.evaluate e fixed_evals advice_evals instance_evals) polys)
      gates.

  Definition proof_expressions
      (vk : VerifyingKey.t)
      (advice_evals instance_evals fixed_evals : list Z)
      (perm : PermutationVerifier.Evaluated)
      (perm_common : PermutationVerifier.CommonEvaluated)
      (lookups : list LookupVerifier.Evaluated)
      (l_0 l_last l_blind theta beta gamma x : Z) : list Z :=
    gate_expressions vk.(VerifyingKey.cs).(ConstraintSystem.gates)
      advice_evals fixed_evals instance_evals
    ++ PermutationVerifier.expressions perm vk
         vk.(VerifyingKey.cs).(ConstraintSystem.permutation)
         perm_common advice_evals fixed_evals instance_evals
         l_0 l_last l_blind beta gamma x
    ++ List.flat_map (fun '(ev, arg) =>
         LookupVerifier.expressions ev arg l_0 l_last l_blind theta beta gamma
           advice_evals fixed_evals instance_evals)
         (List.combine lookups vk.(VerifyingKey.cs).(ConstraintSystem.lookups)).

  Definition queries_for_columns (vk : VerifyingKey.t)
      (qs : list (Column.t * Rotation.t))
      (comms : list VestaCurve.point) (evals : list Z) (x : Z) (id_base : nat) :
      list Multiopen.VerifierQuery :=
    fst (List.fold_left (fun '(acc, qi) '((column, rot), ev) =>
      let P := List.nth (Integer.to_nat column.(Column.index)) comms VestaCurve.Infinity in
      let xi := EvaluationDomain.rotate_omega vk.(VerifyingKey.domain) x rot in
      (acc ++ [Multiopen.new_commitment (id_base + Integer.to_nat column.(Column.index))
                 P xi ev], S qi))
      (List.combine qs evals) ([], 0%nat)).

  Definition lookup_queries_all (vk : VerifyingKey.t)
      (lookups : list LookupVerifier.Evaluated) (x : Z) (id_base : nat) :
      list Multiopen.VerifierQuery :=
    fst (List.fold_left (fun '(acc, i) ev =>
      let prod_id := (id_base + 3 * i)%nat in
      (acc ++ LookupVerifier.queries ev vk x prod_id (S prod_id) (S (S prod_id)),
       S i)) lookups ([], 0%nat)).

  Definition read_lookups_committed
      (perms : list LookupVerifier.PermutationCommitments) (tr : Blake2bRead.t) :
      Result.t (list LookupVerifier.Committed * Blake2bRead.t) TranscriptError.t :=
    fold_result (fun '(acc, tr) p =>
      Result.map (fun '(c, tr) => (acc ++ [c], tr))
        (LookupVerifier.read_product_commitment p tr))
      perms ([], tr).

  Definition evaluate_lookups
      (comms : list LookupVerifier.Committed) (tr : Blake2bRead.t) :
      Result.t (list LookupVerifier.Evaluated * Blake2bRead.t) TranscriptError.t :=
    fold_result (fun '(acc, tr) c =>
      Result.map (fun '(e, tr) => (acc ++ [e], tr))
        (LookupVerifier.evaluate c tr))
      comms ([], tr).

  Definition nth_or {A : Set} (i : nat) (xs : list A) (d : A) : A :=
    List.nth i xs d.

  Definition expressions_for_all_proofs
      (vk : VerifyingKey.t)
      (advice_evals instance_evals : list (list Z))
      (fixed_evals : list Z)
      (perms : list PermutationVerifier.Evaluated)
      (perm_common : PermutationVerifier.CommonEvaluated)
      (lookups : list (list LookupVerifier.Evaluated))
      (l_0 l_last l_blind theta beta gamma x : Z) : list Z :=
    let n := List.length advice_evals in
    List.concat
      (List.map (fun i =>
        proof_expressions vk
          (nth_or i advice_evals [])
          (nth_or i instance_evals [])
          fixed_evals
          (nth_or i perms {| PermutationVerifier.sets := [] |})
          perm_common
          (nth_or i lookups [])
          l_0 l_last l_blind theta beta gamma x)
        (List.seq 0 n)).

  Definition queries_for_all_proofs
      (vk : VerifyingKey.t)
      (instance_commitments : list (list VestaCurve.point))
      (instance_evals : list (list Z))
      (advice_commitments : list (list VestaCurve.point))
      (advice_evals : list (list Z))
      (perms : list PermutationVerifier.Evaluated)
      (lookups : list (list LookupVerifier.Evaluated))
      (x : Z) : list Multiopen.VerifierQuery :=
    let n := List.length instance_commitments in
    List.concat
      (List.map (fun i =>
        queries_for_columns vk vk.(VerifyingKey.cs).(ConstraintSystem.instance_queries)
          (nth_or i instance_commitments []) (nth_or i instance_evals [])
          x (1000 + 100 * i)%nat
        ++ queries_for_columns vk vk.(VerifyingKey.cs).(ConstraintSystem.advice_queries)
             (nth_or i advice_commitments []) (nth_or i advice_evals [])
             x (2000 + 100 * i)%nat
        ++ PermutationVerifier.queries
             (nth_or i perms {| PermutationVerifier.sets := [] |})
             vk x (3000 + 100 * i)%nat
        ++ lookup_queries_all vk (nth_or i lookups []) x (4000 + 100 * i)%nat)
        (List.seq 0 n)).

  Definition rotations_l_i (blinding : nat) : list Z :=
    (* Inclusive range [-(blinding+1), 0]. *)
    List.map (fun i => - Z.of_nat (S blinding - i)) (List.seq 0 (S (S blinding))).

  Definition finalize
      (params : Params.t) (vk : VerifyingKey.t) (tr : Blake2bRead.t)
      (instance_commitments : list (list VestaCurve.point))
      (advice_commitments : list (list VestaCurve.point))
      (instance_evals advice_evals : list (list Z))
      (fixed_evals : list Z)
      (perms : list PermutationVerifier.Evaluated)
      (perm_common : PermutationVerifier.CommonEvaluated)
      (lookups : list (list LookupVerifier.Evaluated))
      (vanishing : VanishingVerifier.PartiallyEvaluated)
      (theta beta gamma y x : Z) : Result.t unit Error.t :=
    let xn := Fp.pow_vartime x params.(Params.n).(Integer.value) in
    let blinding := Integer.to_nat vk.(VerifyingKey.cs).(ConstraintSystem.blinding_factors) in
    let l_evals := EvaluationDomain.l_i_range vk.(VerifyingKey.domain) x xn
      (rotations_l_i blinding) in
    let l_last := nth_or 0%nat l_evals 0 in
    let l_blind :=
      List.fold_left (fun acc e => acc +s e)
        (List.firstn blinding (List.skipn 1%nat l_evals)) 0 in
    let l_0 := nth_or (S blinding) l_evals 0 in
    let exprs :=
      expressions_for_all_proofs vk advice_evals instance_evals fixed_evals
        perms perm_common lookups l_0 l_last l_blind theta beta gamma x in
    let vanishing := VanishingVerifier.verify vanishing params exprs y xn in
    let queries :=
      queries_for_all_proofs vk instance_commitments instance_evals
        advice_commitments advice_evals perms lookups x
      ++ queries_for_columns vk vk.(VerifyingKey.cs).(ConstraintSystem.fixed_queries)
           vk.(VerifyingKey.fixed_commitments) fixed_evals x 5000%nat
      ++ PermutationVerifier.common_queries perm_common vk x 6000%nat
      ++ VanishingVerifier.queries vanishing x 7000%nat 7001%nat in
    Result.and_then (fun '(guard, _) =>
      let msm := Ipa.use_challenges guard in
      if MSM.eval msm then Result.Ok tt else Result.Err Error.ConstraintSystemFailure)
      (of_tr (Multiopen.verify_proof params tr queries (empty_msm params))).

  Definition verify_proof (params : Params.t) (vk : VerifyingKey.t)
      (instances : list (list (list Z))) (tr0 : Blake2bRead.t) : Result.t unit Error.t :=
    Result.and_then (fun _ =>
    Result.and_then (fun instance_commitments =>
      let num_proofs := List.length instance_commitments in
      let tr := VerifyingKey.hash_into vk tr0 in
      Result.and_then (fun tr =>
      let nadv := Integer.to_nat vk.(VerifyingKey.cs).(ConstraintSystem.num_advice_columns) in
      Result.and_then (fun '(advice_commitments, tr) =>
      let '(theta, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      let nlook := List.length vk.(VerifyingKey.cs).(ConstraintSystem.lookups) in
      Result.and_then (fun '(lookups_permuted, tr) =>
      let '(beta, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      let '(gamma, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      Result.and_then (fun '(permutations_committed, tr) =>
      Result.and_then (fun '(lookups_committed, tr) =>
      Result.and_then (fun '(van0, tr) =>
      let '(y, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      Result.and_then (fun '(van1, tr) =>
      let '(x, tr) := Blake2bRead.squeeze_challenge_scalar tr in
      let n_inst_q := List.length vk.(VerifyingKey.cs).(ConstraintSystem.instance_queries) in
      let n_adv_q := List.length vk.(VerifyingKey.cs).(ConstraintSystem.advice_queries) in
      let n_fix_q := List.length vk.(VerifyingKey.cs).(ConstraintSystem.fixed_queries) in
      Result.and_then (fun '(instance_evals, tr) =>
      Result.and_then (fun '(advice_evals, tr) =>
      Result.and_then (fun '(fixed_evals, tr) =>
      Result.and_then (fun '(van2, tr) =>
      Result.and_then (fun '(perm_common, tr) =>
      Result.and_then (fun '(perms_ev, tr) =>
      Result.and_then (fun '(lookups_ev, tr) =>
        finalize params vk tr instance_commitments advice_commitments
          instance_evals advice_evals fixed_evals
          perms_ev perm_common lookups_ev van2
          theta beta gamma y x)
        (of_tr (fold_result (fun '(acc, tr) cs =>
          Result.map (fun '(es, tr) => (acc ++ [es], tr))
            (evaluate_lookups cs tr)) lookups_committed ([], tr))))
        (of_tr (fold_result (fun '(acc, tr) c =>
          Result.map (fun '(e, tr) => (acc ++ [e], tr))
            (PermutationVerifier.evaluate c tr)) permutations_committed ([], tr))))
        (of_tr (PermutationVerifier.evaluate_common vk tr)))
        (of_tr (VanishingVerifier.evaluate_after_x van1 tr)))
        (of_tr (Blake2bRead.read_n_scalars tr n_fix_q)))
        (of_tr (repeat_read (fun tr => Blake2bRead.read_n_scalars tr n_adv_q) num_proofs tr)))
        (of_tr (repeat_read (fun tr => Blake2bRead.read_n_scalars tr n_inst_q) num_proofs tr)))
        (of_tr (VanishingVerifier.read_commitments_after_y van0 vk tr)))
        (of_tr (VanishingVerifier.read_commitments_before_y tr)))
        (of_tr (fold_result (fun '(acc, tr) ps =>
          Result.map (fun '(cs, tr) => (acc ++ [cs], tr))
            (read_lookups_committed ps tr)) lookups_permuted ([], tr))))
        (of_tr (repeat_read (PermutationVerifier.read_product_commitments vk) num_proofs tr)))
        (of_tr (repeat_read (repeat_read LookupVerifier.read_permuted_commitments nlook) num_proofs tr)))
        (of_tr (repeat_read (fun tr => Blake2bRead.read_n_points tr nadv) num_proofs tr)))
        (of_tr (hash_instance_commitments tr instance_commitments)))
      (commit_instances params instances))
      (check_instance_widths vk instances).
End PlonkVerifier.
