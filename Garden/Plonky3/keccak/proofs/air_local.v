Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.proofs.air_small_parts.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

(** In this definition, we group all the constraints about the current [local] row. *)
Definition eval_local {p} `{Prime p} (SQUARE_SIZE : Z) (local : KeccakCols.t) : M.t unit :=
  let* _ := preimage_a.eval SQUARE_SIZE local in
  let* _ := export_bool.eval local in
  let* _ := export_zero.eval local in
  let* _ := c_c_prime.eval SQUARE_SIZE local in
  let* _ := a_a_prime_c_c_prime.eval SQUARE_SIZE local in
  let* _ := a_prime_c_prime.eval SQUARE_SIZE local in
  let* _ := a_prime_prime.eval SQUARE_SIZE local in
  let* _ := a_prime_prime_0_0_bits_bools.eval local in
  let* _ := a_prime_prime_0_0_limbs.eval local in
  let* _ := a_prime_prime_prime_0_0_limbs.eval local in
  M.pure tt.

Require Import Plonky3.MExpr.

Module Trace.
  Module Event.
    Inductive t : Set :=
    | AssertZero (expr : Z).

    Definition map_condition {p} `{Prime p} (condition : Z) (event : t) : t :=
      match event with
      | AssertZero expr => AssertZero (condition *F expr)
      end.
  End Event.

  Definition t : Set := list Event.t.
End Trace.

Fixpoint to_trace {p} `{Prime p} {A : Set} (e : M.t A) : A * Trace.t :=
  match e with
  | M.Pure value => (value, [])
  | M.AssertZero expr value => (value, [Trace.Event.AssertZero expr])
  | M.Call e => to_trace e
  | M.Let e k =>
    let '(value_e, trace_e) := to_trace e in
    let '(value_k, trace_k) := to_trace (k value_e) in
    (value_k, trace_e ++ trace_k)
  | M.When condition e =>
    let '(value_e, trace_e) := to_trace e in
    (value_e, List.map (Trace.Event.map_condition condition) trace_e)
  end.

Ltac to_expr e :=
  lazymatch e with
  | MGenerate.Var ?index => constr:(Expr.var index)
  | UnOp.opp ?x =>
    let x := to_expr x in
    constr:(Expr.Neg x)
  | BinOp.add ?x ?y =>
    let x := to_expr x in
    let y := to_expr y in
    constr:(Expr.Add x y)
  | BinOp.sub ?x ?y =>
    let x := to_expr x in
    let y := to_expr y in
    constr:(Expr.Sub x y)
  | BinOp.mul ?x ?y =>
    let x := to_expr x in
    let y := to_expr y in
    constr:(Expr.Mul x y)
  | ?z => constr:(Expr.constant z)
  end.

Ltac to_mexpr_trace_aux trace :=
  lazymatch trace with
  | List.nil => constr:(List.nil (A := MExpr.Trace.Event.t))
  | List.cons ?event ?trace =>
    lazymatch event with
    | Trace.Event.AssertZero ?expr =>
      let expr := to_expr expr in
      let trace := to_mexpr_trace_aux trace in
      constr:(List.cons (MExpr.Trace.Event.AssertZero expr) trace)
    end
  end.

Ltac to_mexpr_trace e :=
  let v := fresh "v" in
  pose e as v;
  (
    with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
    with_strategy transparent [M.for_in_zero_to_n]
      cbv in v
  );
  lazymatch eval unfold v in v with
  | ?e =>
    let result := to_mexpr_trace_aux e in
    exact result
  end.

Goal forall {p} `{Prime p}, True.
Proof.
  intros.
  set (pre := to_trace (export_bool.eval (MGenerate.eval MGenerate.generate))).
  (* set (all := to_trace (eval_local 1 (MGenerate.eval MGenerate.generate))). *)
  set (all := to_trace (
    let local := MGenerate.eval MGenerate.generate in
    let* _ := preimage_a.eval 1 local in
    let* _ := export_bool.eval local in
    let* _ := export_zero.eval local in
    let* _ := c_c_prime.eval 1 local in
    let* _ := a_a_prime_c_c_prime.eval 1 local in
    let* _ := a_prime_c_prime.eval 1 local in
    let* _ := a_prime_prime.eval 1 local in
    let* _ := a_prime_prime_0_0_bits_bools.eval local in
    let* _ := a_prime_prime_0_0_limbs.eval local in
    let* _ := a_prime_prime_prime_0_0_limbs.eval local in
    M.pure tt
  )).
  (* Time
    with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
    with_strategy transparent [M.for_in_zero_to_n]
    cbv in all.
  Show. *)
  (* Time set (bla := ltac:(to_mexpr_trace (snd all))). *)
  Compute ToRocq.cats [
    ToRocq.endl;
    ToRocq.to_rocq ltac:(to_mexpr_trace (snd all)) 0;
    ToRocq.endl
  ].
Admitted.

(*
  Compute ToRocq.to_rocq ltac:(to_mexpr_trace (snd all)) 0.
  sdfsdf.

  set (gre := ltac:(
    let g := to_expr (MGenerate.Var 91 -F MGenerate.Var 191) in
    exact g
  )).
  set (result := 12).
  set (gre2 := ltac:(
    to_mexpr_trace (snd pre)
  )).

  Compute ToRocq.to_rocq ltac:(to_mexpr_trace (snd pre)) 0.
  Compute ToRocq.to_rocq ltac:(to_mexpr_trace (snd all)) 0.

  set (foo := ltac:(to_mexpr_trace (snd pre))).
  set (foo5 := ltac:(to_mexpr (
    M.Let (M.Pure 12) (fun x => M.Pure x)
  ))).
  set (foo2 := ltac:(to_mexpr pre)).
  (* set (bar2 := MExpr.Pure tt). *)
  let v := fresh "v" in
  pose (M.Pure tt) as v;
  (
    with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
    with_strategy transparent [M.for_in_zero_to_n]
      cbv in v
  ).
  set (foo := ltac:(to_mexpr (M.Pure tt))).

  Ltac to_mexpr_aux e :=
    match e with
    | M.Pure ?value =>
      constr:(MExpr.Pure value)
    | M.AssertZero ?expr ?value =>
      constr:(MExpr.Pure value)
    | M.Call ?e =>
      constr:(MExpr.Call (ltac:(to_mexpr_aux e)))
    | M.Let ?e ?k =>
      constr:(MExpr.Let (ltac:(to_mexpr_aux e)) (fun x => ltac:(to_mexpr_aux (k x))))
    | M.When ?condition ?e =>
      constr:(MExpr.When condition (ltac:(to_mexpr_aux e)))
    end.

  Ltac to_mexpr e :=
    let v := fresh "v" in
    pose e as v;
    (
      with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
      with_strategy transparent [M.for_in_zero_to_n]
        cbv in v
    );
    match eval unfold v in v with
    | ?e =>
      let result := fresh "result" in
      let result := to_mexpr_aux e in
      exact result
    end.

  (* Ltac to_mexpr e :=
    let v := fresh "v" in
    let v := (
      with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
      with_strategy transparent [M.for_in_zero_to_n]
        exact ltac:(eval cbv in e)
    ) in
    pose (ltac:(constr:(v))) as arg. *)

  set (foo := ltac:(to_mexpr (M.Pure 12))).
  set (foo5 := ltac:(to_mexpr (
    M.Let (M.Pure 12) (fun x => M.Pure x)
  ))).
  set (foo2 := ltac:(to_mexpr pre)).
  (* set (bar2 := MExpr.Pure tt). *)
  let v := fresh "v" in
  pose (M.Pure tt) as v;
  (
    with_strategy opaque [UnOp.opp UnOp.from BinOp.add BinOp.sub BinOp.mul]
    with_strategy transparent [M.for_in_zero_to_n]
      cbv in v
  ).
  set (foo := ltac:(to_mexpr (M.Pure tt))).


  Print pre.
  dsfdf.

  set (ll := (MGenerate.eval MGenerate.generate : KeccakCols.t)).
  Time cbv in ll.
  Show.
  dfsdf.
  
  set (x := eval_local (MGenerate.eval MGenerate.generate)).
  unfold eval_local in x.
  cbn in x.
  unfold MGenerate.eval, MGenerate.generate_list, MGenerate.generate_var in x.
  cbn in x.
  Show.
  Time cbv in x.
Qed.
*)

Definition xorbs (bs : list bool) : bool :=
  Lists.List.fold_left xorb bs false.

Module FirstRowsFrom_a.
  Module From.
    Record t (local : KeccakCols.t) : Prop := {
      c_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c_c_prime (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_a local x y z =
        xorbs [
          KeccakCols.Bool.get_a_prime local x y z;
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c_prime local x z
        ];
      a_prime_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_a_prime local x 0 z;
          KeccakCols.Bool.get_a_prime local x 1 z;
          KeccakCols.Bool.get_a_prime local x 2 z;
          KeccakCols.Bool.get_a_prime local x 3 z;
          KeccakCols.Bool.get_a_prime local x 4 z
        ];
    }.
  End From.

  Module To.
    Record t (local : KeccakCols.t) : Prop := {
      a_c (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c local x z =
        xorbs [
          KeccakCols.Bool.get_a local x 0 z;
          KeccakCols.Bool.get_a local x 1 z;
          KeccakCols.Bool.get_a local x 2 z;
          KeccakCols.Bool.get_a local x 3 z;
          KeccakCols.Bool.get_a local x 4 z
        ];
      c_c_prime (x z : Z) :
        0 <= x < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_c_prime local x z =
        xorbs [
          KeccakCols.Bool.get_c local x z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
      a_a_prime_c (x y z : Z) :
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        KeccakCols.Bool.get_a_prime local x y z =
        xorbs [
          KeccakCols.Bool.get_a local x y z;
          KeccakCols.Bool.get_c local ((x + 4) mod 5) z;
          KeccakCols.Bool.get_c local ((x + 1) mod 5) ((z + 63) mod 64)
        ];
    }.
  End To.

  (** The lemma explains why the calculation for the first rows is deterministic. *)
  Lemma from_implies_to (local : KeccakCols.t) :
    From.t local ->
    To.t local.
  Proof.
    intros []; constructor; intros; cbn in *.
    { repeat rewrite a_a_prime_c_c_prime by lia.
      repeat rewrite a_prime_c_prime by lia.
      repeat destruct (KeccakCols.Bool.get_c _);
        repeat destruct (KeccakCols.Bool.get_a_prime _);
        reflexivity.
    }
    { hauto l: on. }
    { rewrite a_a_prime_c_c_prime by lia.
      rewrite c_c_prime by lia.
      repeat destruct (KeccakCols.Bool.get_a_prime _);
        repeat destruct (KeccakCols.Bool.get_c _);
        reflexivity.
    }
  Qed.
End FirstRowsFrom_a.

Lemma sum_eq {p} `{Prime p}
    (b0 b1 b2 b3 b4 : bool) :
    Lists.List.fold_left BinOp.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 =
    Lists.List.fold_left Z.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 mod p.
Proof.
  cbn; unfold UnOp.from, BinOp.add.
  show_equality_modulo.
Qed.

Lemma mul_diff_or_eq {p} `{Prime p} (H_p : 6 <= p)
    (b0 b1 b2 b3 b4 b : bool)
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            Z.b2z b0;
            Z.b2z b1;
            Z.b2z b2;
            Z.b2z b3;
            Z.b2z b4
          ] 0 in
        BinOp.sub sum (Z.b2z b) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  let sum :=
    Lists.List.fold_left Z.add [
      Z.b2z b0;
      Z.b2z b1;
      Z.b2z b2;
      Z.b2z b3;
      Z.b2z b4
    ] 0 in
  let diff :=
    sum - Z.b2z b in
  diff = 0 \/ diff - 2 = 0 \/ diff - 4 = 0.
Proof.
  intros.
  rewrite sum_eq in H_sum_diff.
  fold sum in H_sum_diff.
  rewrite M.mul_zero_implies_zero_3 in H_sum_diff.
  cbn -[sum] in H_sum_diff.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b - 2))
    in H_sum_diff
    by show_equality_modulo.
  replace (UnOp.from (BinOp.sub _ _))
    with (UnOp.from (sum - Z.b2z b - 4))
    in H_sum_diff
    by show_equality_modulo.
  repeat (rewrite M.is_zero_small in H_sum_diff by (destruct_all bool; cbn in *; lia)).
  trivial.
Qed.

(** Lemma to show that the calculation with the [diff] is actually a calculation of XOR. *)
Lemma xor_sum_diff_eq {p} `{Prime p} (H_p : 6 <= p) (local : KeccakCols.t) (x z : Z)
    (H_a_prime_bools :
      forall x y z,
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_a_prime local x y z)
    )
    (H_c_prime_bools :
      forall x z,
        0 <= x < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_c_prime local x z)
    )
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            KeccakCols.get_a_prime local x 0 z;
            KeccakCols.get_a_prime local x 1 z;
            KeccakCols.get_a_prime local x 2 z;
            KeccakCols.get_a_prime local x 3 z;
            KeccakCols.get_a_prime local x 4 z
          ] 0 in
        BinOp.sub sum (KeccakCols.get_c_prime local x z) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  KeccakCols.Bool.get_c_prime local x z =
  xorbs [
    KeccakCols.Bool.get_a_prime local x 0 z;
    KeccakCols.Bool.get_a_prime local x 1 z;
    KeccakCols.Bool.get_a_prime local x 2 z;
    KeccakCols.Bool.get_a_prime local x 3 z;
    KeccakCols.Bool.get_a_prime local x 4 z
  ].
Proof.
  intros.
  unfold KeccakCols.Bool.get_a_prime, KeccakCols.Bool.get_c_prime.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff by lia)
    );
    let b := fresh "b" in
    set (b := Z.odd _) in H_sum_diff;
    fold b;
    clearbody b
  ).
  epose proof (mul_diff_or_eq H_p _ _ _ _ _ _ H_sum_diff) as H_sum_diff_bis.
  clear H_sum_diff.
  destruct_all bool; cbn in *; destruct H_sum_diff_bis as [|[|] ]; congruence.
Qed.

Definition p_goldilocks : Z :=
  2^64 - 2^32 + 1.

(** As an experiment, we do the same proof as above but using an explicit value for the prime. The
    proof both happens to be faster and much simpler to write. *)
Lemma xor_sum_diff_eq_goldilocks `{Prime p_goldilocks} (local : KeccakCols.t) (x z : Z)
    (H_a_prime_bools :
      forall x y z,
        0 <= x < 5 ->
        0 <= y < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_a_prime local x y z)
    )
    (H_c_prime_bools :
      forall x z,
        0 <= x < 5 ->
        0 <= z < 64 ->
        IsBool.t (KeccakCols.get_c_prime local x z)
    )
    (H_sum_diff :
      let diff :=
        let sum :=
          Lists.List.fold_left BinOp.add [
            KeccakCols.get_a_prime local x 0 z;
            KeccakCols.get_a_prime local x 1 z;
            KeccakCols.get_a_prime local x 2 z;
            KeccakCols.get_a_prime local x 3 z;
            KeccakCols.get_a_prime local x 4 z
          ] 0 in
        BinOp.sub sum (KeccakCols.get_c_prime local x z) in
      BinOp.mul (BinOp.mul diff (BinOp.sub diff 2)) (BinOp.sub diff 4) = 0
    ) :
  0 <= x < 5 ->
  0 <= z < 64 ->
  KeccakCols.Bool.get_c_prime local x z =
  xorbs [
    KeccakCols.Bool.get_a_prime local x 0 z;
    KeccakCols.Bool.get_a_prime local x 1 z;
    KeccakCols.Bool.get_a_prime local x 2 z;
    KeccakCols.Bool.get_a_prime local x 3 z;
    KeccakCols.Bool.get_a_prime local x 4 z
  ].
Proof.
  intros.
  unfold KeccakCols.Bool.get_a_prime, KeccakCols.Bool.get_c_prime.
  repeat (
    (
      (rewrite H_a_prime_bools in H_sum_diff by lia) ||
      (rewrite H_c_prime_bools in H_sum_diff by lia)
    );
    let b := fresh "b" in
    set (b := Z.odd _) in H_sum_diff;
    fold b;
    clearbody b
  ).
  destruct_all bool; cbv in H_sum_diff; cbv; congruence.
Qed.

Module Pre.
  Record t (local : KeccakCols.t) : Prop := {
    a_bools (x y z : Z) :
      0 <= x < 5 ->
      0 <= y < 5 ->
      0 <= z < 64 ->
      IsBool.t (KeccakCols.get_a local x y z)
  }.
End Pre.

Module Post.
  Record t {p} `{Prime p} (local : KeccakCols.t) : Prop := {
    to : FirstRowsFrom_a.To.t local;
    a_prime_prime : a_prime_prime.Post.t 5 local;
    a_prime_prime_0_0_bits_bools : a_prime_prime_0_0_bits_bools.Post.t local;
    a_prime_prime_0_0_limbs : a_prime_prime_0_0_limbs.Post.t local;
    a_prime_prime_prime_0_0_limbs : a_prime_prime_prime_0_0_limbs.Post.t local;
  }.
End Post.

Lemma eval_local_implies {p} `{Prime p} (H_p : 6 <= p) (local' : KeccakCols.t) :
  let local := M.map_mod local' in
  Pre.t local ->
  {{ eval_local 5 local 🔽
    tt,
    Post.t local
  }}.
Proof.
  intros * [].
  unfold eval_local.
  eapply Run.LetAccumulate. {
    apply preimage_a.implies.
  }
  intros H_eval_assert_preimage_a.
  eapply Run.LetAccumulate. {
    apply export_bool.implies.
  }
  intros H_eval_assert_export_bool.
  eapply Run.LetAccumulate. {
    apply export_zero.implies.
  }
  intros H_eval_assert_export_zero.
  eapply Run.LetAccumulate. {
    apply c_c_prime.implies.
  }
  intros [].
  eapply Run.LetAccumulate. {
    apply a_a_prime_c_c_prime.implies.
  }
  intros [].
  eapply Run.LetAccumulate. {
    apply a_prime_c_prime.implies.
  }
  intros H_eval_assert_a_prime_c_prime.
  eapply Run.LetAccumulate. {
    apply a_prime_prime.implies.
  }
  intros H_eval_assert_a_prime_prime.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_bits_bools.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_bits_bools.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_0_0_limbs.
  eapply Run.LetAccumulate. {
    apply a_prime_prime_prime_0_0_limbs.implies.
  }
  intros H_eval_assert_a_prime_prime_prime_0_0_limbs.
  eapply Run.Implies. {
    apply Run.Pure.
  }
  intros [].
  assert (c_prime_bools :
    forall x z,
    0 <= x < 5 ->
    0 <= z < 64 ->
    IsBool.t (KeccakCols.get_c_prime local x z)
  ). {
    intros.
    rewrite c_c_prime_eq by lia.
    apply M.xor3_is_bool; apply c_bools; lia.
  }
  constructor.
  { apply FirstRowsFrom_a.from_implies_to.
    constructor; intros.
    { unfold KeccakCols.Bool.get_c, KeccakCols.Bool.get_c_prime.
      rewrite c_c_prime_eq by lia.
      repeat rewrite c_bools by lia.
      rewrite xor3_eq.
      repeat (cbn || f_equal || rewrite odd_b2z_eq).
    }
    { unfold KeccakCols.Bool.get_a.
      unfold KeccakCols.get_a in a_a_prime_c_c_prime_eq.
      erewrite Limbs.get_bit_of_bools_eqs; try (unfold U64_LIMBS, BITS_PER_LIMB; lia).
      3: {
        intros.
        apply a_a_prime_c_c_prime_eq; lia.
      }
      2: {
        intros.
        unfold a_a_prime_c_c_prime.get_bit.
        apply M.xor3_is_bool; cbn in *.
        { apply a_prime_bools; lia. }
        { apply c_bools; lia. }
        { apply c_prime_bools; lia. }
      }
      unfold a_a_prime_c_c_prime.get_bit.
      cbn - [local].
      rewrite <- odd_b2z_eq; f_equal.
      rewrite <- M.xor3_eq; f_equal.
      { apply a_prime_bools; lia. }
      { apply c_bools; lia. }
      { apply c_prime_bools; lia. }
    }
    { apply xor_sum_diff_eq; trivial.
      apply H_eval_assert_a_prime_c_prime; lia.
    }
  }
  { assumption. }
  { assumption. }
  { assumption. }
  { assumption. }
Qed.

Module FunctionalSpec.
  Module Input.
    Record t : Set := {
      step : Z;
      export : bool;
      preimage : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
      a : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5;
    }.

    Definition apply (input : t) (local : KeccakCols.t) : KeccakCols.t :=
      local
        <| KeccakCols.step_flags := {| Array.get r := Z.b2z (r =? input.(step)) |} |>
        <| KeccakCols.export := Z.b2z input.(export) |>
        <| KeccakCols.preimage := input.(preimage) |>
        <| KeccakCols.a := input.(a) |>.
  End Input.

  (*
    let get_xored_bit = |i| {
        let mut rc_bit_i = AB::Expr::ZERO;
        for r in 0..NUM_ROUNDS {
            let this_round = local.step_flags[r];
            let this_round_constant = AB::Expr::from_bool(rc_value_bit(r, i) != 0);
            rc_bit_i += this_round * this_round_constant;
        }

        rc_bit_i.xor(&local.a_prime_prime_0_0_bits[i].into())
    };
  *)
  (** Boolean version of the function above. *)
  Definition get_xored_bit {p} `{Prime p}
      (step : Z)
      (a_prime_prime_0_0_bits : Array.t bool 64)
      (i : Z) :
      bool :=
    xorb (rc_value_bit step i) a_prime_prime_0_0_bits.[i].

  Definition local_of_input {p} `{Prime p}
      (input : Input.t) :
      KeccakCols.t :=
    let step_flags : Array.t bool NUM_ROUNDS :=
      {|
        Array.get r := r =? input.(Input.step);
      |} in
    let c : Array.t (Array.t bool 64) 5 :=
      {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[0].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[1].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[2].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[3].[x] z;
              Limbs.get_bit BITS_PER_LIMB input.(Input.a).[4].[x] z
            ];
        |}
      |} in
    let c_prime : Array.t (Array.t bool 64) 5 :=
      {|
        Array.get x := {|
          Array.get z :=
            xorbs [
              c.[x].[z];
              c.[(x + 4) mod 5].[z];
              c.[(x + 1) mod 5].[(z + 63) mod 64]
            ];
        |}
      |} in
    let a_prime : Array.t (Array.t (Array.t bool 64) 5) 5 :=
      {|
        Array.get y := {|
          Array.get x := {|
            Array.get z :=
              xorbs [
                Limbs.get_bit BITS_PER_LIMB input.(Input.a).[y].[x] z;
                c.[(x + 4) mod 5].[z];
                c.[(x + 1) mod 5].[(z + 63) mod 64]
              ];
            |}
        |}
      |} in
    let a_prime_prime : Array.t (Array.t (Array.t Z U64_LIMBS) 5) 5 :=
      {|
        Array.get y := {|
          Array.get x :=
            Limbs.of_bools U64_LIMBS BITS_PER_LIMB {|
              Array.get z :=
                let andn :=
                  andb
                    (Impl_KeccakCols.b_of_a_prime a_prime ((x + 1) mod 5) y z)
                    (Impl_KeccakCols.b_of_a_prime a_prime ((x + 2) mod 5) y z) in
                Z.b2z (xorb andn (Impl_KeccakCols.b_of_a_prime a_prime x y z));
            |};
        |}
      |} in
    let a_prime_prime_0_0_bits : Array.t bool 64 :=
      {|
        Array.get z :=
          Limbs.get_bit BITS_PER_LIMB a_prime_prime.[0].[0] z;
      |} in
    let a_prime_prime_prime_0_0_limbs : Array.t Z U64_LIMBS :=
      Limbs.of_bools U64_LIMBS BITS_PER_LIMB {|
        Array.get z := Z.b2z (get_xored_bit input.(Input.step) a_prime_prime_0_0_bits z);
      |} in
    {|
      KeccakCols.step_flags := Array.map Z.b2z step_flags;
      KeccakCols.export := Z.b2z input.(Input.export);
      KeccakCols.preimage := input.(Input.preimage);
      KeccakCols.a := input.(Input.a);
      KeccakCols.c := Array.map (Array.map Z.b2z) c;
      KeccakCols.c_prime := Array.map (Array.map Z.b2z) c_prime;
      KeccakCols.a_prime := Array.map (Array.map (Array.map Z.b2z)) a_prime;
      KeccakCols.a_prime_prime := a_prime_prime;
      KeccakCols.a_prime_prime_0_0_bits := Array.map Z.b2z a_prime_prime_0_0_bits;
      KeccakCols.a_prime_prime_prime_0_0_limbs := a_prime_prime_prime_0_0_limbs;
    |}.

  Lemma implied_by_post {p} `{Prime p}
      (local' : KeccakCols.t)
      (input : Input.t) :
    let local := M.map_mod (Input.apply input local') in
    forall
      (H_pre : Pre.t local)
      (H_post : Post.t local),
    local = local_of_input input.
  Proof.
    intros.
    cbn in local.
    unfold local in *; clear local.
    destruct local'; cbn in *.
    unfold local_of_input; f_equal.
  Admitted.
End FunctionalSpec.
