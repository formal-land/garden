(** In this file, we analyse a short example of circuit with a loop, taken from OpenVM. Not that
    this example is not used as it is in the OpenVM code, we take the code to make a self-contained
    example. *)
Require Import Garden.Plonky3.M.

(*
  Pseudo Rust code:
  // Parameter: cmp_eq
  let mut sum = cmp_eq.clone();
  for i in 0..NUM_LIMBS {
      sum += (a[i] - b[i]) * inv_marker[i];
      builder.assert_zero(cmp_eq.clone() * (a[i] - b[i]));
  }
  builder.assert_one(sum);
*)
Definition eval {p} `{Prime p} {NUM_LIMBS : Z}
    (a b inv_marker : Array.t Z NUM_LIMBS)
    (cmp_eq : Z) :
    M.t unit :=
  let* _ := M.for_in_zero_to_n NUM_LIMBS (fun i =>
    M.assert_zero (BinOp.mul cmp_eq (BinOp.sub (Array.get_mod a i) (Array.get_mod b i)))
  ) in
  let sum : Z := M.sum_for_in_zero_to_n NUM_LIMBS (fun i =>
    BinOp.mul (Array.get_mod inv_marker i) (BinOp.sub (Array.get_mod a i) (Array.get_mod b i))
  ) in
  let sum := BinOp.add sum cmp_eq in
  M.assert_one sum.

Module Limbs.
  Parameter to_Z : forall {p} `{Prime p} {NUM_LIMBS : Z}, Array.t Z NUM_LIMBS -> Z.
End Limbs.

Ltac show_equality_modulo :=
  repeat (
    (
      (
        apply Zplus_eqm ||
        apply Zmult_eqm ||
        apply Zopp_eqm
      );
      unfold eqm
    ) ||
    rewrite Zmod_eqm ||
    reflexivity
  ).

Axiom foo_add : forall a b p, (a mod p + b mod p) mod p = (a + b) mod p.
Axiom foo_sub : forall a b p, (a mod p - b mod p) mod p = (a - b) mod p.
Axiom foo_mul : forall a b p, ((a mod p) * (b mod p)) mod p = (a * b) mod p.
Axiom foo_mod_mod : forall a p, (a mod p) mod p = a mod p.
Axiom foo_add_left : forall a b p, (a mod p + b) mod p = (a + b) mod p.
Axiom foo_add_right : forall a b p, (a + b mod p) mod p = (a + b) mod p.
Axiom foo_sub_left : forall a b p, (a mod p - b) mod p = (a - b) mod p.
Axiom foo_sub_right : forall a b p, (a - b mod p) mod p = (a - b) mod p.
Axiom foo_mul_left : forall a b p, ((a mod p) * b) mod p = (a * b) mod p.
Axiom foo_mul_right : forall a b p, (a * (b mod p)) mod p = (a * b) mod p.
Axiom foo_eq_sub : forall a b p, (a mod p - b mod p) mod p = 0 -> a mod p = b mod p.
Axiom foo_mul_0 : forall a p, (a * 0) mod p = 0.

Ltac bubble_mod_expr e :=
  match e with
  | Z.modulo (Z.add ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite foo_add_left;
    try rewrite foo_add_right
  | Z.modulo (Z.sub ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite foo_sub_left;
    try rewrite foo_sub_right
  | Z.modulo (Z.mul ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite foo_mul_left;
    try rewrite foo_mul_right
  | _ => idtac
  end.

Ltac bubble_mod_goal :=
  unfold BinOp.add, BinOp.sub, BinOp.mul, Array.get_mod;
  repeat rewrite foo_mod_mod;
  repeat match goal with
  | |- context [?e1 mod ?p = ?e2 mod ?p] =>
    bubble_mod_expr (e1 mod p);
    bubble_mod_expr (e2 mod p)
  end.

Lemma eval_equal_is_valid {p} `{Prime p} {NUM_LIMBS : Z}
    (a b inv_marker : Array.t Z NUM_LIMBS)
    (cmp_eq : Z)
    (H_NUM_LIMBS : 0 <= NUM_LIMBS)
    (H_a_eq_b : forall i, 0 <= i < NUM_LIMBS -> Array.get_mod a i = Array.get_mod b i) :
  {{ eval a b inv_marker cmp_eq 🔽
    tt,
    cmp_eq mod p = 1 mod p
  }}.
Proof.
  eapply Run.Implies. {
    apply Run.Let with (value := tt) (P1 := True). {
      eapply Run.Implies. {
        apply Run.ForInZeroToN; intros.
        apply Run.Equal.
      }
      trivial.
    }
    intros _.
    replace NUM_LIMBS with (Z.of_nat (Z.to_nat NUM_LIMBS)) in * by lia.
    replace (M.sum_for_in_zero_to_n _ _) with (0 mod p). 2: {
      unfold M.sum_for_in_zero_to_n.
      generalize H_a_eq_b.
      set (foo := NUM_LIMBS).
      replace NUM_LIMBS with (Z.of_nat (Z.to_nat NUM_LIMBS)).
Admitted.
