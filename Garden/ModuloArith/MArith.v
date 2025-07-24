From Coqtail Require Import Arith.Zeqm.

Require Export Coq.ZArith.ZArith.
Require Export Garden.Basics.

Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope type_scope.
Global Open Scope Z_scope.


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


Theorem mod_add : forall a b p, (a mod p + b mod p) mod p = (a + b) mod p.
Proof.
  symmetry.
  apply Zplus_mod.
Qed.

Theorem mod_sub : forall a b p, (a mod p - b mod p) mod p = (a - b) mod p.
Proof.
  symmetry.
  apply Zminus_mod.
Qed.

Theorem mod_mul : forall a b p, ((a mod p) * (b mod p)) mod p = (a * b) mod p.
Proof.
  symmetry.
  apply Zmult_mod.
Qed.

Theorem mod_mod : forall a p, (a mod p) mod p = a mod p.
Proof.
  apply Zmod_mod.
Qed.

Theorem mod_add_left : forall a b p, (a mod p + b) mod p = (a + b) mod p.
Proof.
    apply Zplus_mod_idemp_l.
Qed.

Theorem mod_add_right : forall a b p, (a + b mod p) mod p = (a + b) mod p.
Proof.
    intros a b.
    apply (Zplus_mod_idemp_r b a).
Qed.

Theorem mod_sub_left : forall a b p, (a mod p - b) mod p = (a - b) mod p.
Proof.
    apply Zminus_mod_idemp_l.
Qed.


Theorem mod_sub_right : forall a b p, (a - b mod p) mod p = (a - b) mod p.
Proof.
    apply Zminus_mod_idemp_r.
Qed.

Theorem mod_mul_left : forall a b p, ((a mod p) * b) mod p = (a * b) mod p.
Proof.
    apply Zmult_mod_idemp_l.
Qed.

Theorem mod_mul_right : forall a b p, (a * (b mod p)) mod p = (a * b) mod p.
Proof.
    intros a b.
    apply (Zmult_mod_idemp_r b a).
Qed.

Ltac bubble_mod_expr e :=
  match e with
  | Z.modulo (Z.add ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite mod_add_left;
    try rewrite mod_add_right
  | Z.modulo (Z.sub ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite mod_sub_left;
    try rewrite mod_sub_right
  | Z.modulo (Z.mul ?a ?b) _ =>
    bubble_mod_expr a;
    bubble_mod_expr b;
    try rewrite mod_mul_left;
    try rewrite mod_mul_right
  | _ => idtac
  end.

Ltac bubble_mod_goal :=
  unfold BinOp.add, BinOp.sub, BinOp.mul, Array.get_mod;
  repeat rewrite mod_mod;
  repeat match goal with
  | |- context [?e1 mod ?p = ?e2 mod ?p] =>
    bubble_mod_expr (e1 mod p);
    bubble_mod_expr (e2 mod p)
  end.