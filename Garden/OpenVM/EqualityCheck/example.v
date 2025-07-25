(** In this file, we analyse a short example of circuit with a loop, taken from OpenVM. Not that
    this example is not used as it is in the OpenVM code, we take the code to make a self-contained
    example. *)
Require Import Garden.Plonky3.MLessEffects.

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
    assert_zero (BinOp.mul cmp_eq (BinOp.sub (Array.get_mod a i) (Array.get_mod b i)))
  ) in
  let sum : Z := M.sum_for_in_zero_to_n NUM_LIMBS (fun i =>
    BinOp.mul (Array.get_mod inv_marker i) (BinOp.sub (Array.get_mod a i) (Array.get_mod b i))
  ) in
  let sum := BinOp.add sum cmp_eq in
  assert_one sum.

Module Limbs.
  Parameter to_Z : forall {p} `{Prime p} {NUM_LIMBS : Z}, Array.t Z NUM_LIMBS -> Z.
End Limbs.


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
