Require Import Circom.M.
Require Import Circom.Circomlib.translation.circuits.sha256.xor3.

Import Run.

Lemma run_Xor3 (P : Z) (a b c out mid : list F.t)
    (H_length_a : List.length a = 3%nat)
    (H_length_b : List.length b = 3%nat)
    (H_length_c : List.length c = 3%nat)
    (H_bits_a : List.Forall (fun x => x = 0 \/ x = 1) a)
    (H_bits_b : List.Forall (fun x => x = 0 \/ x = 1) b)
    (H_bits_c : List.Forall (fun x => x = 0 \/ x = 1) c) :
  let signals := {|
    Xor3Signals.a := a;
    Xor3Signals.b := b;
    Xor3Signals.c := c;
    Xor3Signals.out := out;
    Xor3Signals.mid := mid;
  |} in
  {{ Xor3Signals.IsNamed.P, 97 , signals, Scopes.empty ⏩
    Xor3 3 🔽 BlockUnit.Tt
  ⏩ Scopes.empty, True, True }}.
Proof.
  do 4 (destruct a as [|? a]; cbn in H_length_a; try discriminate).
  do 4 (destruct b as [|? b]; cbn in H_length_b; try discriminate).
  do 4 (destruct c as [|? c]; cbn in H_length_c; try discriminate).
  repeat match goal with
  | H : List.Forall _ _ |- _ => inversion_clear H
  end.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  end;
    subst.
  { run_deterministic.
    1-6: admit.
  }
  1-511: admit.
Admitted.
