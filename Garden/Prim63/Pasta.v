(** * Primitive Montgomery arithmetic for the two Pasta moduli *)

From Stdlib Require Import ZArith.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Montgomery.

Local Open Scope Z_scope.

Module PallasPConfig <: Prim63MontgomeryConfig.
  Import Prim63Words.

  Definition modulus_Z : Z :=
    28948022309329048855892746252171976963363056481941560715954676764349967630337.

  Definition modulus : words5 :=
    {| w0 := 1814160019365560321%uint63;
       w1 := 4939659307829031479%uint63;
       w2 := 0%uint63;
       w3 := 0%uint63;
       w4 := 4%uint63 |}.

  Definition n0_prime : word := 1814160019365560319%uint63.

  Definition montgomery_one : words5 :=
    {| w0 := 8731689047006642177%uint63;
       w1 := 6791962312201335350%uint63;
       w2 := 7988457209897517938%uint63;
       w3 := 9223372036854775807%uint63;
       w4 := 3%uint63 |}.

  Definition r2 : words5 :=
    {| w0 := 516943352054953635%uint63;
       w1 := 7465595124130393850%uint63;
       w2 := 410022111918250107%uint63;
       w3 := 3577420757648261792%uint63;
       w4 := 0%uint63 |}.

  Definition r_inverse_words : words5 :=
    {| w0 := 209542381926959437%uint63;
       w1 := 5053829415489735773%uint63;
       w2 := 8710664881734183608%uint63;
       w3 := 1188030470326425057%uint63;
       w4 := 1%uint63 |}.

  Definition r_inverse_Z : Z := eval5 r_inverse_words.

  Lemma modulus_words_correct : eval5 modulus = modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma modulus_positive : 0 < modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma twice_modulus_fits : 2 * modulus_Z < radix5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma n0_prime_correct :
    (Uint63.to_Z modulus.(w0) * Uint63.to_Z n0_prime + 1) mod radix = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma montgomery_one_correct :
    eval5 montgomery_one = radix5 mod modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r2_correct :
    eval5 r2 = (radix5 * radix5) mod modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r_inverse_correct :
    (radix5 * r_inverse_Z) mod modulus_Z = 1.
  Proof. vm_compute. reflexivity. Qed.
End PallasPConfig.

Module PallasP := Prim63Montgomery PallasPConfig.

Module PallasQConfig <: Prim63MontgomeryConfig.
  Import Prim63Words.

  Definition modulus_Z : Z :=
    28948022309329048855892746252171976963363056481941647379679742748393362948097.

  Definition modulus : words5 :=
    {| w0 := 884652903791329281%uint63;
       w1 := 4939659307838427579%uint63;
       w2 := 0%uint63;
       w3 := 0%uint63;
       w4 := 4%uint63 |}.

  Definition n0_prime : word := 884652903791329279%uint63.

  Definition montgomery_one : words5 :=
    {| w0 := 7802181931432411137%uint63;
       w1 := 7024339091104289210%uint63;
       w2 := 7988457209895168913%uint63;
       w3 := 9223372036854775807%uint63;
       w4 := 3%uint63 |}.

  Definition r2 : words5 :=
    {| w0 := 6250714017270805259%uint63;
       w1 := 6714242267414112777%uint63;
       w2 := 3867435386900240532%uint63;
       w3 := 2361396541261249778%uint63;
       w4 := 2%uint63 |}.

  Definition r_inverse_words : words5 :=
    {| w0 := 2534093983798897212%uint63;
       w1 := 1320197803779838919%uint63;
       w2 := 4414915818488113580%uint63;
       w3 := 6382762153436520543%uint63;
       w4 := 2%uint63 |}.

  Definition r_inverse_Z : Z := eval5 r_inverse_words.

  Lemma modulus_words_correct : eval5 modulus = modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma modulus_positive : 0 < modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma twice_modulus_fits : 2 * modulus_Z < radix5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma n0_prime_correct :
    (Uint63.to_Z modulus.(w0) * Uint63.to_Z n0_prime + 1) mod radix = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma montgomery_one_correct :
    eval5 montgomery_one = radix5 mod modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r2_correct :
    eval5 r2 = (radix5 * radix5) mod modulus_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r_inverse_correct :
    (radix5 * r_inverse_Z) mod modulus_Z = 1.
  Proof. vm_compute. reflexivity. Qed.
End PallasQConfig.

Module PallasQ := Prim63Montgomery PallasQConfig.
