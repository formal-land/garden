(** Pocklington primality certificates for the six [Garden.Field] primes,
    checked by the Coqprime reflexive verifier ([Pocklington_refl] /
    [test_Certif], kernel-evaluated via [vm_cast_no_check]).  The certificate
    data (the partial factorisations of each [N - 1] and the witnesses) is
    untrusted input produced offline (trial division, Pollard-Brent rho, and
    factordb lookups for the two 255-bit Pallas primes); only the reflexive
    check below is trusted.  Only the pure-[positive] checker
    ([Coqprime.PrimalityTest.PocklingtonCertificat]) is required -- not the
    primitive-integer [num]/[Pock] layer -- so every lemma here is closed
    under the global context (no [Uint63] axioms).  The base cases are
    [Znumtheory.prime_2] / [prime_3]; every other auxiliary prime carries its
    own certificate. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Coqprime.PrimalityTest.PocklingtonCertificat.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Lemma prime_11 : prime 11.
Proof.
  apply (Pocklington_refl
    (Pock_certif 11 2 ((2, 1) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_331 : prime 331.
Proof.
  apply (Pocklington_refl
    (Pock_certif 331 3 ((11, 1) :: (2, 1) :: nil)%positive 1)
    ((Proof_certif 11 prime_11) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_5 : prime 5.
Proof.
  apply (Pocklington_refl
    (Pock_certif 5 2 ((2, 2) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_151 : prime 151.
Proof.
  apply (Pocklington_refl
    (Pock_certif 151 3 ((5, 2) :: (2, 1) :: nil)%positive 1)
    ((Proof_certif 5 prime_5) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma mersenne31_is_prime : prime 2147483647.
Proof.
  apply (Pocklington_refl
    (Pock_certif 2147483647 3 ((331, 1) :: (151, 1) :: (2, 1) :: nil)%positive 1)
    ((Proof_certif 331 prime_331) ::
     (Proof_certif 151 prime_151) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma baby_bear_is_prime : prime 2013265921.
Proof.
  apply (Pocklington_refl
    (Pock_certif 2013265921 11 ((2, 27) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma koala_bear_is_prime : prime 2130706433.
Proof.
  apply (Pocklington_refl
    (Pock_certif 2130706433 3 ((2, 24) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma goldilocks_is_prime : prime 18446744069414584321.
Proof.
  apply (Pocklington_refl
    (Pock_certif 18446744069414584321 7 ((2, 32) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_13 : prime 13.
Proof.
  apply (Pocklington_refl
    (Pock_certif 13 2 ((2, 2) :: nil)%positive 1)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_25741 : prime 25741.
Proof.
  apply (Pocklington_refl
    (Pock_certif 25741 2 ((13, 1) :: (2, 2) :: nil)%positive 78)
    ((Proof_certif 13 prime_13) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_772231 : prime 772231.
Proof.
  apply (Pocklington_refl
    (Pock_certif 772231 3 ((25741, 1) :: (2, 1) :: nil)%positive 1)
    ((Proof_certif 25741 prime_25741) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_325086459374267 : prime 325086459374267.
Proof.
  apply (Pocklington_refl
    (Pock_certif 325086459374267 2 ((772231, 1) :: (2, 1) :: nil)%positive 438410)
    ((Proof_certif 772231 prime_772231) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_8999194758858563409123804352480028797519453 : prime 8999194758858563409123804352480028797519453.
Proof.
  apply (Pocklington_refl
    (Pock_certif 8999194758858563409123804352480028797519453 2 ((325086459374267, 1) :: (2, 2) :: nil)%positive 484126610051852)
    ((Proof_certif 325086459374267 prime_325086459374267) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma pallas_p_is_prime : prime 28948022309329048855892746252171976963363056481941560715954676764349967630337.
Proof.
  apply (Pocklington_refl
    (Pock_certif 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((8999194758858563409123804352480028797519453, 1) :: (2, 32) :: nil)%positive 1)
    ((Proof_certif 8999194758858563409123804352480028797519453 prime_8999194758858563409123804352480028797519453) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_31649 : prime 31649.
Proof.
  apply (Pocklington_refl
    (Pock_certif 31649 3 ((2, 5) :: nil)%positive 26)
    ((Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_5239247429827 : prime 5239247429827.
Proof.
  apply (Pocklington_refl
    (Pock_certif 5239247429827 2 ((31649, 1) :: (2, 1) :: nil)%positive 103948)
    ((Proof_certif 31649 prime_31649) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_10427374428728808478656897599072717 : prime 10427374428728808478656897599072717.
Proof.
  apply (Pocklington_refl
    (Pock_certif 10427374428728808478656897599072717 2 ((5239247429827, 1) :: (2, 2) :: nil)%positive 15549769573040)
    ((Proof_certif 5239247429827 prime_5239247429827) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Lemma pallas_q_is_prime : prime 28948022309329048855892746252171976963363056481941647379679742748393362948097.
Proof.
  apply (Pocklington_refl
    (Pock_certif 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((10427374428728808478656897599072717, 1) :: (2, 32) :: nil)%positive 1)
    ((Proof_certif 10427374428728808478656897599072717 prime_10427374428728808478656897599072717) ::
     (Proof_certif 2 prime_2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.
