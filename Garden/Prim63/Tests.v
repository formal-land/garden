(** * Closed regression vectors for the primitive Pasta-field backend *)

From Stdlib Require Import ZArith.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Pasta.

Local Open Scope Z_scope.

Module PTests.
  Import PallasPConfig.

  Example zero_decodes : PallasP.to_Z PallasP.zero = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example one_decodes : PallasP.to_Z PallasP.one = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example from_Z_small : PallasP.to_Z (PallasP.from_Z 42) = 42.
  Proof. vm_compute. reflexivity. Qed.

  Example from_Z_negative :
    PallasP.to_Z (PallasP.from_Z (-1)) = modulus_Z - 1.
  Proof. vm_compute. reflexivity. Qed.

  Example add_small :
    PallasP.to_Z (PallasP.add (PallasP.from_Z 5) (PallasP.from_Z 7)) = 12.
  Proof. vm_compute. reflexivity. Qed.

  Example add_wraps :
    PallasP.to_Z
      (PallasP.add (PallasP.from_Z (modulus_Z - 1)) (PallasP.from_Z 1)) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example sub_wraps :
    PallasP.to_Z (PallasP.sub (PallasP.from_Z 5) (PallasP.from_Z 7)) =
      modulus_Z - 2.
  Proof. vm_compute. reflexivity. Qed.

  Example neg_small :
    PallasP.to_Z (PallasP.neg (PallasP.from_Z 5)) = modulus_Z - 5.
  Proof. vm_compute. reflexivity. Qed.

  Example mul_small :
    PallasP.to_Z
      (PallasP.mul (PallasP.from_Z 123456789) (PallasP.from_Z 987654321)) =
      121932631112635269.
  Proof. vm_compute. reflexivity. Qed.

  Example mul_minus_one :
    PallasP.to_Z
      (PallasP.square (PallasP.from_Z (modulus_Z - 1))) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example equal_reflexive :
    PallasP.equal (PallasP.from_Z 12345) (PallasP.from_Z 12345) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example equal_distinguishes :
    PallasP.equal (PallasP.from_Z 12345) (PallasP.from_Z 12346) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example window8_crosses_word_boundary :
    PallasP.window8_standard
      (PallasP.standard_of_Z (171 * 2 ^ 120)) 15%uint63 = 171%uint63.
  Proof. vm_compute. reflexivity. Qed.
End PTests.

Module QTests.
  Import PallasQConfig.

  Example zero_decodes : PallasQ.to_Z PallasQ.zero = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example one_decodes : PallasQ.to_Z PallasQ.one = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example from_Z_small : PallasQ.to_Z (PallasQ.from_Z 42) = 42.
  Proof. vm_compute. reflexivity. Qed.

  Example from_Z_negative :
    PallasQ.to_Z (PallasQ.from_Z (-1)) = modulus_Z - 1.
  Proof. vm_compute. reflexivity. Qed.

  Example add_wraps :
    PallasQ.to_Z
      (PallasQ.add (PallasQ.from_Z (modulus_Z - 1)) (PallasQ.from_Z 1)) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example sub_wraps :
    PallasQ.to_Z (PallasQ.sub (PallasQ.from_Z 5) (PallasQ.from_Z 7)) =
      modulus_Z - 2.
  Proof. vm_compute. reflexivity. Qed.

  Example mul_small :
    PallasQ.to_Z
      (PallasQ.mul (PallasQ.from_Z 123456789) (PallasQ.from_Z 987654321)) =
      121932631112635269.
  Proof. vm_compute. reflexivity. Qed.

  Example mul_minus_one :
    PallasQ.to_Z
      (PallasQ.square (PallasQ.from_Z (modulus_Z - 1))) = 1.
  Proof. vm_compute. reflexivity. Qed.
End QTests.
