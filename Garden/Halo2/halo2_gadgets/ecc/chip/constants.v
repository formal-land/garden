Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Definition fixed_base_window_size : Z := 3.

Definition h : Z := 2 ^ fixed_base_window_size.

Definition h_nat : nat := 8.

Definition num_windows : Z := 85.

Definition num_windows_short : Z := 22.

Definition l_scalar_short : Z := 64.

Definition t_q : Z := Primes.t_q.

Definition t_p : Z := Primes.t_p.

Definition pallas_b : Z := 5.

Definition pallas_p : Z := Primes.pallas_p.

Definition two_inv : Z := (pallas_p + 1) / 2.
