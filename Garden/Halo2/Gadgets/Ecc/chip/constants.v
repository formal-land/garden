Require Import Garden.Halo2.main.

Global Open Scope Z_scope.

Definition fixed_base_window_size : Z := 3.

Definition h : Z := 2 ^ fixed_base_window_size.

Definition h_nat : nat := 8.

Definition num_windows : Z := 85.

Definition num_windows_short : Z := 22.

Definition l_scalar_short : Z := 64.

Definition t_q : Z := 45560315531506369815346746415080538113.

Definition t_p : Z := 45560315531419706090280762371685220353.

Definition pallas_b : Z := 5.

Definition pallas_p : Z := 2 ^ 254 + t_p.

Definition two_inv : Z := (pallas_p + 1) / 2.
