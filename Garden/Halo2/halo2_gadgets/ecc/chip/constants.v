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

(** [2^{-n} mod pallas_p]: the [inv_two_pow_s] constants that the short lookup
    range check pins into the running-sum column at offset 2
    ([lookup_range_check.rs] [short_range_check]).  Reduced literals, as
    [ConstrainConstant] requires. *)
Definition inv_two_pow_4 : Z :=
  27138770914995983302399449611411228403152865451820213171207509466578094653441.
Definition inv_two_pow_5 : Z :=
  28043396612162516079146097931791602683257960966880886943581093115464031141889.
Definition inv_two_pow_6 : Z :=
  28495709460745782467519422091981789823310508724411223829767884939906999386113.
Definition inv_two_pow_8 : Z :=
  28834944097183232258799415212124430178349919542558976494407978808239225569281.
Definition inv_two_pow_9 : Z :=
  28891483203256140557346080732148203570856488012250268605181327786294596599809.
