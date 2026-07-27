(** * Integer lift for the §4.14 bundle balance sum

    The pure-ℤ step of the transaction-level balance argument (§4.14
    'Balance and Binding Signature (Orchard)' of the Zcash protocol
    specification): a bundle's net-value residue

      [v* = Σ (v_old_i - v_new_i) - v^balanceOrchard]

    that vanishes modulo the Pallas scalar-field order [pallas_q] vanishes
    over ℤ.  The interval bound comes from the consensus ranges: at most
    [2^16 - 1] actions, each net value in the open interval
    [(-(2^64), 2^64)] (both note values are 64-bit), and the balance a
    signed 64-bit integer, so

      [|v*| <= (2^16 - 1) * (2^64 - 1) + 2^63 < 2^81 < pallas_q],

    and the only multiple of [pallas_q] in that interval is [0].

    Exports: the list sum [zsum] with its fold bridge [zsum_map], the
    triangle bound [zsum_abs_le], the lift [net_value_lift] over
    [list Z], and its instance [net_value_fold_lift] at a per-element
    projection (the shape of the bundle layer's net-value fold). *)

Require Import Garden.Field.Field.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Global Open Scope Z_scope.

Module OrchardBundleIntegerLift.
  (** The sum of a list of integers. *)
  Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

  (** A fold accumulating a per-element projection is the sum of the
      mapped list. *)
  Lemma zsum_map {A : Type} (f : A -> Z) (l : list A) :
    fold_right (fun a s => f a + s) 0 l = zsum (map f l).
  Proof.
    unfold zsum.
    induction l as [| a l IH]; cbn [fold_right map]; [reflexivity |].
    now rewrite IH.
  Qed.

  (** Triangle bound for the list sum: entries bounded by [B] in absolute
      value sum to at most [length * B]. *)
  Lemma zsum_abs_le (B : Z) (l : list Z)
      (Hl : Forall (fun x => Z.abs x <= B) l) :
    Z.abs (zsum l) <= Z.of_nat (length l) * B.
  Proof.
    unfold zsum.
    induction Hl as [| x l Hx Hl IH]; cbn [fold_right length].
    - cbn; lia.
    - rewrite Nat2Z.inj_succ.
      pose proof (Z.abs_triangle x (fold_right Z.add 0 l)) as Htri.
      replace (Z.succ (Z.of_nat (length l)) * B)
        with (Z.of_nat (length l) * B + B) by ring.
      clear -Hx IH Htri; lia.
  Qed.

  (** The integer lift: with at most [2^16 - 1] summands, each in the
      open interval [(-(2^64), 2^64)] (the range of a difference of two
      64-bit note values), and [vb] a signed 64-bit integer, a sum-minus-
      balance residue divisible by [pallas_q] is zero over ℤ.  The residue
      is bounded by [(2^16 - 1) * (2^64 - 1) + 2^63 < 2^81 < pallas_q]. *)
  Theorem net_value_lift (l : list Z) (vb : Z)
      (Hn : Z.of_nat (length l) <= 2 ^ 16 - 1)
      (Hl : Forall (fun x => - 2 ^ 64 < x < 2 ^ 64) l)
      (Hvb : - 2 ^ 63 <= vb < 2 ^ 63)
      (Hmod : (zsum l - vb) mod Primes.pallas_q = 0) :
    zsum l - vb = 0.
  Proof.
    assert (Hq : Primes.pallas_q =
        28948022309329048855892746252171976963363056481941647379679742748393362948097)
      by reflexivity.
    assert (Hqnz : Primes.pallas_q <> 0) by (rewrite Hq; discriminate).
    assert (H63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
    (* Per-entry absolute bound from the open interval. *)
    assert (Habs : Forall (fun x => Z.abs x <= 2 ^ 64 - 1) l).
    { eapply Forall_impl; [| exact Hl].
      intros x [Hx1 Hx2]; clear -Hx1 Hx2; lia. }
    (* The sum bound, capped by the action-count consensus rule. *)
    pose proof (zsum_abs_le (2 ^ 64 - 1) l Habs) as Hsum.
    assert (Hcap : Z.of_nat (length l) * (2 ^ 64 - 1) <=
        (2 ^ 16 - 1) * (2 ^ 64 - 1)).
    { apply Z.mul_le_mono_nonneg_r; [| exact Hn].
      assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
      clear -H64; lia. }
    assert (Hcap_lit : (2 ^ 16 - 1) * (2 ^ 64 - 1) = 1208907372870555465089025)
      by reflexivity.
    (* The residue is a multiple of [pallas_q] inside [(-q, q)], hence 0. *)
    pose proof (proj1 (Z.mod_divide _ _ Hqnz) Hmod) as [k Hk].
    rewrite Hq in Hk.
    clear -Hsum Hcap Hcap_lit Hvb H63 Hk; lia.
  Qed.

  (** The lift at a per-element net-value projection [f]: the shape of the
      bundle layer's fold [Σ f(action_i) - value_balance]. *)
  Corollary net_value_fold_lift {A : Type} (f : A -> Z)
      (acts : list A) (vb : Z)
      (Hn : Z.of_nat (length acts) <= 2 ^ 16 - 1)
      (Hacts : Forall (fun a => - 2 ^ 64 < f a < 2 ^ 64) acts)
      (Hvb : - 2 ^ 63 <= vb < 2 ^ 63)
      (Hmod : (fold_right (fun a s => f a + s) 0 acts - vb)
          mod Primes.pallas_q = 0) :
    fold_right (fun a s => f a + s) 0 acts - vb = 0.
  Proof.
    rewrite zsum_map in Hmod |- *.
    apply net_value_lift.
    - rewrite length_map; exact Hn.
    - apply Forall_map; exact Hacts.
    - exact Hvb.
    - exact Hmod.
  Qed.
End OrchardBundleIntegerLift.
