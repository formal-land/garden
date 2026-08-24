(** * Pasta field encodings and Vesta affine operations

    Byte codecs the Halo 2 verifier uses over Vesta, plus the affine
    group law [y^2 = x^3 + 5] over [F_{pallas_q}]. The moduli are the
    Pasta primes of [Garden.Field.Field.Primes]; field arithmetic is
    [Z] reduced modulo those primes so this file depends only on the
    standard library (the same residues [EllipticCurve.Vesta] uses).

    Coordinates of a Vesta point live in [F_{pallas_q}]; IPA scalars
    live in [F_{pallas_p}]. [from_uniform_bytes] is a 64-byte
    little-endian integer reduced into the field, matching
    [pasta_curves] [from_u512]. The 32-byte compressed affine encoding
    is [x] with the odd-[y] flag in the high bit of the last byte; the
    identity is 32 zero bytes. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Garden.Rust.primitives.

Import List.ListNotations.
Global Open Scope Z_scope.

Module PastaPrimes.
  Definition t_q : Z := 45560315531506369815346746415080538113.
  Definition t_p : Z := 45560315531419706090280762371685220353.
  Definition pallas_p : Z := 2 ^ 254 + t_p.
  Definition pallas_q : Z := 2 ^ 254 + t_q.
End PastaPrimes.

Module FieldOps.
  Definition add (p x y : Z) : Z := (x + y) mod p.
  Definition sub (p x y : Z) : Z := (x - y) mod p.
  Definition mul (p x y : Z) : Z := (x * y) mod p.
  Definition opp (p x : Z) : Z := (- x) mod p.
  Definition from (p x : Z) : Z := x mod p.

  Fixpoint mod_inv_loop (fuel : nat) (t newt r newr : Z) : Z :=
    match fuel with
    | O => t
    | S f =>
      if newr =? 0 then t
      else
        let q := r / newr in
        mod_inv_loop f newt (t - q * newt) newr (r - q * newr)
    end.

  Definition invert (p a : Z) : option Z :=
    let a' := a mod p in
    if a' =? 0 then None
    else Some ((mod_inv_loop (2 * Z.to_nat (Z.log2 p) + 4)%nat 0 1 p a') mod p).

  Fixpoint modpow_pos (p base : Z) (e : positive) : Z :=
    match e with
    | xH => from p base
    | xO e' => let h := modpow_pos p base e' in mul p h h
    | xI e' => let h := modpow_pos p base e' in mul p (mul p h h) base
    end.

  Definition pow (p base e : Z) : Z :=
    match e with
    | Zpos q => modpow_pos p base q
    | _ => from p 1
    end.

  Definition to_le_bytes (width : nat) (z : Z) : list Z :=
    (fix go (w : nat) (z : Z) : list Z :=
      match w with
      | O => []
      | S w => Z.land z 255 :: go w (Z.shiftr z 8)
      end) width z.

  Definition of_le_bytes (bs : list Z) : Z :=
    List.fold_right (fun b acc => b + 256 * acc) 0 bs.

  Definition to_repr (p z : Z) : list Z :=
    to_le_bytes 32%nat (from p z).

  Definition from_repr (p : Z) (bs : list Z) : option Z :=
    if Nat.eqb (List.length bs) 32%nat then
      let z := of_le_bytes bs in
      if (0 <=? z) && (z <? p) then Some z else None
    else None.

  Definition from_uniform_bytes (p : Z) (bs : list Z) : Z :=
    from p (of_le_bytes (List.firstn 64%nat bs)).

  Definition is_odd (p z : Z) : bool :=
    Z.odd (from p z).

  (** Tonelli–Shanks square root. [nz] is a quadratic non-residue. *)
  Fixpoint split_two (fuel : nat) (n : Z) : nat * Z :=
    match fuel with
    | O => (O, n)
    | S fuel =>
      if Z.even n then
        let '(s, q) := split_two fuel (n / 2) in (S s, q)
      else (O, n)
    end.

  Fixpoint pow2_i (p t : Z) (i : nat) : Z :=
    match i with
    | O => from p t
    | S i => mul p (pow2_i p t i) (pow2_i p t i)
    end.

  Fixpoint find_i (p t : Z) (i m : nat) : nat :=
    match m with
    | O => O
    | S m =>
      if from p (pow2_i p t i) =? 1 then i
      else find_i p t (S i) m
    end.

  Fixpoint ts_loop (p : Z) (fuel m : nat) (c t r : Z) : Z :=
    match fuel with
    | O => r
    | S fuel =>
      if from p t =? 1 then r
      else
        let i := find_i p t 1%nat m in
        let b := pow2_i p c (Nat.pred (m - i)) in
        let c' := mul p b b in
        ts_loop p fuel i c' (mul p t c') (mul p r b)
    end.

  Definition sqrt (p nz n : Z) : Z :=
    let n := from p n in
    if n =? 0 then 0
    else
      let fuel := S (Z.to_nat (Z.log2 p)) in
      let '(s, q) := split_two fuel (p - 1) in
      ts_loop p s s (pow p nz q) (pow p n q) (pow p n ((q + 1) / 2)).

  Definition is_square (p n : Z) : bool :=
    let n := from p n in
    (n =? 0) || (pow p n ((p - 1) / 2) =? 1).
End FieldOps.

Module Fp.
  Definition p : Z := PastaPrimes.pallas_p.
  Definition add := FieldOps.add p.
  Definition sub := FieldOps.sub p.
  Definition mul := FieldOps.mul p.
  Definition opp := FieldOps.opp p.
  Definition from := FieldOps.from p.
  Definition invert (z : Z) : option Z := FieldOps.invert p z.
  Definition pow_vartime (base exp : Z) : Z := FieldOps.pow p base exp.
  Definition to_repr (z : Z) : list Z := FieldOps.to_repr p z.
  Definition from_repr (bs : list Z) : option Z := FieldOps.from_repr p bs.
  Definition from_uniform_bytes (bs : list Z) : Z :=
    FieldOps.from_uniform_bytes p bs.
  Definition is_odd (z : Z) : bool := FieldOps.is_odd p z.
  Definition DELTA : Z := 5.
End Fp.

Module Fq.
  Definition p : Z := PastaPrimes.pallas_q.
  Definition add := FieldOps.add p.
  Definition sub := FieldOps.sub p.
  Definition mul := FieldOps.mul p.
  Definition opp := FieldOps.opp p.
  Definition from := FieldOps.from p.
  Definition invert (z : Z) : option Z := FieldOps.invert p z.
  Definition pow_vartime (base exp : Z) : Z := FieldOps.pow p base exp.
  Definition to_repr (z : Z) : list Z := FieldOps.to_repr p z.
  Definition from_repr (bs : list Z) : option Z := FieldOps.from_repr p bs.
  Definition from_uniform_bytes (bs : list Z) : Z :=
    FieldOps.from_uniform_bytes p bs.
  Definition is_odd (z : Z) : bool := FieldOps.is_odd p z.
  (** 5 is a quadratic non-residue in [F_{pallas_q}]. *)
  Definition nonresidue : Z := 5.
  Definition sqrt (n : Z) : Z := FieldOps.sqrt p nonresidue n.
  Definition is_square (n : Z) : bool := FieldOps.is_square p n.
End Fq.

Infix "+s" := Fp.add (at level 50, left associativity).
Infix "*s" := Fp.mul (at level 40, left associativity).
Infix "-s" := Fp.sub (at level 50, left associativity).
Notation "-s x" := (Fp.opp x) (at level 35, right associativity).

Module VestaCurve.
  Inductive point : Set :=
  | Infinity
  | Affine (x y : Z).

  Definition identity : point := Infinity.

  Definition on_curveb (P : point) : bool :=
    match P with
    | Infinity => true
    | Affine x y =>
      Z.eqb (Fq.mul y y)
        (Fq.add (Fq.mul (Fq.mul x x) x) (Fq.from 5))
    end.

  Definition neg (P : point) : point :=
    match P with
    | Infinity => Infinity
    | Affine x y => Affine x (Fq.opp y)
    end.

  Definition add (P Q : point) : point :=
    match P, Q with
    | Infinity, R | R, Infinity => R
    | Affine x1 y1, Affine x2 y2 =>
      if (Fq.from x1 =? Fq.from x2)%Z then
        if (Fq.from y1 =? Fq.from y2)%Z then
          if (Fq.from y1 =? 0)%Z then Infinity
          else
            match Fq.invert (Fq.mul (Fq.from 2) y1) with
            | None => Infinity
            | Some inv2y =>
              let lam := Fq.mul (Fq.mul (Fq.from 3) (Fq.mul x1 x1)) inv2y in
              let x3 := Fq.sub (Fq.mul lam lam) (Fq.mul (Fq.from 2) x1) in
              let y3 := Fq.sub (Fq.mul lam (Fq.sub x1 x3)) y1 in
              Affine x3 y3
            end
        else Infinity
      else
        match Fq.invert (Fq.sub x2 x1) with
        | None => Infinity
        | Some invdx =>
          let lam := Fq.mul (Fq.sub y2 y1) invdx in
          let x3 := Fq.sub (Fq.sub (Fq.mul lam lam) x1) x2 in
          let y3 := Fq.sub (Fq.mul lam (Fq.sub x1 x3)) y1 in
          Affine x3 y3
        end
    end.

  Fixpoint mul_pos (k : positive) (P : point) : point :=
    match k with
    | xH => P
    | xO k => let Q := mul_pos k P in add Q Q
    | xI k => let Q := mul_pos k P in add P (add Q Q)
    end.

  Definition mul (k : Z) (P : point) : point :=
    match k with
    | Z0 => Infinity
    | Zpos k => mul_pos k P
    | Zneg k => neg (mul_pos k P)
    end.

  Definition is_identity (P : point) : bool :=
    match P with
    | Infinity => true
    | Affine _ _ => false
    end.

  Definition coordinates (P : point) : option (Z * Z) :=
    match P with
    | Infinity => None
    | Affine x y => Some (x, y)
    end.
End VestaCurve.

Module VestaEncoding.
  Definition identity_bytes : list Z := List.repeat 0 32%nat.

  Definition is_zero_bytes (bs : list Z) : bool :=
    List.forallb (Z.eqb 0) bs.

  Definition to_bytes (P : VestaCurve.point) : list Z :=
    match P with
    | VestaCurve.Infinity => identity_bytes
    | VestaCurve.Affine x y =>
      let xb := Fq.to_repr x in
      let prefix := List.firstn 31%nat xb in
      let last := List.nth 31%nat xb 0 in
      let last := if Fq.is_odd y then Z.lor last 128 else last in
      prefix ++ [last]
    end.

  Definition rhs (x : Z) : Z :=
    Fq.add (Fq.mul (Fq.mul x x) x) (Fq.from 5).

  Definition from_bytes (bs : list Z) : option VestaCurve.point :=
    if Nat.eqb (List.length bs) 32%nat then
      if is_zero_bytes bs then Some VestaCurve.Infinity
      else
        let last := List.nth 31%nat bs 0 in
        let y_odd := (Z.land last 128 =? 128)%Z in
        let last_x := Z.land last 127 in
        let x_bytes := List.firstn 31%nat bs ++ [last_x] in
        match Fq.from_repr x_bytes with
        | None => None
        | Some x =>
          let r := rhs x in
          if Fq.is_square r then
            let y := Fq.sqrt r in
            let y := if Bool.eqb (Fq.is_odd y) y_odd then y else Fq.opp y in
            Some (VestaCurve.Affine x y)
          else None
        end
    else None.

  Definition from_xy (x y : Z) : option VestaCurve.point :=
    let P := VestaCurve.Affine (Fq.from x) (Fq.from y) in
    if VestaCurve.on_curveb P then Some P else None.

  Definition is_identity (P : VestaCurve.point) : bool :=
    VestaCurve.is_identity P.

  Definition coordinates (P : VestaCurve.point) : option (Z * Z) :=
    VestaCurve.coordinates P.
End VestaEncoding.

Module PastaTests.
  Lemma fp_from_repr_roundtrip :
    Fp.from_repr (Fp.to_repr 7) = Some 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fp_from_repr_rejects_modulus :
    Fp.from_repr (FieldOps.to_le_bytes 32%nat Fp.p) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fp_from_uniform_small :
    Fp.from_uniform_bytes (7 :: List.repeat 0 63%nat) = 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma vesta_identity_bytes :
    VestaEncoding.to_bytes VestaCurve.Infinity = VestaEncoding.identity_bytes.
  Proof. reflexivity. Qed.

  Lemma vesta_identity_from_bytes :
    VestaEncoding.from_bytes VestaEncoding.identity_bytes = Some VestaCurve.Infinity.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fp_invert_7 :
    match Fp.invert 7 with
    | Some i => Fp.mul i 7
    | None => 0
    end = 1.
  Proof. vm_compute. reflexivity. Qed.
End PastaTests.
