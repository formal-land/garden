(** * Solinas modular arithmetic for the Pasta primes

    Both Pasta primes have the shape [2 ^ 254 + t] with [0 < t < 2 ^ 126]
    ([Field.Primes]), so [2 ^ 254] is congruent to [- t] modulo the prime. A
    value below [p * p] is therefore reduced by folding its high half down
    twice with two multiplications by [t], and a bounded number of conditional
    shifts by [p] finishes the job; sums, differences and negations of already
    reduced inputs need a single conditional shift. This replaces the
    [Z.modulo] of [UnOp]/[BinOp], whose bit-by-bit long division on 510-bit
    operands dominates kernel evaluation of the field layer.

    Every operation here is proved equal to its [Field] counterpart on reduced
    inputs. The field layer keeps its definitions and its meaning: these are
    evaluation-only replacements, and any statement phrased over [BinOp]
    transfers by rewriting with the [_spec] lemmas below, with no new
    hypotheses.

    The generic development is stated once over an abstract Solinas pair
    [(t, p)]; the [pallas_q] and [pallas_p] operations repeat the body with
    the concrete constants so that kernel evaluation sees the modulus and the
    fold constant as cached constant references and applies no closure. In
    each product the small operand leads, because [Pos.mul] recurses on its
    first argument. *)

Require Import Garden.Field.Field.

(** ** A residue characterised by its difference

    Every correction branch below produces a value in [[0, m)] whose distance
    to the input is an explicit multiple of [m]. *)

Lemma Zmod_eq_of_diff (m z r k : Z) :
  0 < m ->
  0 <= r < m ->
  z - r = m * k ->
  z mod m = r.
Proof.
  intros Hm Hr Hk.
  replace z with (r + k * m) by lia.
  rewrite Z.mod_add by lia.
  now apply Z.mod_small.
Qed.

(** ** Additive operations on reduced inputs

    For [x] and [y] already in [[0, m)] the sum, difference and negation leave
    the range by at most one multiple of [m]. *)

Section Reduced.
  Variable m : Z.
  Hypothesis m_pos : 0 < m.

  Definition add_reduced (x y : Z) : Z :=
    let s := x + y in
    if m <=? s then s - m else s.

  Definition sub_reduced (x y : Z) : Z :=
    let d := x - y in
    if d <? 0 then d + m else d.

  Definition opp_reduced (x : Z) : Z :=
    if x =? 0 then 0 else m - x.

  Lemma add_reduced_spec (x y : Z) :
    0 <= x < m ->
    0 <= y < m ->
    add_reduced x y = (x + y) mod m.
  Proof.
    intros Hx Hy.
    unfold add_reduced; cbv zeta.
    destruct (Z.leb_spec m (x + y)) as [Hge | Hlt]; symmetry.
    - apply (Zmod_eq_of_diff m (x + y) (x + y - m) 1); lia.
    - apply (Zmod_eq_of_diff m (x + y) (x + y) 0); lia.
  Qed.

  Lemma sub_reduced_spec (x y : Z) :
    0 <= x < m ->
    0 <= y < m ->
    sub_reduced x y = (x - y) mod m.
  Proof.
    intros Hx Hy.
    unfold sub_reduced; cbv zeta.
    destruct (Z.ltb_spec (x - y) 0) as [Hneg | Hnonneg]; symmetry.
    - apply (Zmod_eq_of_diff m (x - y) (x - y + m) (-1)); lia.
    - apply (Zmod_eq_of_diff m (x - y) (x - y) 0); lia.
  Qed.

  Lemma opp_reduced_spec (x : Z) :
    0 <= x < m ->
    opp_reduced x = (- x) mod m.
  Proof.
    intros Hx.
    unfold opp_reduced.
    destruct (Z.eqb_spec x 0) as [-> | Hnz]; symmetry.
    - now rewrite Z.opp_0, Z.mod_0_l by lia.
    - apply (Zmod_eq_of_diff m (- x) (m - x) (-1)); lia.
  Qed.
End Reduced.

(** ** The two-fold Solinas reduction

    With [p = 2 ^ 254 + t] the input splits as [z = z1 * 2 ^ 254 + z0]; since
    [2 ^ 254] is congruent to [- t], the class of [z] is that of [z0 - t * z1].
    The product [t * z1] is itself split as [u1 * 2 ^ 254 + u0], which turns
    the subtraction into [z0 - u0 + t * u1]. The bounds [z1 < 2 ^ 255] and
    [u1 < 2 ^ 127] confine that value to [(- 2 ^ 254, 2 ^ 254 + 2 ^ 253)],
    a subset of [(- p, 2 * p)], so one conditional addition of [p] followed by
    one conditional subtraction lands in [[0, p)]. *)

(** The low-254-bit mask [2 ^ 254 - 1]. *)
Definition mask254 : Z := Z.ones 254.

Section Solinas.
  Variable t : Z.
  Variable p : Z.
  Hypothesis t_small : 0 < t < 2 ^ 126.
  Hypothesis p_shape : p = 2 ^ 254 + t.

  Definition red_solinas (z : Z) : Z :=
    let z0 := Z.land z mask254 in
    let z1 := Z.shiftr z 254 in
    let w := t * z1 in
    let u0 := Z.land w mask254 in
    let u1 := Z.shiftr w 254 in
    let r := z0 - u0 + t * u1 in
    let r := if r <? 0 then r + p else r in
    if p <=? r then r - p else r.

  Definition mul_solinas (x y : Z) : Z :=
    red_solinas (x * y).

  Lemma p_pos : 0 < p.
  Proof. rewrite p_shape; lia. Qed.

  (** The correction branches are justified by the range of the folded value,
      the splitting identities being the only algebraic input. *)
  Lemma red_solinas_core (z z0 z1 u0 u1 : Z) :
    z = 2 ^ 254 * z1 + z0 ->
    t * z1 = 2 ^ 254 * u1 + u0 ->
    0 <= z0 < 2 ^ 254 ->
    0 <= u0 < 2 ^ 254 ->
    0 <= t * u1 < 2 ^ 253 ->
    (let r := z0 - u0 + t * u1 in
     let r := if r <? 0 then r + p else r in
     if p <=? r then r - p else r) = z mod p.
  Proof.
    intros Hz Hw Hz0 Hu0 Hu1.
    pose proof p_pos as Hp.
    assert (Hpbig : 2 ^ 254 < p) by (rewrite p_shape; lia).
    assert (Htwice : 2 ^ 254 + 2 ^ 253 < 2 * p) by (rewrite p_shape; lia).
    assert (Hid : z - (z0 - u0 + t * u1) = p * (z1 - u1)).
    { rewrite p_shape, Hz.
      replace u0 with (t * z1 - 2 ^ 254 * u1) by lia.
      ring. }
    cbv zeta.
    destruct (Z.ltb_spec (z0 - u0 + t * u1) 0) as [Hneg | Hnonneg].
    - destruct (Z.leb_spec p (z0 - u0 + t * u1 + p)) as [Hge | Hlt].
      + lia.
      + symmetry.
        apply (Zmod_eq_of_diff p z (z0 - u0 + t * u1 + p) (z1 - u1 - 1));
          [lia | lia | ].
        rewrite Z.mul_sub_distr_l, <- Hid; lia.
    - destruct (Z.leb_spec p (z0 - u0 + t * u1)) as [Hge | Hlt]; symmetry.
      + apply (Zmod_eq_of_diff p z (z0 - u0 + t * u1 - p) (z1 - u1 + 1));
          [lia | lia | ].
        rewrite Z.mul_add_distr_l, <- Hid; lia.
      + apply (Zmod_eq_of_diff p z (z0 - u0 + t * u1) (z1 - u1));
          [lia | lia | exact Hid].
  Qed.

  Lemma red_solinas_spec (z : Z) :
    0 <= z < p * p ->
    red_solinas z = z mod p.
  Proof.
    intros Hz.
    pose proof p_pos as Hp.
    assert (H254 : 0 < 2 ^ 254) by lia.
    (* The input fits in 509 bits, hence its high half fits in 255. *)
    assert (Hsq : p * p < 2 ^ 509).
    { apply Z.le_lt_trans with ((2 ^ 254 + 2 ^ 126) * (2 ^ 254 + 2 ^ 126)).
      - apply Z.mul_le_mono_nonneg; lia.
      - lia. }
    assert (Hz1 : 0 <= z / 2 ^ 254 < 2 ^ 255).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    (* The fold product fits in 381 bits, hence its high half fits in 127. *)
    assert (Hw : 0 <= t * (z / 2 ^ 254) < 2 ^ 381).
    { split.
      - apply Z.mul_nonneg_nonneg; lia.
      - apply Z.le_lt_trans with ((2 ^ 126 - 1) * (2 ^ 255 - 1)).
        + apply Z.mul_le_mono_nonneg; lia.
        + lia. }
    assert (Hu1 : 0 <= t * (z / 2 ^ 254) / 2 ^ 254 < 2 ^ 127).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    unfold red_solinas, mask254.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !Z.land_ones by lia.
    apply red_solinas_core with (z1 := z / 2 ^ 254).
    - apply Z.div_mod; lia.
    - apply Z.div_mod; lia.
    - apply Z.mod_pos_bound; lia.
    - apply Z.mod_pos_bound; lia.
    - split.
      + apply Z.mul_nonneg_nonneg; lia.
      + apply Z.le_lt_trans with ((2 ^ 126 - 1) * (2 ^ 127 - 1)).
        * apply Z.mul_le_mono_nonneg; lia.
        * lia.
  Qed.

  Lemma mul_solinas_spec (x y : Z) :
    0 <= x < p ->
    0 <= y < p ->
    mul_solinas x y = (x * y) mod p.
  Proof.
    intros Hx Hy.
    apply red_solinas_spec.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - apply Z.le_lt_trans with ((p - 1) * (p - 1)).
      + apply Z.mul_le_mono_nonneg; lia.
      + pose proof p_pos; lia.
  Qed.
End Solinas.

(** ** The Solinas shape of the two Pasta primes *)

Lemma t_q_range : 0 < Primes.t_q < 2 ^ 126.
Proof. vm_compute; split; reflexivity. Qed.

Lemma t_p_range : 0 < Primes.t_p < 2 ^ 126.
Proof. vm_compute; split; reflexivity. Qed.

Lemma pallas_q_shape : Primes.pallas_q = 2 ^ 254 + Primes.t_q.
Proof. reflexivity. Qed.

Lemma pallas_p_shape : Primes.pallas_p = 2 ^ 254 + Primes.t_p.
Proof. reflexivity. Qed.

Lemma pallas_q_pos : 0 < Primes.pallas_q.
Proof. exact (p_pos Primes.t_q Primes.pallas_q t_q_range pallas_q_shape). Qed.

Lemma pallas_p_pos : 0 < Primes.pallas_p.
Proof. exact (p_pos Primes.t_p Primes.pallas_p t_p_range pallas_p_shape). Qed.

(** ** Operations modulo [pallas_q] *)

Definition redq (z : Z) : Z :=
  let z0 := Z.land z mask254 in
  let z1 := Z.shiftr z 254 in
  let w := Primes.t_q * z1 in
  let u0 := Z.land w mask254 in
  let u1 := Z.shiftr w 254 in
  let r := z0 - u0 + Primes.t_q * u1 in
  let r := if r <? 0 then r + Primes.pallas_q else r in
  if Primes.pallas_q <=? r then r - Primes.pallas_q else r.

Definition mulq (x y : Z) : Z := redq (x * y).

Definition addq (x y : Z) : Z :=
  let s := x + y in
  if Primes.pallas_q <=? s then s - Primes.pallas_q else s.

Definition subq (x y : Z) : Z :=
  let d := x - y in
  if d <? 0 then d + Primes.pallas_q else d.

Definition oppq (x : Z) : Z :=
  if x =? 0 then 0 else Primes.pallas_q - x.

Lemma redq_eq (z : Z) :
  redq z = red_solinas Primes.t_q Primes.pallas_q z.
Proof. reflexivity. Qed.

Lemma redq_spec (z : Z) :
  0 <= z < Primes.pallas_q * Primes.pallas_q ->
  redq z = z mod Primes.pallas_q.
Proof.
  intros Hz.
  rewrite redq_eq.
  now apply red_solinas_spec with (t := Primes.t_q);
    [exact t_q_range | exact pallas_q_shape | ].
Qed.

Lemma mulq_spec (x y : Z) :
  0 <= x < Primes.pallas_q ->
  0 <= y < Primes.pallas_q ->
  mulq x y = BinOp.mul (p := Primes.pallas_q) x y.
Proof.
  intros Hx Hy.
  unfold mulq, BinOp.mul.
  apply redq_spec.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.le_lt_trans with ((Primes.pallas_q - 1) * (Primes.pallas_q - 1)).
    + apply Z.mul_le_mono_nonneg; lia.
    + pose proof pallas_q_pos; lia.
Qed.

Lemma addq_spec (x y : Z) :
  0 <= x < Primes.pallas_q ->
  0 <= y < Primes.pallas_q ->
  addq x y = BinOp.add (p := Primes.pallas_q) x y.
Proof.
  intros Hx Hy.
  unfold BinOp.add.
  change (addq x y) with (add_reduced Primes.pallas_q x y).
  now apply add_reduced_spec; [exact pallas_q_pos | | ].
Qed.

Lemma subq_spec (x y : Z) :
  0 <= x < Primes.pallas_q ->
  0 <= y < Primes.pallas_q ->
  subq x y = BinOp.sub (p := Primes.pallas_q) x y.
Proof.
  intros Hx Hy.
  unfold BinOp.sub.
  change (subq x y) with (sub_reduced Primes.pallas_q x y).
  now apply sub_reduced_spec; [exact pallas_q_pos | | ].
Qed.

Lemma oppq_spec (x : Z) :
  0 <= x < Primes.pallas_q ->
  oppq x = UnOp.opp (p := Primes.pallas_q) x.
Proof.
  intros Hx.
  unfold UnOp.opp.
  change (oppq x) with (opp_reduced Primes.pallas_q x).
  now apply opp_reduced_spec; [exact pallas_q_pos | ].
Qed.

(** ** Operations modulo [pallas_p] *)

Definition redp (z : Z) : Z :=
  let z0 := Z.land z mask254 in
  let z1 := Z.shiftr z 254 in
  let w := Primes.t_p * z1 in
  let u0 := Z.land w mask254 in
  let u1 := Z.shiftr w 254 in
  let r := z0 - u0 + Primes.t_p * u1 in
  let r := if r <? 0 then r + Primes.pallas_p else r in
  if Primes.pallas_p <=? r then r - Primes.pallas_p else r.

Definition mulp (x y : Z) : Z := redp (x * y).

Definition addp (x y : Z) : Z :=
  let s := x + y in
  if Primes.pallas_p <=? s then s - Primes.pallas_p else s.

Definition subp (x y : Z) : Z :=
  let d := x - y in
  if d <? 0 then d + Primes.pallas_p else d.

Definition oppp (x : Z) : Z :=
  if x =? 0 then 0 else Primes.pallas_p - x.

Lemma redp_eq (z : Z) :
  redp z = red_solinas Primes.t_p Primes.pallas_p z.
Proof. reflexivity. Qed.

Lemma redp_spec (z : Z) :
  0 <= z < Primes.pallas_p * Primes.pallas_p ->
  redp z = z mod Primes.pallas_p.
Proof.
  intros Hz.
  rewrite redp_eq.
  now apply red_solinas_spec with (t := Primes.t_p);
    [exact t_p_range | exact pallas_p_shape | ].
Qed.

Lemma mulp_spec (x y : Z) :
  0 <= x < Primes.pallas_p ->
  0 <= y < Primes.pallas_p ->
  mulp x y = BinOp.mul (p := Primes.pallas_p) x y.
Proof.
  intros Hx Hy.
  unfold mulp, BinOp.mul.
  apply redp_spec.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.le_lt_trans with ((Primes.pallas_p - 1) * (Primes.pallas_p - 1)).
    + apply Z.mul_le_mono_nonneg; lia.
    + pose proof pallas_p_pos; lia.
Qed.

Lemma addp_spec (x y : Z) :
  0 <= x < Primes.pallas_p ->
  0 <= y < Primes.pallas_p ->
  addp x y = BinOp.add (p := Primes.pallas_p) x y.
Proof.
  intros Hx Hy.
  unfold BinOp.add.
  change (addp x y) with (add_reduced Primes.pallas_p x y).
  now apply add_reduced_spec; [exact pallas_p_pos | | ].
Qed.

Lemma subp_spec (x y : Z) :
  0 <= x < Primes.pallas_p ->
  0 <= y < Primes.pallas_p ->
  subp x y = BinOp.sub (p := Primes.pallas_p) x y.
Proof.
  intros Hx Hy.
  unfold BinOp.sub.
  change (subp x y) with (sub_reduced Primes.pallas_p x y).
  now apply sub_reduced_spec; [exact pallas_p_pos | | ].
Qed.

Lemma oppp_spec (x : Z) :
  0 <= x < Primes.pallas_p ->
  oppp x = UnOp.opp (p := Primes.pallas_p) x.
Proof.
  intros Hx.
  unfold UnOp.opp.
  change (oppp x) with (opp_reduced Primes.pallas_p x).
  now apply opp_reduced_spec; [exact pallas_p_pos | ].
Qed.
