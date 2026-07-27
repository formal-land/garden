Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.poseidon.pow5.
Require Import Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module State.
  Record t : Set := {
    x0 : Z;
    x1 : Z;
    x2 : Z;
  }.

  Definition get (state : t) (column : nat) : Z :=
    match column with
    | O => state.(x0)
    | S O => state.(x1)
    | S (S O) => state.(x2)
    | _ => 0
    end.

  Global Instance IsMapMod : MapMod t := {
    map_mod state := {|
      x0 := UnOp.from state.(x0);
      x1 := UnOp.from state.(x1);
      x2 := UnOp.from state.(x2);
    |};
  }.
End State.

Definition coeff
    (rows : list (list Z))
    (row column : nat)
    : Z :=
  p128pow5t3.get rows row column.

Definition lin
    (rows : list (list Z))
    (row : nat)
    (state : State.t)
    : Z :=
  coeff rows row 0 *F state.(State.x0) +F
  coeff rows row 1 *F state.(State.x1) +F
  coeff rows row 2 *F state.(State.x2).

Definition matrix_mul
    (rows : list (list Z))
    (state : State.t)
    : State.t := {|
  State.x0 := lin rows 0 state;
  State.x1 := lin rows 1 state;
  State.x2 := lin rows 2 state;
|}.

Definition mds_mul : State.t -> State.t :=
  matrix_mul p128pow5t3.mds.

Definition mds_inv_mul : State.t -> State.t :=
  matrix_mul p128pow5t3.mds_inv.

Module MatrixInverse.
  (** A sum of three reduced terms collapses to a single modulo. *)
  Lemma add3_mod (u v w : Z) :
      ((u mod Primes.pallas_p + v mod Primes.pallas_p) mod Primes.pallas_p +
        w mod Primes.pallas_p) mod Primes.pallas_p =
        (u + v + w) mod Primes.pallas_p.
  Proof.
    pose proof (prime_range (p := Primes.pallas_p)).
    now rewrite (Z.add_mod (u + v) w), (Z.add_mod u v) by lia.
  Qed.

  (** A linear combination of reduced inputs is the reduced integer
      dot-product. *)
  Lemma lin_mod (c0 c1 c2 y0 y1 y2 : Z) :
      c0 *F UnOp.from y0 +F c1 *F UnOp.from y1 +F c2 *F UnOp.from y2 =
        (c0 * y0 + c1 * y1 + c2 * y2) mod Primes.pallas_p.
  Proof.
    unfold BinOp.add, BinOp.mul, UnOp.from.
    rewrite !Zmult_mod_idemp_r.
    apply add3_mod.
  Qed.

  (** Each coordinate of the composition of two linear maps collapses, modulo
      [p], to a single dot-product of integers applied to the initial
      coordinates. *)
  Lemma compose_coordinate_eq
      (a0 a1 a2 b00 b01 b02 b10 b11 b12 b20 b21 b22 x0 x1 x2 : Z) :
      a0 *F (b00 *F UnOp.from x0 +F b01 *F UnOp.from x1 +F b02 *F UnOp.from x2) +F
      a1 *F (b10 *F UnOp.from x0 +F b11 *F UnOp.from x1 +F b12 *F UnOp.from x2) +F
      a2 *F (b20 *F UnOp.from x0 +F b21 *F UnOp.from x1 +F b22 *F UnOp.from x2) =
      ((a0 * b00 + a1 * b10 + a2 * b20) * x0 +
       (a0 * b01 + a1 * b11 + a2 * b21) * x1 +
       (a0 * b02 + a1 * b12 + a2 * b22) * x2) mod Primes.pallas_p.
  Proof.
    rewrite !lin_mod.
    unfold BinOp.add, BinOp.mul.
    rewrite !Zmult_mod_idemp_r.
    rewrite add3_mod.
    f_equal; ring.
  Qed.

  (** A dot-product whose coefficients reduce to [(1, 0, 0)] modulo [p]
      returns its first argument modulo [p]. *)
  Lemma identity_row_0 (s0 s1 s2 x0 x1 x2 : Z)
      (Hs0 : s0 mod Primes.pallas_p = 1)
      (Hs1 : s1 mod Primes.pallas_p = 0)
      (Hs2 : s2 mod Primes.pallas_p = 0) :
      (s0 * x0 + s1 * x1 + s2 * x2) mod Primes.pallas_p =
        x0 mod Primes.pallas_p.
  Proof.
    pose proof (prime_range (p := Primes.pallas_p)).
    rewrite Z.add_mod by lia.
    rewrite (Z.add_mod (s0 * x0)) by lia.
    rewrite (Z.mul_mod s0), (Z.mul_mod s1), (Z.mul_mod s2) by lia.
    rewrite Hs0, Hs1, Hs2.
    rewrite Z.mul_1_l, !Z.mul_0_l, !Zmod_0_l, !Z.add_0_r, !Zmod_mod.
    reflexivity.
  Qed.

  Lemma identity_row_1 (s0 s1 s2 x0 x1 x2 : Z)
      (Hs0 : s0 mod Primes.pallas_p = 0)
      (Hs1 : s1 mod Primes.pallas_p = 1)
      (Hs2 : s2 mod Primes.pallas_p = 0) :
      (s0 * x0 + s1 * x1 + s2 * x2) mod Primes.pallas_p =
        x1 mod Primes.pallas_p.
  Proof.
    replace (s0 * x0 + s1 * x1 + s2 * x2)
      with (s1 * x1 + s0 * x0 + s2 * x2)
      by ring.
    now apply identity_row_0.
  Qed.

  Lemma identity_row_2 (s0 s1 s2 x0 x1 x2 : Z)
      (Hs0 : s0 mod Primes.pallas_p = 0)
      (Hs1 : s1 mod Primes.pallas_p = 0)
      (Hs2 : s2 mod Primes.pallas_p = 1) :
      (s0 * x0 + s1 * x1 + s2 * x2) mod Primes.pallas_p =
        x2 mod Primes.pallas_p.
  Proof.
    replace (s0 * x0 + s1 * x1 + s2 * x2)
      with (s2 * x2 + s0 * x0 + s1 * x1)
      by ring.
    now apply identity_row_0.
  Qed.

  (** Composing two [matrix_mul] whose integer product reduces to the
      identity matrix modulo [p] gives back the reduced state. *)
  Lemma matrix_compose_identity
      (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Z)
      (b00 b01 b02 b10 b11 b12 b20 b21 b22 : Z)
      (H00 : (a00 * b00 + a01 * b10 + a02 * b20) mod Primes.pallas_p = 1)
      (H01 : (a00 * b01 + a01 * b11 + a02 * b21) mod Primes.pallas_p = 0)
      (H02 : (a00 * b02 + a01 * b12 + a02 * b22) mod Primes.pallas_p = 0)
      (H10 : (a10 * b00 + a11 * b10 + a12 * b20) mod Primes.pallas_p = 0)
      (H11 : (a10 * b01 + a11 * b11 + a12 * b21) mod Primes.pallas_p = 1)
      (H12 : (a10 * b02 + a11 * b12 + a12 * b22) mod Primes.pallas_p = 0)
      (H20 : (a20 * b00 + a21 * b10 + a22 * b20) mod Primes.pallas_p = 0)
      (H21 : (a20 * b01 + a21 * b11 + a22 * b21) mod Primes.pallas_p = 0)
      (H22 : (a20 * b02 + a21 * b12 + a22 * b22) mod Primes.pallas_p = 1)
      (state : State.t) :
      matrix_mul [ [a00; a01; a02]; [a10; a11; a12]; [a20; a21; a22] ]
        (matrix_mul [ [b00; b01; b02]; [b10; b11; b12]; [b20; b21; b22] ]
          (Field.map_mod state)) =
        Field.map_mod state.
  Proof.
    unfold matrix_mul, lin, coeff, p128pow5t3.get.
    with_strategy opaque [BinOp.add BinOp.mul UnOp.from] cbn.
    f_equal; rewrite compose_coordinate_eq; unfold UnOp.from.
    - now apply identity_row_0.
    - now apply identity_row_1.
    - now apply identity_row_2.
  Qed.
End MatrixInverse.

Lemma mds_mul_mds_inv_identity (state : State.t) :
    mds_mul (mds_inv_mul (Field.map_mod state)) =
      Field.map_mod state.
Proof.
  unfold mds_mul, mds_inv_mul, p128pow5t3.mds, p128pow5t3.mds_inv.
  apply MatrixInverse.matrix_compose_identity; now vm_compute.
Qed.

Lemma mds_inv_mul_mds_identity (state : State.t) :
    mds_inv_mul (mds_mul (Field.map_mod state)) =
      Field.map_mod state.
Proof.
  unfold mds_mul, mds_inv_mul, p128pow5t3.mds, p128pow5t3.mds_inv.
  apply MatrixInverse.matrix_compose_identity; now vm_compute.
Qed.

Lemma mds_inv_mul_injective
    (left right : State.t)
    (H : mds_inv_mul (Field.map_mod left) = mds_inv_mul (Field.map_mod right)) :
    Field.map_mod left = Field.map_mod right.
Proof.
  rewrite <- (mds_mul_mds_inv_identity left).
  rewrite <- (mds_mul_mds_inv_identity right).
  now rewrite H.
Qed.

Lemma dot3 (c0 c1 c2 x0 x1 x2 : Z) :
    c0 *F x0 +F c1 *F x1 +F c2 *F x2 =
    x0 *F UnOp.from c0 +F x1 *F UnOp.from c1 +F x2 *F UnOp.from c2.
Proof.
  FieldRewrite.run.
  now unfold BinOp.mul;
    rewrite (Z.mul_comm c0 x0), (Z.mul_comm c1 x1), (Z.mul_comm c2 x2).
Qed.

Lemma mds_roundtrip (state : State.t)
    (H0 : UnOp.from state.(State.x0) = state.(State.x0))
    (H1 : UnOp.from state.(State.x1) = state.(State.x1))
    (H2 : UnOp.from state.(State.x2) = state.(State.x2)) :
    mds_mul (mds_inv_mul state) = state.
Proof.
  assert (Hmm : Field.map_mod state = state).
  { destruct state; cbn in *; now rewrite H0, H1, H2. }
  rewrite <- Hmm.
  apply mds_mul_mds_inv_identity.
Qed.

Definition pow5 (value : Z) : Z :=
  let value_2 := value *F value in
  let value_4 := value_2 *F value_2 in
  value_4 *F value.

Module FullRound.
  Definition output_coordinate
      (row : nat)
      (state_0 state_1 state_2 : Z)
      (round_constant_0 round_constant_1 round_constant_2 : Z)
      : Z :=
    let state_0_sbox := pow5 (state_0 +F round_constant_0) in
    let state_1_sbox := pow5 (state_1 +F round_constant_1) in
    let state_2_sbox := pow5 (state_2 +F round_constant_2) in
    state_0_sbox *F UnOp.from (p128pow5t3.mds_coeff row 0) +F
    state_1_sbox *F UnOp.from (p128pow5t3.mds_coeff row 1) +F
    state_2_sbox *F UnOp.from (p128pow5t3.mds_coeff row 2).

  Definition output
      (state_0 state_1 state_2 : Z)
      (round_constant_0 round_constant_1 round_constant_2 : Z)
      : State.t := {|
    State.x0 :=
      output_coordinate
        0
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
    State.x1 :=
      output_coordinate
        1
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
    State.x2 :=
      output_coordinate
        2
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
  |}.

  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QPoseidonFull ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ pow5.full_round_gate ⟧ (region, row)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output, output_coordinate, pow5.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
      cbn in *.
    hauto lq: on.
  Qed.

  (* Chip-level determinism: [pow5.synthesize] enables
     [QPoseidonFull] at offset 0 of region [Poseidon.FullRound], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic].
     See [CompleteAddition.synthesize_correct] (add_proof.v) for the
     template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
            ConstraintSystem.empty)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.FullRound, 0);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.FullRound, 0);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.FullRound, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.FullRound, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - (* [QPoseidonFull] enabled at offset 0 of region [Poseidon.FullRound]. *)
      cbn in Hfacts.
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ Selector.QPoseidonFull
        (RegionId.Poseidon RegionId.Poseidon.FullRound) 0 H1).
    - (* The full-round gate is the first of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
          ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.poseidon.pow5.full_round_gate
        (RegionId.Poseidon RegionId.Poseidon.FullRound) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End FullRound.

Module PartialRound.
  Definition sbox_partial (state : State.t) : State.t := {|
    State.x0 := pow5 state.(State.x0);
    State.x1 := state.(State.x1);
    State.x2 := state.(State.x2);
  |}.

  Definition output
      (state_0 state_1 state_2 : Z)
      (round_constant_a_0 round_constant_a_1 round_constant_a_2 : Z)
      (round_constant_b_0 round_constant_b_1 round_constant_b_2 : Z)
      : State.t :=
    let after_a :=
      mds_mul (sbox_partial {|
        State.x0 := state_0 +F round_constant_a_0;
        State.x1 := state_1 +F round_constant_a_1;
        State.x2 := state_2 +F round_constant_a_2;
      |}) in
    mds_mul (sbox_partial {|
      State.x0 := after_a.(State.x0) +F round_constant_b_0;
      State.x1 := after_a.(State.x1) +F round_constant_b_1;
      State.x2 := after_a.(State.x2) +F round_constant_b_2;
    |}).

  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QPoseidonPartial ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ pow5.partial_rounds_gate ⟧ (region, row)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold pow5.partial_rounds_gate in Hgate.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from
      p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff]
      cbn in Hgate.
    destruct Hgate as (h1 & h2 & h3 & h4).
    specialize (h1 Hselector).
    specialize (h2 Hselector).
    specialize (h3 Hselector).
    specialize (h4 Hselector).
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from
      p128pow5t3.mds_coeff p128pow5t3.mds_inv_coeff
      output sbox_partial pow5 mds_mul mds_inv_mul matrix_mul lin coeff]
      cbn.
    set (s0 := UnOp.from (Γ.(Assignment.advice) Advice.A6 region
      (rotated_row row Rotation.cur))) in *.
    set (s1 := UnOp.from (Γ.(Assignment.advice) Advice.A7 region
      (rotated_row row Rotation.cur))) in *.
    set (s2 := UnOp.from (Γ.(Assignment.advice) Advice.A8 region
      (rotated_row row Rotation.cur))) in *.
    set (a0 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs2 region
      (rotated_row row Rotation.cur))) in *.
    set (a1 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs3 region
      (rotated_row row Rotation.cur))) in *.
    set (a2 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs4 region
      (rotated_row row Rotation.cur))) in *.
    set (b0 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs5 region
      (rotated_row row Rotation.cur))) in *.
    set (b1 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs6 region
      (rotated_row row Rotation.cur))) in *.
    set (b2 := UnOp.from (Γ.(Assignment.fixed) Fixed.LagrangeCoeffs7 region
      (rotated_row row Rotation.cur))) in *.
    set (m0 := UnOp.from (Γ.(Assignment.advice) Advice.A5 region
      (rotated_row row Rotation.cur))) in *.
    set (n0 := UnOp.from (Γ.(Assignment.advice) Advice.A6 region
      (rotated_row row Rotation.next))) in *.
    set (n1 := UnOp.from (Γ.(Assignment.advice) Advice.A7 region
      (rotated_row row Rotation.next))) in *.
    set (n2 := UnOp.from (Γ.(Assignment.advice) Advice.A8 region
      (rotated_row row Rotation.next))) in *.
    (* Fold the [pow5] applications back so the round S-boxes are visible. *)
    assert (h1' : pow5 (s0 +F a0) = m0) by exact h1.
    assert (h2' :
      pow5 (m0 *F UnOp.from (mds_coeff 0 0) +F
            (s1 +F a1) *F UnOp.from (mds_coeff 0 1) +F
            (s2 +F a2) *F UnOp.from (mds_coeff 0 2) +F b0) =
      n0 *F UnOp.from (mds_inv_coeff 0 0) +F
      n1 *F UnOp.from (mds_inv_coeff 0 1) +F
      n2 *F UnOp.from (mds_inv_coeff 0 2)) by exact h2.
    clear h1 h2.
    (* Round a followed by the MDS matrix maps the input state to the
       intermediate state read off the partial-round constraints. *)
    assert (Ha :
      mds_mul (sbox_partial {|
        State.x0 := s0 +F a0;
        State.x1 := s1 +F a1;
        State.x2 := s2 +F a2;
      |}) = {|
        State.x0 := m0 *F UnOp.from (mds_coeff 0 0) +F
          (s1 +F a1) *F UnOp.from (mds_coeff 0 1) +F
          (s2 +F a2) *F UnOp.from (mds_coeff 0 2);
        State.x1 := m0 *F UnOp.from (mds_coeff 1 0) +F
          (s1 +F a1) *F UnOp.from (mds_coeff 1 1) +F
          (s2 +F a2) *F UnOp.from (mds_coeff 1 2);
        State.x2 := m0 *F UnOp.from (mds_coeff 2 0) +F
          (s1 +F a1) *F UnOp.from (mds_coeff 2 1) +F
          (s2 +F a2) *F UnOp.from (mds_coeff 2 2);
      |}).
    {
      unfold mds_mul, matrix_mul, lin, sbox_partial.
      cbn [State.x0 State.x1 State.x2].
      rewrite h1'.
      f_equal; apply dot3.
    }
    (* The next-row state is the MDS-inverse image of round b's S-box output,
       so applying the MDS matrix recovers it. *)
    transitivity (mds_mul (mds_inv_mul {|
      State.x0 := n0; State.x1 := n1; State.x2 := n2;
    |})).
    - symmetry.
      apply mds_roundtrip; cbn [State.x0 State.x1 State.x2];
        apply FieldRewrite.from_from.
    - unfold output.
      rewrite !Ha.
      cbn [State.x0 State.x1 State.x2].
      f_equal.
      unfold mds_inv_mul, matrix_mul, lin, sbox_partial.
      cbn [State.x0 State.x1 State.x2].
      f_equal.
      + rewrite dot3, h2'. reflexivity.
      + rewrite dot3, h3 at 1. reflexivity.
      + rewrite dot3, h4 at 1. reflexivity.
  Qed.

  (* Chip-level determinism: [pow5.synthesize] enables
     [QPoseidonPartial] at offset 0 of region [Poseidon.PartialRounds], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic]. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
            ConstraintSystem.empty)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PartialRounds, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - (* [QPoseidonPartial] enabled at offset 0 of region [Poseidon.PartialRounds]. *)
      cbn in Hfacts.
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ Selector.QPoseidonPartial
        (RegionId.Poseidon RegionId.Poseidon.PartialRounds) 0 H2).
    - (* The partial-rounds gate is the second of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
          ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.poseidon.pow5.partial_rounds_gate
        (RegionId.Poseidon RegionId.Poseidon.PartialRounds) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End PartialRound.

Module PadAndAdd.
  Definition output
      (previous_state_0 previous_state_1 previous_state_2 : Z)
      (current_state_0 current_state_1 : Z)
      : State.t := {|
    State.x0 := previous_state_0 +F current_state_0;
    State.x1 := previous_state_1 +F current_state_1;
    State.x2 := previous_state_2;
  |}.

  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QPoseidonPadAndAdd ⟧ (region, row) <> 0)
      (Hgate : Γ ⊢ ⟦ pow5.pad_and_add_gate ⟧ (region, row)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
      cbn in *.
    hauto lq: on.
  Qed.

  (* Chip-level determinism: [pow5.synthesize] enables
     [QPoseidonPadAndAdd] at offset 0 of region [Poseidon.PadAndAdd], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic]. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
            ConstraintSystem.empty)) :
      {|
        State.x0 := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0);
        State.x1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0);
        State.x2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
          (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧
            (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.prev ⟧
            (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧
            (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
            (RegionId.Poseidon RegionId.Poseidon.PadAndAdd, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - (* [QPoseidonPadAndAdd] enabled at offset 0 of region [Poseidon.PadAndAdd]. *)
      cbn in Hfacts.
      destruct Hfacts as (H1 & H2 & H3 & Htrivial).
      exact (enabled_nonzero Γ Selector.QPoseidonPadAndAdd
        (RegionId.Poseidon RegionId.Poseidon.PadAndAdd) 0 H3).
    - (* The pad-and-add gate is the third of the three configured gates. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.poseidon.pow5.configure
          ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.poseidon.pow5.pad_and_add_gate
        (RegionId.Poseidon RegionId.Poseidon.PadAndAdd) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End PadAndAdd.
