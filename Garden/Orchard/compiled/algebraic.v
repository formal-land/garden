(** * Algebraic acceptance of the derived Orchard system, down to the Action statement.

    The L1 rung of the refinement ladder for the concrete Orchard action
    circuit: [orchard_algebraic_accepts] states the three all-challenge
    identity families ([PlonkishAlgebraic.algebraic_accepts]) over the
    configure-derived system [OrchardCompiledCheck.compiled], the checked
    evaluation-domain root [PolyDomain.omega] (k = 11, n = 2048), the
    permutation chunking [chunk_len = cs.degree() - 2] read off the
    modeled system degree, and the coset label assignment
    [delta^i * omega^j] with [delta = GENERATOR^(2^S)] of the Pallas base
    field ([pasta_curves] [fields/fp.rs]).

    [orchard_algebraic_sound] discharges algebraic acceptance of a
    replayed witness grid into [orchard_compiled_accepts], the compiled
    satisfaction the R2 assembly consumes; the committed chain
    ([orchard_compiled_sound] / [orchard_compiled_operational_sound] /
    [orchard_compiled_action_statement]) then carries it to
    [mock_prover_accepts], to the relational [circuit_holds], and to the
    §4.18.4 Action statement with [ValidActionInputs].

    Every decidable side condition is a [vm_compute] certificate on the
    concrete instance: the σ mapping shape and boundary-row fixed points,
    the [delta] order and small-power facts anchoring the coset-label
    injectivity, the lookup replacement exactness and combination-column
    avoidance of the substitution seam, the canonical fixed-plane event
    values, and the table-padding row-0 pinning.  The witness-facing
    hypotheses of the headline theorems are acceptance itself, the replay
    equation, and one canonicity condition: the witness planes carry
    canonical residues on the permutation cell space (the committed
    values of a real prover are field elements). *)

Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.mock.
Require Import Garden.Halo2.plonkish.compile.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Halo2.plonkish.lookup_compile.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Halo2.plonkish.vanishing.
Require Import Garden.Halo2.plonkish.permutation_poly.
Require Import Garden.Halo2.plonkish.lookup_poly.
Require Import Garden.Halo2.plonkish.algebraic.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.main.
Require Garden.Orchard.circuit.
Require Garden.Orchard.protocol_spec.
Require Garden.Orchard.circuit_proof.inputs.
Require Garden.Orchard.circuit_proof.merkle.
Require Garden.Orchard.circuit_proof.note_commit.cmx.
Require Garden.Orchard.circuit_proof.valid_action_inputs.

Import ListNotations.
Import Plonkish.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardCompiledAlgebraic.

(** ** The coset generator [delta]

    [delta = GENERATOR^(2^S)] of the Pallas base field, with
    [GENERATOR = 5] and [S = 32] ([pasta_curves] [fields/fp.rs]): a
    [t]-th root of unity for the odd cofactor [t = (p - 1) / 2^32].  The
    permutation argument labels the cell [(i, j)] of the equality space
    with [delta^i * omega^j]; the label injectivity below rests on the
    order split — [delta] generates odd order, [omega] order [2^11]. *)

Definition delta : Z :=
  0x0a757d0f0006ab6cbd455b7112a5049df5e4f3f13eee56366a6ccd20dd7b9ba2.

(** The odd cofactor [t] with [p - 1 = 2^32 * t]. *)
Definition t_odd : Z :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed.

(** The inverse of [t] modulo [2^11] and the matching cofactor:
    [t * 1253 = 1 + 2048 * t_cofactor]. *)
Definition t_cofactor : Z :=
  4123634420646942341640352771488720365493226128350303904095563892239.

Lemma delta_generator :
  fast_pow_modulo_positive 1 5 Primes.pallas_p 4294967296 = delta.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma p_split : Primes.pallas_p - 1 = 4294967296 * t_odd.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma t_odd_unit : t_odd * 1253 = 1 + 2048 * t_cofactor.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma t_odd_nonneg : 0 <= t_odd.
Proof.
  apply Z.leb_le.
  vm_compute.
  reflexivity.
Qed.

Lemma t_cofactor_nonneg : 0 <= t_cofactor.
Proof.
  apply Z.leb_le.
  vm_compute.
  reflexivity.
Qed.

Lemma delta_canonical : delta mod Primes.pallas_p = delta.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma delta_nonzero : delta <> 0.
Proof.
  apply Z.eqb_neq.
  vm_compute.
  reflexivity.
Qed.

Lemma delta_pow_t_check :
  fast_pow_modulo_positive 1 delta Primes.pallas_p
    6739986666787659948666753771754907668419893943225396963757154709741%positive
  = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** [delta^t = 1]: [delta] lies in the odd-order subgroup. *)
Lemma delta_order_t : Fpow (p := Primes.pallas_p) delta t_odd = 1.
Proof.
  assert (Hp : 0 < Primes.pallas_p)
    by (pose proof PolyDomain.pallas_p_big; lia).
  pose proof (fast_pow_correct Primes.pallas_p Hp
    6739986666787659948666753771754907668419893943225396963757154709741%positive
    1 delta) as Hf.
  rewrite Z.mul_1_l in Hf.
  unfold Fpow, UnOp.from.
  change t_odd with
    (Z.pos 6739986666787659948666753771754907668419893943225396963757154709741).
  rewrite <- Hf.
  exact delta_pow_t_check.
Qed.

(** No power [delta^k] with [1 <= k <= 14] is [1]: the 15 permutation
    columns receive distinct [delta]-cosets. *)
Lemma delta_small_pows_check :
  List.forallb
    (fun k => negb (Fpow (p := Primes.pallas_p) delta (Z.of_nat k) =? 1))
    (List.seq 1 14) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma delta_small_pow_neq (k : Z) :
  1 <= k <= 14 -> Fpow (p := Primes.pallas_p) delta k <> 1.
Proof.
  intros Hk Heq.
  pose proof delta_small_pows_check as Hc.
  rewrite List.forallb_forall in Hc.
  assert (Hin : List.In (Z.to_nat k) (List.seq 1 14))
    by (apply List.in_seq; clear -Hk; lia).
  specialize (Hc _ Hin).
  rewrite Z2Nat.id in Hc by lia.
  rewrite Heq in Hc.
  discriminate Hc.
Qed.

(** ** Field-power bookkeeping over the concrete modulus *)

Lemma fpow_canonical (a n : Z) :
  Fpow (p := Primes.pallas_p) a n mod Primes.pallas_p =
  Fpow (p := Primes.pallas_p) a n.
Proof.
  exact (Fpow_reduced a n).
Qed.

Lemma fpow_one (n : Z) : 0 <= n -> Fpow (p := Primes.pallas_p) 1 n = 1.
Proof.
  intros Hn.
  unfold Fpow, UnOp.from.
  rewrite Z.pow_1_l by exact Hn.
  apply Z.mod_1_l.
  exact PolyDomain.pallas_p_big.
Qed.

Lemma fmul_one_r (x : Z) :
  BinOp.mul (p := Primes.pallas_p) x 1 = x mod Primes.pallas_p.
Proof.
  unfold BinOp.mul.
  f_equal.
  ring.
Qed.

Lemma fmul_one_l (x : Z) :
  BinOp.mul (p := Primes.pallas_p) 1 x = x mod Primes.pallas_p.
Proof.
  unfold BinOp.mul.
  f_equal.
  ring.
Qed.

Lemma fmul_swap (a b c d : Z) :
  BinOp.mul (p := Primes.pallas_p)
    (BinOp.mul (p := Primes.pallas_p) a b)
    (BinOp.mul (p := Primes.pallas_p) c d) =
  BinOp.mul (p := Primes.pallas_p)
    (BinOp.mul (p := Primes.pallas_p) a c)
    (BinOp.mul (p := Primes.pallas_p) b d).
Proof.
  unfold BinOp.mul.
  rewrite !Zmult_mod_idemp_l.
  rewrite !Zmult_mod_idemp_r.
  f_equal.
  ring.
Qed.

Lemma fpow_pow_swap (a m n : Z) :
  0 <= m -> 0 <= n ->
  Fpow (p := Primes.pallas_p) (Fpow (p := Primes.pallas_p) a m) n =
  Fpow (p := Primes.pallas_p) (Fpow (p := Primes.pallas_p) a n) m.
Proof.
  intros Hm Hn.
  rewrite Fpow_mul by assumption.
  rewrite Z.mul_comm.
  rewrite <- Fpow_mul by assumption.
  reflexivity.
Qed.

Lemma omega_2048 : Fpow (p := Primes.pallas_p) PolyDomain.omega 2048 = 1.
Proof.
  exact PolyDomain.omega_order_full.
Qed.

(** [omega]-powers reduce modulo the order [2048]. *)
Lemma omega_pow_reduce (m : Z) (Hm : 0 <= m) :
  Fpow (p := Primes.pallas_p) PolyDomain.omega m =
  Fpow (p := Primes.pallas_p) PolyDomain.omega (m mod 2048).
Proof.
  assert (Hq : 0 <= m / 2048) by (apply Z.div_pos; lia).
  assert (Hr : 0 <= m mod 2048 < 2048) by (apply Z.mod_pos_bound; lia).
  assert (H2048q : 0 <= 2048 * (m / 2048)) by lia.
  rewrite (Z.div_mod m 2048 ltac:(lia)) at 1.
  rewrite Fpow_add by lia.
  rewrite <- (Fpow_mul PolyDomain.omega 2048 (m / 2048) ltac:(lia) Hq).
  rewrite omega_2048.
  rewrite fpow_one by exact Hq.
  rewrite fmul_one_l.
  exact (fpow_canonical _ _).
Qed.

(** An [omega]-power killed by the odd cofactor [t] is already [1]: the
    orders [2^11] and [t] are coprime. *)
Lemma omega_pow_kill_t (m : Z) (Hm : 0 <= m)
    (Hmt : Fpow (p := Primes.pallas_p) PolyDomain.omega (m * t_odd) = 1) :
  Fpow (p := Primes.pallas_p) PolyDomain.omega m = 1.
Proof.
  pose proof t_odd_nonneg as Ht.
  pose proof t_cofactor_nonneg as Hc.
  assert (Hmt_nonneg : 0 <= m * t_odd)
    by (apply Z.mul_nonneg_nonneg; assumption).
  assert (Hmc : 0 <= m * t_cofactor)
    by (apply Z.mul_nonneg_nonneg; assumption).
  assert (H2048c : 0 <= 2048 * (m * t_cofactor)) by lia.
  assert (Hu :
    Fpow (p := Primes.pallas_p) PolyDomain.omega (m * t_odd * 1253) = 1).
  { rewrite <- Fpow_mul by lia.
    rewrite Hmt.
    apply fpow_one.
    lia. }
  replace (m * t_odd * 1253) with (m + 2048 * (m * t_cofactor)) in Hu.
  2: {
    replace (m * t_odd * 1253) with (m * (t_odd * 1253)) by ring.
    rewrite t_odd_unit.
    ring.
  }
  rewrite Fpow_add in Hu by assumption.
  rewrite <- (Fpow_mul PolyDomain.omega 2048 (m * t_cofactor)
    ltac:(lia) Hmc) in Hu.
  rewrite omega_2048 in Hu.
  rewrite fpow_one in Hu by exact Hmc.
  rewrite fmul_one_r in Hu.
  rewrite fpow_canonical in Hu.
  exact Hu.
Qed.

(** ** Cancelling small [delta]-powers *)

Lemma delta_pow_extend (a b : Z)
    (Ha : 0 <= a) (Hb : 0 <= b <= 14)
    (Heq : Fpow (p := Primes.pallas_p) delta (a + b) =
           Fpow (p := Primes.pallas_p) delta a) :
  b = 0.
Proof.
  rewrite Fpow_add in Heq by lia.
  assert (Hzero : BinOp.mul (p := Primes.pallas_p)
    (Fpow (p := Primes.pallas_p) delta a)
    (Fpow (p := Primes.pallas_p) delta b - 1) = 0).
  { unfold BinOp.mul in *.
    rewrite Z.mul_sub_distr_l.
    rewrite Zminus_mod.
    rewrite Heq.
    rewrite Z.mul_1_r.
    rewrite fpow_canonical.
    rewrite Z.sub_diag.
    apply Zmod_0_l. }
  destruct (proj1 (mul_zero_implies_zero _ _) Hzero) as [Hz | Hz].
  - exfalso.
    assert (Hdnz : UnOp.from (p := Primes.pallas_p) delta <> 0).
    { intros Hd0.
      apply delta_nonzero.
      unfold UnOp.from in Hd0.
      rewrite delta_canonical in Hd0.
      exact Hd0. }
    apply (Fpow_nonzero (p := Primes.pallas_p) delta a Ha Hdnz).
    unfold UnOp.from in Hz.
    rewrite fpow_canonical in Hz.
    exact Hz.
  - assert (Hb1 : Fpow (p := Primes.pallas_p) delta b = 1).
    { pose proof
        (proj1 (sub_zero_equiv (p := Primes.pallas_p)
          (Fpow (p := Primes.pallas_p) delta b) 1) Hz) as Hz1.
      unfold UnOp.from in Hz1.
      rewrite fpow_canonical in Hz1.
      rewrite Z.mod_1_l in Hz1 by exact PolyDomain.pallas_p_big.
      exact Hz1. }
    destruct (Z.eq_dec b 0) as [-> | Hbne]; [reflexivity |].
    exfalso.
    exact (delta_small_pow_neq b ltac:(lia) Hb1).
Qed.

(** ** The Orchard domain bookkeeping *)

Lemma orchard_bf : OrchardCompiled.orchard_domain.(Domain.blinding_factors) = 5.
Proof.
  vm_cast_no_check (@eq_refl Z 5).
Qed.

Lemma orchard_usable_rows :
  Domain.usable_rows OrchardCompiled.orchard_domain = 2042.
Proof.
  unfold Domain.usable_rows.
  rewrite OrchardCompiled.orchard_domain_n, orchard_bf.
  reflexivity.
Qed.

Lemma orchard_un : PermutationPoly.un OrchardCompiled.orchard_domain = 2042%nat.
Proof.
  unfold PermutationPoly.un.
  rewrite orchard_usable_rows.
  reflexivity.
Qed.

Lemma orchard_nn : PermutationPoly.nn OrchardCompiled.orchard_domain = 2048%nat.
Proof.
  unfold PermutationPoly.nn.
  rewrite OrchardCompiled.orchard_domain_n.
  reflexivity.
Qed.

Lemma orchard_k_nonneg : 0 <= OrchardCompiled.orchard_domain.(Domain.k).
Proof.
  unfold OrchardCompiled.orchard_domain.
  cbn [Domain.k].
  lia.
Qed.

Lemma orchard_ur_nonneg :
  0 <= Domain.usable_rows OrchardCompiled.orchard_domain.
Proof.
  rewrite orchard_usable_rows.
  lia.
Qed.

Lemma orchard_n_pow :
  Domain.n OrchardCompiled.orchard_domain = Z.of_nat (2 ^ PolyDomain.k).
Proof.
  rewrite OrchardCompiled.orchard_domain_n.
  reflexivity.
Qed.

Lemma orchard_k_ge : (1 <= PolyDomain.k)%nat.
Proof.
  unfold PolyDomain.k.
  lia.
Qed.

(** ** The permutation chunking of the deployed verifier

    [chunk_len = cs.degree() - 2] ([plonk/permutation/verifier.rs]); the
    modeled system degree of the derived Orchard system is [9]. *)

Definition orchard_configured_degree : nat :=
  system_degree_with_minimum orchard_indexed_system
    OrchardConfigure.minimum_degree.

Definition orchard_chunk_len : nat := (orchard_configured_degree - 2)%nat.

Lemma orchard_degree : system_degree orchard_indexed_system = 9%nat.
Proof.
  vm_cast_no_check (@eq_refl nat 9%nat).
Qed.

Lemma orchard_configured_degree_eq : orchard_configured_degree = 9%nat.
Proof.
  unfold orchard_configured_degree.
  rewrite OrchardConfigure.minimum_degree_eq.
  fold (system_degree orchard_indexed_system).
  exact orchard_degree.
Qed.

Lemma orchard_chunk_pos : (0 < orchard_chunk_len)%nat.
Proof.
  unfold orchard_chunk_len.
  rewrite orchard_configured_degree_eq.
  lia.
Qed.

Lemma orchard_all_cells_length :
  Z.of_nat
    (List.length
      (PermutationPoly.all_cells OrchardCompiled.orchard_domain 15
        orchard_chunk_len)) = 30630.
Proof.
  vm_cast_no_check (@eq_refl Z 30630).
Qed.

Lemma orchard_big :
  2 * Z.of_nat
    (List.length
      (PermutationPoly.all_cells OrchardCompiled.orchard_domain 15
        orchard_chunk_len)) + 1 <= Primes.pallas_p.
Proof.
  rewrite orchard_all_cells_length.
  apply Z.leb_le.
  vm_compute.
  reflexivity.
Qed.

(** ** The coset label assignment and its injectivity *)

Definition coset_lbl (c : Sigma.cell) : Z :=
  BinOp.mul (p := Primes.pallas_p)
    (Fpow (p := Primes.pallas_p) delta (Z.of_nat (fst c)))
    (Fpow (p := Primes.pallas_p) PolyDomain.omega (Z.of_nat (snd c))).

Lemma coset_lbl_inj (c d : Sigma.cell) :
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c ->
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 d ->
  coset_lbl c mod Primes.pallas_p = coset_lbl d mod Primes.pallas_p ->
  c = d.
Proof.
  destruct c as [i j], d as [i' j'].
  intros [Hi Hj] [Hi' Hj'] Heq.
  cbn [fst snd] in Hi, Hj, Hi', Hj'.
  rewrite orchard_nn in Hj, Hj'.
  unfold coset_lbl in Heq.
  cbn [fst snd] in Heq.
  rewrite !(PermutationPoly.fmul_canonical (p := Primes.pallas_p)) in Heq.
  assert (HiZ : 0 <= Z.of_nat i <= 14) by (clear -Hi; lia).
  assert (HiZ' : 0 <= Z.of_nat i' <= 14) by (clear -Hi'; lia).
  assert (HjZ : 0 <= Z.of_nat j <= 2047) by (clear -Hj; lia).
  assert (HjZ' : 0 <= Z.of_nat j' <= 2047) by (clear -Hj'; lia).
  pose proof t_odd_nonneg as Ht.
  assert (H0_15 : 0 <= 15) by (apply Z.leb_le; reflexivity).
  assert (HA_nonneg : 0 <= Z.of_nat i + (15 - Z.of_nat i'))
    by (clear -HiZ HiZ'; lia).
  set (M := Z.of_nat j' + (2048 - Z.of_nat j)).
  assert (HM_range : 1 <= M <= 4095)
    by (unfold M; clear -HjZ HjZ'; lia).
  assert (HM_nonneg : 0 <= M) by (clear -HM_range; lia).
  (* The cross-multiplied form: delta^(i + 15 - i') = delta^15 * omega^M. *)
  assert (HE1 :
    Fpow (p := Primes.pallas_p) delta (Z.of_nat i + (15 - Z.of_nat i')) =
    BinOp.mul (p := Primes.pallas_p)
      (Fpow (p := Primes.pallas_p) delta 15)
      (Fpow (p := Primes.pallas_p) PolyDomain.omega M)).
  { transitivity
      (BinOp.mul (p := Primes.pallas_p)
        (BinOp.mul (p := Primes.pallas_p)
          (Fpow (p := Primes.pallas_p) delta (Z.of_nat i))
          (Fpow (p := Primes.pallas_p) PolyDomain.omega (Z.of_nat j)))
        (BinOp.mul (p := Primes.pallas_p)
          (Fpow (p := Primes.pallas_p) delta (15 - Z.of_nat i'))
          (Fpow (p := Primes.pallas_p) PolyDomain.omega
            (2048 - Z.of_nat j)))).
    - rewrite fmul_swap.
      rewrite <- !Fpow_add by lia.
      replace (Z.of_nat j + (2048 - Z.of_nat j)) with 2048 by ring.
      rewrite omega_2048.
      rewrite fmul_one_r.
      symmetry.
      exact (fpow_canonical _ _).
    - rewrite Heq.
      rewrite fmul_swap.
      rewrite <- !Fpow_add by lia.
      replace (Z.of_nat i' + (15 - Z.of_nat i')) with 15 by ring.
      unfold M.
      reflexivity. }
  (* Raising to t kills the delta factors and forces omega^(M t) = 1. *)
  assert (HMt :
    Fpow (p := Primes.pallas_p) PolyDomain.omega (M * t_odd) = 1).
  { pose proof
      (f_equal (fun x => Fpow (p := Primes.pallas_p) x t_odd) HE1) as Hf.
    cbv beta in Hf.
    rewrite (fpow_pow_swap delta (Z.of_nat i + (15 - Z.of_nat i')) t_odd
      HA_nonneg Ht) in Hf.
    rewrite delta_order_t in Hf.
    rewrite fpow_one in Hf by exact HA_nonneg.
    rewrite Fpow_mul_base in Hf by exact Ht.
    rewrite (fpow_pow_swap delta 15 t_odd H0_15 Ht) in Hf.
    rewrite delta_order_t in Hf.
    rewrite fpow_one in Hf by exact H0_15.
    rewrite (Fpow_mul PolyDomain.omega M t_odd HM_nonneg Ht) in Hf.
    rewrite fmul_one_l in Hf.
    symmetry in Hf.
    rewrite fpow_canonical in Hf.
    exact Hf. }
  pose proof (omega_pow_kill_t M HM_nonneg HMt) as HM1.
  rewrite (omega_pow_reduce M HM_nonneg) in HM1.
  assert (HM0 : M mod 2048 = 0).
  { assert (Hzero : Fpow (p := Primes.pallas_p) PolyDomain.omega 0 = 1).
    { rewrite Fpow_0.
      unfold UnOp.from.
      apply Z.mod_1_l.
      exact PolyDomain.pallas_p_big. }
    apply (Poly.w_pow_inj (p := Primes.pallas_p) PolyDomain.omega
      PolyDomain.k orchard_k_ge PolyDomain.pallas_p_gt2
      PolyDomain.omega_order_full PolyDomain.omega_order_half
      (M mod 2048) 0).
    - change (2 ^ Z.of_nat PolyDomain.k) with 2048.
      apply Z.mod_pos_bound.
      apply Z.ltb_lt.
      reflexivity.
    - change (2 ^ Z.of_nat PolyDomain.k) with 2048.
      split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity.
    - rewrite Hzero.
      exact HM1. }
  assert (HMeq : M = 2048) by (clear -HM0 HM_range; lia).
  assert (Hjj : j = j').
  { unfold M in HMeq.
    clear -HMeq.
    lia. }
  (* Back-substitution pins the delta exponent to 15. *)
  assert (HE2 :
    Fpow (p := Primes.pallas_p) delta (Z.of_nat i + (15 - Z.of_nat i')) =
    Fpow (p := Primes.pallas_p) delta 15).
  { rewrite HE1.
    rewrite HMeq.
    rewrite omega_2048.
    rewrite fmul_one_r.
    exact (fpow_canonical _ _). }
  assert (Hii : i = i').
  { destruct (Z_le_gt_dec 15 (Z.of_nat i + (15 - Z.of_nat i')))
      as [Hge | Hlt].
    - assert (Hbr : 0 <= Z.of_nat i + (15 - Z.of_nat i') - 15 <= 14)
        by (clear -HiZ HiZ' Hge; lia).
      assert (Hb0 : Z.of_nat i + (15 - Z.of_nat i') - 15 = 0).
      { apply (delta_pow_extend 15
          (Z.of_nat i + (15 - Z.of_nat i') - 15) H0_15 Hbr).
        replace (15 + (Z.of_nat i + (15 - Z.of_nat i') - 15)) with
          (Z.of_nat i + (15 - Z.of_nat i')) by ring.
        exact HE2. }
      clear -Hb0.
      lia.
    - assert (Hbr : 0 <= 15 - (Z.of_nat i + (15 - Z.of_nat i')) <= 14)
        by (clear -HiZ HiZ' Hlt; lia).
      assert (Hb0 : 15 - (Z.of_nat i + (15 - Z.of_nat i')) = 0).
      { apply (delta_pow_extend (Z.of_nat i + (15 - Z.of_nat i'))
          (15 - (Z.of_nat i + (15 - Z.of_nat i'))) HA_nonneg Hbr).
        replace (Z.of_nat i + (15 - Z.of_nat i') +
          (15 - (Z.of_nat i + (15 - Z.of_nat i')))) with 15 by ring.
        symmetry.
        exact HE2. }
      clear -Hb0.
      lia. }
  rewrite Hii, Hjj.
  reflexivity.
Qed.

(** ** The σ side conditions: range and off-usable fixed points *)

Lemma cell_eqb_eq (c d : Sigma.cell) : Sigma.cell_eqb c d = true -> c = d.
Proof.
  destruct c as [a b], d as [a' b'].
  unfold Sigma.cell_eqb.
  cbn [fst snd].
  intros Hb.
  apply Bool.andb_true_iff in Hb.
  destruct Hb as [H1 H2].
  apply Nat.eqb_eq in H1, H2.
  congruence.
Qed.

Lemma orchard_mapping_length :
  List.length (Sigma.mapping OrchardCompiled.orchard_sigma) = 15%nat.
Proof.
  vm_cast_no_check (@eq_refl nat 15%nat).
Qed.

Lemma orchard_mapping_rows :
  List.forallb (fun row_cells => (List.length row_cells =? 2048)%nat)
    (Sigma.mapping OrchardCompiled.orchard_sigma) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_mapping_space :
  List.forallb
    (List.forallb
      (fun c : Sigma.cell => andb (fst c <? 15)%nat (snd c <? 2048)%nat))
    (Sigma.mapping OrchardCompiled.orchard_sigma) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** The [l_last] spare row and the blinding rows are fixed points of σ:
    no copy obligation reaches past the usable prefix. *)
Lemma orchard_perm_boundary :
  List.forallb
    (fun i =>
      List.forallb
        (fun j =>
          Sigma.cell_eqb (Sigma.perm OrchardCompiled.orchard_sigma (i, j))
            (i, j))
        (List.seq 2042 6))
    (List.seq 0 15) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_sigma_range (c : Sigma.cell) :
  PermutationPoly.usable_cell OrchardCompiled.orchard_domain 15 c ->
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15
    (Sigma.perm OrchardCompiled.orchard_sigma c).
Proof.
  intros [Hc1 Hc2].
  destruct c as [i j].
  cbn [fst snd] in Hc1, Hc2.
  rewrite orchard_un in Hc2.
  assert (Hrow_in :
    List.In (List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) [])
      (Sigma.mapping OrchardCompiled.orchard_sigma)).
  { apply List.nth_In.
    rewrite orchard_mapping_length.
    exact Hc1. }
  assert (Hrow_len :
    List.length
      (List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) []) =
    2048%nat).
  { pose proof orchard_mapping_rows as Hb.
    rewrite List.forallb_forall in Hb.
    apply Nat.eqb_eq.
    exact (Hb _ Hrow_in). }
  assert (Hin :
    List.In
      (List.nth j
        (List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) []) (i, j))
      (List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) [])).
  { apply List.nth_In.
    rewrite Hrow_len.
    lia. }
  pose proof orchard_mapping_space as Hs.
  rewrite List.forallb_forall in Hs.
  specialize (Hs _ Hrow_in).
  rewrite List.forallb_forall in Hs.
  specialize (Hs _ Hin).
  apply Bool.andb_true_iff in Hs.
  destruct Hs as [Hs1 Hs2].
  apply Nat.ltb_lt in Hs1, Hs2.
  unfold Sigma.perm, Sigma.get2.
  cbn [fst snd].
  split.
  - exact Hs1.
  - rewrite orchard_nn.
    exact Hs2.
Qed.

Lemma orchard_sigma_fix (c : Sigma.cell) :
  ~ PermutationPoly.usable_cell OrchardCompiled.orchard_domain 15 c ->
  Sigma.perm OrchardCompiled.orchard_sigma c = c.
Proof.
  intros Hnc.
  destruct c as [i j].
  unfold PermutationPoly.usable_cell in Hnc.
  cbn [fst snd] in Hnc.
  rewrite orchard_un in Hnc.
  destruct (Nat.ltb_spec i 15) as [Hi | Hi].
  - destruct (Nat.ltb_spec j 2042) as [Hj | Hj].
    + exfalso.
      exact (Hnc (conj Hi Hj)).
    + destruct (Nat.ltb_spec j 2048) as [Hj2 | Hj2].
      * (* Boundary rows 2042..2047: the certificate. *)
        pose proof orchard_perm_boundary as Hb.
        rewrite List.forallb_forall in Hb.
        specialize (Hb i ltac:(apply List.in_seq; lia)).
        rewrite List.forallb_forall in Hb.
        specialize (Hb j ltac:(apply List.in_seq; lia)).
        exact (cell_eqb_eq _ _ Hb).
      * (* Rows past the matrix width read the default. *)
        assert (Hrow_len :
          List.length
            (List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) []) =
          2048%nat).
        { pose proof orchard_mapping_rows as Hbr.
          rewrite List.forallb_forall in Hbr.
          apply Nat.eqb_eq.
          apply Hbr.
          apply List.nth_In.
          rewrite orchard_mapping_length.
          exact Hi. }
        unfold Sigma.perm, Sigma.get2.
        cbn [fst snd].
        apply List.nth_overflow.
        rewrite Hrow_len.
        lia.
  - (* Columns past the matrix height read the default. *)
    unfold Sigma.perm, Sigma.get2.
    cbn [fst snd].
    assert (Hrow :
      List.nth i (Sigma.mapping OrchardCompiled.orchard_sigma) [] = []).
    { apply List.nth_overflow.
      rewrite orchard_mapping_length.
      lia. }
    rewrite Hrow.
    apply List.nth_overflow.
    cbn.
    lia.
Qed.

(** ** The gate and lookup side-condition certificates *)

Lemma orchard_gates_count :
  Z.of_nat
    (List.length (OrchardCompiledCheck.compiled.(CompiledSystem.gates))) =
  193.
Proof.
  vm_cast_no_check (@eq_refl Z 193).
Qed.

Lemma orchard_gates_bound :
  Z.of_nat
    (List.length (OrchardCompiledCheck.compiled.(CompiledSystem.gates))) <=
  Primes.pallas_p.
Proof.
  rewrite orchard_gates_count.
  apply Z.leb_le.
  vm_compute.
  reflexivity.
Qed.

Lemma orchard_table_rows_eq : orchard_table_rows = 1024.
Proof.
  vm_cast_no_check (@eq_refl Z 1024).
Qed.

Lemma orchard_tr_pos : 0 < orchard_table_rows.
Proof.
  rewrite orchard_table_rows_eq.
  lia.
Qed.

Lemma orchard_tr_le :
  orchard_table_rows <= Domain.usable_rows OrchardCompiled.orchard_domain.
Proof.
  rewrite orchard_table_rows_eq, orchard_usable_rows.
  lia.
Qed.

Lemma orchard_hp_pts :
  Z.of_nat
    (2 * Z.to_nat (Domain.usable_rows OrchardCompiled.orchard_domain) + 2) <=
  Primes.pallas_p.
Proof.
  rewrite orchard_usable_rows.
  apply Z.leb_le.
  vm_compute.
  reflexivity.
Qed.

Lemma orchard_theta_bounds_b :
  List.forallb
    (fun arg : LookupArgument.t Configure.indexed_columns =>
      Z.of_nat
        (Z.to_nat (Domain.usable_rows OrchardCompiled.orchard_domain) *
         List.length arg.(LookupArgument.pairs) + 1) <=? Primes.pallas_p)
    (OrchardCompiledCheck.compiled.(CompiledSystem.lookups)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_theta_bounds :
  List.Forall
    (fun arg : LookupArgument.t Configure.indexed_columns =>
      Z.of_nat
        (Z.to_nat (Domain.usable_rows OrchardCompiled.orchard_domain) *
         List.length arg.(LookupArgument.pairs) + 1) <= Primes.pallas_p)
    (OrchardCompiledCheck.compiled.(CompiledSystem.lookups)).
Proof.
  pose proof orchard_theta_bounds_b as Hb.
  rewrite List.forallb_forall in Hb.
  apply List.Forall_forall.
  intros arg Hin.
  apply Z.leb_le.
  exact (Hb _ Hin).
Qed.

(** Every fixed-plane event value is a canonical residue. *)
Lemma orchard_fixed_values_ok :
  PlonkishAlgebraic.event_fixed_values_ok_b
    (fun value => andb (0 <=? value) (value <? Primes.pallas_p))
    orchard_events = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** Every table column's padding fill covers the usable band
    [[table_rows, usable_rows)] and its value is pinned at row [0]. *)
Lemma orchard_tables_fill_row0 :
  PlonkishAlgebraic.tables_fill_row0_b orchard_events orchard_table_rows
    (Domain.usable_rows OrchardCompiled.orchard_domain)
    (OrchardCompiledCheck.compiled.(CompiledSystem.lookups)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** No compiled lookup table column is a combination column. *)
Lemma orchard_tables_avoid :
  PlonkishAlgebraic.lookup_tables_avoid_b
    (OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns))
    (OrchardCompiledCheck.compiled.(CompiledSystem.lookups)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** The value-exactness of the lookup selector replacements. *)
Lemma orchard_lookup_exact :
  PlonkishLookup.lookup_replacements_exact_b (p := Primes.pallas_p)
    (PlonkishCompile.combination_view OrchardCompiledCheck.compiled)
    (PlonkishCompile.info_activations OrchardCompiledCheck.orchard_infos)
    (Z.to_nat (Domain.n OrchardCompiled.orchard_domain))
    (OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments))
    orchard_indexed_system = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** No lookup input queries a combination column and no table column is
    one. *)
Lemma orchard_lookup_avoid :
  PlonkishLookup.lookup_columns_avoid_b
    (OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns))
    orchard_indexed_system = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_selector_rows_within :
  PlonkishMock.selector_rows_within_b
    (Domain.usable_rows OrchardCompiled.orchard_domain) orchard_events = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_lookup_defaults :
  PlonkishMock.lookup_defaults_of_events_b (p := Primes.pallas_p)
    orchard_events orchard_indexed_system orchard_table_rows = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** The two combination-plane installations coincide. *)
Lemma with_combinations_planes_eq
    (compiled : CompiledSystem.t) (grid : RawGrid.t) :
  OrchardCompiled.with_combinations compiled grid =
  PlonkishLookup.with_combination_planes compiled grid.
Proof.
  reflexivity.
Qed.

(** ** Algebraic acceptance of the derived Orchard system *)

(** The permutation cell values of a witness grid over the configure-derived
    permutation columns. *)
Definition orchard_perm_values (grid : RawGrid.t) : Sigma.cell -> Z :=
  OrchardCompiled.permutation_cell_value
    OrchardConfigure.permutation_columns grid.

(** The all-challenge identity package over the compiled derived system:
    the vanishing quotient for the 193 compiled gate polynomials (through
    polynomials [Es] agreeing with the grid on [H]), the four permutation
    product rules against the [delta^i omega^j] coset labels and the σ of
    the Orchard copy obligations, and the five lookup rules for the three
    compiled lookup arguments — every challenge universally quantified. *)
Definition orchard_algebraic_accepts (grid : RawGrid.t) (Es : list Poly.t)
    : Prop :=
  PlonkishAlgebraic.algebraic_accepts (p := Primes.pallas_p)
    OrchardCompiled.orchard_domain PolyDomain.omega PolyDomain.k
    OrchardCompiledCheck.compiled grid 15 orchard_chunk_len
    (orchard_perm_values grid) coset_lbl OrchardCompiled.orchard_sigma Es.

(** The canonicity condition on the witness planes: the values on the
    permutation cell space are canonical residues (the committed column
    values of a real prover are field elements). *)
Definition orchard_perm_values_canonical (grid : RawGrid.t) : Prop :=
  forall c : Sigma.cell,
    PermutationPoly.usable_cell OrchardCompiled.orchard_domain 15 c ->
    0 <= orchard_perm_values grid c < Primes.pallas_p.

(** ** The headline soundness chain *)

(** Algebraic acceptance of a replayed grid yields the compiled
    satisfaction triple of the R2 assembly. *)
Theorem orchard_algebraic_sound
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hcanon : orchard_perm_values_canonical grid)
    (Haccepts : orchard_algebraic_accepts grid Es) :
  OrchardCompiled.orchard_compiled_accepts grid.
Proof.
  destruct (PlonkishAlgebraic.algebraic_sound (p := Primes.pallas_p)
    OrchardCompiled.orchard_domain PolyDomain.omega PolyDomain.k
    orchard_k_ge PolyDomain.pallas_p_gt2 PolyDomain.omega_order_full
    PolyDomain.omega_order_half orchard_n_pow
    orchard_indexed_system OrchardCompiledCheck.orchard_infos
    OrchardConfigure.base_fixed_columns
    OrchardConfigure.permutation_columns OrchardConfigure.constants
    OrchardCompiledCheck.compiled orchard_events advice instance_ grid
    orchard_table_rows 15 orchard_chunk_len (orchard_perm_values grid)
    coset_lbl OrchardCompiled.orchard_sigma Es
    Hreplay OrchardCompiled.orchard_compiled_lookups_eq
    OrchardCompiled.orchard_compiled_selector_assignments_eq
    orchard_gates_bound orchard_k_nonneg
    OrchardCompiled.orchard_blinding_nonneg
    orchard_ur_nonneg orchard_chunk_pos orchard_big coset_lbl_inj
    orchard_sigma_range orchard_sigma_fix Hcanon orchard_tr_pos
    orchard_tr_le orchard_hp_pts orchard_theta_bounds
    orchard_fixed_values_ok orchard_tables_fill_row0 orchard_tables_avoid
    (OrchardCompiled.orchard_selector_plane advice instance_ grid Hreplay)
    orchard_lookup_exact orchard_lookup_avoid orchard_selector_rows_within
    orchard_lookup_defaults Haccepts)
    as (Hgates & Hlookups & Hsigma).
  refine (conj _ (conj Hlookups Hsigma)).
  unfold OrchardCompiled.orchard_compiled_grid.
  rewrite with_combinations_planes_eq.
  exact Hgates.
Qed.

(** Algebraic acceptance implies acceptance by the ideal operational
    checker. *)
Theorem orchard_algebraic_mock_accepts
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hcanon : orchard_perm_values_canonical grid)
    (Haccepts : orchard_algebraic_accepts grid Es) :
  mock_prover_accepts orchard_indexed_system orchard_events grid
    orchard_table_rows.
Proof.
  exact (OrchardCompiled.orchard_compiled_sound advice instance_ grid Hreplay
    (orchard_algebraic_sound advice instance_ grid Es Hreplay Hcanon
      Haccepts)).
Qed.

(** Algebraic acceptance yields the relational [circuit_holds] of the
    realized assignment — the [Holds] hypothesis of the Orchard action
    surface, with the instance plane of the accepted grid read back by
    [realize]. *)
Theorem orchard_algebraic_operational_sound
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hcanon : orchard_perm_values_canonical grid)
    (Haccepts : orchard_algebraic_accepts grid Es) :
  circuit_holds (realize Index.indices region_start_of grid)
    Garden.Orchard.circuit.synthesize
    orchard_system.
Proof.
  exact (OrchardCompiled.orchard_compiled_operational_sound advice instance_
    grid Hreplay
    (orchard_algebraic_sound advice instance_ grid Es Hreplay Hcanon
      Haccepts)).
Qed.

(** The chain end: algebraic acceptance of the derived system, together
    with the four witness-honesty side conditions, gives the §4.18.4
    Action statement and [ValidActionInputs] of the realized
    assignment. *)
Corollary orchard_algebraic_action_statement
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hcanon : orchard_perm_values_canonical grid)
    (Haccepts : orchard_algebraic_accepts grid Es)
    (Hmerkle_ok :
      Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle.merkle_witness_ok
        (realize Index.indices region_start_of grid))
    (Hnote_ok :
      Garden.Orchard.circuit_proof.note_commit.cmx.NoteCommitNewCmx
        .note_commit_witness_ok
        (realize Index.indices region_start_of grid))
    (Hold_note_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .old_note_witness_ok
        (realize Index.indices region_start_of grid))
    (Hivk_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .commit_ivk_witness_ok
        (realize Index.indices region_start_of grid)) :
  (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs.read_action_outputs
      (realize Index.indices region_start_of grid) =
    Garden.Orchard.protocol_spec.OrchardProtocolSpec.orchard_action_spec
      Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .orchard_circuit_params
      (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .read_action_inputs
        (realize Index.indices region_start_of grid))) /\
  Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
    .ValidActionInputs
    (realize Index.indices region_start_of grid).
Proof.
  exact (OrchardCompiled.orchard_compiled_action_statement advice instance_
    grid Hreplay
    (orchard_algebraic_sound advice instance_ grid Es Hreplay Hcanon
      Haccepts)
    Hmerkle_ok Hnote_ok Hold_note_ok Hivk_ok).
Qed.

(** ** The σ side conditions of the completeness direction

    Soundness needs σ only to land in the cell space and to fix the
    non-usable cells; completeness additionally needs it to be injective,
    since the honest running products are built from the σ-side factors
    being a permutation of the identity-side ones.  That is not a new
    certificate: [sigma_of_copies_inj] exports it from the assembly
    invariant the σ construction already maintains. *)

Lemma orchard_permutation_columns_length :
  List.length OrchardConfigure.permutation_columns = 15%nat.
Proof.
  vm_cast_no_check (@eq_refl nat 15%nat).
Qed.

(** The assembly's cell domain is the permutation cell space. *)
Lemma orchard_cell_dom_space (c : Sigma.cell) :
  cell_dom OrchardConfigure.permutation_columns
    OrchardCompiled.orchard_n_rows c <->
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c.
Proof.
  unfold cell_dom, PermutationPoly.space_cell, PermutationPoly.nn,
    OrchardCompiled.orchard_n_rows.
  rewrite orchard_permutation_columns_length.
  reflexivity.
Qed.

Lemma orchard_sigma_space_dom (c : Sigma.cell) :
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c ->
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15
    (Sigma.perm OrchardCompiled.orchard_sigma c).
Proof.
  intros Hc.
  exact (proj1 (orchard_cell_dom_space _)
    (sigma_of_copies_dom OrchardConfigure.permutation_columns
      OrchardCompiled.orchard_n_rows OrchardCompiled.orchard_copies
      OrchardCompiled.orchard_sigma OrchardCompiled.orchard_sigma_eq c
      (proj2 (orchard_cell_dom_space c) Hc))).
Qed.

Lemma orchard_sigma_space_inj (c d : Sigma.cell) :
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c ->
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 d ->
  Sigma.perm OrchardCompiled.orchard_sigma c =
  Sigma.perm OrchardCompiled.orchard_sigma d -> c = d.
Proof.
  intros Hc Hd Heq.
  exact (sigma_of_copies_inj OrchardConfigure.permutation_columns
    OrchardCompiled.orchard_n_rows OrchardCompiled.orchard_copies
    OrchardCompiled.orchard_sigma OrchardCompiled.orchard_sigma_eq c d
    (proj2 (orchard_cell_dom_space c) Hc)
    (proj2 (orchard_cell_dom_space d) Hd) Heq).
Qed.

Lemma orchard_space_dec (c : Sigma.cell) :
  PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c \/
  ~ PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 c.
Proof.
  unfold PermutationPoly.space_cell.
  rewrite orchard_nn.
  destruct (Nat.ltb_spec (fst c) 15) as [H1 | H1];
    [destruct (Nat.ltb_spec (snd c) 2048) as [H2 | H2] |].
  - left. exact (conj H1 H2).
  - right. intros [_ Hb]. lia.
  - right. intros [Ha _]. lia.
Qed.

(** σ is injective on the whole cell type: inside the space it is the
    assembly's injection, and outside it is the identity (a non-space cell
    is in particular not usable, so [orchard_sigma_fix] applies), and the
    space is σ-closed, so the two regimes cannot mix. *)
Lemma orchard_sigma_ginj (c d : Sigma.cell) :
  Sigma.perm OrchardCompiled.orchard_sigma c =
  Sigma.perm OrchardCompiled.orchard_sigma d -> c = d.
Proof.
  intros Heq.
  assert (Hout : forall e : Sigma.cell,
    ~ PermutationPoly.space_cell OrchardCompiled.orchard_domain 15 e ->
    Sigma.perm OrchardCompiled.orchard_sigma e = e).
  { intros e He.
    apply orchard_sigma_fix.
    intros [Hu1 Hu2].
    apply He.
    split; [exact Hu1 |].
    rewrite orchard_nn.
    rewrite orchard_un in Hu2.
    lia. }
  destruct (orchard_space_dec c) as [Hc | Hc];
    destruct (orchard_space_dec d) as [Hd | Hd].
  - exact (orchard_sigma_space_inj c d Hc Hd Heq).
  - exfalso.
    apply Hd.
    rewrite <- (Hout d Hd), <- Heq.
    exact (orchard_sigma_space_dom c Hc).
  - exfalso.
    apply Hc.
    rewrite <- (Hout c Hc), Heq.
    exact (orchard_sigma_space_dom d Hd).
  - rewrite <- (Hout c Hc), <- (Hout d Hd).
    exact Heq.
Qed.

(** ** The headline completeness chain *)

(** The regular-challenge reading of the identity package: the permutation
    conjunct is asked only at the [(β, γ)] where no identity-side factor
    vanishes on a usable cell.  This is the predicate
    [orchard_algebraic_sound] already consumes — [algebraic_accepts_regular]
    is weaker than [algebraic_accepts] — so it is the meeting point of the
    two directions at L1. *)
Definition orchard_algebraic_accepts_regular (grid : RawGrid.t)
    (Es : list Poly.t) : Prop :=
  PlonkishAlgebraic.algebraic_accepts_regular (p := Primes.pallas_p)
    OrchardCompiled.orchard_domain PolyDomain.omega PolyDomain.k
    OrchardCompiledCheck.compiled grid 15 orchard_chunk_len
    (orchard_perm_values grid) coset_lbl OrchardCompiled.orchard_sigma Es.

(** The compiled satisfaction triple of the R2 assembly yields algebraic
    acceptance of the derived system: the converse of
    [orchard_algebraic_sound] at the regular challenges. *)
Theorem orchard_algebraic_complete
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hagree :
      PlonkishAlgebraic.gates_agree (p := Primes.pallas_p) PolyDomain.omega
        PolyDomain.k OrchardCompiledCheck.compiled grid Es)
    (Haccepts : OrchardCompiled.orchard_compiled_accepts grid) :
  orchard_algebraic_accepts_regular grid Es.
Proof.
  destruct Haccepts as (Hgates & Hlookups & Hsigma).
  exact (PlonkishAlgebraic.algebraic_complete (p := Primes.pallas_p)
    OrchardCompiled.orchard_domain PolyDomain.omega PolyDomain.k
    orchard_k_ge PolyDomain.pallas_p_gt2 PolyDomain.omega_order_full
    PolyDomain.omega_order_half orchard_n_pow
    orchard_indexed_system OrchardCompiledCheck.orchard_infos
    OrchardConfigure.base_fixed_columns
    OrchardConfigure.permutation_columns OrchardConfigure.constants
    OrchardCompiledCheck.compiled advice instance_ grid
    orchard_table_rows
    15 orchard_chunk_len (orchard_perm_values grid) coset_lbl
    OrchardCompiled.orchard_sigma Es
    OrchardCompiled.orchard_compiled_lookups_eq
    OrchardCompiled.orchard_compiled_selector_assignments_eq
    orchard_gates_bound orchard_k_nonneg
    OrchardCompiled.orchard_blinding_nonneg orchard_ur_nonneg
    orchard_chunk_pos orchard_tr_le
    (OrchardCompiled.orchard_selector_plane advice instance_ grid Hreplay)
    orchard_lookup_exact orchard_lookup_avoid orchard_sigma_fix
    orchard_sigma_ginj Hagree Hgates Hlookups Hsigma).
Qed.

(** The gate-polynomial witness is never the obstacle: the zero
    polynomials agree on [H] with a grid whose compiled gates already
    vanish there, so compiled acceptance gives an *inhabited* algebraic
    acceptance — the L1 non-vacuity certificate. *)
Corollary orchard_algebraic_complete_ex
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Haccepts : OrchardCompiled.orchard_compiled_accepts grid) :
  exists Es : list Poly.t, orchard_algebraic_accepts_regular grid Es.
Proof.
  exists (PlonkishAlgebraic.zero_gate_polys OrchardCompiledCheck.compiled).
  apply (orchard_algebraic_complete advice instance_ grid _ Hreplay);
    [| exact Haccepts].
  exact (PlonkishAlgebraic.gates_agree_zero (p := Primes.pallas_p)
    OrchardCompiled.orchard_domain PolyDomain.omega PolyDomain.k
    OrchardCompiledCheck.compiled grid orchard_n_pow (proj1 Haccepts)).
Qed.

End OrchardCompiledAlgebraic.
