(** * Semantic consequences of the executable Orchard domain certificate *)

From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Bool.Bool Lists.List ZArith Lia.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Prim63.Loop.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaRefinement.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.vk.provenance.Domain.
Require Import Garden.Orchard.vk.provenance.FFT.
Require Import Garden.Orchard.vk.provenance.generated.DomainData.
Require Import Garden.Orchard.vk.provenance.ArrayOfListRefinement.
Require Import Garden.Orchard.vk_msm.

Local Open Scope Z_scope.
Local Open Scope uint63_scope.
Local Open Scope nat_scope.

Module VkDomainPowerRefinement.
  Module F := PallasP.
  Module FR := PallasPRefinement.

  Lemma foldi_from_and_true
      (count start : nat) (test : nat -> bool) (ok : bool) :
    Prim63Loop.foldi_from count start
      (fun index previous => previous && test index) ok = true ->
    ok = true /\
    forall index, start <= index < start + count -> test index = true.
  Proof.
    revert start ok.
    induction count as [|count IH]; intros start ok Hfold.
    - cbn in Hfold. split; [exact Hfold | intros index Hindex; lia].
    - cbn in Hfold.
      destruct (IH (S start) (ok && test start) Hfold)
        as [Hfirst Hrest].
      apply andb_prop in Hfirst as [Hok Htest].
      split; [exact Hok |].
      intros index Hindex.
      destruct (Nat.eq_dec index start) as [-> | Hne]; [exact Htest |].
      apply Hrest. lia.
  Qed.

  Lemma bit_reversal_check_parts :
    VkDomain.bit_reversal_check = true ->
    PrimArray.length@{VkIFFT.array_u} VkDomain.bit_reversed_array = 2048%uint63 /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get@{VkIFFT.array_u} VkDomain.bit_reversed_array (ArrayLinear.index index) =
        VkDomain.reverse_11 (ArrayLinear.index index).
  Proof.
    unfold VkDomain.bit_reversal_check, VkDomain.length_is.
    intros Hcheck.
    apply andb_prop in Hcheck as [Hlength Hfold].
    apply Uint63.eqb_spec in Hlength.
    split; [exact Hlength |].
    change 0%uint63 with (ArrayLinear.index O) in Hfold.
    rewrite Prim63Loop.foldi_u63_index in Hfold
      by exact ArrayLinear.vector_size_fits_word.
    destruct (foldi_from_and_true VkIFFT.size_nat O
      (fun index =>
        PrimInt63.eqb
          (PrimArray.get@{VkIFFT.array_u} VkDomain.bit_reversed_array
            (ArrayLinear.index index))
          (VkDomain.reverse_11 (ArrayLinear.index index))) true Hfold)
      as [_ Hall].
    intros index Hindex.
    apply Uint63.eqb_spec.
    apply Hall. unfold VkIFFT.size_nat in Hindex |- *. lia.
  Qed.

  Lemma bit_reversal_exact (certificate : VkDomain.certificate) :
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get@{VkIFFT.array_u} VkDomain.bit_reversed_array (ArrayLinear.index index) =
        VkDomain.reverse_11 (ArrayLinear.index index).
  Proof.
    apply bit_reversal_check_parts.
    exact certificate.(VkDomain.bit_reversal_checked).
  Qed.

  (** ** Natural-number semantics of the bit-reversal table *)

  Lemma reverse_nat_bound (count input : nat) :
    input < 2 ^ count -> VkDomain.reverse_nat count input < 2 ^ count.
  Proof.
    revert input.
    induction count as [|count IH]; intros input Hinput.
    - cbn [VkDomain.reverse_nat Nat.pow] in *. lia.
    - cbn [VkDomain.reverse_nat Nat.pow].
      assert (Hpow : 0 < 2 ^ count).
      { pose proof (Nat.pow_nonzero 2 count ltac:(lia)). lia. }
      assert (Hmod : input mod 2 ^ count < 2 ^ count)
        by (apply Nat.mod_upper_bound; lia).
      specialize (IH (input mod 2 ^ count) Hmod).
      assert (Hdiv : input / 2 ^ count < 2).
      { apply Nat.div_lt_upper_bound.
        - lia.
        - replace (2 ^ count * 2) with (2 ^ S count) by (cbn; lia).
          exact Hinput. }
      lia.
  Qed.

  Lemma reverse_nat_succ_low (count input : nat) :
    input < 2 ^ count ->
    VkDomain.reverse_nat (S count) input =
      2 * VkDomain.reverse_nat count input.
  Proof.
    intros Hinput.
    cbn [VkDomain.reverse_nat].
    rewrite Nat.mod_small by exact Hinput.
    rewrite Nat.div_small by exact Hinput.
    lia.
  Qed.

  Lemma reverse_nat_succ_high (count input : nat) :
    input < 2 ^ count ->
    VkDomain.reverse_nat (S count) (2 ^ count + input) =
      2 * VkDomain.reverse_nat count input + 1.
  Proof.
    intros Hinput.
    assert (Hnonzero : 2 ^ count <> 0) by (apply Nat.pow_nonzero; lia).
    cbn [VkDomain.reverse_nat].
    rewrite Nat.add_mod by exact Hnonzero.
    rewrite Nat.mod_same by exact Hnonzero.
    cbn [Nat.add].
    rewrite Nat.mod_mod by exact Hnonzero.
    rewrite Nat.mod_small by exact Hinput.
    replace (2 ^ count + input) with (1 * 2 ^ count + input) by lia.
    rewrite Nat.div_add_l by exact Hnonzero.
    rewrite Nat.div_small by exact Hinput.
    lia.
  Qed.

  Lemma reverse_11_natural (index : nat) :
    index < VkIFFT.size_nat ->
    VkDomain.reverse_11 (ArrayLinear.index index) =
      ArrayLinear.index (VkDomain.reverse_nat 11 index).
  Proof.
    intros Hindex.
    unfold VkDomain.reverse_11.
    rewrite ArrayLinear.index_nat_index.
    - reflexivity.
    - apply (ArrayLinear.fits_nat_lt index VkIFFT.size_nat Hindex).
      exact ArrayLinear.vector_size_fits_word.
  Qed.

  Lemma reverse_11_bound (index : nat) :
    index < VkIFFT.size_nat ->
    VkDomain.reverse_nat 11 index < VkIFFT.size_nat.
  Proof.
    unfold VkIFFT.size_nat.
    exact (reverse_nat_bound 11 index).
  Qed.

  Lemma bit_reversal_index (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < VkIFFT.size_nat) :
    PrimArray.get@{VkIFFT.array_u} VkDomain.bit_reversed_array
      (ArrayLinear.index index) =
    ArrayLinear.index (VkDomain.reverse_nat 11 index).
  Proof.
    rewrite (bit_reversal_exact certificate index Hindex).
    apply reverse_11_natural.
    exact Hindex.
  Qed.

  (** ** Recurrence checks expose every generated power *)

  Definition preceding (array : VkIFFT.field_array)
      (start : nat) (initial : F.t) (offset : nat) : F.t :=
    match offset with
    | O => initial
    | S offset =>
        PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index (start + offset))
    end.

  Lemma powers_fold_true (array : VkIFFT.field_array) (ratio : F.t)
      (count start : nat) (ok : bool) (previous : F.t) :
    fst
      (Prim63Loop.foldi_from count start
        (fun index state =>
          let previous := snd state in
          let current :=
            PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index) in
          (fst state && F.equal current (F.mul previous ratio), current))
        (ok, previous)) = true ->
    ok = true /\
    forall offset, offset < count ->
      F.equal
        (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index (start + offset)))
        (F.mul (preceding array start previous offset) ratio) = true.
  Proof.
    revert start ok previous.
    induction count as [|count IH]; intros start ok previous Hfold.
    - cbn in Hfold. split; [exact Hfold | intros offset Hoffset; lia].
    - cbn [Prim63Loop.foldi_from] in Hfold.
      set (current :=
        PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index start)) in *.
      destruct (IH (S start)
        (ok && F.equal current (F.mul previous ratio)) current Hfold)
        as [Hfirst Hrest].
      apply andb_prop in Hfirst as [Hok Hcurrent].
      split; [exact Hok |].
      intros [|offset] Hoffset.
      + cbn [preceding]. rewrite Nat.add_0_r.
        unfold current in Hcurrent. exact Hcurrent.
      + specialize (Hrest offset ltac:(lia)).
        destruct offset as [|offset].
        * cbn [preceding] in Hrest |- *.
          rewrite Nat.add_0_r.
          unfold current in Hrest.
          replace (start + 1) with (S start + 0) by lia.
          exact Hrest.
        * cbn [preceding] in Hrest |- *.
          replace (start + S (S offset)) with
            (S start + S offset) by lia.
          replace (start + S offset) with
            (S start + offset) by lia.
          exact Hrest.
  Qed.

  Lemma powers_check_parts (array : VkIFFT.field_array)
      (length : PrimInt63.int) (count : nat) (ratio : F.t) :
    ArrayLinear.fits_nat (1 + count) ->
    VkDomain.powers_check array length count ratio = true ->
    PrimArray.length@{VkIFFT.array_u} array = length /\
    PrimArray.get@{VkIFFT.array_u} array 0%uint63 = F.one /\
    forall index : nat, 1 <= index <= count ->
      PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index) =
        F.mul
          (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index (index - 1))) ratio.
  Proof.
    unfold VkDomain.powers_check, VkDomain.length_is.
    intros Hfits Hcheck.
    apply andb_prop in Hcheck as [Hprefix Hfold].
    apply andb_prop in Hprefix as [Hlength Hone].
    apply Uint63.eqb_spec in Hlength.
    apply (proj1 (FR.equal_spec _ _)) in Hone.
    split; [exact Hlength |].
    split; [exact Hone |].
    change 1%uint63 with (ArrayLinear.index 1) in Hfold.
    rewrite Prim63Loop.foldi_u63_index in Hfold by exact Hfits.
    destruct (powers_fold_true array ratio count 1 true
      (PrimArray.get@{VkIFFT.array_u} array 0%uint63) Hfold) as [_ Hall].
    intros index Hindex.
    specialize (Hall (index - 1) ltac:(lia)).
    replace (1 + (index - 1)) with index in Hall by lia.
    unfold preceding in Hall.
    destruct index as [|[|index]]; try lia.
    all: cbn [Nat.sub Nat.add] in Hall |- *.
    all: apply (proj1 (FR.equal_spec _ _)).
    all: exact Hall.
  Qed.

  Lemma checked_powers_semantics (array : VkIFFT.field_array)
      (count : nat) (ratio : F.t)
      (Hone : PrimArray.get@{VkIFFT.array_u} array 0%uint63 = F.one)
      (Hstep : forall index : nat, 1 <= index <= count ->
        PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index) =
          F.mul
            (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index (index - 1))) ratio)
      (Hratio : F.canonical ratio) :
    forall index : nat, index <= count ->
      F.canonical
        (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index)) /\
      F.denote (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index)) =
        ((F.denote ratio ^ Z.of_nat index)
          mod PallasPConfig.modulus_Z)%Z.
  Proof.
    intros index Hindex.
    induction index as [|index IH].
    - change (ArrayLinear.index O) with 0%uint63.
      rewrite Hone.
      split; [exact FR.one_canonical |].
      change (1%Z = (1 mod PallasPConfig.modulus_Z)%Z).
      symmetry. apply Z.mod_1_l.
      exact PallasPConfig.modulus_positive.
    - assert (Hindex' : index <= count) by lia.
      specialize (IH Hindex').
      rewrite (Hstep (S index) ltac:(lia)).
      replace (S index - 1)%nat with index by lia.
      split.
      + apply FR.mul_canonical. exact Hratio.
      + transitivity
          (((F.denote
              (PrimArray.get@{VkIFFT.array_u} array (ArrayLinear.index index))) *
            F.denote ratio) mod PallasPConfig.modulus_Z)%Z.
        * apply FR.mul_denote. exact Hratio.
        * rewrite (proj2 IH).
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        rewrite Z.mul_mod_idemp_l.
        f_equal; ring.
    all: try reflexivity; try lia; try ring.
    all: pose proof PallasPConfig.modulus_positive; lia.
  Qed.

  Lemma omega_canonical : F.canonical VkDomain.omega.
  Proof. apply FR.from_Z_canonical. Qed.

  Lemma omega_denote :
    F.denote VkDomain.omega =
      (PolyDomain.omega mod PallasPConfig.modulus_Z)%Z.
  Proof. apply FR.from_Z_denote. Qed.

  Lemma delta_canonical : F.canonical VkDomain.delta.
  Proof. apply FR.from_Z_canonical. Qed.

  Lemma delta_denote :
    F.denote VkDomain.delta =
      (OrchardCompiledAlgebraic.delta mod PallasPConfig.modulus_Z)%Z.
  Proof. apply FR.from_Z_denote. Qed.

  Lemma inverse_omega_canonical : F.canonical VkDomain.inverse_omega.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inverse_omega_denote :
    F.denote VkDomain.inverse_omega = VkMsm.omega_inv.
  Proof. vm_compute. reflexivity. Qed.

  Lemma n_inverse_canonical : F.canonical VkDomainData.n_inverse.
  Proof. vm_compute. reflexivity. Qed.

  Lemma n_inverse_denote :
    F.denote VkDomainData.n_inverse = VkMsm.n_inv.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inverse_roots_checked_parts (certificate : VkDomain.certificate) :
    PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array 0%uint63 = F.one /\
    forall index : nat, 1 <= index <= 1023 ->
      PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
        (ArrayLinear.index index) =
      F.mul
        (PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
          (ArrayLinear.index (index - 1))) VkDomain.inverse_omega.
  Proof.
    pose proof certificate.(VkDomain.inverse_roots_checked) as Hcheck.
    unfold VkDomain.inverse_roots_check in Hcheck.
    apply andb_prop in Hcheck as [_ Hpowers].
    destruct (powers_check_parts VkDomain.inverse_roots_array
      1024%uint63 1023 VkDomain.inverse_omega
      ltac:(vm_compute; reflexivity) Hpowers) as [_ Hparts].
    exact Hparts.
  Qed.

  Lemma inverse_roots_semantics (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 1024) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
        (ArrayLinear.index index)) /\
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
        (ArrayLinear.index index)) =
      ((VkMsm.omega_inv ^ Z.of_nat index) mod Primes.pallas_p)%Z.
  Proof.
    assert (Hbound : index <= 1023) by lia.
    destruct (inverse_roots_checked_parts certificate) as [Hone Hstep].
    pose proof (checked_powers_semantics
      VkDomain.inverse_roots_array 1023 VkDomain.inverse_omega
      Hone Hstep inverse_omega_canonical index Hbound) as H.
    destruct H as [Hcanonical Hdenote].
    split; [exact Hcanonical |].
    change PallasPConfig.modulus_Z with Primes.pallas_p in Hdenote.
    rewrite inverse_omega_denote in Hdenote.
    exact Hdenote.
  Qed.

  Lemma inverse_roots_canonical (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 1024) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
        (ArrayLinear.index index)).
  Proof. exact (proj1 (inverse_roots_semantics certificate index Hindex)). Qed.

  Lemma inverse_roots_denote (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 1024) :
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.inverse_roots_array
        (ArrayLinear.index index)) =
      ((VkMsm.omega_inv ^ Z.of_nat index) mod Primes.pallas_p)%Z.
  Proof. exact (proj2 (inverse_roots_semantics certificate index Hindex)). Qed.

  Lemma omega_powers_checked_parts (certificate : VkDomain.certificate) :
    PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array 0%uint63 = F.one /\
    forall index : nat, 1 <= index <= 2047 ->
      PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
        (ArrayLinear.index index) =
      F.mul
        (PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
          (ArrayLinear.index (index - 1))) VkDomain.omega.
  Proof.
    pose proof certificate.(VkDomain.omega_powers_checked) as Hcheck.
    unfold VkDomain.omega_powers_check in Hcheck.
    destruct (powers_check_parts VkDomain.omega_powers_array
      2048%uint63 2047 VkDomain.omega
      ltac:(vm_compute; reflexivity)
      Hcheck) as [_ Hparts].
    exact Hparts.
  Qed.

  Lemma omega_powers_semantics (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 2048) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
        (ArrayLinear.index index)) /\
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
        (ArrayLinear.index index)) =
      ((PolyDomain.omega ^ Z.of_nat index) mod Primes.pallas_p)%Z.
  Proof.
    assert (Hbound : index <= 2047) by lia.
    destruct (omega_powers_checked_parts certificate) as [Hone Hstep].
    pose proof (checked_powers_semantics VkDomain.omega_powers_array
      2047 VkDomain.omega Hone Hstep omega_canonical index Hbound) as H.
    destruct H as [Hcanonical Hdenote].
    split; [exact Hcanonical |].
    change PallasPConfig.modulus_Z with Primes.pallas_p in Hdenote.
    assert (Hright :
      ((F.denote VkDomain.omega ^ Z.of_nat index)
        mod Primes.pallas_p)%Z =
      ((PolyDomain.omega ^ Z.of_nat index)
        mod Primes.pallas_p)%Z).
    { rewrite omega_denote.
      apply VkMsm.pow_mod_base. apply Nat2Z.is_nonneg. }
    exact (eq_trans Hdenote Hright).
  Qed.

  Lemma omega_powers_canonical (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 2048) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
        (ArrayLinear.index index)).
  Proof. exact (proj1 (omega_powers_semantics certificate index Hindex)). Qed.

  Lemma omega_powers_denote (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 2048) :
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.omega_powers_array
        (ArrayLinear.index index)) =
      ((PolyDomain.omega ^ Z.of_nat index) mod Primes.pallas_p)%Z.
  Proof. exact (proj2 (omega_powers_semantics certificate index Hindex)). Qed.

  Lemma delta_powers_checked_parts (certificate : VkDomain.certificate) :
    PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array 0%uint63 = F.one /\
    forall index : nat, 1 <= index <= 14 ->
      PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
        (ArrayLinear.index index) =
      F.mul
        (PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
          (ArrayLinear.index (index - 1))) VkDomain.delta.
  Proof.
    pose proof certificate.(VkDomain.delta_powers_checked) as Hcheck.
    unfold VkDomain.delta_powers_check in Hcheck.
    destruct (powers_check_parts VkDomain.delta_powers_array
      15%uint63 14 VkDomain.delta
      ltac:(vm_compute; reflexivity)
      Hcheck) as [_ Hparts].
    exact Hparts.
  Qed.

  Lemma delta_powers_semantics (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 15) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
        (ArrayLinear.index index)) /\
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
        (ArrayLinear.index index)) =
      ((OrchardCompiledAlgebraic.delta ^ Z.of_nat index)
        mod Primes.pallas_p)%Z.
  Proof.
    assert (Hbound : index <= 14) by lia.
    destruct (delta_powers_checked_parts certificate) as [Hone Hstep].
    pose proof (checked_powers_semantics VkDomain.delta_powers_array
      14 VkDomain.delta Hone Hstep delta_canonical index Hbound) as H.
    destruct H as [Hcanonical Hdenote].
    split; [exact Hcanonical |].
    change PallasPConfig.modulus_Z with Primes.pallas_p in Hdenote.
    assert (Hright :
      ((F.denote VkDomain.delta ^ Z.of_nat index)
        mod Primes.pallas_p)%Z =
      ((OrchardCompiledAlgebraic.delta ^ Z.of_nat index)
        mod Primes.pallas_p)%Z).
    { rewrite delta_denote.
      apply VkMsm.pow_mod_base. apply Nat2Z.is_nonneg. }
    exact (eq_trans Hdenote Hright).
  Qed.

  Lemma delta_powers_canonical (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 15) :
    F.canonical
      (PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
        (ArrayLinear.index index)).
  Proof. exact (proj1 (delta_powers_semantics certificate index Hindex)). Qed.

  Lemma delta_powers_denote (certificate : VkDomain.certificate)
      (index : nat) (Hindex : index < 15) :
    F.denote
      (PrimArray.get@{VkIFFT.array_u} VkDomain.delta_powers_array
        (ArrayLinear.index index)) =
      ((OrchardCompiledAlgebraic.delta ^ Z.of_nat index)
        mod Primes.pallas_p)%Z.
  Proof. exact (proj2 (delta_powers_semantics certificate index Hindex)). Qed.

End VkDomainPowerRefinement.
