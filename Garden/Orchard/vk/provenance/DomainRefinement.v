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
Require Import Garden.Orchard.vk.provenance.DomainPowerRefinement.

Local Open Scope Z_scope.
Local Open Scope uint63_scope.
Local Open Scope nat_scope.

Module VkDomainRefinement.
  Include VkDomainPowerRefinement.

  (** ** Array/list denotation used by the executable FFT refinement *)

  Definition tabulate (value : nat -> Z) : list Z :=
    List.map value (List.seq O VkIFFT.size_nat).

  Lemma tabulate_length (value : nat -> Z) :
    List.length (tabulate value) = VkIFFT.size_nat.
  Proof.
    unfold tabulate.
    now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma tabulate_nth_error (value : nat -> Z) (index : nat) :
    index < VkIFFT.size_nat ->
    List.nth_error (tabulate value) index = Some (value index).
  Proof.
    intros Hindex.
    unfold tabulate.
    rewrite List.nth_error_map, List.nth_error_seq.
    rewrite (proj2 (Nat.ltb_lt _ _) Hindex).
    cbn. reflexivity.
  Qed.

  Record array_denotes (array : PrimArray.array F.t)
      (values : list Z) : Prop := {
    array_denotes_values_length :
      List.length values = VkIFFT.size_nat;
    array_denotes_length :
      PrimArray.length array = ArrayLinear.vector_size;
    array_denotes_entry : forall (index : nat) (value : Z),
      List.nth_error values index = Some value ->
      F.canonical (PrimArray.get array (ArrayLinear.index index)) /\
      F.denote (PrimArray.get array (ArrayLinear.index index)) = value;
  }.

  Arguments array_denotes_values_length {_ _} _.
  Arguments array_denotes_length {_ _} _.
  Arguments array_denotes_entry {_ _} _ _ _ _.

  Lemma array_denotes_nth (array : PrimArray.array F.t)
      (values : list Z) (Hdenotes : array_denotes array values)
      (index : nat) (Hindex : index < VkIFFT.size_nat) :
    F.canonical (PrimArray.get array (ArrayLinear.index index)) /\
    F.denote (PrimArray.get array (ArrayLinear.index index)) =
      List.nth index values 0%Z.
  Proof.
    apply (array_denotes_entry Hdenotes).
    apply List.nth_error_nth'.
    rewrite (array_denotes_values_length Hdenotes).
    exact Hindex.
  Qed.

  Lemma fill_vector_spec {A : Type} (default : A) (value : nat -> A) :
    PrimArray.length (VkIFFT.fill default value) =
      ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get (VkIFFT.fill default value)
        (ArrayLinear.index index) = value index.
  Proof.
    unfold VkIFFT.fill.
    set (Inv := fun (next : nat) (array : PrimArray.array A) =>
      PrimArray.length array = ArrayLinear.vector_size /\
      forall index : nat, index < next ->
        PrimArray.get array (ArrayLinear.index index) = value index).
    assert (Hinitial : Inv O
      (PrimArray.make ArrayLinear.vector_size default)).
    { split.
      - apply ArrayLinear.make_vector_length.
      - intros index Hindex. lia. }
    assert (Hstep : forall index current,
      O <= index < O + VkIFFT.size_nat ->
      Inv index current ->
      Inv (S index)
        (PrimArray.set current (ArrayLinear.index index) (value index))).
    { intros index current Hindex [Hlength Hprevious].
      assert (Hindex_bound : index < ArrayLinear.vector_size_nat)
        by exact (proj2 Hindex).
      split.
      - rewrite ArrayLinear.length_set. exact Hlength.
      - intros observed Hobserved.
        destruct (Nat.eq_dec observed index) as [-> | Hne].
        + apply ArrayLinear.get_set_same.
          unfold ArrayLinear.in_bounds.
          rewrite Hlength.
          apply ArrayLinear.vector_index_bound. exact Hindex_bound.
        + rewrite ArrayLinear.get_set_other.
          * apply Hprevious. lia.
          * intros Hequal.
            apply Hne.
            apply ArrayLinear.index_inj.
            -- apply (ArrayLinear.fits_nat_lt observed
                  ArrayLinear.vector_size_nat); [lia |].
               exact ArrayLinear.vector_size_fits_word.
            -- apply (ArrayLinear.fits_nat_lt index
                  ArrayLinear.vector_size_nat); [exact Hindex_bound |].
               exact ArrayLinear.vector_size_fits_word.
            -- symmetry. exact Hequal. }
    pose proof (Prim63Loop.foldi_from_invariant Inv
      VkIFFT.size_nat O
      (fun index array =>
        PrimArray.set array (ArrayLinear.index index) (value index))
      (PrimArray.make ArrayLinear.vector_size default)
      Hinitial Hstep) as Hfinal.
    replace (O + VkIFFT.size_nat) with VkIFFT.size_nat in Hfinal by lia.
    exact Hfinal.
  Qed.

  Lemma fill_vector_named_spec {A : Type} (default : A)
      (value : nat -> A) (output : PrimArray.array A) :
    output = VkIFFT.fill default value ->
    PrimArray.length output = ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get output (ArrayLinear.index index) = value index.
  Proof.
    intro Houtput. subst output.
    exact (fill_vector_spec (A := A) default value).
  Qed.

  (** Opaque named wrappers prevent the larger semantic proofs below from
      retaining a conversion between an anonymous [fill_vector_spec] fold
      and the corresponding executable FFT operation. *)
  Lemma load_evaluations_fill_spec (evaluation : nat -> Z)
      (output : PrimArray.array VkIFFT.F.t) :
    output = VkIFFT.load_evaluations evaluation ->
    PrimArray.length output = ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get output (ArrayLinear.index index) =
        VkIFFT.F.from_Z (evaluation index).
  Proof.
    intro Houtput.
    apply (fill_vector_named_spec VkIFFT.F.zero
      (fun index => VkIFFT.F.from_Z (evaluation index))
      output).
    transitivity (VkIFFT.load_evaluations evaluation).
    - exact Houtput.
    - unfold VkIFFT.load_evaluations. reflexivity.
  Qed.

  Lemma load_field_evaluations_fill_spec
      (evaluation : nat -> VkIFFT.F.t)
      (output : PrimArray.array VkIFFT.F.t) :
    output = VkIFFT.load_field_evaluations evaluation ->
    PrimArray.length output = ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get output (ArrayLinear.index index) = evaluation index.
  Proof.
    intro Houtput.
    apply (fill_vector_named_spec VkIFFT.F.zero evaluation output).
    transitivity (VkIFFT.load_field_evaluations evaluation).
    - exact Houtput.
    - unfold VkIFFT.load_field_evaluations. reflexivity.
  Qed.

  Lemma bit_reverse_fill_spec
      (table : PrimArray.array PrimInt63.int)
      (array output : PrimArray.array VkIFFT.F.t) :
    output = VkIFFT.bit_reverse table array ->
    PrimArray.length output = ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get output (ArrayLinear.index index) =
      PrimArray.get array
        (PrimArray.get table (ArrayLinear.index index)).
  Proof.
    intro Houtput.
    apply (fill_vector_named_spec VkIFFT.F.zero
      (fun index =>
        PrimArray.get array
          (PrimArray.get table (ArrayLinear.index index)))
      output).
    transitivity (VkIFFT.bit_reverse table array).
    - exact Houtput.
    - unfold VkIFFT.bit_reverse. reflexivity.
  Qed.

  Lemma scale_fill_spec (n_inverse : VkIFFT.F.t)
      (array output : PrimArray.array VkIFFT.F.t) :
    output = VkIFFT.scale n_inverse array ->
    PrimArray.length output = ArrayLinear.vector_size /\
    forall index : nat, index < VkIFFT.size_nat ->
      PrimArray.get output (ArrayLinear.index index) =
      VkIFFT.F.mul (PrimArray.get array (ArrayLinear.index index)) n_inverse.
  Proof.
    intro Houtput.
    apply (fill_vector_named_spec VkIFFT.F.zero
      (fun index => VkIFFT.F.mul
        (PrimArray.get array (ArrayLinear.index index)) n_inverse)
      output).
    transitivity (VkIFFT.scale n_inverse array).
    - exact Houtput.
    - unfold VkIFFT.scale. reflexivity.
  Qed.

  Definition evaluation_values (evaluation : nat -> Z) : list Z :=
    tabulate (fun index => (evaluation index mod Primes.pallas_p)%Z).

  Definition field_evaluation_values (evaluation : nat -> F.t) : list Z :=
    tabulate (fun index => F.denote (evaluation index)).

  Lemma load_evaluations_sound (evaluation : nat -> Z) :
    array_denotes (VkIFFT.load_evaluations evaluation)
      (evaluation_values evaluation).
  Proof.
    remember (VkIFFT.load_evaluations evaluation) as output eqn:Houtput.
    destruct (load_evaluations_fill_spec evaluation output Houtput)
      as [Hlength Hentry].
    constructor.
    - apply tabulate_length.
    - exact Hlength.
    - intros index value Hvalue.
      assert (Hindex : index < VkIFFT.size_nat).
      { apply (proj1 (List.nth_error_Some
          (evaluation_values evaluation) index)).
        rewrite Hvalue. discriminate. }
      pose proof (tabulate_nth_error
        (fun index => (evaluation index mod Primes.pallas_p)%Z)
        index Hindex) as Hexpected.
      unfold evaluation_values in Hvalue.
      rewrite Hexpected in Hvalue. inversion Hvalue; subst value.
      pose proof (Hentry index Hindex) as Hloaded.
      change
        (PrimArray.get output
          (ArrayLinear.index index) = F.from_Z (evaluation index))
        in Hloaded.
      split.
      - exact (eq_ind_r F.canonical
          (FR.from_Z_canonical (evaluation index)) Hloaded).
      - refine (eq_trans (f_equal F.denote Hloaded) _).
        rewrite FR.from_Z_denote. reflexivity.
  Qed.

  Lemma load_field_evaluations_sound (evaluation : nat -> F.t) :
    (forall index : nat, index < VkIFFT.size_nat ->
      F.canonical (evaluation index)) ->
    array_denotes (VkIFFT.load_field_evaluations evaluation)
      (field_evaluation_values evaluation).
  Proof.
    intros Hcanonical.
    remember (VkIFFT.load_field_evaluations evaluation)
      as output eqn:Houtput.
    destruct (load_field_evaluations_fill_spec evaluation output Houtput)
      as [Hlength Hentry].
    constructor.
    - apply tabulate_length.
    - exact Hlength.
    - intros index value Hvalue.
      assert (Hindex : index < VkIFFT.size_nat).
      { apply (proj1 (List.nth_error_Some
          (field_evaluation_values evaluation) index)).
        rewrite Hvalue. discriminate. }
      pose proof (tabulate_nth_error
        (fun index => F.denote (evaluation index)) index Hindex)
        as Hexpected.
      unfold field_evaluation_values in Hvalue.
      rewrite Hexpected in Hvalue. inversion Hvalue; subst value.
      pose proof (Hentry index Hindex) as Hloaded.
      change
        (PrimArray.get output
          (ArrayLinear.index index) = evaluation index) in Hloaded.
      split.
      - exact (eq_ind_r F.canonical (Hcanonical index Hindex) Hloaded).
      - exact (f_equal F.denote Hloaded).
  Qed.

  Definition bit_reverse_values (values : list Z) : list Z :=
    tabulate (fun index =>
      List.nth (VkDomain.reverse_nat 11 index) values 0%Z).

  Lemma bit_reverse_sound (certificate : VkDomain.certificate)
      (array : PrimArray.array F.t) (values : list Z) :
    array_denotes array values ->
    array_denotes
      (VkIFFT.bit_reverse VkDomainData.bit_reversed_array array)
      (bit_reverse_values values).
  Proof.
    intros Hdenotes.
    remember
      (VkIFFT.bit_reverse VkDomainData.bit_reversed_array array)
      as output eqn:Houtput.
    destruct (bit_reverse_fill_spec
      VkDomainData.bit_reversed_array array output Houtput)
      as [Hlength Hentry].
    constructor.
    - apply tabulate_length.
    - exact Hlength.
    - intros index value Hvalue.
      assert (Hindex : index < VkIFFT.size_nat).
      { apply (proj1 (List.nth_error_Some
          (bit_reverse_values values) index)).
        rewrite Hvalue. discriminate. }
      pose proof (tabulate_nth_error
        (fun index =>
          List.nth (VkDomain.reverse_nat 11 index) values 0%Z)
        index Hindex) as Hexpected.
      unfold bit_reverse_values in Hvalue.
      rewrite Hexpected in Hvalue. inversion Hvalue; subst value.
      pose proof (Hentry index Hindex) as Hloaded.
      change
        (PrimArray.get
          output
          (ArrayLinear.index index) =
        PrimArray.get array
          (PrimArray.get VkDomainData.bit_reversed_array
            (ArrayLinear.index index))) in Hloaded.
      rewrite bit_reversal_index in Hloaded by exact Hindex.
      assert (Hsource :
        F.canonical
          (PrimArray.get array
            (ArrayLinear.index (VkDomain.reverse_nat 11 index))) /\
        F.denote
          (PrimArray.get array
            (ArrayLinear.index (VkDomain.reverse_nat 11 index))) =
          List.nth (VkDomain.reverse_nat 11 index) values 0%Z).
      { apply (array_denotes_entry Hdenotes).
        apply List.nth_error_nth'.
        rewrite (array_denotes_values_length Hdenotes).
        apply reverse_11_bound. exact Hindex. }
      destruct Hsource as [Hcanonical Hdenote].
      split.
      - exact (eq_ind_r F.canonical Hcanonical Hloaded).
      - exact (eq_trans (f_equal F.denote Hloaded) Hdenote).
  Qed.

  (** The nested production loops write one disjoint butterfly pair at a
      time.  These pointwise definitions are shared by the array invariant
      and the later list-level butterfly proof. *)
  Definition stage_left_index (length block offset : nat) : nat :=
    block * length + offset.

  Definition stage_right_index (length half block offset : nat) : nat :=
    stage_left_index length block offset + half.

  Definition stage_twiddle_index (stride offset : nat) : nat :=
    offset * stride.

  Definition stage_left_word (inverse_roots : PrimArray.array F.t)
      (input : PrimArray.array F.t) (length half stride block offset : nat)
      : F.t :=
    let left := PrimArray.get input
      (ArrayLinear.index (stage_left_index length block offset)) in
    let right := F.mul
      (PrimArray.get input
        (ArrayLinear.index
          (stage_right_index length half block offset)))
      (PrimArray.get inverse_roots
        (ArrayLinear.index (stage_twiddle_index stride offset))) in
    F.add left right.

  Definition stage_right_word (inverse_roots : PrimArray.array F.t)
      (input : PrimArray.array F.t) (length half stride block offset : nat)
      : F.t :=
    let left := PrimArray.get input
      (ArrayLinear.index (stage_left_index length block offset)) in
    let right := F.mul
      (PrimArray.get input
        (ArrayLinear.index
          (stage_right_index length half block offset)))
      (PrimArray.get inverse_roots
        (ArrayLinear.index (stage_twiddle_index stride offset))) in
    F.sub left right.

  Definition stage_left_value (root : Z) (values : list Z)
      (length half block offset : nat) : Z :=
    (List.nth (block * length + offset) values 0%Z +
      root ^ Z.of_nat offset *
        List.nth (block * length + offset + half) values 0%Z)
      mod Primes.pallas_p.

  Definition stage_right_value (root : Z) (values : list Z)
      (length half block offset : nat) : Z :=
    (List.nth (block * length + offset) values 0%Z -
      root ^ Z.of_nat offset *
        List.nth (block * length + offset + half) values 0%Z)
      mod Primes.pallas_p.

  Definition inverse_stage_root (stride : nat) : Z :=
    ((VkMsm.omega_inv ^ Z.of_nat stride) mod Primes.pallas_p)%Z.

  Lemma inverse_stage_root_power (stride offset : nat) :
    ((VkMsm.omega_inv ^ Z.of_nat (offset * stride))
      mod Primes.pallas_p)%Z =
    (((inverse_stage_root stride) ^ Z.of_nat offset)
      mod Primes.pallas_p)%Z.
  Proof.
    unfold inverse_stage_root.
    rewrite Nat2Z.inj_mul.
    replace (Z.of_nat offset * Z.of_nat stride)%Z with
      (Z.of_nat stride * Z.of_nat offset)%Z by ring.
    rewrite Z.pow_mul_l.
    symmetry.
    apply VkMsm.pow_mod_base.
    lia.
  Qed.

  Lemma inverse_root_for_stage (certificate : VkDomain.certificate)
      (stride offset : nat) (Hindex : offset * stride < 1024) :
    F.canonical
      (PrimArray.get VkDomainData.inverse_roots_array
        (ArrayLinear.index (stage_twiddle_index stride offset))) /\
    F.denote
      (PrimArray.get VkDomainData.inverse_roots_array
        (ArrayLinear.index (stage_twiddle_index stride offset))) =
      (((inverse_stage_root stride) ^ Z.of_nat offset)
        mod Primes.pallas_p)%Z.
  Proof.
    unfold stage_twiddle_index.
    pose proof (inverse_roots_semantics certificate
      (offset * stride) Hindex) as [Hcanonical Hdenote].
    split; [exact Hcanonical |].
    rewrite Hdenote.
    apply inverse_stage_root_power.
  Qed.

  Lemma stage_left_word_refines (certificate : VkDomain.certificate)
      (input : PrimArray.array F.t) (values : list Z)
      (length half stride block offset : nat)
      (Hdenotes : array_denotes input values)
      (Hleft : stage_left_index length block offset < VkIFFT.size_nat)
      (Hright :
        stage_right_index length half block offset < VkIFFT.size_nat)
      (Htwiddle : offset * stride < 1024) :
    F.canonical
      (stage_left_word VkDomainData.inverse_roots_array input
        length half stride block offset) /\
    F.denote
      (stage_left_word VkDomainData.inverse_roots_array input
        length half stride block offset) =
      stage_left_value (inverse_stage_root stride) values
        length half block offset.
  Proof.
    pose proof (array_denotes_nth input values Hdenotes
      (stage_left_index length block offset) Hleft)
      as [Hleft_canonical Hleft_denote].
    pose proof (array_denotes_nth input values Hdenotes
      (stage_right_index length half block offset) Hright)
      as [Hright_canonical Hright_denote].
    pose proof (inverse_root_for_stage certificate stride offset Htwiddle)
      as [Hroot_canonical Hroot_denote].
    unfold stage_left_word.
    cbn zeta.
    split.
    - apply FR.add_canonical.
      + exact Hleft_canonical.
      + apply FR.mul_canonical. exact Hroot_canonical.
    - rewrite (FR.add_denote _ _ Hleft_canonical
        (FR.mul_canonical _ _ Hroot_canonical)).
      rewrite (FR.mul_denote _ _ Hroot_canonical).
      rewrite Hleft_denote, Hright_denote, Hroot_denote.
      unfold stage_left_value, stage_left_index, stage_right_index.
      rewrite Z.mul_mod_idemp_r by
        (pose proof VkMsm.scalar_p_big; lia).
      rewrite Z.add_mod_idemp_r by
        (pose proof VkMsm.scalar_p_big; lia).
      f_equal. ring.
  Qed.

  Lemma stage_right_word_refines (certificate : VkDomain.certificate)
      (input : PrimArray.array F.t) (values : list Z)
      (length half stride block offset : nat)
      (Hdenotes : array_denotes input values)
      (Hleft : stage_left_index length block offset < VkIFFT.size_nat)
      (Hright :
        stage_right_index length half block offset < VkIFFT.size_nat)
      (Htwiddle : offset * stride < 1024) :
    F.canonical
      (stage_right_word VkDomainData.inverse_roots_array input
        length half stride block offset) /\
    F.denote
      (stage_right_word VkDomainData.inverse_roots_array input
        length half stride block offset) =
      stage_right_value (inverse_stage_root stride) values
        length half block offset.
  Proof.
    pose proof (array_denotes_nth input values Hdenotes
      (stage_left_index length block offset) Hleft)
      as [Hleft_canonical Hleft_denote].
    pose proof (array_denotes_nth input values Hdenotes
      (stage_right_index length half block offset) Hright)
      as [Hright_canonical Hright_denote].
    pose proof (inverse_root_for_stage certificate stride offset Htwiddle)
      as [Hroot_canonical Hroot_denote].
    unfold stage_right_word.
    cbn zeta.
    split.
    - apply FR.sub_canonical.
      + exact Hleft_canonical.
      + apply FR.mul_canonical. exact Hroot_canonical.
    - rewrite (FR.sub_denote _ _ Hleft_canonical
        (FR.mul_canonical _ _ Hroot_canonical)).
      rewrite (FR.mul_denote _ _ Hroot_canonical).
      rewrite Hleft_denote, Hright_denote, Hroot_denote.
      unfold stage_right_value, stage_left_index, stage_right_index.
      rewrite Z.mul_mod_idemp_r by
        (pose proof VkMsm.scalar_p_big; lia).
      rewrite Zminus_mod_idemp_r.
      f_equal. ring.
  Qed.

  Definition stage_block_done (inverse_roots : PrimArray.array F.t)
      (input : PrimArray.array F.t) (length half stride block : nat)
      (output : PrimArray.array F.t) : Prop :=
    forall offset : nat, offset < half ->
      PrimArray.get output
        (ArrayLinear.index (stage_left_index length block offset)) =
          stage_left_word inverse_roots input
            length half stride block offset /\
      PrimArray.get output
        (ArrayLinear.index (stage_right_index length half block offset)) =
          stage_right_word inverse_roots input
            length half stride block offset.

  Lemma bounded_index_neq (left right : nat) :
    left < VkIFFT.size_nat -> right < VkIFFT.size_nat -> left <> right ->
    ArrayLinear.index left <> ArrayLinear.index right.
  Proof.
    intros Hleft Hright Hneq Hequal.
    apply Hneq.
    apply ArrayLinear.index_inj.
    - apply (ArrayLinear.fits_nat_lt left ArrayLinear.vector_size_nat);
        [exact Hleft | exact ArrayLinear.vector_size_fits_word].
    - apply (ArrayLinear.fits_nat_lt right ArrayLinear.vector_size_nat);
        [exact Hright | exact ArrayLinear.vector_size_fits_word].
    - exact Hequal.
  Qed.

  Lemma stage_index_bounds (length half blocks block offset : nat) :
    length = 2 * half ->
    blocks * length = VkIFFT.size_nat ->
    block < blocks -> offset < half ->
    stage_left_index length block offset < VkIFFT.size_nat /\
    stage_right_index length half block offset < VkIFFT.size_nat.
  Proof.
    unfold stage_left_index, stage_right_index.
    intros Hlength Hsize Hblock Hoffset.
    nia.
  Qed.

  Lemma stage_block_preserves
      (inverse_roots : PrimArray.array F.t)
      (input output : PrimArray.array F.t)
      (length half stride blocks block : nat) :
    length = 2 * half -> 0 < half ->
    blocks * length = VkIFFT.size_nat -> block < blocks ->
    PrimArray.length output = ArrayLinear.vector_size ->
    (forall previous, previous < block ->
      stage_block_done inverse_roots input length half stride previous output) ->
    let result := VkIFFT.stage_block inverse_roots input
      length half stride block output in
    PrimArray.length result = ArrayLinear.vector_size /\
    (forall previous, previous < block ->
      stage_block_done inverse_roots input length half stride previous result) /\
    stage_block_done inverse_roots input length half stride block result.
  Proof.
    intros Hlength Hhalf Hsize Hblock Houtput Hprevious.
    cbn zeta.
    set (Inv := fun (next : nat) (current : PrimArray.array F.t) =>
      PrimArray.length current = ArrayLinear.vector_size /\
      (forall previous, previous < block ->
        stage_block_done inverse_roots input
          length half stride previous current) /\
      forall offset, offset < next ->
        PrimArray.get current
          (ArrayLinear.index (stage_left_index length block offset)) =
            stage_left_word inverse_roots input
              length half stride block offset /\
        PrimArray.get current
          (ArrayLinear.index
            (stage_right_index length half block offset)) =
            stage_right_word inverse_roots input
              length half stride block offset).
    assert (Hinitial : Inv O output).
    { repeat split; try assumption.
      intros offset Hoffset. lia. }
    assert (Hstep : forall offset current,
      O <= offset < O + half ->
      Inv offset current ->
      Inv (S offset)
        (VkIFFT.stage_pair_at inverse_roots input
          length half stride block offset current)).
    { intros offset current Hoffset
        [Hcurrent [Hblocks Hoffsets]].
      assert (Hcurrent_bounds := stage_index_bounds
        length half blocks block offset Hlength Hsize Hblock ltac:(lia)).
      destruct Hcurrent_bounds as [Hleft_bound Hright_bound].
      unfold VkIFFT.stage_pair_at.
      cbn zeta.
      repeat split.
      - rewrite !ArrayLinear.length_set. exact Hcurrent.
      - intros previous Hprevious_block previous_offset Hprevious_offset.
        pose proof (Hblocks previous Hprevious_block
          previous_offset Hprevious_offset) as [Hleft Hright].
        pose proof (stage_index_bounds length half blocks previous
          previous_offset Hlength Hsize ltac:(lia) Hprevious_offset)
          as [Hprevious_left_bound Hprevious_right_bound].
        split.
        + rewrite ArrayLinear.get_set_other.
          2: { apply bounded_index_neq; try assumption.
            unfold stage_left_index, stage_right_index. nia. }
          rewrite ArrayLinear.get_set_other.
          2: { apply bounded_index_neq; try assumption.
            unfold stage_left_index. nia. }
          exact Hleft.
        + rewrite ArrayLinear.get_set_other.
          2: { apply bounded_index_neq; try assumption.
            unfold stage_right_index, stage_left_index. nia. }
          rewrite ArrayLinear.get_set_other.
          2: { apply bounded_index_neq; try assumption.
            unfold stage_left_index, stage_right_index. nia. }
          exact Hright.
      - intros observed Hobserved.
        destruct (Nat.eq_dec observed offset) as [-> | Hneq].
        + split.
          * rewrite ArrayLinear.get_set_other.
            2: { apply bounded_index_neq; try assumption.
              unfold stage_left_index, stage_right_index. nia. }
            apply ArrayLinear.get_set_same.
            unfold ArrayLinear.in_bounds.
            rewrite Hcurrent.
            apply ArrayLinear.vector_index_bound. exact Hleft_bound.
          * apply ArrayLinear.get_set_same.
            unfold ArrayLinear.in_bounds.
            rewrite ArrayLinear.length_set, Hcurrent.
            apply ArrayLinear.vector_index_bound. exact Hright_bound.
        + pose proof (Hoffsets observed ltac:(lia)) as [Hleft Hright].
          pose proof (stage_index_bounds length half blocks block
            observed Hlength Hsize Hblock ltac:(lia))
            as [Hprevious_left_bound Hprevious_right_bound].
          split.
          * rewrite ArrayLinear.get_set_other.
            2: { apply bounded_index_neq; try assumption.
              unfold stage_left_index, stage_right_index. nia. }
            rewrite ArrayLinear.get_set_other.
            2: { apply bounded_index_neq; try assumption.
              unfold stage_left_index. nia. }
            exact Hleft.
          * rewrite ArrayLinear.get_set_other.
            2: { apply bounded_index_neq; try assumption.
              unfold stage_right_index, stage_left_index. nia. }
            rewrite ArrayLinear.get_set_other.
            2: { apply bounded_index_neq; try assumption.
              unfold stage_left_index, stage_right_index. nia. }
            exact Hright. }
    pose proof (Prim63Loop.foldi_from_invariant Inv half O
      (fun offset current =>
        VkIFFT.stage_pair_at inverse_roots input
          length half stride block offset current)
      output Hinitial Hstep) as Hfinal.
    replace (O + half) with half in Hfinal by lia.
    destruct Hfinal as [Hresult [Hblocks Hoffsets]].
    repeat split; try assumption.
  Qed.

  Lemma stage_entries
      (inverse_roots : PrimArray.array F.t)
      (input : PrimArray.array F.t) (length half stride blocks : nat) :
    length = 2 * half -> 0 < half ->
    blocks * length = VkIFFT.size_nat ->
    let result :=
      Prim63Loop.foldi_from blocks O
        (VkIFFT.stage_block inverse_roots input length half stride)
        (PrimArray.make ArrayLinear.vector_size F.zero) in
    PrimArray.length result = ArrayLinear.vector_size /\
    forall block, block < blocks ->
      stage_block_done inverse_roots input length half stride block result.
  Proof.
    intros Hlength Hhalf Hsize.
    cbn zeta.
    set (Inv := fun (next : nat) (output : PrimArray.array F.t) =>
      PrimArray.length output = ArrayLinear.vector_size /\
      forall block, block < next ->
        stage_block_done inverse_roots input
          length half stride block output).
    assert (Hinitial : Inv O
      (PrimArray.make ArrayLinear.vector_size F.zero)).
    { split; [apply ArrayLinear.make_vector_length |].
      intros block Hblock. lia. }
    assert (Hstep : forall block output,
      O <= block < O + blocks -> Inv block output ->
      Inv (S block)
        (VkIFFT.stage_block inverse_roots input
          length half stride block output)).
    { intros block output Hblock [Houtput Hdone].
      pose proof (stage_block_preserves inverse_roots input output
        length half stride blocks block Hlength Hhalf Hsize
        ltac:(lia) Houtput Hdone) as H.
      destruct H as [Hresult [Hprevious Hcurrent]].
      split; [exact Hresult |].
      intros observed Hobserved.
      destruct (Nat.eq_dec observed block) as [-> | Hneq].
      - exact Hcurrent.
      - apply Hprevious. lia. }
    pose proof (Prim63Loop.foldi_from_invariant Inv blocks O
      (VkIFFT.stage_block inverse_roots input length half stride)
      (PrimArray.make ArrayLinear.vector_size F.zero)
      Hinitial Hstep) as Hfinal.
    replace (O + blocks) with blocks in Hfinal by lia.
    exact Hfinal.
  Qed.

  (** ** Pure iterative FFT

      [VkMsm.fft] is written recursively, while Halo2 and the executable
      checker use ascending, in-place-sized butterfly passes.  The model
      below isolates that algorithmic difference from primitive-array and
      Montgomery details. *)

  Definition tabulate_n (size : nat) (value : nat -> Z) : list Z :=
    List.map value (List.seq O size).

  Lemma tabulate_n_length (size : nat) (value : nat -> Z) :
    List.length (tabulate_n size value) = size.
  Proof.
    unfold tabulate_n.
    now rewrite List.length_map, List.length_seq.
  Qed.

  Lemma tabulate_n_nth (size : nat) (value : nat -> Z) (index : nat) :
    index < size -> List.nth index (tabulate_n size value) 0%Z = value index.
  Proof.
    intros Hindex.
    apply List.nth_error_nth with (x := value index).
    unfold tabulate_n.
    rewrite List.nth_error_map, List.nth_error_seq.
    rewrite Nat.ltb_lt by exact Hindex.
    cbn. now rewrite Nat.add_0_l.
  Qed.

  Definition bit_reverse_list (count : nat) (values : list Z) : list Z :=
    tabulate_n (2 ^ count)
      (fun index => List.nth (VkDomain.reverse_nat count index) values 0%Z).

  Lemma bit_reverse_list_length (count : nat) (values : list Z) :
    List.length (bit_reverse_list count values) = 2 ^ count.
  Proof. apply tabulate_n_length. Qed.

  Lemma evens_two (a b : Z) (values : list Z) :
    VkMsm.evens (a :: b :: values) = a :: VkMsm.evens values.
  Proof.
    unfold VkMsm.evens.
    cbn [VkMsm.deinter].
    now destruct (VkMsm.deinter values).
  Qed.

  Lemma odds_two (a b : Z) (values : list Z) :
    VkMsm.odds (a :: b :: values) = b :: VkMsm.odds values.
  Proof.
    unfold VkMsm.odds.
    cbn [VkMsm.deinter].
    now destruct (VkMsm.deinter values).
  Qed.

  Lemma evens_odds_nth (values : list Z) (index : nat) :
    List.nth index (VkMsm.evens values) 0%Z =
      List.nth (2 * index) values 0%Z /\
    List.nth index (VkMsm.odds values) 0%Z =
      List.nth (2 * index + 1) values 0%Z.
  Proof.
    revert values.
    induction index as [|index IH]; intros [|a [|b values]].
    all: try reflexivity.
    - cbn [VkMsm.evens VkMsm.odds VkMsm.deinter]. reflexivity.
    - rewrite evens_two, odds_two. cbn [List.nth].
      replace (2 * S index) with (S (S (2 * index))) by lia.
      replace (2 * S index + 1) with (S (S (2 * index + 1))) by lia.
      exact (IH values).
  Qed.

  Lemma bit_reverse_list_succ (count : nat) (values : list Z) :
    bit_reverse_list (S count) values =
      bit_reverse_list count (VkMsm.evens values) ++
      bit_reverse_list count (VkMsm.odds values).
  Proof.
    apply List.nth_ext with (d := 0%Z) (d' := 0%Z).
    - rewrite bit_reverse_list_length, List.length_app,
        !bit_reverse_list_length.
      cbn [Nat.pow]. lia.
    - intros index Hindex.
      rewrite bit_reverse_list_length in Hindex.
      cbn [Nat.pow] in Hindex.
      destruct (Nat.lt_ge_cases index (2 ^ count)) as [Hlow | Hhigh].
      + rewrite (tabulate_n_nth (2 ^ S count)
          (fun index =>
            List.nth (VkDomain.reverse_nat (S count) index) values 0%Z)
          index) by (cbn [Nat.pow]; lia).
        rewrite List.app_nth1.
        2: { rewrite bit_reverse_list_length. exact Hlow. }
        rewrite (tabulate_n_nth (2 ^ count)
          (fun index => List.nth (VkDomain.reverse_nat count index)
            (VkMsm.evens values) 0%Z) index Hlow).
        rewrite reverse_nat_succ_low by exact Hlow.
        symmetry. apply (proj1 (evens_odds_nth values
          (VkDomain.reverse_nat count index))).
      + set (offset := index - 2 ^ count).
        assert (Hoffset : offset < 2 ^ count) by
          (unfold offset; lia).
        assert (Hindex_offset : index = 2 ^ count + offset) by
          (unfold offset; lia).
        rewrite (tabulate_n_nth (2 ^ S count)
          (fun index =>
            List.nth (VkDomain.reverse_nat (S count) index) values 0%Z)
          index) by (cbn [Nat.pow]; lia).
        rewrite List.app_nth2.
        2: { rewrite bit_reverse_list_length. exact Hhigh. }
        rewrite bit_reverse_list_length.
        fold offset.
        rewrite (tabulate_n_nth (2 ^ count)
          (fun index => List.nth (VkDomain.reverse_nat count index)
            (VkMsm.odds values) 0%Z) offset Hoffset).
        rewrite Hindex_offset, reverse_nat_succ_high by exact Hoffset.
        symmetry. apply (proj2 (evens_odds_nth values
          (VkDomain.reverse_nat count offset))).
  Qed.

  Definition butterfly_block (half : nat) (root : Z)
      (values : list Z) : list Z :=
    let left := List.firstn half values in
    let right := List.firstn half (List.skipn half values) in
    let outputs := VkMsm.bfly root 1 left right in
    fst outputs ++ snd outputs.

  Fixpoint stage_blocks (count half : nat) (root : Z)
      (values : list Z) : list Z :=
    match count with
    | O => []
    | S count =>
        butterfly_block half root values ++
        stage_blocks count half root (List.skipn (2 * half) values)
    end.

  Lemma butterfly_block_length (half : nat) (root : Z)
      (values : list Z) :
    2 * half <= List.length values ->
    List.length (butterfly_block half root values) = 2 * half.
  Proof.
    intros Hlength.
    unfold butterfly_block.
    assert (Hleft : List.length (List.firstn half values) = half).
    { rewrite List.firstn_length. apply Nat.min_l. lia. }
    assert (Hright :
      List.length (List.firstn half (List.skipn half values)) = half).
    { rewrite List.firstn_length, List.length_skipn.
      apply Nat.min_l. lia. }
    destruct (VkMsm.bfly_length root 1
      (List.firstn half values)
      (List.firstn half (List.skipn half values))
      ltac:(rewrite Hleft, Hright; reflexivity)) as [Hfirst Hsecond].
    destruct (VkMsm.bfly root 1 (List.firstn half values)
      (List.firstn half (List.skipn half values))) as [first second].
    cbn [fst snd] in Hfirst, Hsecond |- *.
    rewrite List.length_app, Hfirst, Hsecond, Hleft.
    lia.
  Qed.

  Lemma stage_blocks_length (count half : nat) (root : Z)
      (values : list Z) :
    List.length values = count * (2 * half) ->
    List.length (stage_blocks count half root values) =
      count * (2 * half).
  Proof.
    revert values.
    induction count as [|count IH]; intros values Hlength.
    - reflexivity.
    - cbn [stage_blocks].
      rewrite List.length_app.
      rewrite butterfly_block_length by lia.
      rewrite IH.
      + lia.
      + rewrite List.length_skipn, Hlength. lia.
  Qed.

  Lemma stage_blocks_app (left_count right_count half : nat)
      (root : Z) (left right : list Z) :
    List.length left = left_count * (2 * half) ->
    stage_blocks (left_count + right_count) half root (left ++ right) =
      stage_blocks left_count half root left ++
      stage_blocks right_count half root right.
  Proof.
    revert left.
    induction left_count as [|left_count IH]; intros left Hlength.
    - apply List.length_zero_iff_nil in Hlength. subst left. reflexivity.
    - cbn [stage_blocks].
      assert (Hblock : 2 * half <= List.length left) by lia.
      assert (Hfirst : List.firstn half (left ++ right) =
          List.firstn half left).
      { rewrite List.firstn_app.
        replace (half - List.length left) with O by lia.
        now rewrite List.firstn_O, List.app_nil_r. }
      assert (Hskip_first : List.skipn half (left ++ right) =
          List.skipn half left ++ right).
      { rewrite List.skipn_app.
        replace (half - List.length left) with O by lia.
        now rewrite List.skipn_O. }
      assert (Hskip_block : List.skipn (2 * half) (left ++ right) =
          List.skipn (2 * half) left ++ right).
      { rewrite List.skipn_app.
        replace (2 * half - List.length left) with O by lia.
        now rewrite List.skipn_O. }
      unfold butterfly_block at 1.
      rewrite Hfirst, Hskip_first.
      rewrite List.firstn_app.
      replace (half - List.length (List.skipn half left)) with O.
      2: { rewrite List.length_skipn. lia. }
      rewrite List.firstn_O, List.app_nil_r, Hskip_block.
      rewrite (IH (List.skipn (2 * half) left)).
      + rewrite List.app_assoc. reflexivity.
      + rewrite List.length_skipn, Hlength. lia.
  Qed.

  Lemma stage_blocks_one (half : nat) (root : Z)
      (left right : list Z) :
    List.length left = half -> List.length right = half ->
    stage_blocks 1 half root (left ++ right) =
      fst (VkMsm.bfly root 1 left right) ++
      snd (VkMsm.bfly root 1 left right).
  Proof.
    intros Hleft Hright.
    cbn [stage_blocks]. rewrite List.app_nil_r.
    unfold butterfly_block.
    rewrite List.firstn_app, Hleft, Nat.sub_diag, List.firstn_O,
      List.app_nil_r, List.firstn_all.
    rewrite List.skipn_app, Hleft, Nat.sub_diag, List.skipn_all,
      List.skipn_O, List.app_nil_l, List.firstn_all.
    reflexivity.
  Qed.

  Lemma butterfly_block_nth (half : nat) (root : Z)
      (values : list Z) (offset : nat) :
    2 * half <= List.length values -> offset < half ->
    List.nth offset (butterfly_block half root values) 0%Z =
      stage_left_value root values (2 * half) half O offset /\
    List.nth (half + offset) (butterfly_block half root values) 0%Z =
      stage_right_value root values (2 * half) half O offset.
  Proof.
    intros Hlength Hoffset.
    set (left := List.firstn half values).
    set (right := List.firstn half (List.skipn half values)).
    assert (Hleft : List.length left = half).
    { unfold left. rewrite List.firstn_length. apply Nat.min_l. lia. }
    assert (Hright : List.length right = half).
    { unfold right. rewrite List.firstn_length, List.length_skipn.
      apply Nat.min_l. lia. }
    pose proof (VkMsm.bfly_nth root 1 left right offset
      ltac:(rewrite Hleft, Hright; reflexivity)
      ltac:(rewrite Hleft; exact Hoffset)) as Hnth.
    destruct (VkMsm.bfly root 1 left right) as [first second] eqn:Hbfly.
    cbn [fst snd] in Hnth.
    destruct Hnth as [Hfirst Hsecond].
    pose proof (VkMsm.bfly_length root 1 left right
      ltac:(rewrite Hleft, Hright; reflexivity)) as Houtput_lengths.
    rewrite Hbfly in Houtput_lengths.
    cbn [fst snd] in Houtput_lengths.
    destruct Houtput_lengths as [Hfirst_length Hsecond_length].
    unfold butterfly_block.
    fold left right.
    rewrite Hbfly. cbn [fst snd].
    split.
    - rewrite List.app_nth1 by (rewrite Hfirst_length, Hleft; exact Hoffset).
      rewrite Hfirst.
      unfold stage_left_value.
      cbn [Nat.mul Nat.add].
      unfold left, right.
      rewrite !List.nth_firstn, !Nat.ltb_lt by exact Hoffset.
      rewrite List.nth_skipn.
      f_equal. ring.
    - rewrite List.app_nth2 by (rewrite Hfirst_length, Hleft; lia).
      rewrite Hfirst_length, Hleft.
      replace (half + offset - half) with offset by lia.
      rewrite Hsecond.
      unfold stage_right_value.
      cbn [Nat.mul Nat.add].
      unfold left, right.
      rewrite !List.nth_firstn, !Nat.ltb_lt by exact Hoffset.
      rewrite List.nth_skipn.
      f_equal. ring.
  Qed.

  Lemma stage_blocks_nth (count half : nat) (root : Z)
      (values : list Z) (block offset : nat) :
    List.length values = count * (2 * half) ->
    block < count -> offset < half ->
    List.nth (block * (2 * half) + offset)
      (stage_blocks count half root values) 0%Z =
        stage_left_value root values (2 * half) half block offset /\
    List.nth (block * (2 * half) + half + offset)
      (stage_blocks count half root values) 0%Z =
        stage_right_value root values (2 * half) half block offset.
  Proof.
    revert values block.
    induction count as [|count IH]; intros values [|block]
      Hlength Hblock Hoffset; try lia.
    - cbn [stage_blocks Nat.mul Nat.add].
      assert (Hbutterfly :
        List.length (butterfly_block half root values) = 2 * half)
        by (apply butterfly_block_length; lia).
      split.
      + rewrite List.app_nth1 by (rewrite Hbutterfly; exact Hoffset).
        exact (proj1 (butterfly_block_nth half root values offset
          ltac:(lia) Hoffset)).
      + rewrite List.app_nth1 by (rewrite Hbutterfly; lia).
        exact (proj2 (butterfly_block_nth half root values offset
          ltac:(lia) Hoffset)).
    - cbn [stage_blocks].
      assert (Hbutterfly :
        List.length (butterfly_block half root values) = 2 * half)
        by (apply butterfly_block_length; lia).
      assert (Htail :
        List.length (List.skipn (2 * half) values) =
          count * (2 * half)).
      { rewrite List.length_skipn, Hlength. nia. }
      pose proof (IH (List.skipn (2 * half) values) block
        Htail ltac:(lia) Hoffset) as [Hleft Hright].
      split.
      + rewrite List.app_nth2 by (rewrite Hbutterfly; nia).
        rewrite Hbutterfly.
        replace (S block * (2 * half) + offset - 2 * half)
          with (block * (2 * half) + offset) by nia.
        rewrite Hleft.
        unfold stage_left_value in *.
        rewrite !List.nth_skipn in Hleft |- *.
        replace (2 * half + (block * (2 * half) + offset))
          with (S block * (2 * half) + offset) by nia.
        replace (2 * half + (block * (2 * half) + offset + half))
          with (S block * (2 * half) + offset + half) by nia.
        reflexivity.
      + rewrite List.app_nth2 by (rewrite Hbutterfly; nia).
        rewrite Hbutterfly.
        replace (S block * (2 * half) + half + offset - 2 * half)
          with (block * (2 * half) + half + offset) by nia.
        rewrite Hright.
        unfold stage_right_value in *.
        rewrite !List.nth_skipn in Hright |- *.
        replace (2 * half + (block * (2 * half) + offset))
          with (S block * (2 * half) + offset) by nia.
        replace (2 * half + (block * (2 * half) + offset + half))
          with (S block * (2 * half) + offset + half) by nia.
        reflexivity.
  Qed.

  Lemma exact_stage_divisions (length half blocks : nat) :
    length = 2 * half -> 0 < half ->
    blocks * length = VkIFFT.size_nat ->
    length / 2 = half /\ VkIFFT.size_nat / length = blocks.
  Proof.
    intros Hlength Hhalf Hsize.
    split.
    - rewrite Hlength, Nat.mul_comm.
      apply Nat.div_mul. lia.
    - rewrite <- Hsize.
      apply Nat.div_mul. nia.
  Qed.

  Lemma stage_sound (certificate : VkDomain.certificate)
      (input : PrimArray.array F.t) (values : list Z)
      (length half blocks : nat)
      (Hlength : length = 2 * half) (Hhalf : 0 < half)
      (Hsize : blocks * length = VkIFFT.size_nat)
      (Hdenotes : array_denotes input values) :
    array_denotes
      (VkIFFT.stage VkDomainData.inverse_roots_array length input)
      (stage_blocks blocks half (inverse_stage_root blocks) values).
  Proof.
    destruct (exact_stage_divisions length half blocks
      Hlength Hhalf Hsize) as [Hhalf_div Hblocks_div].
    assert (Hvalues_blocks :
      List.length values = blocks * (2 * half)).
    { rewrite (array_denotes_values_length Hdenotes), <- Hsize, Hlength.
      reflexivity. }
    assert (Hstage_length :
      List.length
        (stage_blocks blocks half (inverse_stage_root blocks) values) =
        VkIFFT.size_nat).
    { rewrite stage_blocks_length by exact Hvalues_blocks.
      rewrite <- Hsize, Hlength. reflexivity. }
    pose proof (stage_entries VkDomainData.inverse_roots_array input
      length half blocks blocks Hlength Hhalf Hsize)
      as [Houtput_length Hentries].
    unfold VkIFFT.stage.
    cbn zeta.
    rewrite Hhalf_div, Hblocks_div.
    constructor.
    - exact Hstage_length.
    - exact Houtput_length.
    - intros index value Hvalue.
      assert (Hindex : index < VkIFFT.size_nat).
      { rewrite <- Hstage_length.
        apply (proj1 (List.nth_error_Some
          (stage_blocks blocks half (inverse_stage_root blocks) values)
          index)).
        rewrite Hvalue. discriminate. }
      assert (Hnthvalue :
        List.nth index
          (stage_blocks blocks half (inverse_stage_root blocks) values)
          0%Z = value).
      { apply List.nth_error_nth with (x := value).
        exact Hvalue. }
      remember (index / length) as block eqn:Hblock_definition.
      remember (index mod length) as within eqn:Hwithin_definition.
      assert (Hlength_positive : 0 < length) by nia.
      assert (Hdecompose : index = block * length + within).
      { subst block within.
        pose proof (Nat.div_mod index length ltac:(lia)) as Hdivmod.
        nia. }
      assert (Hwithin : within < length).
      { subst within. apply Nat.mod_upper_bound. lia. }
      assert (Hblock : block < blocks).
      { unfold VkIFFT.size_nat in Hsize, Hindex.
        nia. }
      destruct (Nat.lt_ge_cases within half) as [Hleft | Hright].
      + pose proof (stage_index_bounds length half blocks block within
          Hlength Hsize Hblock Hleft) as [Hleft_bound Hright_bound].
        assert (Htwiddle : within * blocks < 1024).
        { unfold VkIFFT.size_nat in Hsize. nia. }
        pose proof (stage_left_word_refines certificate input values
          length half blocks block within Hdenotes Hleft_bound
          Hright_bound Htwiddle) as [Hcanonical Hdenotation].
        pose proof (Hentries block Hblock within Hleft) as [Hentry _].
        pose proof (stage_blocks_nth blocks half
          (inverse_stage_root blocks) values block within
          Hvalues_blocks Hblock Hleft) as [Hlist _].
        assert (Hsame :
          index = stage_left_index length block within).
        { unfold stage_left_index. exact Hdecompose. }
        rewrite Hsame, Hentry.
        split; [exact Hcanonical |].
        rewrite Hdenotation.
        rewrite <- Hnthvalue, Hsame.
        unfold stage_left_index.
        rewrite Hlength.
        symmetry. exact Hlist.
      + set (offset := within - half).
        assert (Hoffset : offset < half).
        { unfold offset. rewrite Hlength in Hwithin. lia. }
        assert (Hwithin_offset : within = half + offset).
        { unfold offset. lia. }
        pose proof (stage_index_bounds length half blocks block offset
          Hlength Hsize Hblock Hoffset) as [Hleft_bound Hright_bound].
        assert (Htwiddle : offset * blocks < 1024).
        { unfold VkIFFT.size_nat in Hsize. nia. }
        pose proof (stage_right_word_refines certificate input values
          length half blocks block offset Hdenotes Hleft_bound
          Hright_bound Htwiddle) as [Hcanonical Hdenotation].
        pose proof (Hentries block Hblock offset Hoffset) as [_ Hentry].
        pose proof (stage_blocks_nth blocks half
          (inverse_stage_root blocks) values block offset
          Hvalues_blocks Hblock Hoffset) as [_ Hlist].
        assert (Hsame :
          index = stage_right_index length half block offset).
        { unfold stage_right_index, stage_left_index. nia. }
        rewrite Hsame, Hentry.
        split; [exact Hcanonical |].
        rewrite Hdenotation.
        rewrite <- Hnthvalue, Hsame.
        unfold stage_right_index, stage_left_index.
        rewrite Hlength.
        symmetry. exact Hlist.
  Qed.

  Definition stages_values (values : list Z) : list Z :=
    let values :=
      stage_blocks 1024 1 (inverse_stage_root 1024) values in
    let values :=
      stage_blocks 512 2 (inverse_stage_root 512) values in
    let values :=
      stage_blocks 256 4 (inverse_stage_root 256) values in
    let values :=
      stage_blocks 128 8 (inverse_stage_root 128) values in
    let values :=
      stage_blocks 64 16 (inverse_stage_root 64) values in
    let values :=
      stage_blocks 32 32 (inverse_stage_root 32) values in
    let values :=
      stage_blocks 16 64 (inverse_stage_root 16) values in
    let values :=
      stage_blocks 8 128 (inverse_stage_root 8) values in
    let values :=
      stage_blocks 4 256 (inverse_stage_root 4) values in
    let values :=
      stage_blocks 2 512 (inverse_stage_root 2) values in
    stage_blocks 1 1024 (inverse_stage_root 1) values.

  Lemma stages_sound (certificate : VkDomain.certificate)
      (input : PrimArray.array F.t) (values : list Z) :
    array_denotes input values ->
    array_denotes
      (VkIFFT.stages VkDomainData.inverse_roots_array input)
      (stages_values values).
  Proof.
    intros Hdenotes.
    pose proof (stage_sound certificate input values 2 1 1024
      eq_refl ltac:(lia) eq_refl Hdenotes) as H2.
    pose proof (stage_sound certificate _ _ 4 2 512
      eq_refl ltac:(lia) eq_refl H2) as H4.
    pose proof (stage_sound certificate _ _ 8 4 256
      eq_refl ltac:(lia) eq_refl H4) as H8.
    pose proof (stage_sound certificate _ _ 16 8 128
      eq_refl ltac:(lia) eq_refl H8) as H16.
    pose proof (stage_sound certificate _ _ 32 16 64
      eq_refl ltac:(lia) eq_refl H16) as H32.
    pose proof (stage_sound certificate _ _ 64 32 32
      eq_refl ltac:(lia) eq_refl H32) as H64.
    pose proof (stage_sound certificate _ _ 128 64 16
      eq_refl ltac:(lia) eq_refl H64) as H128.
    pose proof (stage_sound certificate _ _ 256 128 8
      eq_refl ltac:(lia) eq_refl H128) as H256.
    pose proof (stage_sound certificate _ _ 512 256 4
      eq_refl ltac:(lia) eq_refl H256) as H512.
    pose proof (stage_sound certificate _ _ 1024 512 2
      eq_refl ltac:(lia) eq_refl H512) as H1024.
    pose proof (stage_sound certificate _ _ 2048 1024 1
      eq_refl ltac:(lia) eq_refl H1024) as H2048.
    unfold VkIFFT.stages, stages_values.
    exact H2048.
  Qed.

  Fixpoint run_stages (copies : nat) (roots : list Z) (half : nat)
      (values : list Z) : list Z :=
    match roots with
    | [] => values
    | root :: roots =>
        run_stages copies roots (2 * half)
          (stage_blocks (copies * 2 ^ List.length roots) half root values)
    end.

  Lemma run_stages_length (copies : nat) (roots : list Z) (half : nat)
      (values : list Z) :
    List.length values = copies * 2 ^ List.length roots * half ->
    List.length (run_stages copies roots half values) =
      copies * 2 ^ List.length roots * half.
  Proof.
    revert half values.
    induction roots as [|root roots IH]; intros half values Hlength.
    - exact Hlength.
    - cbn [run_stages List.length] in *.
      rewrite IH.
      + exact Hlength.
      + rewrite stage_blocks_length.
        * cbn [Nat.pow] in Hlength |- *. lia.
        * cbn [Nat.pow] in Hlength |- *. lia.
  Qed.

  Lemma run_stages_add (left_copies right_copies : nat)
      (roots : list Z) (half : nat) (left right : list Z) :
    List.length left = left_copies * 2 ^ List.length roots * half ->
    List.length right = right_copies * 2 ^ List.length roots * half ->
    run_stages (left_copies + right_copies) roots half (left ++ right) =
      run_stages left_copies roots half left ++
      run_stages right_copies roots half right.
  Proof.
    revert half left right.
    induction roots as [|root roots IH]; intros half left right Hleft Hright.
    - reflexivity.
    - cbn [run_stages List.length] in *.
      rewrite stage_blocks_app.
      2: { cbn [Nat.pow] in Hleft |- *. lia. }
      rewrite IH.
      + reflexivity.
      + rewrite stage_blocks_length.
        * cbn [Nat.pow] in Hleft |- *. lia.
        * cbn [Nat.pow] in Hleft |- *. lia.
      + rewrite stage_blocks_length.
        * cbn [Nat.pow] in Hright |- *. lia.
        * cbn [Nat.pow] in Hright |- *. lia.
  Qed.

  Lemma nat_pow_add (base left right : nat) :
    base ^ (left + right) = base ^ left * base ^ right.
  Proof.
    induction left as [|left IH]; cbn [Nat.pow].
    - lia.
    - rewrite IH. ring.
  Qed.

  Lemma run_stages_app (copies : nat) (left_roots right_roots : list Z)
      (half : nat) (values : list Z) :
    run_stages copies (left_roots ++ right_roots) half values =
      run_stages copies right_roots (2 ^ List.length left_roots * half)
        (run_stages (copies * 2 ^ List.length right_roots)
          left_roots half values).
  Proof.
    revert copies half values.
    induction left_roots as [|root left_roots IH];
      intros copies half values.
    - cbn [run_stages List.length Nat.pow]. reflexivity.
    - cbn [run_stages List.length] in *.
      rewrite IH.
      cbn [Nat.pow].
      replace
        (copies * 2 ^ List.length right_roots *
          2 ^ List.length left_roots)
        with
        (copies * 2 ^ List.length (left_roots ++ right_roots))
        by (rewrite List.length_app, nat_pow_add; ring).
      replace (2 ^ List.length left_roots * (2 * half)) with
        (2 * 2 ^ List.length left_roots * half) by lia.
      reflexivity.
  Qed.

  Fixpoint stage_roots (count : nat) (root : Z) : list Z :=
    match count with
    | O => []
    | S count =>
        stage_roots count ((root * root) mod Primes.pallas_p)%Z ++ [root]
    end.

  Lemma stage_roots_length (count : nat) (root : Z) :
    List.length (stage_roots count root) = count.
  Proof.
    revert root.
    induction count as [|count IH]; intros root; cbn [stage_roots].
    - reflexivity.
    - rewrite List.length_app, IH. cbn. lia.
  Qed.

  Fixpoint stage_strides (count stride : nat) : list nat :=
    match count with
    | O => []
    | S count => stage_strides count (2 * stride) ++ [stride]
    end.

  Lemma inverse_stage_root_double (stride : nat) :
    (((inverse_stage_root stride * inverse_stage_root stride)
      mod Primes.pallas_p)%Z) = inverse_stage_root (2 * stride).
  Proof.
    unfold inverse_stage_root.
    rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by
      (pose proof VkMsm.scalar_p_big; lia).
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    rewrite Nat2Z.inj_mul.
    lia.
  Qed.

  Lemma stage_roots_from_power (count stride : nat) :
    stage_roots count (inverse_stage_root stride) =
      List.map inverse_stage_root (stage_strides count stride).
  Proof.
    revert stride.
    induction count as [|count IH]; intros stride.
    - reflexivity.
    - cbn [stage_roots, stage_strides].
      rewrite inverse_stage_root_double, IH, List.map_app.
      reflexivity.
  Qed.

  Lemma inverse_stage_root_one :
    inverse_stage_root 1 = VkMsm.omega_inv.
  Proof.
    unfold inverse_stage_root.
    rewrite Nat2Z.inj_1, Z.pow_1_r.
    apply Z.mod_small.
    exact VkMsm.omega_inv_range.
  Qed.

  Lemma stage_roots_11 :
    stage_roots 11 VkMsm.omega_inv =
      [inverse_stage_root 1024; inverse_stage_root 512;
       inverse_stage_root 256; inverse_stage_root 128;
       inverse_stage_root 64; inverse_stage_root 32;
       inverse_stage_root 16; inverse_stage_root 8;
       inverse_stage_root 4; inverse_stage_root 2;
       inverse_stage_root 1].
  Proof.
    rewrite <- inverse_stage_root_one at 1.
    rewrite stage_roots_from_power.
    reflexivity.
  Qed.

  Lemma stages_values_run (values : list Z) :
    stages_values values =
      run_stages 1 (stage_roots 11 VkMsm.omega_inv) 1 values.
  Proof.
    rewrite stage_roots_11.
    unfold stages_values.
    cbn only [run_stages List.length Nat.pow Nat.mul Nat.add].
    reflexivity.
  Qed.

  Definition iterative_fft (count : nat) (root : Z)
      (values : list Z) : list Z :=
    run_stages 1 (stage_roots count root) 1
      (bit_reverse_list count values).

  Lemma iterative_fft_correct (count : nat) (root : Z)
      (values : list Z) :
    List.length values = 2 ^ count ->
    iterative_fft count root values = VkMsm.fft count root values.
  Proof.
    revert root values.
    induction count as [|count IH]; intros root values Hlength.
    - unfold iterative_fft, bit_reverse_list, tabulate_n.
      cbn [stage_roots run_stages VkDomain.reverse_nat List.seq List.map].
      destruct values as [|value [|extra values]];
        cbn in Hlength; try lia; reflexivity.
    - assert (Hhalves :
        List.length (VkMsm.evens values) = 2 ^ count /\
        List.length (VkMsm.odds values) = 2 ^ count).
      { apply VkMsm.deinter_length.
        cbn [Nat.pow] in Hlength |- *. exact Hlength. }
      unfold iterative_fft at 1.
      cbn [stage_roots].
      rewrite bit_reverse_list_succ.
      rewrite run_stages_app.
      rewrite stage_roots_length.
      cbn [List.length Nat.pow Nat.mul].
      rewrite (run_stages_add 1 1 (stage_roots count
        ((root * root) mod Primes.pallas_p)%Z) 1).
      2: { rewrite bit_reverse_list_length, stage_roots_length. lia. }
      2: { rewrite bit_reverse_list_length, stage_roots_length. lia. }
      unfold iterative_fft in IH.
      rewrite (IH ((root * root) mod Primes.pallas_p)%Z
        (VkMsm.evens values) (proj1 Hhalves)).
      rewrite (IH ((root * root) mod Primes.pallas_p)%Z
        (VkMsm.odds values) (proj2 Hhalves)).
      rewrite stage_blocks_one.
      2: exact (proj1 Hhalves).
      2: exact (proj2 Hhalves).
      cbn [run_stages].
      cbn [VkMsm.fft].
      reflexivity.
  Qed.

  Lemma bit_reverse_values_spec (values : list Z) :
    bit_reverse_values values = bit_reverse_list 11 values.
  Proof. reflexivity. Qed.

  Definition scale_values (values : list Z) : list Z :=
    List.map (fun value => (VkMsm.n_inv * value) mod Primes.pallas_p)%Z
      values.

  Lemma scale_values_length (values : list Z) :
    List.length (scale_values values) = List.length values.
  Proof. apply List.length_map. Qed.

  Lemma scale_sound (array : PrimArray.array F.t) (values : list Z) :
    array_denotes array values ->
    array_denotes (VkIFFT.scale VkDomainData.n_inverse array)
      (scale_values values).
  Proof.
    intros Hdenotes.
    remember (VkIFFT.scale VkDomainData.n_inverse array)
      as output eqn:Houtput.
    destruct (scale_fill_spec VkDomainData.n_inverse array output Houtput)
      as [Hlength Hentry].
    constructor.
    - rewrite scale_values_length.
      exact (array_denotes_values_length Hdenotes).
    - exact Hlength.
    - intros index value Hvalue.
      rewrite List.nth_error_map in Hvalue.
      destruct (List.nth_error values index) as [input |] eqn:Hinput;
        cbn in Hvalue; [inversion Hvalue; subst value | discriminate].
      pose proof (array_denotes_entry Hdenotes index input Hinput)
        as [Hcanonical Hdenote].
      assert (Hindex : index < VkIFFT.size_nat).
      { apply (proj1 (List.nth_error_Some values index)).
        rewrite Hinput. discriminate. }
      pose proof (Hentry index Hindex) as Hloaded.
      change
        (PrimArray.get output
          (ArrayLinear.index index) =
          F.mul (PrimArray.get array (ArrayLinear.index index))
            VkDomainData.n_inverse) in Hloaded.
      assert (Hproduct_canonical :
        F.canonical
          (F.mul (PrimArray.get array (ArrayLinear.index index))
            VkDomainData.n_inverse)).
      { apply FR.mul_canonical. exact n_inverse_canonical. }
      split.
      + exact (eq_ind_r F.canonical Hproduct_canonical Hloaded).
      + refine (eq_trans (f_equal F.denote Hloaded) _).
        rewrite FR.mul_denote by exact n_inverse_canonical.
        rewrite Hdenote, n_inverse_denote.
        reflexivity.
  Qed.

  Lemma inverse_fft_values (values : list Z) :
    List.length values = VkIFFT.size_nat ->
    scale_values (stages_values (bit_reverse_values values)) =
      VkMsm.intt values.
  Proof.
    intros Hlength.
    rewrite bit_reverse_values_spec, stages_values_run.
    fold (iterative_fft 11 VkMsm.omega_inv values).
    rewrite iterative_fft_correct.
    - reflexivity.
    - exact Hlength.
  Qed.

  Theorem inverse_fft_sound (certificate : VkDomain.certificate)
      (array : PrimArray.array F.t) (values : list Z) :
    array_denotes array values ->
    array_denotes
      (VkIFFT.inverse_fft VkDomainData.bit_reversed_array
        VkDomainData.inverse_roots_array VkDomainData.n_inverse array)
      (VkMsm.intt values).
  Proof.
    intros Hdenotes.
    pose proof (bit_reverse_sound certificate array values Hdenotes)
      as Hreversed.
    pose proof (stages_sound certificate _ _ Hreversed) as Hstages.
    pose proof (scale_sound _ _ Hstages) as Hscaled.
    rewrite (inverse_fft_values values
      (array_denotes_values_length Hdenotes)) in Hscaled.
    unfold VkIFFT.inverse_fft.
    exact Hscaled.
  Qed.

  Lemma coefficients_match_array_entries
      (computed : PrimArray.array F.t)
      (expected : PrimArray.array Prim63Words.words5) :
    VkIFFT.coefficients_match_array computed expected = true ->
    forall index : nat, index < VkIFFT.size_nat ->
      F.equal
        (F.decode
          (PrimArray.get computed (ArrayLinear.index index)))
        (PrimArray.get expected (ArrayLinear.index index)) = true.
  Proof.
    intros Hcheck.
    unfold VkIFFT.coefficients_match_array in Hcheck.
    change 0%uint63 with (ArrayLinear.index O) in Hcheck.
    rewrite Prim63Loop.foldi_u63_index in Hcheck by
      exact ArrayLinear.vector_size_fits_word.
    destruct (foldi_from_and_true VkIFFT.size_nat O
      (fun index =>
        F.equal
          (F.decode
            (PrimArray.get computed (ArrayLinear.index index)))
          (PrimArray.get expected (ArrayLinear.index index)))
      true Hcheck) as [_ Hentries].
    intros index Hindex.
    apply Hentries. lia.
  Qed.

  Lemma coefficients_match_array_sound
      (computed : PrimArray.array F.t) (values : list Z)
      (coefficients : list Prim63Words.words5) :
    array_denotes computed values ->
    List.length coefficients = VkIFFT.size_nat ->
    VkIFFT.coefficients_match_array computed
      (VkIFFT.standard_coefficients_array coefficients) = true ->
    List.map Prim63Words.eval5 coefficients = values.
  Proof.
    intros Hdenotes Hcoefficients_length Hcheck.
    pose proof (coefficients_match_array_entries computed
      (VkIFFT.standard_coefficients_array coefficients) Hcheck)
      as Hentries.
    apply List.nth_ext with
      (d := Prim63Words.eval5 Prim63Words.zero5) (d' := 0%Z).
    - rewrite List.length_map, Hcoefficients_length.
      exact (array_denotes_values_length Hdenotes).
    - intros index Hindex.
      rewrite List.length_map, Hcoefficients_length in Hindex.
      rewrite (List.map_nth Prim63Words.eval5 coefficients
        Prim63Words.zero5 index).
      set (coefficient :=
        List.nth index coefficients Prim63Words.zero5).
      assert (Hcoefficient :
        List.nth_error coefficients index = Some coefficient).
      { unfold coefficient.
        apply List.nth_error_nth'.
        rewrite Hcoefficients_length. exact Hindex. }
      pose proof (VkArrayOfListRefinement.array_of_list_get
        Prim63Words.zero5 coefficient coefficients index
        ltac:(rewrite Hcoefficients_length;
          exact ArrayLinear.vector_size_fits_word)
        ltac:(rewrite Hcoefficients_length;
          exact ArrayLinear.vector_size_fits_array)
        Hcoefficient) as Hexpected.
      pose proof (Hentries index Hindex) as Hequal.
      unfold VkIFFT.standard_coefficients_array in Hequal.
      rewrite Hexpected in Hequal.
      apply (proj1 (FR.equal_spec _ _)) in Hequal.
      pose proof (array_denotes_nth computed values Hdenotes
        index Hindex) as [_ Hcomputed].
      rewrite <- Hequal, FR.decode_eval5.
      exact Hcomputed.
  Qed.

  Theorem coefficients_match_sound
      (certificate : VkDomain.certificate) (evaluation : nat -> Z)
      (coefficients : list Prim63Words.words5) :
    VkIFFT.coefficients_match VkDomainData.bit_reversed_array
      VkDomainData.inverse_roots_array VkDomainData.n_inverse
      evaluation coefficients = true ->
    List.map Prim63Words.eval5 coefficients =
      VkMsm.intt
        (List.map
          (fun row => (evaluation row mod Primes.pallas_p)%Z)
          (List.seq O 2048)).
  Proof.
    intros Hcheck.
    unfold VkIFFT.coefficients_match in Hcheck.
    apply andb_prop in Hcheck as [Hlength Harray].
    apply Nat.eqb_eq in Hlength.
    pose proof (load_evaluations_sound evaluation) as Hloaded.
    pose proof (inverse_fft_sound certificate _ _ Hloaded) as Hcomputed.
    pose proof (coefficients_match_array_sound _ _ coefficients
      Hcomputed Hlength Harray) as Hsound.
    unfold evaluation_values, tabulate in Hsound.
    exact Hsound.
  Qed.

  Theorem coefficients_match_field_sound
      (certificate : VkDomain.certificate) (evaluation : nat -> F.t)
      (coefficients : list Prim63Words.words5) :
    (forall row : nat, row < VkIFFT.size_nat ->
      F.canonical (evaluation row)) ->
    VkIFFT.coefficients_match_field VkDomainData.bit_reversed_array
      VkDomainData.inverse_roots_array VkDomainData.n_inverse
      evaluation coefficients = true ->
    List.map Prim63Words.eval5 coefficients =
      VkMsm.intt
        (List.map (fun row => F.denote (evaluation row))
          (List.seq O 2048)).
  Proof.
    intros Hcanonical Hcheck.
    unfold VkIFFT.coefficients_match_field in Hcheck.
    apply andb_prop in Hcheck as [Hlength Harray].
    apply Nat.eqb_eq in Hlength.
    pose proof (load_field_evaluations_sound evaluation Hcanonical)
      as Hloaded.
    pose proof (inverse_fft_sound certificate _ _ Hloaded) as Hcomputed.
    pose proof (coefficients_match_array_sound _ _ coefficients
      Hcomputed Hlength Harray) as Hsound.
    unfold field_evaluation_values, tabulate in Hsound.
    exact Hsound.
  Qed.

End VkDomainRefinement.
