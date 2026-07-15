Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.

(** Decidable and Boolean equality for the Orchard column and region
    enumerations, together with reflection lemmas.  The completeness layer
    compares selectors, columns, regions, and cells while folding the finite
    witness facts, so it needs a computable [eqb] with a reflection principle
    for each of these types.  The definitions here leave [columns.v] and
    [regions.v] untouched. *)
Module OrchardDecidableEq.
  Local Open Scope Z_scope.

  (** Boolean equality derived from a decidable-equality procedure, with the
      three reflection views used downstream. *)
  Definition dec_to_eqb {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
      (x y : A) : bool :=
    if dec x y then true else false.

  Lemma dec_to_eqb_eq {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
      (x y : A) :
    dec_to_eqb dec x y = true <-> x = y.
  Proof. unfold dec_to_eqb; destruct (dec x y); split; congruence. Qed.

  Lemma dec_to_eqb_refl {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
      (x : A) :
    dec_to_eqb dec x x = true.
  Proof. unfold dec_to_eqb; destruct (dec x x); congruence. Qed.

  Lemma dec_to_eqb_spec {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
      (x y : A) :
    reflect (x = y) (dec_to_eqb dec x y).
  Proof.
    unfold dec_to_eqb; destruct (dec x y); [ now apply ReflectT | now apply ReflectF ].
  Qed.

  (** * Column enumerations (columns.v). *)

  Definition advice_eq_dec (x y : Advice.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition fixed_eq_dec (x y : Fixed.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition lookup_eq_dec (x y : Lookup.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition instance_eq_dec (x y : Instance_.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition selector_eq_dec (x y : Selector.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  (** * Region sub-enumerations (regions.v). *)

  Definition witness_input_eq_dec (x y : RegionId.WitnessInput.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition merkle_layer_eq_dec (x y : RegionId.Merkle.Layer.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition merkle_region_eq_dec (x y : RegionId.Merkle.Region.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition poseidon_eq_dec (x y : RegionId.Poseidon.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition value_commitment_eq_dec (x y : RegionId.ValueCommitment.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition nullifier_eq_dec (x y : RegionId.Nullifier.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition spend_authority_eq_dec (x y : RegionId.SpendAuthority.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition addr_mul_eq_dec (x y : RegionId.AddressIntegrity.Mul.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition addr_eq_dec (x y : RegionId.AddressIntegrity.t) : {x = y} + {x <> y}.
  Proof. decide equality; solve [ apply addr_mul_eq_dec ]. Defined.

  Definition commit_ivk_eq_dec (x y : RegionId.CommitIvk.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition note_commit_which_eq_dec (x y : RegionId.NoteCommit.Which.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition note_commit_ysubject_eq_dec (x y : RegionId.NoteCommit.YSubject.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition note_commit_ycanon_eq_dec (x y : RegionId.NoteCommit.YCanonicity.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition note_commit_eq_dec (x y : RegionId.NoteCommit.t) : {x = y} + {x <> y}.
  Proof.
    decide equality;
      solve [ apply note_commit_ysubject_eq_dec | apply note_commit_ycanon_eq_dec ].
  Defined.

  Definition gadget_local_eq_dec (x y : RegionId.GadgetLocal.t) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  (** * The top-level region identifier (regions.v). *)

  Definition region_id_eq_dec (x y : RegionId.t) : {x = y} + {x <> y}.
  Proof.
    decide equality;
      solve [ apply witness_input_eq_dec
            | apply merkle_layer_eq_dec
            | apply merkle_region_eq_dec
            | apply poseidon_eq_dec
            | apply value_commitment_eq_dec
            | apply nullifier_eq_dec
            | apply spend_authority_eq_dec
            | apply addr_eq_dec
            | apply commit_ivk_eq_dec
            | apply note_commit_eq_dec
            | apply note_commit_which_eq_dec
            | apply gadget_local_eq_dec ].
  Defined.

  (** * Column references and cells (Synthesis.v), over the Orchard columns and
        region identifier. *)

  Definition column_ref_eq_dec (x y : ColumnRef.t columns) : {x = y} + {x <> y}.
  Proof.
    decide equality;
      solve [ apply advice_eq_dec | apply fixed_eq_dec | apply instance_eq_dec ].
  Defined.

  Definition cell_eq_dec (x y : Cell.t columns RegionId.t) : {x = y} + {x <> y}.
  Proof.
    decide equality;
      solve [ apply Z.eq_dec | apply region_id_eq_dec | apply column_ref_eq_dec ].
  Defined.

  (** * Boolean equality and reflection for every type above. *)

  Definition advice_eqb : Advice.t -> Advice.t -> bool := dec_to_eqb advice_eq_dec.
  Definition advice_eqb_eq x y : advice_eqb x y = true <-> x = y := dec_to_eqb_eq advice_eq_dec x y.
  Definition advice_eqb_refl x : advice_eqb x x = true := dec_to_eqb_refl advice_eq_dec x.
  Definition advice_eqb_spec x y : reflect (x = y) (advice_eqb x y) := dec_to_eqb_spec advice_eq_dec x y.

  Definition fixed_eqb : Fixed.t -> Fixed.t -> bool := dec_to_eqb fixed_eq_dec.
  Definition fixed_eqb_eq x y : fixed_eqb x y = true <-> x = y := dec_to_eqb_eq fixed_eq_dec x y.
  Definition fixed_eqb_refl x : fixed_eqb x x = true := dec_to_eqb_refl fixed_eq_dec x.
  Definition fixed_eqb_spec x y : reflect (x = y) (fixed_eqb x y) := dec_to_eqb_spec fixed_eq_dec x y.

  Definition lookup_eqb : Lookup.t -> Lookup.t -> bool := dec_to_eqb lookup_eq_dec.
  Definition lookup_eqb_eq x y : lookup_eqb x y = true <-> x = y := dec_to_eqb_eq lookup_eq_dec x y.
  Definition lookup_eqb_refl x : lookup_eqb x x = true := dec_to_eqb_refl lookup_eq_dec x.
  Definition lookup_eqb_spec x y : reflect (x = y) (lookup_eqb x y) := dec_to_eqb_spec lookup_eq_dec x y.

  Definition instance_eqb : Instance_.t -> Instance_.t -> bool := dec_to_eqb instance_eq_dec.
  Definition instance_eqb_eq x y : instance_eqb x y = true <-> x = y := dec_to_eqb_eq instance_eq_dec x y.
  Definition instance_eqb_refl x : instance_eqb x x = true := dec_to_eqb_refl instance_eq_dec x.
  Definition instance_eqb_spec x y : reflect (x = y) (instance_eqb x y) := dec_to_eqb_spec instance_eq_dec x y.

  Definition selector_eqb : Selector.t -> Selector.t -> bool := dec_to_eqb selector_eq_dec.
  Definition selector_eqb_eq x y : selector_eqb x y = true <-> x = y := dec_to_eqb_eq selector_eq_dec x y.
  Definition selector_eqb_refl x : selector_eqb x x = true := dec_to_eqb_refl selector_eq_dec x.
  Definition selector_eqb_spec x y : reflect (x = y) (selector_eqb x y) := dec_to_eqb_spec selector_eq_dec x y.

  Definition witness_input_eqb : RegionId.WitnessInput.t -> RegionId.WitnessInput.t -> bool :=
    dec_to_eqb witness_input_eq_dec.
  Definition witness_input_eqb_eq x y : witness_input_eqb x y = true <-> x = y := dec_to_eqb_eq witness_input_eq_dec x y.
  Definition witness_input_eqb_refl x : witness_input_eqb x x = true := dec_to_eqb_refl witness_input_eq_dec x.
  Definition witness_input_eqb_spec x y : reflect (x = y) (witness_input_eqb x y) := dec_to_eqb_spec witness_input_eq_dec x y.

  Definition merkle_layer_eqb : RegionId.Merkle.Layer.t -> RegionId.Merkle.Layer.t -> bool :=
    dec_to_eqb merkle_layer_eq_dec.
  Definition merkle_layer_eqb_eq x y : merkle_layer_eqb x y = true <-> x = y := dec_to_eqb_eq merkle_layer_eq_dec x y.
  Definition merkle_layer_eqb_refl x : merkle_layer_eqb x x = true := dec_to_eqb_refl merkle_layer_eq_dec x.
  Definition merkle_layer_eqb_spec x y : reflect (x = y) (merkle_layer_eqb x y) := dec_to_eqb_spec merkle_layer_eq_dec x y.

  Definition merkle_region_eqb : RegionId.Merkle.Region.t -> RegionId.Merkle.Region.t -> bool :=
    dec_to_eqb merkle_region_eq_dec.
  Definition merkle_region_eqb_eq x y : merkle_region_eqb x y = true <-> x = y := dec_to_eqb_eq merkle_region_eq_dec x y.
  Definition merkle_region_eqb_refl x : merkle_region_eqb x x = true := dec_to_eqb_refl merkle_region_eq_dec x.
  Definition merkle_region_eqb_spec x y : reflect (x = y) (merkle_region_eqb x y) := dec_to_eqb_spec merkle_region_eq_dec x y.

  Definition poseidon_eqb : RegionId.Poseidon.t -> RegionId.Poseidon.t -> bool :=
    dec_to_eqb poseidon_eq_dec.
  Definition poseidon_eqb_eq x y : poseidon_eqb x y = true <-> x = y := dec_to_eqb_eq poseidon_eq_dec x y.
  Definition poseidon_eqb_refl x : poseidon_eqb x x = true := dec_to_eqb_refl poseidon_eq_dec x.
  Definition poseidon_eqb_spec x y : reflect (x = y) (poseidon_eqb x y) := dec_to_eqb_spec poseidon_eq_dec x y.

  Definition value_commitment_eqb : RegionId.ValueCommitment.t -> RegionId.ValueCommitment.t -> bool :=
    dec_to_eqb value_commitment_eq_dec.
  Definition value_commitment_eqb_eq x y : value_commitment_eqb x y = true <-> x = y := dec_to_eqb_eq value_commitment_eq_dec x y.
  Definition value_commitment_eqb_refl x : value_commitment_eqb x x = true := dec_to_eqb_refl value_commitment_eq_dec x.
  Definition value_commitment_eqb_spec x y : reflect (x = y) (value_commitment_eqb x y) := dec_to_eqb_spec value_commitment_eq_dec x y.

  Definition nullifier_eqb : RegionId.Nullifier.t -> RegionId.Nullifier.t -> bool :=
    dec_to_eqb nullifier_eq_dec.
  Definition nullifier_eqb_eq x y : nullifier_eqb x y = true <-> x = y := dec_to_eqb_eq nullifier_eq_dec x y.
  Definition nullifier_eqb_refl x : nullifier_eqb x x = true := dec_to_eqb_refl nullifier_eq_dec x.
  Definition nullifier_eqb_spec x y : reflect (x = y) (nullifier_eqb x y) := dec_to_eqb_spec nullifier_eq_dec x y.

  Definition spend_authority_eqb : RegionId.SpendAuthority.t -> RegionId.SpendAuthority.t -> bool :=
    dec_to_eqb spend_authority_eq_dec.
  Definition spend_authority_eqb_eq x y : spend_authority_eqb x y = true <-> x = y := dec_to_eqb_eq spend_authority_eq_dec x y.
  Definition spend_authority_eqb_refl x : spend_authority_eqb x x = true := dec_to_eqb_refl spend_authority_eq_dec x.
  Definition spend_authority_eqb_spec x y : reflect (x = y) (spend_authority_eqb x y) := dec_to_eqb_spec spend_authority_eq_dec x y.

  Definition addr_mul_eqb : RegionId.AddressIntegrity.Mul.t -> RegionId.AddressIntegrity.Mul.t -> bool :=
    dec_to_eqb addr_mul_eq_dec.
  Definition addr_mul_eqb_eq x y : addr_mul_eqb x y = true <-> x = y := dec_to_eqb_eq addr_mul_eq_dec x y.
  Definition addr_mul_eqb_refl x : addr_mul_eqb x x = true := dec_to_eqb_refl addr_mul_eq_dec x.
  Definition addr_mul_eqb_spec x y : reflect (x = y) (addr_mul_eqb x y) := dec_to_eqb_spec addr_mul_eq_dec x y.

  Definition addr_eqb : RegionId.AddressIntegrity.t -> RegionId.AddressIntegrity.t -> bool :=
    dec_to_eqb addr_eq_dec.
  Definition addr_eqb_eq x y : addr_eqb x y = true <-> x = y := dec_to_eqb_eq addr_eq_dec x y.
  Definition addr_eqb_refl x : addr_eqb x x = true := dec_to_eqb_refl addr_eq_dec x.
  Definition addr_eqb_spec x y : reflect (x = y) (addr_eqb x y) := dec_to_eqb_spec addr_eq_dec x y.

  Definition commit_ivk_eqb : RegionId.CommitIvk.t -> RegionId.CommitIvk.t -> bool :=
    dec_to_eqb commit_ivk_eq_dec.
  Definition commit_ivk_eqb_eq x y : commit_ivk_eqb x y = true <-> x = y := dec_to_eqb_eq commit_ivk_eq_dec x y.
  Definition commit_ivk_eqb_refl x : commit_ivk_eqb x x = true := dec_to_eqb_refl commit_ivk_eq_dec x.
  Definition commit_ivk_eqb_spec x y : reflect (x = y) (commit_ivk_eqb x y) := dec_to_eqb_spec commit_ivk_eq_dec x y.

  Definition note_commit_which_eqb : RegionId.NoteCommit.Which.t -> RegionId.NoteCommit.Which.t -> bool :=
    dec_to_eqb note_commit_which_eq_dec.
  Definition note_commit_which_eqb_eq x y : note_commit_which_eqb x y = true <-> x = y := dec_to_eqb_eq note_commit_which_eq_dec x y.
  Definition note_commit_which_eqb_refl x : note_commit_which_eqb x x = true := dec_to_eqb_refl note_commit_which_eq_dec x.
  Definition note_commit_which_eqb_spec x y : reflect (x = y) (note_commit_which_eqb x y) := dec_to_eqb_spec note_commit_which_eq_dec x y.

  Definition note_commit_ysubject_eqb : RegionId.NoteCommit.YSubject.t -> RegionId.NoteCommit.YSubject.t -> bool :=
    dec_to_eqb note_commit_ysubject_eq_dec.
  Definition note_commit_ysubject_eqb_eq x y : note_commit_ysubject_eqb x y = true <-> x = y := dec_to_eqb_eq note_commit_ysubject_eq_dec x y.
  Definition note_commit_ysubject_eqb_refl x : note_commit_ysubject_eqb x x = true := dec_to_eqb_refl note_commit_ysubject_eq_dec x.
  Definition note_commit_ysubject_eqb_spec x y : reflect (x = y) (note_commit_ysubject_eqb x y) := dec_to_eqb_spec note_commit_ysubject_eq_dec x y.

  Definition note_commit_ycanon_eqb : RegionId.NoteCommit.YCanonicity.t -> RegionId.NoteCommit.YCanonicity.t -> bool :=
    dec_to_eqb note_commit_ycanon_eq_dec.
  Definition note_commit_ycanon_eqb_eq x y : note_commit_ycanon_eqb x y = true <-> x = y := dec_to_eqb_eq note_commit_ycanon_eq_dec x y.
  Definition note_commit_ycanon_eqb_refl x : note_commit_ycanon_eqb x x = true := dec_to_eqb_refl note_commit_ycanon_eq_dec x.
  Definition note_commit_ycanon_eqb_spec x y : reflect (x = y) (note_commit_ycanon_eqb x y) := dec_to_eqb_spec note_commit_ycanon_eq_dec x y.

  Definition note_commit_eqb : RegionId.NoteCommit.t -> RegionId.NoteCommit.t -> bool :=
    dec_to_eqb note_commit_eq_dec.
  Definition note_commit_eqb_eq x y : note_commit_eqb x y = true <-> x = y := dec_to_eqb_eq note_commit_eq_dec x y.
  Definition note_commit_eqb_refl x : note_commit_eqb x x = true := dec_to_eqb_refl note_commit_eq_dec x.
  Definition note_commit_eqb_spec x y : reflect (x = y) (note_commit_eqb x y) := dec_to_eqb_spec note_commit_eq_dec x y.

  Definition gadget_local_eqb : RegionId.GadgetLocal.t -> RegionId.GadgetLocal.t -> bool :=
    dec_to_eqb gadget_local_eq_dec.
  Definition gadget_local_eqb_eq x y : gadget_local_eqb x y = true <-> x = y := dec_to_eqb_eq gadget_local_eq_dec x y.
  Definition gadget_local_eqb_refl x : gadget_local_eqb x x = true := dec_to_eqb_refl gadget_local_eq_dec x.
  Definition gadget_local_eqb_spec x y : reflect (x = y) (gadget_local_eqb x y) := dec_to_eqb_spec gadget_local_eq_dec x y.

  Definition region_id_eqb : RegionId.t -> RegionId.t -> bool := dec_to_eqb region_id_eq_dec.
  Definition region_id_eqb_eq x y : region_id_eqb x y = true <-> x = y := dec_to_eqb_eq region_id_eq_dec x y.
  Definition region_id_eqb_refl x : region_id_eqb x x = true := dec_to_eqb_refl region_id_eq_dec x.
  Definition region_id_eqb_spec x y : reflect (x = y) (region_id_eqb x y) := dec_to_eqb_spec region_id_eq_dec x y.

  Definition column_ref_eqb : ColumnRef.t columns -> ColumnRef.t columns -> bool := dec_to_eqb column_ref_eq_dec.
  Definition column_ref_eqb_eq x y : column_ref_eqb x y = true <-> x = y := dec_to_eqb_eq column_ref_eq_dec x y.
  Definition column_ref_eqb_refl x : column_ref_eqb x x = true := dec_to_eqb_refl column_ref_eq_dec x.
  Definition column_ref_eqb_spec x y : reflect (x = y) (column_ref_eqb x y) := dec_to_eqb_spec column_ref_eq_dec x y.

  Definition cell_eqb : Cell.t columns RegionId.t -> Cell.t columns RegionId.t -> bool := dec_to_eqb cell_eq_dec.
  Definition cell_eqb_eq x y : cell_eqb x y = true <-> x = y := dec_to_eqb_eq cell_eq_dec x y.
  Definition cell_eqb_refl x : cell_eqb x x = true := dec_to_eqb_refl cell_eq_dec x.
  Definition cell_eqb_spec x y : reflect (x = y) (cell_eqb x y) := dec_to_eqb_spec cell_eq_dec x y.
End OrchardDecidableEq.
