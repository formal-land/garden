(** * Derived Orchard configure state used by key generation *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.configure_metadata.
Require Garden.Orchard.circuit.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardConfigure.

(** The explicit formal metadata trace is installed in the same free
    configure program that produces the gate and lookup constraint system.
    Its correspondence with the Rust builder is checked by the external
    configure-JSON comparison; it is not reconstructed from gate ASTs. *)
Definition state : Metadata.State.t :=
  𝓒.run_metadata_unit
    OrchardConfigureMetadata.indices
    Garden.Orchard.circuit.configure
    Metadata.State.empty.

Definition counts : Metadata.Counts.t := state.(Metadata.State.counts).
Definition base_fixed_columns : Z := counts.(Metadata.Counts.fixed).
Definition num_advice_columns : Z := counts.(Metadata.Counts.advice).
Definition num_instance_columns : Z := counts.(Metadata.Counts.instance_).
Definition num_selectors : Z := counts.(Metadata.Counts.selectors).
Definition selector_types : list bool := state.(Metadata.State.selector_types).
Definition advice_queries : list (Z * Z) :=
  state.(Metadata.State.queries).(Metadata.Queries.advice).
Definition fixed_queries : list (Z * Z) :=
  state.(Metadata.State.queries).(Metadata.Queries.fixed).
Definition instance_queries : list (Z * Z) :=
  state.(Metadata.State.queries).(Metadata.Queries.instance_).
Definition constants : list Z := state.(Metadata.State.constants).
Definition minimum_degree : option nat := state.(Metadata.State.minimum_degree).

Definition raw_column_kind
    (kind : Metadata.IndexedColumn.Kind) : Raw.ColumnKind.t :=
  match kind with
  | Metadata.IndexedColumn.Advice => Raw.ColumnKind.Advice
  | Metadata.IndexedColumn.Fixed => Raw.ColumnKind.Fixed
  | Metadata.IndexedColumn.Instance_ => Raw.ColumnKind.Instance_
  end.

Definition raw_column (column : Metadata.IndexedColumn.t) : Raw.ColumnRef.t := {|
  Raw.ColumnRef.kind := raw_column_kind column.(Metadata.IndexedColumn.kind);
  Raw.ColumnRef.index := column.(Metadata.IndexedColumn.index);
|}.

Definition permutation_columns : list Raw.ColumnRef.t :=
  List.map raw_column state.(Metadata.State.permutation_columns).

(** A lookup-column identifier is its position in the typed [Lookup] type;
    the metadata allocator records the corresponding fixed-column index. *)
Definition lookup_fixed_column (lookup_index : Z) : Z :=
  List.nth (Z.to_nat lookup_index) state.(Metadata.State.lookup_columns) (-1).

Lemma state_valid : state.(Metadata.State.valid) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma base_fixed_columns_eq : base_fixed_columns = 14.
Proof. vm_compute. reflexivity. Qed.

Lemma num_advice_columns_eq : num_advice_columns = 10.
Proof. vm_compute. reflexivity. Qed.

Lemma num_instance_columns_eq : num_instance_columns = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma num_selectors_eq : num_selectors = 56.
Proof. vm_compute. reflexivity. Qed.

Lemma minimum_degree_eq : minimum_degree = None.
Proof. vm_compute. reflexivity. Qed.

Lemma lookup_fixed_columns_eq :
  List.map lookup_fixed_column [0; 1; 2] = [0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

End OrchardConfigure.
