(* Certificate for the constant emissions: the [𝓡.ConstrainConstant] operations
   of the Orchard synthesis program, resolved to absolute cells through the
   serializer's [indices] and the V1 [region_start_of] placement, coincide as
   a multiset with the Halo2 floor-planner constant bindings replayed from the
   Rust implementation dump ([circuit_synthesis_constants.v]).  This is the
   constants-mechanism analogue of the synthesis JSON parity comparison: the
   replay table is generated from the Rust side, so equality here checks the
   hand-written emissions against the real circuit. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.serialize.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit_synthesis_constants.
Require Garden.Orchard.circuit_synthesis_layout.

Import ListNotations.
Global Open Scope Z_scope.

Module ConstantsCheck.
  (* Collect the [ConstrainConstant] leaves of a region program, resolving
     cells the same way [V1.eval_region] resolves its raw events. *)
  Fixpoint region_constants {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (region : RegionId)
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      {struct program}
      : A * list (Raw.Cell.t * Z) :=
    match program with
    | Garden.Halo2.Synthesis.𝓡.Ret value => (value, [])
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        let '(value, constants_first) :=
          region_constants indices region_start region first in
        let '(value, constants_second) :=
          region_constants indices region_start region (second value) in
        (value, constants_first ++ constants_second)
    | Garden.Halo2.Synthesis.𝓡.EnableSelector _ _ _ => (tt, [])
    | Garden.Halo2.Synthesis.𝓡.AssignFixed _ _ _ _ => (tt, [])
    | Garden.Halo2.Synthesis.𝓡.Copy _ _ => (tt, [])
    | Garden.Halo2.Synthesis.𝓡.ConstrainConstant cell value =>
        (tt, [(Cell.to_raw indices region_start cell, value)])
    end.

  Fixpoint layouter_constants {columns : Columns.t} {RegionId : Set} {A : Set}
      (indices : Indices.t columns)
      (region_start : RegionId -> Z)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : A * list (Raw.Cell.t * Z) :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret value => (value, [])
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        let '(value, constants_first) :=
          layouter_constants indices region_start first in
        let '(value, constants_second) :=
          layouter_constants indices region_start (second value) in
        (value, constants_first ++ constants_second)
    | Garden.Halo2.Synthesis.𝓛.AddRegion region _ region_program =>
        region_constants indices region_start region (region_program region)
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance _ _ _ => (tt, [])
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables _ _ => (tt, [])
    | Garden.Halo2.Synthesis.𝓛.InNamespace _ nested =>
        layouter_constants indices region_start nested
    end.

  (* Injective key: the column kind and index, the absolute row, and the
     pinned value packed into one [Z].  Rows and column indices are far below
     [2^40], and pinned values are field elements below [2^256]. *)
  Definition kind_to_Z (kind : Raw.ColumnKind.t) : Z :=
    match kind with
    | Raw.ColumnKind.Advice => 0
    | Raw.ColumnKind.Fixed => 1
    | Raw.ColumnKind.Instance_ => 2
    end.

  Definition entry_key (entry : Raw.Cell.t * Z) : Z :=
    let '(cell, value) := entry in
    (((kind_to_Z cell.(Raw.Cell.column).(Raw.ColumnRef.kind)) * (2 ^ 40)
        + cell.(Raw.Cell.column).(Raw.ColumnRef.index)) * (2 ^ 40)
      + cell.(Raw.Cell.row)) * (2 ^ 256)
      + value.

  Fixpoint insert_sorted (key : Z) (keys : list Z) : list Z :=
    match keys with
    | [] => [key]
    | key' :: keys' =>
        if key <=? key'
        then key :: keys
        else key' :: insert_sorted key keys'
    end.

  Fixpoint sort_keys (keys : list Z) : list Z :=
    match keys with
    | [] => []
    | key :: keys' => insert_sorted key (sort_keys keys')
    end.

  Definition emitted : list Z :=
    sort_keys
      (List.map entry_key
        (snd
          (layouter_constants
            Index.indices
            Garden.Orchard.circuit_synthesis_layout.region_start_of
            Garden.Orchard.circuit.synthesize))).

  Definition expected : list Z :=
    sort_keys
      (List.map
        (fun entry =>
          entry_key
            (Garden.Orchard.circuit_synthesis_constants.advice_cell
              entry.(Garden.Orchard.circuit_synthesis_constants
                .ConstantCopy.advice_column)
              entry.(Garden.Orchard.circuit_synthesis_constants
                .ConstantCopy.advice_row),
            entry.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.value)))
        Garden.Orchard.circuit_synthesis_constants.constant_copies).

  (* The certificate: 166 pinned cells on each side, equal as multisets. *)
  Lemma constant_copies_certificate : emitted = expected.
  Proof. vm_compute. reflexivity. Qed.
End ConstantsCheck.
