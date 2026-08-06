From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.

Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.high_level_trace.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Orchard.circuit.
Require Garden.Orchard.columns.
Require Import Garden.Orchard.compiled.configuration.
Require Garden.Orchard.circuit_synthesis_layout.

Extraction Language OCaml.
Set Extraction Output Directory "_build/orchard_synthesis_json".

Extract Constant PrimString.string => "Pstring.t".

Definition model_configure : ConstraintSystem.t Configure.indexed_columns :=
  Configure.to_indexed
    Garden.Orchard.columns.Index.indices
    (𝓒.run_unit
      Garden.Orchard.circuit.configure
      (@ConstraintSystem.empty Garden.Orchard.columns.columns)).

Definition model_synthesis_events : list Raw.Event.t :=
  Garden.Orchard.circuit.synthesize_events
    Garden.Orchard.columns.Index.indices.

(** The structural traces are separate from [model_synthesis_events]: they
    retain semantic constraints, namespace nesting, relative region cells,
    and inline [ConstrainConstant] operations, while the operational event
    artifact and its parity schema remain unchanged. *)
Definition model_configure_trace : list HighLevelTrace.ConfigureOp.t :=
  snd
    (HighLevelTrace.eval_configure
      Garden.Orchard.columns.Index.indices
      Garden.Orchard.circuit.configure).

(** Builder metadata used by key generation, interpreted from the same
    configure program.  Its JSON view is compared externally with Halo 2's
    implementation snapshot; the closed Rocq compilation certificate does
    not trust that comparison. *)
Definition model_configure_metadata : Metadata.State.t :=
  OrchardConfigure.state.

Definition model_layout_trace : list HighLevelTrace.LayoutNode.t :=
  snd
    (HighLevelTrace.eval_layouter
      Garden.Orchard.columns.Index.indices
      Garden.Orchard.circuit_synthesis_layout.region_index_of
      Garden.Orchard.circuit_synthesis_layout.region_start_of
      Garden.Orchard.circuit.synthesize).

Extraction "orchard_synthesis_model.ml"
  model_configure
  model_configure_metadata
  model_synthesis_events
  model_configure_trace
  model_layout_trace.
