From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.

Require Import Garden.Halo2.Synthesis.
Require Garden.Orchard.circuit.
Require Garden.Orchard.columns.

Extraction Language OCaml.
Set Extraction Output Directory "_build/orchard_synthesis_json".

Extract Constant PrimString.string => "Pstring.t".

Definition schema : PrimString.string :=
  "orchard.action_circuit.synthesis.v1".

Definition source : PrimString.string :=
  "Garden.Orchard.circuit.synthesize_events".

Definition model_events : list Raw.Event.t :=
  Garden.Orchard.circuit.synthesize_events
    Garden.Orchard.columns.Index.indices.

Extraction "orchard_synthesis_model.ml"
  schema
  source
  model_events.
