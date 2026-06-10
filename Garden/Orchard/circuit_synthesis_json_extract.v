From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.

Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Garden.Orchard.circuit.
Require Garden.Orchard.columns.

Extraction Language OCaml.
Set Extraction Output Directory "_build/orchard_synthesis_json".

Extract Constant PrimString.string => "Pstring.t".

Definition configure_schema : PrimString.string :=
  "orchard.action_circuit.configure.v1".

Definition configure_source : PrimString.string :=
  "Garden.Orchard.circuit.configure".

Definition model_configure : ConstraintSystem.t Configure.indexed_columns :=
  Configure.to_indexed
    Garden.Orchard.columns.Index.indices
    (Garden.Orchard.circuit.configure
      (@ConstraintSystem.empty Garden.Orchard.columns.columns)).

Definition synthesis_schema : PrimString.string :=
  "orchard.action_circuit.synthesis.v1".

Definition synthesis_source : PrimString.string :=
  "Garden.Orchard.circuit.synthesize_events".

Definition model_synthesis_events : list Raw.Event.t :=
  Garden.Orchard.circuit.synthesize_events
    Garden.Orchard.columns.Index.indices.

Extraction "orchard_synthesis_model.ml"
  configure_schema
  configure_source
  model_configure
  synthesis_schema
  synthesis_source
  model_synthesis_events.
