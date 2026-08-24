(** * OCaml evaluation entry point for Orchard verifier snapshots

    The verifier, replay, and normalization functions remain Rocq definitions.
    This file only extracts two closed evaluation wrappers after Rocq VM
    reduction proved too slow for the valid proof cases and this Rocq build
    reported native reduction as disabled. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt
  ExtrOcamlZBigInt.
From Stdlib Require Import ExtrOCamlInt63 ExtrOCamlPArray ExtrOCamlPString.
Require Import Garden.Orchard.Verifier.Snapshots.Generated.
Require Import Garden.Orchard.Verifier.Snapshots.Replay.

Extraction Language OCaml.
Set Extraction Output Directory "_build/orchard_verifier_replay".
Set Extraction Optimize.
Set Extraction AutoInline.
Extraction NoInline PrimArray.array.

(** These rocq-of-rust metadata types do not occur in the verifier result.
    Extraction may nevertheless retain their definitions through the integer
    facade, so give their erased runtime representatives explicitly. *)
Extract Constant RocqOfRust.M.Ty.t => "unit".
Extract Constant RocqOfRust.M.Ty.path => "(fun _ -> ())".

Module OrchardVerifierSnapshotExtract.
  (** Direct indexing avoids constructing the other 39 results when timing a
      single case. *)
  Definition run_case (index : nat) : bool :=
    OrchardVerifierSnapshotReplay.case_matches_at index.

  (** Construct the vector only when [run_all] is called.  Referencing Replay's
      closed [case_match_vector] here would make OCaml evaluate every verifier
      case eagerly while initializing the extracted module, including for
      [run_case]. *)
  Definition run_all (_ : unit) : list bool * bool :=
    let vector :=
      List.map OrchardVerifierSnapshotReplay.case_matchesb
        OrchardVerifierGeneratedSnapshots.cases in
    (vector, List.forallb (fun matched => matched) vector).

End OrchardVerifierSnapshotExtract.

Extraction "orchard_verifier_replay.ml"
  OrchardVerifierSnapshotExtract.run_case
  OrchardVerifierSnapshotExtract.run_all.
