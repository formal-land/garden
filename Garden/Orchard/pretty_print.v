Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.Printer.
Require Import Garden.Orchard.circuit.main.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition print_orchard_action_circuit : string :=
  PrettyPrint.cats [
    PrettyPrint.endl;
    PrettyPrint.to_string action_circuit 0;
    PrettyPrint.endl
  ].

Compute print_orchard_action_circuit.
