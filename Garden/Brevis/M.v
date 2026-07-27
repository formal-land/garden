Require Import Garden.Plonky3.M.
Require Import Garden.Field.Field.

(** Additional primitives for Brevis *)

(** The lookups are axiomatized *)
Parameter looking : forall {M : Set}, M -> M.t unit.
Parameter looked : forall {M : Set}, M -> M.t unit.
