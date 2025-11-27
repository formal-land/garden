Require Import Garden.Plonky3.M.

(** Additional primitives for Brevis *)

(** For now, we axiomatize the lookups *)
Parameter looking : forall {M : Set}, M -> M.t unit.
Parameter looked : forall {M : Set}, M -> M.t unit.
