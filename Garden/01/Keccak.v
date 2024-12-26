Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import ListNotations.

Module Sponges.
    Parameter t : Set.
End Sponges.

Module Steps.
    Inductive t : Set :=
    | Round (n : Z)
    | Sponge (s : Sponges.t)
    .
End Steps.

Module Variable_.
    Parameter t : Set.

    Parameter add : t -> t -> t.
    Parameter mul : t -> t -> t.
    Parameter sub : t -> t -> t.
    Parameter one : t.
    Parameter zero : t.
End Variable_.

Module Keccak.
    Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)).
    Admitted.
End Keccak.