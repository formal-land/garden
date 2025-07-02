(** * Here we give a manual definition of the adder circuit. *)
Require Import Garden.Garden.

(** ** Circuit constraints *)

(*
  (input ST u32)
  (input CT u4)
  (input CT_MAX u3)
  (input BYTE_1 u8)
  (input BYTE_2 u8)
  (input BYTE_R u8)
  (input ACC_1 u64)
  (input ACC_2 u64)
  (input ACC_R u65)
  (input ARG_1 u64)
  (input ARG_2 u64)
  (input RES u65)
*)
Record t : Set := {
  ST : Z;
  CT : Z;
  CT_MAX : Z;
  BYTE_1 : Z;
  BYTE_2 : Z;
  BYTE_R : Z;
  ACC_1 : Z;
  ACC_2 : Z;
  ACC_R : Z;
  ARG_1 : Z;
  ARG_2 : Z;
  RES : Z;
}.

(*
  (range BYTE_1 u8)
  (range BYTE_2 u8)
  (range BYTE_R u8)
*)
Module Range.
  Record t (self : t) : Prop := {
    BYTE_1 : 0 <= self.(BYTE_1) < 256;
    BYTE_2 : 0 <= self.(BYTE_2) < 256;
    BYTE_R : 0 <= self.(BYTE_R) < 256;
  }.
End Range.

(*
(vanish (increment)
   (∨ (== ST (shift ST 1)) (==
      (+ 1 ST) (shift ST 1))))
*)
Definition increment (local next : t) : Prop :=
  next.(ST) = local.(ST) \/
  next.(ST) = local.(ST) + 1.

(*
(vanish (upper-bound) (!= 8 CT))
*)
Definition upper_bound (local next : t) : Prop :=
  next.(CT) <> 8.

(*
(vanish (reset) 
   (∨ (== ST (shift ST 1)) (== (shift CT 1) 0)))
*)
Definition reset (local next : t) : Prop :=
  next.(ST) = local.(ST) \/
  next.(CT) = 0.

(*
(vanish (heartbeat) (ite (== ST 0) _ (ite (== CT CT_MAX) (== (shift ST 1) 
   (+ 1 ST)) (== 
   (+ 1 CT) (shift CT 1)))))
*)
Definition heartbeat (local next : t) : Prop :=
  if local.(ST) =? 0 then
    True
  else if local.(CT) =? local.(CT_MAX) then
    next.(ST) = local.(ST) + 1
  else
    next.(CT) = local.(CT) + 1.

(*
(vanish (byte_decompositions) 
   (∧ (ite (== CT 0) (== ACC_1 BYTE_1) (== ACC_1 
      (+ 
         ( * 256 (shift ACC_1 -1)) BYTE_1))) (ite (== CT 0) (== ACC_2 BYTE_2) (== ACC_2 
      (+ 
         ( * 256 (shift ACC_2 -1)) BYTE_2))) (ite (== CT 0) (== ACC_R BYTE_R) (== ACC_R 
      (+ 
         ( * 256 (shift ACC_R -1)) BYTE_R)))))
*)
Definition byte_decompositions (local next : t) : Prop :=
  (
    if next.(CT) =? 0 then
      next.(ACC_1) = next.(BYTE_1)
    else
      next.(ACC_1) = next.(BYTE_1) + (256 * local.(ACC_1))
  ) /\ (
    if next.(CT) =? 0 then
      next.(ACC_2) = next.(BYTE_2)
    else
      next.(ACC_2) = next.(BYTE_2) + (256 * local.(ACC_2))
  ) /\ (
    if next.(CT) =? 0 then
      next.(ACC_R) = next.(BYTE_R)
    else
      next.(ACC_R) = next.(BYTE_R) + (256 * local.(ACC_R))
  ).

(*
(vanish (counter-constancies) 
   (∧
      (ite (!= CT 0) (== ARG_1 (shift ARG_1 -1)))
      (ite (!= CT 0) (== ARG_2 (shift ARG_2 -1)))
      (ite (!= CT 0) (== RES (shift RES -1)))
      (ite (!= CT 0) (== CT_MAX (shift CT_MAX -1)))))
*)
Definition counter_constancies (local next : t) : Prop :=
  (
    if negb (next.(CT) =? 0) then
      next.(ARG_1) = local.(ARG_1)
    else
      True
  ) /\ (
    if negb (next.(CT) =? 0) then
      next.(ARG_2) = local.(ARG_2)
    else
      True
  ) /\ (
    if negb (next.(CT) =? 0) then
      next.(RES) = local.(RES)
    else
      True
  ) /\ (
    if negb (next.(CT) =? 0) then
      next.(CT_MAX) = local.(CT_MAX)
    else
      True
  ).

(*
(vanish (target-constraints) (ite (== ST 0) _ (ite (== CT CT_MAX) 
   (∧ (== ARG_1 ACC_1) (== ARG_2 ACC_2) (== RES ACC_R)))))
*)
Definition target_constraints (self : t) : Prop :=
  if self.(ST) =? 0 then
    True
  else if self.(CT) =? self.(CT_MAX) then
    self.(ARG_1) = self.(ACC_1) /\
    self.(ARG_2) = self.(ACC_2) /\
    self.(RES) = self.(ACC_R)
  else
    True.

(*
(vanish (adder) (ite (== ST 0) _ (== RES 
   (+ ARG_1 ARG_2))))
*)
Definition adder (self : t) : Prop :=
  if self.(ST) =? 0 then
    True
  else
    self.(RES) = self.(ARG_1) + self.(ARG_2).

(** ** Specification *)
(*
Definition step_in_frame (local : t) : t :=
  {|
    ST := local.(ST);
    CT := local.(CT) + 1;
    CT_MAX := local.(CT_MAX);
    BYTE_1 := local.(BYTE_1);
    BYTE_2 := local.(BYTE_2);
    BYTE_R := local.(BYTE_R);
    ACC_1 := local.(ACC_1);
    ACC_2 := local.(ACC_2);
    ACC_R := local.(ACC_R);
    ARG_1 := local.(ARG_1);
    ARG_2 := local.(ARG_2);
    RES := local.(RES);
  |}
*)
