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
Module Row.
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
End Row.

(*
  (range BYTE_1 u8)
  (range BYTE_2 u8)
  (range BYTE_R u8)
*)
Module Range.
  Record t (self : Row.t) : Prop := {
    BYTE_1 : 0 <= self.(Row.BYTE_1) < 256;
    BYTE_2 : 0 <= self.(Row.BYTE_2) < 256;
    BYTE_R : 0 <= self.(Row.BYTE_R) < 256;
  }.
End Range.

(* (vanish (first:first) (== ST 0)) *)
Definition first (self : Row.t) : Prop :=
  self.(Row.ST) = 0.

(* (vanish (last:last) (ite (== ST 0) _ (== CT CT_MAX))) *)
Definition last (self : Row.t) : Prop :=
  if self.(Row.ST) =? 0 then
    True
  else
    self.(Row.CT) = self.(Row.CT_MAX).

(*
(vanish (increment)
   (∨ (== ST (shift ST 1)) (==
      (+ 1 ST) (shift ST 1))))
*)
Definition increment (local next : Row.t) : Prop :=
  next.(Row.ST) = local.(Row.ST) \/
  next.(Row.ST) = local.(Row.ST) + 1.

(*
(vanish (upper-bound) (!= 8 CT))
*)
Definition upper_bound (local next : Row.t) : Prop :=
  next.(Row.CT) <> 8.

(*
(vanish (reset) 
   (∨ (== ST (shift ST 1)) (== (shift CT 1) 0)))
*)
Definition reset (local next : Row.t) : Prop :=
  next.(Row.ST) = local.(Row.ST) \/
  next.(Row.CT) = 0.

(*
(vanish (heartbeat) (ite (== ST 0) _ (ite (== CT CT_MAX) (== (shift ST 1) 
   (+ 1 ST)) (== 
   (+ 1 CT) (shift CT 1)))))
*)
Definition heartbeat (local next : Row.t) : Prop :=
  if local.(Row.ST) =? 0 then
    True
  else if local.(Row.CT) =? local.(Row.CT_MAX) then
    next.(Row.ST) = local.(Row.ST) + 1
  else
    next.(Row.CT) = local.(Row.CT) + 1.

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
Definition byte_decompositions (local next : Row.t) : Prop :=
  (
    if next.(Row.CT) =? 0 then
      next.(Row.ACC_1) = next.(Row.BYTE_1)
    else
      next.(Row.ACC_1) = next.(Row.BYTE_1) + (256 * local.(Row.ACC_1))
  ) /\ (
    if next.(Row.CT) =? 0 then
      next.(Row.ACC_2) = next.(Row.BYTE_2)
    else
      next.(Row.ACC_2) = next.(Row.BYTE_2) + (256 * local.(Row.ACC_2))
  ) /\ (
    if next.(Row.CT) =? 0 then
      next.(Row.ACC_R) = next.(Row.BYTE_R)
    else
      next.(Row.ACC_R) = next.(Row.BYTE_R) + (256 * local.(Row.ACC_R))
  ).

(*
(vanish (counter-constancies) 
   (∧
      (ite (!= CT 0) (== ARG_1 (shift ARG_1 -1)))
      (ite (!= CT 0) (== ARG_2 (shift ARG_2 -1)))
      (ite (!= CT 0) (== RES (shift RES -1)))
      (ite (!= CT 0) (== CT_MAX (shift CT_MAX -1)))))
*)
Definition counter_constancies (local next : Row.t) : Prop :=
  (
    if negb (next.(Row.CT) =? 0) then
      next.(Row.ARG_1) = local.(Row.ARG_1)
    else
      True
  ) /\ (
    if negb (next.(Row.CT) =? 0) then
      next.(Row.ARG_2) = local.(Row.ARG_2)
    else
      True
  ) /\ (
    if negb (next.(Row.CT) =? 0) then
      next.(Row.RES) = local.(Row.RES)
    else
      True
  ) /\ (
    if negb (next.(Row.CT) =? 0) then
      next.(Row.CT_MAX) = local.(Row.CT_MAX)
    else
      True
  ).

(*
(vanish (target-constraints) (ite (== ST 0) _ (ite (== CT CT_MAX) 
   (∧ (== ARG_1 ACC_1) (== ARG_2 ACC_2) (== RES ACC_R)))))
*)
Definition target_constraints (self : Row.t) : Prop :=
  if self.(Row.ST) =? 0 then
    True
  else if self.(Row.CT) =? self.(Row.CT_MAX) then
    self.(Row.ARG_1) = self.(Row.ACC_1) /\
    self.(Row.ARG_2) = self.(Row.ACC_2) /\
    self.(Row.RES) = self.(Row.ACC_R)
  else
    True.

(*
(vanish (adder) (ite (== ST 0) _ (== RES 
   (+ ARG_1 ARG_2))))
*)
Definition adder (self : Row.t) : Prop :=
  if self.(Row.ST) =? 0 then
    True
  else
    self.(Row.RES) = self.(Row.ARG_1) + self.(Row.ARG_2).

Module Generate.
  (** Specify the constraints on the next row, or an explicit marker for the end of the matrix. *)
  Record t {current : list Row.t} {next : option Row.t} : Prop := {
    range :
      match next with
      | Some next => Range.t next
      | None => True
      end;
    first :
      match current, next with
      | [], Some next => first next
      | _, _ => True
      end;
    last :
      match current, next with
      | local :: _, None => last local
      | _, _ => True
      end;
    increment :
      match current, next with
      | local :: _, Some next => increment local next
      | _, _ => True
      end;
    upper_bound :
      match current, next with
      | local :: _, Some next => upper_bound local next
      | _, _ => True
      end;
    reset :
      match current, next with
      | local :: _, Some next => reset local next
      | _, _ => True
      end;
    heartbeat :
      match current, next with
      | local :: _, Some next => heartbeat local next
      | _, _ => True
      end;
    byte_decompositions :
      match current, next with
      | local :: _, Some next => byte_decompositions local next
      | _, _ => True
      end;
    counter_constancies :
      match current, next with
      | local :: _, Some next => counter_constancies local next
      | _, _ => True
      end;
    target_constraints :
      match next with
      | Some next => target_constraints next
      | None => True
      end;
    adder :
      match next with
      | Some next => adder next
      | None => True
      end;
  }.
  Arguments t : clear implicits.
End Generate.

Module Matrix.
  Definition t : Set :=
    list Row.t.

  Module Valid.
    Fixpoint aux (current : list Row.t) (next : option Row.t) : Prop :=
      Generate.t current next /\
      match current with
      | local :: rest => aux rest (Some local)
      | [] => True
      end.

    Definition t (self : t) : Prop :=
      aux self None.
  End Valid.
End Matrix.

Module GenerateList.
  Fixpoint t (current : list Row.t) (nexts : list Row.t) : Prop :=
    match nexts with
    | [] => True
    | next :: nexts =>
      Generate.t current (Some next) /\
      t (next :: current) nexts
    end.
End GenerateList.

Module Function.
  (** [heartbeat] and [reset] to update [ST] and [CT] *)
  Definition heartbeat_reset (local next : Row.t) : Row.t :=
    if local.(Row.CT) =? local.(Row.CT_MAX) then
      next
        <| Row.ST := local.(Row.ST) + 1 |>
        <| Row.CT := 0 |>
    else
      next
        <| Row.ST := local.(Row.ST) |>
        <| Row.CT := local.(Row.CT) + 1 |>.

  Lemma heartbeat_reset_is_valid local rest next
      (H_ST :local.(Row.ST) <> 0)
      (H_CT : local.(Row.CT) >= 0)
      (H_generate : Generate.t (local :: rest) (Some next)) :
    next = heartbeat_reset local next.
  Proof.
    destruct H_generate.
    unfold heartbeat_reset.
    unfold reset, heartbeat in *.
    destruct (local.(Row.ST) =? 0) eqn:?; [lia|].
    destruct (local.(Row.CT) =? local.(Row.CT_MAX)).
    { destruct reset0; [lia|].
      hauto lq: on.
    }
    { destruct reset0; [|lia].
      hauto lq: on.
    }
  Qed.

  Definition counter_constancies (local next : Row.t) : Row.t :=
    next
      <| Row.ARG_1 := local.(Row.ARG_1) |>
      <| Row.ARG_2 := local.(Row.ARG_2) |>
      <| Row.RES := local.(Row.RES) |>
      <| Row.CT_MAX := local.(Row.CT_MAX) |>.

  Lemma counter_constancies_is_valid local rest next
      (H_CT :next.(Row.CT) <> 0)
      (H_generate : Generate.t (local :: rest) (Some next)) :
    next = counter_constancies local next.
  Proof.
    destruct H_generate.
    unfold counter_constancies.
    unfold adder.counter_constancies in *.
    qauto l: on.
  Qed.

  (* Fixpoint generate_cycle (CT_MAX_fuel : nat) (local : Row.t) : list (Row.t -> Row.t) :=
    match CT_MAX_fuel with
    | O => []
    | S CT_MAX_fuel =>
      (fun next =>
        next
          <| Row.ST := local.(Row.ST) |>
          <| Row.CT := local.(Row.CT_MAX) - Z.of_nat CT_MAX_fuel + 1 |>
          <| Row.ARG_1 := local.(Row.ARG_1) |>
          <| Row.ARG_2 := local.(Row.ARG_2) |>
          <| Row.RES := local.(Row.RES) |>
          <| Row.CT_MAX := local.(Row.CT_MAX) |>
      ) ::
      generate_cycle CT_MAX_fuel local
    end.

  Lemma generate_cycle_is_valid local current nexts (CT_MAX : nat)
    (H_CT_MAX : local.(Row.CT_MAX) = Z.of_nat CT_MAX)
    (H_length : List.Forall2 (fun _ _ => True) nexts (generate_cycle CT_MAX local))
    (H_generate_list : GenerateList.t (local :: current) nexts) :
    List.Forall2 (fun next f => f next = next) nexts (generate_cycle CT_MAX local).
  Proof.
    induction CT_MAX; cbn in *.
    { inversion H_length.
      constructor.
    }
    { inversion H_length as [|next ? nexts'].
      replace nexts with (next :: nexts') in * by congruence.
      cbn in *.
      constructor.
      {

      }
    }
    intros.
    destruct H_generate_list.
    constructor.
    { apply heartbeat_reset_is_valid; auto.
    }
    { apply counter_constancies_is_valid; auto.
    } *)
  (* Definition next_ST_CT (ST CT : Z) : Z * Z :=
    if ST =? 0 then
      (0, CT)
    else if CT =? CT_MAX then *)
End Function.

(* Definition next_ST_CT (ST CT : Z) : Z * Z := *)


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
