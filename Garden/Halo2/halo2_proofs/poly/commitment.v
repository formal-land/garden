(** * IPA parameters and MSM, specialized to Vesta

    Transcription of [halo2_proofs/src/poly/commitment.rs] ([Params],
    [commit_lagrange], [empty_msm]) and [commitment/msm.rs] ([MSM] terms,
    [append_term], [scale], [eval]). The [other] map is a list of
    [(x, y, scalar)] terms keyed by affine [x], matching the B-tree
    accumulation (matching [y] adds scalars; the negation of [y]
    subtracts). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.arithmetic.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Params.
  Record t : Set := {
    k : u32;
    n : u64;
    g : list VestaCurve.point;
    g_lagrange : list VestaCurve.point;
    w : VestaCurve.point;
    u : VestaCurve.point;
  }.
End Params.

Module OtherTerm.
  Record t : Set := {
    x : Z;
    y : Z;
    scalar : Z;
  }.
End OtherTerm.

Module MSM.

  Record t : Set := {
    params : Params.t;
    g_scalars : option (list Z);
    w_scalar : option Z;
    u_scalar : option Z;
    other : list OtherTerm.t;
  }.

  Definition new (params : Params.t) : t := {|
    MSM.params := params;
    g_scalars := None;
    w_scalar := None;
    u_scalar := None;
    other := [];
  |}.

  Fixpoint add_other (terms : list OtherTerm.t) (x y s : Z) : list OtherTerm.t :=
    match terms with
    | [] => [{| OtherTerm.x := x; OtherTerm.y := y; OtherTerm.scalar := s |}]
    | tm :: rest =>
      if Fq.from tm.(OtherTerm.x)
           =? Fq.from x then
        if Fq.from tm.(OtherTerm.y)
             =? Fq.from y then
          {| OtherTerm.x := tm.(OtherTerm.x);
             OtherTerm.y := tm.(OtherTerm.y);
             OtherTerm.scalar := tm.(OtherTerm.scalar) +s s |} :: rest
        else
          {| OtherTerm.x := tm.(OtherTerm.x);
             OtherTerm.y := tm.(OtherTerm.y);
             OtherTerm.scalar := tm.(OtherTerm.scalar) -s s |} :: rest
      else
        tm :: add_other rest x y s
    end.

  Definition append_term (msm : t) (scalar : Z) (point : VestaCurve.point) : t :=
    match VestaEncoding.coordinates point with
    | None => msm
    | Some (x, y) =>
      {| params := msm.(params);
         g_scalars := msm.(g_scalars);
         w_scalar := msm.(w_scalar);
         u_scalar := msm.(u_scalar);
         other := add_other msm.(other) x y scalar |}
    end.

  Definition add_constant_term (msm : t) (constant : Z) : t :=
    match msm.(g_scalars) with
    | Some gs =>
      match gs with
      | [] => msm
      | g0 :: rest =>
        {| params := msm.(params);
           g_scalars := Some ((g0 +s constant) :: rest);
           w_scalar := msm.(w_scalar);
           u_scalar := msm.(u_scalar);
           other := msm.(other) |}
      end
    | None =>
      let n := Integer.to_nat msm.(params).(Params.n) in
      {| params := msm.(params);
         g_scalars := Some (constant :: List.repeat 0 (Nat.pred n));
         w_scalar := msm.(w_scalar);
         u_scalar := msm.(u_scalar);
         other := msm.(other) |}
    end.

  Fixpoint zip_add (a b : list Z) : list Z :=
    match a, b with
    | x :: a, y :: b => (x +s y) :: zip_add a b
    | _, _ => a
    end.

  Definition add_to_g_scalars (msm : t) (scalars : list Z) : t :=
    match msm.(g_scalars) with
    | Some gs =>
      {| params := msm.(params);
         g_scalars := Some (zip_add gs scalars);
         w_scalar := msm.(w_scalar);
         u_scalar := msm.(u_scalar);
         other := msm.(other) |}
    | None =>
      {| params := msm.(params);
         g_scalars := Some scalars;
         w_scalar := msm.(w_scalar);
         u_scalar := msm.(u_scalar);
         other := msm.(other) |}
    end.

  Definition add_to_w_scalar (msm : t) (scalar : Z) : t :=
    {| params := msm.(params);
       g_scalars := msm.(g_scalars);
       w_scalar :=
         match msm.(w_scalar) with
         | Some a => Some (a +s scalar)
         | None => Some scalar
         end;
       u_scalar := msm.(u_scalar);
       other := msm.(other) |}.

  Definition add_to_u_scalar (msm : t) (scalar : Z) : t :=
    {| params := msm.(params);
       g_scalars := msm.(g_scalars);
       w_scalar := msm.(w_scalar);
       u_scalar :=
         match msm.(u_scalar) with
         | Some a => Some (a +s scalar)
         | None => Some scalar
         end;
       other := msm.(other) |}.

  Definition add_msm (msm other : t) : t :=
    let msm :=
      List.fold_left
        (fun msm tm =>
          append_term msm tm.(OtherTerm.scalar)
            (VestaCurve.Affine tm.(OtherTerm.x) tm.(OtherTerm.y)))
        other.(MSM.other) msm in
    let msm :=
      match other.(g_scalars) with
      | Some gs => add_to_g_scalars msm gs
      | None => msm
      end in
    let msm :=
      match other.(w_scalar) with
      | Some s => add_to_w_scalar msm s
      | None => msm
      end in
    match other.(u_scalar) with
    | Some s => add_to_u_scalar msm s
    | None => msm
    end.

  Definition scale (msm : t) (factor : Z) : t :=
    {| params := msm.(params);
       g_scalars :=
         match msm.(g_scalars) with
         | Some gs => Some (List.map (fun g => g *s factor) gs)
         | None => None
         end;
       w_scalar :=
         match msm.(w_scalar) with
         | Some a => Some (a *s factor)
         | None => None
         end;
       u_scalar :=
         match msm.(u_scalar) with
         | Some a => Some (a *s factor)
         | None => None
         end;
       other :=
         List.map (fun tm =>
           {| OtherTerm.x := tm.(OtherTerm.x);
              OtherTerm.y := tm.(OtherTerm.y);
              OtherTerm.scalar := tm.(OtherTerm.scalar) *s factor |})
           msm.(other) |}.

  Definition eval (msm : t) : bool :=
    let '(scalars, bases) :=
      let others :=
        List.map (fun tm =>
          (tm.(OtherTerm.scalar), VestaCurve.Affine tm.(OtherTerm.x) tm.(OtherTerm.y)))
          msm.(other) in
      let wu :=
        match msm.(w_scalar) with
        | Some s => [(s, msm.(params).(Params.w))]
        | None => []
        end ++
        match msm.(u_scalar) with
        | Some s => [(s, msm.(params).(Params.u))]
        | None => []
        end in
      let gs :=
        match msm.(g_scalars) with
        | Some gs => List.combine gs msm.(params).(Params.g)
        | None => []
        end in
      let all := others ++ wu ++ gs in
      (List.map fst all, List.map snd all) in
    VestaEncoding.is_identity (Arithmetic.best_multiexp scalars bases).
End MSM.

Definition empty_msm (params : Params.t) : MSM.t := MSM.new params.

Definition commit_lagrange (params : Params.t) (values : list Z) (blind : Z) : VestaCurve.point :=
  Arithmetic.best_multiexp
    (values ++ [blind])
    (params.(Params.g_lagrange) ++ [params.(Params.w)]).
