(** * Halo2 polynomial-commitment MSM

    This module mirrors [poly/commitment/msm.rs].  The [other] map is an
    explicitly x-sorted list.  Points with the same x-coordinate and equal y
    add coefficients; points with opposite y subtract coefficients; any other
    same-x pair is a Rust assertion panic.  Identity points are ignored, while
    zero coefficients remain present just as they do in the Rust [BTreeMap]. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.Halo2.Verifier.Algebra.

Import ListNotations.
Local Open Scope Z_scope.

Module CommitmentVerifier.

Module F := VerifierField.

Definition point : Type := Vesta.point.
Definition identity : point := Vesta.identity.

Definition base_canon (x : Z) : Z := x mod Primes.pallas_q.

Definition coordinates (value : point) : option (Z * Z) :=
  match value with
  | Weierstrass.Infinity => None
  | Weierstrass.Affine x y => Some (base_canon x, base_canon y)
  end.

Record other_term : Type := {
  term_x : Z;
  term_scalar : F.t;
  term_y : Z;
}.

Record msm : Type := {
  params_n : nat;
  g_scalars : option (list F.t);
  w_scalar : option F.t;
  u_scalar : option F.t;
  other : list other_term;
}.

Inductive msm_panic : Type :=
| InconsistentSameXPoint (x existing_y new_y : Z)
| GeneratorScalarLengthMismatch (expected actual : nat).

Inductive msm_result : Type :=
| MsmOk (value : msm)
| MsmPanicked (failure : msm_panic).

Definition empty (n : nat) : msm := {|
  params_n := n;
  g_scalars := None;
  w_scalar := None;
  u_scalar := None;
  other := [];
|}.

Definition option_add (left right : option F.t) : option F.t :=
  match left, right with
  | None, None => None
  | Some x, None | None, Some x => Some x
  | Some x, Some y => Some (F.add x y)
  end.

Definition option_scale (factor : F.t) (value : option F.t) : option F.t :=
  match value with None => None | Some x => Some (F.mul x factor) end.

Fixpoint insert_other (new_term : other_term) (terms : list other_term) :
    msm_result :=
  match terms with
  | [] =>
      MsmOk {| params_n := 0; g_scalars := None; w_scalar := None;
               u_scalar := None; other := [new_term] |}
  | current :: tail =>
      if Z.eqb new_term.(term_x) current.(term_x) then
        if Z.eqb new_term.(term_y) current.(term_y) then
          MsmOk {| params_n := 0; g_scalars := None; w_scalar := None;
                   u_scalar := None;
                   other :=
                     {| term_x := current.(term_x);
                        term_scalar := F.add current.(term_scalar)
                          new_term.(term_scalar);
                        term_y := current.(term_y) |} :: tail |}
        else if Z.eqb current.(term_y) (base_canon (- new_term.(term_y))) then
          MsmOk {| params_n := 0; g_scalars := None; w_scalar := None;
                   u_scalar := None;
                   other :=
                     {| term_x := current.(term_x);
                        term_scalar := F.sub current.(term_scalar)
                          new_term.(term_scalar);
                        term_y := current.(term_y) |} :: tail |}
        else MsmPanicked (InconsistentSameXPoint current.(term_x)
          current.(term_y) new_term.(term_y))
      else if Z.ltb new_term.(term_x) current.(term_x) then
        MsmOk {| params_n := 0; g_scalars := None; w_scalar := None;
                 u_scalar := None; other := new_term :: terms |}
      else
        match insert_other new_term tail with
        | MsmPanicked failure => MsmPanicked failure
        | MsmOk inserted =>
            MsmOk {| params_n := 0; g_scalars := None; w_scalar := None;
                     u_scalar := None; other := current :: inserted.(other) |}
        end
  end.

Definition with_other (state : msm) (terms : list other_term) : msm := {|
  params_n := state.(params_n);
  g_scalars := state.(g_scalars);
  w_scalar := state.(w_scalar);
  u_scalar := state.(u_scalar);
  other := terms;
|}.

Definition append_coordinates (scalar x y : Z) (state : msm) : msm_result :=
  let term := {| term_x := base_canon x; term_scalar := F.canon scalar;
                 term_y := base_canon y |} in
  match insert_other term state.(other) with
  | MsmPanicked failure => MsmPanicked failure
  | MsmOk inserted => MsmOk (with_other state inserted.(other))
  end.

Definition append_term (scalar : F.t) (value : point) (state : msm) : msm_result :=
  match coordinates value with
  | None => MsmOk state
  | Some (x, y) => append_coordinates scalar x y state
  end.

Fixpoint zip_add (left right : list F.t) : list F.t :=
  match left, right with
  | x :: xs, y :: ys => F.add x y :: zip_add xs ys
  | _, _ => []
  end.

Definition add_to_g_scalars (scalars : list F.t) (state : msm) : msm_result :=
  if Nat.eqb (List.length scalars) state.(params_n) then
    match state.(g_scalars) with
    | None => MsmOk {|
        params_n := state.(params_n); g_scalars := Some scalars;
        w_scalar := state.(w_scalar); u_scalar := state.(u_scalar);
        other := state.(other) |}
    | Some existing => MsmOk {|
        params_n := state.(params_n);
        g_scalars := Some (zip_add existing scalars);
        w_scalar := state.(w_scalar); u_scalar := state.(u_scalar);
        other := state.(other) |}
    end
  else MsmPanicked (GeneratorScalarLengthMismatch state.(params_n)
    (List.length scalars)).

Definition add_constant_term (constant : F.t) (state : msm) : msm_result :=
  let scalars :=
    match state.(g_scalars) with
    | None => F.repeat_scalar F.zero state.(params_n)
    | Some scalars => scalars
    end in
  match scalars with
  | [] => MsmPanicked (GeneratorScalarLengthMismatch state.(params_n) 0)
  | head :: tail => MsmOk {|
      params_n := state.(params_n);
      g_scalars := Some (F.add head constant :: tail);
      w_scalar := state.(w_scalar); u_scalar := state.(u_scalar);
      other := state.(other) |}
  end.

Definition add_to_w_scalar (scalar : F.t) (state : msm) : msm := {|
  params_n := state.(params_n); g_scalars := state.(g_scalars);
  w_scalar := option_add state.(w_scalar) (Some scalar);
  u_scalar := state.(u_scalar); other := state.(other);
|}.

Definition add_to_u_scalar (scalar : F.t) (state : msm) : msm := {|
  params_n := state.(params_n); g_scalars := state.(g_scalars);
  w_scalar := state.(w_scalar);
  u_scalar := option_add state.(u_scalar) (Some scalar);
  other := state.(other);
|}.

Definition scale (factor : F.t) (state : msm) : msm := {|
  params_n := state.(params_n);
  g_scalars :=
    match state.(g_scalars) with
    | None => None
    | Some scalars => Some (map (F.mul factor) scalars)
    end;
  w_scalar := option_scale factor state.(w_scalar);
  u_scalar := option_scale factor state.(u_scalar);
  other := map (fun term =>
    {| term_x := term.(term_x);
       term_scalar := F.mul term.(term_scalar) factor;
       term_y := term.(term_y) |}) state.(other);
|}.

Fixpoint add_other_terms (terms : list other_term) (state : msm) : msm_result :=
  match terms with
  | [] => MsmOk state
  | term :: terms' =>
      match append_coordinates term.(term_scalar) term.(term_x) term.(term_y) state with
      | MsmPanicked failure => MsmPanicked failure
      | MsmOk state' => add_other_terms terms' state'
      end
  end.

Definition add_msm (additional state : msm) : msm_result :=
  match add_other_terms additional.(other) state with
  | MsmPanicked failure => MsmPanicked failure
  | MsmOk state' =>
      let with_special := {|
        params_n := state'.(params_n);
        g_scalars := state'.(g_scalars);
        w_scalar := option_add state'.(w_scalar) additional.(w_scalar);
        u_scalar := option_add state'.(u_scalar) additional.(u_scalar);
        other := state'.(other) |} in
      match additional.(g_scalars) with
      | None => MsmOk with_special
      | Some scalars => add_to_g_scalars scalars with_special
      end
  end.

Record parameters : Type := {
  parameter_g : list point;
  parameter_w : point;
  parameter_u : point;
}.

Definition point_sum (points : list point) : point :=
  fold_left Vesta.add points Vesta.identity.

Definition terms_points (terms : list other_term) : list point :=
  map (fun term => Vesta.mul term.(term_scalar)
    (Vesta.affine term.(term_x) term.(term_y))) terms.

Definition optional_point (scalar : option F.t) (base : point) : list point :=
  match scalar with None => [] | Some value => [Vesta.mul value base] end.

Definition eval (params : parameters) (state : msm) : option bool :=
  match state.(g_scalars) with
  | Some scalars =>
      if Nat.eqb (List.length scalars) (List.length params.(parameter_g)) then
        Some (match point_sum
          (terms_points state.(other) ++
           optional_point state.(w_scalar) params.(parameter_w) ++
           optional_point state.(u_scalar) params.(parameter_u) ++
           map (fun pair => Vesta.mul (fst pair) (snd pair))
             (combine scalars params.(parameter_g))) with
          | Weierstrass.Infinity => true | _ => false end)
      else None
  | None => Some (match point_sum
      (terms_points state.(other) ++
       optional_point state.(w_scalar) params.(parameter_w) ++
       optional_point state.(u_scalar) params.(parameter_u)) with
      | Weierstrass.Infinity => true | _ => false end)
  end.

End CommitmentVerifier.
