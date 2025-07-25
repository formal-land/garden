(* Generated *)
Require Import Garden.LLZK.M.

Module Module_Line_3.
  Module NoConstraints.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : NoConstraints.t) (arg_fun_1 : Felt.t) : M.t unit :=
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t NoConstraints.t :=
      let* var_self : NoConstraints.t := M.CreateStruct in
      M.Pure var_self.
  End NoConstraints.
End Module_Line_3.

Module Module_Line_20.
  Definition global_add {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Felt.t :=
    let var_0 : Felt.t := BinOp.add arg_fun_0 arg_fun_1 in
    M.Pure var_0.

  Module Adder.
    Record t : Set := {
      sum : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Adder.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(Adder.sum) in
      let* var_1 : Felt.t := global_add arg_fun_1 arg_fun_2 in
      let* _ : unit := M.AssertEqual var_0 var_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Adder.t :=
      let* var_self : Adder.t := M.CreateStruct in
      let* var_0 : Felt.t := global_add arg_fun_0 arg_fun_1 in
      let* _ : unit := M.AssertEqual var_self.(Adder.sum) var_0 in
      M.Pure var_self.
  End Adder.
End Module_Line_20.

Module Module_Line_52.
  Definition global_add {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Felt.t :=
    let var_0 : Felt.t := BinOp.add arg_fun_0 arg_fun_1 in
    M.Pure var_0.

  Module Adder2.
    Record t : Set := {
      sum : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Adder2.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(Adder2.sum) in
      let* var_1 : Felt.t := global_add arg_fun_1 arg_fun_2 in
      let var_2 : Felt.t := BinOp.add var_1 var_1 in
      let* _ : unit := M.AssertEqual var_0 var_2 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Adder2.t :=
      let* var_self : Adder2.t := M.CreateStruct in
      let* var_0 : Felt.t := global_add arg_fun_0 arg_fun_1 in
      let* _ : unit := M.AssertEqual var_self.(Adder2.sum) var_0 in
      M.Pure var_self.
  End Adder2.
End Module_Line_52.

Module Module_Line_85.
  Module ComponentB.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ComponentB.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Array.t Felt.t [5]) : M.t unit :=
      let* _ : unit := M.AssertIn arg_fun_1 arg_fun_2 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Array.t Felt.t [5]) : M.t ComponentB.t :=
      let* var_self : ComponentB.t := M.CreateStruct in
      M.Pure var_self.
  End ComponentB.
End Module_Line_85.

Module Module_Line_105.
  Module EnsureZero.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : EnsureZero.t) (arg_fun_1 : Felt.t) : M.t unit :=
      let var_felt_const_0 : Felt.t := UnOp.from 0 in
      let* _ : unit := M.AssertEqual arg_fun_1 var_felt_const_0 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t EnsureZero.t :=
      let* var_self : EnsureZero.t := M.CreateStruct in
      M.Pure var_self.
  End EnsureZero.

  Module EnsureBothZero.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : EnsureBothZero.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_felt_const_0 : Felt.t := UnOp.from 0 in
      let* _ : unit := M.AssertEqual arg_fun_1 arg_fun_2 in
      let* _ : unit := M.AssertEqual arg_fun_1 var_felt_const_0 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t EnsureBothZero.t :=
      let* var_self : EnsureBothZero.t := M.CreateStruct in
      M.Pure var_self.
  End EnsureBothZero.
End Module_Line_105.

Module Module_Line_147.
  Module Passthrough.
    Record t : Set := {
      out : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Passthrough.t) (arg_fun_1 : Felt.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(Passthrough.out) in
      let* _ : unit := M.AssertEqual arg_fun_1 var_0 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t Passthrough.t :=
      let* var_self : Passthrough.t := M.CreateStruct in
      let* _ : unit := M.AssertEqual var_self.(Passthrough.out) arg_fun_0 in
      M.Pure var_self.
  End Passthrough.

  Module EnsureIsZero.
    Record t : Set := {
      p : Passthrough.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : EnsureIsZero.t) (arg_fun_1 : Felt.t) : M.t unit :=
      let var_felt_const_0 : Felt.t := UnOp.from 0 in
      let var_0 : Passthrough.t := arg_fun_0.(EnsureIsZero.p) in
      let* _ : unit := Passthrough.constrain var_0 var_felt_const_0 in
      let var_1 : Felt.t := var_0.(Passthrough.out) in
      let* _ : unit := M.AssertEqual arg_fun_1 var_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t EnsureIsZero.t :=
      let* var_self : EnsureIsZero.t := M.CreateStruct in
      let* var_0 : Passthrough.t := Passthrough.compute arg_fun_0 in
      let* _ : unit := M.AssertEqual var_self.(EnsureIsZero.p) var_0 in
      M.Pure var_self.
  End EnsureIsZero.
End Module_Line_147.

Module Module_Line_196.
  Module ArrayCheck.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ArrayCheck.t) (arg_fun_1 : Array.t Felt.t [5]) : M.t unit :=
      let var_felt_const_7 : Felt.t := UnOp.from 7 in
      let var_c3 : Index.t := 3 in
      let var_0 : Felt.t := Array.read arg_fun_1 (var_c3, tt) in
      let* _ : unit := M.AssertEqual var_0 var_felt_const_7 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [5]) : M.t ArrayCheck.t :=
      let* var_self : ArrayCheck.t := M.CreateStruct in
      M.Pure var_self.
  End ArrayCheck.
End Module_Line_196.

Module Module_Line_219.
  Module ArrayForCheck.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ArrayForCheck.t) (arg_fun_1 : Array.t Felt.t [5]) : M.t unit :=
      let var_c0 : Index.t := 0 in
      let var_c5 : Index.t := 5 in
      let var_c1 : Index.t := 1 in
      let var_felt_const_7 : Felt.t := UnOp.from 7 in
      let* _ : unit := M.for_ var_c0 (* to *) var_c5 (* step *) var_c1 (fun (arg_for_226_7 : Index.t) =>
        let var_0 : Felt.t := Array.read arg_fun_1 (arg_for_226_7, tt) in
        let* _ : unit := M.AssertEqual var_0 var_felt_const_7 in
        M.yield tt      ) in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [5]) : M.t ArrayForCheck.t :=
      let* var_self : ArrayForCheck.t := M.CreateStruct in
      M.Pure var_self.
  End ArrayForCheck.
End Module_Line_219.

Module Module_Line_246.
  Module ConstConstraints.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ConstConstraints.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_felt_const_1 : Felt.t := UnOp.from 1 in
      let* _ : unit := M.AssertEqual arg_fun_1 var_felt_const_1 in
      let* _ : unit := M.AssertEqual arg_fun_2 var_felt_const_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t ConstConstraints.t :=
      let* var_self : ConstConstraints.t := M.CreateStruct in
      M.Pure var_self.
  End ConstConstraints.
End Module_Line_246.

Module Module_Line_270.
  Module ArrayConstrain.
    Inductive t (A B : nat) : Set := Make.

    Definition constrain {p} `{Prime p} {A B : nat} (arg_fun_0 : ArrayConstrain.t A B) (arg_fun_1 : Array.t Felt.t [3]) : M.t unit :=
      let var_0 : Felt.t := UnOp.from (Z.of_nat A) in
      let var_1 : Felt.t := UnOp.from (Z.of_nat B) in
      let var_c0 : Index.t := 0 in
      let var_c2 : Index.t := 2 in
      let var_2 : Felt.t := Array.read arg_fun_1 (var_c0, tt) in
      let var_3 : Felt.t := Array.read arg_fun_1 (var_c2, tt) in
      let* _ : unit := M.AssertEqual var_2 var_0 in
      let* _ : unit := M.AssertEqual var_3 var_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} {A B : nat} (arg_fun_0 : Array.t Felt.t [3]) : M.t (ArrayConstrain.t A B) :=
      let* var_self : ArrayConstrain.t A B := M.CreateStruct in
      M.Pure var_self.
  End ArrayConstrain.

  Module MatrixConstrain.
    Record t : Set := {
      check0 : ArrayConstrain.t 7 11;
      check1 : ArrayConstrain.t 13 17;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : MatrixConstrain.t) (arg_fun_1 : Array.t Felt.t [2; 3]) : M.t unit :=
      let var_0 : ArrayConstrain.t 7 11 := arg_fun_0.(MatrixConstrain.check0) in
      let var_c0 : Index.t := 0 in
      let var_1 : Array.t Felt.t [3] := Array.extract (Ns := [_]) arg_fun_1 (var_c0, tt) in
      let* _ : unit := ArrayConstrain.constrain var_0 var_1 in
      let var_2 : ArrayConstrain.t 13 17 := arg_fun_0.(MatrixConstrain.check1) in
      let var_c1 : Index.t := 1 in
      let var_3 : Array.t Felt.t [3] := Array.extract (Ns := [_]) arg_fun_1 (var_c1, tt) in
      let* _ : unit := ArrayConstrain.constrain var_2 var_3 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [2; 3]) : M.t MatrixConstrain.t :=
      let* var_self : MatrixConstrain.t := M.CreateStruct in
      M.Pure var_self.
  End MatrixConstrain.
End Module_Line_270.

Module Module_Line_331.
  Module ArrayConstrain.
    Inductive t : Set := Make.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ArrayConstrain.t) (arg_fun_1 : Array.t Felt.t [3]) : M.t unit :=
      let var_felt_const_7 : Felt.t := UnOp.from 7 in
      let var_c1 : Index.t := 1 in
      let var_0 : Felt.t := Array.read arg_fun_1 (var_c1, tt) in
      let* _ : unit := M.AssertEqual var_0 var_felt_const_7 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [3]) : M.t ArrayConstrain.t :=
      let* var_self : ArrayConstrain.t := M.CreateStruct in
      M.Pure var_self.
  End ArrayConstrain.

  Module MatrixConstrain.
    Record t : Set := {
      check : ArrayConstrain.t;
      a : Felt.t;
      b : Felt.t;
      c : Felt.t;
      d : Felt.t;
      e : Felt.t;
      f : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : MatrixConstrain.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(MatrixConstrain.a) in
      let var_1 : Felt.t := arg_fun_0.(MatrixConstrain.b) in
      let var_2 : Felt.t := arg_fun_0.(MatrixConstrain.c) in
      let var_3 : Felt.t := arg_fun_0.(MatrixConstrain.d) in
      let var_4 : Felt.t := arg_fun_0.(MatrixConstrain.e) in
      let var_5 : Felt.t := arg_fun_0.(MatrixConstrain.f) in
      let var_array : Array.t Felt.t [2; 3] := Array.new [var_0; var_1; var_2; var_3; var_4; var_5] in
      let var_6 : ArrayConstrain.t := arg_fun_0.(MatrixConstrain.check) in
      let var_c0 : Index.t := 0 in
      let var_7 : Array.t Felt.t [3] := Array.extract (Ns := [_]) var_array (var_c0, tt) in
      let* _ : unit := ArrayConstrain.constrain var_6 var_7 in
      M.Pure tt.

    Definition compute {p} `{Prime p} : M.t MatrixConstrain.t :=
      let* var_self : MatrixConstrain.t := M.CreateStruct in
      M.Pure var_self.
  End MatrixConstrain.
End Module_Line_331.

Module Module_Line_392.
  Module UnknownArrayConstrain.
    Inductive t (N : nat) : Set := Make.

    Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : UnknownArrayConstrain.t N) (arg_fun_1 : Array.t Felt.t [N]) : M.t unit :=
      let var_felt_const_7 : Felt.t := UnOp.from 7 in
      let var_c1 : Index.t := 1 in
      let var_0 : Felt.t := Array.read arg_fun_1 (var_c1, tt) in
      let* _ : unit := M.AssertEqual var_0 var_felt_const_7 in
      M.Pure tt.

    Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Array.t Felt.t [N]) : M.t (UnknownArrayConstrain.t N) :=
      let* var_self : UnknownArrayConstrain.t N := M.CreateStruct in
      M.Pure var_self.
  End UnknownArrayConstrain.
End Module_Line_392.

Module Module_Line_415.
  Module UnknownArrayConstrain.
    Inductive t (N : nat) : Set := Make.

    Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : UnknownArrayConstrain.t N) (arg_fun_1 : Array.t Felt.t [N]) : M.t unit :=
      let var_felt_const_7 : Felt.t := UnOp.from 7 in
      let var_c1 : Index.t := 1 in
      let var_0 : Felt.t := Array.read arg_fun_1 (var_c1, tt) in
      let* _ : unit := M.AssertEqual var_0 var_felt_const_7 in
      M.Pure tt.

    Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Array.t Felt.t [N]) : M.t (UnknownArrayConstrain.t N) :=
      let* var_self : UnknownArrayConstrain.t N := M.CreateStruct in
      M.Pure var_self.
  End UnknownArrayConstrain.

  Module UnknownMatrixConstrain.
    Record t {M N : nat} : Set := {
      check : UnknownArrayConstrain.t N;
    }.
    Arguments t : clear implicits.

    Definition constrain {p} `{Prime p} {M N : nat} (arg_fun_0 : UnknownMatrixConstrain.t M N) (arg_fun_1 : Array.t Felt.t [M; N]) : M.t unit :=
      let var_0 : UnknownArrayConstrain.t N := arg_fun_0.(UnknownMatrixConstrain.check) in
      let var_c0 : Index.t := 0 in
      let var_1 : Array.t Felt.t [N] := Array.extract (Ns := [_]) arg_fun_1 (var_c0, tt) in
      let* _ : unit := UnknownArrayConstrain.constrain var_0 var_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} {M N : nat} (arg_fun_0 : Array.t Felt.t [M; N]) : M.t (UnknownMatrixConstrain.t M N) :=
      let* var_self : UnknownMatrixConstrain.t M N := M.CreateStruct in
      M.Pure var_self.
  End UnknownMatrixConstrain.
End Module_Line_415.

Module Module_Line_458.
  (* Require Import FrontendLang.Zirgen.zir_example_0 as zir. *)
End Module_Line_458.

Module Module_Line_474.
  (* Require Import FrontendLang.Zirgen.zir_example_1 as zir. *)
End Module_Line_474.

Module Module_Line_497.
  (* Require Import FrontendLang.Zirgen.zir_example_2 as zir. *)
End Module_Line_497.

Module Module_Line_547.
  (* Require Import FrontendLang.Zirgen.zir_example_3 as zir. *)
End Module_Line_547.

Module Module_Line_569.
  (* Require Import Inputs.bits as bits. *)
End Module_Line_569.

Module Module_Line_642.
  Definition extern_add {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Felt.t.
  Admitted.

  Module ExternAdder.
    Record t : Set := {
      sum : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : ExternAdder.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(ExternAdder.sum) in
      let* var_1 : Felt.t := extern_add arg_fun_1 arg_fun_2 in
      let* _ : unit := M.AssertEqual var_0 var_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t ExternAdder.t :=
      let* var_self : ExternAdder.t := M.CreateStruct in
      M.Pure var_self.
  End ExternAdder.
End Module_Line_642.

Module Module_Line_669.
  Definition global_add {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Felt.t :=
    let var_0 : Felt.t := BinOp.add arg_fun_0 arg_fun_1 in
    M.Pure var_0.

  Definition irrelevant {p} `{Prime p} : M.t unit.
  Admitted.

  Module Adder2.
    Record t : Set := {
      sum : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Adder2.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
      let var_0 : Felt.t := arg_fun_0.(Adder2.sum) in
      let* var_1 : Felt.t := global_add arg_fun_1 arg_fun_2 in
      let var_2 : Felt.t := BinOp.add var_1 var_1 in
      let* _ : unit := irrelevant in
      let* _ : unit := M.AssertEqual var_0 var_2 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Adder2.t :=
      let* var_self : Adder2.t := M.CreateStruct in
      let* var_0 : Felt.t := global_add arg_fun_0 arg_fun_1 in
      let* _ : unit := M.AssertEqual var_self.(Adder2.sum) var_0 in
      M.Pure var_self.
  End Adder2.
End Module_Line_669.

Module Module_Line_707.
  Module Signal.
    Record t : Set := {
      reg : Felt.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Signal.t) (arg_fun_1 : Felt.t) : M.t unit :=
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t Signal.t :=
      let* var_self : Signal.t := M.CreateStruct in
      let* _ : unit := M.AssertEqual var_self.(Signal.reg) arg_fun_0 in
      M.Pure var_self.
  End Signal.

  Module Component00.
    Record t : Set := {
      f : Signal.t;
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Component00.t) (arg_fun_1 : Signal.t) : M.t unit :=
      let var_0 : Signal.t := arg_fun_0.(Component00.f) in
      let* _ : unit := M.AssertEqual var_0 arg_fun_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Signal.t) : M.t Component00.t :=
      let* var_self : Component00.t := M.CreateStruct in
      let* _ : unit := M.AssertEqual var_self.(Component00.f) arg_fun_0 in
      M.Pure var_self.
  End Component00.

  Module Component01.
    Record t : Set := {
      f : Array.t Signal.t [2];
    }.

    Definition constrain {p} `{Prime p} (arg_fun_0 : Component01.t) (arg_fun_1 : Array.t Signal.t [2]) : M.t unit :=
      let var_0 : Array.t Signal.t [2] := arg_fun_0.(Component01.f) in
      let* _ : unit := M.AssertEqual var_0 arg_fun_1 in
      M.Pure tt.

    Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Signal.t [2]) : M.t Component01.t :=
      let* var_self : Component01.t := M.CreateStruct in
      let* _ : unit := M.AssertEqual var_self.(Component01.f) arg_fun_0 in
      M.Pure var_self.
  End Component01.
End Module_Line_707.
