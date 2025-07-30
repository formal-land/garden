(* Generated *)
Require Import Garden.LLZK.M.

Module Module_Line_5.
  (* Empty module *)
End Module_Line_5.

Module Component.
  Inductive t : Set := Make.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := α;
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Component.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} : M.t Component.t :=
    let* var_self : Component.t := M.CreateStruct in
    M.Pure var_self.
End Component.

Module NondetReg.
  Record t : Set := {
    dollar_super : Felt.t;
    reg : Felt.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      reg := map_mod α.(reg);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : NondetReg.t) (arg_fun_1 : Felt.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t NondetReg.t :=
    let* var_self : NondetReg.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(NondetReg.reg) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(NondetReg.dollar_super) arg_fun_0 in
    M.Pure var_self.
End NondetReg.

Module NondetExtReg.
  Record t : Set := {
    dollar_super : Array.t Felt.t [4]%nat;
    reg : Array.t Felt.t [4]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      reg := map_mod α.(reg);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : NondetExtReg.t) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [4]%nat) : M.t NondetExtReg.t :=
    let* var_self : NondetExtReg.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(NondetExtReg.reg) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(NondetExtReg.dollar_super) arg_fun_0 in
    M.Pure var_self.
End NondetExtReg.

Module EqzExt.
  Record t : Set := {
    dollar_super : Component.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : EqzExt.t) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [4]%nat) : M.t EqzExt.t :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c3 : Index.t := 3%nat in
    let var_c2 : Index.t := 2%nat in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let* var_self : EqzExt.t := M.CreateStruct in
    let var_0 : Felt.t := Array.read arg_fun_0 (var_c0, tt) in
    let var_1 : Felt.t := Array.read arg_fun_0 (var_c1, tt) in
    let var_2 : Felt.t := Array.read arg_fun_0 (var_c2, tt) in
    let var_3 : Felt.t := Array.read arg_fun_0 (var_c3, tt) in
    let var_4 : bool := Bool.cmp BoolCmp.Eq var_0 var_felt_const_0 in
    let var_5 : bool := Bool.cmp BoolCmp.Eq var_1 var_felt_const_0 in
    let var_6 : bool := Bool.cmp BoolCmp.Eq var_2 var_felt_const_0 in
    let var_7 : bool := Bool.cmp BoolCmp.Eq var_3 var_felt_const_0 in
    let var_8 : bool := Bool.and var_4 var_5 in
    let var_9 : bool := Bool.and var_8 var_6 in
    let var_10 : bool := Bool.and var_9 var_7 in
    let* _ : unit := M.AssertBool var_10 in
    let* var_11 : Component.t := Component.compute in
    let* _ : unit := M.FieldWrite var_self.(EqzExt.dollar_super) var_11 in
    M.Pure var_self.
End EqzExt.

Module Reg.
  Record t : Set := {
    dollar_super : NondetReg.t;
    reg : NondetReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      reg := map_mod α.(reg);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Reg.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_0 : NondetReg.t := arg_fun_0.(Reg.reg) in
    let* _ : unit := NondetReg.constrain var_0 arg_fun_1 in
    let var_1 : Felt.t := var_0.(NondetReg.dollar_super) in
    let* _ : unit := M.AssertEqual arg_fun_1 var_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t Reg.t :=
    let* var_self : Reg.t := M.CreateStruct in
    let* var_0 : NondetReg.t := NondetReg.compute arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(Reg.reg) var_0 in
    let var_1 : NondetReg.t := var_self.(Reg.reg) in
    let var_2 : Felt.t := var_1.(NondetReg.dollar_super) in
    let* _ : unit := M.FieldWrite var_self.(Reg.dollar_super) var_1 in
    M.Pure var_self.
End Reg.

Module ExtReg.
  Record t : Set := {
    dollar_super : NondetExtReg.t;
    dollar_temp : EqzExt.t;
    reg : NondetExtReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      reg := map_mod α.(reg);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : ExtReg.t) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t unit :=
    let var_c3 : Index.t := 3%nat in
    let var_c2 : Index.t := 2%nat in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let var_0 : NondetExtReg.t := arg_fun_0.(ExtReg.reg) in
    let* _ : unit := NondetExtReg.constrain var_0 arg_fun_1 in
    let var_1 : Array.t Felt.t [4]%nat := var_0.(NondetExtReg.dollar_super) in
    let var_2 : Felt.t := Array.read var_1 (var_c0, tt) in
    let var_3 : Felt.t := Array.read var_1 (var_c1, tt) in
    let var_4 : Felt.t := Array.read var_1 (var_c2, tt) in
    let var_5 : Felt.t := Array.read var_1 (var_c3, tt) in
    let var_6 : Felt.t := Array.read arg_fun_1 (var_c0, tt) in
    let var_7 : Felt.t := Array.read arg_fun_1 (var_c1, tt) in
    let var_8 : Felt.t := Array.read arg_fun_1 (var_c2, tt) in
    let var_9 : Felt.t := Array.read arg_fun_1 (var_c3, tt) in
    let var_10 : Felt.t := BinOp.sub var_2 var_6 in
    let var_11 : Felt.t := BinOp.sub var_3 var_7 in
    let var_12 : Felt.t := BinOp.sub var_4 var_8 in
    let var_13 : Felt.t := BinOp.sub var_5 var_9 in
    let var_array : Array.t Felt.t [4]%nat := Array.new [var_10; var_11; var_12; var_13] in
    let var_14 : EqzExt.t := arg_fun_0.(ExtReg.dollar_temp) in
    let* _ : unit := EqzExt.constrain var_14 var_array in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [4]%nat) : M.t ExtReg.t :=
    let var_c3 : Index.t := 3%nat in
    let var_c2 : Index.t := 2%nat in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let* var_self : ExtReg.t := M.CreateStruct in
    let* var_0 : NondetExtReg.t := NondetExtReg.compute arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(ExtReg.reg) var_0 in
    let var_1 : NondetExtReg.t := var_self.(ExtReg.reg) in
    let var_2 : Array.t Felt.t [4]%nat := var_1.(NondetExtReg.dollar_super) in
    let var_3 : Felt.t := Array.read var_2 (var_c0, tt) in
    let var_4 : Felt.t := Array.read var_2 (var_c1, tt) in
    let var_5 : Felt.t := Array.read var_2 (var_c2, tt) in
    let var_6 : Felt.t := Array.read var_2 (var_c3, tt) in
    let var_7 : Felt.t := Array.read arg_fun_0 (var_c0, tt) in
    let var_8 : Felt.t := Array.read arg_fun_0 (var_c1, tt) in
    let var_9 : Felt.t := Array.read arg_fun_0 (var_c2, tt) in
    let var_10 : Felt.t := Array.read arg_fun_0 (var_c3, tt) in
    let var_11 : Felt.t := BinOp.sub var_3 var_7 in
    let var_12 : Felt.t := BinOp.sub var_4 var_8 in
    let var_13 : Felt.t := BinOp.sub var_5 var_9 in
    let var_14 : Felt.t := BinOp.sub var_6 var_10 in
    let var_array : Array.t Felt.t [4]%nat := Array.new [var_11; var_12; var_13; var_14] in
    let* var_15 : EqzExt.t := EqzExt.compute var_array in
    let* _ : unit := M.FieldWrite var_self.(ExtReg.dollar_temp) var_15 in
    let var_16 : EqzExt.t := var_self.(ExtReg.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(ExtReg.dollar_super) var_1 in
    M.Pure var_self.
End ExtReg.

Module Div.
  Record t : Set := {
    dollar_super : Felt.t;
    reciprocal : Felt.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      reciprocal := map_mod α.(reciprocal);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Div.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_0 : Felt.t := arg_fun_0.(Div.reciprocal) in
    let var_1 : Felt.t := BinOp.mul var_0 arg_fun_2 in
    let* _ : unit := M.AssertEqual var_1 var_felt_const_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Div.t :=
    let* var_self : Div.t := M.CreateStruct in
    let var_0 : Felt.t := UnOp.inv arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(Div.reciprocal) var_0 in
    let var_1 : Felt.t := var_self.(Div.reciprocal) in
    let var_2 : Felt.t := BinOp.mul var_1 arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(Div.dollar_super) var_2 in
    M.Pure var_self.
End Div.

Definition Logdollar_dollar_extern {p} `{Prime p} (arg_fun_0 : string) (arg_fun_1 : Array.t Felt.t [Array.dimension_any]%nat) : M.t Component.t.
Admitted.

Module Log.
  Record t : Set := {
    dollar_super : Component.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Log.t) (arg_fun_1 : string) (arg_fun_2 : Array.t Felt.t [Array.dimension_any]%nat) : M.t unit :=
    let* var_0 : Component.t := Logdollar_dollar_extern arg_fun_1 arg_fun_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : string) (arg_fun_1 : Array.t Felt.t [Array.dimension_any]%nat) : M.t Log.t :=
    let* var_self : Log.t := M.CreateStruct in
    let* var_0 : Component.t := Logdollar_dollar_extern arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(Log.dollar_super) var_0 in
    M.Pure var_self.
End Log.

Definition Abortdollar_dollar_extern {p} `{Prime p} : M.t Component.t.
Admitted.

Module Abort.
  Record t : Set := {
    dollar_super : Component.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Abort.t) : M.t unit :=
    let* var_0 : Component.t := Abortdollar_dollar_extern in
    M.Pure tt.

  Definition compute {p} `{Prime p} : M.t Abort.t :=
    let* var_self : Abort.t := M.CreateStruct in
    let* var_0 : Component.t := Abortdollar_dollar_extern in
    let* _ : unit := M.FieldWrite var_self.(Abort.dollar_super) var_0 in
    M.Pure var_self.
End Abort.

Definition Assertdollar_dollar_extern {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : string) : M.t Component.t.
Admitted.

Module Assert.
  Record t : Set := {
    dollar_super : Component.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Assert.t) (arg_fun_1 : Felt.t) (arg_fun_2 : string) : M.t unit :=
    let* var_0 : Component.t := Assertdollar_dollar_extern arg_fun_1 arg_fun_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : string) : M.t Assert.t :=
    let* var_self : Assert.t := M.CreateStruct in
    let* var_0 : Component.t := Assertdollar_dollar_extern arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(Assert.dollar_super) var_0 in
    M.Pure var_self.
End Assert.

Module AssertBit.
  Record t : Set := {
    dollar_super : Component.t;
    dollar_temp : Component.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : AssertBit.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_0 : Felt.t := BinOp.sub var_felt_const_1 arg_fun_1 in
    let var_1 : Felt.t := BinOp.mul arg_fun_1 var_0 in
    let* _ : unit := M.AssertEqual var_1 var_felt_const_0 in
    let var_2 : Component.t := arg_fun_0.(AssertBit.dollar_temp) in
    let* _ : unit := Component.constrain var_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t AssertBit.t :=
    let* var_self : AssertBit.t := M.CreateStruct in
    let* var_0 : Component.t := Component.compute in
    let* _ : unit := M.FieldWrite var_self.(AssertBit.dollar_temp) var_0 in
    let var_1 : Component.t := var_self.(AssertBit.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(AssertBit.dollar_super) var_1 in
    M.Pure var_self.
End AssertBit.

Module NondetBitReg.
  Record t : Set := {
    dollar_super : NondetReg.t;
    dollar_temp : AssertBit.t;
    reg : NondetReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      reg := map_mod α.(reg);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : NondetBitReg.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_0 : NondetReg.t := arg_fun_0.(NondetBitReg.reg) in
    let* _ : unit := NondetReg.constrain var_0 arg_fun_1 in
    let var_1 : Felt.t := var_0.(NondetReg.dollar_super) in
    let var_2 : AssertBit.t := arg_fun_0.(NondetBitReg.dollar_temp) in
    let* _ : unit := AssertBit.constrain var_2 var_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t NondetBitReg.t :=
    let* var_self : NondetBitReg.t := M.CreateStruct in
    let* var_0 : NondetReg.t := NondetReg.compute arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(NondetBitReg.reg) var_0 in
    let var_1 : NondetReg.t := var_self.(NondetBitReg.reg) in
    let var_2 : Felt.t := var_1.(NondetReg.dollar_super) in
    let* var_3 : AssertBit.t := AssertBit.compute var_2 in
    let* _ : unit := M.FieldWrite var_self.(NondetBitReg.dollar_temp) var_3 in
    let var_4 : AssertBit.t := var_self.(NondetBitReg.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(NondetBitReg.dollar_super) var_1 in
    M.Pure var_self.
End NondetBitReg.

Module BitAnd.
  Record t : Set := {
    dollar_super : Felt.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : BitAnd.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t BitAnd.t :=
    let* var_self : BitAnd.t := M.CreateStruct in
    let var_0 : Felt.t := BinOp.mul arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(BitAnd.dollar_super) var_0 in
    M.Pure var_self.
End BitAnd.

Module OneHot.
  Record t {N : nat} : Set := {
    dollar_super : Array.t NondetBitReg.t [Array.affine_map]%nat;
    dollar_temp_1 : Array.t Felt.t [Array.affine_map]%nat;
    dollar_array : Array.t Felt.t [Array.affine_map]%nat;
    dollar_temp_0 : Array.t Felt.t [Array.affine_map]%nat;
    dollar_temp : Array.t NondetBitReg.t [Array.affine_map]%nat;
    bits : Array.t NondetBitReg.t [Array.affine_map]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {N : nat} : MapMod (t N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      bits := map_mod α.(bits);
    |};
  }.

  Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : OneHot.t N) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_365_7 : Index.t) =>
      let var_14 : Felt.t := M.cast_to_felt arg_for_365_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_365_7, tt) var_14 in
      M.yield tt
    ) in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t NondetBitReg.t [Array.affine_map]%nat := Array.new [] in
    let* var_4 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_4 (* step *) var_c1 (fun (arg_for_372_7 : Index.t) =>
      let var_14 : Felt.t := Array.read var_array (arg_for_372_7, tt) in
      let var_15 : Felt.t := BinOp.sub var_14 arg_fun_1 in
      let var_16 : bool := Bool.cmp BoolCmp.Eq var_15 var_felt_const_0 in
      let var_17 : Felt.t := M.cast_to_felt var_16 in
      let var_18 : Array.t NondetBitReg.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp) in
      let var_19 : Array.t NondetBitReg.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp) in
      let var_20 : NondetBitReg.t := Array.read var_19 (arg_for_372_7, tt) in
      let* _ : unit := NondetBitReg.constrain var_20 var_17 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_372_7, tt) var_20 in
      M.yield tt
    ) in
    let var_5 : Array.t NondetBitReg.t [Array.affine_map]%nat := arg_fun_0.(OneHot.bits) in
    let* var_6 : Index.t := Array.len var_5 var_c0 in
    let* var_7 : Felt.t := M.for_ var_c0 (* to *) var_6 (* step *) var_c1 (fun (arg_for_385_12 : Index.t) (arg_for_385_12 : Felt.t) =>
      let var_14 : NondetBitReg.t := Array.read var_5 (arg_for_385_12, tt) in
      let var_15 : NondetReg.t := var_14.(NondetBitReg.dollar_super) in
      let var_16 : Felt.t := var_15.(NondetReg.dollar_super) in
      let var_17 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp_0) in
      let var_18 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp_0) in
      let var_19 : Felt.t := Array.read var_18 (arg_for_385_12, tt) in
      M.yield var_19
    ) in
    let* _ : unit := M.AssertEqual var_7 var_felt_const_1 in
    let var_8 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_1 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_397_7 : Index.t) =>
      let var_14 : Felt.t := M.cast_to_felt arg_for_397_7 in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_397_7, tt) var_14 in
      M.yield tt
    ) in
    let var_9 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_2 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* var_10 : Index.t := Array.len var_array_1 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_10 (* step *) var_c1 (fun (arg_for_404_7 : Index.t) =>
      let var_14 : Felt.t := Array.read var_array_1 (arg_for_404_7, tt) in
      let var_15 : Index.t := M.cast_to_index var_14 in
      let var_16 : NondetBitReg.t := Array.read var_5 (var_15, tt) in
      let var_17 : NondetReg.t := var_16.(NondetBitReg.dollar_super) in
      let var_18 : Felt.t := var_17.(NondetReg.dollar_super) in
      let var_19 : Felt.t := BinOp.mul var_18 var_14 in
      let* _ : unit := M.ArrayWrite var_array_2 (arg_for_404_7, tt) var_19 in
      M.yield tt
    ) in
    let var_11 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_array) in
    let* var_12 : Index.t := Array.len var_11 var_c0 in
    let* var_13 : Felt.t := M.for_ var_c0 (* to *) var_12 (* step *) var_c1 (fun (arg_for_415_13 : Index.t) (arg_for_415_13 : Felt.t) =>
      let var_14 : Felt.t := Array.read var_11 (arg_for_415_13, tt) in
      let var_15 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp_1) in
      let var_16 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(OneHot.dollar_temp_1) in
      let var_17 : Felt.t := Array.read var_16 (arg_for_415_13, tt) in
      M.yield var_17
    ) in
    let* _ : unit := M.AssertEqual var_13 arg_fun_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Felt.t) : M.t (OneHot.t N) :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : OneHot.t N := M.CreateStruct in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_287_7 : Index.t) =>
      let var_14 : Felt.t := M.cast_to_felt arg_for_287_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_287_7, tt) var_14 in
      M.yield tt
    ) in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t NondetBitReg.t [Array.affine_map]%nat := Array.new [] in
    let* var_4 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_4 (* step *) var_c1 (fun (arg_for_294_7 : Index.t) =>
      let var_14 : Felt.t := Array.read var_array (arg_for_294_7, tt) in
      let var_15 : Felt.t := BinOp.sub var_14 arg_fun_0 in
      let var_16 : bool := Bool.cmp BoolCmp.Eq var_15 var_felt_const_0 in
      let var_17 : Felt.t := M.cast_to_felt var_16 in
      let* var_18 : NondetBitReg.t := NondetBitReg.compute var_17 in
      let var_19 : Array.t NondetBitReg.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_19 (arg_for_294_7, tt) var_18 in
      let* _ : unit := M.FieldWrite var_self.(OneHot.dollar_temp) var_19 in
      let var_20 : Array.t NondetBitReg.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp) in
      let var_21 : NondetBitReg.t := Array.read var_20 (arg_for_294_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_294_7, tt) var_21 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(OneHot.bits) var_array_0 in
    let var_5 : Array.t NondetBitReg.t [Array.affine_map]%nat := var_self.(OneHot.bits) in
    let* var_6 : Index.t := Array.len var_5 var_c0 in
    let* var_7 : Felt.t := M.for_ var_c0 (* to *) var_6 (* step *) var_c1 (fun (arg_for_310_12 : Index.t) (arg_for_310_12 : Felt.t) =>
      let var_14 : NondetBitReg.t := Array.read var_5 (arg_for_310_12, tt) in
      let var_15 : NondetReg.t := var_14.(NondetBitReg.dollar_super) in
      let var_16 : Felt.t := var_15.(NondetReg.dollar_super) in
      let var_17 : Felt.t := BinOp.add arg_for_310_12 var_16 in
      let var_18 : Array.t Felt.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_18 (arg_for_310_12, tt) var_17 in
      let* _ : unit := M.FieldWrite var_self.(OneHot.dollar_temp_0) var_18 in
      let var_19 : Array.t Felt.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp_0) in
      let var_20 : Felt.t := Array.read var_19 (arg_for_310_12, tt) in
      M.yield var_20
    ) in
    let var_8 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_1 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_324_7 : Index.t) =>
      let var_14 : Felt.t := M.cast_to_felt arg_for_324_7 in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_324_7, tt) var_14 in
      M.yield tt
    ) in
    let var_9 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_2 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* var_10 : Index.t := Array.len var_array_1 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_10 (* step *) var_c1 (fun (arg_for_331_7 : Index.t) =>
      let var_14 : Felt.t := Array.read var_array_1 (arg_for_331_7, tt) in
      let var_15 : Index.t := M.cast_to_index var_14 in
      let var_16 : NondetBitReg.t := Array.read var_5 (var_15, tt) in
      let var_17 : NondetReg.t := var_16.(NondetBitReg.dollar_super) in
      let var_18 : Felt.t := var_17.(NondetReg.dollar_super) in
      let var_19 : Felt.t := BinOp.mul var_18 var_14 in
      let* _ : unit := M.ArrayWrite var_array_2 (arg_for_331_7, tt) var_19 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(OneHot.dollar_array) var_array_2 in
    let var_11 : Array.t Felt.t [Array.affine_map]%nat := var_self.(OneHot.dollar_array) in
    let* var_12 : Index.t := Array.len var_11 var_c0 in
    let* var_13 : Felt.t := M.for_ var_c0 (* to *) var_12 (* step *) var_c1 (fun (arg_for_343_13 : Index.t) (arg_for_343_13 : Felt.t) =>
      let var_14 : Felt.t := Array.read var_11 (arg_for_343_13, tt) in
      let var_15 : Felt.t := BinOp.add arg_for_343_13 var_14 in
      let var_16 : Array.t Felt.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp_1) in
      let* _ : unit := M.ArrayWrite var_16 (arg_for_343_13, tt) var_15 in
      let* _ : unit := M.FieldWrite var_self.(OneHot.dollar_temp_1) var_16 in
      let var_17 : Array.t Felt.t [Array.affine_map]%nat := var_self.(OneHot.dollar_temp_1) in
      let var_18 : Felt.t := Array.read var_17 (arg_for_343_13, tt) in
      M.yield var_18
    ) in
    let* _ : unit := M.FieldWrite var_self.(OneHot.dollar_super) var_5 in
    M.Pure var_self.
End OneHot.

Module Switch.
  Record t {N idx : nat} : Set := {
    dollar_super : Array.t Felt.t [Array.affine_map]%nat;
    dollar_array : Array.t Felt.t [Array.affine_map]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {N idx : nat} : MapMod (t N idx) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} {N idx : nat} (arg_fun_0 : Switch.t N idx) : M.t unit :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Felt.t := UnOp.from (Z.of_nat idx) in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_467_7 : Index.t) =>
      let var_7 : Felt.t := M.cast_to_felt arg_for_467_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_467_7, tt) var_7 in
      M.yield tt
    ) in
    let var_4 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* var_5 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_5 (* step *) var_c1 (fun (arg_for_474_7 : Index.t) =>
      let var_7 : Felt.t := Array.read var_array (arg_for_474_7, tt) in
      let var_8 : Felt.t := BinOp.sub var_7 var_1 in
      let var_9 : bool := Bool.cmp BoolCmp.Eq var_8 var_felt_const_0 in
      let var_10 : Felt.t := M.cast_to_felt var_9 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_474_7, tt) var_10 in
      M.yield tt
    ) in
    let var_6 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(Switch.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {N idx : nat} : M.t (Switch.t N idx) :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : Switch.t N idx := M.CreateStruct in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Felt.t := UnOp.from (Z.of_nat idx) in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_439_7 : Index.t) =>
      let var_7 : Felt.t := M.cast_to_felt arg_for_439_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_439_7, tt) var_7 in
      M.yield tt
    ) in
    let var_4 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let* var_5 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_5 (* step *) var_c1 (fun (arg_for_446_7 : Index.t) =>
      let var_7 : Felt.t := Array.read var_array (arg_for_446_7, tt) in
      let var_8 : Felt.t := BinOp.sub var_7 var_1 in
      let var_9 : bool := Bool.cmp BoolCmp.Eq var_8 var_felt_const_0 in
      let var_10 : Felt.t := M.cast_to_felt var_9 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_446_7, tt) var_10 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(Switch.dollar_array) var_array_0 in
    let var_6 : Array.t Felt.t [Array.affine_map]%nat := var_self.(Switch.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(Switch.dollar_super) var_6 in
    M.Pure var_self.
End Switch.

Module M_INT_DIAG_HZN.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : M_INT_DIAG_HZN.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} : M.t M_INT_DIAG_HZN.t :=
    let var_felt_const_918610824 : Felt.t := UnOp.from 918610824 in
    let var_felt_const_13683276 : Felt.t := UnOp.from 13683276 in
    let var_felt_const_606789471 : Felt.t := UnOp.from 606789471 in
    let var_felt_const_1974912880 : Felt.t := UnOp.from 1974912880 in
    let var_felt_const_65998480 : Felt.t := UnOp.from 65998480 in
    let var_felt_const_1461037801 : Felt.t := UnOp.from 1461037801 in
    let var_felt_const_1997365680 : Felt.t := UnOp.from 1997365680 in
    let var_felt_const_801504236 : Felt.t := UnOp.from 801504236 in
    let var_felt_const_1792686146 : Felt.t := UnOp.from 1792686146 in
    let var_felt_const_1001081699 : Felt.t := UnOp.from 1001081699 in
    let var_felt_const_98371040 : Felt.t := UnOp.from 98371040 in
    let var_felt_const_1389833583 : Felt.t := UnOp.from 1389833583 in
    let var_felt_const_106789798 : Felt.t := UnOp.from 106789798 in
    let var_felt_const_1188752902 : Felt.t := UnOp.from 1188752902 in
    let var_felt_const_20525701 : Felt.t := UnOp.from 20525701 in
    let var_felt_const_1558116381 : Felt.t := UnOp.from 1558116381 in
    let var_felt_const_1942928017 : Felt.t := UnOp.from 1942928017 in
    let var_felt_const_1928969209 : Felt.t := UnOp.from 1928969209 in
    let var_felt_const_51866717 : Felt.t := UnOp.from 51866717 in
    let var_felt_const_658182609 : Felt.t := UnOp.from 658182609 in
    let var_felt_const_1867716110 : Felt.t := UnOp.from 1867716110 in
    let var_felt_const_111593398 : Felt.t := UnOp.from 111593398 in
    let var_felt_const_375892129 : Felt.t := UnOp.from 375892129 in
    let var_felt_const_1083257840 : Felt.t := UnOp.from 1083257840 in
    let* var_self : M_INT_DIAG_HZN.t := M.CreateStruct in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_1083257840; var_felt_const_375892129; var_felt_const_111593398; var_felt_const_1867716110; var_felt_const_658182609; var_felt_const_51866717; var_felt_const_1928969209; var_felt_const_1942928017; var_felt_const_1558116381; var_felt_const_20525701; var_felt_const_1188752902; var_felt_const_106789798; var_felt_const_1389833583; var_felt_const_98371040; var_felt_const_1001081699; var_felt_const_1792686146; var_felt_const_801504236; var_felt_const_1997365680; var_felt_const_1461037801; var_felt_const_65998480; var_felt_const_1974912880; var_felt_const_606789471; var_felt_const_13683276; var_felt_const_918610824] in
    let* _ : unit := M.FieldWrite var_self.(M_INT_DIAG_HZN.dollar_super) var_array in
    M.Pure var_self.
End M_INT_DIAG_HZN.

Module MultiplyByMInt.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
    dollar_temp_0 : Array.t M_INT_DIAG_HZN.t [24]%nat;
    dollar_array : Array.t Felt.t [24]%nat;
    dollar_temp : Array.t Felt.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : MultiplyByMInt.t) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t unit :=
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c24 : Index.t := 24%nat in
    let* var_0 : Felt.t := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_617_12 : Index.t) (arg_for_617_12 : Felt.t) =>
      let var_2 : Felt.t := Array.read arg_fun_1 (arg_for_617_12, tt) in
      let var_3 : Array.t Felt.t [24]%nat := arg_fun_0.(MultiplyByMInt.dollar_temp) in
      let var_4 : Array.t Felt.t [24]%nat := arg_fun_0.(MultiplyByMInt.dollar_temp) in
      let var_5 : Felt.t := Array.read var_4 (arg_for_617_12, tt) in
      M.yield var_5
    ) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_626_7 : Index.t) =>
      let var_2 : Felt.t := Array.read var_array (arg_for_626_7, tt) in
      let var_3 : Array.t M_INT_DIAG_HZN.t [24]%nat := arg_fun_0.(MultiplyByMInt.dollar_temp_0) in
      let var_4 : Array.t M_INT_DIAG_HZN.t [24]%nat := arg_fun_0.(MultiplyByMInt.dollar_temp_0) in
      let var_5 : M_INT_DIAG_HZN.t := Array.read var_4 (arg_for_626_7, tt) in
      let* _ : unit := M_INT_DIAG_HZN.constrain var_5 in
      let var_6 : Array.t Felt.t [24]%nat := var_5.(M_INT_DIAG_HZN.dollar_super) in
      let var_7 : Index.t := M.cast_to_index var_2 in
      let var_8 : Felt.t := Array.read var_6 (var_7, tt) in
      let var_9 : Index.t := M.cast_to_index var_2 in
      let var_10 : Felt.t := Array.read arg_fun_1 (var_9, tt) in
      let var_11 : Felt.t := BinOp.mul var_8 var_10 in
      let var_12 : Felt.t := BinOp.add var_0 var_11 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_626_7, tt) var_12 in
      M.yield tt
    ) in
    let var_1 : Array.t Felt.t [24]%nat := arg_fun_0.(MultiplyByMInt.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) : M.t MultiplyByMInt.t :=
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : MultiplyByMInt.t := M.CreateStruct in
    let* var_0 : Felt.t := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_555_12 : Index.t) (arg_for_555_12 : Felt.t) =>
      let var_2 : Felt.t := Array.read arg_fun_0 (arg_for_555_12, tt) in
      let var_3 : Felt.t := BinOp.add arg_for_555_12 var_2 in
      let var_4 : Array.t Felt.t [24]%nat := var_self.(MultiplyByMInt.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_4 (arg_for_555_12, tt) var_3 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMInt.dollar_temp) var_4 in
      let var_5 : Array.t Felt.t [24]%nat := var_self.(MultiplyByMInt.dollar_temp) in
      let var_6 : Felt.t := Array.read var_5 (arg_for_555_12, tt) in
      M.yield var_6
    ) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_567_7 : Index.t) =>
      let var_2 : Felt.t := Array.read var_array (arg_for_567_7, tt) in
      let* var_3 : M_INT_DIAG_HZN.t := M_INT_DIAG_HZN.compute in
      let var_4 : Array.t M_INT_DIAG_HZN.t [24]%nat := var_self.(MultiplyByMInt.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_4 (arg_for_567_7, tt) var_3 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMInt.dollar_temp_0) var_4 in
      let var_5 : Array.t M_INT_DIAG_HZN.t [24]%nat := var_self.(MultiplyByMInt.dollar_temp_0) in
      let var_6 : M_INT_DIAG_HZN.t := Array.read var_5 (arg_for_567_7, tt) in
      let var_7 : Array.t Felt.t [24]%nat := var_6.(M_INT_DIAG_HZN.dollar_super) in
      let var_8 : Index.t := M.cast_to_index var_2 in
      let var_9 : Felt.t := Array.read var_7 (var_8, tt) in
      let var_10 : Index.t := M.cast_to_index var_2 in
      let var_11 : Felt.t := Array.read arg_fun_0 (var_10, tt) in
      let var_12 : Felt.t := BinOp.mul var_9 var_11 in
      let var_13 : Felt.t := BinOp.add var_0 var_12 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_567_7, tt) var_13 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByMInt.dollar_array) var_array_0 in
    let var_1 : Array.t Felt.t [24]%nat := var_self.(MultiplyByMInt.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByMInt.dollar_super) var_1 in
    M.Pure var_self.
End MultiplyByMInt.

Module INT_ROUND_CONSTANTS.
  Record t : Set := {
    dollar_super : Array.t Felt.t [21]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : INT_ROUND_CONSTANTS.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} : M.t INT_ROUND_CONSTANTS.t :=
    let var_felt_const_1810596765 : Felt.t := UnOp.from 1810596765 in
    let var_felt_const_1210751726 : Felt.t := UnOp.from 1210751726 in
    let var_felt_const_1327682690 : Felt.t := UnOp.from 1327682690 in
    let var_felt_const_1886977120 : Felt.t := UnOp.from 1886977120 in
    let var_felt_const_1551596046 : Felt.t := UnOp.from 1551596046 in
    let var_felt_const_1186174623 : Felt.t := UnOp.from 1186174623 in
    let var_felt_const_1199068823 : Felt.t := UnOp.from 1199068823 in
    let var_felt_const_1240419708 : Felt.t := UnOp.from 1240419708 in
    let var_felt_const_1708681573 : Felt.t := UnOp.from 1708681573 in
    let var_felt_const_308575117 : Felt.t := UnOp.from 308575117 in
    let var_felt_const_1111544260 : Felt.t := UnOp.from 1111544260 in
    let var_felt_const_822033215 : Felt.t := UnOp.from 822033215 in
    let var_felt_const_1891545577 : Felt.t := UnOp.from 1891545577 in
    let var_felt_const_440300254 : Felt.t := UnOp.from 440300254 in
    let var_felt_const_1726563304 : Felt.t := UnOp.from 1726563304 in
    let var_felt_const_1365519753 : Felt.t := UnOp.from 1365519753 in
    let var_felt_const_924863639 : Felt.t := UnOp.from 924863639 in
    let var_felt_const_1540960371 : Felt.t := UnOp.from 1540960371 in
    let var_felt_const_1052077299 : Felt.t := UnOp.from 1052077299 in
    let var_felt_const_1930103076 : Felt.t := UnOp.from 1930103076 in
    let var_felt_const_497520322 : Felt.t := UnOp.from 497520322 in
    let* var_self : INT_ROUND_CONSTANTS.t := M.CreateStruct in
    let var_array : Array.t Felt.t [21]%nat := Array.new [var_felt_const_497520322; var_felt_const_1930103076; var_felt_const_1052077299; var_felt_const_1540960371; var_felt_const_924863639; var_felt_const_1365519753; var_felt_const_1726563304; var_felt_const_440300254; var_felt_const_1891545577; var_felt_const_822033215; var_felt_const_1111544260; var_felt_const_308575117; var_felt_const_1708681573; var_felt_const_1240419708; var_felt_const_1199068823; var_felt_const_1186174623; var_felt_const_1551596046; var_felt_const_1886977120; var_felt_const_1327682690; var_felt_const_1210751726; var_felt_const_1810596765] in
    let* _ : unit := M.FieldWrite var_self.(INT_ROUND_CONSTANTS.dollar_super) var_array in
    M.Pure var_self.
End INT_ROUND_CONSTANTS.

Module SBox.
  Record t : Set := {
    dollar_super : Reg.t;
    out : Reg.t;
    cubed : Reg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      out := map_mod α.(out);
      cubed := map_mod α.(cubed);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : SBox.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_0 : Felt.t := BinOp.mul arg_fun_1 arg_fun_1 in
    let var_1 : Felt.t := BinOp.mul var_0 arg_fun_1 in
    let var_2 : Reg.t := arg_fun_0.(SBox.cubed) in
    let* _ : unit := Reg.constrain var_2 var_1 in
    let var_3 : NondetReg.t := var_2.(Reg.dollar_super) in
    let var_4 : Felt.t := var_3.(NondetReg.dollar_super) in
    let var_5 : NondetReg.t := var_2.(Reg.dollar_super) in
    let var_6 : Felt.t := var_5.(NondetReg.dollar_super) in
    let var_7 : Felt.t := BinOp.mul var_4 var_6 in
    let var_8 : Felt.t := BinOp.mul var_7 arg_fun_1 in
    let var_9 : Reg.t := arg_fun_0.(SBox.out) in
    let* _ : unit := Reg.constrain var_9 var_8 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t SBox.t :=
    let* var_self : SBox.t := M.CreateStruct in
    let var_0 : Felt.t := BinOp.mul arg_fun_0 arg_fun_0 in
    let var_1 : Felt.t := BinOp.mul var_0 arg_fun_0 in
    let* var_2 : Reg.t := Reg.compute var_1 in
    let* _ : unit := M.FieldWrite var_self.(SBox.cubed) var_2 in
    let var_3 : Reg.t := var_self.(SBox.cubed) in
    let var_4 : NondetReg.t := var_3.(Reg.dollar_super) in
    let var_5 : Felt.t := var_4.(NondetReg.dollar_super) in
    let var_6 : NondetReg.t := var_3.(Reg.dollar_super) in
    let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
    let var_8 : Felt.t := BinOp.mul var_5 var_7 in
    let var_9 : Felt.t := BinOp.mul var_8 arg_fun_0 in
    let* var_10 : Reg.t := Reg.compute var_9 in
    let* _ : unit := M.FieldWrite var_self.(SBox.out) var_10 in
    let var_11 : Reg.t := var_self.(SBox.out) in
    let* _ : unit := M.FieldWrite var_self.(SBox.dollar_super) var_11 in
    M.Pure var_self.
End SBox.

Module DoIntRound.
  Record t : Set := {
    dollar_super : MultiplyByMInt.t;
    dollar_temp : MultiplyByMInt.t;
    mat_in : Array.t Felt.t [24]%nat;
    sbox : SBox.t;
    x : Felt.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      mat_in := map_mod α.(mat_in);
      sbox := map_mod α.(sbox);
      x := map_mod α.(x);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : DoIntRound.t) (arg_fun_1 : Array.t Felt.t [24]%nat) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : Index.t := M.cast_to_index var_felt_const_0 in
    let var_1 : Felt.t := Array.read arg_fun_1 (var_0, tt) in
    let var_2 : Felt.t := BinOp.add var_1 arg_fun_2 in
    let var_3 : SBox.t := arg_fun_0.(DoIntRound.sbox) in
    let* _ : unit := SBox.constrain var_3 var_2 in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_822_7 : Index.t) =>
      let var_7 : Felt.t := Array.read var_array (arg_for_822_7, tt) in
      let var_8 : bool := Bool.cmp BoolCmp.Eq var_7 var_felt_const_0 in
      let var_9 : Felt.t := M.cast_to_felt var_8 in
      let var_10 : Reg.t := var_3.(SBox.dollar_super) in
      let var_11 : NondetReg.t := var_10.(Reg.dollar_super) in
      let var_12 : Felt.t := var_11.(NondetReg.dollar_super) in
      let var_13 : Felt.t := BinOp.mul var_9 var_12 in
      let var_14 : bool := Bool.cmp BoolCmp.Eq var_7 var_felt_const_0 in
      let var_15 : Felt.t := M.cast_to_felt var_14 in
      let var_16 : Felt.t := BinOp.sub var_felt_const_1 var_15 in
      let var_17 : Index.t := M.cast_to_index var_7 in
      let var_18 : Felt.t := Array.read arg_fun_1 (var_17, tt) in
      let var_19 : Felt.t := BinOp.mul var_16 var_18 in
      let var_20 : Felt.t := BinOp.add var_13 var_19 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_822_7, tt) var_20 in
      M.yield tt
    ) in
    let var_4 : Array.t Felt.t [24]%nat := arg_fun_0.(DoIntRound.mat_in) in
    let* var_5 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_4 in
    let var_6 : MultiplyByMInt.t := arg_fun_0.(DoIntRound.dollar_temp) in
    let* _ : unit := MultiplyByMInt.constrain var_6 var_5 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) (arg_fun_1 : Felt.t) : M.t DoIntRound.t :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : DoIntRound.t := M.CreateStruct in
    let var_0 : Index.t := M.cast_to_index var_felt_const_0 in
    let var_1 : Felt.t := Array.read arg_fun_0 (var_0, tt) in
    let var_2 : Felt.t := BinOp.add var_1 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(DoIntRound.x) var_2 in
    let* var_3 : SBox.t := SBox.compute var_2 in
    let* _ : unit := M.FieldWrite var_self.(DoIntRound.sbox) var_3 in
    let var_4 : SBox.t := var_self.(DoIntRound.sbox) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_761_7 : Index.t) =>
      let var_9 : Felt.t := Array.read var_array (arg_for_761_7, tt) in
      let var_10 : bool := Bool.cmp BoolCmp.Eq var_9 var_felt_const_0 in
      let var_11 : Felt.t := M.cast_to_felt var_10 in
      let var_12 : Reg.t := var_4.(SBox.dollar_super) in
      let var_13 : NondetReg.t := var_12.(Reg.dollar_super) in
      let var_14 : Felt.t := var_13.(NondetReg.dollar_super) in
      let var_15 : Felt.t := BinOp.mul var_11 var_14 in
      let var_16 : bool := Bool.cmp BoolCmp.Eq var_9 var_felt_const_0 in
      let var_17 : Felt.t := M.cast_to_felt var_16 in
      let var_18 : Felt.t := BinOp.sub var_felt_const_1 var_17 in
      let var_19 : Index.t := M.cast_to_index var_9 in
      let var_20 : Felt.t := Array.read arg_fun_0 (var_19, tt) in
      let var_21 : Felt.t := BinOp.mul var_18 var_20 in
      let var_22 : Felt.t := BinOp.add var_15 var_21 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_761_7, tt) var_22 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoIntRound.mat_in) var_array_0 in
    let var_5 : Array.t Felt.t [24]%nat := var_self.(DoIntRound.mat_in) in
    let* var_6 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_5 in
    let* var_7 : MultiplyByMInt.t := MultiplyByMInt.compute var_6 in
    let* _ : unit := M.FieldWrite var_self.(DoIntRound.dollar_temp) var_7 in
    let var_8 : MultiplyByMInt.t := var_self.(DoIntRound.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(DoIntRound.dollar_super) var_8 in
    M.Pure var_self.
End DoIntRound.

Module DoIntRounds.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
    dollar_temp_0 : Array.t DoIntRound.t [21]%nat;
    dollar_array : Array.t Felt.t [21]%nat;
    dollar_temp : INT_ROUND_CONSTANTS.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : DoIntRounds.t) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t unit :=
    let var_c21 : Index.t := 21%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_0 : INT_ROUND_CONSTANTS.t := arg_fun_0.(DoIntRounds.dollar_temp) in
    let* _ : unit := INT_ROUND_CONSTANTS.constrain var_0 in
    let var_1 : Array.t Felt.t [21]%nat := var_0.(INT_ROUND_CONSTANTS.dollar_super) in
    let var_array : Array.t Felt.t [21]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c21 (* step *) var_c1 (fun (arg_for_891_7 : Index.t) =>
      let var_4 : Felt.t := Array.read var_1 (arg_for_891_7, tt) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_891_7, tt) var_4 in
      M.yield tt
    ) in
    let var_2 : Array.t Felt.t [21]%nat := arg_fun_0.(DoIntRounds.dollar_array) in
    let* var_3 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c21 (* step *) var_c1 (fun (arg_for_896_12 : Index.t) (arg_for_896_12 : Array.t Felt.t [24]%nat) =>
      let var_4 : Felt.t := Array.read var_2 (arg_for_896_12, tt) in
      let var_5 : Array.t DoIntRound.t [21]%nat := arg_fun_0.(DoIntRounds.dollar_temp_0) in
      let var_6 : Array.t DoIntRound.t [21]%nat := arg_fun_0.(DoIntRounds.dollar_temp_0) in
      let var_7 : DoIntRound.t := Array.read var_6 (arg_for_896_12, tt) in
      let* _ : unit := DoIntRound.constrain var_7 arg_for_896_12 var_4 in
      let var_8 : MultiplyByMInt.t := var_7.(DoIntRound.dollar_super) in
      let var_9 : Array.t Felt.t [24]%nat := var_8.(MultiplyByMInt.dollar_super) in
      let* var_10 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_9 in
      M.yield var_10
    ) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) : M.t DoIntRounds.t :=
    let var_c21 : Index.t := 21%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : DoIntRounds.t := M.CreateStruct in
    let* var_0 : INT_ROUND_CONSTANTS.t := INT_ROUND_CONSTANTS.compute in
    let* _ : unit := M.FieldWrite var_self.(DoIntRounds.dollar_temp) var_0 in
    let var_1 : INT_ROUND_CONSTANTS.t := var_self.(DoIntRounds.dollar_temp) in
    let var_2 : Array.t Felt.t [21]%nat := var_1.(INT_ROUND_CONSTANTS.dollar_super) in
    let var_array : Array.t Felt.t [21]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c21 (* step *) var_c1 (fun (arg_for_861_7 : Index.t) =>
      let var_5 : Felt.t := Array.read var_2 (arg_for_861_7, tt) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_861_7, tt) var_5 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoIntRounds.dollar_array) var_array in
    let var_3 : Array.t Felt.t [21]%nat := var_self.(DoIntRounds.dollar_array) in
    let* var_4 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c21 (* step *) var_c1 (fun (arg_for_867_12 : Index.t) (arg_for_867_12 : Array.t Felt.t [24]%nat) =>
      let var_5 : Felt.t := Array.read var_3 (arg_for_867_12, tt) in
      let* var_6 : DoIntRound.t := DoIntRound.compute arg_for_867_12 var_5 in
      let var_7 : Array.t DoIntRound.t [21]%nat := var_self.(DoIntRounds.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_7 (arg_for_867_12, tt) var_6 in
      let* _ : unit := M.FieldWrite var_self.(DoIntRounds.dollar_temp_0) var_7 in
      let var_8 : Array.t DoIntRound.t [21]%nat := var_self.(DoIntRounds.dollar_temp_0) in
      let var_9 : DoIntRound.t := Array.read var_8 (arg_for_867_12, tt) in
      let var_10 : MultiplyByMInt.t := var_9.(DoIntRound.dollar_super) in
      let var_11 : Array.t Felt.t [24]%nat := var_10.(MultiplyByMInt.dollar_super) in
      let* var_12 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_11 in
      M.yield var_12
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoIntRounds.dollar_super) var_4 in
    M.Pure var_self.
End DoIntRounds.

Module MultiplyByCirculant.
  Record t : Set := {
    dollar_super : Array.t Felt.t [4]%nat;
    t7 : Felt.t;
    t6 : Felt.t;
    t5 : Felt.t;
    t4 : Felt.t;
    t3 : Felt.t;
    t2 : Felt.t;
    t1 : Felt.t;
    t0 : Felt.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      t7 := map_mod α.(t7);
      t6 := map_mod α.(t6);
      t5 := map_mod α.(t5);
      t4 := map_mod α.(t4);
      t3 := map_mod α.(t3);
      t2 := map_mod α.(t2);
      t1 := map_mod α.(t1);
      t0 := map_mod α.(t0);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : MultiplyByCirculant.t) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t unit :=
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : Index.t := M.cast_to_index var_felt_const_0 in
    let var_1 : Felt.t := Array.read arg_fun_1 (var_0, tt) in
    let var_2 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_3 : Felt.t := Array.read arg_fun_1 (var_2, tt) in
    let var_4 : Index.t := M.cast_to_index var_felt_const_2 in
    let var_5 : Felt.t := Array.read arg_fun_1 (var_4, tt) in
    let var_6 : Index.t := M.cast_to_index var_felt_const_3 in
    let var_7 : Felt.t := Array.read arg_fun_1 (var_6, tt) in
    let var_8 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_9 : Felt.t := Array.read arg_fun_1 (var_8, tt) in
    let var_10 : Index.t := M.cast_to_index var_felt_const_3 in
    let var_11 : Felt.t := Array.read arg_fun_1 (var_10, tt) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [4]%nat) : M.t MultiplyByCirculant.t :=
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : MultiplyByCirculant.t := M.CreateStruct in
    let var_0 : Index.t := M.cast_to_index var_felt_const_0 in
    let var_1 : Felt.t := Array.read arg_fun_0 (var_0, tt) in
    let var_2 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_3 : Felt.t := Array.read arg_fun_0 (var_2, tt) in
    let var_4 : Felt.t := BinOp.add var_1 var_3 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t0) var_4 in
    let var_5 : Index.t := M.cast_to_index var_felt_const_2 in
    let var_6 : Felt.t := Array.read arg_fun_0 (var_5, tt) in
    let var_7 : Index.t := M.cast_to_index var_felt_const_3 in
    let var_8 : Felt.t := Array.read arg_fun_0 (var_7, tt) in
    let var_9 : Felt.t := BinOp.add var_6 var_8 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t1) var_9 in
    let var_10 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_11 : Felt.t := Array.read arg_fun_0 (var_10, tt) in
    let var_12 : Felt.t := BinOp.mul var_11 var_felt_const_2 in
    let var_13 : Felt.t := BinOp.add var_12 var_9 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t2) var_13 in
    let var_14 : Index.t := M.cast_to_index var_felt_const_3 in
    let var_15 : Felt.t := Array.read arg_fun_0 (var_14, tt) in
    let var_16 : Felt.t := BinOp.mul var_15 var_felt_const_2 in
    let var_17 : Felt.t := BinOp.add var_16 var_4 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t3) var_17 in
    let var_18 : Felt.t := BinOp.mul var_9 var_felt_const_4 in
    let var_19 : Felt.t := BinOp.add var_18 var_17 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t4) var_19 in
    let var_20 : Felt.t := BinOp.mul var_4 var_felt_const_4 in
    let var_21 : Felt.t := BinOp.add var_20 var_13 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t5) var_21 in
    let var_22 : Felt.t := BinOp.add var_17 var_21 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t6) var_22 in
    let var_23 : Felt.t := BinOp.add var_13 var_19 in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.t7) var_23 in
    let var_array : Array.t Felt.t [4]%nat := Array.new [var_22; var_21; var_23; var_19] in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByCirculant.dollar_super) var_array in
    M.Pure var_self.
End MultiplyByCirculant.

Module ReduceVec4.
  Record t : Set := {
    dollar_super : Array.t Felt.t [4]%nat;
    dollar_array : Array.t Felt.t [4]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : ReduceVec4.t) (arg_fun_1 : Array.t Felt.t [4]%nat) (arg_fun_2 : Array.t Felt.t [4]%nat) : M.t unit :=
    let var_c4 : Index.t := 4%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_array : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
    let var_array_0 : Array.t Felt.t [4]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_1021_7 : Index.t) =>
      let var_1 : Felt.t := Array.read var_array (arg_for_1021_7, tt) in
      let var_2 : Index.t := M.cast_to_index var_1 in
      let var_3 : Felt.t := Array.read arg_fun_1 (var_2, tt) in
      let var_4 : Index.t := M.cast_to_index var_1 in
      let var_5 : Felt.t := Array.read arg_fun_2 (var_4, tt) in
      let var_6 : Felt.t := BinOp.add var_3 var_5 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1021_7, tt) var_6 in
      M.yield tt
    ) in
    let var_0 : Array.t Felt.t [4]%nat := arg_fun_0.(ReduceVec4.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [4]%nat) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t ReduceVec4.t :=
    let var_c4 : Index.t := 4%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : ReduceVec4.t := M.CreateStruct in
    let var_array : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
    let var_array_0 : Array.t Felt.t [4]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_997_7 : Index.t) =>
      let var_1 : Felt.t := Array.read var_array (arg_for_997_7, tt) in
      let var_2 : Index.t := M.cast_to_index var_1 in
      let var_3 : Felt.t := Array.read arg_fun_0 (var_2, tt) in
      let var_4 : Index.t := M.cast_to_index var_1 in
      let var_5 : Felt.t := Array.read arg_fun_1 (var_4, tt) in
      let var_6 : Felt.t := BinOp.add var_3 var_5 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_997_7, tt) var_6 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(ReduceVec4.dollar_array) var_array_0 in
    let var_0 : Array.t Felt.t [4]%nat := var_self.(ReduceVec4.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(ReduceVec4.dollar_super) var_0 in
    M.Pure var_self.
End ReduceVec4.

Module MultiplyByMExt.
  Record t : Set := {
    dollar_super : Array.t block$.t [24]%nat;
    dollar_temp_2 : Array.t block$.t [24]%nat;
    g : Array.t Felt.t [24]%nat;
    j : Array.t BitAnd.t [24]%nat;
    dollar_array : Array.t block$.t [24]%nat;
    dollar_temp_1 : Array.t ReduceVec4.t [6]%nat;
    dollar_temp_0 : Array.t block$_2.t [6]%nat;
    dollar_temp : Array.t MultiplyByCirculant.t [6]%nat;
    chunk : Array.t Felt.t [6; 4]%nat;
    grouped : Array.t block$_2.t [6]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_2 := map_mod α.(dollar_temp_2);
      g := map_mod α.(g);
      j := map_mod α.(j);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      chunk := map_mod α.(chunk);
      grouped := map_mod α.(grouped);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : MultiplyByMExt.t) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t unit :=
    let var_felt_const_1509949441 : Felt.t := UnOp.from 1509949441 in
    let var_c24 : Index.t := 24%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_c4 : Index.t := 4%nat in
    let var_c6 : Index.t := 6%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_array : Array.t Felt.t [6]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5] in
    let var_array_0 : Array.t block$_2.t [6]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c6 (* step *) var_c1 (fun (arg_for_1207_7 : Index.t) =>
      let var_3 : Felt.t := Array.read var_array (arg_for_1207_7, tt) in
      let var_array_4 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
      let var_array_5 : Array.t Felt.t [4]%nat := Array.new [] in
      let* _ : unit := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_1211_9 : Index.t) =>
        let var_15 : Felt.t := Array.read var_array_4 (arg_for_1211_9, tt) in
        let var_16 : Felt.t := BinOp.mul var_3 var_felt_const_4 in
        let var_17 : Felt.t := BinOp.add var_16 var_15 in
        let var_18 : Index.t := M.cast_to_index var_17 in
        let var_19 : Felt.t := Array.read arg_fun_1 (var_18, tt) in
        let* _ : unit := M.ArrayWrite var_array_5 (arg_for_1211_9, tt) var_19 in
        M.yield tt
      ) in
      let var_4 : Array.t Felt.t [6; 4]%nat := arg_fun_0.(MultiplyByMExt.chunk) in
      let var_5 : Array.t Felt.t [6; 4]%nat := arg_fun_0.(MultiplyByMExt.chunk) in
      let var_6 : Array.t Felt.t [4]%nat := Array.extract (Ns := [_]) var_5 (arg_for_1207_7, tt) in
      let var_7 : Array.t MultiplyByCirculant.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp) in
      let var_8 : Array.t MultiplyByCirculant.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp) in
      let var_9 : MultiplyByCirculant.t := Array.read var_8 (arg_for_1207_7, tt) in
      let* _ : unit := MultiplyByCirculant.constrain var_9 var_6 in
      let var_10 : Array.t Felt.t [6; 4]%nat := arg_fun_0.(MultiplyByMExt.chunk) in
      let var_11 : Array.t Felt.t [4]%nat := Array.extract (Ns := [_]) var_10 (arg_for_1207_7, tt) in
      let var_12 : Array.t block$_2.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_0) in
      let var_13 : Array.t block$_2.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_0) in
      let var_14 : block$_2.t := Array.read var_13 (arg_for_1207_7, tt) in
      let* _ : unit := blockdollar__2.constrain var_14 var_9 var_11 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1207_7, tt) var_14 in
      M.yield tt
    ) in
    let var_0 : Array.t block$_2.t [6]%nat := arg_fun_0.(MultiplyByMExt.grouped) in
    let var_array_1 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_0; var_felt_const_0; var_felt_const_0] in
    let* var_1 : Array.t Felt.t [4]%nat := M.for_ var_c0 (* to *) var_c6 (* step *) var_c1 (fun (arg_for_1236_12 : Index.t) (arg_for_1236_12 : Array.t Felt.t [4]%nat) =>
      let var_3 : block$_2.t := Array.read var_0 (arg_for_1236_12, tt) in
      let var_4 : MultiplyByCirculant.t := var_3.(block$_2.dollar_super) in
      let var_5 : Array.t Felt.t [4]%nat := var_4.(MultiplyByCirculant.dollar_super) in
      let* var_6 : Array.t Felt.t [4]%nat := UnOp.unifiable_cast var_5 in
      let var_7 : Array.t ReduceVec4.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_1) in
      let var_8 : Array.t ReduceVec4.t [6]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_1) in
      let var_9 : ReduceVec4.t := Array.read var_8 (arg_for_1236_12, tt) in
      let* _ : unit := ReduceVec4.constrain var_9 arg_for_1236_12 var_6 in
      let var_10 : Array.t Felt.t [4]%nat := var_9.(ReduceVec4.dollar_super) in
      let* var_11 : Array.t Felt.t [4]%nat := UnOp.unifiable_cast var_10 in
      M.yield var_11
    ) in
    let var_array_2 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_3 : Array.t block$.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1251_7 : Index.t) =>
      let var_3 : Felt.t := Array.read var_array_2 (arg_for_1251_7, tt) in
      let var_4 : Array.t BitAnd.t [24]%nat := arg_fun_0.(MultiplyByMExt.j) in
      let var_5 : Array.t BitAnd.t [24]%nat := arg_fun_0.(MultiplyByMExt.j) in
      let var_6 : BitAnd.t := Array.read var_5 (arg_for_1251_7, tt) in
      let* _ : unit := BitAnd.constrain var_6 var_3 var_felt_const_3 in
      let var_7 : Felt.t := var_6.(BitAnd.dollar_super) in
      let var_8 : Felt.t := BinOp.sub var_3 var_7 in
      let var_9 : Felt.t := BinOp.mul var_8 var_felt_const_1509949441 in
      let var_10 : Array.t Felt.t [24]%nat := arg_fun_0.(MultiplyByMExt.g) in
      let var_11 : Index.t := M.cast_to_index var_9 in
      let var_12 : block$_2.t := Array.read var_0 (var_11, tt) in
      let var_13 : MultiplyByCirculant.t := var_12.(block$_2.dollar_super) in
      let var_14 : Array.t Felt.t [4]%nat := var_13.(MultiplyByCirculant.dollar_super) in
      let var_15 : Felt.t := var_6.(BitAnd.dollar_super) in
      let var_16 : Index.t := M.cast_to_index var_15 in
      let var_17 : Felt.t := Array.read var_14 (var_16, tt) in
      let var_18 : Felt.t := var_6.(BitAnd.dollar_super) in
      let var_19 : Index.t := M.cast_to_index var_18 in
      let var_20 : Felt.t := Array.read var_1 (var_19, tt) in
      let var_21 : Felt.t := BinOp.add var_17 var_20 in
      let var_22 : Array.t Felt.t [24]%nat := arg_fun_0.(MultiplyByMExt.g) in
      let var_23 : Felt.t := Array.read var_22 (arg_for_1251_7, tt) in
      let var_24 : Array.t BitAnd.t [24]%nat := arg_fun_0.(MultiplyByMExt.j) in
      let var_25 : BitAnd.t := Array.read var_24 (arg_for_1251_7, tt) in
      let var_26 : Array.t block$.t [24]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_2) in
      let var_27 : Array.t block$.t [24]%nat := arg_fun_0.(MultiplyByMExt.dollar_temp_2) in
      let var_28 : block$.t := Array.read var_27 (arg_for_1251_7, tt) in
      let* _ : unit := blockdollar_.constrain var_28 var_21 var_23 var_25 in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_1251_7, tt) var_28 in
      M.yield tt
    ) in
    let var_2 : Array.t block$.t [24]%nat := arg_fun_0.(MultiplyByMExt.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) : M.t MultiplyByMExt.t :=
    let var_felt_const_1509949441 : Felt.t := UnOp.from 1509949441 in
    let var_c24 : Index.t := 24%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_c4 : Index.t := 4%nat in
    let var_c6 : Index.t := 6%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : MultiplyByMExt.t := M.CreateStruct in
    let var_array : Array.t Felt.t [6]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5] in
    let var_array_0 : Array.t block$_2.t [6]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c6 (* step *) var_c1 (fun (arg_for_1079_7 : Index.t) =>
      let var_3 : Felt.t := Array.read var_array (arg_for_1079_7, tt) in
      let var_array_4 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
      let var_array_5 : Array.t Felt.t [4]%nat := Array.new [] in
      let* _ : unit := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_1083_9 : Index.t) =>
        let var_17 : Felt.t := Array.read var_array_4 (arg_for_1083_9, tt) in
        let var_18 : Felt.t := BinOp.mul var_3 var_felt_const_4 in
        let var_19 : Felt.t := BinOp.add var_18 var_17 in
        let var_20 : Index.t := M.cast_to_index var_19 in
        let var_21 : Felt.t := Array.read arg_fun_0 (var_20, tt) in
        let* _ : unit := M.ArrayWrite var_array_5 (arg_for_1083_9, tt) var_21 in
        M.yield tt
      ) in
      let var_4 : Array.t Felt.t [6; 4]%nat := var_self.(MultiplyByMExt.chunk) in
      let* _ : unit := Array.insert var_4 (arg_for_1079_7, tt) var_array_5 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.chunk) var_4 in
      let var_5 : Array.t Felt.t [6; 4]%nat := var_self.(MultiplyByMExt.chunk) in
      let var_6 : Array.t Felt.t [4]%nat := Array.extract (Ns := [_]) var_5 (arg_for_1079_7, tt) in
      let* var_7 : MultiplyByCirculant.t := MultiplyByCirculant.compute var_6 in
      let var_8 : Array.t MultiplyByCirculant.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_8 (arg_for_1079_7, tt) var_7 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_temp) var_8 in
      let var_9 : Array.t MultiplyByCirculant.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp) in
      let var_10 : MultiplyByCirculant.t := Array.read var_9 (arg_for_1079_7, tt) in
      let var_11 : Array.t Felt.t [6; 4]%nat := var_self.(MultiplyByMExt.chunk) in
      let var_12 : Array.t Felt.t [4]%nat := Array.extract (Ns := [_]) var_11 (arg_for_1079_7, tt) in
      let* var_13 : block$_2.t := blockdollar__2.compute var_10 var_12 in
      let var_14 : Array.t block$_2.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_14 (arg_for_1079_7, tt) var_13 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_temp_0) var_14 in
      let var_15 : Array.t block$_2.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp_0) in
      let var_16 : block$_2.t := Array.read var_15 (arg_for_1079_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1079_7, tt) var_16 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.grouped) var_array_0 in
    let var_0 : Array.t block$_2.t [6]%nat := var_self.(MultiplyByMExt.grouped) in
    let var_array_1 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0; var_felt_const_0; var_felt_const_0; var_felt_const_0] in
    let* var_1 : Array.t Felt.t [4]%nat := M.for_ var_c0 (* to *) var_c6 (* step *) var_c1 (fun (arg_for_1115_12 : Index.t) (arg_for_1115_12 : Array.t Felt.t [4]%nat) =>
      let var_3 : block$_2.t := Array.read var_0 (arg_for_1115_12, tt) in
      let var_4 : MultiplyByCirculant.t := var_3.(block$_2.dollar_super) in
      let var_5 : Array.t Felt.t [4]%nat := var_4.(MultiplyByCirculant.dollar_super) in
      let* var_6 : Array.t Felt.t [4]%nat := UnOp.unifiable_cast var_5 in
      let* var_7 : ReduceVec4.t := ReduceVec4.compute arg_for_1115_12 var_6 in
      let var_8 : Array.t ReduceVec4.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp_1) in
      let* _ : unit := M.ArrayWrite var_8 (arg_for_1115_12, tt) var_7 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_temp_1) var_8 in
      let var_9 : Array.t ReduceVec4.t [6]%nat := var_self.(MultiplyByMExt.dollar_temp_1) in
      let var_10 : ReduceVec4.t := Array.read var_9 (arg_for_1115_12, tt) in
      let var_11 : Array.t Felt.t [4]%nat := var_10.(ReduceVec4.dollar_super) in
      let* var_12 : Array.t Felt.t [4]%nat := UnOp.unifiable_cast var_11 in
      M.yield var_12
    ) in
    let var_array_2 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_3 : Array.t block$.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1132_7 : Index.t) =>
      let var_3 : Felt.t := Array.read var_array_2 (arg_for_1132_7, tt) in
      let* var_4 : BitAnd.t := BitAnd.compute var_3 var_felt_const_3 in
      let var_5 : Array.t BitAnd.t [24]%nat := var_self.(MultiplyByMExt.j) in
      let* _ : unit := M.ArrayWrite var_5 (arg_for_1132_7, tt) var_4 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.j) var_5 in
      let var_6 : Array.t BitAnd.t [24]%nat := var_self.(MultiplyByMExt.j) in
      let var_7 : BitAnd.t := Array.read var_6 (arg_for_1132_7, tt) in
      let var_8 : Felt.t := var_7.(BitAnd.dollar_super) in
      let var_9 : Felt.t := BinOp.sub var_3 var_8 in
      let var_10 : Felt.t := BinOp.mul var_9 var_felt_const_1509949441 in
      let var_11 : Array.t Felt.t [24]%nat := var_self.(MultiplyByMExt.g) in
      let* _ : unit := M.ArrayWrite var_11 (arg_for_1132_7, tt) var_10 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.g) var_11 in
      let var_12 : Index.t := M.cast_to_index var_10 in
      let var_13 : block$_2.t := Array.read var_0 (var_12, tt) in
      let var_14 : MultiplyByCirculant.t := var_13.(block$_2.dollar_super) in
      let var_15 : Array.t Felt.t [4]%nat := var_14.(MultiplyByCirculant.dollar_super) in
      let var_16 : Felt.t := var_7.(BitAnd.dollar_super) in
      let var_17 : Index.t := M.cast_to_index var_16 in
      let var_18 : Felt.t := Array.read var_15 (var_17, tt) in
      let var_19 : Felt.t := var_7.(BitAnd.dollar_super) in
      let var_20 : Index.t := M.cast_to_index var_19 in
      let var_21 : Felt.t := Array.read var_1 (var_20, tt) in
      let var_22 : Felt.t := BinOp.add var_18 var_21 in
      let var_23 : Array.t Felt.t [24]%nat := var_self.(MultiplyByMExt.g) in
      let var_24 : Felt.t := Array.read var_23 (arg_for_1132_7, tt) in
      let var_25 : Array.t BitAnd.t [24]%nat := var_self.(MultiplyByMExt.j) in
      let var_26 : BitAnd.t := Array.read var_25 (arg_for_1132_7, tt) in
      let* var_27 : block$.t := blockdollar_.compute var_22 var_24 var_26 in
      let var_28 : Array.t block$.t [24]%nat := var_self.(MultiplyByMExt.dollar_temp_2) in
      let* _ : unit := M.ArrayWrite var_28 (arg_for_1132_7, tt) var_27 in
      let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_temp_2) var_28 in
      let var_29 : Array.t block$.t [24]%nat := var_self.(MultiplyByMExt.dollar_temp_2) in
      let var_30 : block$.t := Array.read var_29 (arg_for_1132_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_1132_7, tt) var_30 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_array) var_array_3 in
    let var_2 : Array.t block$.t [24]%nat := var_self.(MultiplyByMExt.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(MultiplyByMExt.dollar_super) var_2 in
    M.Pure var_self.
End MultiplyByMExt.

Module ExtRoundConstants.
  Record t : Set := {
    dollar_super : Array.t Felt.t [8; 24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : ExtRoundConstants.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} : M.t ExtRoundConstants.t :=
    let var_c7 : Index.t := 7%nat in
    let var_c6 : Index.t := 6%nat in
    let var_c5 : Index.t := 5%nat in
    let var_c4 : Index.t := 4%nat in
    let var_c3 : Index.t := 3%nat in
    let var_c2 : Index.t := 2%nat in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let var_felt_const_1380248020 : Felt.t := UnOp.from 1380248020 in
    let var_felt_const_1608891156 : Felt.t := UnOp.from 1608891156 in
    let var_felt_const_1672219447 : Felt.t := UnOp.from 1672219447 in
    let var_felt_const_1262312258 : Felt.t := UnOp.from 1262312258 in
    let var_felt_const_162506101 : Felt.t := UnOp.from 162506101 in
    let var_felt_const_809508074 : Felt.t := UnOp.from 809508074 in
    let var_felt_const_1303271640 : Felt.t := UnOp.from 1303271640 in
    let var_felt_const_1393671120 : Felt.t := UnOp.from 1393671120 in
    let var_felt_const_641665156 : Felt.t := UnOp.from 641665156 in
    let var_felt_const_1090783436 : Felt.t := UnOp.from 1090783436 in
    let var_felt_const_1111203133 : Felt.t := UnOp.from 1111203133 in
    let var_felt_const_1296144415 : Felt.t := UnOp.from 1296144415 in
    let var_felt_const_202271745 : Felt.t := UnOp.from 202271745 in
    let var_felt_const_459826664 : Felt.t := UnOp.from 459826664 in
    let var_felt_const_781141772 : Felt.t := UnOp.from 781141772 in
    let var_felt_const_1832911930 : Felt.t := UnOp.from 1832911930 in
    let var_felt_const_228520958 : Felt.t := UnOp.from 228520958 in
    let var_felt_const_813674331 : Felt.t := UnOp.from 813674331 in
    let var_felt_const_1889898 : Felt.t := UnOp.from 1889898 in
    let var_felt_const_1124078057 : Felt.t := UnOp.from 1124078057 in
    let var_felt_const_738091882 : Felt.t := UnOp.from 738091882 in
    let var_felt_const_1003792297 : Felt.t := UnOp.from 1003792297 in
    let var_felt_const_1896271507 : Felt.t := UnOp.from 1896271507 in
    let var_felt_const_1206940496 : Felt.t := UnOp.from 1206940496 in
    let var_felt_const_1827572010 : Felt.t := UnOp.from 1827572010 in
    let var_felt_const_1507649755 : Felt.t := UnOp.from 1507649755 in
    let var_felt_const_1042892522 : Felt.t := UnOp.from 1042892522 in
    let var_felt_const_760115692 : Felt.t := UnOp.from 760115692 in
    let var_felt_const_1841795381 : Felt.t := UnOp.from 1841795381 in
    let var_felt_const_457372011 : Felt.t := UnOp.from 457372011 in
    let var_felt_const_1748789933 : Felt.t := UnOp.from 1748789933 in
    let var_felt_const_1478577620 : Felt.t := UnOp.from 1478577620 in
    let var_felt_const_76770019 : Felt.t := UnOp.from 76770019 in
    let var_felt_const_1293938517 : Felt.t := UnOp.from 1293938517 in
    let var_felt_const_1150410028 : Felt.t := UnOp.from 1150410028 in
    let var_felt_const_1065075039 : Felt.t := UnOp.from 1065075039 in
    let var_felt_const_1198261138 : Felt.t := UnOp.from 1198261138 in
    let var_felt_const_59510015 : Felt.t := UnOp.from 59510015 in
    let var_felt_const_1402624179 : Felt.t := UnOp.from 1402624179 in
    let var_felt_const_158646617 : Felt.t := UnOp.from 158646617 in
    let var_felt_const_890243564 : Felt.t := UnOp.from 890243564 in
    let var_felt_const_1463323727 : Felt.t := UnOp.from 1463323727 in
    let var_felt_const_1080533265 : Felt.t := UnOp.from 1080533265 in
    let var_felt_const_192082241 : Felt.t := UnOp.from 192082241 in
    let var_felt_const_1891637550 : Felt.t := UnOp.from 1891637550 in
    let var_felt_const_1950429111 : Felt.t := UnOp.from 1950429111 in
    let var_felt_const_1663353317 : Felt.t := UnOp.from 1663353317 in
    let var_felt_const_1567618575 : Felt.t := UnOp.from 1567618575 in
    let var_felt_const_150307788 : Felt.t := UnOp.from 150307788 in
    let var_felt_const_755691969 : Felt.t := UnOp.from 755691969 in
    let var_felt_const_1715719711 : Felt.t := UnOp.from 1715719711 in
    let var_felt_const_1545325389 : Felt.t := UnOp.from 1545325389 in
    let var_felt_const_989618631 : Felt.t := UnOp.from 989618631 in
    let var_felt_const_1401020792 : Felt.t := UnOp.from 1401020792 in
    let var_felt_const_930036496 : Felt.t := UnOp.from 930036496 in
    let var_felt_const_238616145 : Felt.t := UnOp.from 238616145 in
    let var_felt_const_1006235079 : Felt.t := UnOp.from 1006235079 in
    let var_felt_const_942439428 : Felt.t := UnOp.from 942439428 in
    let var_felt_const_1649953458 : Felt.t := UnOp.from 1649953458 in
    let var_felt_const_1647665372 : Felt.t := UnOp.from 1647665372 in
    let var_felt_const_708123747 : Felt.t := UnOp.from 708123747 in
    let var_felt_const_925018226 : Felt.t := UnOp.from 925018226 in
    let var_felt_const_78845751 : Felt.t := UnOp.from 78845751 in
    let var_felt_const_1889603648 : Felt.t := UnOp.from 1889603648 in
    let var_felt_const_993455846 : Felt.t := UnOp.from 993455846 in
    let var_felt_const_140621810 : Felt.t := UnOp.from 140621810 in
    let var_felt_const_117294666 : Felt.t := UnOp.from 117294666 in
    let var_felt_const_790726260 : Felt.t := UnOp.from 790726260 in
    let var_felt_const_1213686459 : Felt.t := UnOp.from 1213686459 in
    let var_felt_const_390340387 : Felt.t := UnOp.from 390340387 in
    let var_felt_const_714957516 : Felt.t := UnOp.from 714957516 in
    let var_felt_const_1209164052 : Felt.t := UnOp.from 1209164052 in
    let var_felt_const_1040977421 : Felt.t := UnOp.from 1040977421 in
    let var_felt_const_1792450386 : Felt.t := UnOp.from 1792450386 in
    let var_felt_const_1470845646 : Felt.t := UnOp.from 1470845646 in
    let var_felt_const_1363837384 : Felt.t := UnOp.from 1363837384 in
    let var_felt_const_1878280202 : Felt.t := UnOp.from 1878280202 in
    let var_felt_const_434078361 : Felt.t := UnOp.from 434078361 in
    let var_felt_const_1946596189 : Felt.t := UnOp.from 1946596189 in
    let var_felt_const_875839332 : Felt.t := UnOp.from 875839332 in
    let var_felt_const_463976218 : Felt.t := UnOp.from 463976218 in
    let var_felt_const_976057819 : Felt.t := UnOp.from 976057819 in
    let var_felt_const_48375137 : Felt.t := UnOp.from 48375137 in
    let var_felt_const_1549779579 : Felt.t := UnOp.from 1549779579 in
    let var_felt_const_1679178250 : Felt.t := UnOp.from 1679178250 in
    let var_felt_const_530151394 : Felt.t := UnOp.from 530151394 in
    let var_felt_const_1629316321 : Felt.t := UnOp.from 1629316321 in
    let var_felt_const_1854174607 : Felt.t := UnOp.from 1854174607 in
    let var_felt_const_720724951 : Felt.t := UnOp.from 720724951 in
    let var_felt_const_14387587 : Felt.t := UnOp.from 14387587 in
    let var_felt_const_1883820770 : Felt.t := UnOp.from 1883820770 in
    let var_felt_const_205609311 : Felt.t := UnOp.from 205609311 in
    let var_felt_const_1136469704 : Felt.t := UnOp.from 1136469704 in
    let var_felt_const_1439947916 : Felt.t := UnOp.from 1439947916 in
    let var_felt_const_723038058 : Felt.t := UnOp.from 723038058 in
    let var_felt_const_53041581 : Felt.t := UnOp.from 53041581 in
    let var_felt_const_1291790245 : Felt.t := UnOp.from 1291790245 in
    let var_felt_const_1781980094 : Felt.t := UnOp.from 1781980094 in
    let var_felt_const_273790406 : Felt.t := UnOp.from 273790406 in
    let var_felt_const_1239734761 : Felt.t := UnOp.from 1239734761 in
    let var_felt_const_1221257987 : Felt.t := UnOp.from 1221257987 in
    let var_felt_const_51256176 : Felt.t := UnOp.from 51256176 in
    let var_felt_const_172614232 : Felt.t := UnOp.from 172614232 in
    let var_felt_const_306391314 : Felt.t := UnOp.from 306391314 in
    let var_felt_const_1647670797 : Felt.t := UnOp.from 1647670797 in
    let var_felt_const_53007114 : Felt.t := UnOp.from 53007114 in
    let var_felt_const_1269493554 : Felt.t := UnOp.from 1269493554 in
    let var_felt_const_1338899225 : Felt.t := UnOp.from 1338899225 in
    let var_felt_const_1740472809 : Felt.t := UnOp.from 1740472809 in
    let var_felt_const_1454563174 : Felt.t := UnOp.from 1454563174 in
    let var_felt_const_204228775 : Felt.t := UnOp.from 204228775 in
    let var_felt_const_588764636 : Felt.t := UnOp.from 588764636 in
    let var_felt_const_1718628547 : Felt.t := UnOp.from 1718628547 in
    let var_felt_const_427731030 : Felt.t := UnOp.from 427731030 in
    let var_felt_const_825405577 : Felt.t := UnOp.from 825405577 in
    let var_felt_const_342857858 : Felt.t := UnOp.from 342857858 in
    let var_felt_const_1290028279 : Felt.t := UnOp.from 1290028279 in
    let var_felt_const_608401422 : Felt.t := UnOp.from 608401422 in
    let var_felt_const_1587822577 : Felt.t := UnOp.from 1587822577 in
    let var_felt_const_128479034 : Felt.t := UnOp.from 128479034 in
    let var_felt_const_862495875 : Felt.t := UnOp.from 862495875 in
    let var_felt_const_447555988 : Felt.t := UnOp.from 447555988 in
    let var_felt_const_1910423126 : Felt.t := UnOp.from 1910423126 in
    let var_felt_const_1099252725 : Felt.t := UnOp.from 1099252725 in
    let var_felt_const_1584033957 : Felt.t := UnOp.from 1584033957 in
    let var_felt_const_1079030649 : Felt.t := UnOp.from 1079030649 in
    let var_felt_const_1622328571 : Felt.t := UnOp.from 1622328571 in
    let var_felt_const_1908416316 : Felt.t := UnOp.from 1908416316 in
    let var_felt_const_1549062383 : Felt.t := UnOp.from 1549062383 in
    let var_felt_const_623051854 : Felt.t := UnOp.from 623051854 in
    let var_felt_const_162510541 : Felt.t := UnOp.from 162510541 in
    let var_felt_const_1608853840 : Felt.t := UnOp.from 1608853840 in
    let var_felt_const_538103555 : Felt.t := UnOp.from 538103555 in
    let var_felt_const_1424297384 : Felt.t := UnOp.from 1424297384 in
    let var_felt_const_552696906 : Felt.t := UnOp.from 552696906 in
    let var_felt_const_946500736 : Felt.t := UnOp.from 946500736 in
    let var_felt_const_1215259350 : Felt.t := UnOp.from 1215259350 in
    let var_felt_const_855276054 : Felt.t := UnOp.from 855276054 in
    let var_felt_const_1664590951 : Felt.t := UnOp.from 1664590951 in
    let var_felt_const_217046702 : Felt.t := UnOp.from 217046702 in
    let var_felt_const_142102402 : Felt.t := UnOp.from 142102402 in
    let var_felt_const_1257820264 : Felt.t := UnOp.from 1257820264 in
    let var_felt_const_27129487 : Felt.t := UnOp.from 27129487 in
    let var_felt_const_1147522062 : Felt.t := UnOp.from 1147522062 in
    let var_felt_const_989176635 : Felt.t := UnOp.from 989176635 in
    let var_felt_const_241306552 : Felt.t := UnOp.from 241306552 in
    let var_felt_const_1507936940 : Felt.t := UnOp.from 1507936940 in
    let var_felt_const_1687379185 : Felt.t := UnOp.from 1687379185 in
    let var_felt_const_1150912935 : Felt.t := UnOp.from 1150912935 in
    let var_felt_const_1917549072 : Felt.t := UnOp.from 1917549072 in
    let var_felt_const_1201063290 : Felt.t := UnOp.from 1201063290 in
    let var_felt_const_395622276 : Felt.t := UnOp.from 395622276 in
    let var_felt_const_1997503974 : Felt.t := UnOp.from 1997503974 in
    let var_felt_const_716894289 : Felt.t := UnOp.from 716894289 in
    let var_felt_const_897025192 : Felt.t := UnOp.from 897025192 in
    let var_felt_const_1282239129 : Felt.t := UnOp.from 1282239129 in
    let var_felt_const_1737016378 : Felt.t := UnOp.from 1737016378 in
    let var_felt_const_686842369 : Felt.t := UnOp.from 686842369 in
    let var_felt_const_622609176 : Felt.t := UnOp.from 622609176 in
    let var_felt_const_1339793538 : Felt.t := UnOp.from 1339793538 in
    let var_felt_const_1518763784 : Felt.t := UnOp.from 1518763784 in
    let var_felt_const_1989924532 : Felt.t := UnOp.from 1989924532 in
    let var_felt_const_1170029417 : Felt.t := UnOp.from 1170029417 in
    let var_felt_const_1917861751 : Felt.t := UnOp.from 1917861751 in
    let var_felt_const_1333667262 : Felt.t := UnOp.from 1333667262 in
    let var_felt_const_540703332 : Felt.t := UnOp.from 540703332 in
    let var_felt_const_1845603984 : Felt.t := UnOp.from 1845603984 in
    let var_felt_const_695835963 : Felt.t := UnOp.from 695835963 in
    let var_felt_const_831813382 : Felt.t := UnOp.from 831813382 in
    let var_felt_const_1421525369 : Felt.t := UnOp.from 1421525369 in
    let var_felt_const_1751797115 : Felt.t := UnOp.from 1751797115 in
    let var_felt_const_1964135730 : Felt.t := UnOp.from 1964135730 in
    let var_felt_const_525458520 : Felt.t := UnOp.from 525458520 in
    let var_felt_const_638242172 : Felt.t := UnOp.from 638242172 in
    let var_felt_const_1307439985 : Felt.t := UnOp.from 1307439985 in
    let var_felt_const_343354132 : Felt.t := UnOp.from 343354132 in
    let var_felt_const_1389166148 : Felt.t := UnOp.from 1389166148 in
    let var_felt_const_1660766320 : Felt.t := UnOp.from 1660766320 in
    let var_felt_const_1464793095 : Felt.t := UnOp.from 1464793095 in
    let var_felt_const_1180307149 : Felt.t := UnOp.from 1180307149 in
    let var_felt_const_1930780904 : Felt.t := UnOp.from 1930780904 in
    let var_felt_const_1066694495 : Felt.t := UnOp.from 1066694495 in
    let var_felt_const_1773108264 : Felt.t := UnOp.from 1773108264 in
    let var_felt_const_1004040026 : Felt.t := UnOp.from 1004040026 in
    let var_felt_const_815798990 : Felt.t := UnOp.from 815798990 in
    let var_felt_const_454905424 : Felt.t := UnOp.from 454905424 in
    let var_felt_const_118043943 : Felt.t := UnOp.from 118043943 in
    let var_felt_const_157582794 : Felt.t := UnOp.from 157582794 in
    let var_felt_const_246143118 : Felt.t := UnOp.from 246143118 in
    let var_felt_const_314968988 : Felt.t := UnOp.from 314968988 in
    let var_felt_const_127253399 : Felt.t := UnOp.from 127253399 in
    let var_felt_const_262278199 : Felt.t := UnOp.from 262278199 in
    let* var_self : ExtRoundConstants.t := M.CreateStruct in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_262278199; var_felt_const_127253399; var_felt_const_314968988; var_felt_const_246143118; var_felt_const_157582794; var_felt_const_118043943; var_felt_const_454905424; var_felt_const_815798990; var_felt_const_1004040026; var_felt_const_1773108264; var_felt_const_1066694495; var_felt_const_1930780904; var_felt_const_1180307149; var_felt_const_1464793095; var_felt_const_1660766320; var_felt_const_1389166148; var_felt_const_343354132; var_felt_const_1307439985; var_felt_const_638242172; var_felt_const_525458520; var_felt_const_1964135730; var_felt_const_1751797115; var_felt_const_1421525369; var_felt_const_831813382] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_695835963; var_felt_const_1845603984; var_felt_const_540703332; var_felt_const_1333667262; var_felt_const_1917861751; var_felt_const_1170029417; var_felt_const_1989924532; var_felt_const_1518763784; var_felt_const_1339793538; var_felt_const_622609176; var_felt_const_686842369; var_felt_const_1737016378; var_felt_const_1282239129; var_felt_const_897025192; var_felt_const_716894289; var_felt_const_1997503974; var_felt_const_395622276; var_felt_const_1201063290; var_felt_const_1917549072; var_felt_const_1150912935; var_felt_const_1687379185; var_felt_const_1507936940; var_felt_const_241306552; var_felt_const_989176635] in
    let var_array_1 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_1147522062; var_felt_const_27129487; var_felt_const_1257820264; var_felt_const_142102402; var_felt_const_217046702; var_felt_const_1664590951; var_felt_const_855276054; var_felt_const_1215259350; var_felt_const_946500736; var_felt_const_552696906; var_felt_const_1424297384; var_felt_const_538103555; var_felt_const_1608853840; var_felt_const_162510541; var_felt_const_623051854; var_felt_const_1549062383; var_felt_const_1908416316; var_felt_const_1622328571; var_felt_const_1079030649; var_felt_const_1584033957; var_felt_const_1099252725; var_felt_const_1910423126; var_felt_const_447555988; var_felt_const_862495875] in
    let var_array_2 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_128479034; var_felt_const_1587822577; var_felt_const_608401422; var_felt_const_1290028279; var_felt_const_342857858; var_felt_const_825405577; var_felt_const_427731030; var_felt_const_1718628547; var_felt_const_588764636; var_felt_const_204228775; var_felt_const_1454563174; var_felt_const_1740472809; var_felt_const_1338899225; var_felt_const_1269493554; var_felt_const_53007114; var_felt_const_1647670797; var_felt_const_306391314; var_felt_const_172614232; var_felt_const_51256176; var_felt_const_1221257987; var_felt_const_1239734761; var_felt_const_273790406; var_felt_const_1781980094; var_felt_const_1291790245] in
    let var_array_3 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_53041581; var_felt_const_723038058; var_felt_const_1439947916; var_felt_const_1136469704; var_felt_const_205609311; var_felt_const_1883820770; var_felt_const_14387587; var_felt_const_720724951; var_felt_const_1854174607; var_felt_const_1629316321; var_felt_const_530151394; var_felt_const_1679178250; var_felt_const_1549779579; var_felt_const_48375137; var_felt_const_976057819; var_felt_const_463976218; var_felt_const_875839332; var_felt_const_1946596189; var_felt_const_434078361; var_felt_const_1878280202; var_felt_const_1363837384; var_felt_const_1470845646; var_felt_const_1792450386; var_felt_const_1040977421] in
    let var_array_4 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_1209164052; var_felt_const_714957516; var_felt_const_390340387; var_felt_const_1213686459; var_felt_const_790726260; var_felt_const_117294666; var_felt_const_140621810; var_felt_const_993455846; var_felt_const_1889603648; var_felt_const_78845751; var_felt_const_925018226; var_felt_const_708123747; var_felt_const_1647665372; var_felt_const_1649953458; var_felt_const_942439428; var_felt_const_1006235079; var_felt_const_238616145; var_felt_const_930036496; var_felt_const_1401020792; var_felt_const_989618631; var_felt_const_1545325389; var_felt_const_1715719711; var_felt_const_755691969; var_felt_const_150307788] in
    let var_array_5 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_1567618575; var_felt_const_1663353317; var_felt_const_1950429111; var_felt_const_1891637550; var_felt_const_192082241; var_felt_const_1080533265; var_felt_const_1463323727; var_felt_const_890243564; var_felt_const_158646617; var_felt_const_1402624179; var_felt_const_59510015; var_felt_const_1198261138; var_felt_const_1065075039; var_felt_const_1150410028; var_felt_const_1293938517; var_felt_const_76770019; var_felt_const_1478577620; var_felt_const_1748789933; var_felt_const_457372011; var_felt_const_1841795381; var_felt_const_760115692; var_felt_const_1042892522; var_felt_const_1507649755; var_felt_const_1827572010] in
    let var_array_6 : Array.t Felt.t [24]%nat := Array.new [var_felt_const_1206940496; var_felt_const_1896271507; var_felt_const_1003792297; var_felt_const_738091882; var_felt_const_1124078057; var_felt_const_1889898; var_felt_const_813674331; var_felt_const_228520958; var_felt_const_1832911930; var_felt_const_781141772; var_felt_const_459826664; var_felt_const_202271745; var_felt_const_1296144415; var_felt_const_1111203133; var_felt_const_1090783436; var_felt_const_641665156; var_felt_const_1393671120; var_felt_const_1303271640; var_felt_const_809508074; var_felt_const_162506101; var_felt_const_1262312258; var_felt_const_1672219447; var_felt_const_1608891156; var_felt_const_1380248020] in
    let var_array_7 : Array.t Felt.t [8; 24]%nat := Array.new [] in
    let* _ : unit := Array.insert var_array_7 (var_c0, tt) var_array in
    let* _ : unit := Array.insert var_array_7 (var_c1, tt) var_array_0 in
    let* _ : unit := Array.insert var_array_7 (var_c2, tt) var_array_1 in
    let* _ : unit := Array.insert var_array_7 (var_c3, tt) var_array_2 in
    let* _ : unit := Array.insert var_array_7 (var_c4, tt) var_array_3 in
    let* _ : unit := Array.insert var_array_7 (var_c5, tt) var_array_4 in
    let* _ : unit := Array.insert var_array_7 (var_c6, tt) var_array_5 in
    let* _ : unit := Array.insert var_array_7 (var_c7, tt) var_array_6 in
    let* _ : unit := M.FieldWrite var_self.(ExtRoundConstants.dollar_super) var_array_7 in
    M.Pure var_self.
End ExtRoundConstants.

Module DoExtRound.
  Record t : Set := {
    dollar_super : MultiplyByMExt.t;
    dollar_temp_0 : MultiplyByMExt.t;
    dollar_temp : Array.t SBox.t [24]%nat;
    dollar_array : Array.t SBox.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : DoExtRound.t) (arg_fun_1 : Array.t Felt.t [24]%nat) (arg_fun_2 : Array.t Felt.t [24]%nat) : M.t unit :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t SBox.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1612_7 : Index.t) =>
      let var_3 : Felt.t := Array.read var_array (arg_for_1612_7, tt) in
      let var_4 : Index.t := M.cast_to_index var_3 in
      let var_5 : Felt.t := Array.read arg_fun_1 (var_4, tt) in
      let var_6 : Index.t := M.cast_to_index var_3 in
      let var_7 : Felt.t := Array.read arg_fun_2 (var_6, tt) in
      let var_8 : Felt.t := BinOp.add var_5 var_7 in
      let var_9 : Array.t SBox.t [24]%nat := arg_fun_0.(DoExtRound.dollar_temp) in
      let var_10 : Array.t SBox.t [24]%nat := arg_fun_0.(DoExtRound.dollar_temp) in
      let var_11 : SBox.t := Array.read var_10 (arg_for_1612_7, tt) in
      let* _ : unit := SBox.constrain var_11 var_8 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1612_7, tt) var_11 in
      M.yield tt
    ) in
    let var_0 : Array.t SBox.t [24]%nat := arg_fun_0.(DoExtRound.dollar_array) in
    let var_array_1 : Array.t Felt.t [24]%nat := Array.new [] in
    let* var_1 : Index.t := Array.len var_0 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_1 (fun (arg_for_1628_7 : Index.t) =>
      let var_3 : SBox.t := Array.read var_0 (arg_for_1628_7, tt) in
      let var_4 : Reg.t := var_3.(SBox.dollar_super) in
      let var_5 : NondetReg.t := var_4.(Reg.dollar_super) in
      let var_6 : Felt.t := var_5.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_1628_7, tt) var_6 in
      M.yield tt
    ) in
    let var_2 : MultiplyByMExt.t := arg_fun_0.(DoExtRound.dollar_temp_0) in
    let* _ : unit := MultiplyByMExt.constrain var_2 var_array_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t DoExtRound.t :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : DoExtRound.t := M.CreateStruct in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t SBox.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1550_7 : Index.t) =>
      let var_4 : Felt.t := Array.read var_array (arg_for_1550_7, tt) in
      let var_5 : Index.t := M.cast_to_index var_4 in
      let var_6 : Felt.t := Array.read arg_fun_0 (var_5, tt) in
      let var_7 : Index.t := M.cast_to_index var_4 in
      let var_8 : Felt.t := Array.read arg_fun_1 (var_7, tt) in
      let var_9 : Felt.t := BinOp.add var_6 var_8 in
      let* var_10 : SBox.t := SBox.compute var_9 in
      let var_11 : Array.t SBox.t [24]%nat := var_self.(DoExtRound.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_11 (arg_for_1550_7, tt) var_10 in
      let* _ : unit := M.FieldWrite var_self.(DoExtRound.dollar_temp) var_11 in
      let var_12 : Array.t SBox.t [24]%nat := var_self.(DoExtRound.dollar_temp) in
      let var_13 : SBox.t := Array.read var_12 (arg_for_1550_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1550_7, tt) var_13 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoExtRound.dollar_array) var_array_0 in
    let var_0 : Array.t SBox.t [24]%nat := var_self.(DoExtRound.dollar_array) in
    let var_array_1 : Array.t Felt.t [24]%nat := Array.new [] in
    let* var_1 : Index.t := Array.len var_0 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_1 (fun (arg_for_1569_7 : Index.t) =>
      let var_4 : SBox.t := Array.read var_0 (arg_for_1569_7, tt) in
      let var_5 : Reg.t := var_4.(SBox.dollar_super) in
      let var_6 : NondetReg.t := var_5.(Reg.dollar_super) in
      let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_1569_7, tt) var_7 in
      M.yield tt
    ) in
    let* var_2 : MultiplyByMExt.t := MultiplyByMExt.compute var_array_1 in
    let* _ : unit := M.FieldWrite var_self.(DoExtRound.dollar_temp_0) var_2 in
    let var_3 : MultiplyByMExt.t := var_self.(DoExtRound.dollar_temp_0) in
    let* _ : unit := M.FieldWrite var_self.(DoExtRound.dollar_super) var_3 in
    M.Pure var_self.
End DoExtRound.

Module AddConsts.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
    dollar_array : Array.t Felt.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : AddConsts.t) (arg_fun_1 : Array.t Felt.t [24]%nat) (arg_fun_2 : Array.t Felt.t [24]%nat) : M.t unit :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1718_7 : Index.t) =>
      let var_1 : Felt.t := Array.read var_array (arg_for_1718_7, tt) in
      let var_2 : Index.t := M.cast_to_index var_1 in
      let var_3 : Felt.t := Array.read arg_fun_1 (var_2, tt) in
      let var_4 : Index.t := M.cast_to_index var_1 in
      let var_5 : Felt.t := Array.read arg_fun_2 (var_4, tt) in
      let var_6 : Felt.t := BinOp.add var_3 var_5 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1718_7, tt) var_6 in
      M.yield tt
    ) in
    let var_0 : Array.t Felt.t [24]%nat := arg_fun_0.(AddConsts.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t AddConsts.t :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : AddConsts.t := M.CreateStruct in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1674_7 : Index.t) =>
      let var_1 : Felt.t := Array.read var_array (arg_for_1674_7, tt) in
      let var_2 : Index.t := M.cast_to_index var_1 in
      let var_3 : Felt.t := Array.read arg_fun_0 (var_2, tt) in
      let var_4 : Index.t := M.cast_to_index var_1 in
      let var_5 : Felt.t := Array.read arg_fun_1 (var_4, tt) in
      let var_6 : Felt.t := BinOp.add var_3 var_5 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1674_7, tt) var_6 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(AddConsts.dollar_array) var_array_0 in
    let var_0 : Array.t Felt.t [24]%nat := var_self.(AddConsts.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(AddConsts.dollar_super) var_0 in
    M.Pure var_self.
End AddConsts.

Module MultBy.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
    dollar_array : Array.t Felt.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : MultBy.t) (arg_fun_1 : Array.t Felt.t [24]%nat) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_array : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1755_7 : Index.t) =>
      let var_1 : Felt.t := Array.read arg_fun_1 (arg_for_1755_7, tt) in
      let var_2 : Felt.t := BinOp.mul var_1 arg_fun_2 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_1755_7, tt) var_2 in
      M.yield tt
    ) in
    let var_0 : Array.t Felt.t [24]%nat := arg_fun_0.(MultBy.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) (arg_fun_1 : Felt.t) : M.t MultBy.t :=
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : MultBy.t := M.CreateStruct in
    let var_array : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1740_7 : Index.t) =>
      let var_1 : Felt.t := Array.read arg_fun_0 (arg_for_1740_7, tt) in
      let var_2 : Felt.t := BinOp.mul var_1 arg_fun_1 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_1740_7, tt) var_2 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MultBy.dollar_array) var_array in
    let var_0 : Array.t Felt.t [24]%nat := var_self.(MultBy.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(MultBy.dollar_super) var_0 in
    M.Pure var_self.
End MultBy.

Module DoExtRoundByIdx.
  Record t : Set := {
    dollar_super : DoExtRound.t;
    dollar_temp_2 : DoExtRound.t;
    dollar_temp_1 : Array.t AddConsts.t [8]%nat;
    dollar_temp_0 : Array.t MultBy.t [8]%nat;
    dollar_temp : Array.t ExtRoundConstants.t [8]%nat;
    dollar_array : Array.t MultBy.t [8]%nat;
    zeroConsts : Array.t Felt.t [24]%nat;
    idxHot : OneHot.t 8;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_2 := map_mod α.(dollar_temp_2);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      dollar_array := map_mod α.(dollar_array);
      zeroConsts := map_mod α.(zeroConsts);
      idxHot := map_mod α.(idxHot);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : DoExtRoundByIdx.t) (arg_fun_1 : Array.t Felt.t [24]%nat) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_c8 : Index.t := 8%nat in
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : OneHot.t 8 := arg_fun_0.(DoExtRoundByIdx.idxHot) in
    let* _ : unit := OneHot.constrain var_0 arg_fun_2 in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1895_7 : Index.t) =>
      let var_5 : Felt.t := Array.read var_array (arg_for_1895_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1895_7, tt) var_felt_const_0 in
      M.yield tt
    ) in
    let var_1 : Array.t Felt.t [24]%nat := arg_fun_0.(DoExtRoundByIdx.zeroConsts) in
    let var_array_1 : Array.t Felt.t [8]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7] in
    let var_array_2 : Array.t MultBy.t [8]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c8 (* step *) var_c1 (fun (arg_for_1902_7 : Index.t) =>
      let var_5 : Felt.t := Array.read var_array_1 (arg_for_1902_7, tt) in
      let var_6 : Array.t ExtRoundConstants.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp) in
      let var_7 : Array.t ExtRoundConstants.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp) in
      let var_8 : ExtRoundConstants.t := Array.read var_7 (arg_for_1902_7, tt) in
      let* _ : unit := ExtRoundConstants.constrain var_8 in
      let var_9 : Array.t Felt.t [8; 24]%nat := var_8.(ExtRoundConstants.dollar_super) in
      let var_10 : Index.t := M.cast_to_index var_5 in
      let var_11 : Array.t Felt.t [24]%nat := Array.extract (Ns := [_]) var_9 (var_10, tt) in
      let var_12 : Array.t NondetBitReg.t [8]%nat := var_0.(OneHot.bits) in
      let var_13 : Index.t := M.cast_to_index var_5 in
      let var_14 : NondetBitReg.t := Array.read var_12 (var_13, tt) in
      let var_15 : NondetReg.t := var_14.(NondetBitReg.dollar_super) in
      let var_16 : Felt.t := var_15.(NondetReg.dollar_super) in
      let var_17 : Array.t MultBy.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp_0) in
      let var_18 : Array.t MultBy.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp_0) in
      let var_19 : MultBy.t := Array.read var_18 (arg_for_1902_7, tt) in
      let* _ : unit := MultBy.constrain var_19 var_11 var_16 in
      let* _ : unit := M.ArrayWrite var_array_2 (arg_for_1902_7, tt) var_19 in
      M.yield tt
    ) in
    let var_2 : Array.t MultBy.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_array) in
    let* var_3 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c8 (* step *) var_c1 (fun (arg_for_1923_12 : Index.t) (arg_for_1923_12 : Array.t Felt.t [24]%nat) =>
      let var_5 : MultBy.t := Array.read var_2 (arg_for_1923_12, tt) in
      let var_6 : Array.t Felt.t [24]%nat := var_5.(MultBy.dollar_super) in
      let* var_7 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_6 in
      let var_8 : Array.t AddConsts.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp_1) in
      let var_9 : Array.t AddConsts.t [8]%nat := arg_fun_0.(DoExtRoundByIdx.dollar_temp_1) in
      let var_10 : AddConsts.t := Array.read var_9 (arg_for_1923_12, tt) in
      let* _ : unit := AddConsts.constrain var_10 arg_for_1923_12 var_7 in
      let var_11 : Array.t Felt.t [24]%nat := var_10.(AddConsts.dollar_super) in
      let* var_12 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_11 in
      M.yield var_12
    ) in
    let var_4 : DoExtRound.t := arg_fun_0.(DoExtRoundByIdx.dollar_temp_2) in
    let* _ : unit := DoExtRound.constrain var_4 arg_fun_1 var_3 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) (arg_fun_1 : Felt.t) : M.t DoExtRoundByIdx.t :=
    let var_c8 : Index.t := 8%nat in
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : DoExtRoundByIdx.t := M.CreateStruct in
    let* var_0 : OneHot.t 8 := OneHot.compute arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.idxHot) var_0 in
    let var_1 : OneHot.t 8 := var_self.(DoExtRoundByIdx.idxHot) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_0 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_1808_7 : Index.t) =>
      let var_7 : Felt.t := Array.read var_array (arg_for_1808_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_1808_7, tt) var_felt_const_0 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.zeroConsts) var_array_0 in
    let var_2 : Array.t Felt.t [24]%nat := var_self.(DoExtRoundByIdx.zeroConsts) in
    let var_array_1 : Array.t Felt.t [8]%nat := Array.new [var_felt_const_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7] in
    let var_array_2 : Array.t MultBy.t [8]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c8 (* step *) var_c1 (fun (arg_for_1816_7 : Index.t) =>
      let var_7 : Felt.t := Array.read var_array_1 (arg_for_1816_7, tt) in
      let* var_8 : ExtRoundConstants.t := ExtRoundConstants.compute in
      let var_9 : Array.t ExtRoundConstants.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_9 (arg_for_1816_7, tt) var_8 in
      let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_temp) var_9 in
      let var_10 : Array.t ExtRoundConstants.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp) in
      let var_11 : ExtRoundConstants.t := Array.read var_10 (arg_for_1816_7, tt) in
      let var_12 : Array.t Felt.t [8; 24]%nat := var_11.(ExtRoundConstants.dollar_super) in
      let var_13 : Index.t := M.cast_to_index var_7 in
      let var_14 : Array.t Felt.t [24]%nat := Array.extract (Ns := [_]) var_12 (var_13, tt) in
      let var_15 : Array.t NondetBitReg.t [8]%nat := var_1.(OneHot.bits) in
      let var_16 : Index.t := M.cast_to_index var_7 in
      let var_17 : NondetBitReg.t := Array.read var_15 (var_16, tt) in
      let var_18 : NondetReg.t := var_17.(NondetBitReg.dollar_super) in
      let var_19 : Felt.t := var_18.(NondetReg.dollar_super) in
      let* var_20 : MultBy.t := MultBy.compute var_14 var_19 in
      let var_21 : Array.t MultBy.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_21 (arg_for_1816_7, tt) var_20 in
      let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_temp_0) var_21 in
      let var_22 : Array.t MultBy.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp_0) in
      let var_23 : MultBy.t := Array.read var_22 (arg_for_1816_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_2 (arg_for_1816_7, tt) var_23 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_array) var_array_2 in
    let var_3 : Array.t MultBy.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_array) in
    let* var_4 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c8 (* step *) var_c1 (fun (arg_for_1842_12 : Index.t) (arg_for_1842_12 : Array.t Felt.t [24]%nat) =>
      let var_7 : MultBy.t := Array.read var_3 (arg_for_1842_12, tt) in
      let var_8 : Array.t Felt.t [24]%nat := var_7.(MultBy.dollar_super) in
      let* var_9 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_8 in
      let* var_10 : AddConsts.t := AddConsts.compute arg_for_1842_12 var_9 in
      let var_11 : Array.t AddConsts.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp_1) in
      let* _ : unit := M.ArrayWrite var_11 (arg_for_1842_12, tt) var_10 in
      let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_temp_1) var_11 in
      let var_12 : Array.t AddConsts.t [8]%nat := var_self.(DoExtRoundByIdx.dollar_temp_1) in
      let var_13 : AddConsts.t := Array.read var_12 (arg_for_1842_12, tt) in
      let var_14 : Array.t Felt.t [24]%nat := var_13.(AddConsts.dollar_super) in
      let* var_15 : Array.t Felt.t [24]%nat := UnOp.unifiable_cast var_14 in
      M.yield var_15
    ) in
    let* var_5 : DoExtRound.t := DoExtRound.compute arg_fun_0 var_4 in
    let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_temp_2) var_5 in
    let var_6 : DoExtRound.t := var_self.(DoExtRoundByIdx.dollar_temp_2) in
    let* _ : unit := M.FieldWrite var_self.(DoExtRoundByIdx.dollar_super) var_6 in
    M.Pure var_self.
End DoExtRoundByIdx.

Module Pegs.
  Record t {N : nat} : Set := {
    dollar_super : Array.t Reg.t [N]%nat;
    dollar_temp : Array.t Reg.t [N]%nat;
    dollar_array : Array.t Reg.t [N]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {N : nat} : MapMod (t N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : Pegs.t N) (arg_fun_1 : Array.t Felt.t [N]%nat) : M.t unit :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_array : Array.t Reg.t [N]%nat := Array.new [] in
    let* var_0 : Index.t := Array.len arg_fun_1 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_0 (* step *) var_c1 (fun (arg_for_1970_7 : Index.t) =>
      let var_2 : Felt.t := Array.read arg_fun_1 (arg_for_1970_7, tt) in
      let var_3 : Array.t Reg.t [N]%nat := arg_fun_0.(Pegs.dollar_temp) in
      let var_4 : Array.t Reg.t [N]%nat := arg_fun_0.(Pegs.dollar_temp) in
      let var_5 : Reg.t := Array.read var_4 (arg_for_1970_7, tt) in
      let* _ : unit := Reg.constrain var_5 var_2 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_1970_7, tt) var_5 in
      M.yield tt
    ) in
    let var_1 : Array.t Reg.t [N]%nat := arg_fun_0.(Pegs.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Array.t Felt.t [N]%nat) : M.t (Pegs.t N) :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : Pegs.t N := M.CreateStruct in
    let var_array : Array.t Reg.t [N]%nat := Array.new [] in
    let* var_0 : Index.t := Array.len arg_fun_0 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_0 (* step *) var_c1 (fun (arg_for_1950_7 : Index.t) =>
      let var_2 : Felt.t := Array.read arg_fun_0 (arg_for_1950_7, tt) in
      let* var_3 : Reg.t := Reg.compute var_2 in
      let var_4 : Array.t Reg.t [N]%nat := var_self.(Pegs.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_4 (arg_for_1950_7, tt) var_3 in
      let* _ : unit := M.FieldWrite var_self.(Pegs.dollar_temp) var_4 in
      let var_5 : Array.t Reg.t [N]%nat := var_self.(Pegs.dollar_temp) in
      let var_6 : Reg.t := Array.read var_5 (arg_for_1950_7, tt) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_1950_7, tt) var_6 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(Pegs.dollar_array) var_array in
    let var_1 : Array.t Reg.t [N]%nat := var_self.(Pegs.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(Pegs.dollar_super) var_1 in
    M.Pure var_self.
End Pegs.

Module Nonce.
  Record t : Set := {
    dollar_super : Reg.t;
    dollar_temp : Reg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Nonce.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_0 : Reg.t := arg_fun_0.(Nonce.dollar_temp) in
    let* _ : unit := Reg.constrain var_0 arg_fun_1 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t Nonce.t :=
    let* var_self : Nonce.t := M.CreateStruct in
    let* var_0 : Reg.t := Reg.compute arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(Nonce.dollar_temp) var_0 in
    let var_1 : Reg.t := var_self.(Nonce.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(Nonce.dollar_super) var_1 in
    M.Pure var_self.
End Nonce.

Module IsZero.
  Record t : Set := {
    dollar_super : NondetReg.t;
    dollar_temp_0 : AssertBit.t;
    inv : NondetReg.t;
    dollar_temp : Felt.t;
    isZero : NondetReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      inv := map_mod α.(inv);
      dollar_temp := map_mod α.(dollar_temp);
      isZero := map_mod α.(isZero);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : IsZero.t) (arg_fun_1 : Felt.t) : M.t unit :=
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_0 : bool := Bool.cmp BoolCmp.Eq arg_fun_1 var_felt_const_0 in
    let var_1 : Felt.t := M.cast_to_felt var_0 in
    let var_2 : NondetReg.t := arg_fun_0.(IsZero.isZero) in
    let* _ : unit := NondetReg.constrain var_2 var_1 in
    let var_3 : Felt.t := arg_fun_0.(IsZero.dollar_temp) in
    let var_4 : NondetReg.t := arg_fun_0.(IsZero.inv) in
    let* _ : unit := NondetReg.constrain var_4 var_3 in
    let var_5 : Felt.t := var_2.(NondetReg.dollar_super) in
    let var_6 : AssertBit.t := arg_fun_0.(IsZero.dollar_temp_0) in
    let* _ : unit := AssertBit.constrain var_6 var_5 in
    let var_7 : Felt.t := var_4.(NondetReg.dollar_super) in
    let var_8 : Felt.t := BinOp.mul arg_fun_1 var_7 in
    let var_9 : Felt.t := var_2.(NondetReg.dollar_super) in
    let var_10 : Felt.t := BinOp.sub var_felt_const_1 var_9 in
    let* _ : unit := M.AssertEqual var_8 var_10 in
    let var_11 : Felt.t := var_2.(NondetReg.dollar_super) in
    let var_12 : Felt.t := BinOp.mul var_11 arg_fun_1 in
    let* _ : unit := M.AssertEqual var_12 var_felt_const_0 in
    let var_13 : Felt.t := var_2.(NondetReg.dollar_super) in
    let var_14 : Felt.t := var_4.(NondetReg.dollar_super) in
    let var_15 : Felt.t := BinOp.mul var_13 var_14 in
    let* _ : unit := M.AssertEqual var_15 var_felt_const_0 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) : M.t IsZero.t :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : IsZero.t := M.CreateStruct in
    let var_0 : bool := Bool.cmp BoolCmp.Eq arg_fun_0 var_felt_const_0 in
    let var_1 : Felt.t := M.cast_to_felt var_0 in
    let* var_2 : NondetReg.t := NondetReg.compute var_1 in
    let* _ : unit := M.FieldWrite var_self.(IsZero.isZero) var_2 in
    let var_3 : NondetReg.t := var_self.(IsZero.isZero) in
    let var_4 : Felt.t := UnOp.inv arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(IsZero.dollar_temp) var_4 in
    let var_5 : Felt.t := var_self.(IsZero.dollar_temp) in
    let* var_6 : NondetReg.t := NondetReg.compute var_5 in
    let* _ : unit := M.FieldWrite var_self.(IsZero.inv) var_6 in
    let var_7 : NondetReg.t := var_self.(IsZero.inv) in
    let var_8 : Felt.t := var_3.(NondetReg.dollar_super) in
    let* var_9 : AssertBit.t := AssertBit.compute var_8 in
    let* _ : unit := M.FieldWrite var_self.(IsZero.dollar_temp_0) var_9 in
    let var_10 : AssertBit.t := var_self.(IsZero.dollar_temp_0) in
    let var_11 : Felt.t := var_7.(NondetReg.dollar_super) in
    let var_12 : Felt.t := var_3.(NondetReg.dollar_super) in
    let var_13 : Felt.t := var_3.(NondetReg.dollar_super) in
    let var_14 : Felt.t := var_3.(NondetReg.dollar_super) in
    let var_15 : Felt.t := var_7.(NondetReg.dollar_super) in
    let* _ : unit := M.FieldWrite var_self.(IsZero.dollar_super) var_3 in
    M.Pure var_self.
End IsZero.

Module Eq.
  Record t : Set := {
    dollar_super : IsZero.t;
    dollar_temp : IsZero.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Eq.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_0 : Felt.t := BinOp.sub arg_fun_1 arg_fun_2 in
    let var_1 : IsZero.t := arg_fun_0.(Eq.dollar_temp) in
    let* _ : unit := IsZero.constrain var_1 var_0 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Eq.t :=
    let* var_self : Eq.t := M.CreateStruct in
    let var_0 : Felt.t := BinOp.sub arg_fun_0 arg_fun_1 in
    let* var_1 : IsZero.t := IsZero.compute var_0 in
    let* _ : unit := M.FieldWrite var_self.(Eq.dollar_temp) var_1 in
    let var_2 : IsZero.t := var_self.(Eq.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(Eq.dollar_super) var_2 in
    M.Pure var_self.
End Eq.

Module EnsureEq.
  Record t {T : nat} : Set := {
    dollar_super : Eq.t;
    dollar_temp : Assert.t;
    r : Eq.t;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {T : nat} : MapMod (t T) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      r := map_mod α.(r);
    |};
  }.

  Definition constrain {p} `{Prime p} {T : nat} (arg_fun_0 : EnsureEq.t T) (arg_fun_1 : TypeVar.t @T) (arg_fun_2 : TypeVar.t @T) : M.t unit :=
    let* var_0 : string := String.new Provided values are not equal in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* _ : unit := M.AssertEqual arg_fun_1 arg_fun_2 in
    let* var_1 : Felt.t := UnOp.unifiable_cast arg_fun_1 in
    let* var_2 : Felt.t := UnOp.unifiable_cast arg_fun_2 in
    let var_3 : Eq.t := arg_fun_0.(EnsureEq.r) in
    let* _ : unit := Eq.constrain var_3 var_1 var_2 in
    let var_4 : IsZero.t := var_3.(Eq.dollar_super) in
    let var_5 : NondetReg.t := var_4.(IsZero.dollar_super) in
    let var_6 : Felt.t := var_5.(NondetReg.dollar_super) in
    let var_7 : bool := Bool.cmp BoolCmp.Eq var_6 var_felt_const_0 in
    let var_8 : Felt.t := M.cast_to_felt var_7 in
    let var_9 : Assert.t := arg_fun_0.(EnsureEq.dollar_temp) in
    let* _ : unit := Assert.constrain var_9 var_8 var_0 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {T : nat} (arg_fun_0 : TypeVar.t @T) (arg_fun_1 : TypeVar.t @T) : M.t (EnsureEq.t T) :=
    let* var_0 : string := String.new Provided values are not equal in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : EnsureEq.t T := M.CreateStruct in
    let* var_1 : Felt.t := UnOp.unifiable_cast arg_fun_0 in
    let* var_2 : Felt.t := UnOp.unifiable_cast arg_fun_1 in
    let* var_3 : Eq.t := Eq.compute var_1 var_2 in
    let* _ : unit := M.FieldWrite var_self.(EnsureEq.r) var_3 in
    let var_4 : Eq.t := var_self.(EnsureEq.r) in
    let var_5 : IsZero.t := var_4.(Eq.dollar_super) in
    let var_6 : NondetReg.t := var_5.(IsZero.dollar_super) in
    let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
    let var_8 : bool := Bool.cmp BoolCmp.Eq var_7 var_felt_const_0 in
    let var_9 : Felt.t := M.cast_to_felt var_8 in
    let* var_10 : Assert.t := Assert.compute var_9 var_0 in
    let* _ : unit := M.FieldWrite var_self.(EnsureEq.dollar_temp) var_10 in
    let var_11 : Assert.t := var_self.(EnsureEq.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(EnsureEq.dollar_super) var_4 in
    M.Pure var_self.
End EnsureEq.

Module MulReg.
  Record t : Set := {
    dollar_super : NondetReg.t;
    dollar_temp : NondetReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : MulReg.t) (arg_fun_1 : NondetReg.t) (arg_fun_2 : NondetReg.t) : M.t unit :=
    let var_0 : Felt.t := arg_fun_1.(NondetReg.dollar_super) in
    let var_1 : Felt.t := arg_fun_2.(NondetReg.dollar_super) in
    let var_2 : Felt.t := BinOp.mul var_0 var_1 in
    let var_3 : NondetReg.t := arg_fun_0.(MulReg.dollar_temp) in
    let* _ : unit := NondetReg.constrain var_3 var_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : NondetReg.t) (arg_fun_1 : NondetReg.t) : M.t MulReg.t :=
    let* var_self : MulReg.t := M.CreateStruct in
    let var_0 : Felt.t := arg_fun_0.(NondetReg.dollar_super) in
    let var_1 : Felt.t := arg_fun_1.(NondetReg.dollar_super) in
    let var_2 : Felt.t := BinOp.mul var_0 var_1 in
    let* var_3 : NondetReg.t := NondetReg.compute var_2 in
    let* _ : unit := M.FieldWrite var_self.(MulReg.dollar_temp) var_3 in
    let var_4 : NondetReg.t := var_self.(MulReg.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(MulReg.dollar_super) var_4 in
    M.Pure var_self.
End MulReg.

Module CheckBounds.
  Record t {COLORS PEGS : nat} : Set := {
    dollar_super : Array.t block$_1.t [PEGS]%nat;
    dollar_temp_4 : Array.t block$_1.t [PEGS]%nat;
    dollar_temp_3 : Array.t Component.t [PEGS]%nat;
    dollar_temp_2 : Array.t Assert.t [PEGS]%nat;
    check : Array.t Reg.t [PEGS]%nat;
    dollar_temp_1 : Array.t MulReg.t [PEGS; Array.affine_map]%nat;
    dollar_temp_0 : Array.t NondetReg.t [PEGS]%nat;
    dollar_temp : Array.t NondetReg.t [PEGS; Array.affine_map]%nat;
    dollar_array_0 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat;
    dollar_array : Array.t block$_1.t [PEGS]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {COLORS PEGS : nat} : MapMod (t COLORS PEGS) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_4 := map_mod α.(dollar_temp_4);
      dollar_temp_3 := map_mod α.(dollar_temp_3);
      dollar_temp_2 := map_mod α.(dollar_temp_2);
      check := map_mod α.(check);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      dollar_array_0 := map_mod α.(dollar_array_0);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : CheckBounds.t COLORS PEGS) (arg_fun_1 : Pegs.t PEGS) : M.t unit :=
    let* var_0 : string := String.new Not a valid color in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_1 : Felt.t := UnOp.from (Z.of_nat COLORS) in
    let var_2 : Array.t Reg.t [PEGS]%nat := arg_fun_1.(Pegs.dollar_super) in
    let var_array : Array.t block$_1.t [PEGS]%nat := Array.new [] in
    let* var_3 : Index.t := Array.len var_2 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_2260_7 : Index.t) =>
      let var_5 : Reg.t := Array.read var_2 (arg_for_2260_7, tt) in
      let var_6 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let var_array_0 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
      let var_7 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let* _ : unit := M.for_ var_c0 (* to *) var_7 (* step *) var_c1 (fun (arg_for_2265_9 : Index.t) =>
        let var_37 : Felt.t := M.cast_to_felt arg_for_2265_9 in
        let* _ : unit := M.ArrayWrite var_array_0 (arg_for_2265_9, tt) var_37 in
        M.yield tt
      ) in
      let var_8 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let var_array_1 : Array.t NondetReg.t [Array.affine_map]%nat := Array.new [] in
      let* var_9 : Index.t := Array.len var_array_0 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_9 (* step *) var_c1 (fun (arg_for_2272_9 : Index.t) =>
        let var_37 : Felt.t := Array.read var_array_0 (arg_for_2272_9, tt) in
        let var_38 : NondetReg.t := var_5.(Reg.dollar_super) in
        let var_39 : Felt.t := var_38.(NondetReg.dollar_super) in
        let var_40 : Felt.t := BinOp.sub var_37 var_39 in
        let var_41 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_temp) in
        let var_42 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_temp) in
        let var_43 : NondetReg.t := Array.read var_42 (arg_for_2260_7, arg_for_2272_9, tt) in
        let* _ : unit := NondetReg.constrain var_43 var_40 in
        let* _ : unit := M.ArrayWrite var_array_1 (arg_for_2272_9, tt) var_43 in
        M.yield tt
      ) in
      let var_10 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_array_0) in
      let var_11 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_array_0) in
      let var_12 : Array.t NondetReg.t [Array.affine_map]%nat := Array.extract (Ns := [_]) var_11 (arg_for_2260_7, tt) in
      let var_13 : Array.t NondetReg.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_0) in
      let var_14 : Array.t NondetReg.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_0) in
      let var_15 : NondetReg.t := Array.read var_14 (arg_for_2260_7, tt) in
      let* _ : unit := NondetReg.constrain var_15 var_felt_const_1 in
      let* var_16 : Index.t := Array.len var_12 var_c0 in
      let* var_17 : NondetReg.t := M.for_ var_c0 (* to *) var_16 (* step *) var_c1 (fun (arg_for_2291_15 : Index.t) (arg_for_2291_15 : NondetReg.t) =>
        let var_37 : NondetReg.t := Array.read var_12 (arg_for_2291_15, tt) in
        let var_38 : Array.t MulReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_temp_1) in
        let var_39 : Array.t MulReg.t [PEGS; Array.affine_map]%nat := arg_fun_0.(CheckBounds.dollar_temp_1) in
        let var_40 : MulReg.t := Array.read var_39 (arg_for_2260_7, arg_for_2291_15, tt) in
        let* _ : unit := MulReg.constrain var_40 arg_for_2291_15 var_37 in
        let var_41 : NondetReg.t := var_40.(MulReg.dollar_super) in
        M.yield var_41
      ) in
      let var_18 : Felt.t := var_17.(NondetReg.dollar_super) in
      let var_19 : Array.t Reg.t [PEGS]%nat := arg_fun_0.(CheckBounds.check) in
      let var_20 : Array.t Reg.t [PEGS]%nat := arg_fun_0.(CheckBounds.check) in
      let var_21 : Reg.t := Array.read var_20 (arg_for_2260_7, tt) in
      let* _ : unit := Reg.constrain var_21 var_18 in
      let var_22 : NondetReg.t := var_21.(Reg.dollar_super) in
      let var_23 : Felt.t := var_22.(NondetReg.dollar_super) in
      let* _ : unit := M.AssertEqual var_23 var_felt_const_0 in
      let var_24 : NondetReg.t := var_21.(Reg.dollar_super) in
      let var_25 : Felt.t := var_24.(NondetReg.dollar_super) in
      let var_26 : Array.t Assert.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_2) in
      let var_27 : Array.t Assert.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_2) in
      let var_28 : Assert.t := Array.read var_27 (arg_for_2260_7, tt) in
      let* _ : unit := Assert.constrain var_28 var_25 var_0 in
      let var_29 : Array.t Component.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_3) in
      let var_30 : Array.t Component.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_3) in
      let var_31 : Component.t := Array.read var_30 (arg_for_2260_7, tt) in
      let* _ : unit := Component.constrain var_31 in
      let var_32 : Array.t Reg.t [PEGS]%nat := arg_fun_0.(CheckBounds.check) in
      let var_33 : Reg.t := Array.read var_32 (arg_for_2260_7, tt) in
      let var_34 : Array.t block$_1.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_4) in
      let var_35 : Array.t block$_1.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_temp_4) in
      let var_36 : block$_1.t := Array.read var_35 (arg_for_2260_7, tt) in
      let* _ : unit := blockdollar__1.constrain var_36 var_31 var_33 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2260_7, tt) var_36 in
      M.yield tt
    ) in
    let var_4 : Array.t block$_1.t [PEGS]%nat := arg_fun_0.(CheckBounds.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : Pegs.t PEGS) : M.t (CheckBounds.t COLORS PEGS) :=
    let* var_0 : string := String.new Not a valid color in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : CheckBounds.t COLORS PEGS := M.CreateStruct in
    let var_1 : Felt.t := UnOp.from (Z.of_nat COLORS) in
    let var_2 : Array.t Reg.t [PEGS]%nat := arg_fun_0.(Pegs.dollar_super) in
    let var_array : Array.t block$_1.t [PEGS]%nat := Array.new [] in
    let* var_3 : Index.t := Array.len var_2 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_2164_7 : Index.t) =>
      let var_5 : Reg.t := Array.read var_2 (arg_for_2164_7, tt) in
      let var_6 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let var_array_0 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
      let var_7 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let* _ : unit := M.for_ var_c0 (* to *) var_7 (* step *) var_c1 (fun (arg_for_2169_9 : Index.t) =>
        let var_42 : Felt.t := M.cast_to_felt arg_for_2169_9 in
        let* _ : unit := M.ArrayWrite var_array_0 (arg_for_2169_9, tt) var_42 in
        M.yield tt
      ) in
      let var_8 : Index.t := UnOp.from (Z.of_nat COLORS) in
      let var_array_1 : Array.t NondetReg.t [Array.affine_map]%nat := Array.new [] in
      let* var_9 : Index.t := Array.len var_array_0 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_9 (* step *) var_c1 (fun (arg_for_2176_9 : Index.t) =>
        let var_42 : Felt.t := Array.read var_array_0 (arg_for_2176_9, tt) in
        let var_43 : NondetReg.t := var_5.(Reg.dollar_super) in
        let var_44 : Felt.t := var_43.(NondetReg.dollar_super) in
        let var_45 : Felt.t := BinOp.sub var_42 var_44 in
        let* var_46 : NondetReg.t := NondetReg.compute var_45 in
        let var_47 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_temp) in
        let* _ : unit := M.ArrayWrite var_47 (arg_for_2164_7, arg_for_2176_9, tt) var_46 in
        let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp) var_47 in
        let var_48 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_temp) in
        let var_49 : NondetReg.t := Array.read var_48 (arg_for_2164_7, arg_for_2176_9, tt) in
        let* _ : unit := M.ArrayWrite var_array_1 (arg_for_2176_9, tt) var_49 in
        M.yield tt
      ) in
      let var_10 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_array_0) in
      let* _ : unit := Array.insert var_10 (arg_for_2164_7, tt) var_array_1 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_array_0) var_10 in
      let var_11 : Array.t NondetReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_array_0) in
      let var_12 : Array.t NondetReg.t [Array.affine_map]%nat := Array.extract (Ns := [_]) var_11 (arg_for_2164_7, tt) in
      let* var_13 : NondetReg.t := NondetReg.compute var_felt_const_1 in
      let var_14 : Array.t NondetReg.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_14 (arg_for_2164_7, tt) var_13 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp_0) var_14 in
      let var_15 : Array.t NondetReg.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_0) in
      let var_16 : NondetReg.t := Array.read var_15 (arg_for_2164_7, tt) in
      let* var_17 : Index.t := Array.len var_12 var_c0 in
      let* var_18 : NondetReg.t := M.for_ var_c0 (* to *) var_17 (* step *) var_c1 (fun (arg_for_2201_15 : Index.t) (arg_for_2201_15 : NondetReg.t) =>
        let var_42 : NondetReg.t := Array.read var_12 (arg_for_2201_15, tt) in
        let* var_43 : MulReg.t := MulReg.compute arg_for_2201_15 var_42 in
        let var_44 : Array.t MulReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_temp_1) in
        let* _ : unit := M.ArrayWrite var_44 (arg_for_2164_7, arg_for_2201_15, tt) var_43 in
        let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp_1) var_44 in
        let var_45 : Array.t MulReg.t [PEGS; Array.affine_map]%nat := var_self.(CheckBounds.dollar_temp_1) in
        let var_46 : MulReg.t := Array.read var_45 (arg_for_2164_7, arg_for_2201_15, tt) in
        let var_47 : NondetReg.t := var_46.(MulReg.dollar_super) in
        M.yield var_47
      ) in
      let var_19 : Felt.t := var_18.(NondetReg.dollar_super) in
      let* var_20 : Reg.t := Reg.compute var_19 in
      let var_21 : Array.t Reg.t [PEGS]%nat := var_self.(CheckBounds.check) in
      let* _ : unit := M.ArrayWrite var_21 (arg_for_2164_7, tt) var_20 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.check) var_21 in
      let var_22 : Array.t Reg.t [PEGS]%nat := var_self.(CheckBounds.check) in
      let var_23 : Reg.t := Array.read var_22 (arg_for_2164_7, tt) in
      let var_24 : NondetReg.t := var_23.(Reg.dollar_super) in
      let var_25 : Felt.t := var_24.(NondetReg.dollar_super) in
      let var_26 : NondetReg.t := var_23.(Reg.dollar_super) in
      let var_27 : Felt.t := var_26.(NondetReg.dollar_super) in
      let* var_28 : Assert.t := Assert.compute var_27 var_0 in
      let var_29 : Array.t Assert.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_2) in
      let* _ : unit := M.ArrayWrite var_29 (arg_for_2164_7, tt) var_28 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp_2) var_29 in
      let var_30 : Array.t Assert.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_2) in
      let var_31 : Assert.t := Array.read var_30 (arg_for_2164_7, tt) in
      let* var_32 : Component.t := Component.compute in
      let var_33 : Array.t Component.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_3) in
      let* _ : unit := M.ArrayWrite var_33 (arg_for_2164_7, tt) var_32 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp_3) var_33 in
      let var_34 : Array.t Component.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_3) in
      let var_35 : Component.t := Array.read var_34 (arg_for_2164_7, tt) in
      let var_36 : Array.t Reg.t [PEGS]%nat := var_self.(CheckBounds.check) in
      let var_37 : Reg.t := Array.read var_36 (arg_for_2164_7, tt) in
      let* var_38 : block$_1.t := blockdollar__1.compute var_35 var_37 in
      let var_39 : Array.t block$_1.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_4) in
      let* _ : unit := M.ArrayWrite var_39 (arg_for_2164_7, tt) var_38 in
      let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_temp_4) var_39 in
      let var_40 : Array.t block$_1.t [PEGS]%nat := var_self.(CheckBounds.dollar_temp_4) in
      let var_41 : block$_1.t := Array.read var_40 (arg_for_2164_7, tt) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2164_7, tt) var_41 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_array) var_array in
    let var_4 : Array.t block$_1.t [PEGS]%nat := var_self.(CheckBounds.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(CheckBounds.dollar_super) var_4 in
    M.Pure var_self.
End CheckBounds.

Module CodeHash.
  Record t : Set := {
    dollar_super : Array.t Felt.t [24]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : CodeHash.t) (arg_fun_1 : Array.t Felt.t [24]%nat) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Array.t Felt.t [24]%nat) : M.t CodeHash.t :=
    let* var_self : CodeHash.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(CodeHash.dollar_super) arg_fun_0 in
    M.Pure var_self.
End CodeHash.

Module GenerateCodeHash.
  Record t {N : nat} : Set := {
    dollar_super : CodeHash.t;
    dollar_temp_1 : CodeHash.t;
    dollar_temp_0 : Array.t DoExtRoundByIdx.t [4]%nat;
    stage2 : DoIntRounds.t;
    dollar_temp : Array.t DoExtRoundByIdx.t [4]%nat;
    stage0 : MultiplyByMExt.t;
    in : Array.t Felt.t [24]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {N : nat} : MapMod (t N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      stage2 := map_mod α.(stage2);
      dollar_temp := map_mod α.(dollar_temp);
      stage0 := map_mod α.(stage0);
      in := map_mod α.(in);
    |};
  }.

  Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : GenerateCodeHash.t N) (arg_fun_1 : Nonce.t) (arg_fun_2 : Pegs.t N) : M.t unit :=
    let var_c4 : Index.t := 4%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_24 : Felt.t := UnOp.from 24 in
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0_0 : Felt.t := UnOp.from 0 in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_1 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_2528_7 : Index.t) =>
      let var_10 : Felt.t := Array.read var_array (arg_for_2528_7, tt) in
      let var_11 : bool := Bool.cmp BoolCmp.Eq var_10 var_felt_const_0_0 in
      let var_12 : Felt.t := M.cast_to_felt var_11 in
      let var_13 : bool := Bool.cmp BoolCmp.Le var_felt_const_1 var_10 in
      let var_14 : bool := Bool.cmp BoolCmp.Lt var_10 var_0 in
      let var_15 : Felt.t := M.cast_to_felt var_13 in
      let var_16 : Felt.t := M.cast_to_felt var_14 in
      let var_17 : Felt.t := BinOp.mul var_15 var_16 in
      let var_18 : bool := Bool.cmp BoolCmp.Le var_0 var_10 in
      let var_19 : bool := Bool.cmp BoolCmp.Lt var_10 var_felt_const_24 in
      let var_20 : Felt.t := M.cast_to_felt var_18 in
      let var_21 : Felt.t := M.cast_to_felt var_19 in
      let var_22 : Felt.t := BinOp.mul var_20 var_21 in
      let var_array_4 : Array.t Felt.t [3]%nat := Array.new [var_12; var_17; var_22] in
      let var_23 : Index.t := M.cast_to_index var_felt_const_0_0 in
      let var_24 : Felt.t := Array.read var_array_4 (var_23, tt) in
      let var_25 : bool := Bool.cmp BoolCmp.Ne var_24 var_felt_const_0 in
      let var_26 : Index.t := M.cast_to_index var_felt_const_1 in
      let var_27 : Felt.t := Array.read var_array_4 (var_26, tt) in
      let var_28 : bool := Bool.cmp BoolCmp.Ne var_27 var_felt_const_0 in
      let var_29 : Index.t := M.cast_to_index var_felt_const_2 in
      let var_30 : Felt.t := Array.read var_array_4 (var_29, tt) in
      let var_31 : bool := Bool.cmp BoolCmp.Ne var_30 var_felt_const_0 in
      let* var_32 : Felt.t := M.if_ var_25 then
        let var_33 : Reg.t := arg_fun_1.(Nonce.dollar_super) in
        let var_34 : NondetReg.t := var_33.(Reg.dollar_super) in
        let var_35 : Felt.t := var_34.(NondetReg.dollar_super) in
        M.yield var_35 else
        let* var_33 : Felt.t := M.if_ var_28 then
          let var_34 : Felt.t := BinOp.sub var_10 var_felt_const_1 in
          let var_35 : Array.t Reg.t [N]%nat := arg_fun_2.(Pegs.dollar_super) in
          let var_36 : Index.t := M.cast_to_index var_34 in
          let var_37 : Reg.t := Array.read var_35 (var_36, tt) in
          let var_38 : NondetReg.t := var_37.(Reg.dollar_super) in
          let var_39 : Felt.t := var_38.(NondetReg.dollar_super) in
          M.yield var_39 else
          let* _ : unit := M.AssertBool var_31 in
          M.yield var_felt_const_0_0 in
        M.yield var_33 in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_2528_7, tt) var_32 in
      M.yield tt
    ) in
    let var_1 : Array.t Felt.t [24]%nat := arg_fun_0.(GenerateCodeHash.in) in
    let var_2 : MultiplyByMExt.t := arg_fun_0.(GenerateCodeHash.stage0) in
    let* _ : unit := MultiplyByMExt.constrain var_2 var_1 in
    let var_array_2 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
    let* var_3 : MultiplyByMExt.t := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_2578_12 : Index.t) (arg_for_2578_12 : MultiplyByMExt.t) =>
      let var_10 : Felt.t := Array.read var_array_2 (arg_for_2578_12, tt) in
      let var_11 : Array.t block$.t [24]%nat := arg_for_2578_12.(MultiplyByMExt.dollar_super) in
      let var_array_4 : Array.t Felt.t [24]%nat := Array.new [] in
      let* var_12 : Index.t := Array.len var_11 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_12 (fun (arg_for_2583_9 : Index.t) =>
        let var_18 : block$.t := Array.read var_11 (arg_for_2583_9, tt) in
        let var_19 : Felt.t := var_18.(block$.dollar_super) in
        let* _ : unit := M.ArrayWrite var_array_4 (arg_for_2583_9, tt) var_19 in
        M.yield tt
      ) in
      let var_13 : Array.t DoExtRoundByIdx.t [4]%nat := arg_fun_0.(GenerateCodeHash.dollar_temp) in
      let var_14 : Array.t DoExtRoundByIdx.t [4]%nat := arg_fun_0.(GenerateCodeHash.dollar_temp) in
      let var_15 : DoExtRoundByIdx.t := Array.read var_14 (arg_for_2578_12, tt) in
      let* _ : unit := DoExtRoundByIdx.constrain var_15 var_array_4 var_10 in
      let var_16 : DoExtRound.t := var_15.(DoExtRoundByIdx.dollar_super) in
      let var_17 : MultiplyByMExt.t := var_16.(DoExtRound.dollar_super) in
      M.yield var_17
    ) in
    let var_4 : Array.t block$.t [24]%nat := var_3.(MultiplyByMExt.dollar_super) in
    let var_array_3 : Array.t Felt.t [24]%nat := Array.new [] in
    let* var_5 : Index.t := Array.len var_4 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_5 (fun (arg_for_2599_7 : Index.t) =>
      let var_10 : block$.t := Array.read var_4 (arg_for_2599_7, tt) in
      let var_11 : Felt.t := var_10.(block$.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_2599_7, tt) var_11 in
      M.yield tt
    ) in
    let var_6 : DoIntRounds.t := arg_fun_0.(GenerateCodeHash.stage2) in
    let* _ : unit := DoIntRounds.constrain var_6 var_array_3 in
    let var_7 : Array.t Felt.t [24]%nat := var_6.(DoIntRounds.dollar_super) in
    let* var_8 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_2607_12 : Index.t) (arg_for_2607_12 : Array.t Felt.t [24]%nat) =>
      let var_10 : Felt.t := Array.read var_array_2 (arg_for_2607_12, tt) in
      let var_11 : Array.t DoExtRoundByIdx.t [4]%nat := arg_fun_0.(GenerateCodeHash.dollar_temp_0) in
      let var_12 : Array.t DoExtRoundByIdx.t [4]%nat := arg_fun_0.(GenerateCodeHash.dollar_temp_0) in
      let var_13 : DoExtRoundByIdx.t := Array.read var_12 (arg_for_2607_12, tt) in
      let* _ : unit := DoExtRoundByIdx.constrain var_13 arg_for_2607_12 var_10 in
      let var_14 : DoExtRound.t := var_13.(DoExtRoundByIdx.dollar_super) in
      let var_15 : MultiplyByMExt.t := var_14.(DoExtRound.dollar_super) in
      let var_16 : Array.t block$.t [24]%nat := var_15.(MultiplyByMExt.dollar_super) in
      let var_array_4 : Array.t Felt.t [24]%nat := Array.new [] in
      let* var_17 : Index.t := Array.len var_16 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_17 (fun (arg_for_2618_9 : Index.t) =>
        let var_18 : block$.t := Array.read var_16 (arg_for_2618_9, tt) in
        let var_19 : Felt.t := var_18.(block$.dollar_super) in
        let* _ : unit := M.ArrayWrite var_array_4 (arg_for_2618_9, tt) var_19 in
        M.yield tt
      ) in
      M.yield var_array_4
    ) in
    let var_9 : CodeHash.t := arg_fun_0.(GenerateCodeHash.dollar_temp_1) in
    let* _ : unit := CodeHash.constrain var_9 var_8 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Nonce.t) (arg_fun_1 : Pegs.t N) : M.t (GenerateCodeHash.t N) :=
    let var_c4 : Index.t := 4%nat in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_24 : Felt.t := UnOp.from 24 in
    let var_c24 : Index.t := 24%nat in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_felt_const_23 : Felt.t := UnOp.from 23 in
    let var_felt_const_22 : Felt.t := UnOp.from 22 in
    let var_felt_const_21 : Felt.t := UnOp.from 21 in
    let var_felt_const_20 : Felt.t := UnOp.from 20 in
    let var_felt_const_19 : Felt.t := UnOp.from 19 in
    let var_felt_const_18 : Felt.t := UnOp.from 18 in
    let var_felt_const_17 : Felt.t := UnOp.from 17 in
    let var_felt_const_16 : Felt.t := UnOp.from 16 in
    let var_felt_const_15 : Felt.t := UnOp.from 15 in
    let var_felt_const_14 : Felt.t := UnOp.from 14 in
    let var_felt_const_13 : Felt.t := UnOp.from 13 in
    let var_felt_const_12 : Felt.t := UnOp.from 12 in
    let var_felt_const_11 : Felt.t := UnOp.from 11 in
    let var_felt_const_10 : Felt.t := UnOp.from 10 in
    let var_felt_const_9 : Felt.t := UnOp.from 9 in
    let var_felt_const_8 : Felt.t := UnOp.from 8 in
    let var_felt_const_7 : Felt.t := UnOp.from 7 in
    let var_felt_const_6 : Felt.t := UnOp.from 6 in
    let var_felt_const_5 : Felt.t := UnOp.from 5 in
    let var_felt_const_4 : Felt.t := UnOp.from 4 in
    let var_felt_const_3 : Felt.t := UnOp.from 3 in
    let var_felt_const_2 : Felt.t := UnOp.from 2 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0_0 : Felt.t := UnOp.from 0 in
    let* var_self : GenerateCodeHash.t N := M.CreateStruct in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [24]%nat := Array.new [var_felt_const_0_0; var_felt_const_1; var_felt_const_2; var_felt_const_3; var_felt_const_4; var_felt_const_5; var_felt_const_6; var_felt_const_7; var_felt_const_8; var_felt_const_9; var_felt_const_10; var_felt_const_11; var_felt_const_12; var_felt_const_13; var_felt_const_14; var_felt_const_15; var_felt_const_16; var_felt_const_17; var_felt_const_18; var_felt_const_19; var_felt_const_20; var_felt_const_21; var_felt_const_22; var_felt_const_23] in
    let var_array_1 : Array.t Felt.t [24]%nat := Array.new [] in
    let* _ : unit := M.for_ var_c0 (* to *) var_c24 (* step *) var_c1 (fun (arg_for_2384_7 : Index.t) =>
      let var_13 : Felt.t := Array.read var_array (arg_for_2384_7, tt) in
      let var_14 : bool := Bool.cmp BoolCmp.Eq var_13 var_felt_const_0_0 in
      let var_15 : Felt.t := M.cast_to_felt var_14 in
      let var_16 : bool := Bool.cmp BoolCmp.Le var_felt_const_1 var_13 in
      let var_17 : bool := Bool.cmp BoolCmp.Lt var_13 var_0 in
      let var_18 : Felt.t := M.cast_to_felt var_16 in
      let var_19 : Felt.t := M.cast_to_felt var_17 in
      let var_20 : Felt.t := BinOp.mul var_18 var_19 in
      let var_21 : bool := Bool.cmp BoolCmp.Le var_0 var_13 in
      let var_22 : bool := Bool.cmp BoolCmp.Lt var_13 var_felt_const_24 in
      let var_23 : Felt.t := M.cast_to_felt var_21 in
      let var_24 : Felt.t := M.cast_to_felt var_22 in
      let var_25 : Felt.t := BinOp.mul var_23 var_24 in
      let var_array_4 : Array.t Felt.t [3]%nat := Array.new [var_15; var_20; var_25] in
      let var_26 : Index.t := M.cast_to_index var_felt_const_0_0 in
      let var_27 : Felt.t := Array.read var_array_4 (var_26, tt) in
      let var_28 : bool := Bool.cmp BoolCmp.Ne var_27 var_felt_const_0 in
      let var_29 : Index.t := M.cast_to_index var_felt_const_1 in
      let var_30 : Felt.t := Array.read var_array_4 (var_29, tt) in
      let var_31 : bool := Bool.cmp BoolCmp.Ne var_30 var_felt_const_0 in
      let var_32 : Index.t := M.cast_to_index var_felt_const_2 in
      let var_33 : Felt.t := Array.read var_array_4 (var_32, tt) in
      let var_34 : bool := Bool.cmp BoolCmp.Ne var_33 var_felt_const_0 in
      let* var_35 : Felt.t := M.if_ var_28 then
        let var_36 : Reg.t := arg_fun_0.(Nonce.dollar_super) in
        let var_37 : NondetReg.t := var_36.(Reg.dollar_super) in
        let var_38 : Felt.t := var_37.(NondetReg.dollar_super) in
        M.yield var_38 else
        let* var_36 : Felt.t := M.if_ var_31 then
          let var_37 : Felt.t := BinOp.sub var_13 var_felt_const_1 in
          let var_38 : Array.t Reg.t [N]%nat := arg_fun_1.(Pegs.dollar_super) in
          let var_39 : Index.t := M.cast_to_index var_37 in
          let var_40 : Reg.t := Array.read var_38 (var_39, tt) in
          let var_41 : NondetReg.t := var_40.(Reg.dollar_super) in
          let var_42 : Felt.t := var_41.(NondetReg.dollar_super) in
          M.yield var_42 else
          let* _ : unit := M.AssertBool var_34 in
          M.yield var_felt_const_0_0 in
        M.yield var_36 in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_2384_7, tt) var_35 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.in) var_array_1 in
    let var_1 : Array.t Felt.t [24]%nat := var_self.(GenerateCodeHash.in) in
    let* var_2 : MultiplyByMExt.t := MultiplyByMExt.compute var_1 in
    let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.stage0) var_2 in
    let var_3 : MultiplyByMExt.t := var_self.(GenerateCodeHash.stage0) in
    let var_array_2 : Array.t Felt.t [4]%nat := Array.new [var_felt_const_0_0; var_felt_const_1; var_felt_const_2; var_felt_const_3] in
    let* var_4 : MultiplyByMExt.t := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_2436_12 : Index.t) (arg_for_2436_12 : MultiplyByMExt.t) =>
      let var_13 : Felt.t := Array.read var_array_2 (arg_for_2436_12, tt) in
      let var_14 : Array.t block$.t [24]%nat := arg_for_2436_12.(MultiplyByMExt.dollar_super) in
      let var_array_4 : Array.t Felt.t [24]%nat := Array.new [] in
      let* var_15 : Index.t := Array.len var_14 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_15 (fun (arg_for_2441_9 : Index.t) =>
        let var_22 : block$.t := Array.read var_14 (arg_for_2441_9, tt) in
        let var_23 : Felt.t := var_22.(block$.dollar_super) in
        let* _ : unit := M.ArrayWrite var_array_4 (arg_for_2441_9, tt) var_23 in
        M.yield tt
      ) in
      let* var_16 : DoExtRoundByIdx.t := DoExtRoundByIdx.compute var_array_4 var_13 in
      let var_17 : Array.t DoExtRoundByIdx.t [4]%nat := var_self.(GenerateCodeHash.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_17 (arg_for_2436_12, tt) var_16 in
      let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.dollar_temp) var_17 in
      let var_18 : Array.t DoExtRoundByIdx.t [4]%nat := var_self.(GenerateCodeHash.dollar_temp) in
      let var_19 : DoExtRoundByIdx.t := Array.read var_18 (arg_for_2436_12, tt) in
      let var_20 : DoExtRound.t := var_19.(DoExtRoundByIdx.dollar_super) in
      let var_21 : MultiplyByMExt.t := var_20.(DoExtRound.dollar_super) in
      M.yield var_21
    ) in
    let var_5 : Array.t block$.t [24]%nat := var_4.(MultiplyByMExt.dollar_super) in
    let var_array_3 : Array.t Felt.t [24]%nat := Array.new [] in
    let* var_6 : Index.t := Array.len var_5 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_6 (fun (arg_for_2459_7 : Index.t) =>
      let var_13 : block$.t := Array.read var_5 (arg_for_2459_7, tt) in
      let var_14 : Felt.t := var_13.(block$.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_2459_7, tt) var_14 in
      M.yield tt
    ) in
    let* var_7 : DoIntRounds.t := DoIntRounds.compute var_array_3 in
    let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.stage2) var_7 in
    let var_8 : DoIntRounds.t := var_self.(GenerateCodeHash.stage2) in
    let var_9 : Array.t Felt.t [24]%nat := var_8.(DoIntRounds.dollar_super) in
    let* var_10 : Array.t Felt.t [24]%nat := M.for_ var_c0 (* to *) var_c4 (* step *) var_c1 (fun (arg_for_2468_13 : Index.t) (arg_for_2468_13 : Array.t Felt.t [24]%nat) =>
      let var_13 : Felt.t := Array.read var_array_2 (arg_for_2468_13, tt) in
      let* var_14 : DoExtRoundByIdx.t := DoExtRoundByIdx.compute arg_for_2468_13 var_13 in
      let var_15 : Array.t DoExtRoundByIdx.t [4]%nat := var_self.(GenerateCodeHash.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_15 (arg_for_2468_13, tt) var_14 in
      let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.dollar_temp_0) var_15 in
      let var_16 : Array.t DoExtRoundByIdx.t [4]%nat := var_self.(GenerateCodeHash.dollar_temp_0) in
      let var_17 : DoExtRoundByIdx.t := Array.read var_16 (arg_for_2468_13, tt) in
      let var_18 : DoExtRound.t := var_17.(DoExtRoundByIdx.dollar_super) in
      let var_19 : MultiplyByMExt.t := var_18.(DoExtRound.dollar_super) in
      let var_20 : Array.t block$.t [24]%nat := var_19.(MultiplyByMExt.dollar_super) in
      let var_array_4 : Array.t Felt.t [24]%nat := Array.new [] in
      let* var_21 : Index.t := Array.len var_20 var_c0 in
      let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_21 (fun (arg_for_2481_9 : Index.t) =>
        let var_22 : block$.t := Array.read var_20 (arg_for_2481_9, tt) in
        let var_23 : Felt.t := var_22.(block$.dollar_super) in
        let* _ : unit := M.ArrayWrite var_array_4 (arg_for_2481_9, tt) var_23 in
        M.yield tt
      ) in
      M.yield var_array_4
    ) in
    let* var_11 : CodeHash.t := CodeHash.compute var_10 in
    let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.dollar_temp_1) var_11 in
    let var_12 : CodeHash.t := var_self.(GenerateCodeHash.dollar_temp_1) in
    let* _ : unit := M.FieldWrite var_self.(GenerateCodeHash.dollar_super) var_12 in
    M.Pure var_self.
End GenerateCodeHash.

Module SetCode.
  Record t {COLORS PEGS : nat} : Set := {
    dollar_super : GenerateCodeHash.t PEGS;
    dollar_temp_0 : GenerateCodeHash.t PEGS;
    dollar_temp : CheckBounds.t COLORS PEGS;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {COLORS PEGS : nat} : MapMod (t COLORS PEGS) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : SetCode.t COLORS PEGS) (arg_fun_1 : Nonce.t) (arg_fun_2 : Pegs.t PEGS) : M.t unit :=
    let var_0 : CheckBounds.t COLORS PEGS := arg_fun_0.(SetCode.dollar_temp) in
    let* _ : unit := CheckBounds.constrain var_0 arg_fun_2 in
    let var_1 : GenerateCodeHash.t PEGS := arg_fun_0.(SetCode.dollar_temp_0) in
    let* _ : unit := GenerateCodeHash.constrain var_1 arg_fun_1 arg_fun_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : Nonce.t) (arg_fun_1 : Pegs.t PEGS) : M.t (SetCode.t COLORS PEGS) :=
    let* var_self : SetCode.t COLORS PEGS := M.CreateStruct in
    let* var_0 : CheckBounds.t COLORS PEGS := CheckBounds.compute arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(SetCode.dollar_temp) var_0 in
    let var_1 : CheckBounds.t COLORS PEGS := var_self.(SetCode.dollar_temp) in
    let* var_2 : GenerateCodeHash.t PEGS := GenerateCodeHash.compute arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(SetCode.dollar_temp_0) var_2 in
    let var_3 : GenerateCodeHash.t PEGS := var_self.(SetCode.dollar_temp_0) in
    let* _ : unit := M.FieldWrite var_self.(SetCode.dollar_super) var_3 in
    M.Pure var_self.
End SetCode.

Module Minimum.
  Record t : Set := {
    dollar_super : Felt.t;
    dollar_temp_0 : NondetReg.t;
    dollar_temp : NondetReg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Minimum.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0_0 : Felt.t := UnOp.from 0 in
    let var_0 : bool := Bool.cmp BoolCmp.Le var_felt_const_0_0 arg_fun_1 in
    let var_1 : bool := Bool.cmp BoolCmp.Lt arg_fun_1 arg_fun_2 in
    let var_2 : Felt.t := M.cast_to_felt var_0 in
    let var_3 : Felt.t := M.cast_to_felt var_1 in
    let var_4 : Felt.t := BinOp.mul var_2 var_3 in
    let var_5 : NondetReg.t := arg_fun_0.(Minimum.dollar_temp) in
    let* _ : unit := NondetReg.constrain var_5 var_4 in
    let var_6 : NondetReg.t := arg_fun_0.(Minimum.dollar_temp_0) in
    let* _ : unit := NondetReg.constrain var_6 var_4 in
    let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
    let var_8 : Felt.t := BinOp.sub var_felt_const_1 var_7 in
    let var_9 : Felt.t := var_5.(NondetReg.dollar_super) in
    let var_array : Array.t Felt.t [2]%nat := Array.new [var_9; var_8] in
    let var_10 : Index.t := M.cast_to_index var_felt_const_0_0 in
    let var_11 : Felt.t := Array.read var_array (var_10, tt) in
    let var_12 : bool := Bool.cmp BoolCmp.Ne var_11 var_felt_const_0 in
    let var_13 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_14 : Felt.t := Array.read var_array (var_13, tt) in
    let var_15 : bool := Bool.cmp BoolCmp.Ne var_14 var_felt_const_0 in
    let* _ : unit := M.if_ var_12 then
      M.yield tt else
      let* _ : unit := M.AssertBool var_15 in
      M.yield tt in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Minimum.t :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0_0 : Felt.t := UnOp.from 0 in
    let* var_self : Minimum.t := M.CreateStruct in
    let var_0 : bool := Bool.cmp BoolCmp.Le var_felt_const_0_0 arg_fun_0 in
    let var_1 : bool := Bool.cmp BoolCmp.Lt arg_fun_0 arg_fun_1 in
    let var_2 : Felt.t := M.cast_to_felt var_0 in
    let var_3 : Felt.t := M.cast_to_felt var_1 in
    let var_4 : Felt.t := BinOp.mul var_2 var_3 in
    let* var_5 : NondetReg.t := NondetReg.compute var_4 in
    let* _ : unit := M.FieldWrite var_self.(Minimum.dollar_temp) var_5 in
    let var_6 : NondetReg.t := var_self.(Minimum.dollar_temp) in
    let* var_7 : NondetReg.t := NondetReg.compute var_4 in
    let* _ : unit := M.FieldWrite var_self.(Minimum.dollar_temp_0) var_7 in
    let var_8 : NondetReg.t := var_self.(Minimum.dollar_temp_0) in
    let var_9 : Felt.t := var_8.(NondetReg.dollar_super) in
    let var_10 : Felt.t := BinOp.sub var_felt_const_1 var_9 in
    let var_11 : Felt.t := var_6.(NondetReg.dollar_super) in
    let var_array : Array.t Felt.t [2]%nat := Array.new [var_11; var_10] in
    let var_12 : Index.t := M.cast_to_index var_felt_const_0_0 in
    let var_13 : Felt.t := Array.read var_array (var_12, tt) in
    let var_14 : bool := Bool.cmp BoolCmp.Ne var_13 var_felt_const_0 in
    let var_15 : Index.t := M.cast_to_index var_felt_const_1 in
    let var_16 : Felt.t := Array.read var_array (var_15, tt) in
    let var_17 : bool := Bool.cmp BoolCmp.Ne var_16 var_felt_const_0 in
    let* var_18 : Felt.t := Arith.select var_14 arg_fun_0 arg_fun_1 in
    let* _ : unit := M.if_ var_14 then
      M.yield tt else
      let* _ : unit := M.AssertBool var_17 in
      M.yield tt in
    let* _ : unit := M.FieldWrite var_self.(Minimum.dollar_super) var_18 in
    M.Pure var_self.
End Minimum.

Module CountColors.
  Record t {N : nat} : Set := {
    dollar_super : Felt.t;
    dollar_temp_0 : Array.t Felt.t [N]%nat;
    dollar_temp : Array.t IsZero.t [N]%nat;
    dollar_array : Array.t IsZero.t [N]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {N : nat} : MapMod (t N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_temp := map_mod α.(dollar_temp);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} {N : nat} (arg_fun_0 : CountColors.t N) (arg_fun_1 : Pegs.t N) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_0 : Array.t Reg.t [N]%nat := arg_fun_1.(Pegs.dollar_super) in
    let var_array : Array.t IsZero.t [N]%nat := Array.new [] in
    let* var_1 : Index.t := Array.len var_0 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_1 (* step *) var_c1 (fun (arg_for_2771_7 : Index.t) =>
      let var_4 : Reg.t := Array.read var_0 (arg_for_2771_7, tt) in
      let var_5 : NondetReg.t := var_4.(Reg.dollar_super) in
      let var_6 : Felt.t := var_5.(NondetReg.dollar_super) in
      let var_7 : Felt.t := BinOp.sub var_6 arg_fun_2 in
      let var_8 : Array.t IsZero.t [N]%nat := arg_fun_0.(CountColors.dollar_temp) in
      let var_9 : Array.t IsZero.t [N]%nat := arg_fun_0.(CountColors.dollar_temp) in
      let var_10 : IsZero.t := Array.read var_9 (arg_for_2771_7, tt) in
      let* _ : unit := IsZero.constrain var_10 var_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2771_7, tt) var_10 in
      M.yield tt
    ) in
    let var_2 : Array.t IsZero.t [N]%nat := arg_fun_0.(CountColors.dollar_array) in
    let* var_3 : Index.t := Array.len var_2 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_2784_7 : Index.t) =>
      let var_4 : IsZero.t := Array.read var_2 (arg_for_2784_7, tt) in
      let var_5 : NondetReg.t := var_4.(IsZero.dollar_super) in
      let var_6 : Felt.t := var_5.(NondetReg.dollar_super) in
      let var_7 : Array.t Felt.t [N]%nat := arg_fun_0.(CountColors.dollar_temp_0) in
      let var_8 : Array.t Felt.t [N]%nat := arg_fun_0.(CountColors.dollar_temp_0) in
      let var_9 : Felt.t := Array.read var_8 (arg_for_2784_7, tt) in
      M.yield tt
    ) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {N : nat} (arg_fun_0 : Pegs.t N) (arg_fun_1 : Felt.t) : M.t (CountColors.t N) :=
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : CountColors.t N := M.CreateStruct in
    let var_0 : Array.t Reg.t [N]%nat := arg_fun_0.(Pegs.dollar_super) in
    let var_array : Array.t IsZero.t [N]%nat := Array.new [] in
    let* var_1 : Index.t := Array.len var_0 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_1 (* step *) var_c1 (fun (arg_for_2734_7 : Index.t) =>
      let var_5 : Reg.t := Array.read var_0 (arg_for_2734_7, tt) in
      let var_6 : NondetReg.t := var_5.(Reg.dollar_super) in
      let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
      let var_8 : Felt.t := BinOp.sub var_7 arg_fun_1 in
      let* var_9 : IsZero.t := IsZero.compute var_8 in
      let var_10 : Array.t IsZero.t [N]%nat := var_self.(CountColors.dollar_temp) in
      let* _ : unit := M.ArrayWrite var_10 (arg_for_2734_7, tt) var_9 in
      let* _ : unit := M.FieldWrite var_self.(CountColors.dollar_temp) var_10 in
      let var_11 : Array.t IsZero.t [N]%nat := var_self.(CountColors.dollar_temp) in
      let var_12 : IsZero.t := Array.read var_11 (arg_for_2734_7, tt) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2734_7, tt) var_12 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(CountColors.dollar_array) var_array in
    let var_2 : Array.t IsZero.t [N]%nat := var_self.(CountColors.dollar_array) in
    let* var_3 : Index.t := Array.len var_2 var_c0 in
    let* var_4 : Felt.t := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_2750_12 : Index.t) (arg_for_2750_12 : Felt.t) =>
      let var_5 : IsZero.t := Array.read var_2 (arg_for_2750_12, tt) in
      let var_6 : NondetReg.t := var_5.(IsZero.dollar_super) in
      let var_7 : Felt.t := var_6.(NondetReg.dollar_super) in
      let var_8 : Felt.t := BinOp.add arg_for_2750_12 var_7 in
      let var_9 : Array.t Felt.t [N]%nat := var_self.(CountColors.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_9 (arg_for_2750_12, tt) var_8 in
      let* _ : unit := M.FieldWrite var_self.(CountColors.dollar_temp_0) var_9 in
      let var_10 : Array.t Felt.t [N]%nat := var_self.(CountColors.dollar_temp_0) in
      let var_11 : Felt.t := Array.read var_10 (arg_for_2750_12, tt) in
      M.yield var_11
    ) in
    let* _ : unit := M.FieldWrite var_self.(CountColors.dollar_super) var_4 in
    M.Pure var_self.
End CountColors.

Module Guess.
  Record t : Set := {
    dollar_super : Component.t;
    dollar_temp : Component.t;
    partial : Reg.t;
    correct : Reg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      partial := map_mod α.(partial);
      correct := map_mod α.(correct);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : Guess.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) : M.t unit :=
    let var_0 : Reg.t := arg_fun_0.(Guess.correct) in
    let* _ : unit := Reg.constrain var_0 arg_fun_1 in
    let var_1 : Reg.t := arg_fun_0.(Guess.partial) in
    let* _ : unit := Reg.constrain var_1 arg_fun_2 in
    let var_2 : Component.t := arg_fun_0.(Guess.dollar_temp) in
    let* _ : unit := Component.constrain var_2 in
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) : M.t Guess.t :=
    let* var_self : Guess.t := M.CreateStruct in
    let* var_0 : Reg.t := Reg.compute arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(Guess.correct) var_0 in
    let var_1 : Reg.t := var_self.(Guess.correct) in
    let* var_2 : Reg.t := Reg.compute arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(Guess.partial) var_2 in
    let var_3 : Reg.t := var_self.(Guess.partial) in
    let* var_4 : Component.t := Component.compute in
    let* _ : unit := M.FieldWrite var_self.(Guess.dollar_temp) var_4 in
    let var_5 : Component.t := var_self.(Guess.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(Guess.dollar_super) var_5 in
    M.Pure var_self.
End Guess.

Module Pair.
  Record t {Fst Snd : nat} : Set := {
    dollar_super : Component.t;
    dollar_temp : Component.t;
    snd : TypeVar.t @Snd;
    fst : TypeVar.t @Fst;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {Fst Snd : nat} : MapMod (t Fst Snd) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      snd := map_mod α.(snd);
      fst := map_mod α.(fst);
    |};
  }.

  Definition constrain {p} `{Prime p} {Fst Snd : nat} (arg_fun_0 : Pair.t Fst Snd) (arg_fun_1 : TypeVar.t @Fst) (arg_fun_2 : TypeVar.t @Snd) : M.t unit :=
    let var_0 : Component.t := arg_fun_0.(Pair.dollar_temp) in
    let* _ : unit := Component.constrain var_0 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {Fst Snd : nat} (arg_fun_0 : TypeVar.t @Fst) (arg_fun_1 : TypeVar.t @Snd) : M.t (Pair.t Fst Snd) :=
    let* var_self : Pair.t Fst Snd := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(Pair.fst) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(Pair.snd) arg_fun_1 in
    let* var_0 : Component.t := Component.compute in
    let* _ : unit := M.FieldWrite var_self.(Pair.dollar_temp) var_0 in
    let var_1 : Component.t := var_self.(Pair.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(Pair.dollar_super) var_1 in
    M.Pure var_self.
End Pair.

Module Zip.
  Record t {Lhs Rhs N : nat} : Set := {
    dollar_super : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat;
    dollar_array : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {Lhs Rhs N : nat} : MapMod (t Lhs Rhs N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_array := map_mod α.(dollar_array);
    |};
  }.

  Definition constrain {p} `{Prime p} {Lhs Rhs N : nat} (arg_fun_0 : Zip.t Lhs Rhs N) (arg_fun_1 : Array.t TypeVar.t @Lhs [N]%nat) (arg_fun_2 : Array.t TypeVar.t @Rhs [N]%nat) : M.t unit :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_2884_7 : Index.t) =>
      let var_6 : Felt.t := M.cast_to_felt arg_for_2884_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2884_7, tt) var_6 in
      M.yield tt
    ) in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat := Array.new [] in
    let* var_4 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_4 (* step *) var_c1 (fun (arg_for_2891_7 : Index.t) =>
      let var_6 : Felt.t := Array.read var_array (arg_for_2891_7, tt) in
      let var_7 : Index.t := M.cast_to_index var_6 in
      let var_8 : TypeVar.t @Lhs := Array.read arg_fun_1 (var_7, tt) in
      let var_9 : Index.t := M.cast_to_index var_6 in
      let var_10 : TypeVar.t @Rhs := Array.read arg_fun_2 (var_9, tt) in
      let var_11 : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat := arg_fun_0.(Zip.dollar_array) in
      let var_12 : Pair.t TypeVar.t @Lhs TypeVar.t @Rhs := Array.read var_11 (arg_for_2891_7, tt) in
      let* _ : unit := Pair.constrain var_12 var_8 var_10 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_2891_7, tt) var_12 in
      M.yield tt
    ) in
    let var_5 : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat := arg_fun_0.(Zip.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {Lhs Rhs N : nat} (arg_fun_0 : Array.t TypeVar.t @Lhs [N]%nat) (arg_fun_1 : Array.t TypeVar.t @Rhs [N]%nat) : M.t (Zip.t Lhs Rhs N) :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : Zip.t Lhs Rhs N := M.CreateStruct in
    let var_0 : Felt.t := UnOp.from (Z.of_nat N) in
    let var_1 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let* _ : unit := M.for_ var_c0 (* to *) var_2 (* step *) var_c1 (fun (arg_for_2856_7 : Index.t) =>
      let var_6 : Felt.t := M.cast_to_felt arg_for_2856_7 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2856_7, tt) var_6 in
      M.yield tt
    ) in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array_0 : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat := Array.new [] in
    let* var_4 : Index.t := Array.len var_array var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_4 (* step *) var_c1 (fun (arg_for_2863_7 : Index.t) =>
      let var_6 : Felt.t := Array.read var_array (arg_for_2863_7, tt) in
      let var_7 : Index.t := M.cast_to_index var_6 in
      let var_8 : TypeVar.t @Lhs := Array.read arg_fun_0 (var_7, tt) in
      let var_9 : Index.t := M.cast_to_index var_6 in
      let var_10 : TypeVar.t @Rhs := Array.read arg_fun_1 (var_9, tt) in
      let* var_11 : Pair.t TypeVar.t @Lhs TypeVar.t @Rhs := Pair.compute var_8 var_10 in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_2863_7, tt) var_11 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(Zip.dollar_array) var_array_0 in
    let var_5 : Array.t (Pair.t TypeVar.t @Lhs TypeVar.t @Rhs) [Array.affine_map]%nat := var_self.(Zip.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(Zip.dollar_super) var_5 in
    M.Pure var_self.
End Zip.

Module AssertArrsEq.
  Record t {T N : nat} : Set := {
    dollar_super : Array.t Component.t [Array.affine_map]%nat;
    dollar_temp_1 : Array.t Component.t [Array.affine_map]%nat;
    dollar_temp_0 : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat;
    dollar_array : Array.t Component.t [Array.affine_map]%nat;
    dollar_temp : Zip.t TypeVar.t @T TypeVar.t @T N;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {T N : nat} : MapMod (t T N) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} {T N : nat} (arg_fun_0 : AssertArrsEq.t T N) (arg_fun_1 : Array.t TypeVar.t @T [N]%nat) (arg_fun_2 : Array.t TypeVar.t @T [N]%nat) : M.t unit :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let var_0 : Zip.t TypeVar.t @T TypeVar.t @T N := arg_fun_0.(AssertArrsEq.dollar_temp) in
    let* _ : unit := Zip.constrain var_0 arg_fun_1 arg_fun_2 in
    let var_1 : Array.t (Pair.t TypeVar.t @T TypeVar.t @T) [Array.affine_map]%nat := var_0.(Zip.dollar_super) in
    let var_2 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t Component.t [Array.affine_map]%nat := Array.new [] in
    let* var_3 : Index.t := Array.len var_1 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_3 (* step *) var_c1 (fun (arg_for_2959_7 : Index.t) =>
      let var_5 : Pair.t TypeVar.t @T TypeVar.t @T := Array.read var_1 (arg_for_2959_7, tt) in
      let var_6 : TypeVar.t @T := var_5.(Pair.fst) in
      let var_7 : TypeVar.t @T := var_5.(Pair.snd) in
      let var_8 : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat := arg_fun_0.(AssertArrsEq.dollar_temp_0) in
      let var_9 : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat := arg_fun_0.(AssertArrsEq.dollar_temp_0) in
      let var_10 : EnsureEq.t TypeVar.t @T := Array.read var_9 (arg_for_2959_7, tt) in
      let* _ : unit := EnsureEq.constrain var_10 var_6 var_7 in
      let var_11 : Array.t Component.t [Array.affine_map]%nat := arg_fun_0.(AssertArrsEq.dollar_temp_1) in
      let var_12 : Array.t Component.t [Array.affine_map]%nat := arg_fun_0.(AssertArrsEq.dollar_temp_1) in
      let var_13 : Component.t := Array.read var_12 (arg_for_2959_7, tt) in
      let* _ : unit := Component.constrain var_13 in
      let* _ : unit := M.ArrayWrite var_array (arg_for_2959_7, tt) var_13 in
      M.yield tt
    ) in
    let var_4 : Array.t Component.t [Array.affine_map]%nat := arg_fun_0.(AssertArrsEq.dollar_array) in
    M.Pure tt.

  Definition compute {p} `{Prime p} {T N : nat} (arg_fun_0 : Array.t TypeVar.t @T [N]%nat) (arg_fun_1 : Array.t TypeVar.t @T [N]%nat) : M.t (AssertArrsEq.t T N) :=
    let var_c0 : Index.t := 0%nat in
    let var_c1 : Index.t := 1%nat in
    let* var_self : AssertArrsEq.t T N := M.CreateStruct in
    let* var_0 : Zip.t TypeVar.t @T TypeVar.t @T N := Zip.compute arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_temp) var_0 in
    let var_1 : Zip.t TypeVar.t @T TypeVar.t @T N := var_self.(AssertArrsEq.dollar_temp) in
    let var_2 : Array.t (Pair.t TypeVar.t @T TypeVar.t @T) [Array.affine_map]%nat := var_1.(Zip.dollar_super) in
    let var_3 : Index.t := UnOp.from (Z.of_nat N) in
    let var_array : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat := Array.new [] in
    let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_temp_0) var_array in
    let var_array_0 : Array.t Component.t [Array.affine_map]%nat := Array.new [] in
    let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_temp_1) var_array_0 in
    let var_array_1 : Array.t Component.t [Array.affine_map]%nat := Array.new [] in
    let* var_4 : Index.t := Array.len var_2 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_4 (* step *) var_c1 (fun (arg_for_2927_7 : Index.t) =>
      let var_6 : Pair.t TypeVar.t @T TypeVar.t @T := Array.read var_2 (arg_for_2927_7, tt) in
      let var_7 : TypeVar.t @T := var_6.(Pair.fst) in
      let var_8 : TypeVar.t @T := var_6.(Pair.snd) in
      let* var_9 : EnsureEq.t TypeVar.t @T := EnsureEq.compute var_7 var_8 in
      let var_10 : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat := var_self.(AssertArrsEq.dollar_temp_0) in
      let* _ : unit := M.ArrayWrite var_10 (arg_for_2927_7, tt) var_9 in
      let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_temp_0) var_10 in
      let var_11 : Array.t (EnsureEq.t TypeVar.t @T) [Array.affine_map]%nat := var_self.(AssertArrsEq.dollar_temp_0) in
      let var_12 : EnsureEq.t TypeVar.t @T := Array.read var_11 (arg_for_2927_7, tt) in
      let* var_13 : Component.t := Component.compute in
      let var_14 : Array.t Component.t [Array.affine_map]%nat := var_self.(AssertArrsEq.dollar_temp_1) in
      let* _ : unit := M.ArrayWrite var_14 (arg_for_2927_7, tt) var_13 in
      let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_temp_1) var_14 in
      let var_15 : Array.t Component.t [Array.affine_map]%nat := var_self.(AssertArrsEq.dollar_temp_1) in
      let var_16 : Component.t := Array.read var_15 (arg_for_2927_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_2927_7, tt) var_16 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_array) var_array_1 in
    let var_5 : Array.t Component.t [Array.affine_map]%nat := var_self.(AssertArrsEq.dollar_array) in
    let* _ : unit := M.FieldWrite var_self.(AssertArrsEq.dollar_super) var_5 in
    M.Pure var_self.
End AssertArrsEq.

Module MakeGuess.
  Record t {COLORS PEGS : nat} : Set := {
    dollar_super : Guess.t;
    dollar_temp_9 : Guess.t;
    dollar_temp_8 : Log.t;
    partialGuesses : Felt.t;
    dollar_temp_7 : Array.t Felt.t [Array.affine_map]%nat;
    dollar_temp_6 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat;
    dollar_temp_5 : Array.t Minimum.t [Array.affine_map]%nat;
    pegsCount : Array.t (CountColors.t PEGS) [Array.affine_map]%nat;
    guessCount : Array.t (CountColors.t PEGS) [Array.affine_map]%nat;
    dollar_array_0 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat;
    dollar_temp_4 : Log.t;
    dollar_temp_3 : Array.t Felt.t [Array.affine_map]%nat;
    dollar_temp_2 : Array.t IsZero.t [Array.affine_map]%nat;
    dollar_array : Array.t IsZero.t [Array.affine_map]%nat;
    dollar_temp_1 : Zip.t Felt.t Felt.t PEGS;
    dollar_temp_0 : AssertArrsEq.t Felt.t 24;
    code : SetCode.t COLORS PEGS;
    dollar_temp : CheckBounds.t COLORS PEGS;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {COLORS PEGS : nat} : MapMod (t COLORS PEGS) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp_9 := map_mod α.(dollar_temp_9);
      dollar_temp_8 := map_mod α.(dollar_temp_8);
      partialGuesses := map_mod α.(partialGuesses);
      dollar_temp_7 := map_mod α.(dollar_temp_7);
      dollar_temp_6 := map_mod α.(dollar_temp_6);
      dollar_temp_5 := map_mod α.(dollar_temp_5);
      pegsCount := map_mod α.(pegsCount);
      guessCount := map_mod α.(guessCount);
      dollar_array_0 := map_mod α.(dollar_array_0);
      dollar_temp_4 := map_mod α.(dollar_temp_4);
      dollar_temp_3 := map_mod α.(dollar_temp_3);
      dollar_temp_2 := map_mod α.(dollar_temp_2);
      dollar_array := map_mod α.(dollar_array);
      dollar_temp_1 := map_mod α.(dollar_temp_1);
      dollar_temp_0 := map_mod α.(dollar_temp_0);
      code := map_mod α.(code);
      dollar_temp := map_mod α.(dollar_temp);
    |};
  }.

  Definition constrain {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : MakeGuess.t COLORS PEGS) (arg_fun_1 : Nonce.t) (arg_fun_2 : Pegs.t PEGS) (arg_fun_3 : CodeHash.t) (arg_fun_4 : Pegs.t PEGS) : M.t unit :=
    let* var_0 : string := String.new Partial guesses: %u in
    let* var_1 : string := String.new Correct guesses: %u in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let var_2 : Felt.t := UnOp.from (Z.of_nat COLORS) in
    let var_3 : CheckBounds.t COLORS PEGS := arg_fun_0.(MakeGuess.dollar_temp) in
    let* _ : unit := CheckBounds.constrain var_3 arg_fun_4 in
    let var_4 : SetCode.t COLORS PEGS := arg_fun_0.(MakeGuess.code) in
    let* _ : unit := SetCode.constrain var_4 arg_fun_1 arg_fun_2 in
    let var_5 : Array.t Felt.t [24]%nat := arg_fun_3.(CodeHash.dollar_super) in
    let var_6 : GenerateCodeHash.t PEGS := var_4.(SetCode.dollar_super) in
    let var_7 : CodeHash.t := var_6.(GenerateCodeHash.dollar_super) in
    let var_8 : Array.t Felt.t [24]%nat := var_7.(CodeHash.dollar_super) in
    let var_9 : AssertArrsEq.t Felt.t 24 := arg_fun_0.(MakeGuess.dollar_temp_0) in
    let* _ : unit := AssertArrsEq.constrain var_9 var_5 var_8 in
    let var_10 : Array.t Reg.t [PEGS]%nat := arg_fun_2.(Pegs.dollar_super) in
    let var_array : Array.t Felt.t [PEGS]%nat := Array.new [] in
    let* var_11 : Index.t := Array.len var_10 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_11 (fun (arg_for_3167_7 : Index.t) =>
      let var_34 : Reg.t := Array.read var_10 (arg_for_3167_7, tt) in
      let var_35 : NondetReg.t := var_34.(Reg.dollar_super) in
      let var_36 : Felt.t := var_35.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_3167_7, tt) var_36 in
      M.yield tt
    ) in
    let var_12 : Array.t Reg.t [PEGS]%nat := arg_fun_4.(Pegs.dollar_super) in
    let var_array_0 : Array.t Felt.t [PEGS]%nat := Array.new [] in
    let* var_13 : Index.t := Array.len var_12 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_13 (fun (arg_for_3176_7 : Index.t) =>
      let var_34 : Reg.t := Array.read var_12 (arg_for_3176_7, tt) in
      let var_35 : NondetReg.t := var_34.(Reg.dollar_super) in
      let var_36 : Felt.t := var_35.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_3176_7, tt) var_36 in
      M.yield tt
    ) in
    let var_14 : Zip.t Felt.t Felt.t PEGS := arg_fun_0.(MakeGuess.dollar_temp_1) in
    let* _ : unit := Zip.constrain var_14 var_array var_array_0 in
    let var_15 : Array.t (Pair.t Felt.t Felt.t) [Array.affine_map]%nat := var_14.(Zip.dollar_super) in
    let var_16 : Index.t := UnOp.from (Z.of_nat PEGS) in
    let var_array_1 : Array.t IsZero.t [Array.affine_map]%nat := Array.new [] in
    let* var_17 : Index.t := Array.len var_15 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_17 (* step *) var_c1 (fun (arg_for_3188_7 : Index.t) =>
      let var_34 : Pair.t Felt.t Felt.t := Array.read var_15 (arg_for_3188_7, tt) in
      let var_35 : Felt.t := var_34.(Pair.fst) in
      let var_36 : Felt.t := var_34.(Pair.snd) in
      let var_37 : Felt.t := BinOp.sub var_35 var_36 in
      let var_38 : Array.t IsZero.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_2) in
      let var_39 : Array.t IsZero.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_2) in
      let var_40 : IsZero.t := Array.read var_39 (arg_for_3188_7, tt) in
      let* _ : unit := IsZero.constrain var_40 var_37 in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_3188_7, tt) var_40 in
      M.yield tt
    ) in
    let var_18 : Array.t IsZero.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_array) in
    let* var_19 : Index.t := Array.len var_18 var_c0 in
    let* var_20 : Felt.t := M.for_ var_c0 (* to *) var_19 (* step *) var_c1 (fun (arg_for_3201_13 : Index.t) (arg_for_3201_13 : Felt.t) =>
      let var_34 : IsZero.t := Array.read var_18 (arg_for_3201_13, tt) in
      let var_35 : NondetReg.t := var_34.(IsZero.dollar_super) in
      let var_36 : Felt.t := var_35.(NondetReg.dollar_super) in
      let var_37 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_3) in
      let var_38 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_3) in
      let var_39 : Felt.t := Array.read var_38 (arg_for_3201_13, tt) in
      M.yield var_39
    ) in
    let var_array_2 : Array.t Felt.t [1]%nat := Array.new [var_20] in
    let* var_21 : Array.t Felt.t [Array.dimension_any]%nat := UnOp.unifiable_cast var_array_2 in
    let var_22 : Log.t := arg_fun_0.(MakeGuess.dollar_temp_4) in
    let* _ : unit := Log.constrain var_22 var_1 var_21 in
    let var_23 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let var_array_3 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_24 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let* _ : unit := M.for_ var_c0 (* to *) var_24 (* step *) var_c1 (fun (arg_for_3217_7 : Index.t) =>
      let var_34 : Felt.t := M.cast_to_felt arg_for_3217_7 in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_3217_7, tt) var_34 in
      M.yield tt
    ) in
    let var_25 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let var_array_4 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := Array.new [] in
    let* var_26 : Index.t := Array.len var_array_3 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_26 (* step *) var_c1 (fun (arg_for_3224_7 : Index.t) =>
      let var_34 : Felt.t := Array.read var_array_3 (arg_for_3224_7, tt) in
      let var_35 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.guessCount) in
      let var_36 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.guessCount) in
      let var_37 : CountColors.t PEGS := Array.read var_36 (arg_for_3224_7, tt) in
      let* _ : unit := CountColors.constrain var_37 arg_fun_4 var_34 in
      let var_38 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.pegsCount) in
      let var_39 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.pegsCount) in
      let var_40 : CountColors.t PEGS := Array.read var_39 (arg_for_3224_7, tt) in
      let* _ : unit := CountColors.constrain var_40 arg_fun_2 var_34 in
      let var_41 : Felt.t := var_37.(CountColors.dollar_super) in
      let var_42 : Felt.t := var_40.(CountColors.dollar_super) in
      let var_43 : Array.t Minimum.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_5) in
      let var_44 : Array.t Minimum.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_5) in
      let var_45 : Minimum.t := Array.read var_44 (arg_for_3224_7, tt) in
      let* _ : unit := Minimum.constrain var_45 var_41 var_42 in
      let var_46 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.guessCount) in
      let var_47 : CountColors.t PEGS := Array.read var_46 (arg_for_3224_7, tt) in
      let var_48 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.pegsCount) in
      let var_49 : CountColors.t PEGS := Array.read var_48 (arg_for_3224_7, tt) in
      let var_50 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_6) in
      let var_51 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_6) in
      let var_52 : block$_0.t PEGS := Array.read var_51 (arg_for_3224_7, tt) in
      let* _ : unit := blockdollar__0.constrain var_52 var_45 var_47 var_49 in
      let* _ : unit := M.ArrayWrite var_array_4 (arg_for_3224_7, tt) var_52 in
      M.yield tt
    ) in
    let var_27 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_array_0) in
    let* var_28 : Index.t := Array.len var_27 var_c0 in
    let* var_29 : Felt.t := M.for_ var_c0 (* to *) var_28 (* step *) var_c1 (fun (arg_for_3252_13 : Index.t) (arg_for_3252_13 : Felt.t) =>
      let var_34 : block$_0.t PEGS := Array.read var_27 (arg_for_3252_13, tt) in
      let var_35 : Minimum.t := var_34.(block$_0.dollar_super) in
      let var_36 : Felt.t := var_35.(Minimum.dollar_super) in
      let var_37 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_7) in
      let var_38 : Array.t Felt.t [Array.affine_map]%nat := arg_fun_0.(MakeGuess.dollar_temp_7) in
      let var_39 : Felt.t := Array.read var_38 (arg_for_3252_13, tt) in
      M.yield var_39
    ) in
    let var_30 : Felt.t := BinOp.sub var_29 var_20 in
    let var_array_5 : Array.t Felt.t [1]%nat := Array.new [var_30] in
    let* var_31 : Array.t Felt.t [Array.dimension_any]%nat := UnOp.unifiable_cast var_array_5 in
    let var_32 : Log.t := arg_fun_0.(MakeGuess.dollar_temp_8) in
    let* _ : unit := Log.constrain var_32 var_0 var_31 in
    let var_33 : Guess.t := arg_fun_0.(MakeGuess.dollar_temp_9) in
    let* _ : unit := Guess.constrain var_33 var_20 var_30 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : Nonce.t) (arg_fun_1 : Pegs.t PEGS) (arg_fun_2 : CodeHash.t) (arg_fun_3 : Pegs.t PEGS) : M.t (MakeGuess.t COLORS PEGS) :=
    let* var_0 : string := String.new Partial guesses: %u in
    let* var_1 : string := String.new Correct guesses: %u in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_c1 : Index.t := 1%nat in
    let var_c0 : Index.t := 0%nat in
    let* var_self : MakeGuess.t COLORS PEGS := M.CreateStruct in
    let var_2 : Felt.t := UnOp.from (Z.of_nat COLORS) in
    let* var_3 : CheckBounds.t COLORS PEGS := CheckBounds.compute arg_fun_3 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp) var_3 in
    let var_4 : CheckBounds.t COLORS PEGS := var_self.(MakeGuess.dollar_temp) in
    let* var_5 : SetCode.t COLORS PEGS := SetCode.compute arg_fun_0 arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.code) var_5 in
    let var_6 : SetCode.t COLORS PEGS := var_self.(MakeGuess.code) in
    let var_7 : Array.t Felt.t [24]%nat := arg_fun_2.(CodeHash.dollar_super) in
    let var_8 : GenerateCodeHash.t PEGS := var_6.(SetCode.dollar_super) in
    let var_9 : CodeHash.t := var_8.(GenerateCodeHash.dollar_super) in
    let var_10 : Array.t Felt.t [24]%nat := var_9.(CodeHash.dollar_super) in
    let* var_11 : AssertArrsEq.t Felt.t 24 := AssertArrsEq.compute var_7 var_10 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_0) var_11 in
    let var_12 : AssertArrsEq.t Felt.t 24 := var_self.(MakeGuess.dollar_temp_0) in
    let var_13 : Array.t Reg.t [PEGS]%nat := arg_fun_1.(Pegs.dollar_super) in
    let var_array : Array.t Felt.t [PEGS]%nat := Array.new [] in
    let* var_14 : Index.t := Array.len var_13 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_14 (fun (arg_for_3020_7 : Index.t) =>
      let var_41 : Reg.t := Array.read var_13 (arg_for_3020_7, tt) in
      let var_42 : NondetReg.t := var_41.(Reg.dollar_super) in
      let var_43 : Felt.t := var_42.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array (arg_for_3020_7, tt) var_43 in
      M.yield tt
    ) in
    let var_15 : Array.t Reg.t [PEGS]%nat := arg_fun_3.(Pegs.dollar_super) in
    let var_array_0 : Array.t Felt.t [PEGS]%nat := Array.new [] in
    let* var_16 : Index.t := Array.len var_15 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_c1 (* step *) var_16 (fun (arg_for_3029_7 : Index.t) =>
      let var_41 : Reg.t := Array.read var_15 (arg_for_3029_7, tt) in
      let var_42 : NondetReg.t := var_41.(Reg.dollar_super) in
      let var_43 : Felt.t := var_42.(NondetReg.dollar_super) in
      let* _ : unit := M.ArrayWrite var_array_0 (arg_for_3029_7, tt) var_43 in
      M.yield tt
    ) in
    let* var_17 : Zip.t Felt.t Felt.t PEGS := Zip.compute var_array var_array_0 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_1) var_17 in
    let var_18 : Zip.t Felt.t Felt.t PEGS := var_self.(MakeGuess.dollar_temp_1) in
    let var_19 : Array.t (Pair.t Felt.t Felt.t) [Array.affine_map]%nat := var_18.(Zip.dollar_super) in
    let var_20 : Index.t := UnOp.from (Z.of_nat PEGS) in
    let var_array_1 : Array.t IsZero.t [Array.affine_map]%nat := Array.new [] in
    let* var_21 : Index.t := Array.len var_19 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_21 (* step *) var_c1 (fun (arg_for_3042_7 : Index.t) =>
      let var_41 : Pair.t Felt.t Felt.t := Array.read var_19 (arg_for_3042_7, tt) in
      let var_42 : Felt.t := var_41.(Pair.fst) in
      let var_43 : Felt.t := var_41.(Pair.snd) in
      let var_44 : Felt.t := BinOp.sub var_42 var_43 in
      let* var_45 : IsZero.t := IsZero.compute var_44 in
      let var_46 : Array.t IsZero.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_2) in
      let* _ : unit := M.ArrayWrite var_46 (arg_for_3042_7, tt) var_45 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_2) var_46 in
      let var_47 : Array.t IsZero.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_2) in
      let var_48 : IsZero.t := Array.read var_47 (arg_for_3042_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_1 (arg_for_3042_7, tt) var_48 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_array) var_array_1 in
    let var_22 : Array.t IsZero.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_array) in
    let* var_23 : Index.t := Array.len var_22 var_c0 in
    let* var_24 : Felt.t := M.for_ var_c0 (* to *) var_23 (* step *) var_c1 (fun (arg_for_3058_13 : Index.t) (arg_for_3058_13 : Felt.t) =>
      let var_41 : IsZero.t := Array.read var_22 (arg_for_3058_13, tt) in
      let var_42 : NondetReg.t := var_41.(IsZero.dollar_super) in
      let var_43 : Felt.t := var_42.(NondetReg.dollar_super) in
      let var_44 : Felt.t := BinOp.add arg_for_3058_13 var_43 in
      let var_45 : Array.t Felt.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_3) in
      let* _ : unit := M.ArrayWrite var_45 (arg_for_3058_13, tt) var_44 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_3) var_45 in
      let var_46 : Array.t Felt.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_3) in
      let var_47 : Felt.t := Array.read var_46 (arg_for_3058_13, tt) in
      M.yield var_47
    ) in
    let var_array_2 : Array.t Felt.t [1]%nat := Array.new [var_24] in
    let* var_25 : Array.t Felt.t [Array.dimension_any]%nat := UnOp.unifiable_cast var_array_2 in
    let* var_26 : Log.t := Log.compute var_1 var_25 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_4) var_26 in
    let var_27 : Log.t := var_self.(MakeGuess.dollar_temp_4) in
    let var_28 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let var_array_3 : Array.t Felt.t [Array.affine_map]%nat := Array.new [] in
    let var_29 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let* _ : unit := M.for_ var_c0 (* to *) var_29 (* step *) var_c1 (fun (arg_for_3078_7 : Index.t) =>
      let var_41 : Felt.t := M.cast_to_felt arg_for_3078_7 in
      let* _ : unit := M.ArrayWrite var_array_3 (arg_for_3078_7, tt) var_41 in
      M.yield tt
    ) in
    let var_30 : Index.t := UnOp.from (Z.of_nat COLORS) in
    let var_array_4 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := Array.new [] in
    let* var_31 : Index.t := Array.len var_array_3 var_c0 in
    let* _ : unit := M.for_ var_c0 (* to *) var_31 (* step *) var_c1 (fun (arg_for_3085_7 : Index.t) =>
      let var_41 : Felt.t := Array.read var_array_3 (arg_for_3085_7, tt) in
      let* var_42 : CountColors.t PEGS := CountColors.compute arg_fun_3 var_41 in
      let var_43 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.guessCount) in
      let* _ : unit := M.ArrayWrite var_43 (arg_for_3085_7, tt) var_42 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.guessCount) var_43 in
      let var_44 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.guessCount) in
      let var_45 : CountColors.t PEGS := Array.read var_44 (arg_for_3085_7, tt) in
      let* var_46 : CountColors.t PEGS := CountColors.compute arg_fun_1 var_41 in
      let var_47 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.pegsCount) in
      let* _ : unit := M.ArrayWrite var_47 (arg_for_3085_7, tt) var_46 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.pegsCount) var_47 in
      let var_48 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.pegsCount) in
      let var_49 : CountColors.t PEGS := Array.read var_48 (arg_for_3085_7, tt) in
      let var_50 : Felt.t := var_45.(CountColors.dollar_super) in
      let var_51 : Felt.t := var_49.(CountColors.dollar_super) in
      let* var_52 : Minimum.t := Minimum.compute var_50 var_51 in
      let var_53 : Array.t Minimum.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_5) in
      let* _ : unit := M.ArrayWrite var_53 (arg_for_3085_7, tt) var_52 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_5) var_53 in
      let var_54 : Array.t Minimum.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_5) in
      let var_55 : Minimum.t := Array.read var_54 (arg_for_3085_7, tt) in
      let var_56 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.guessCount) in
      let var_57 : CountColors.t PEGS := Array.read var_56 (arg_for_3085_7, tt) in
      let var_58 : Array.t (CountColors.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.pegsCount) in
      let var_59 : CountColors.t PEGS := Array.read var_58 (arg_for_3085_7, tt) in
      let* var_60 : block$_0.t PEGS := blockdollar__0.compute var_55 var_57 var_59 in
      let var_61 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_6) in
      let* _ : unit := M.ArrayWrite var_61 (arg_for_3085_7, tt) var_60 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_6) var_61 in
      let var_62 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_6) in
      let var_63 : block$_0.t PEGS := Array.read var_62 (arg_for_3085_7, tt) in
      let* _ : unit := M.ArrayWrite var_array_4 (arg_for_3085_7, tt) var_63 in
      M.yield tt
    ) in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_array_0) var_array_4 in
    let var_32 : Array.t (block$_0.t PEGS) [Array.affine_map]%nat := var_self.(MakeGuess.dollar_array_0) in
    let* var_33 : Index.t := Array.len var_32 var_c0 in
    let* var_34 : Felt.t := M.for_ var_c0 (* to *) var_33 (* step *) var_c1 (fun (arg_for_3122_13 : Index.t) (arg_for_3122_13 : Felt.t) =>
      let var_41 : block$_0.t PEGS := Array.read var_32 (arg_for_3122_13, tt) in
      let var_42 : Minimum.t := var_41.(block$_0.dollar_super) in
      let var_43 : Felt.t := var_42.(Minimum.dollar_super) in
      let var_44 : Felt.t := BinOp.add arg_for_3122_13 var_43 in
      let var_45 : Array.t Felt.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_7) in
      let* _ : unit := M.ArrayWrite var_45 (arg_for_3122_13, tt) var_44 in
      let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_7) var_45 in
      let var_46 : Array.t Felt.t [Array.affine_map]%nat := var_self.(MakeGuess.dollar_temp_7) in
      let var_47 : Felt.t := Array.read var_46 (arg_for_3122_13, tt) in
      M.yield var_47
    ) in
    let var_35 : Felt.t := BinOp.sub var_34 var_24 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.partialGuesses) var_35 in
    let var_array_5 : Array.t Felt.t [1]%nat := Array.new [var_35] in
    let* var_36 : Array.t Felt.t [Array.dimension_any]%nat := UnOp.unifiable_cast var_array_5 in
    let* var_37 : Log.t := Log.compute var_0 var_36 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_8) var_37 in
    let var_38 : Log.t := var_self.(MakeGuess.dollar_temp_8) in
    let* var_39 : Guess.t := Guess.compute var_24 var_35 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_temp_9) var_39 in
    let var_40 : Guess.t := var_self.(MakeGuess.dollar_temp_9) in
    let* _ : unit := M.FieldWrite var_self.(MakeGuess.dollar_super) var_40 in
    M.Pure var_self.
End MakeGuess.

Module MakeGuessWithChecks.
  Record t {COLORS PEGS : nat} : Set := {
    dollar_super : MakeGuess.t COLORS PEGS;
    dollar_temp : Assert.t;
    guess : MakeGuess.t COLORS PEGS;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {COLORS PEGS : nat} : MapMod (t COLORS PEGS) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      dollar_temp := map_mod α.(dollar_temp);
      guess := map_mod α.(guess);
    |};
  }.

  Definition constrain {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : MakeGuessWithChecks.t COLORS PEGS) (arg_fun_1 : Nonce.t) (arg_fun_2 : Pegs.t PEGS) (arg_fun_3 : CodeHash.t) (arg_fun_4 : Pegs.t PEGS) : M.t unit :=
    let* var_0 : string := String.new Guess check post condition failed in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let var_1 : Felt.t := UnOp.from (Z.of_nat PEGS) in
    let var_2 : MakeGuess.t COLORS PEGS := arg_fun_0.(MakeGuessWithChecks.guess) in
    let* _ : unit := MakeGuess.constrain var_2 arg_fun_1 arg_fun_2 arg_fun_3 arg_fun_4 in
    let var_3 : Guess.t := var_2.(MakeGuess.dollar_super) in
    let var_4 : Reg.t := var_3.(Guess.correct) in
    let var_5 : Guess.t := var_2.(MakeGuess.dollar_super) in
    let var_6 : Reg.t := var_5.(Guess.partial) in
    let var_7 : NondetReg.t := var_4.(Reg.dollar_super) in
    let var_8 : Felt.t := var_7.(NondetReg.dollar_super) in
    let var_9 : NondetReg.t := var_6.(Reg.dollar_super) in
    let var_10 : Felt.t := var_9.(NondetReg.dollar_super) in
    let var_11 : Felt.t := BinOp.add var_8 var_10 in
    let var_12 : Felt.t := BinOp.add var_1 var_felt_const_1 in
    let var_13 : bool := Bool.cmp BoolCmp.Le var_felt_const_0 var_11 in
    let var_14 : bool := Bool.cmp BoolCmp.Lt var_11 var_12 in
    let var_15 : Felt.t := M.cast_to_felt var_13 in
    let var_16 : Felt.t := M.cast_to_felt var_14 in
    let var_17 : Felt.t := BinOp.mul var_15 var_16 in
    let var_18 : bool := Bool.cmp BoolCmp.Eq var_17 var_felt_const_0 in
    let var_19 : Felt.t := M.cast_to_felt var_18 in
    let var_20 : Assert.t := arg_fun_0.(MakeGuessWithChecks.dollar_temp) in
    let* _ : unit := Assert.constrain var_20 var_19 var_0 in
    M.Pure tt.

  Definition compute {p} `{Prime p} {COLORS PEGS : nat} (arg_fun_0 : Nonce.t) (arg_fun_1 : Pegs.t PEGS) (arg_fun_2 : CodeHash.t) (arg_fun_3 : Pegs.t PEGS) : M.t (MakeGuessWithChecks.t COLORS PEGS) :=
    let* var_0 : string := String.new Guess check post condition failed in
    let var_felt_const_1 : Felt.t := UnOp.from 1 in
    let var_felt_const_0 : Felt.t := UnOp.from 0 in
    let* var_self : MakeGuessWithChecks.t COLORS PEGS := M.CreateStruct in
    let var_1 : Felt.t := UnOp.from (Z.of_nat PEGS) in
    let* var_2 : MakeGuess.t COLORS PEGS := MakeGuess.compute arg_fun_0 arg_fun_1 arg_fun_2 arg_fun_3 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuessWithChecks.guess) var_2 in
    let var_3 : MakeGuess.t COLORS PEGS := var_self.(MakeGuessWithChecks.guess) in
    let var_4 : Guess.t := var_3.(MakeGuess.dollar_super) in
    let var_5 : Reg.t := var_4.(Guess.correct) in
    let var_6 : Guess.t := var_3.(MakeGuess.dollar_super) in
    let var_7 : Reg.t := var_6.(Guess.partial) in
    let var_8 : NondetReg.t := var_5.(Reg.dollar_super) in
    let var_9 : Felt.t := var_8.(NondetReg.dollar_super) in
    let var_10 : NondetReg.t := var_7.(Reg.dollar_super) in
    let var_11 : Felt.t := var_10.(NondetReg.dollar_super) in
    let var_12 : Felt.t := BinOp.add var_9 var_11 in
    let var_13 : Felt.t := BinOp.add var_1 var_felt_const_1 in
    let var_14 : bool := Bool.cmp BoolCmp.Le var_felt_const_0 var_12 in
    let var_15 : bool := Bool.cmp BoolCmp.Lt var_12 var_13 in
    let var_16 : Felt.t := M.cast_to_felt var_14 in
    let var_17 : Felt.t := M.cast_to_felt var_15 in
    let var_18 : Felt.t := BinOp.mul var_16 var_17 in
    let var_19 : bool := Bool.cmp BoolCmp.Eq var_18 var_felt_const_0 in
    let var_20 : Felt.t := M.cast_to_felt var_19 in
    let* var_21 : Assert.t := Assert.compute var_20 var_0 in
    let* _ : unit := M.FieldWrite var_self.(MakeGuessWithChecks.dollar_temp) var_21 in
    let var_22 : Assert.t := var_self.(MakeGuessWithChecks.dollar_temp) in
    let* _ : unit := M.FieldWrite var_self.(MakeGuessWithChecks.dollar_super) var_3 in
    M.Pure var_self.
End MakeGuessWithChecks.

Module block$.
  Record t : Set := {
    dollar_super : Felt.t;
    g : Felt.t;
    j : BitAnd.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      g := map_mod α.(g);
      j := map_mod α.(j);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : block$.t) (arg_fun_1 : Felt.t) (arg_fun_2 : Felt.t) (arg_fun_3 : BitAnd.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Felt.t) (arg_fun_1 : Felt.t) (arg_fun_2 : BitAnd.t) : M.t block$.t :=
    let* var_self : block$.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(block$.dollar_super) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(block$.g) arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(block$.j) arg_fun_2 in
    M.Pure var_self.
End block$.

Module block$_0.
  Record t {PEGS : nat} : Set := {
    dollar_super : Minimum.t;
    guessCount : CountColors.t PEGS;
    pegsCount : CountColors.t PEGS;
  }.
  Arguments t : clear implicits.

  Global Instance IsMapMop {ρ} `{Prime ρ} {PEGS : nat} : MapMod (t PEGS) := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      guessCount := map_mod α.(guessCount);
      pegsCount := map_mod α.(pegsCount);
    |};
  }.

  Definition constrain {p} `{Prime p} {PEGS : nat} (arg_fun_0 : block$_0.t PEGS) (arg_fun_1 : Minimum.t) (arg_fun_2 : CountColors.t PEGS) (arg_fun_3 : CountColors.t PEGS) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} {PEGS : nat} (arg_fun_0 : Minimum.t) (arg_fun_1 : CountColors.t PEGS) (arg_fun_2 : CountColors.t PEGS) : M.t (block$_0.t PEGS) :=
    let* var_self : block$_0.t PEGS := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(block$_0.dollar_super) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(block$_0.guessCount) arg_fun_1 in
    let* _ : unit := M.FieldWrite var_self.(block$_0.pegsCount) arg_fun_2 in
    M.Pure var_self.
End block$_0.

Module block$_1.
  Record t : Set := {
    dollar_super : Component.t;
    check : Reg.t;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      check := map_mod α.(check);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : block$_1.t) (arg_fun_1 : Component.t) (arg_fun_2 : Reg.t) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : Component.t) (arg_fun_1 : Reg.t) : M.t block$_1.t :=
    let* var_self : block$_1.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(block$_1.dollar_super) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(block$_1.check) arg_fun_1 in
    M.Pure var_self.
End block$_1.

Module block$_2.
  Record t : Set := {
    dollar_super : MultiplyByCirculant.t;
    chunk : Array.t Felt.t [4]%nat;
  }.

  Global Instance IsMapMop {ρ} `{Prime ρ} : MapMod t := {
    map_mod α := {|
      dollar_super := map_mod α.(dollar_super);
      chunk := map_mod α.(chunk);
    |};
  }.

  Definition constrain {p} `{Prime p} (arg_fun_0 : block$_2.t) (arg_fun_1 : MultiplyByCirculant.t) (arg_fun_2 : Array.t Felt.t [4]%nat) : M.t unit :=
    M.Pure tt.

  Definition compute {p} `{Prime p} (arg_fun_0 : MultiplyByCirculant.t) (arg_fun_1 : Array.t Felt.t [4]%nat) : M.t block$_2.t :=
    let* var_self : block$_2.t := M.CreateStruct in
    let* _ : unit := M.FieldWrite var_self.(block$_2.dollar_super) arg_fun_0 in
    let* _ : unit := M.FieldWrite var_self.(block$_2.chunk) arg_fun_1 in
    M.Pure var_self.
End block$_2.
