Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.chips.gadgets.add.
Require Import Garden.Brevis.compiler.word.
Require Import Garden.Brevis.primitives.consts.

Module AddSubValueCols.
  Record t : Set := {
    add_operation : AddGadget.t;
    operand_1 : Word.t;
    operand_2 : Word.t;
    is_add : Z;
    is_sub : Z;
  }.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := {|
      add_operation := M.map_mod x.(add_operation);
      operand_1 := M.map_mod x.(operand_1);
      operand_2 := M.map_mod x.(operand_2);
      is_add := M.map_mod x.(is_add);
      is_sub := M.map_mod x.(is_sub);
    |};
  }.

  Global Instance IsGenerate : MGenerate.C t := {
    generate :=
      [[
        {|
          add_operation := MGenerate.generate (||);
          operand_1 := MGenerate.generate (||);
          operand_2 := MGenerate.generate (||);
          is_add := MGenerate.generate (||);
          is_sub := MGenerate.generate (||);
        |}
      ]];
  }.
End AddSubValueCols.

Module AddSubCols.
  Record t : Set := {
    values : Array.t AddSubValueCols.t ADD_SUB_DATAPAR;
  }.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := {|
      values := M.map_mod x.(values);
    |};
  }.

  Global Instance IsGenerate : MGenerate.C t := {
    generate :=
      [[
        {|
          values := MGenerate.generate (||);
        |}
      ]];
  }.
End AddSubCols.
