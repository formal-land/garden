Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.compiler.word.
Require Import Garden.Brevis.machine.builder.range_check.

Module AddGadget.
  Record t : Set := {
    value : Word.t;
    carry : Array.t Z 3;
  }.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := {|
      value := M.map_mod x.(value);
      carry := M.map_mod x.(carry);
    |};
  }.

  Global Instance IsGenerate : MGenerate.C t := {
    generate :=
      [[
        {|
          value := MGenerate.generate (||);
          carry := MGenerate.generate (||);
        |}
      ]];
  }.

  Definition eval {p} `{Prime p}
      (a b : Array.t Z 4)
      (cols : t)
      (is_real : Z) :
      M.t unit :=
    let one := 1 in
    let base := 256 mod p in

    let* _ := M.when is_real (
      let overflow_0 := a.[0] +F b.[0] -F cols.(value).[0] in
      let overflow_1 := a.[1] +F b.[1] -F cols.(value).[1] +F cols.(carry).[0] in
      let overflow_2 := a.[2] +F b.[2] -F cols.(value).[2] +F cols.(carry).[1] in
      let overflow_3 := a.[3] +F b.[3] -F cols.(value).[3] +F cols.(carry).[2] in

      let* _ := M.assert_zero (overflow_0 *F (overflow_0 -F base)) in
      let* _ := M.assert_zero (overflow_1 *F (overflow_1 -F base)) in
      let* _ := M.assert_zero (overflow_2 *F (overflow_2 -F base)) in
      let* _ := M.assert_zero (overflow_3 *F (overflow_3 -F base)) in

      let* _ := M.assert_zero (cols.(carry).[0] *F (overflow_0 -F base)) in
      let* _ := M.assert_zero (cols.(carry).[1] *F (overflow_1 -F base)) in
      let* _ := M.assert_zero (cols.(carry).[2] *F (overflow_2 -F base)) in

      let* _ := M.assert_zero ((cols.(carry).[0] -F one) *F overflow_0) in
      let* _ := M.assert_zero ((cols.(carry).[1] -F one) *F overflow_1) in
      let* _ := M.assert_zero ((cols.(carry).[2] -F one) *F overflow_2) in

      let* _ := M.assert_bool cols.(carry).[0] in
      let* _ := M.assert_bool cols.(carry).[1] in
      let* _ := M.assert_bool cols.(carry).[2] in
      let* _ := M.assert_bool is_real in

      M.Pure tt
    ) in
    let* _ :=
      let* _ := slice_range_check_u8 a is_real in
      let* _ := slice_range_check_u8 b is_real in
      let* _ := slice_range_check_u8 cols.(value) is_real in
      M.pure tt in
    M.Pure tt.
End AddGadget.
