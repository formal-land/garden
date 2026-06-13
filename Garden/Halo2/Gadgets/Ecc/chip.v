Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Ecc.chip.witness_point.
Require Garden.Halo2.Gadgets.Ecc.chip.add_incomplete.
Require Garden.Halo2.Gadgets.Ecc.chip.add.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.
Require Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.
Require Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.full_width.
Require Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.short.
Require Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.base_field_elem.

Definition configure : 𝓒 columns unit :=
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.witness_point.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.add_incomplete.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.add.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.full_width.configure in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.short.configure in
  do🞵
    Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.base_field_elem.configure in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.witness_point.synthesize in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.add_incomplete.synthesize in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.add.synthesize in
  let🞵 '(base_x, base_y) :=
    𝓛.AddRegion
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccChipDummyBase)
      "variable-base scalar mul dummy base" (fun region =>
      let x := Cell.advice region Advice.A0 0 in
      let y := Cell.advice region Advice.A1 0 in
      return🞵 (x, y)) in
  let🞵 _ :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.synthesize
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulVariableBase)
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulOverflowS)
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulOverflowLookup)
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulOverflowCheck)
      base_x
      base_x
      base_y in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.synthesize in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.full_width.synthesize in
  do🞵 Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.short.synthesize in
  Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.base_field_elem.synthesize.
