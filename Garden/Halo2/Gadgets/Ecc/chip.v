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

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.witness_point.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.add_incomplete.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.add.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.full_width.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.short.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul_fixed.base_field_elem.configure
      meta in
  meta.
