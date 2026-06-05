Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.LookupRangeCheck.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module CircuitVersion.
  Inductive t : Set :=
  | InsecureUnanchoredBase
  | AnchoredBase.
End CircuitVersion.

Module EccConfig.
  Record t : Set := {
    advices : list Column.t;
    lagrange_coeffs : list Column.t;
    lookup_config : LookupRangeCheckConfig.t;
    version : CircuitVersion.t;
  }.
End EccConfig.

Definition gate (name summary : string) : Config.Event.t :=
  Config.Event.CreateGate (Gate.make
    name
    None
    [GateConstraint.make summary (Expr.Named summary (Expr.named_cell name))]).

Definition configure
    (advices : list Column.t)
    (lagrange_coeffs : list Column.t)
    (lookup_config : LookupRangeCheckConfig.t)
    (version : CircuitVersion.t)
    : EccConfig.t * Config.Trace :=
  ({|
    EccConfig.advices := advices;
    EccConfig.lagrange_coeffs := lagrange_coeffs;
    EccConfig.lookup_config := lookup_config;
    EccConfig.version := version;
  |},
  [
    Config.Event.ConfigureChip
      "EccChip"
      "Pallas curve point constraints used by Orchard"
      [
        "halo2_gadgets::ecc::chip";
        "halo2_gadgets::ecc::chip::witness_point";
        "halo2_gadgets::ecc::chip::add";
        "halo2_gadgets::ecc::chip::add_incomplete";
        "halo2_gadgets::ecc::chip::mul";
        "halo2_gadgets::ecc::chip::mul_fixed"
      ];
    gate "witness point" "x/y satisfy the Pallas curve equation";
    gate "witness non-identity point" "witnessed point is not the identity";
    gate "complete addition" "complete addition formula for two assigned points";
    gate "incomplete addition" "incomplete addition formula used by fixed-base mul";
    gate "LSB check" "scalar least-significant-bit decomposition";
    gate "overflow checks" "overflow limb decomposition during variable-base mul";
    gate "q_mul_1 == 1 checks" "first variable-base scalar-mul row shape";
    gate "q_mul_2 == 1 checks" "second variable-base scalar-mul row shape";
    gate "q_mul_3 == 1 checks" "third variable-base scalar-mul row shape";
    gate "Full-width fixed-base scalar mul" "full-width fixed-base scalar multiplication";
    gate "Short fixed-base mul gate" "short scalar fixed-base multiplication";
    gate "Canonicity checks" "base-field scalar canonicity checks";
    gate "Running sum coordinates check" "running-sum coordinates for fixed-base mul"
  ]).

Definition construct (cfg : EccConfig.t) : Synth.Event.t :=
  Synth.Event.ConstructChip "EccChip".

Definition witness_point (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "Point::new" ["witness affine point"];
    Synth.Event.Region "witness point" [
      RegionEvent.Note "assign x/y coordinates and constrain curve equation"
    ];
    Synth.Event.Return name
  ].

Definition witness_non_identity_point (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "NonIdentityPoint::new" ["witness affine point"];
    Synth.Event.Region "witness non-identity point" [
      RegionEvent.Note "assign x/y coordinates and constrain non-identity"
    ];
    Synth.Event.Return name
  ].

Definition scalar_fixed (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "ScalarFixed::new" ["scalar witness"];
    Synth.Event.Return name
  ].

Definition scalar_fixed_short (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "ScalarFixedShort::new" ["magnitude"; "sign"];
    Synth.Event.Return name
  ].

Definition scalar_var_from_base (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "ScalarVar::from_base" ["base-field cell"];
    Synth.Event.Return name
  ].

Definition fixed_mul (name base scalar : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "FixedPoint::mul" [base; scalar];
    Synth.Event.Region "fixed-base scalar multiplication" [
      RegionEvent.Note "use full-width or short fixed-base mul gates"
    ];
    Synth.Event.Return name
  ].

Definition variable_mul (name point scalar : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "NonIdentityPoint::mul" [point; scalar];
    Synth.Event.Region "variable-base scalar multiplication" [
      RegionEvent.Note "use anchored or historical unanchored base depending on circuit version"
    ];
    Synth.Event.Return name
  ].

Definition add (name left right : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "Point::add" [left; right];
    Synth.Event.Region "complete addition" [
      RegionEvent.Note "assign sum point and constrain complete addition gate"
    ];
    Synth.Event.Return name
  ].

Definition constrain_equal (name left right : string) : Synth.Event.t :=
  Synth.Event.ConstrainEqual name (CellRef.named left) (CellRef.named right).
