Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.halo2_poseidon.p128pow5t3.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition round_constant_entry : Set :=
  Fixed.t * string * Z.

Definition round_constant_row : Set :=
  Selector.t * list round_constant_entry.

Definition full_round_row
    (round : nat)
    (annotation_0 annotation_1 annotation_2 : string)
    : round_constant_row :=
  (Selector.QPoseidonFull, [
    (Fixed.LagrangeCoeffs2, annotation_0,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round 0);
    (Fixed.LagrangeCoeffs3, annotation_1,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round 1);
    (Fixed.LagrangeCoeffs4, annotation_2,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round 2)
  ]).

Definition partial_round_row
    (round_a round_b : nat)
    (annotation_a_0 annotation_a_1 annotation_a_2 : string)
    (annotation_b_0 annotation_b_1 annotation_b_2 : string)
    : round_constant_row :=
  (Selector.QPoseidonPartial, [
    (Fixed.LagrangeCoeffs2, annotation_a_0,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_a 0);
    (Fixed.LagrangeCoeffs3, annotation_a_1,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_a 1);
    (Fixed.LagrangeCoeffs4, annotation_a_2,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_a 2);
    (Fixed.LagrangeCoeffs5, annotation_b_0,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_b 0);
    (Fixed.LagrangeCoeffs6, annotation_b_1,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_b 1);
    (Fixed.LagrangeCoeffs7, annotation_b_2,
      Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant round_b 2)
  ]).

Definition permutation_rows : list round_constant_row := [
  full_round_row 0%nat "round_0 rc_0" "round_0 rc_1" "round_0 rc_2";
  full_round_row 1%nat "round_1 rc_0" "round_1 rc_1" "round_1 rc_2";
  full_round_row 2%nat "round_2 rc_0" "round_2 rc_1" "round_2 rc_2";
  full_round_row 3%nat "round_3 rc_0" "round_3 rc_1" "round_3 rc_2";
  partial_round_row 4%nat 5%nat "round_4 rc_0" "round_4 rc_1" "round_4 rc_2" "round_5 rc_0" "round_5 rc_1" "round_5 rc_2";
  partial_round_row 6%nat 7%nat "round_6 rc_0" "round_6 rc_1" "round_6 rc_2" "round_7 rc_0" "round_7 rc_1" "round_7 rc_2";
  partial_round_row 8%nat 9%nat "round_8 rc_0" "round_8 rc_1" "round_8 rc_2" "round_9 rc_0" "round_9 rc_1" "round_9 rc_2";
  partial_round_row 10%nat 11%nat "round_10 rc_0" "round_10 rc_1" "round_10 rc_2" "round_11 rc_0" "round_11 rc_1" "round_11 rc_2";
  partial_round_row 12%nat 13%nat "round_12 rc_0" "round_12 rc_1" "round_12 rc_2" "round_13 rc_0" "round_13 rc_1" "round_13 rc_2";
  partial_round_row 14%nat 15%nat "round_14 rc_0" "round_14 rc_1" "round_14 rc_2" "round_15 rc_0" "round_15 rc_1" "round_15 rc_2";
  partial_round_row 16%nat 17%nat "round_16 rc_0" "round_16 rc_1" "round_16 rc_2" "round_17 rc_0" "round_17 rc_1" "round_17 rc_2";
  partial_round_row 18%nat 19%nat "round_18 rc_0" "round_18 rc_1" "round_18 rc_2" "round_19 rc_0" "round_19 rc_1" "round_19 rc_2";
  partial_round_row 20%nat 21%nat "round_20 rc_0" "round_20 rc_1" "round_20 rc_2" "round_21 rc_0" "round_21 rc_1" "round_21 rc_2";
  partial_round_row 22%nat 23%nat "round_22 rc_0" "round_22 rc_1" "round_22 rc_2" "round_23 rc_0" "round_23 rc_1" "round_23 rc_2";
  partial_round_row 24%nat 25%nat "round_24 rc_0" "round_24 rc_1" "round_24 rc_2" "round_25 rc_0" "round_25 rc_1" "round_25 rc_2";
  partial_round_row 26%nat 27%nat "round_26 rc_0" "round_26 rc_1" "round_26 rc_2" "round_27 rc_0" "round_27 rc_1" "round_27 rc_2";
  partial_round_row 28%nat 29%nat "round_28 rc_0" "round_28 rc_1" "round_28 rc_2" "round_29 rc_0" "round_29 rc_1" "round_29 rc_2";
  partial_round_row 30%nat 31%nat "round_30 rc_0" "round_30 rc_1" "round_30 rc_2" "round_31 rc_0" "round_31 rc_1" "round_31 rc_2";
  partial_round_row 32%nat 33%nat "round_32 rc_0" "round_32 rc_1" "round_32 rc_2" "round_33 rc_0" "round_33 rc_1" "round_33 rc_2";
  partial_round_row 34%nat 35%nat "round_34 rc_0" "round_34 rc_1" "round_34 rc_2" "round_35 rc_0" "round_35 rc_1" "round_35 rc_2";
  partial_round_row 36%nat 37%nat "round_36 rc_0" "round_36 rc_1" "round_36 rc_2" "round_37 rc_0" "round_37 rc_1" "round_37 rc_2";
  partial_round_row 38%nat 39%nat "round_38 rc_0" "round_38 rc_1" "round_38 rc_2" "round_39 rc_0" "round_39 rc_1" "round_39 rc_2";
  partial_round_row 40%nat 41%nat "round_40 rc_0" "round_40 rc_1" "round_40 rc_2" "round_41 rc_0" "round_41 rc_1" "round_41 rc_2";
  partial_round_row 42%nat 43%nat "round_42 rc_0" "round_42 rc_1" "round_42 rc_2" "round_43 rc_0" "round_43 rc_1" "round_43 rc_2";
  partial_round_row 44%nat 45%nat "round_44 rc_0" "round_44 rc_1" "round_44 rc_2" "round_45 rc_0" "round_45 rc_1" "round_45 rc_2";
  partial_round_row 46%nat 47%nat "round_46 rc_0" "round_46 rc_1" "round_46 rc_2" "round_47 rc_0" "round_47 rc_1" "round_47 rc_2";
  partial_round_row 48%nat 49%nat "round_48 rc_0" "round_48 rc_1" "round_48 rc_2" "round_49 rc_0" "round_49 rc_1" "round_49 rc_2";
  partial_round_row 50%nat 51%nat "round_50 rc_0" "round_50 rc_1" "round_50 rc_2" "round_51 rc_0" "round_51 rc_1" "round_51 rc_2";
  partial_round_row 52%nat 53%nat "round_52 rc_0" "round_52 rc_1" "round_52 rc_2" "round_53 rc_0" "round_53 rc_1" "round_53 rc_2";
  partial_round_row 54%nat 55%nat "round_54 rc_0" "round_54 rc_1" "round_54 rc_2" "round_55 rc_0" "round_55 rc_1" "round_55 rc_2";
  partial_round_row 56%nat 57%nat "round_56 rc_0" "round_56 rc_1" "round_56 rc_2" "round_57 rc_0" "round_57 rc_1" "round_57 rc_2";
  partial_round_row 58%nat 59%nat "round_58 rc_0" "round_58 rc_1" "round_58 rc_2" "round_59 rc_0" "round_59 rc_1" "round_59 rc_2";
  full_round_row 60%nat "round_60 rc_0" "round_60 rc_1" "round_60 rc_2";
  full_round_row 61%nat "round_61 rc_0" "round_61 rc_1" "round_61 rc_2";
  full_round_row 62%nat "round_62 rc_0" "round_62 rc_1" "round_62 rc_2";
  full_round_row 63%nat "round_63 rc_0" "round_63 rc_1" "round_63 rc_2"
].
