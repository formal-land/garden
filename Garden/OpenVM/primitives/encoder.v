Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.

(*
pub struct Encoder {
    var_cnt: usize,
    flag_cnt: usize,
    max_flag_degree: u32,
    pts: Vec<Vec<u32>>,
    reserve_invalid: bool,
}
*)
Module Encoder.
  Record t : Set := {
    var_cnt : Z;
    flag_cnt : Z;
    max_flag_degree : Z;
    pts : list (list Z);
    reserve_invalid : bool;
  }.
End Encoder.
