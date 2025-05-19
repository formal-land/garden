Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

(*
pub(crate) fn eval_round_flags<AB: AirBuilder>(builder: &mut AB) {
    let main = builder.main();
    let (local, next) = (
        main.row_slice(0).expect("The matrix is empty?"),
        main.row_slice(1).expect("The matrix only has 1 row?"),
    );
    let local: &KeccakCols<AB::Var> = ( *local).borrow();
    let next: &KeccakCols<AB::Var> = ( *next).borrow();

    // Initially, the first step flag should be 1 while the others should be 0.
    builder.when_first_row().assert_one(local.step_flags[0]);
    builder
        .when_first_row()
        .assert_zeros::<NUM_ROUNDS_MIN_1, _>(local.step_flags[1..].try_into().unwrap());

    builder
        .when_transition()
        .assert_zeros::<NUM_ROUNDS, _>(array::from_fn(|i| {
            local.step_flags[i] - next.step_flags[(i + 1) % NUM_ROUNDS]
        }));
}
*)
Definition eval_round_flags (is_first_row is_transition : bool) (local next : KeccakCols.t) :
    M.t unit :=
  let* _ := when is_first_row [[
    assert_one (| Array.get (| local.(KeccakCols.step_flags), 0 |) |)
  ]] in
  let* _ := when is_first_row [[
    assert_zeros (| Array.slice_from local.(KeccakCols.step_flags) 1 |)
  ]] in
  let* _ := when is_transition [[
    assert_zeros (N := NUM_ROUNDS) (| Array.from_fn (| fun i => [[
      M.sub (|
        Array.get (| local.(KeccakCols.step_flags), i |),
        Array.get (| next.(KeccakCols.step_flags), M.mod_ (| i + 1, NUM_ROUNDS |) |)
      |)
    ]] |) |)
  ]] in
  M.Pure tt.
