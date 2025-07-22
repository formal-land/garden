Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.blake3.constantsOld.

(*
/// A state at a single instance of time.
///
/// Rows `0` and `2` are saved as `2` `16` bit limbs.
/// Rows `1` and `3` are saved as `32` boolean values.
#[repr(C)]
pub struct Blake3State<T> {
    pub row0: [[T; U32_LIMBS]; 4],
    pub row1: [[T; 32]; 4],
    pub row2: [[T; U32_LIMBS]; 4],
    pub row3: [[T; 32]; 4],
}
*)
Module Blake3State.
  Record t {T : Set} : Set := {
    row0 : Array.t (Array.t T U32_LIMBS) 4;
    row1 : Array.t (Array.t T 32) 4;
    row2 : Array.t (Array.t T U32_LIMBS) 4;
    row3 : Array.t (Array.t T 32) 4;
  }.
  Arguments t : clear implicits.

  Module Valid.
    Record t {T : Set} (P : T -> Prop) (x : Blake3State.t T) : Prop := {
      row0 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(row0);
      row1 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(row1);
      row2 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(row2);
      row3 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(row3);
    }.
  End Valid.
End Blake3State.

(*
/// Full round columns.
#[repr(C)]
pub struct FullRound<T> {
    
    /// The outputs after applying the first half of the column quarter round functions.
    pub state_prime: Blake3State<T>,

    /// The outputs after the first sub round.
    pub state_middle: Blake3State<T>,

    /// The outputs after applying the first half of the diagonal quarter round functions.
    pub state_middle_prime: Blake3State<T>,

    /// This will also be the input to the next row.
    pub state_output: Blake3State<T>,
}
*)
Module FullRound.
  Record t {T : Set} : Set := {
    state_prime : Blake3State.t T;
    state_middle : Blake3State.t T;
    state_middle_prime : Blake3State.t T;
    state_output : Blake3State.t T;
  }.
  Arguments t : clear implicits.

  Module Valid.
    Record t {T : Set} (P : T -> Prop) (x : FullRound.t T) : Prop := {
      state_prime : Blake3State.Valid.t P x.(state_prime);
      state_middle : Blake3State.Valid.t P x.(state_middle);
      state_middle_prime : Blake3State.Valid.t P x.(state_middle_prime);
      state_output : Blake3State.Valid.t P x.(state_output);
    }.
  End Valid.
End FullRound.

(* Main Blake3 columns structure *)
(*
#[repr(C)]
pub struct Blake3Cols<T> {
    // The inputs to the hash function.
    pub inputs: [[T; 32]; 16],

    // The chaining values are the first eight outputs of the previous compression.
    pub chaining_values: [[[T; 32]; 4]; 2],

    // A few auxiliary values use to flesh out the first state.
    pub counter_low: [T; 32],
    pub counter_hi: [T; 32],
    pub block_len: [T; 32],
    pub flags: [T; 32],

    // It should be possible to remove these two but this makes a negligible difference to the overall width of the trace.
    pub initial_row0: [[T; U32_LIMBS]; 4],
    pub initial_row2: [[T; U32_LIMBS]; 4],

    pub full_rounds: [FullRound<T>; 7],

    pub final_round_helpers: [[T; 32]; 4],

    pub outputs: [[[T; 32]; 4]; 4],
}
*)
(* Main Blake3 columns structure *)
Module Blake3Cols.
  Record t {T : Set} : Set := {
    inputs : Array.t (Array.t T 32) 16;
    chaining_values : Array.t (Array.t (Array.t T 32) 4) 2;
    counter_low : Array.t T 32;
    counter_hi : Array.t T 32;
    block_len : Array.t T 32;
    flags : Array.t T 32;
    initial_row0 : Array.t (Array.t T U32_LIMBS) 4;
    initial_row2 : Array.t (Array.t T U32_LIMBS) 4;
    full_rounds : Array.t (FullRound.t T) 7;
    final_round_helpers : Array.t (Array.t T 32) 4;
    outputs : Array.t (Array.t (Array.t T 32) 4) 4;
  }.
  Arguments t : clear implicits.

  Module Valid.
    Record t {T : Set} (P : T -> Prop) (x : Blake3Cols.t T) : Prop := {
      inputs : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(inputs);
      chaining_values : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun val => P val))) x.(chaining_values);
      counter_low : Array.Valid.t (fun val => P val) x.(counter_low);
      counter_hi : Array.Valid.t (fun val => P val) x.(counter_hi);
      block_len : Array.Valid.t (fun val => P val) x.(block_len);
      flags : Array.Valid.t (fun val => P val) x.(flags);
      initial_row0 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(initial_row0);
      initial_row2 : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(initial_row2);
      full_rounds : Array.Valid.t (FullRound.Valid.t P) x.(full_rounds);
      final_round_helpers : Array.Valid.t (Array.Valid.t (fun val => P val)) x.(final_round_helpers);
      outputs : Array.Valid.t (Array.Valid.t (Array.Valid.t (fun val => P val))) x.(outputs);
    }.
  End Valid.
End Blake3Cols.

(* 
#[repr(C)]
pub(crate) struct QuarterRound<'a, T, U> {
    // The inputs to the quarter round function.
    pub a: &'a [T; U32_LIMBS],
    pub b: &'a [T; 32],
    pub c: &'a [T; U32_LIMBS],
    pub d: &'a [T; 32],

    pub m_two_i: &'a [U; U32_LIMBS], // m_{2i}

    // The state after the first half of the quarter round function.
    pub a_prime: &'a [T; U32_LIMBS],
    pub b_prime: &'a [T; 32],
    pub c_prime: &'a [T; U32_LIMBS],
    pub d_prime: &'a [T; 32],

    pub m_two_i_plus_one: &'a [U; U32_LIMBS], // m_{2i + 1}

    // The output from the quarter round function.
    pub a_output: &'a [T; U32_LIMBS],
    pub b_output: &'a [T; 32],
    pub c_output: &'a [T; U32_LIMBS],
    pub d_output: &'a [T; 32],
}
 *)
Module QuarterRound.
  Record t {T U : Set} : Set := {
    a : Array.t T U32_LIMBS;
    b : Array.t T 32;
    c : Array.t T U32_LIMBS;
    d : Array.t T 32;
    m_two_i : Array.t U U32_LIMBS;
    a_prime : Array.t T U32_LIMBS;
    b_prime : Array.t T 32;
    c_prime : Array.t T U32_LIMBS;
    d_prime : Array.t T 32;
    m_two_i_plus_one : Array.t U U32_LIMBS;
    a_output : Array.t T U32_LIMBS;
    b_output : Array.t T 32;
    c_output : Array.t T U32_LIMBS;
    d_output : Array.t T 32;
  }.
  Arguments t : clear implicits.

  Module Valid.
    Record t {T U : Set} (P_T : T -> Prop) (P_U : U -> Prop) (x : QuarterRound.t T U) : Prop := {
      a : Array.Valid.t P_T x.(a);
      b : Array.Valid.t P_T x.(b);
      c : Array.Valid.t P_T x.(c);
      d : Array.Valid.t P_T x.(d);
      m_two_i : Array.Valid.t P_U x.(m_two_i);
      a_prime : Array.Valid.t P_T x.(a_prime);
      b_prime : Array.Valid.t P_T x.(b_prime);
      c_prime : Array.Valid.t P_T x.(c_prime);
      d_prime : Array.Valid.t P_T x.(d_prime);
      m_two_i_plus_one : Array.Valid.t P_U x.(m_two_i_plus_one);
      a_output : Array.Valid.t P_T x.(a_output);
      b_output : Array.Valid.t P_T x.(b_output);
      c_output : Array.Valid.t P_T x.(c_output);
      d_output : Array.Valid.t P_T x.(d_output);
    }.
  End Valid.
End QuarterRound.

(* pub const NUM_BLAKE3_COLS: usize = size_of::<Blake3Cols<u8>>(); 
simplified arithmetic result in Plonky3 Rust files is 9168.
*)
Definition NUM_BLAKE3_COLS : Z := 9168.