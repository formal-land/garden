Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

(*
pub const DIM: usize = 5;
pub const QUARTERS: usize = 4;
*)

Definition QUARTERS : Z := 4.
Definition DIM : Z := 5.
Definition THETA_DENSE_C_LEN : Z := QUARTERS * DIM.
Definition THETA_STATE_A_LEN : Z := QUARTERS * DIM * DIM.
Definition THETA_SHIFTS_C_LEN : Z := 4 * QUARTERS * DIM.
Definition THETA_EXPAND_ROT_C_LEN : Z := QUARTERS * DIM.


Module Sponges.
  Parameter t : Set.
End Sponges.

Module Steps.
  Inductive t : Set :=
  | Round (n : Z)
  | Sponge (s : Sponges.t)
  .
End Steps.

Module Variable_.
  Parameter t : Set.

  Parameter add : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter one : t.
  Parameter zero : t.
End Variable_.

Module Constraint.
  Parameter t : Set.

  Parameter BooleanityPadding : Z -> t.
  Parameter AbsorbZeroPad : Z -> t.
  Parameter AbsorbRootZero : Z -> t.
  Parameter AbsorbXor : Z -> t.
  Parameter AbsorbShifts : Z -> t.
  Parameter PadAtEnd : t.
  Parameter PaddingSuffix : Z -> t.
  Parameter SqueezeShifts : Z -> t.
  Parameter ThetaWordC : Z -> t.
  Parameter ThetaRotatedC : Z -> t.
  Parameter ThetaQuotientC : Z -> t.
  Parameter ThetaShiftsC : Z -> Z -> t.
  Parameter PiRhoWordE : Z -> Z -> t.
  Parameter PiRhoRotatedE : Z -> Z -> t.
  Parameter PiRhoShiftsE : Z -> Z -> Z -> t.
  Parameter ChiShiftsB : Z -> Z -> Z -> t.
  Parameter ChiShiftsSum : Z -> Z -> Z -> t.
  Parameter IotaStateG : Z -> t.
End Constraint.

Module ColumnAlias.
  Parameter t : Set.

  Parameter HashIndex : t.
  Parameter BlockIndex : t.
  Parameter StepIndex : t.

  Parameter Input : Z -> t.
  Parameter Output : Z -> t.

  Parameter ThetaShiftsC : Z -> t.
  Parameter ThetaDenseC : Z -> t.
  Parameter ThetaQuotientC : Z -> t.
  Parameter ThetaRemainderC : Z -> t.
  Parameter ThetaDenseRotC : Z -> t.
  Parameter ThetaExpandRotC : Z -> t.
  Parameter PiRhoShiftsE : Z -> t.
  Parameter PiRhoDenseE : Z -> t.
  Parameter PiRhoQuotientE : Z -> t.
  Parameter PiRhoRemainderE : Z -> t.
  Parameter PiRhoDenseRotE : Z -> t.
  Parameter PiRhoExpandRotE : Z -> t.
  Parameter ChiShiftsB : Z -> t.
  Parameter ChiShiftsSum : Z -> t.

  Parameter SpongeNewState : Z -> t.
  Parameter SpongeZeros : Z -> t.
  Parameter SpongeBytes : Z -> t.
  Parameter SpongeShifts : Z -> t.

  Parameter RoundNumber : t.
  Parameter RoundConstants : Z -> t.

  Parameter PadLength : t.
  Parameter TwoToPad : t.
  Parameter PadSuffix : Z -> t.
  Parameter PadBytesFlags : Z -> t.
End ColumnAlias.

Parameter variable : ColumnAlias.t -> Variable_.t.

Definition quotient_c (self : Variable_.t) (x : nat) : Variable_.t :=
  variable (ColumnAlias.ThetaQuotientC (Z.of_nat x)).

Definition mode_round (self : Variable_.t) (step : Steps.t) : Variable_.t :=
  match step with
  | Steps.Round _ => Variable_.one
  | _ => Variable_.zero
  end.

Definition is_round (self : Variable_.t) (step : Steps.t) : Variable_.t :=
  mode_round self step.

Definition is_boolean (x : Variable_.t) : Variable_.t :=
  Variable_.mul x (Variable_.sub x Variable_.one).

Module Keccak.
  Fixpoint var_two_pow (n : nat) : Variable_.t :=
    match n with
    | 0 => Variable_.one
    | S n' => Variable_.mul (Variable_.add Variable_.one Variable_.one) (var_two_pow n')
    end.

  Definition Self := Variable_.t.

  Parameter constrain : Self -> Constraint.t -> Variable_.t -> Variable_.t -> Self.

  Definition nth_or_default {A : Set} (default : A) (l : list A) (n : nat) : A :=
    List.nth n l default.

  (*
    #[macro_export]
    macro_rules! grid {
      (5, $v:expr) => {{
          |x: usize| $v[x].clone()
      }};
      (20, $v:expr) => {{
          |x: usize, q: usize| $v[q + QUARTERS * x].clone()
      }};
      (80, $v:expr) => {{
          |i: usize, x: usize, q: usize| $v[q + QUARTERS * (x + DIM * i)].clone()
      }};
      (100, $v:expr) => {{
          |y: usize, x: usize, q: usize| $v[q + QUARTERS * (x + DIM * y)].clone()
      }};
      (400, $v:expr) => {{
          |i: usize, y: usize, x: usize, q: usize| {
              $v[q + QUARTERS * (x + DIM * (y + DIM * i))].clone()
          }
      }};
    }
  *)

  Definition grid_100 (quarters : list Variable_.t) (y x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * y)).

  Definition grid_20 (quarters : list Variable_.t) (x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * x).

  Definition grid_80 (quarters : list Variable_.t) (i x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * i)).

  Definition grid_400 (quarters : list Variable_.t) (i y x q : nat) : Variable_.t :=
    nth_or_default Variable_.zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * (y + (Z.to_nat DIM) * i))).

  Axiom from_quarters_TODO : Variable_.t.

  (*
  fn from_quarters(quarters: &[Self::Variable], y: Option<usize>, x: usize) -> Self::Variable {
        if let Some(y) = y {
            assert!(quarters.len() == 100, "Invalid length of quarters");
            let quarters = grid!(100, quarters);
            quarters(y, x, 0)
                + Self::two_pow(16) * quarters(y, x, 1)
                + Self::two_pow(32) * quarters(y, x, 2)
                + Self::two_pow(48) * quarters(y, x, 3)
        } else {
            assert!(quarters.len() == 20, "Invalid length of quarters");
            let quarters = grid!(20, quarters);
            quarters(x, 0)
                + Self::two_pow(16) * quarters(x, 1)
                + Self::two_pow(32) * quarters(x, 2)
                + Self::two_pow(48) * quarters(x, 3)
        }
    }
  *)

  Definition from_quarters (quarters : list Variable_.t) (y : option nat) (x : nat) : Variable_.t :=
    match y with
    | Some y' =>
      if length quarters =? 100 then
          Variable_.add (grid_100 quarters y' x 0) (Variable_.add
            (Variable_.mul (var_two_pow 16) (grid_100 quarters y' x 1))
            (Variable_.add
            (Variable_.mul (var_two_pow 32) (grid_100 quarters y' x 2))
            (Variable_.mul (var_two_pow 48) (grid_100 quarters y' x 3))))
      else
        from_quarters_TODO
    | None =>
      if length quarters =? 20 then
          Variable_.add (grid_20 quarters x 0) (Variable_.add
            (Variable_.mul (var_two_pow 16) (grid_20 quarters x 1))
            (Variable_.add
            (Variable_.mul (var_two_pow 32) (grid_20 quarters x 2))
            (Variable_.mul (var_two_pow 48) (grid_20 quarters x 3))))
        else
          from_quarters_TODO
    end.

  Definition grid_index (length i y x q : Z) : Z :=
    match length with
    | 5%Z => x
    | 20%Z => q + QUARTERS * x
    | 80%Z => q + QUARTERS * (x + DIM * i)
    | 100%Z => q + QUARTERS * (x + DIM * y)
    | 400%Z => q + QUARTERS * (x + DIM * (y + DIM * i))
    | _ => 0
    end.

  Definition vec_dense_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaDenseC (Z.of_nat idx)))
            (seq 0 (Z.to_nat THETA_DENSE_C_LEN)).

  Definition vec_remainder_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaRemainderC (Z.of_nat idx)))
            (seq 0 (Z.to_nat DIM)).

  Definition vec_dense_rot_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaDenseRotC (Z.of_nat idx)))
            (seq 0 (Z.to_nat DIM)).

  Definition vec_shifts_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaShiftsC (Z.of_nat idx)))
            (seq 0 (Z.to_nat THETA_SHIFTS_C_LEN)).

  Definition shifts_c (self : Variable_.t) (i x q : Z) : Variable_.t :=
    let idx := grid_index THETA_SHIFTS_C_LEN i 0 x q in
    variable (ColumnAlias.Input idx).
  
  Definition expand_rot_c (self : Variable_.t) (x q : Z) : Variable_.t :=
    let idx := grid_index THETA_EXPAND_ROT_C_LEN 0 0 x q in
    variable (ColumnAlias.Input idx).

  Definition state_a (y x q : Z) : Variable_.t :=
    let idx := grid_index THETA_STATE_A_LEN 0 y x q in
    variable (ColumnAlias.Input idx).
  
  (*
  fn from_shifts(
        shifts: &[Self::Variable],
        i: Option<usize>,
        y: Option<usize>,
        x: Option<usize>,
        q: Option<usize>,
    ) -> Self::Variable {
        match shifts.len() {
            400 => {
                if let Some(i) = i {
                    auto_clone_array!(shifts);
                    shifts(i)
                        + Self::two_pow(1) * shifts(100 + i)
                        + Self::two_pow(2) * shifts(200 + i)
                        + Self::two_pow(3) * shifts(300 + i)
                } else {
                    let shifts = grid!(400, shifts);
                    shifts(0, y.unwrap(), x.unwrap(), q.unwrap())
                        + Self::two_pow(1) * shifts(1, y.unwrap(), x.unwrap(), q.unwrap())
                        + Self::two_pow(2) * shifts(2, y.unwrap(), x.unwrap(), q.unwrap())
                        + Self::two_pow(3) * shifts(3, y.unwrap(), x.unwrap(), q.unwrap())
                }
            }
            80 => {
                let shifts = grid!(80, shifts);
                shifts(0, x.unwrap(), q.unwrap())
                    + Self::two_pow(1) * shifts(1, x.unwrap(), q.unwrap())
                    + Self::two_pow(2) * shifts(2, x.unwrap(), q.unwrap())
                    + Self::two_pow(3) * shifts(3, x.unwrap(), q.unwrap())
            }
            _ => panic!("Invalid length of shifts"),
        }
    }
  *)

  Definition from_shifts (shifts : list Variable_.t) (i y x q : option Z) : Variable_.t :=
    if List.length shifts =? 400 then
      match i with
      | Some i_z =>
          let i_nat := Z.to_nat i_z in
          let shifts_i := nth_or_default Variable_.zero shifts i_nat in
          let shifts_100_i := nth_or_default Variable_.zero shifts (100 + i_nat) in
          let shifts_200_i := nth_or_default Variable_.zero shifts (200 + i_nat) in
          let shifts_300_i := nth_or_default Variable_.zero shifts (300 + i_nat) in
          Variable_.add shifts_i (Variable_.add (Variable_.mul (var_two_pow 1) shifts_100_i)
                                                (Variable_.add (Variable_.mul (var_two_pow 2) shifts_200_i)
                                                              (Variable_.mul (var_two_pow 3) shifts_300_i)))
      | None =>
          match y, x, q with
          | Some y_z, Some x_z, Some q_z =>
              let y_nat := Z.to_nat y_z in
              let x_nat := Z.to_nat x_z in
              let q_nat := Z.to_nat q_z in
              let shifts_0 := grid_400 shifts 0 y_nat x_nat q_nat in
              let shifts_1 := grid_400 shifts 1 y_nat x_nat q_nat in
              let shifts_2 := grid_400 shifts 2 y_nat x_nat q_nat in
              let shifts_3 := grid_400 shifts 3 y_nat x_nat q_nat in
              Variable_.add shifts_0 (Variable_.add (Variable_.mul (var_two_pow 1) shifts_1)
                                                    (Variable_.add (Variable_.mul (var_two_pow 2) shifts_2)
                                                                  (Variable_.mul (var_two_pow 3) shifts_3)))
          | _, _, _ => Variable_.zero
          end
      end
    else if List.length shifts =? 80 then
      match x, q with
      | Some x_z, Some q_z =>
          let x_nat := Z.to_nat x_z in
          let q_nat := Z.to_nat q_z in
          let shifts_0 := grid_80 shifts 0 x_nat q_nat in
          let shifts_1 := grid_80 shifts 1 x_nat q_nat in
          let shifts_2 := grid_80 shifts 2 x_nat q_nat in
          let shifts_3 := grid_80 shifts 3 x_nat q_nat in
          Variable_.add shifts_0 (Variable_.add (Variable_.mul (var_two_pow 1) shifts_1)
                                                (Variable_.add (Variable_.mul (var_two_pow 2) shifts_2)
                                                              (Variable_.mul (var_two_pow 3) shifts_3)))
      | _, _ => Variable_.zero
      end
    else Variable_.zero.

  (*
  fn constrain_theta(&mut self, step: Steps) -> Vec<Vec<Vec<Self::Variable>>> {
        // Define vectors storing expressions which are not in the witness layout for efficiency
        let mut state_c = vec![vec![Self::zero(); QUARTERS]; DIM];
        let mut state_d = vec![vec![Self::zero(); QUARTERS]; DIM];
        let mut state_e = vec![vec![vec![Self::zero(); QUARTERS]; DIM]; DIM];

        for x in 0..DIM {
            let word_c = Self::from_quarters(&self.vec_dense_c(), None, x);
            let rem_c = Self::from_quarters(&self.vec_remainder_c(), None, x);
            let rot_c = Self::from_quarters(&self.vec_dense_rot_c(), None, x);

            self.constrain(
                ThetaWordC(x),
                self.is_round(step),
                word_c * Self::two_pow(1)
                    - (self.quotient_c(x) * Self::two_pow(64) + rem_c.clone()),
            );
            self.constrain(
                ThetaRotatedC(x),
                self.is_round(step),
                rot_c - (self.quotient_c(x) + rem_c),
            );
            self.constrain(
                ThetaQuotientC(x),
                self.is_round(step),
                Self::is_boolean(self.quotient_c(x)),
            );

            for q in 0..QUARTERS {
                state_c[x][q] = self.state_a(0, x, q)
                    + self.state_a(1, x, q)
                    + self.state_a(2, x, q)
                    + self.state_a(3, x, q)
                    + self.state_a(4, x, q);
                self.constrain(
                    ThetaShiftsC(x, q),
                    self.is_round(step),
                    state_c[x][q].clone()
                        - Self::from_shifts(&self.vec_shifts_c(), None, None, Some(x), Some(q)),
                );

                state_d[x][q] =
                    self.shifts_c(0, (x + DIM - 1) % DIM, q) + self.expand_rot_c((x + 1) % DIM, q);

                for (y, column_e) in state_e.iter_mut().enumerate() {
                    column_e[x][q] = self.state_a(y, x, q) + state_d[x][q].clone();
                }
            }
        }
        state_e
    }
  *)

  Definition constrain_theta (self : Variable_.t) (step : Steps.t) : list (list (list Variable_.t)) :=
    let state_c := List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_d := List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_e := List.repeat (List.repeat (List.repeat Variable_.zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM) in

    let indices := seq 0 (Z.to_nat DIM) in
   let self :=
  fold_left
    (fun self (x : nat) =>
        let word_c := from_quarters (vec_dense_c self) None x in
        let rem_c := from_quarters (vec_remainder_c self) None x in
        let rot_c := from_quarters (vec_dense_rot_c self) None x in

        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (Variable_.sub (Variable_.mul word_c (var_two_pow 1))
                      (Variable_.add (Variable_.mul (quotient_c self x) (var_two_pow 64)) rem_c)) in
        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (Variable_.sub rot_c (Variable_.add (quotient_c self x) rem_c)) in
        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (is_boolean (quotient_c self x)) in

        let quarters := seq 0 (Z.to_nat QUARTERS) in
        fold_left
        (fun self (q : nat) =>
          let q := Z.of_nat q in
          let state_c_q :=
            Variable_.add (state_a 0 (Z.of_nat x) q)
            (Variable_.add (state_a 1 (Z.of_nat x) q)
            (Variable_.add (state_a 2 (Z.of_nat x) q)
            (Variable_.add (state_a 3 (Z.of_nat x) q)
            (state_a 4 (Z.of_nat x) q)))) in
      
          let self := constrain self (Constraint.ThetaShiftsC (Z.of_nat x) q) (is_round self step)
                        (Variable_.sub state_c_q
                        (from_shifts (vec_shifts_c self) None None (Some (Z.of_nat x)) (Some q))) in
      
          let state_d_q :=
            Variable_.add (shifts_c self 0 ((Z.of_nat x + DIM - 1) mod DIM) q)
            (expand_rot_c self ((Z.of_nat x + 1) mod DIM) q) in
      
          let state_e_q :=
            List.map
              (fun y => Variable_.add (state_a y (Z.of_nat x) q) state_d_q)
              (List.map Z.of_nat (seq 0 (Z.to_nat DIM))) in
      
          self
        ) quarters self
    ) indices self in
state_e.
End Keccak.