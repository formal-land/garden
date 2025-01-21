Require Import Coq.Logic.Eqdep.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z.

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
  Inductive t : Set :=
  | Add : t -> t -> t
  | Mul : t -> t -> t
  | Sub : t -> t -> t
  | One : t
  | Zero : t.

  Fixpoint eval (x : t) : Z :=
    match x with
    | Add x1 x2 => eval x1 + eval x2
    | Mul x1 x2 => eval x1 * eval x2
    | Sub x1 x2 => eval x1 - eval x2
    | One => 1
    | Zero => 0
    end.
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
  | Steps.Round _ => Variable_.One
  | _ => Variable_.Zero
  end.

Lemma mode_round_correct :
  forall (self : Variable_.t) (step : Steps.t),
    Variable_.eval (mode_round self step) =
    match step with
    | Steps.Round _ => Z.of_nat 1
    | Steps.Sponge _ => Z.of_nat 0
    end.
Proof.
  intros self step.
  destruct step as [n | s];
  simpl; reflexivity.
Qed.

Definition is_round (self : Variable_.t) (step : Steps.t) : Variable_.t :=
  mode_round self step.

Lemma is_round_correct :
  forall (self : Variable_.t) (step : Steps.t),
    Variable_.eval (is_round self step) =
    match step with
    | Steps.Round _ => Z.of_nat 1
    | Steps.Sponge _ => Z.of_nat 0
    end.
Proof.
  intros self step.
  unfold is_round.
  apply mode_round_correct.
Qed.

Definition is_boolean (x : Variable_.t) : Variable_.t :=
  Variable_.Mul x (Variable_.Sub x Variable_.One).

Module Keccak.
  Fixpoint var_two_pow (n : nat) : Variable_.t :=
    match n with
    | 0%nat => Variable_.One
    | S n' => Variable_.Mul (Variable_.Add Variable_.One Variable_.One) (var_two_pow n')
    end.

  Lemma var_two_pow_correct :
    forall (n : nat),
      Variable_.eval (var_two_pow n) = 2 ^ Z.of_nat n.
  Proof.
    induction n as [| n' IHn].
    { reflexivity. }
    {
      simpl.
      rewrite IHn.
      destruct (2 ^ Z.of_nat n').
      admit.
    }
  Admitted.

  Definition Self := Variable_.t.

  Parameter constrain : Self -> Constraint.t -> Variable_.t -> Variable_.t -> Self.

  Definition nth_or_default {A : Set} (default : A) (l : list A) (n : nat) : A :=
    List.nth n l default.

  Lemma nth_or_default_correct :
    forall {A : Set} (default : A) (l : list A) (n : nat),
      Z.of_nat n < Z.of_nat (List.length l) ->
      List.nth n l default = nth_or_default default l n.
  Proof.
    intros A default l n H.
    unfold nth_or_default.
    reflexivity.
  Qed.

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
    nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * y)).

  Lemma grid_100_is_valid :
    forall (quarters : list Variable_.t) (y x q : nat),
      Z.of_nat (List.length quarters) = 100 ->
      grid_100 quarters y x q = nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * y)).
  Proof.
    intros quarters y x q H.
    unfold grid_100.
    reflexivity.
  Qed.

  Definition grid_20 (quarters : list Variable_.t) (x q : nat) : Variable_.t :=
    nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * x).

  Lemma grid_20_is_valid :
    forall (quarters : list Variable_.t) (x q : nat),
      Z.of_nat (List.length quarters) = 20 ->
      grid_20 quarters x q = nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * x).
  Proof.
    intros quarters x q H.
    unfold grid_20.
    reflexivity.
  Qed.

  Definition grid_80 (quarters : list Variable_.t) (i x q : nat) : Variable_.t :=
    nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * i)).

  Lemma grid_80_is_valid :
    forall (quarters : list Variable_.t) (i x q : nat),
      Z.of_nat (List.length quarters) = 80 ->
      grid_80 quarters i x q = nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * i)).
  Proof.
    intros quarters i x q H.
    unfold grid_80.
    reflexivity.
  Qed.

  Definition grid_400 (quarters : list Variable_.t) (i y x q : nat) : Variable_.t :=
    nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * (y + (Z.to_nat DIM) * i))).

  Lemma grid_400_is_valid :
    forall (quarters : list Variable_.t) (i y x q : nat),
      Z.of_nat (List.length quarters) = 400 ->
      grid_400 quarters i y x q = nth_or_default Variable_.Zero quarters (q + (Z.to_nat QUARTERS) * (x + (Z.to_nat DIM) * (y + (Z.to_nat DIM) * i))).
  Proof.
    intros quarters i y x q H.
    unfold grid_400.
    reflexivity.
  Qed.

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
    if Z.of_nat (List.length quarters) =? 100 then
          Variable_.Add (grid_100 quarters y' x 0) (Variable_.Add
            (Variable_.Mul (var_two_pow 16) (grid_100 quarters y' x 1))
            (Variable_.Add
            (Variable_.Mul (var_two_pow 32) (grid_100 quarters y' x 2))
            (Variable_.Mul (var_two_pow 48) (grid_100 quarters y' x 3))))
      else
        from_quarters_TODO
    | None =>
      if Z.of_nat (List.length quarters) =? 20 then
          Variable_.Add (grid_20 quarters x 0) (Variable_.Add
            (Variable_.Mul (var_two_pow 16) (grid_20 quarters x 1))
            (Variable_.Add
            (Variable_.Mul (var_two_pow 32) (grid_20 quarters x 2))
            (Variable_.Mul (var_two_pow 48) (grid_20 quarters x 3))))
        else
          from_quarters_TODO
    end.

  Lemma from_quarters_correct :
    forall (quarters : list Variable_.t) (y : option nat) (x : nat),
      Z.of_nat (List.length quarters) = 100 ->
      match y with
      | Some y' =>
        from_quarters quarters y x = Variable_.Add (grid_100 quarters y' x 0) (Variable_.Add
          (Variable_.Mul (var_two_pow 16) (grid_100 quarters y' x 1))
          (Variable_.Add
          (Variable_.Mul (var_two_pow 32) (grid_100 quarters y' x 2))
          (Variable_.Mul (var_two_pow 48) (grid_100 quarters y' x 3))))
      | None => True
      end.
  Proof.
    intros quarters y x H.
    unfold from_quarters.
    destruct y as [y' |].
    { simpl.
      rewrite H.
      reflexivity. }
    { reflexivity. }
  Qed.
    
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
            (List.seq 0 (Z.to_nat THETA_DENSE_C_LEN)).

  Definition vec_remainder_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaRemainderC (Z.of_nat idx)))
            (List.seq 0 (Z.to_nat DIM)).

  Definition vec_dense_rot_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaDenseRotC (Z.of_nat idx)))
            (List.seq 0 (Z.to_nat DIM)).

  Definition vec_shifts_c (self : Variable_.t) : list Variable_.t :=
    List.map (fun idx => variable (ColumnAlias.ThetaShiftsC (Z.of_nat idx)))
            (List.seq 0 (Z.to_nat THETA_SHIFTS_C_LEN)).

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
    if Z.of_nat (List.length shifts) =? 400 then
      match i with
      | Some i_z =>
          let i_nat := Z.to_nat i_z in
          let shifts_i := nth_or_default Variable_.Zero shifts i_nat in
          let shifts_100_i := nth_or_default Variable_.Zero shifts (100 + i_nat) in
          let shifts_200_i := nth_or_default Variable_.Zero shifts (200 + i_nat) in
          let shifts_300_i := nth_or_default Variable_.Zero shifts (300 + i_nat) in
          Variable_.Add shifts_i (Variable_.Add (Variable_.Mul (var_two_pow 1) shifts_100_i)
                                                (Variable_.Add (Variable_.Mul (var_two_pow 2) shifts_200_i)
                                                              (Variable_.Mul (var_two_pow 3) shifts_300_i)))
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
              Variable_.Add shifts_0 (Variable_.Add (Variable_.Mul (var_two_pow 1) shifts_1)
                                                    (Variable_.Add (Variable_.Mul (var_two_pow 2) shifts_2)
                                                                  (Variable_.Mul (var_two_pow 3) shifts_3)))
          | _, _, _ => Variable_.Zero
          end
      end
    else if Z.of_nat (List.length shifts) =? 80 then
      match x, q with
      | Some x_z, Some q_z =>
          let x_nat := Z.to_nat x_z in
          let q_nat := Z.to_nat q_z in
          let shifts_0 := grid_80 shifts 0 x_nat q_nat in
          let shifts_1 := grid_80 shifts 1 x_nat q_nat in
          let shifts_2 := grid_80 shifts 2 x_nat q_nat in
          let shifts_3 := grid_80 shifts 3 x_nat q_nat in
          Variable_.Add shifts_0 (Variable_.Add (Variable_.Mul (var_two_pow 1) shifts_1)
                                                (Variable_.Add (Variable_.Mul (var_two_pow 2) shifts_2)
                                                              (Variable_.Mul (var_two_pow 3) shifts_3)))
      | _, _ => Variable_.Zero
      end
    else Variable_.Zero.

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
    let state_c := List.repeat (List.repeat Variable_.Zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_d := List.repeat (List.repeat Variable_.Zero (Z.to_nat QUARTERS)) (Z.to_nat DIM) in
    let state_e := List.repeat (List.repeat (List.repeat Variable_.Zero (Z.to_nat QUARTERS)) (Z.to_nat DIM)) (Z.to_nat DIM) in

    let indices := List.seq 0 (Z.to_nat DIM) in
   let self :=
  List.fold_left
    (fun self (x : nat) =>
        let word_c := from_quarters (vec_dense_c self) None x in
        let rem_c := from_quarters (vec_remainder_c self) None x in
        let rot_c := from_quarters (vec_dense_rot_c self) None x in

        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (Variable_.Sub (Variable_.Mul word_c (var_two_pow 1))
                      (Variable_.Add (Variable_.Mul (quotient_c self x) (var_two_pow 64)) rem_c)) in
        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (Variable_.Sub rot_c (Variable_.Add (quotient_c self x) rem_c)) in
        let self := constrain self (Constraint.ThetaWordC (Z.of_nat x)) (is_round self step)
                    (is_boolean (quotient_c self x)) in

        let quarters := List.seq 0 (Z.to_nat QUARTERS) in
        List.fold_left
        (fun self (q : nat) =>
          let q := Z.of_nat q in
          let state_c_q :=
            Variable_.Add (state_a 0 (Z.of_nat x) q)
            (Variable_.Add (state_a 1 (Z.of_nat x) q)
            (Variable_.Add (state_a 2 (Z.of_nat x) q)
            (Variable_.Add (state_a 3 (Z.of_nat x) q)
            (state_a 4 (Z.of_nat x) q)))) in
      
          let self := constrain self (Constraint.ThetaShiftsC (Z.of_nat x) q) (is_round self step)
                        (Variable_.Sub state_c_q
                        (from_shifts (vec_shifts_c self) None None (Some (Z.of_nat x)) (Some q))) in
      
          let state_d_q :=
            Variable_.Add (shifts_c self 0 ((Z.of_nat x + DIM - 1) mod DIM) q)
            (expand_rot_c self ((Z.of_nat x + 1) mod DIM) q) in
      
          let state_e_q :=
            List.map
              (fun y => Variable_.Add (state_a y (Z.of_nat x) q) state_d_q)
              (List.map Z.of_nat (List.seq 0 (Z.to_nat DIM))) in
      
          self
        ) quarters self
    ) indices self in
state_e.

End Keccak.