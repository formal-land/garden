Require Import LLZK.M.
Require Import LLZK.translated.

Module Module_Line_3.
  Import Module_Line_3.

  Module NoConstraints.
    Lemma constrain_eq {p} `{Prime p} (self : NoConstraints.t) (x : Felt.t) :
      {{ NoConstraints.constrain self x 🔽 tt, True }}.
    Proof.
      apply Run.Pure.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ NoConstraints.compute x 🔽 NoConstraints.Make, True }}.
    Proof.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := NoConstraints.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End NoConstraints.
End Module_Line_3.

Module Module_Line_20.
  Import Module_Line_20.

  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ global_add x y 🔽 (x + y) mod p, True }}.
  Proof.
    unfold global_add.
    apply Run.Pure.
  Qed.

  Module Adder.
    Definition spec {p} `{Prime p} (x y : Felt.t) : Adder.t :=
      {|
        Adder.sum := (x + y) mod p;
      |}.

    Lemma contrain_implies {p} `{Prime p}
        (self : Adder.t)
        (x y : Felt.t) :
      let self := map_mod self in
      {{ Adder.constrain self x y 🔽
        tt,
        self = spec x y
      }}.
    Proof.
      unfold Adder.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      unfold spec.
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Adder.compute x y 🔽
        spec x y, True
      }}.
    Proof.
      unfold Adder.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := Adder.Build_t _).
        }
        intros _.
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          eapply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Adder.
End Module_Line_20.

Module Module_Line_52.
  Import Module_Line_52.

  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ global_add x y 🔽 ((x + y) mod p)%Z, True }}.
  Proof.
    unfold global_add.
    apply Run.Pure.
  Qed.

  Module Adder2.
    Definition spec {p} `{Prime p} (x y : Felt.t) : Adder2.t :=
      {|
        Adder2.sum :=
          let sum := BinOp.add x y in
          BinOp.add sum sum;
      |}.

    Lemma contrain_implies {p} `{Prime p}
        (self : Adder2.t)
        (x y : Felt.t) :
      let self := map_mod self in
      {{ Adder2.constrain self x y 🔽
        tt,
        self = spec x y
      }}.
    Proof.
      unfold Adder2.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      unfold spec.
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Adder2.compute x y 🔽
        {| Adder2.sum := BinOp.add x y |}, True
      }}.
    Proof.
      unfold Adder2.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := Adder2.Build_t _).
        }
        intros _.
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          eapply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Adder2.
End Module_Line_52.

Module Module_Line_85.
  Import Module_Line_85.

  Module ComponentB.
    Lemma constrain_implies {p} `{Prime p}
        (self : ComponentB.t)
        (x : Felt.t)
        (y : Array.t Felt.t [5]%nat) :
      let self := map_mod self in
      {{ ComponentB.constrain self x y 🔽
        tt,
        Array.IsIn.t x y
      }}.
    Proof.
      unfold ComponentB.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertIn.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) (y : Array.t Felt.t [5]%nat) :
      {{ ComponentB.compute x y 🔽
        ComponentB.Make, True
      }}.
    Proof.
      unfold ComponentB.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ComponentB.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ComponentB.
End Module_Line_85.

Module Module_Line_105.
  Import Module_Line_105.

  Module EnsureZero.
    Lemma constrain_implies {p} `{Prime p}
        (self : EnsureZero.t)
        (x : Felt.t) :
      let self := map_mod self in
      {{ EnsureZero.constrain self x 🔽
        tt,
        x = UnOp.from 0
      }}.
    Proof.
      unfold EnsureZero.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ EnsureZero.compute x 🔽
        EnsureZero.Make, True
      }}.
    Proof.
      unfold EnsureZero.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := EnsureZero.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End EnsureZero.

  Module EnsureBothZero.
    Lemma constrain_implies {p} `{Prime p}
        (self : EnsureBothZero.t)
        (x y : Felt.t) :
      let self := map_mod self in
      {{ EnsureBothZero.constrain self x y 🔽
        tt,
        x = y /\ x = UnOp.from 0
      }}.
    Proof.
      unfold EnsureBothZero.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ EnsureBothZero.compute x y 🔽
        EnsureBothZero.Make, True
      }}.
    Proof.
      unfold EnsureBothZero.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := EnsureBothZero.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End EnsureBothZero.
End Module_Line_105.

Module Module_Line_147.
  Import Module_Line_147.

  Module Passthrough.
    Lemma constrain_implies {p} `{Prime p}
        (self : Passthrough.t)
        (x : Felt.t) :
      let self := map_mod self in
      {{ Passthrough.constrain self x 🔽
        tt,
        self.(Passthrough.out) = x
      }}.
    Proof.
      unfold Passthrough.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ Passthrough.compute x 🔽
        {| Passthrough.out := x |}, True
      }}.
    Proof.
      unfold Passthrough.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| Passthrough.out := x |}).
        }
        intros _.
        eapply Run.Let. {
          apply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Passthrough.

  Module EnsureIsZero.
    Lemma constrain_implies {p} `{Prime p}
        (self : EnsureIsZero.t)
        (x : Felt.t) :
      let self := map_mod self in
      let x := x mod p in
      {{ EnsureIsZero.constrain self x 🔽
        tt,
        self.(EnsureIsZero.p).(Passthrough.out) = 0 mod p /\
        self.(EnsureIsZero.p).(Passthrough.out) = x
      }}.
    Proof.
      unfold EnsureIsZero.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Passthrough.constrain_implies.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      let x := x mod p in
      {{ EnsureIsZero.compute x 🔽
        {| EnsureIsZero.p := {| Passthrough.out := x |} |}, True
      }}.
    Proof.
      unfold EnsureIsZero.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| EnsureIsZero.p := _ |}).
        }
        intros _.
        eapply Run.Let. {
          apply Passthrough.compute_eq.
        }
        intros _.
        eapply Run.Let. {
          eapply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End EnsureIsZero.
End Module_Line_147.

Module Module_Line_196.
  Import Module_Line_196.

  Module ArrayCheck.
    Lemma constrain_implies {p} `{Prime p}
        (self : ArrayCheck.t)
        (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      let self := map_mod self in
      {{ ArrayCheck.constrain self x 🔽
        tt,
        d = UnOp.from 7
      }}.
    Proof.
      unfold ArrayCheck.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      cbn.
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      {{ ArrayCheck.compute x 🔽
        ArrayCheck.Make, True
      }}.
    Proof.
      unfold ArrayCheck.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ArrayCheck.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ArrayCheck.
End Module_Line_196.

Module Module_Line_219.
  Import Module_Line_219.

  Module ArrayForCheck.
    Lemma constrain_implies {p} `{Prime p}
        (self : ArrayForCheck.t)
        (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      let self := map_mod self in
      {{ ArrayForCheck.constrain self x 🔽
        tt,
        a = UnOp.from 7 /\
        b = UnOp.from 7 /\
        c = UnOp.from 7 /\
        d = UnOp.from 7 /\
        e = UnOp.from 7
      }}.
    Proof.
      unfold ArrayForCheck.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          rewrite M.for_step_one_eq.
          cbn.
          repeat (
            eapply Run.Let ||
            apply Run.AssertEqual ||
            apply Run.Pure ||
            intros _
          ).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      {{ ArrayForCheck.compute x 🔽
        ArrayForCheck.Make, True
      }}.
    Proof.
      unfold ArrayForCheck.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ArrayForCheck.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ArrayForCheck.
End Module_Line_219.

Module Module_Line_246.
  Import Module_Line_246.

  Module ConstConstraints.
    Lemma constrain_implies {p} `{Prime p}
        (self : ConstConstraints.t)
        (x y : Felt.t) :
      let self := map_mod self in
      let x := x mod p in
      let y := y mod p in
      {{ ConstConstraints.constrain self x y 🔽
        tt,
        x = UnOp.from 1 /\
        y = UnOp.from 1
      }}.
    Proof.
      unfold ConstConstraints.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ ConstConstraints.compute x y 🔽
        ConstConstraints.Make, True
      }}.
    Proof.
      unfold ConstConstraints.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ConstConstraints.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ConstConstraints.
End Module_Line_246.

Module Module_Line_270.
  Import Module_Line_270.

  Module ArrayConstrain.
    Lemma constrain_implies {p} `{Prime p} {A B : nat}
        (self : ArrayConstrain.t A B)
        (arr : Array.t Felt.t [3]%nat) :
      let self := map_mod self in
      {{ ArrayConstrain.constrain self arr 🔽
        tt,
        Array.read arr (0%nat, tt) = UnOp.from (Z.of_nat A) /\
        Array.read arr (2%nat, tt) = UnOp.from (Z.of_nat B)
      }}.
    Proof.
      unfold ArrayConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} {A B : nat} (arr : Array.t Felt.t [3]%nat) :
      {{ ArrayConstrain.compute (A := A) (B := B) arr 🔽
        ArrayConstrain.Make, True
      }}.
    Proof.
      unfold ArrayConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ArrayConstrain.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ArrayConstrain.

  Module MatrixConstrain.
    Lemma constrain_implies {p} `{Prime p}
        (self : MatrixConstrain.t)
        (arr : Array.t Felt.t [2; 3]%nat) :
      let self := map_mod self in
      {{ MatrixConstrain.constrain self arr 🔽
        tt,
        Array.read arr (0%nat, (0%nat, tt)) = UnOp.from 7 /\
        Array.read arr (0%nat, (2%nat, tt)) = UnOp.from 11 /\
        Array.read arr (1%nat, (0%nat, tt)) = UnOp.from 13 /\
        Array.read arr (1%nat, (2%nat, tt)) = UnOp.from 17
      }}.
    Proof.
      unfold MatrixConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply ArrayConstrain.constrain_implies.
        }
        intros _.
        eapply Run.Let. {
          apply ArrayConstrain.constrain_implies.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (arr : Array.t Felt.t [2; 3]%nat) :
      {{ MatrixConstrain.compute arr 🔽
        {|
          MatrixConstrain.check0 := ArrayConstrain.Make;
          MatrixConstrain.check1 := ArrayConstrain.Make;
        |},
        True
      }}.
    Proof.
      unfold MatrixConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {|
            MatrixConstrain.check0 := ArrayConstrain.Make;
            MatrixConstrain.check1 := ArrayConstrain.Make;
          |}).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End MatrixConstrain.
End Module_Line_270.

Module Module_Line_331.
  Import Module_Line_331.

  Module ArrayConstrain.
    Lemma constrain_implies {p} `{Prime p}
        (self : ArrayConstrain.t)
        (arr : Array.t Felt.t [3]%nat) :
      let self := map_mod self in
      {{ ArrayConstrain.constrain self arr 🔽
        tt,
        Array.read arr (1%nat, tt) = UnOp.from 7
      }}.
    Proof.
      unfold ArrayConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (arr : Array.t Felt.t [3]%nat) :
      {{ ArrayConstrain.compute arr 🔽
        ArrayConstrain.Make, True
      }}.
    Proof.
      unfold ArrayConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := ArrayConstrain.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ArrayConstrain.
End Module_Line_331.

Module Module_Line_392.
  Import Module_Line_392.

  Module UnknownArrayConstrain.
    Lemma constrain_implies {p} `{Prime p} {N : nat}
        (self : UnknownArrayConstrain.t N)
        (arr : Array.t Felt.t [N]%nat) :
      let self := map_mod self in
      {{ UnknownArrayConstrain.constrain self arr 🔽
        tt,
        Array.read arr (1%nat, tt) = UnOp.from 7
      }}.
    Proof.
      unfold UnknownArrayConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} {N : nat} (arr : Array.t Felt.t [N]%nat) :
      {{ UnknownArrayConstrain.compute (N := N) arr 🔽
        UnknownArrayConstrain.Make, True
      }}.
    Proof.
      unfold UnknownArrayConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := UnknownArrayConstrain.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End UnknownArrayConstrain.
End Module_Line_392.

Module Module_Line_415.
  Import Module_Line_415.

  Module UnknownArrayConstrain.
    Lemma constrain_implies {p} `{Prime p} {N : nat}
        (self : UnknownArrayConstrain.t N)
        (arr : Array.t Felt.t [N]%nat) :
      let self := map_mod self in
      {{ UnknownArrayConstrain.constrain self arr 🔽
        tt,
        Array.read arr (1%nat, tt) = UnOp.from 7
      }}.
    Proof.
      unfold UnknownArrayConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} {N : nat} (arr : Array.t Felt.t [N]%nat) :
      {{ UnknownArrayConstrain.compute arr 🔽
        UnknownArrayConstrain.Make, True
      }}.
    Proof.
      unfold UnknownArrayConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := UnknownArrayConstrain.Make).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End UnknownArrayConstrain.

  Module UnknownMatrixConstrain.
    Lemma constrain_implies {p} `{Prime p} {M N : nat}
        (self : UnknownMatrixConstrain.t M N)
        (arr : Array.t Felt.t [M; N]%nat) :
      let self := map_mod self in
      {{ UnknownMatrixConstrain.constrain self arr 🔽
        tt,
        Array.read (Array.extract (Ns := [_]) arr (0%nat, tt)) (1%nat, tt) = UnOp.from 7
      }}.
    Proof.
      unfold UnknownMatrixConstrain.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply UnknownArrayConstrain.constrain_implies.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} {M N : nat} (arr : Array.t Felt.t [M; N]%nat) :
      {{ UnknownMatrixConstrain.compute arr 🔽
        {| UnknownMatrixConstrain.check := UnknownArrayConstrain.Make |},
        True
      }}.
    Proof.
      unfold UnknownMatrixConstrain.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| UnknownMatrixConstrain.check := UnknownArrayConstrain.Make |}).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End UnknownMatrixConstrain.
End Module_Line_415.

Module Module_Line_642.
  Import Module_Line_642.

  Parameter extern_add_spec : Felt.t -> Felt.t -> Felt.t.

  Lemma extern_add_eq {p} `{Prime p} (x y : Felt.t) :
    let x := x mod p in
    let y := y mod p in
    {{ extern_add x y 🔽 extern_add_spec x y, True }}.
  Admitted.

  Module ExternAdder.
    Lemma constrain_implies {p} `{Prime p}
        (self : ExternAdder.t)
        (x y : Felt.t) :
      let self := map_mod self in
      let x := x mod p in
      let y := y mod p in
      {{ ExternAdder.constrain self x y 🔽
        tt,
        self.(ExternAdder.sum) = extern_add_spec x y
      }}.
    Proof.
      unfold ExternAdder.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply extern_add_eq.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y sum : Felt.t) :
      let x := x mod p in
      let y := y mod p in
      let sum := sum mod p in
      {{ ExternAdder.compute x y 🔽
        {| ExternAdder.sum := sum |},
        True
      }}.
    Proof.
      unfold ExternAdder.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| ExternAdder.sum := _ |}).
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End ExternAdder.
End Module_Line_642.

Module Module_Line_669.
  Import Module_Line_669.

  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ global_add x y 🔽 BinOp.add x y, True }}.
  Proof.
    unfold global_add.
    apply Run.Pure.
  Qed.

  Lemma irrelevant_eq {p} `{Prime p} :
    {{ irrelevant 🔽 tt, True }}.
  Admitted.

  Module Adder2.
    Lemma constrain_implies {p} `{Prime p}
        (self : Adder2.t)
        (x y : Felt.t) :
      let self := map_mod self in
      {{ Adder2.constrain self x y 🔽
        tt,
        self.(Adder2.sum) =
          let sum := BinOp.add x y in
          BinOp.add sum sum
      }}.
    Proof.
      unfold Adder2.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          apply irrelevant_eq.
        }
        intros _.
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Adder2.compute x y 🔽
        {| Adder2.sum := BinOp.add x y |},
        True
      }}.
    Proof.
      unfold Adder2.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| Adder2.sum := _ |}).
        }
        intros _.
        eapply Run.Let. {
          apply global_add_eq.
        }
        intros _.
        eapply Run.Let. {
          apply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Adder2.
End Module_Line_669.

Module Module_Line_707.
  Import Module_Line_707.

  Module Signal.
    Lemma constrain_implies {p} `{Prime p}
        (self : Signal.t)
        (x : Felt.t) :
      let self := map_mod self in
      {{ Signal.constrain self x 🔽
        tt,
        True
      }}.
    Proof.
      unfold Signal.constrain.
      apply Run.Pure.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ Signal.compute x 🔽
        {| Signal.reg := x |},
        True
      }}.
    Proof.
      unfold Signal.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| Signal.reg := _ |}).
        }
        intros _.
        eapply Run.Let. {
          apply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Signal.

  Module Component00.
    Lemma constrain_implies {p} `{Prime p}
        (self : Component00.t)
        (x : Signal.t) :
      let self := map_mod self in
      {{ Component00.constrain self x 🔽
        tt,
        self.(Component00.f) = x
      }}.
    Proof.
      unfold Component00.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Signal.t) :
      {{ Component00.compute x 🔽
        {| Component00.f := x |},
        True
      }}.
    Proof.
      unfold Component00.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| Component00.f := _ |}).
        }
        intros _.
        eapply Run.Let. {
          apply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Component00.

  Module Component01.
    Lemma constrain_implies {p} `{Prime p}
        (self : Component01.t)
        (x : Array.t Signal.t [2]%nat) :
      let self := map_mod self in
      {{ Component01.constrain self x 🔽
        tt,
        self.(Component01.f) = x
      }}.
    Proof.
      unfold Component01.constrain.
      eapply Run.Implies. {
        eapply Run.Let. {
          apply Run.AssertEqual.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Array.t Signal.t [2]%nat) :
      {{ Component01.compute x 🔽
        {| Component01.f := x |},
        True
      }}.
    Proof.
      unfold Component01.compute.
      eapply Run.Implies. {
        eapply Run.Let. {
          eapply Run.CreateStruct with (value := {| Component01.f := _ |}).
        }
        intros _.
        eapply Run.Let. {
          apply Run.FieldWrite.
        }
        intros _.
        apply Run.Pure.
      }
      easy.
    Qed.
  End Component01.
End Module_Line_707.
