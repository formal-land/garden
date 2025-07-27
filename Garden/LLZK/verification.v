Require Import LLZK.M.
Require Import LLZK.translated.

Module Module_Line_3.
  Import Module_Line_3.

  Module NoConstraints.
    Lemma constrain_eq {p} `{Prime p} (self : NoConstraints.t) (x : Felt.t) :
      {{ NoConstraints.constrain self x 🔽 tt }}.
    Proof.
      apply RunCompute.Pure.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ NoConstraints.compute x 🔽 NoConstraints.Make }}.
    Proof.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := NoConstraints.Make).
      }
      apply RunCompute.Pure.
    Qed.
  End NoConstraints.
End Module_Line_3.

Module Module_Line_20.
  Import Module_Line_20.

  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ global_add x y 🔽 ((x + y) mod p)%Z }}.
  Proof.
    unfold global_add.
    apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.Compute.
          apply global_add_eq.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      unfold spec.
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Adder.compute x y 🔽
        spec x y
      }}.
    Proof.
      unfold Adder.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := Adder.Build_t _).
      }
      eapply RunCompute.Let. {
        apply global_add_eq.
      }
      eapply RunCompute.Let. {
        eapply RunCompute.FieldWrite.
      }
      apply RunCompute.Pure.
    Qed.
  End Adder.
End Module_Line_20.

Module Module_Line_52.
  Import Module_Line_52.

  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ global_add x y 🔽 ((x + y) mod p)%Z }}.
  Proof.
    unfold global_add.
    apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.Compute.
          apply global_add_eq.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      unfold spec.
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Adder2.compute x y 🔽
        {| Adder2.sum := BinOp.add x y |}
      }}.
    Proof.
      unfold Adder2.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := Adder2.Build_t _).
      }
      eapply RunCompute.Let. {
        apply global_add_eq.
      }
      eapply RunCompute.Let. {
        eapply RunCompute.FieldWrite.
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertIn.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) (y : Array.t Felt.t [5]%nat) :
      {{ ComponentB.compute x y 🔽
        ComponentB.Make
      }}.
    Proof.
      unfold ComponentB.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := ComponentB.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ EnsureZero.compute x 🔽
        EnsureZero.Make
      }}.
    Proof.
      unfold EnsureZero.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := EnsureZero.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ EnsureBothZero.compute x y 🔽
        EnsureBothZero.Make
      }}.
    Proof.
      unfold EnsureBothZero.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := EnsureBothZero.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      {{ Passthrough.compute x 🔽
        {| Passthrough.out := x |}
      }}.
    Proof.
      unfold Passthrough.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := {| Passthrough.out := x |}).
      }
      eapply RunCompute.Let. {
        apply RunCompute.FieldWrite.
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply Passthrough.constrain_implies.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x : Felt.t) :
      let x := x mod p in
      {{ EnsureIsZero.compute x 🔽
        {| EnsureIsZero.p := {| Passthrough.out := x |} |}
      }}.
    Proof.
      unfold EnsureIsZero.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := {| EnsureIsZero.p := _ |}).
      }
      eapply RunCompute.Let. {
        apply Passthrough.compute_eq.
      }
      eapply RunCompute.Let. {
        eapply RunCompute.FieldWrite.
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      cbn.
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      {{ ArrayCheck.compute x 🔽
        ArrayCheck.Make
      }}.
    Proof.
      unfold ArrayCheck.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := ArrayCheck.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          rewrite M.for_step_one_eq.
          cbn.
          repeat (
            eapply RunConstrain.Let ||
            apply RunConstrain.AssertEqual ||
            apply RunConstrain.Pure ||
            intros _
          ).
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (a b c d e : Felt.t) :
      let x := Array.new [a; b; c; d; e] in
      {{ ArrayForCheck.compute x 🔽
        ArrayForCheck.Make
      }}.
    Proof.
      unfold ArrayForCheck.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := ArrayForCheck.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ ConstConstraints.compute x y 🔽
        ConstConstraints.Make
      }}.
    Proof.
      unfold ConstConstraints.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := ConstConstraints.Make).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply RunConstrain.AssertEqual.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} {A B : nat} (arr : Array.t Felt.t [3]%nat) :
      {{ ArrayConstrain.compute arr 🔽
        ArrayConstrain.Make A B
      }}.
    Proof.
      unfold ArrayConstrain.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := ArrayConstrain.Make A B).
      }
      apply RunCompute.Pure.
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
      eapply RunConstrain.Implies. {
        eapply RunConstrain.Let. {
          apply ArrayConstrain.constrain_implies.
        }
        intros _.
        eapply RunConstrain.Let. {
          apply ArrayConstrain.constrain_implies.
        }
        intros _.
        apply RunConstrain.Pure.
      }
      easy.
    Qed.

    Lemma compute_eq {p} `{Prime p} (arr : Array.t Felt.t [2; 3]%nat) :
      {{ MatrixConstrain.compute arr 🔽
        {|
          MatrixConstrain.check0 := ArrayConstrain.Make 7 11;
          MatrixConstrain.check1 := ArrayConstrain.Make 13 17;
        |}
      }}.
    Proof.
      unfold MatrixConstrain.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := {| MatrixConstrain.check0 := _; MatrixConstrain.check1 := _ |}).
      }
      apply RunCompute.Pure.
    Qed.
  End MatrixConstrain.
End Module_Line_270.
