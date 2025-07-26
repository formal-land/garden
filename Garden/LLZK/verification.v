Require Import LLZK.M.
Require Import LLZK.translated.

Module Module_Line_20.
  Lemma global_add_eq {p} `{Prime p} (x y : Felt.t) :
    {{ Module_Line_20.global_add x y 🔽 ((x + y) mod p)%Z }}.
  Proof.
    unfold Module_Line_20.global_add.
    apply RunCompute.Pure.
  Qed.

  Module Adder.
    Definition spec {p} `{Prime p} (x y : Felt.t) : Module_Line_20.Adder.t :=
      {|
        Module_Line_20.Adder.sum := (x + y) mod p;
      |}.

    Lemma contrain_implies {p} `{Prime p}
        (adder : Module_Line_20.Adder.t)
        (x y : Felt.t) :
      let adder := map_mod adder in
      {{ Module_Line_20.Adder.constrain adder x y 🔽
        tt,
        adder = spec x y
      }}.
    Proof.
      unfold Module_Line_20.Adder.constrain.
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
        eapply RunConstrain.Pure.
      }
      unfold spec.
      hauto lq: on.
    Qed.

    Lemma compute_eq {p} `{Prime p} (x y : Felt.t) :
      {{ Module_Line_20.Adder.compute x y 🔽
        spec x y
      }}.
    Proof.
      unfold Module_Line_20.Adder.compute.
      eapply RunCompute.Let. {
        eapply RunCompute.CreateStruct with (value := Module_Line_20.Adder.Build_t _).
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
