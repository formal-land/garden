Require Import Garden.Garden.
Require Circom.Circomlib.translation.circuits.binsum.

Import Run.

Lemma run_nbits (p : Z) :
  {{ p , Scopes.empty ⏩ binsum.nbits 6 🔽 23 ⏩ Scopes.empty }}.
Proof.
  unfold binsum.nbits.
  unfold M.function_body; cbn.
  eapply Run.Let. {
    eapply Run.Let. {
      apply Run.PrimitiveDeclareVar.
      apply Run.Pure.
    }
    eapply Run.Let. {
      apply Run.PrimitiveSubstituteVar.
      apply Run.Pure.
    }
    eapply Run.Let. {
      apply Run.PrimitiveDeclareVar.
      apply Run.Pure.
    }
    eapply Run.Let. {
      apply Run.PrimitiveSubstituteVar.
      apply Run.Pure.
    }
    cbn.
    eapply Run.Let. {
      eapply Run.LoopNext. {
        eapply Run.Let. {
Admitted.
