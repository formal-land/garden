Require Import Garden.Garden.
Require Circom.Circomlib.translation.circuits.binsum.

Import Run.

Lemma run_nbits :
  {{ 97 , Scopes.empty ⏩ binsum.nbits 6 🔽 3 ⏩ Scopes.empty }}.
Proof.
  run_deterministic.
Qed.
