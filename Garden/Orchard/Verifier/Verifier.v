(** * Public Orchard verifier entry points *)

From Stdlib Require Import ZArith Lists.List.
Require Export Garden.Orchard.Verifier.PostNu6_3.
Require Export Garden.Orchard.Verifier.Assembly.

Module OrchardVerifier.

Definition verification_report := OrchardPostNu63.verification_report.

(** Structural decoder diagnostic.  It intentionally returns
    [BackendUnavailable] after consuming a valid full proof and must not be
    used as a verifier result. *)
Definition parse_post_nu6_3_report_Z :=
  OrchardPostNu63.verify_post_nu6_3_report_Z.

Definition verify_post_nu6_3_with_backend_Z :=
  OrchardPostNu63.verify_post_nu6_3_with_backend_Z.

(** User-facing Post-NU6.3 verification: one ten-scalar column per action.
    Trailing proof bytes are accepted, matching
    [orchard::circuit::Proof::verify].  Every PLONK query and the final IPA MSM
    are checked before this function can return [Verified]. *)
Definition verify_post_nu6_3_report_Z
    (proof : list Z) (actions : list (list Z)) :=
  OrchardPostNu63.verify_post_nu6_3_with_backend_Z
    (Garden.Orchard.Verifier.Assembly.backend actions) proof actions.

Definition verify_post_nu6_3_Z := verify_post_nu6_3_report_Z.

End OrchardVerifier.
