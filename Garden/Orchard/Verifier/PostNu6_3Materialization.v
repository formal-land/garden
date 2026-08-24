(** * Checked materialization of Post-NU6.3 verifier expressions

    The runtime literals are generated from the deployed pinned VK JSON.  The
    right-hand sides below are independently derived from Garden's formal
    configure program and selector compressor.  VM conversion checks the full
    expression trees, including order, query registration indices, rotations,
    and field constants. *)

Require Import Garden.Orchard.Verifier.PostNu6_3Data.
Require Import Garden.Orchard.Verifier.PostNu6_3Derived.

Theorem post_nu6_3_lookup_descriptions_materialized :
  OrchardPostNu63Data.lookup_descriptions =
  OrchardPostNu63Derived.lookup_descriptions.
Proof. vm_compute. reflexivity. Qed.

Theorem post_nu6_3_gate_polynomials_materialized :
  OrchardPostNu63Data.gate_polynomials =
  OrchardPostNu63Derived.gate_polynomials.
Proof. vm_compute. reflexivity. Qed.
