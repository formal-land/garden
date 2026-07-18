Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.primitives.consts.

Module Word.
  (** We use a type synonym rather than a container, as this is simpler *)
  Definition t := Array.t Z WORD_SIZE.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := M.map_mod x;
  }.

  Global Instance IsGenerate : MGenerate.C t := _.

  Global Instance IsEqual : Equal.C t := {
    Equal.t x y := x =F y;
  }.

  Definition of_Z (z : Z) : t :=
    Array.of_list [
      z mod 256;
      (z / 256) mod 256;
      (z / 256 / 256) mod 256;
      (z / 256 / 256 / 256) mod 256
    ].

  (** We do not use field arithmetic there, as this function is only for specifications. *)
  Definition to_Z (self : t) : Z :=
    self.[0] + 256 * (self.[1] + 256 * (self.[2] + 256 * self.[3])).

  Lemma to_Z_of_Z (z : Z) (H_z : 0 <= z < 2 ^ 32) :
    to_Z (of_Z z) = z.
  Proof.
    unfold of_Z, to_Z.
    cbv - [Z.add Z.mul Z.div Z.modulo].
    lia.
  Qed.
End Word.
