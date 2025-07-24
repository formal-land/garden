Require Export Coq.ZArith.ZArith.

(** We will need later to make the field reasoning. For now we axiomatize it. *)
Parameter IsPrime : Z -> Prop.

Class Prime (p : Z) : Prop := {
  is_prime : IsPrime p;
}.

Module UnOp.
  Definition opp {p} `{Prime p} (x : Z) : Z :=
    (-x) mod p.
  
  Definition from {p} `{Prime p} (x : Z) : Z := 
    x mod p.
End UnOp.

Module BinOp.
  Definition add {p} `{Prime p} (x y : Z) : Z :=
    (x + y) mod p.

  Definition sub {p} `{Prime p} (x y : Z) : Z :=
    (x - y) mod p.

  Definition mul {p} `{Prime p} (x y : Z) : Z :=
    (x * y) mod p.

  Definition div {p} `{Prime p} (x y : Z) : Z :=
    (x / y) mod p.

  Definition mod_ {p} `{Prime p} (x y : Z) : Z :=
    (x mod y) mod p.
End BinOp.


Module Array.
  Record t {A : Set} {N : Z} : Set := {
    get : Z -> A;
  }.
  Arguments t : clear implicits.

  Definition slice_from {A : Set} {N : Z} (x : t A N) (start : Z) : t A (N - start) :=
    {|
      get index := x.(get) (start + index)
    |}.
  
  Definition slice_first {A : Set} {N : Z} (x : t A N) (count : Z) : t A count := 
    {|
      get := x.(get)
    |}.

  Definition get_mod {p} `{Prime p} {N : Z} (x : t Z N) (i : Z) : Z :=
    x.(get) i mod p.
  
  Definition placeholder {A : Set} {N : Z} (x : A) : t A N :=
    {|
      get index := x
    |}.
  
  Definition map {A B : Set} {N : Z} (x : t A N) (f : A -> B) : t B N := 
    {|
      get index := f (x.(get) index)
    |}.
End Array.