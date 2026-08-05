(** * Simplified SWU onto iso-Vesta and the degree-3 isogeny to Vesta

    This is the Vesta-field counterpart of [Garden.GroupHash.sswu].  The
    constants are the canonical integers represented by the little-endian
    limbs in [pasta_curves::Eq]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module IsoVesta.
  (** The iso-Vesta curve [y^2 = x^3 + a*x + 1265]. *)
  Definition a : Z :=
    17413348858408915339762682399132325137863850198379221683097628341577494210225.
  Definition b : Z := 1265.

  Definition z : Z := Primes.pallas_q - 13.

  (** [Fq::ROOT_OF_UNITY] in [pasta_curves]. *)
  Definition lambda : Z :=
    20761624379169977859705911634190121761503565370703356079647768903521299517535.

  Definition theta : Z :=
    19542237030899541288482047651115607340417301175065916331554475033324169403229.

  Definition c1 : Z :=
    25731575386070265649682441113041757300767161317281464337493104665238544842753.
  Definition c2 : Z :=
    13377367003779316331268047403600734872799183885837485433911493934102207511749.
  Definition c3 : Z :=
    11064082577423419940183149293632076317553812518550871517841037420579891210813.
  Definition c4 : Z :=
    22515128462811482443472135973911537638171266152621281295306466582083726737451.
  Definition c5 : Z :=
    4604213796697651557841441623718706001740429044770779386484474413346415813353.
  Definition c6 : Z :=
    9250006497141849826017568406346290940322373181457057184910582871723433210981.
  Definition c7 : Z :=
    8577191795356755216560813704347252433589053772427154779164368221746181614251.
  Definition c8 : Z :=
    21162694656554182593580396827886355918081120183889566406795618341247785229923.
  Definition c9 : Z :=
    11620280474556824258112134491145636201000922752744881519070727793732904824884.
  Definition c10 : Z :=
    13937936667454727226911322269564285204582212380194126516142098360337545123123.
  Definition c11 : Z :=
    21380331849711001764708535561664047484292171808126992769566582994216305194078.
  Definition c12 : Z :=
    27750019491425549478052705219038872820967119544371171554731748615170299632943.
  Definition c13 : Z :=
    28948022309329048855892746252171976963363056481941647379679742748393362947557.

  Definition isogeny_constants : list Z :=
    [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13].

  Definition point : Set := Weierstrass.point.
  Definition identity : point := Weierstrass.Infinity.
  Definition on_curve (P : point) : Prop :=
    Weierstrass.on_curve (p := Primes.pallas_q) a b P.
  Definition reduced (P : point) : Prop :=
    Weierstrass.reduced (p := Primes.pallas_q) P.
  Definition neg (P : point) : point :=
    Weierstrass.neg (p := Primes.pallas_q) P.
  Definition add (P Q : point) : point :=
    Weierstrass.add (p := Primes.pallas_q) a P Q.
  Definition mul (k : Z) (P : point) : point :=
    Weierstrass.mul (p := Primes.pallas_q) a k P.

  Lemma nonsingular :
    Weierstrass.nonsingular (p := Primes.pallas_q) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.

  Lemma lambda_provenance :
    modpow (p := Primes.pallas_q) 5
      ((Primes.pallas_q - 1) / 2 ^ 32) = lambda.
  Proof. vm_compute. reflexivity. Qed.

  Lemma lambda_nonsquare :
    is_square (p := Primes.pallas_q) lambda = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma z_nonsquare : is_square (p := Primes.pallas_q) z = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma theta_spec : theta *F theta *F lambda = UnOp.from z.
  Proof. vm_compute. reflexivity. Qed.
End IsoVesta.

Module SswuVesta.
  Definition z_u2 (u : Z) : Z := IsoVesta.z *F (u *F u).

  Definition ta (u : Z) : Z := z_u2 u *F z_u2 u +F z_u2 u.

  Definition x1_num (u : Z) : Z := IsoVesta.b *F (ta u +F 1).

  Definition x_div (u : Z) : Z :=
    if ta u =? 0
    then IsoVesta.a *F IsoVesta.z
    else IsoVesta.a *F (-F ta u).

  Definition x_div3 (u : Z) : Z := x_div u *F x_div u *F x_div u.

  Definition gx1_num (u : Z) : Z :=
    (x1_num u *F x1_num u +F
       IsoVesta.a *F (x_div u *F x_div u)) *F x1_num u
      +F IsoVesta.b *F x_div3 u.

  Definition x2_num (u : Z) : Z := z_u2 u *F x1_num u.

  Definition sqrt_ratio_witness_ok
      (num div : Z) (was_square : bool) (root : Z) : bool :=
    if was_square
    then (root *F root *F div) =? UnOp.from num
    else (root *F root *F div) =? (IsoVesta.lambda *F num).

  Definition swu_witness_ok (u : Z) (was_square : bool) (root : Z) : bool :=
    sqrt_ratio_witness_ok (gx1_num u) (x_div3 u) was_square root.

  Definition sgn0 (x : Z) : bool :=
    Z.odd (UnOp.from (p := Primes.pallas_q) x).

  Definition map_to_curve_simple_swu_with_root
      (u : Z) (was_square : bool) (root : Z) : IsoVesta.point :=
    let x_num := if was_square then x1_num u else x2_num u in
    let y' :=
      if was_square then root
      else IsoVesta.theta *F z_u2 u *F u *F root in
    let y := if xorb (sgn0 u) (sgn0 y') then -F y' else UnOp.from y' in
    Weierstrass.Affine (BinOp.div x_num (x_div u)) y.

  Definition sqrt_ratio (num div : Z) : bool * Z :=
    let r := BinOp.div num div in
    if is_square (p := Primes.pallas_q) r
    then (true, field_sqrt r)
    else (false, field_sqrt (IsoVesta.lambda *F r)).

  Definition map_to_curve_simple_swu (u : Z) : IsoVesta.point :=
    let '(was_square, root) := sqrt_ratio (gx1_num u) (x_div3 u) in
    map_to_curve_simple_swu_with_root u was_square root.

  Definition iso_map (P : IsoVesta.point) : Vesta.point :=
    match P with
    | Weierstrass.Infinity => Weierstrass.Infinity
    | Weierstrass.Affine x y =>
        let x_num :=
          ((IsoVesta.c1 *F x +F IsoVesta.c2) *F x +F IsoVesta.c3) *F x
            +F IsoVesta.c4 in
        let x_den := (x +F IsoVesta.c5) *F x +F IsoVesta.c6 in
        let y_num :=
          (((IsoVesta.c7 *F x +F IsoVesta.c8) *F x +F IsoVesta.c9) *F x
             +F IsoVesta.c10) *F y in
        let y_den :=
          ((x +F IsoVesta.c11) *F x +F IsoVesta.c12) *F x
            +F IsoVesta.c13 in
        if (x_den =? 0) || (y_den =? 0)
        then Weierstrass.Infinity
        else Weierstrass.Affine
               (BinOp.div x_num x_den) (BinOp.div y_num y_den)
    end.
End SswuVesta.

(** Affine forms of the two iso-Vesta SSWU vectors in
    [pasta_curves::vesta::test_map_to_curve_simple_swu].  The Rust fixture is
    printed in Jacobian coordinates; these literals are the corresponding
    [(X/Z^2, Y/Z^3)] values. *)
Lemma sswu_vesta_zero_reference_vector :
  SswuVesta.map_to_curve_simple_swu 0 =
    Weierstrass.Affine
      16814471377951997301238321206447124488237086731118311486509121688715150177986
      15378103202306912251825539162518451389917835720335280744133156865222402780188.
Proof. vm_compute. reflexivity. Qed.

Lemma sswu_vesta_one_reference_vector :
  SswuVesta.map_to_curve_simple_swu 1 =
    Weierstrass.Affine
      10817538808461803890412871477172625492511932941507219821148041993373366247167
      10058415206041905965582232583312905522192704307933664112640299309118936305655.
Proof. vm_compute. reflexivity. Qed.
