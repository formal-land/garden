(** * Simplified SWU onto iso-Vesta and the degree-3 isogeny to Vesta

    The curve-side half of the Vesta [hash_to_curve] (the pipeline behind
    Halo2's IPA SRS, [Params::new] in [halo2_proofs/src/poly/commitment.rs]):
    the iso-Vesta curve constants, the [map_to_curve_simple_swu] map from
    Vesta-base-field elements onto iso-Vesta in the inversion-avoiding
    [sqrt_ratio] formulation, and the degree-3 isogeny [iso_map] from
    iso-Vesta to Vesta.  Field arithmetic is over [pallas_q] (the Vesta base
    field of the pasta cycle); the module structure mirrors
    [Garden/GroupHash/sswu.v] (the Pallas instantiation, protocol §5.4.9.8).

    Reference implementation: the pinned pasta_curves sources (crate 0.5.1,
    revision fe08536da133280ed2f7e63877d6049a1efc8922) —
    [src/hashtocurve.rs] for [map_to_curve_simple_swu] / [iso_map] (shared
    with Pallas, only the constants differ), and [src/curves.rs] for the
    constants: the [new_curve_impl!] invocation for [IsoEq] ([a], [b]) and
    [impl Eq] ([ISOGENY_CONSTANTS], [Z], [THETA]); [λ] is
    [Fq::ROOT_OF_UNITY] ([src/fields/fq.rs]).  The [Fq::from_raw]
    little-endian [u64] limbs denote the integers below.  The Rust maps
    produce Jacobian coordinates; here the outputs are affine, with each
    denominator cleared by one egcd [mod_inverse] (through [BinOp.div]).

    Square roots are untrusted witnesses: [map_to_curve_simple_swu_with_root]
    takes the [sqrt_ratio] output — the is-square flag and the root — as
    parameters, and [sqrt_ratio_witness_ok] checks a claimed witness by one
    squaring and one multiplication.  [map_to_curve_simple_swu] is the
    self-contained wrapper that computes the root with [field_sqrt]
    (Tonelli–Shanks) for one-off use; because the final sign normalization
    forces [sgn0 y = sgn0 u], the map's output does not depend on which of
    the two roots a witness supplies.

    The two [map_to_curve_simple_swu] test vectors committed in the pinned
    checkout's [src/vesta.rs] ([test_map_to_curve_simple_swu], [u = 0] and
    [u = 1]) are proved at the end of the file, in witnessed form. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

(** [is_square] / [modpow] / [field_sqrt] appear in the statements and bodies
    below over the concrete Vesta base modulus; keep them out of the
    conversion oracle (see the [Strategy opaque] rule in the performance
    notes — lazy unfolding of a [2^253]-exponent [modpow] blows up
    exponentially). *)
Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module IsoVesta.
  (** ** The iso-Vesta curve [E_iso-V : y² = x³ + a·x + b] over [F_{pallas_q}]

      Constants from the [new_curve_impl!] invocation for [IsoEq] and
      [impl Eq] in the pinned [src/curves.rs]. *)

  (** [a_iso-V] =
      0x267f9b2ee592271a81639c4d96f787739673928c7d01b212c515ad7242eaa6b1. *)
  Definition a : Z :=
    17413348858408915339762682399132325137863850198379221683097628341577494210225.

  (** [b_iso-V] = 1265. *)
  Definition b : Z := 1265.

  (** [Z_iso-V] = −13 (mod [pallas_q]), the nonsquare of the simplified SWU
      map ([Eq::Z]). *)
  Definition z : Z := Primes.pallas_q - 13.

  (** [λ_V], the fixed nonsquare of [sqrt_ratio]: the reference
      implementation uses [Fq::ROOT_OF_UNITY], i.e. [5^((q − 1) / 2^32)]
      (0x2de6a9b8746d3f589e5c4dfd492ae26e9bb97ea3c106f049a70e2c1102b6d05f). *)
  Definition lambda : Z :=
    20761624379169977859705911634190121761503565370703356079647768903521299517535.

  (** [θ_iso-V] = √(Z_iso-V / λ_V) ([Eq::THETA],
      0x2b3483a1ee9a382f53c3808d9e2f235738578ccadf03ac27632cae9872df1b5d). *)
  Definition theta : Z :=
    19542237030899541288482047651115607340417301175065916331554475033324169403229.

  (** ** The 13 isogeny constants of the iso-Vesta → Vesta map

      ([Eq::ISOGENY_CONSTANTS] in the pinned [src/curves.rs]; 1-based
      indexing [𝒞₁ … 𝒞₁₃], [ISOGENY_CONSTANTS[i]] = [𝒞_{i+1}]). *)

  (** 0x38e38e38e38e38e38e38e38e38e38e390205dd51cfa0961a43cd42c800000001 *)
  Definition c1 : Z :=
    25731575386070265649682441113041757300767161317281464337493104665238544842753.
  (** 0x1d935247b4473d17acecf10f5f7c09a2216b8861ec72bd5d8b95c6aaf703bcc5 *)
  Definition c2 : Z :=
    13377367003779316331268047403600734872799183885837485433911493934102207511749.
  (** 0x18760c7f7a9ad20ded7ee4a9cdf78f8fd59d03d23b39cb11aeac67bbeb586a3d *)
  Definition c3 : Z :=
    11064082577423419940183149293632076317553812518550871517841037420579891210813.
  (** 0x31c71c71c71c71c71c71c71c71c71c71e1c521a795ac8356fb539a6f0000002b *)
  Definition c4 : Z :=
    22515128462811482443472135973911537638171266152621281295306466582083726737451.
  (** 0x0a2de485568125d51454798a5b5c56b2a3ad678129b604d3b7284f7eaf21a2e9 *)
  Definition c5 : Z :=
    4604213796697651557841441623718706001740429044770779386484474413346415813353.
  (** 0x14735171ee5427780c621de8b91c242a30cd6d53df49d235f169c187d2533465 *)
  Definition c6 : Z :=
    9250006497141849826017568406346290940322373181457057184910582871723433210981.
  (** 0x12f684bda12f684bda12f684bda12f685601f4709a8adcb36bef1642aaaaaaab *)
  Definition c7 : Z :=
    8577191795356755216560813704347252433589053772427154779164368221746181614251.
  (** 0x2ec9a923da239e8bd6767887afbe04d121d910aefb03b31d8bee58e5fb81de63 *)
  Definition c8 : Z :=
    21162694656554182593580396827886355918081120183889566406795618341247785229923.
  (** 0x19b0d87e16e2578866d1466e9de10e6497a3ca5c24e9ea634986913ab4443034 *)
  Definition c9 : Z :=
    11620280474556824258112134491145636201000922752744881519070727793732904824884.
  (** 0x1ed097b425ed097b425ed097b425ed098bc32d36fb21a6a38f64842c55555533 *)
  Definition c10 : Z :=
    13937936667454727226911322269564285204582212380194126516142098360337545123123.
  (** 0x2f44d6c801c1b8bf9e7eb64f890a820c06a767bfc35b5bac58dfecce86b2745e *)
  Definition c11 : Z :=
    21380331849711001764708535561664047484292171808126992769566582994216305194078.
  (** 0x3d59f455cafc7668252659ba2b546c7e926847fb9ddd76a1d43d449776f99d2f *)
  Definition c12 : Z :=
    27750019491425549478052705219038872820967119544371171554731748615170299632943.
  (** 0x40000000000000000000000000000000224698fc0994a8dd8c46eb20fffffde5
      (= [pallas_q] − 540) *)
  Definition c13 : Z :=
    28948022309329048855892746252171976963363056481941647379679742748393362947557.

  (** The constants in the reference implementation's array order
      ([ISOGENY_CONSTANTS[i]] = [𝒞_{i+1}]). *)
  Definition isogeny_constants : list Z :=
    [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13].

  (** ** Curve operations on iso-Vesta

      The generic [Weierstrass] point type and group operations at
      [a := a_iso-V], [p := pallas_q] ([Weierstrass.add] is generic in the
      coefficient [a], so the whole group-law cluster of
      [EllipticCurve/Weierstrass.v] applies verbatim). *)

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

  (** Nonsingularity [4 a³ + 27 b² ≠ 0 mod pallas_q] of iso-Vesta. *)
  Lemma nonsingular : Weierstrass.nonsingular (p := Primes.pallas_q) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.

  (** ** Transcription checks (finite Vesta-base-field computations)

      Each pins one constant against its defining relation in the reference
      implementation. *)

  (** [λ_V] is the reference implementation's [Fq::ROOT_OF_UNITY]
      = [5^((pallas_q − 1) / 2^32)] ([GENERATOR = 5], [S = 32]). *)
  Lemma lambda_provenance :
    modpow (p := Primes.pallas_q) 5 ((Primes.pallas_q - 1) / 2 ^ 32) = lambda.
  Proof. vm_compute. reflexivity. Qed.

  (** [λ_V] is a nonsquare (the requirement [sqrt_ratio] places on it). *)
  Lemma lambda_nonsquare : is_square (p := Primes.pallas_q) lambda = false.
  Proof. vm_compute. reflexivity. Qed.

  (** [Z_iso-V] is a nonsquare (with [lambda_nonsquare]: their ratio is then
      a square, so [θ_iso-V] exists). *)
  Lemma z_nonsquare : is_square (p := Primes.pallas_q) z = false.
  Proof. vm_compute. reflexivity. Qed.

  (** [θ_iso-V]² · λ_V = Z_iso-V: [theta] is a square root of [z / lambda]. *)
  Lemma theta_spec : theta *F theta *F lambda = UnOp.from z.
  Proof. vm_compute. reflexivity. Qed.
End IsoVesta.

Module SswuVesta.
  (** ** [map_to_curve_simple_swu] onto iso-Vesta, affine form

      The inversion-avoiding formulation of [src/hashtocurve.rs]: all
      intermediate values are numerators over the shared denominator [x_div]
      (nonzero because [a_iso-V ≠ 0] and both [−ta] and [Z_iso-V] are nonzero
      in their respective branches).  The structure is that of
      [Garden/GroupHash/sswu.v]'s [Sswu] module with the iso-Vesta constants
      over [pallas_q]. *)

  (** [Zuu] = [Z_iso-V · u²]. *)
  Definition z_u2 (u : Z) : Z := IsoVesta.z *F (u *F u).

  (** [ta] = [Zuu² + Zuu]. *)
  Definition ta (u : Z) : Z := z_u2 u *F z_u2 u +F z_u2 u.

  (** [x1num] = [b_iso-V · (ta + 1)]. *)
  Definition x1_num (u : Z) : Z := IsoVesta.b *F (ta u +F 1).

  (** [xdiv] = [a_iso-V · ((ta = 0) ? Z_iso-V : −ta)]. *)
  Definition x_div (u : Z) : Z :=
    if ta u =? 0
    then IsoVesta.a *F IsoVesta.z
    else IsoVesta.a *F (-F ta u).

  (** [xdiv³]. *)
  Definition x_div3 (u : Z) : Z := x_div u *F x_div u *F x_div u.

  (** [U] = [x1num³ + a_iso-V · x1num · xdiv² + b_iso-V · xdiv³], the
      numerator of [g(x1)] over the denominator [xdiv³]. *)
  Definition gx1_num (u : Z) : Z :=
    (x1_num u *F x1_num u +F IsoVesta.a *F (x_div u *F x_div u)) *F x1_num u
      +F IsoVesta.b *F x_div3 u.

  (** [x2num] = [Zuu · x1num]. *)
  Definition x2_num (u : Z) : Z := z_u2 u *F x1_num u.

  (** ** [sqrt_ratio] witnesses

      [sqrt_ratio(num, div)] returns [(√(num/div), 1)] when [num/div] is
      square and [(√(λ_V · num/div), 0)] otherwise.  A claimed output
      [(root, was_square)] is verified against the defining equation with one
      squaring and one multiplication — no in-kernel square-root computation:
      - [was_square = true]:  [root² · div = num];
      - [was_square = false]: [root² · div = λ_V · num].
      For [num ≠ 0] the two cases are mutually exclusive ([λ_V] is a
      nonsquare), so the equation also pins the flag. *)
  Definition sqrt_ratio_witness_ok
      (num div : Z) (was_square : bool) (root : Z) : bool :=
    if was_square
    then (root *F root *F div) =? UnOp.from num
    else (root *F root *F div) =? (IsoVesta.lambda *F num).

  (** The witness check specialized to the map's own [sqrt_ratio] call
      ([U] over [xdiv³]). *)
  Definition swu_witness_ok (u : Z) (was_square : bool) (root : Z) : bool :=
    sqrt_ratio_witness_ok (gx1_num u) (x_div3 u) was_square root.

  (** [sgn0] ([· mod 2] on the canonical representative). *)
  Definition sgn0 (x : Z) : bool := Z.odd (UnOp.from (p := Primes.pallas_q) x).

  (** The map with the [sqrt_ratio] output supplied as a witness
      ([was_square], [root]) — the checked form for certificate use; validity
      of the pair is [swu_witness_ok].  Output: the affine iso-Vesta point
      [(x_num / x_div, y)] with [sgn0 y = sgn0 u].  Given a valid witness the
      output does not depend on the sign of [root]: flipping [root] flips the
      candidate [y'] in both branches, and the normalization cancels it. *)
  Definition map_to_curve_simple_swu_with_root
      (u : Z) (was_square : bool) (root : Z) : IsoVesta.point :=
    let x_num := if was_square then x1_num u else x2_num u in
    (* [y2 = θ_iso-V · Zuu · u · y1]: a root of [g(x2)] via the theta trick. *)
    let y' := if was_square then root else IsoVesta.theta *F z_u2 u *F u *F root in
    let y :=
      if xorb (sgn0 u) (sgn0 y') then -F y' else UnOp.from y' in
    Weierstrass.Affine (BinOp.div x_num (x_div u)) y.

  (** Self-contained [sqrt_ratio] via [field_sqrt] (Tonelli–Shanks), for
      one-off evaluation; certificate leaves paste offline-computed roots
      and check them with [swu_witness_ok] instead. *)
  Definition sqrt_ratio (num div : Z) : bool * Z :=
    let r := BinOp.div num div in
    if is_square (p := Primes.pallas_q) r
    then (true, field_sqrt r)
    else (false, field_sqrt (IsoVesta.lambda *F r)).

  (** The self-contained map: [sqrt_ratio] computed in place. *)
  Definition map_to_curve_simple_swu (u : Z) : IsoVesta.point :=
    let '(was_square, root) := sqrt_ratio (gx1_num u) (x_div3 u) in
    map_to_curve_simple_swu_with_root u was_square root.

  (** ** [iso_map]: the degree-3 isogeny iso-Vesta → Vesta

      Affine form of the rational map,

        [x' = (𝒞₁·x³ + 𝒞₂·x² + 𝒞₃·x + 𝒞₄) / (x² + 𝒞₅·x + 𝒞₆)]
        [y' = (𝒞₇·x³ + 𝒞₈·x² + 𝒞₉·x + 𝒞₁₀)·y / (x³ + 𝒞₁₁·x² + 𝒞₁₂·x + 𝒞₁₃)],

      with one egcd [mod_inverse] per denominator; a vanishing denominator
      (the isogeny kernel, which maps to the identity) yields the point at
      infinity. *)
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
          ((x +F IsoVesta.c11) *F x +F IsoVesta.c12) *F x +F IsoVesta.c13 in
        if (x_den =? 0) || (y_den =? 0)
        then Weierstrass.Infinity
        else Weierstrass.Affine (BinOp.div x_num x_den) (BinOp.div y_num y_den)
    end.
End SswuVesta.

(** ** Reference vectors

    The two [test_map_to_curve_simple_swu] vectors committed in the pinned
    pasta_curves checkout's [src/vesta.rs], in witnessed form (the pasted
    root is validated by [swu_witness_ok], so no in-kernel [field_sqrt]
    runs); the expected affine points are the [x/z², y/z³] normalizations of
    the Jacobian coordinates the Rust test asserts.  The [u = 0] vector
    exercises the exceptional [ta = 0] branch of [x_div]. *)

Lemma swu_vesta_vector_zero_witness :
  SswuVesta.swu_witness_ok 0 true
    15378103202306912251825539162518451389917835720335280744133156865222402780188
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma swu_vesta_vector_zero :
  SswuVesta.map_to_curve_simple_swu_with_root 0 true
    15378103202306912251825539162518451389917835720335280744133156865222402780188
  = Weierstrass.Affine
      16814471377951997301238321206447124488237086731118311486509121688715150177986
      15378103202306912251825539162518451389917835720335280744133156865222402780188.
Proof. vm_compute. reflexivity. Qed.

Lemma swu_vesta_vector_one_witness :
  SswuVesta.swu_witness_ok 1 false
    21503435133343352163101110005376996892426684476434019279696305389597035434319
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma swu_vesta_vector_one :
  SswuVesta.map_to_curve_simple_swu_with_root 1 false
    21503435133343352163101110005376996892426684476434019279696305389597035434319
  = Weierstrass.Affine
      10817538808461803890412871477172625492511932941507219821148041993373366247167
      10058415206041905965582232583312905522192704307933664112640299309118936305655.
Proof. vm_compute. reflexivity. Qed.
