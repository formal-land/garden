(** * Simplified SWU onto iso-Pallas and the degree-3 isogeny to Pallas

    The curve-side half of [GroupHash^P] (protocol §5.4.9.8, "Group Hash into
    Pallas and Vesta"): the iso-Pallas curve constants, the
    [map_to_curve_simple_swu] map from base-field elements onto iso-Pallas in
    the inversion-avoiding [sqrt_ratio] formulation of [WB2019, §4.2], and the
    degree-3 isogeny [iso_map] from iso-Pallas to Pallas.

    Reference implementation: the vendored pasta_curves sources (crate 0.5.1,
    revision fe08536da133280ed2f7e63877d6049a1efc8922) —
    [Garden/GroupHash/hashtocurve.rs] for
    [map_to_curve_simple_swu] / [iso_map], and
    [Garden/GroupHash/curves_pallas_excerpt.rs] for the constants
    ([ISOGENY_CONSTANTS], [Z], [THETA], and the iso-Pallas [a]/[b]).  The Rust
    maps produce Jacobian coordinates [(x_num·x_div : y·x_div³ : x_div)]; here
    the outputs are affine, matching the protocol's own statement
    [(x_num/x_div, y)], with each denominator cleared by one egcd
    [mod_inverse] (through [BinOp.div]).

    Square roots are untrusted witnesses: [map_to_curve_simple_swu_with_root]
    takes the [sqrt_ratio] output — the is-square flag and the root — as
    parameters, and [sqrt_ratio_witness_ok] checks a claimed witness by one
    squaring and one multiplication.  [map_to_curve_simple_swu] is the
    self-contained wrapper that computes the root with [field_sqrt]
    (Tonelli–Shanks) for one-off use; because the final sign normalization
    forces [sgn0 y = sgn0 u], the map's output does not depend on which of
    the two roots a witness supplies. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

(** [is_square] / [modpow] / [field_sqrt] appear in the statements and bodies
    below over the concrete Pallas modulus; keep them out of the conversion
    oracle (see the [Strategy opaque] rule in the performance notes — lazy
    unfolding of a [2^253]-exponent [modpow] blows up exponentially). *)
Strategy opaque [is_square modpow modpow_pos field_sqrt].

Module IsoPallas.
  (** ** The iso-Pallas curve [E_iso-P : y² = x³ + a·x + b] over [F_{q_P}]

      Constants from protocol §5.4.9.8, cross-checked against the
      [new_curve_impl!] invocation for [IsoEp] and [impl Ep] in
      [curves_pallas_excerpt.rs] (the [Fp::from_raw] little-endian [u64]
      limbs denote the same integers as the spec's big-endian hex). *)

  (** [a_iso-P] =
      0x18354a2eb0ea8c9c49be2d7258370742b74134581a27a59f92bb4b0b657a014b. *)
  Definition a : Z :=
    10949663248450308183708987909873589833737836120165333298109615750520499732811.

  (** [b_iso-P] = 1265. *)
  Definition b : Z := 1265.

  (** [Z_iso-P] = −13 (mod [q_P]), the nonsquare of the simplified SWU map. *)
  Definition z : Z := Primes.pallas_p - 13.

  (** [λ_P], the fixed nonsquare of [sqrt_ratio] (§5.4.9.8 leaves its choice
      free; the reference implementation uses [Fp::ROOT_OF_UNITY], i.e.
      [5^((q_P − 1) / 2^32)], and [θ_iso-P] below is tied to this choice). *)
  Definition lambda : Z :=
    19814229590243028906643993866117402072516588566294623396325693409366934201135.

  (** [θ_iso-P] = √(Z_iso-P / λ_P) ([THETA] in [curves_pallas_excerpt.rs],
      0x0f7bdb65814179b44647aef782d5cdc851f64fc4dc888857ca330bcc09ac318e). *)
  Definition theta : Z :=
    7003529136733518259227950775588032800807760729532353866644138209790443401614.

  (** ** The 13 isogeny constants [𝒞^P] of §5.4.9.8

      ([ISOGENY_CONSTANTS] in [curves_pallas_excerpt.rs]; the spec's
      1-based indexing [𝒞₁ … 𝒞₁₃] is used.) *)

  (** 0x0e38e38e38e38e38e38e38e38e38e38e4081775473d8375b775f6034aaaaaaab *)
  Definition c1 : Z :=
    6432893846517566412420610278260439325191790329320346825767705947633326140075.
  (** 0x3509afd51872d88e267c7ffa51cf412a0f93b82ee4b994958cf863b02814fb76 *)
  Definition c2 : Z :=
    23989696149150192365340222745168215001509815558210986772351135915822265203574.
  (** 0x17329b9ec525375398c7d7ac3d98fd13380af066cfeb6d690eb64faef37ea4f7 *)
  Definition c3 : Z :=
    10492611921771203378452795982353351666191589197598957448093274638589204800759.
  (** 0x1c71c71c71c71c71c71c71c71c71c71c8102eea8e7b06eb6eebec06955555580 *)
  Definition c4 : Z :=
    12865787693035132824841220556520878650383580658640693651535411895266652280192.
  (** 0x1d572e7ddc099cff5a607fcce0494a799c434ac1c96b6980c47f2ab668bcd71f *)
  Definition c5 : Z :=
    13271109177048389296812780941310096270046944650307955939477485891950613419807.
  (** 0x325669becaecd5d11d13bf2a7f22b105b4abf9fb9a1fc81c2aa3af1eae5b6604 *)
  Definition c6 : Z :=
    22768321103861051515190775253992702316905399997697804654926324362758820947460.
  (** 0x1a12f684bda12f684bda12f684bda12f7642b01ad461bad25ad985b5e38e38e4 *)
  Definition c7 : Z :=
    11793638718615538422771118843477472096184948937087302513907460903994431256804.
  (** 0x1a84d7ea8c396c47133e3ffd28e7a09507c9dc17725cca4ac67c31d8140a7dbb *)
  Definition c8 : Z :=
    11994848074575096182670111372584107500754907779105493386175567957911132601787.
  (** 0x3fb98ff0d2ddcadd303216cce1db9ff11765e924f745937802e2be87d225b234 *)
  Definition c9 : Z :=
    28823569610051396102362669851238297121581474897215657071023781420043761726004.
  (** 0x025ed097b425ed097b425ed097b425ed0ac03e8e134eb3e493e53ab371c71c4f *)
  Definition c10 : Z :=
    1072148974419594402070101713043406554198631721553391137627950991272221023311.
  (** 0x0c02c5bcca0e6b7f0790bfb3506defb65941a3a4a97aa1b35a28279b1d1b42ae *)
  Definition c11 : Z :=
    5432652610908059517272798285879155923388888734491153551238890455750936314542.
  (** 0x17033d3c60c68173573b3d7f7d681310d976bbfabbc5661d4d90ab820b12320a *)
  Definition c12 : Z :=
    10408918692925056833786833257634153023990087029210292532869619559576527581706.
  (** 0x40000000000000000000000000000000224698fc094cf91b992d30ecfffffde5
      (= [q_P] − 540) *)
  Definition c13 : Z :=
    28948022309329048855892746252171976963363056481941560715954676764349967629797.

  (** The constants in the reference implementation's array order
      ([ISOGENY_CONSTANTS[i]] = [𝒞_{i+1}]). *)
  Definition isogeny_constants : list Z :=
    [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13].

  (** ** Curve operations on iso-Pallas

      The generic [Weierstrass] point type and group operations at
      [a := a_iso-P], [p := pallas_p] ([Weierstrass.add] is generic in the
      coefficient [a], so the whole group-law cluster of
      [EllipticCurve/Weierstrass.v] applies verbatim). *)

  Definition point : Set := Weierstrass.point.
  Definition identity : point := Weierstrass.Infinity.

  Definition on_curve (P : point) : Prop :=
    Weierstrass.on_curve (p := Primes.pallas_p) a b P.
  Definition reduced (P : point) : Prop :=
    Weierstrass.reduced (p := Primes.pallas_p) P.
  Definition neg (P : point) : point :=
    Weierstrass.neg (p := Primes.pallas_p) P.
  Definition add (P Q : point) : point :=
    Weierstrass.add (p := Primes.pallas_p) a P Q.
  Definition mul (k : Z) (P : point) : point :=
    Weierstrass.mul (p := Primes.pallas_p) a k P.

  (** Nonsingularity [4 a³ + 27 b² ≠ 0 mod q_P] of iso-Pallas. *)
  Lemma nonsingular : Weierstrass.nonsingular (p := Primes.pallas_p) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.

  (** ** Transcription checks (finite Pallas-field computations)

      Each pins one constant against its defining relation in §5.4.9.8. *)

  (** [λ_P] is the reference implementation's [ROOT_OF_UNITY]
      = [5^((q_P − 1) / 2^32)]. *)
  Lemma lambda_provenance :
    modpow (p := Primes.pallas_p) 5 ((Primes.pallas_p - 1) / 2 ^ 32) = lambda.
  Proof. vm_compute. reflexivity. Qed.

  (** [λ_P] is a nonsquare (the requirement §5.4.9.8 places on it). *)
  Lemma lambda_nonsquare : is_square (p := Primes.pallas_p) lambda = false.
  Proof. vm_compute. reflexivity. Qed.

  (** [Z_iso-P] is a nonsquare (with [lambda_nonsquare], footnote 12 of the
      spec: their ratio is then a square, so [θ_iso-P] exists). *)
  Lemma z_nonsquare : is_square (p := Primes.pallas_p) z = false.
  Proof. vm_compute. reflexivity. Qed.

  (** [θ_iso-P]² · λ_P = Z_iso-P: [theta] is a square root of [z / lambda]. *)
  Lemma theta_spec : theta *F theta *F lambda = UnOp.from z.
  Proof. vm_compute. reflexivity. Qed.
End IsoPallas.

Module Sswu.
  (** ** [map_to_curve_simple_swu^iso-P] (§5.4.9.8), affine form

      The inversion-avoiding formulation: all intermediate values are
      numerators over the shared denominator [x_div] (nonzero because
      [a_iso-P ≠ 0] and both [−ta] and [Z_iso-P] are nonzero in their
      respective branches).  Variable names follow the spec's pseudocode
      ([Zuu], [ta], [x1num], [xdiv], [U], [x2num]). *)

  (** [Zuu] = [Z_iso-P · u²]. *)
  Definition z_u2 (u : Z) : Z := IsoPallas.z *F (u *F u).

  (** [ta] = [Zuu² + Zuu]. *)
  Definition ta (u : Z) : Z := z_u2 u *F z_u2 u +F z_u2 u.

  (** [x1num] = [b_iso-P · (ta + 1)]. *)
  Definition x1_num (u : Z) : Z := IsoPallas.b *F (ta u +F 1).

  (** [xdiv] = [a_iso-P · ((ta = 0) ? Z_iso-P : −ta)]. *)
  Definition x_div (u : Z) : Z :=
    if ta u =? 0
    then IsoPallas.a *F IsoPallas.z
    else IsoPallas.a *F (-F ta u).

  (** [xdiv³]. *)
  Definition x_div3 (u : Z) : Z := x_div u *F x_div u *F x_div u.

  (** [U] = [x1num³ + a_iso-P · x1num · xdiv² + b_iso-P · xdiv³], the numerator
      of [g(x1)] over the denominator [xdiv³]. *)
  Definition gx1_num (u : Z) : Z :=
    (x1_num u *F x1_num u +F IsoPallas.a *F (x_div u *F x_div u)) *F x1_num u
      +F IsoPallas.b *F x_div3 u.

  (** [x2num] = [Zuu · x1num]. *)
  Definition x2_num (u : Z) : Z := z_u2 u *F x1_num u.

  (** ** [sqrt_ratio] witnesses

      [sqrt_ratio(num, div)] returns [(√(num/div), 1)] when [num/div] is
      square and [(√(λ_P · num/div), 0)] otherwise.  A claimed output
      [(root, was_square)] is verified against the defining equation with one
      squaring and one multiplication — no in-kernel square-root computation:
      - [was_square = true]:  [root² · div = num];
      - [was_square = false]: [root² · div = λ_P · num].
      For [num ≠ 0] the two cases are mutually exclusive ([λ_P] is a
      nonsquare), so the equation also pins the flag. *)
  Definition sqrt_ratio_witness_ok
      (num div : Z) (was_square : bool) (root : Z) : bool :=
    if was_square
    then (root *F root *F div) =? UnOp.from num
    else (root *F root *F div) =? (IsoPallas.lambda *F num).

  (** The witness check specialized to the map's own [sqrt_ratio] call
      ([U] over [xdiv³]). *)
  Definition swu_witness_ok (u : Z) (was_square : bool) (root : Z) : bool :=
    sqrt_ratio_witness_ok (gx1_num u) (x_div3 u) was_square root.

  (** [sgn0] (§5.4.9.8 uses [· mod 2] on the canonical representative). *)
  Definition sgn0 (x : Z) : bool := Z.odd (UnOp.from (p := Primes.pallas_p) x).

  (** The map with the [sqrt_ratio] output supplied as a witness
      ([was_square], [root]) — the checked form for certificate use; validity
      of the pair is [swu_witness_ok].  Output: the affine iso-Pallas point
      [(x_num / x_div, y)] with [sgn0 y = sgn0 u].  Given a valid witness the
      output does not depend on the sign of [root]: flipping [root] flips the
      candidate [y'] in both branches, and the normalization cancels it. *)
  Definition map_to_curve_simple_swu_with_root
      (u : Z) (was_square : bool) (root : Z) : IsoPallas.point :=
    let x_num := if was_square then x1_num u else x2_num u in
    (* [y2 = θ_iso-P · Zuu · u · y1]: a root of [g(x2)] via the theta trick. *)
    let y' := if was_square then root else IsoPallas.theta *F z_u2 u *F u *F root in
    let y :=
      if xorb (sgn0 u) (sgn0 y') then -F y' else UnOp.from y' in
    Weierstrass.Affine (BinOp.div x_num (x_div u)) y.

  (** Self-contained [sqrt_ratio] via [field_sqrt] (Tonelli–Shanks), for
      one-off evaluation; certificate leaves paste offline-computed roots
      and check them with [swu_witness_ok] instead. *)
  Definition sqrt_ratio (num div : Z) : bool * Z :=
    let r := BinOp.div num div in
    if is_square (p := Primes.pallas_p) r
    then (true, field_sqrt r)
    else (false, field_sqrt (IsoPallas.lambda *F r)).

  (** The self-contained map: [sqrt_ratio] computed in place. *)
  Definition map_to_curve_simple_swu (u : Z) : IsoPallas.point :=
    let '(was_square, root) := sqrt_ratio (gx1_num u) (x_div3 u) in
    map_to_curve_simple_swu_with_root u was_square root.

  (** ** [iso_map^P] (§5.4.9.8): the degree-3 isogeny iso-Pallas → Pallas

      Affine form of the rational map,

        [x' = (𝒞₁·x³ + 𝒞₂·x² + 𝒞₃·x + 𝒞₄) / (x² + 𝒞₅·x + 𝒞₆)]
        [y' = (𝒞₇·x³ + 𝒞₈·x² + 𝒞₉·x + 𝒞₁₀)·y / (x³ + 𝒞₁₁·x² + 𝒞₁₂·x + 𝒞₁₃)],

      with one egcd [mod_inverse] per denominator; a vanishing denominator
      (the isogeny kernel, which maps to [𝒪_P]) yields the point at
      infinity. *)
  Definition iso_map (P : IsoPallas.point) : Pallas.point :=
    match P with
    | Weierstrass.Infinity => Weierstrass.Infinity
    | Weierstrass.Affine x y =>
        let x_num :=
          ((IsoPallas.c1 *F x +F IsoPallas.c2) *F x +F IsoPallas.c3) *F x
            +F IsoPallas.c4 in
        let x_den := (x +F IsoPallas.c5) *F x +F IsoPallas.c6 in
        let y_num :=
          (((IsoPallas.c7 *F x +F IsoPallas.c8) *F x +F IsoPallas.c9) *F x
             +F IsoPallas.c10) *F y in
        let y_den :=
          ((x +F IsoPallas.c11) *F x +F IsoPallas.c12) *F x +F IsoPallas.c13 in
        if (x_den =? 0) || (y_den =? 0)
        then Weierstrass.Infinity
        else Weierstrass.Affine (BinOp.div x_num x_den) (BinOp.div y_num y_den)
    end.
End Sswu.
