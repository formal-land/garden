// Excerpt from pasta_curves src/curves.rs (crate version 0.5.1,
// git revision fe08536da133280ed2f7e63877d6049a1efc8922): the Pallas-relevant
// hash-to-curve pieces only.
//
// - impl_projective_curve_ext (special_a0_b5 arm): the hash_to_curve
//   pipeline (hash_to_field -> 2x map_to_curve_simple_swu -> add -> iso_map)
//   [lines 878-924 of the full file];
// - the new_curve_impl! invocations for Ep ("pallas", a = 0, b = 5) and
//   IsoEp ("iso-pallas", a, b = 1265) [lines 948-988];
// - impl Ep: ISOGENY_CONSTANTS (13 constants of the degree-3 isogeny),
//   Z = -13, and THETA = sqrt(Z / ROOT_OF_UNITY) [lines 1007-1105].
//
// For review and traceability only; not part of the Rocq build.

#[cfg(feature = "alloc")]
macro_rules! impl_projective_curve_ext {
    ($name:ident, $iso:ident, $base:ident, special_a0_b5) => {
        fn hash_to_curve<'a>(domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a> {
            use super::hashtocurve;

            Box::new(move |message| {
                let mut us = [Field::ZERO; 2];
                hashtocurve::hash_to_field($name::CURVE_ID, domain_prefix, message, &mut us);
                let q0 = hashtocurve::map_to_curve_simple_swu::<$base, $name, $iso>(
                    &us[0],
                    $name::THETA,
                    $name::Z,
                );
                let q1 = hashtocurve::map_to_curve_simple_swu::<$base, $name, $iso>(
                    &us[1],
                    $name::THETA,
                    $name::Z,
                );
                let r = q0 + &q1;
                debug_assert!(bool::from(r.is_on_curve()));
                hashtocurve::iso_map::<$base, $name, $iso>(&r, &$name::ISOGENY_CONSTANTS)
            })
        }

        /// Apply the curve endomorphism by multiplying the x-coordinate
        /// by an element of multiplicative order 3.
        fn endo(&self) -> Self {
            $name {
                x: self.x * $base::ZETA,
                y: self.y,
                z: self.z,
            }
        }
    };
    ($name:ident, $iso:ident, $base:ident, general) => {
        /// Unimplemented: hashing to this curve is not supported
        fn hash_to_curve<'a>(_domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a> {
            unimplemented!()
        }

        /// Unimplemented: no endomorphism is supported for this curve.
        fn endo(&self) -> Self {
            unimplemented!()
        }
    };
}

new_curve_impl!(
    (pub),
    Ep,
    EpAffine,
    IsoEp,
    Fp,
    Fq,
    "pallas",
    [0, 0, 0, 0],
    [5, 0, 0, 0],
    special_a0_b5
);
new_curve_impl!(
    (pub),
    Eq,
    EqAffine,
    IsoEq,
    Fq,
    Fp,
    "vesta",
    [0, 0, 0, 0],
    [5, 0, 0, 0],
    special_a0_b5
);
new_curve_impl!(
    (pub(crate)),
    IsoEp,
    IsoEpAffine,
    Ep,
    Fp,
    Fq,
    "iso-pallas",
    [
        0x92bb4b0b657a014b,
        0xb74134581a27a59f,
        0x49be2d7258370742,
        0x18354a2eb0ea8c9c,
    ],
    [1265, 0, 0, 0],
    general
);

impl Ep {
    /// Constants used for computing the isogeny from IsoEp to Ep.
    pub const ISOGENY_CONSTANTS: [Fp; 13] = [
        Fp::from_raw([
            0x775f6034aaaaaaab,
            0x4081775473d8375b,
            0xe38e38e38e38e38e,
            0x0e38e38e38e38e38,
        ]),
        Fp::from_raw([
            0x8cf863b02814fb76,
            0x0f93b82ee4b99495,
            0x267c7ffa51cf412a,
            0x3509afd51872d88e,
        ]),
        Fp::from_raw([
            0x0eb64faef37ea4f7,
            0x380af066cfeb6d69,
            0x98c7d7ac3d98fd13,
            0x17329b9ec5253753,
        ]),
        Fp::from_raw([
            0xeebec06955555580,
            0x8102eea8e7b06eb6,
            0xc71c71c71c71c71c,
            0x1c71c71c71c71c71,
        ]),
        Fp::from_raw([
            0xc47f2ab668bcd71f,
            0x9c434ac1c96b6980,
            0x5a607fcce0494a79,
            0x1d572e7ddc099cff,
        ]),
        Fp::from_raw([
            0x2aa3af1eae5b6604,
            0xb4abf9fb9a1fc81c,
            0x1d13bf2a7f22b105,
            0x325669becaecd5d1,
        ]),
        Fp::from_raw([
            0x5ad985b5e38e38e4,
            0x7642b01ad461bad2,
            0x4bda12f684bda12f,
            0x1a12f684bda12f68,
        ]),
        Fp::from_raw([
            0xc67c31d8140a7dbb,
            0x07c9dc17725cca4a,
            0x133e3ffd28e7a095,
            0x1a84d7ea8c396c47,
        ]),
        Fp::from_raw([
            0x02e2be87d225b234,
            0x1765e924f7459378,
            0x303216cce1db9ff1,
            0x3fb98ff0d2ddcadd,
        ]),
        Fp::from_raw([
            0x93e53ab371c71c4f,
            0x0ac03e8e134eb3e4,
            0x7b425ed097b425ed,
            0x025ed097b425ed09,
        ]),
        Fp::from_raw([
            0x5a28279b1d1b42ae,
            0x5941a3a4a97aa1b3,
            0x0790bfb3506defb6,
            0x0c02c5bcca0e6b7f,
        ]),
        Fp::from_raw([
            0x4d90ab820b12320a,
            0xd976bbfabbc5661d,
            0x573b3d7f7d681310,
            0x17033d3c60c68173,
        ]),
        Fp::from_raw([
            0x992d30ecfffffde5,
            0x224698fc094cf91b,
            0x0000000000000000,
            0x4000000000000000,
        ]),
    ];

    /// Z = -13
    pub const Z: Fp = Fp::from_raw([
        0x992d30ecfffffff4,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ]);

    /// `(F::ROOT_OF_UNITY.invert().unwrap() * z).sqrt().unwrap()`
    pub const THETA: Fp = Fp::from_raw([
        0xca330bcc09ac318e,
        0x51f64fc4dc888857,
        0x4647aef782d5cdc8,
        0x0f7bdb65814179b4,
    ]);
}
