//! The Pallas curve `y^2 = x^3 + 5` natively: base field `F_p`, scalar field `F_q`,
//! points, the Zcash point encoding and `GroupHash^P` (hash-to-curve).
//!
//! Protocol specification (v2026.9.0) sections 5.4.9.6 (Pallas and Vesta), 5.4.9.7
//! (`Extract_P`) and 5.4.9.8 (group hash into Pallas: `hash_to_field` with
//! `expand_message_xmd` over BLAKE2b, simplified SWU on the isogenous curve iso-Pallas,
//! then the degree-3 isogeny). The constants are those of the `pasta_curves` crate
//! (0.6.3); every function here is checked against the Zcash test vectors
//! (`orchard_group_hash`, `orchard_map_to_curve`, `orchard_generators`).
//!
//! Field and point arithmetic is shared with the migration witness implementation.

use super::blake2::Blake2b;
pub use crate::pallas::{FpPallas as Fp, FqPallas as Fq, PallasPoint as Point};
use crate::pallas::{PALLAS_P, PALLAS_Q};

pub const BASE_MODULUS_LE: [u8; 32] = crate::limbs::to_le_bytes(PALLAS_P);
pub const SCALAR_MODULUS_LE: [u8; 32] = crate::limbs::to_le_bytes(PALLAS_Q);

// Hash to curve
// ============================================================================

const ISO_A: Fp = Fp::from_raw([
    0x92bb_4b0b_657a_014b,
    0xb741_3458_1a27_a59f,
    0x49be_2d72_5837_0742,
    0x1835_4a2e_b0ea_8c9c,
]);
const ISO_B: Fp = Fp::from_u64(1265);
/// `Z = -13`.
const SWU_Z: Fp = Fp::from_raw([
    0x992d_30ec_ffff_fff4,
    0x2246_98fc_094c_f91b,
    0,
    0x4000_0000_0000_0000,
]);

/// Coefficients of the isogeny (`pasta_curves` `Ep::ISOGENY_CONSTANTS`).
const ISOGENY: [[u64; 4]; 13] = [
    [
        0x775f6034aaaaaaab,
        0x4081775473d8375b,
        0xe38e38e38e38e38e,
        0x0e38e38e38e38e38,
    ],
    [
        0x8cf863b02814fb76,
        0x0f93b82ee4b99495,
        0x267c7ffa51cf412a,
        0x3509afd51872d88e,
    ],
    [
        0x0eb64faef37ea4f7,
        0x380af066cfeb6d69,
        0x98c7d7ac3d98fd13,
        0x17329b9ec5253753,
    ],
    [
        0xeebec06955555580,
        0x8102eea8e7b06eb6,
        0xc71c71c71c71c71c,
        0x1c71c71c71c71c71,
    ],
    [
        0xc47f2ab668bcd71f,
        0x9c434ac1c96b6980,
        0x5a607fcce0494a79,
        0x1d572e7ddc099cff,
    ],
    [
        0x2aa3af1eae5b6604,
        0xb4abf9fb9a1fc81c,
        0x1d13bf2a7f22b105,
        0x325669becaecd5d1,
    ],
    [
        0x5ad985b5e38e38e4,
        0x7642b01ad461bad2,
        0x4bda12f684bda12f,
        0x1a12f684bda12f68,
    ],
    [
        0xc67c31d8140a7dbb,
        0x07c9dc17725cca4a,
        0x133e3ffd28e7a095,
        0x1a84d7ea8c396c47,
    ],
    [
        0x02e2be87d225b234,
        0x1765e924f7459378,
        0x303216cce1db9ff1,
        0x3fb98ff0d2ddcadd,
    ],
    [
        0x93e53ab371c71c4f,
        0x0ac03e8e134eb3e4,
        0x7b425ed097b425ed,
        0x025ed097b425ed09,
    ],
    [
        0x5a28279b1d1b42ae,
        0x5941a3a4a97aa1b3,
        0x0790bfb3506defb6,
        0x0c02c5bcca0e6b7f,
    ],
    [
        0x4d90ab820b12320a,
        0xd976bbfabbc5661d,
        0x573b3d7f7d681310,
        0x17033d3c60c68173,
    ],
    [
        0x992d30ecfffffde5,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ],
];

/// `hash_to_field` of the `pasta_curves` crate: two field elements from
/// `expand_message_xmd` over BLAKE2b-512 with the domain separation tag
/// `domain_prefix || "-pallas_XMD:BLAKE2b_SSWU_RO_"`.
pub fn hash_to_field(domain_prefix: &str, message: &[u8]) -> [Fp; 2] {
    const CURVE_ID: &[u8] = b"pallas";
    const SUFFIX: &[u8] = b"_XMD:BLAKE2b_SSWU_RO_";
    let dst_len = [(22 + CURVE_ID.len() + domain_prefix.len()) as u8];
    assert!(22 + CURVE_ID.len() + domain_prefix.len() < 256);
    let dst = |st: &mut Blake2b| {
        st.update(domain_prefix.as_bytes())
            .update(b"-")
            .update(CURVE_ID)
            .update(SUFFIX)
            .update(&dst_len);
    };
    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&[0; 128]).update(message).update(&[0, 128, 0]);
    dst(&mut st);
    let b0 = st.finalize();

    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&b0).update(&[1]);
    dst(&mut st);
    let b1 = st.finalize();

    let mut mixed = [0u8; 64];
    for i in 0..64 {
        mixed[i] = b0[i] ^ b1[i];
    }
    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&mixed).update(&[2]);
    dst(&mut st);
    let b2 = st.finalize();

    [b1, b2].map(|mut big| {
        big.reverse();
        Fp::from_bytes_wide(&big)
    })
}

/// Simplified SWU map to an affine point of iso-Pallas.
fn map_to_iso(u: Fp) -> (Fp, Fp) {
    let g = |x: Fp| (x.square() + ISO_A) * x + ISO_B;
    let z_u2 = SWU_Z * u.square();
    let ta = z_u2.square() + z_u2;
    let num_x1 = ISO_B * (ta + Fp::ONE);
    let div = ISO_A * if ta.is_zero() { SWU_Z } else { -ta };
    let x1 = num_x1 * div.invert();
    let (x, y) = match g(x1).sqrt() {
        Some(y) => (x1, y),
        None => {
            let x2 = z_u2 * x1;
            (x2, g(x2).sqrt().expect("one of g(x1), g(x2) is a square"))
        }
    };
    (x, if y.is_odd() == u.is_odd() { y } else { -y })
}

/// Affine addition on iso-Pallas; `None` is the identity.
fn iso_add(p: (Fp, Fp), q: (Fp, Fp)) -> Option<(Fp, Fp)> {
    let lambda = if p.0 == q.0 {
        if p.1 != q.1 || p.1.is_zero() {
            return None;
        }
        (p.0.square() * Fp::from_u64(3) + ISO_A) * p.1.double().invert()
    } else {
        (q.1 - p.1) * (q.0 - p.0).invert()
    };
    let x = lambda.square() - p.0 - q.0;
    Some((x, lambda * (p.0 - x) - p.1))
}

/// The degree-3 isogeny from iso-Pallas to Pallas.
fn iso_map(p: Option<(Fp, Fp)>) -> Point {
    let Some((x, y)) = p else {
        return Point::IDENTITY;
    };
    let iso = ISOGENY.map(Fp::from_raw);
    let num_x = ((iso[0] * x + iso[1]) * x + iso[2]) * x + iso[3];
    let div_x = (x + iso[4]) * x + iso[5];
    let num_y = (((iso[6] * x + iso[7]) * x + iso[8]) * x + iso[9]) * y;
    let div_y = ((x + iso[10]) * x + iso[11]) * x + iso[12];
    if div_x.is_zero() || div_y.is_zero() {
        return Point::IDENTITY;
    }
    Point {
        x: num_x * div_x.invert(),
        y: num_y * div_y.invert(),
        z: Fp::ONE,
    }
}

/// `GroupHash^P(domain_prefix, message)` (protocol specification 5.4.9.8). Public inputs
/// only: not constant time.
pub fn hash_to_curve(domain_prefix: &str, message: &[u8]) -> Point {
    let [u0, u1] = hash_to_field(domain_prefix, message);
    iso_map(iso_add(map_to_iso(u0), map_to_iso(u1)))
}

#[cfg(test)]
mod tests {
    use super::super::vectors::hex32;
    use super::*;

    #[test]
    fn field_constants_are_consistent() {
        // Inversion and square roots.
        let a = Fp::from_u64(0xdead_beef_1234_5678);
        assert_eq!(a * a.invert(), Fp::ONE);
        assert_eq!(Fp::ZERO.invert(), Fp::ZERO);
        let r = (a * a).sqrt().unwrap();
        assert!(r == a || r == -a);
        assert!(
            Fp::from_u64(5).sqrt().is_none(),
            "5 is the non-residue behind the root"
        );
        let s = Fq::from_u64(77);
        assert_eq!(s.mul_mod(&s.invert()), Fq::ONE);
    }

    #[test]
    fn wide_reduction_matches_schoolbook() {
        // 2^256 * hi + lo with small parts, against direct field arithmetic.
        let mut bytes = [0u8; 64];
        bytes[0] = 7;
        bytes[32] = 3;
        let two256 = Fp::from_u64(1 << 32).square().square().square();
        assert_eq!(
            Fp::from_bytes_wide(&bytes),
            two256 * Fp::from_u64(3) + Fp::from_u64(7)
        );
        // All ones: (2^512 - 1) mod p.
        let all = Fp::from_bytes_wide(&[0xff; 64]);
        assert_eq!(all + Fp::ONE, two256.square());
        assert!(Fp::from_bytes(&[0xff; 32]).is_none());
        assert!(Fp::from_bytes(&BASE_MODULUS_LE).is_none());
        let mut pm1 = BASE_MODULUS_LE;
        pm1[0] -= 1;
        assert_eq!(Fp::from_bytes(&pm1).unwrap(), -Fp::ONE);
    }

    #[test]
    fn group_hash_vectors() {
        assert!(super::super::vectors::GROUP_HASH.len() >= 10);
        for (domain, msg, want) in super::super::vectors::GROUP_HASH {
            let p = hash_to_curve(domain, &super::super::vectors::unhex(msg));
            assert_eq!(p.to_bytes(), hex32(want), "domain {domain}");
            assert_eq!(Point::from_bytes(&hex32(want)).unwrap(), p);
        }
    }

    #[test]
    fn map_to_curve_vectors() {
        // The vectors give the simplified-SWU output on iso-Pallas, before the isogeny,
        // in the same compressed encoding.
        assert!(super::super::vectors::MAP_TO_CURVE.len() >= 10);
        for (u, want) in super::super::vectors::MAP_TO_CURVE {
            let (x, y) = map_to_iso(Fp::from_bytes(&hex32(u)).unwrap());
            assert_eq!(y.square(), (x.square() + ISO_A) * x + ISO_B);
            let mut enc = x.to_bytes();
            enc[31] |= (y.is_odd() as u8) << 7;
            assert_eq!(enc, hex32(want));
        }
    }

    #[test]
    fn point_arithmetic_laws() {
        let g = hash_to_curve("z.cash:Orchard", b"G");
        let two = g.double();
        assert_eq!(two, g.add(&g));
        assert_eq!(g.mul(&Fq::from_u64(2)), two);
        assert_eq!(g.mul(&Fq::from_u64(5)), two.double().add(&g));
        assert!(g.add(&g.neg()).is_identity());
        assert_eq!(g.add(&Point::IDENTITY), g);
        // The group order annihilates the generator.
        assert!(g.scalar_mul_limbs_ct(&PALLAS_Q).is_identity());
        assert_eq!(g.mul(&(-Fq::ONE)), g.neg());
        // Encoding round trip, sign bit and rejections.
        let enc = g.to_bytes();
        assert_eq!(Point::from_bytes(&enc).unwrap(), g);
        let mut flipped = enc;
        flipped[31] ^= 0x80;
        assert_eq!(Point::from_bytes(&flipped).unwrap(), g.neg());
        assert!(Point::from_bytes(&[0; 32]).unwrap().is_identity());
        assert!(Point::from_bytes_nonidentity(&[0; 32]).is_none());
        let mut sign_only = [0u8; 32];
        sign_only[31] = 0x80;
        assert!(Point::from_bytes(&sign_only).is_none());
        assert!(Point::from_bytes(&BASE_MODULUS_LE).is_none());
        // Batch conversion agrees with the single one, identity included.
        let last = g.mul(&Fq::from_u64(77));
        let pts = [g, Point::IDENTITY, two, last];
        let batch = Point::batch_to_affine(&pts);
        for (p, a) in pts.iter().zip(&batch) {
            assert_eq!(p.to_affine(), *a);
        }
    }
}
