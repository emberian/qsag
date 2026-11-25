//! Zcash uses 32-byte field encodings and a 255-bit witness layout.
//! Polynomial arithmetic, reductions, carries and comparisons use the common curve engine.

pub use crate::hem::curve::Lazy as Num;
use crate::hem::curve::{self, Element, Modulus};
use alloc::vec::Vec;
use qsag_agg::field::Goldilocks as F;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

pub const LIMBS: usize = 32;

/// A witness in `[0, 2^nbits)` as 8-bit limbs and their bits.
#[derive(Clone)]
pub struct Elem {
    /// Little-endian bits, each Boolean.
    pub bits: Vec<Lc>,
    /// Little-endian limbs; limb `i` holds bits `8i..8i + 8`.
    pub limbs: Vec<Lc>,
}

impl Elem {
    /// The value as an unreduced integer.
    pub fn num(&self) -> Num {
        Num::from_bounded_limbs(&self.limbs, self.bits.len())
    }

    /// An element over bits the caller has constrained Boolean.
    pub fn from_bits(bits: Vec<Lc>) -> Self {
        let limbs = Num::from_bits(&bits).limb_forms();
        Self { bits, limbs }
    }

    /// A public constant of `nbits` bits.
    pub fn constant(value_le: &[u8], nbits: usize) -> Self {
        let bits = (0..nbits)
            .map(|i| {
                Lc::constant(F::from_u64_reduced(
                    ((value_le[i / 8] >> (i % 8)) & 1) as u64,
                ))
            })
            .collect();
        Self::from_bits(bits)
    }

    /// The assigned value, little-endian.
    pub fn value(&self, cs: &ConstraintSystem) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, bit) in self.bits.iter().enumerate() {
            out[i / 8] |= ((cs.eval(bit).to_canonical_u64() & 1) as u8) << (i % 8);
        }
        out
    }
}

impl From<Element> for Elem {
    fn from(e: Element) -> Self {
        Self {
            bits: e.bits_le,
            limbs: e.bytes_le,
        }
    }
}

pub fn alloc_elem(cs: &mut ConstraintSystem, value: &[u8], bits: usize) -> Elem {
    curve::alloc_integer(cs, value, bits).into()
}

pub fn enforce_le_const(cs: &mut ConstraintSystem, bits: &[Lc], bound: &[u8]) {
    curve::enforce_bound(cs, bits, bound);
}

/// `a != b` as integers, for two limb vectors of the same length with limbs in `[0, 255]`.
/// Five rows for 32 limbs.
pub fn enforce_limbs_differ(cs: &mut ConstraintSystem, a: &[Lc], b: &[Lc]) {
    assert_eq!(a.len(), b.len());
    // Seven limbs pack into 56 bits: the packed difference is a nonzero field element
    // exactly when the chunks differ.
    let diffs: Vec<Lc> = a
        .chunks(7)
        .zip(b.chunks(7))
        .map(|(x, y)| {
            let parts: Vec<(F, &Lc)> = (0..x.len())
                .flat_map(|i| {
                    let w = F::from_u64_reduced(1 << (8 * i));
                    [(w, &x[i]), (F::ZERO - w, &y[i])]
                })
                .collect();
            Lc::combine(&parts)
        })
        .collect();
    // sum d_c u_c = 1 has a solution exactly when some d_c is nonzero. The prover inverts
    // the first nonzero difference.
    let mut found = 0u64;
    let mut acc = Lc::constant(F::ONE);
    let last = diffs.len() - 1;
    for (c, d) in diffs.iter().enumerate() {
        let dv = cs.eval(d);
        let nonzero = ((dv.to_canonical_u64() | dv.to_canonical_u64().wrapping_neg()) >> 63) & 1;
        let pick = nonzero & (found ^ 1);
        found |= nonzero;
        let u = cs.alloc(dv.inv_or_zero().const_mul(F::from_u64_reduced(pick)));
        if c == last {
            cs.enforce_mul(d.clone(), u.into(), acc.clone());
        } else {
            let m = cs.mul(d, &u.into());
            acc = acc.minus(&m.into());
        }
    }
}

pub struct Field(pub(super) Modulus);
impl Field {
    pub const BITS: usize = 255;

    pub fn new(p: &[u8; 32]) -> Self {
        Self(Modulus::zcash(p))
    }
    pub fn pallas_base() -> Self {
        Self::new(&super::pallas::BASE_MODULUS_LE)
    }
    pub fn pallas_scalar() -> Self {
        Self::new(&super::pallas::SCALAR_MODULUS_LE)
    }

    pub fn alloc(&self, cs: &mut ConstraintSystem, value: &[u8; 32]) -> Elem {
        alloc_elem(cs, value, Self::BITS)
    }

    pub fn value(&self, cs: &ConstraintSystem, x: &Num) -> [u8; 32] {
        self.0
            .value(cs, x)
            .try_into()
            .expect("32-byte Zcash modulus")
    }

    pub fn enforce_zero(&self, cs: &mut ConstraintSystem, x: &Num) {
        self.0.enforce_zero(cs, x);
    }

    pub fn enforce_equal(&self, cs: &mut ConstraintSystem, a: &Num, b: &Num) {
        self.0.enforce_equal(cs, a, b);
    }

    pub fn reduce(&self, cs: &mut ConstraintSystem, x: &Num) -> Elem {
        let mut e: Elem = self.0.reduce(cs, x).into();
        e.bits.resize(Self::BITS, Lc::zero());
        e
    }

    pub fn enforce_canonical(&self, cs: &mut ConstraintSystem, e: &Elem) {
        self.0.enforce_canonical_bits(cs, &e.bits);
    }

    pub fn reduce_canonical(&self, cs: &mut ConstraintSystem, x: &Num) -> Elem {
        let e = self.reduce(cs, x);
        self.enforce_canonical(cs, &e);
        e
    }
}

#[cfg(test)]
mod tests {
    use super::super::pallas::{BASE_MODULUS_LE, Fp, Fq};
    use super::*;

    fn sample(i: u64) -> Fp {
        // Dense pseudo-random elements.
        let mut x = Fp::from_u64(0x9e37_79b9_7f4a_7c15 ^ i);
        for _ in 0..6 {
            x = x.square() + Fp::from_u64(i + 3);
        }
        x
    }

    #[test]
    fn products_and_congruences_match_native() {
        let field = Field::pallas_base();
        let mut cs = ConstraintSystem::new();
        let (a, b, c) = (sample(1), sample(2), sample(3));
        let (ea, eb, ec) = (
            field.alloc(&mut cs, &a.to_bytes()),
            field.alloc(&mut cs, &b.to_bytes()),
            field.alloc(&mut cs, &c.to_bytes()),
        );
        let rows0 = cs.num_rows();
        let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
        assert_eq!(cs.num_rows() - rows0, 63);
        assert_eq!(field.value(&cs, &ab), (a * b).to_bytes());
        // (a b - c)(a + 3) + 7 b, a degree-3 expression with a negative part.
        let t = Num::mul(&mut cs, &ab.sub(&ec.num()), &ea.num().add(&Num::small(3)));
        let expr = t.add(&eb.num().scale(7));
        let want = (a * b - c) * (a + Fp::from_u64(3)) + b * Fp::from_u64(7);
        assert_eq!(field.value(&cs, &expr), want.to_bytes());
        let rows1 = cs.num_rows();
        let r = field.reduce_canonical(&mut cs, &expr);
        std::println!(
            "reduce of a degree-3 expression: {} rows",
            cs.num_rows() - rows1
        );
        assert_eq!(r.value(&cs), want.to_bytes());
        // Constant factors cost no rows.
        let rows2 = cs.num_rows();
        let k = Num::constant(&sample(9).to_bytes());
        let ka = Num::mul(&mut cs, &k, &ea.num());
        assert_eq!(cs.num_rows(), rows2);
        assert_eq!(field.value(&cs, &ka), (sample(9) * a).to_bytes());
        let rows3 = cs.num_rows();
        field.enforce_equal(&mut cs, &ka, &Num::constant(&(sample(9) * a).to_bytes()));
        std::println!(
            "congruence of a constant product: {} rows",
            cs.num_rows() - rows3
        );
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn a_false_congruence_is_unsatisfiable() {
        let field = Field::pallas_base();
        for delta in [1u64, 2, 1 << 40] {
            let mut cs = ConstraintSystem::new();
            let (a, b) = (sample(4), sample(5));
            let (ea, eb) = (
                field.alloc(&mut cs, &a.to_bytes()),
                field.alloc(&mut cs, &b.to_bytes()),
            );
            let wrong = field.alloc(&mut cs, &(a * b + Fp::from_u64(delta)).to_bytes());
            let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
            field.enforce_equal(&mut cs, &ab, &wrong.num());
            let (shape, z) = cs.finish();
            assert!(!shape.is_satisfied(&z), "delta {delta}");
        }
    }

    #[test]
    fn scalar_field_wide_reduction() {
        // ToScalar: a 512-bit little-endian integer reduced modulo q.
        let field = Field::pallas_scalar();
        let bytes: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11));
        let mut cs = ConstraintSystem::new();
        let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
        let rows0 = cs.num_rows();
        let r = field.reduce_canonical(&mut cs, &Num::from_bits(&bits));
        std::println!("wide reduction: {} rows", cs.num_rows() - rows0);
        assert_eq!(r.value(&cs), Fq::from_bytes_wide(&bytes).to_bytes());
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn jubjub_scalar_order_wide_reduction() {
        // ToScalar^Sapling: a 512-bit integer modulo the 252-bit order r_J.
        use super::super::sapling::{SCALAR_MODULUS_LE, to_scalar};
        let field = Field::new(&SCALAR_MODULUS_LE);
        let mut all_ones = [0xffu8; 64];
        all_ones[63] = 0x7f;
        let mut order = [0u8; 64];
        order[..32].copy_from_slice(&SCALAR_MODULUS_LE);
        for bytes in [
            core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11)),
            [0xff; 64],
            all_ones,
            order,
            [0u8; 64],
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
            let rows0 = cs.num_rows();
            let r = field.reduce_canonical(&mut cs, &Num::from_bits(&bits));
            std::println!("wide reduction modulo r_J: {} rows", cs.num_rows() - rows0);
            assert_eq!(r.value(&cs), to_scalar(&bytes));
            // A canonical residue of a 252-bit modulus has no bit above 251.
            assert!(r.value(&cs)[31] < 0x10);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    #[test]
    fn jubjub_scalar_order_false_congruence_is_unsatisfiable() {
        use super::super::sapling::{SCALAR_MODULUS_LE, to_scalar};
        let field = Field::new(&SCALAR_MODULUS_LE);
        let bytes: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(91).wrapping_add(3));
        let good = to_scalar(&bytes);
        // The residue plus one, plus 2^200, and the non-canonical representative
        // residue + r_J (congruent, so only the canonical check can reject it).
        let mut plus_one = good;
        plus_one[0] ^= 1;
        let mut plus_high = good;
        plus_high[25] ^= 1;
        let mut plus_order = [0u8; 32];
        let mut carry = 0u16;
        for i in 0..32 {
            let t = good[i] as u16 + SCALAR_MODULUS_LE[i] as u16 + carry;
            plus_order[i] = t as u8;
            carry = t >> 8;
        }
        assert_eq!(carry, 0);
        for (claim, canonical, ok) in [
            (good, true, true),
            (plus_one, false, false),
            (plus_high, false, false),
            (plus_order, false, true),
            (plus_order, true, false),
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
            let e = field.alloc(&mut cs, &claim);
            field.enforce_equal(&mut cs, &Num::from_bits(&bits), &e.num());
            if canonical {
                field.enforce_canonical(&mut cs, &e);
            }
            let (shape, z) = cs.finish();
            assert_eq!(
                shape.is_satisfied(&z),
                ok,
                "{claim:?} canonical={canonical}"
            );
        }
    }

    #[test]
    #[should_panic(expected = "modulus must be odd")]
    fn a_modulus_below_2_248_is_refused() {
        let mut p = [0u8; 32];
        p[0] = 1;
        p[30] = 0xff;
        let _ = Field::new(&p);
    }

    #[test]
    fn canonical_check_accepts_exactly_the_residues() {
        let field = Field::pallas_base();
        let mut pm1 = BASE_MODULUS_LE;
        pm1[0] -= 1;
        let mut p_plus = BASE_MODULUS_LE;
        p_plus[0] += 4;
        let mut high = [0u8; 32];
        high[31] = 0x7f;
        let mut mid = BASE_MODULUS_LE;
        mid[20] = 1; // p + 2^160
        for (value, ok) in [
            ([0u8; 32], true),
            (pm1, true),
            (sample(7).to_bytes(), true),
            (BASE_MODULUS_LE, false),
            (p_plus, false),
            (mid, false),
            (high, false),
        ] {
            let mut cs = ConstraintSystem::new();
            let e = field.alloc(&mut cs, &value);
            let rows0 = cs.num_rows();
            field.enforce_canonical(&mut cs, &e);
            assert!(cs.num_rows() - rows0 < 120);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok, "{value:?}");
        }
    }

    #[test]
    fn limb_inequality() {
        let field = Field::pallas_base();
        let a = sample(11).to_bytes();
        let mut near = a;
        near[17] ^= 0x10;
        for (b, ok) in [(sample(12).to_bytes(), true), (near, true), (a, false)] {
            let mut cs = ConstraintSystem::new();
            let ea = field.alloc(&mut cs, &a);
            let eb = field.alloc(&mut cs, &b);
            let rows0 = cs.num_rows();
            enforce_limbs_differ(&mut cs, &ea.limbs, &eb.limbs);
            assert_eq!(cs.num_rows() - rows0, 5);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn a_quotient_cannot_be_forged() {
        // Changing any single assigned variable of a reduction breaks a row.
        let field = Field::pallas_base();
        let mut cs = ConstraintSystem::new();
        let (a, b) = (sample(21), sample(22));
        let (ea, eb) = (
            field.alloc(&mut cs, &a.to_bytes()),
            field.alloc(&mut cs, &b.to_bytes()),
        );
        let first = 1 + 2 * 255; // after the variables of the two operands
        let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
        let _ = field.reduce(&mut cs, &ab);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        let last = z.len() - qsag_agg::zk_hem::relation::MASK_ROWS;
        for idx in (first..last).step_by(7) {
            let mut bad = z.clone();
            bad[idx] += F::ONE;
            assert!(!shape.is_satisfied(&bad), "variable {idx}");
        }
    }
}
