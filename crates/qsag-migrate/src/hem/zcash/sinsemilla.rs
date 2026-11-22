//! Sinsemilla (protocol specification 5.4.1.9 and 5.4.8.4) natively.
//!
//! `SinsemillaHashToPoint(D, M)` pads `M` with zero bits to a multiple of 10, starts from
//! `Q(D) = GroupHash^P("z.cash:SinsemillaQ", D)` and for each 10-bit chunk `m` computes
//! `Acc := (Acc ⸭ S(m)) ⸭ Acc` with `S(m) = GroupHash^P("z.cash:SinsemillaS", I2LEOSP_32(m))`.
//! `⸭` is the incomplete addition: it is undefined (`None` here, `⊥` in the specification)
//! when an operand is the identity or the operands are equal or opposite. The result is
//! checked against the `orchard_sinsemilla` test vectors.
//!
//! Each chunk selects its affine coordinates by scanning the full table. The incomplete
//! addition checks accumulate one validity bit across the whole message.

use alloc::sync::Arc;
use alloc::vec::Vec;

use super::pallas::{Fp, Fq, Point, hash_to_curve};

/// Bits per chunk.
pub const K: usize = 10;
/// Largest number of chunks in a message.
pub const C: usize = 253;

fn build_table() -> Vec<(Fp, Fp)> {
    (0..1u32 << K)
        .map(|j| {
            hash_to_curve("z.cash:SinsemillaS", &j.to_le_bytes())
                .to_affine()
                .expect("S(j) is not the identity")
        })
        .collect()
}

/// The 1024 points `S(j)` in affine coordinates. Cached with `std`; rebuilt otherwise.
#[cfg(feature = "std")]
pub fn s_table() -> Arc<Vec<(Fp, Fp)>> {
    static TABLE: std::sync::OnceLock<Arc<Vec<(Fp, Fp)>>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| Arc::new(build_table())).clone()
}

/// The 1024 points `S(j)` in affine coordinates. Cached with `std`; rebuilt otherwise.
#[cfg(not(feature = "std"))]
pub fn s_table() -> Arc<Vec<(Fp, Fp)>> {
    Arc::new(build_table())
}

/// A Sinsemilla hash domain.
#[derive(Clone, Debug)]
pub struct HashDomain {
    q: Point,
}

impl HashDomain {
    pub fn new(domain: &str) -> Self {
        Self {
            q: hash_to_curve("z.cash:SinsemillaQ", domain.as_bytes()),
        }
    }

    /// The starting point `Q(D)`.
    pub fn q(&self) -> Point {
        self.q
    }

    /// `SinsemillaHashToPoint`; `None` is `⊥`.
    pub fn hash_to_point(&self, bits: &[bool]) -> Option<Point> {
        assert!(bits.len() <= K * C, "Sinsemilla message too long");
        let table = s_table();
        let mut acc = self.q;
        let mut valid = true;
        for chunk in bits.chunks(K) {
            let index = chunk
                .iter()
                .enumerate()
                .fold(0usize, |v, (i, &b)| v | ((b as usize) << i));
            let mut sx = Fp::ZERO;
            let mut sy = Fp::ZERO;
            for (i, &(x, y)) in table.iter().enumerate() {
                let take = qsag_accel::ct::ct_eq_u64(i as u64, index as u64);
                sx = Fp::select(take, x, sx);
                sy = Fp::select(take, y, sy);
            }
            let s = Point::from_affine(sx, sy).expect("table point is on the curve");
            valid &= acc.incomplete_add_defined(&s);
            let t = acc.add(&s);
            valid &= t.incomplete_add_defined(&acc);
            acc = t.add(&acc);
        }
        valid.then_some(acc)
    }

    /// `SinsemillaHash`: the `x` coordinate of [`Self::hash_to_point`].
    pub fn hash(&self, bits: &[bool]) -> Option<Fp> {
        self.hash_to_point(bits).map(|p| p.extract())
    }
}

/// A Sinsemilla commitment domain: the hash domain `D || "-M"` and the randomness base
/// `R = GroupHash^P(D || "-r", "")`.
#[derive(Clone, Debug)]
pub struct CommitDomain {
    m: HashDomain,
    r: Point,
}

impl CommitDomain {
    pub fn new(domain: &str) -> Self {
        let mut m = alloc::string::String::from(domain);
        m.push_str("-M");
        let mut r = alloc::string::String::from(domain);
        r.push_str("-r");
        Self {
            m: HashDomain::new(&m),
            r: hash_to_curve(&r, b""),
        }
    }

    pub fn q(&self) -> Point {
        self.m.q
    }

    /// The randomness base `R`.
    pub fn r(&self) -> Point {
        self.r
    }

    /// `SinsemillaCommit_r(D, M)`; `None` is `⊥`. The last addition is the complete one.
    pub fn commit(&self, bits: &[bool], r: &Fq) -> Option<Point> {
        Some(self.m.hash_to_point(bits)?.add(&self.r.mul(r)))
    }

    /// `SinsemillaShortCommit`: `Extract_P` of the commitment.
    pub fn short_commit(&self, bits: &[bool], r: &Fq) -> Option<Fp> {
        self.commit(bits, r).map(|p| p.extract())
    }
}

/// The low `n` bits of little-endian `bytes`, least significant first.
pub fn le_bits(bytes: &[u8], n: usize) -> Vec<bool> {
    (0..n).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect()
}

#[cfg(test)]
mod tests {
    use super::super::vectors::{GENERATORS, SINSEMILLA, hex32};
    use super::*;

    #[test]
    fn sinsemilla_vectors() {
        assert_eq!(SINSEMILLA.len(), 11);
        for (domain, bits, point, hash) in SINSEMILLA {
            let bits: Vec<bool> = bits.bytes().map(|b| b == b'1').collect();
            let d = HashDomain::new(domain);
            let p = d
                .hash_to_point(&bits)
                .expect("vector is not an exceptional case");
            assert_eq!(p.to_bytes(), hex32(point), "{domain}");
            assert_eq!(d.hash(&bits).unwrap().to_bytes(), hex32(hash), "{domain}");
        }
    }

    #[test]
    fn generators_match_vectors() {
        // skb, nkb, vcvb, vcrb, cmb, cmq, ivkb, ivkq, mcq.
        let note = CommitDomain::new("z.cash:Orchard-NoteCommit");
        let ivk = CommitDomain::new("z.cash:Orchard-CommitIvk");
        let got = [
            hash_to_curve("z.cash:Orchard", b"G"),
            hash_to_curve("z.cash:Orchard", b"K"),
            hash_to_curve("z.cash:Orchard-cv", b"v"),
            hash_to_curve("z.cash:Orchard-cv", b"r"),
            note.r(),
            note.q(),
            ivk.r(),
            ivk.q(),
            HashDomain::new("z.cash:Orchard-MerkleCRH").q(),
        ];
        for (g, want) in got.iter().zip(GENERATORS) {
            assert_eq!(g.to_bytes(), hex32(want));
        }
    }

    #[test]
    fn exceptional_inputs_are_bottom() {
        // Starting from Q = S(0), the first chunk 0 adds S(0) to itself: undefined.
        let table = s_table();
        let (x, y) = table[0];
        let d = HashDomain {
            q: Point::from_affine(x, y).unwrap(),
        };
        assert!(d.hash_to_point(&[]).is_some());
        assert!(d.hash_to_point(&[false; K]).is_none());
        assert!(d.hash_to_point(&[true; K]).is_some());
        // Starting from -S(1), chunk 1 adds opposite points.
        let (x, y) = table[1];
        let d = HashDomain {
            q: Point::from_affine(x, y).unwrap().neg(),
        };
        let mut one = [false; K];
        one[0] = true;
        assert!(d.hash_to_point(&one).is_none());
    }
}
