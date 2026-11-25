//! Pallas in the constraint system: table lookups, point addition and doubling, fixed-
//! and variable-base scalar multiplication, Sinsemilla and Poseidon, all over the
//! non-native arithmetic of [`super::nonnative`].
//!
//! # Exceptional cases
//!
//! Points are affine, so the identity has no representation. The addition used here is
//! the incomplete chord formula. Whenever its operands could have equal `x` for some
//! satisfying assignment, the gadget adds [`enforce_limbs_differ`] on the canonical `x`
//! limbs, which makes that assignment unsatisfiable; it never leaves the slope free. The
//! places are listed at each gadget. For Sinsemilla this is the specified behaviour
//! (`SinsemillaHashToPoint` returns `⊥` there, protocol specification 5.4.1.9, and ZIP 2005
//! requires that a quantum adversary cannot use those cases). For the other gadgets it
//! removes witnesses whose scalars hit an exceptional case, which an honest random key or
//! note does with probability about `2^-250`; it cannot add any.
//!
//! # Lookups
//!
//! A table of public points is addressed by up to ten Boolean bits. The low eight bits are
//! expanded into their 256 monomials (247 rows); every byte of the selected point is then
//! a linear form in those monomials for each value of the high bits, and three rows per
//! byte combine the four forms. No table entry is addressed by a witness value: the
//! assignment follows from evaluating the forms.

use alloc::sync::Arc;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

use super::nonnative::{Elem, Field, LIMBS, Num, enforce_limbs_differ};
use super::pallas::{Fp, Fq, Point, hash_to_curve};
use super::poseidon;

type F = Goldilocks;

use crate::hem::curve::f_int;

fn const_value(lc: &Lc) -> Option<F> {
    match lc.terms() {
        [] => Some(F::ZERO),
        [(0, c)] => Some(*c),
        _ => None,
    }
}

/// Product of two linear forms; no row when either is a constant.
fn mul_fold(cs: &mut ConstraintSystem, a: &Lc, b: &Lc) -> Lc {
    if let Some(c) = const_value(a) {
        b.scaled(c)
    } else if let Some(c) = const_value(b) {
        a.scaled(c)
    } else {
        cs.mul(a, b).into()
    }
}

/// The canonical value of an unreduced integer as a native field element.
fn fp_value(cs: &ConstraintSystem, f: &Field, x: &Num) -> Fp {
    Fp::from_bytes(&f.value(cs, x)).expect("canonical residue")
}

// ============================================================================
// Lookups
// ============================================================================

/// All `2^n` products of subsets of `bits`, indexed by subset mask.
pub(super) fn monomials(cs: &mut ConstraintSystem, bits: &[Lc]) -> Vec<Lc> {
    let mut out = Vec::with_capacity(1 << bits.len());
    out.push(Lc::constant(F::ONE));
    for mask in 1usize..1 << bits.len() {
        let low = mask.trailing_zeros() as usize;
        let rest = mask & (mask - 1);
        let m = if rest == 0 {
            bits[low].clone()
        } else {
            mul_fold(cs, &out[rest], &bits[low])
        };
        out.push(m);
    }
    out
}

/// The multilinear coefficients of a table of public byte strings (the coordinates of
/// points), byte by byte.
pub struct PointTable {
    nbits: usize,
    /// `coef[limb][mask]` for the bytes of an entry (`x || y` for a Pallas point).
    coef: Vec<Vec<i32>>,
}

impl PointTable {
    /// A table of `2^nbits` affine points, `nbits <= 10`.
    pub fn new(points: &[(Fp, Fp)], nbits: usize) -> Self {
        let bytes: Vec<[u8; 64]> = points
            .iter()
            .map(|(x, y)| {
                let mut b = [0u8; 64];
                b[..32].copy_from_slice(&x.to_bytes());
                b[32..].copy_from_slice(&y.to_bytes());
                b
            })
            .collect();
        Self::from_bytes(&bytes, nbits)
    }

    /// A table of `2^nbits` entries of `N` bytes each, `nbits <= 10`: the coordinates of
    /// a point of any curve, with whatever else is looked up beside them.
    pub fn from_bytes<const N: usize>(bytes: &[[u8; N]], nbits: usize) -> Self {
        assert!(nbits <= 10 && bytes.len() == 1 << nbits);
        let coef = (0..N)
            .map(|limb| {
                let mut c: Vec<i32> = bytes.iter().map(|b| b[limb] as i32).collect();
                for i in 0..nbits {
                    for u in 0..c.len() {
                        if u & (1 << i) != 0 {
                            c[u] -= c[u ^ (1 << i)];
                        }
                    }
                }
                c
            })
            .collect();
        Self { nbits, coef }
    }

    /// The limbs `(x, y)` of the point addressed by `bits` (Boolean, little-endian). Each
    /// limb is one variable holding exactly the table byte.
    pub fn lookup(&self, cs: &mut ConstraintSystem, bits: &[Lc]) -> (Vec<Lc>, Vec<Lc>) {
        assert_eq!(self.coef.len(), 2 * LIMBS);
        let mut limbs = self.lookup_bytes(cs, bits);
        let y = limbs.split_off(LIMBS);
        (limbs, y)
    }

    /// The bytes of the entry addressed by `bits` (Boolean, little-endian), each one
    /// variable holding exactly the table byte.
    pub fn lookup_bytes(&self, cs: &mut ConstraintSystem, bits: &[Lc]) -> Vec<Lc> {
        assert_eq!(bits.len(), self.nbits);
        let low_bits = self.nbits.min(8);
        let low = monomials(cs, &bits[..low_bits]);
        let high = monomials(cs, &bits[low_bits..]);
        let mut limbs = Vec::with_capacity(self.coef.len());
        for coef in &self.coef {
            let forms: Vec<Lc> = (0..high.len())
                .map(|h| {
                    let parts: Vec<(F, &Lc)> = low
                        .iter()
                        .enumerate()
                        .filter(|&(s, _)| coef[(h << low_bits) | s] != 0)
                        .map(|(s, m)| (f_int(coef[(h << low_bits) | s] as i128), m))
                        .collect();
                    Lc::combine(&parts)
                })
                .collect();
            // out = forms[0] + sum_{h > 0} high[h] * forms[h]; the last product closes the
            // equation that defines the output variable.
            let value = forms.iter().zip(&high).fold(F::ZERO, |acc, (f, h)| {
                acc + cs.eval(f).const_mul(cs.eval(h))
            });
            let out: Lc = cs.alloc(value).into();
            let mut rest = out.minus(&forms[0]);
            for h in 1..high.len() {
                if h + 1 == high.len() {
                    cs.enforce_mul(high[h].clone(), forms[h].clone(), rest.clone());
                } else {
                    let p = mul_fold(cs, &high[h], &forms[h]);
                    rest = rest.minus(&p);
                }
            }
            if high.len() == 1 {
                cs.enforce_zero(rest);
            }
            limbs.push(out);
        }
        limbs
    }
}

/// Select among `2^n` witness limb vectors by `n` Boolean bits: `2^n - 1` rows per limb.
pub(super) fn select_limbs(cs: &mut ConstraintSystem, monos: &[Lc], options: &[&[Lc]]) -> Vec<Lc> {
    assert_eq!(monos.len(), options.len());
    let n = options.len();
    let width = options[0].len();
    (0..width)
        .map(|l| {
            // Multilinear coefficients of the column `options[.][l]`.
            let mut c: Vec<Lc> = options.iter().map(|o| o[l].clone()).collect();
            let mut i = 1;
            while i < n {
                for u in 0..n {
                    if u & i != 0 {
                        c[u] = c[u].minus(&c[u ^ i]);
                    }
                }
                i <<= 1;
            }
            let value = c.iter().zip(monos).fold(F::ZERO, |acc, (f, m)| {
                acc + cs.eval(f).const_mul(cs.eval(m))
            });
            let out: Lc = cs.alloc(value).into();
            let mut rest = out.minus(&c[0]);
            for u in 1..n {
                if u + 1 == n {
                    cs.enforce_mul(monos[u].clone(), c[u].clone(), rest.clone());
                } else {
                    let p = mul_fold(cs, &monos[u], &c[u]);
                    rest = rest.minus(&p);
                }
            }
            out
        })
        .collect()
}

// ============================================================================
// Points
// ============================================================================

/// How many unreduced products `y` may accumulate before it is reduced.
const MAX_LAZY: u32 = 6;

/// An affine point: `x` as 32 limbs in `[0, 255]`, `y` unreduced.
#[derive(Clone)]
pub struct Pt {
    pub x: Vec<Lc>,
    /// The bits of `x`, when it is a bit-decomposed witness.
    pub x_bits: Option<Vec<Lc>>,
    /// Whether `x` is known to be below `p`.
    pub x_canonical: bool,
    pub y: Num,
    lazy: u32,
}

impl Pt {
    /// A public point.
    pub fn constant(x: Fp, y: Fp) -> Self {
        let e = Elem::constant(&x.to_bytes(), Field::BITS);
        Self {
            x: e.limbs,
            x_bits: Some(e.bits),
            x_canonical: true,
            y: Num::constant(&y.to_bytes()),
            lazy: 0,
        }
    }

    /// A point from limbs that hold exact table bytes.
    pub fn from_table(x: Vec<Lc>, y: Vec<Lc>) -> Self {
        Self {
            x,
            x_bits: None,
            x_canonical: true,
            y: Num::from_limbs(&y),
            lazy: 0,
        }
    }

    /// A point from two bit-decomposed coordinates. The caller states whether `x` has been
    /// constrained canonical and is responsible for the curve equation.
    pub fn from_elems(x: &Elem, x_canonical: bool, y: &Elem) -> Self {
        Self {
            x: x.limbs.clone(),
            x_bits: Some(x.bits.clone()),
            x_canonical,
            y: y.num(),
            lazy: 0,
        }
    }

    pub fn x_num(&self) -> Num {
        Num::from_limbs(&self.x)
    }

    fn values(&self, cs: &ConstraintSystem, f: &Field) -> (Fp, Fp) {
        (fp_value(cs, f, &self.x_num()), fp_value(cs, f, &self.y))
    }

    /// Reduce `y` to a bit-decomposed element.
    pub fn settle(&mut self, cs: &mut ConstraintSystem, f: &Field) -> Elem {
        let y = f.reduce(cs, &self.y);
        self.y = y.num();
        self.lazy = 0;
        y
    }

    fn relax(&mut self, cs: &mut ConstraintSystem, f: &Field) {
        if self.lazy >= MAX_LAZY {
            self.settle(cs, f);
        }
    }

    /// `x` as a canonical bit-decomposed element and `y` likewise: the inputs of
    /// `repr_P` and `Extract_P`.
    pub fn canonical_coordinates(&mut self, cs: &mut ConstraintSystem, f: &Field) -> (Elem, Elem) {
        let x = Elem {
            bits: self.x_bits.clone().expect("x is a witness"),
            limbs: self.x.clone(),
        };
        if !self.x_canonical {
            f.enforce_canonical(cs, &x);
            self.x_canonical = true;
        }
        let y = self.settle(cs, f);
        f.enforce_canonical(cs, &y);
        (x, y)
    }
}

/// `repr_P` of a point with canonical coordinates: the 255 bits of `x`, then the parity
/// of `y`.
pub fn point_repr(x: &Elem, y: &Elem) -> Vec<Lc> {
    let mut bits = x.bits.clone();
    bits.push(y.bits[0].clone());
    bits
}

/// `y^2 = x^3 + 5`.
pub fn enforce_on_curve(cs: &mut ConstraintSystem, f: &Field, x: &Elem, y: &Elem) {
    let x2 = Num::square(cs, &x.num());
    let x3 = Num::mul(cs, &x2, &x.num());
    let y2 = Num::square(cs, &y.num());
    f.enforce_zero(cs, &y2.sub(&x3).sub(&Num::small(5)));
}

/// `a + b` by the chord formula. With `distinct`, `x_a != x_b` is enforced (both must be
/// canonical); without it the caller guarantees that no satisfying assignment has
/// `x_a = x_b (mod p)`. With `canonical`, the resulting `x` is constrained canonical.
pub fn add(
    cs: &mut ConstraintSystem,
    f: &Field,
    a: &Pt,
    b: &Pt,
    distinct: bool,
    canonical: bool,
) -> Pt {
    if distinct {
        assert!(
            a.x_canonical && b.x_canonical,
            "distinctness needs canonical x"
        );
        enforce_limbs_differ(cs, &a.x, &b.x);
    }
    affine_sum(cs, f, a, b, false, canonical)
}

/// Double a Pallas point using its unique tangent.
pub fn double(cs: &mut ConstraintSystem, f: &Field, a: &Pt, canonical: bool) -> Pt {
    affine_sum(cs, f, a, a, true, canonical)
}

fn affine_sum(
    cs: &mut ConstraintSystem,
    f: &Field,
    a: &Pt,
    b: &Pt,
    tangent: bool,
    canonical: bool,
) -> Pt {
    let mut right = b.clone();
    right.relax(cs, f);
    let (x, y) = crate::hem::curve::short_weierstrass_sum(
        cs,
        &f.0,
        (&a.x_num(), &a.y),
        (&right.x_num(), &right.y),
        tangent,
    );
    if canonical {
        f.0.enforce_canonical(cs, &x);
    }
    Pt {
        x: x.bytes_le,
        x_bits: Some(x.bits_le),
        x_canonical: canonical,
        y,
        lazy: right.lazy + 1,
    }
}

// ============================================================================
// Fixed-base scalar multiplication
// ============================================================================

/// Window width of the fixed-base tables.
const WINDOW: usize = 10;
/// Number of windows for a 255-bit scalar.
const WINDOWS: usize = 26;

/// The window tables of a public base `B`.
///
/// For a scalar `k = sum_j u_j 2^(10 j)`, window `j < 25` contributes
/// `[(u_j + 2) 2^(10 j)] B` and the last window `[u_25 2^250 - sum_(j < 25) 2^(10 j + 1)] B`,
/// so the sum is `[k] B`. Before the last window every partial sum `S` and addend `T`
/// satisfy `S < T` and `S + T < 2^251 < q` as integers, so the chord formula is exact for
/// every Boolean input. The last addition is constrained to distinct `x`.
pub struct FixedBase {
    windows: Vec<Vec<(Fp, Fp)>>,
}

impl FixedBase {
    pub fn new(base: &Point) -> Self {
        let mut windows = Vec::with_capacity(WINDOWS);
        let mut p = base.clone();
        let mut offset = Point::IDENTITY;
        let affine = |points: &[Point]| -> Vec<(Fp, Fp)> {
            Point::batch_to_affine(points)
                .into_iter()
                .map(|a| a.expect("table point is not the identity"))
                .collect()
        };
        for _ in 0..WINDOWS - 1 {
            let two_p = p.double();
            offset = offset.add(&two_p);
            let mut cur = two_p;
            let mut points = Vec::with_capacity(1 << WINDOW);
            for _ in 0..1 << WINDOW {
                let next = cur.add(&p);
                points.push(cur);
                cur = next;
            }
            windows.push(affine(&points));
            for _ in 0..WINDOW {
                p = p.double();
            }
        }
        let last_bits = Field::BITS - WINDOW * (WINDOWS - 1);
        let mut cur = offset.neg();
        let mut points = Vec::with_capacity(1 << last_bits);
        for _ in 0..1 << last_bits {
            let next = cur.add(&p);
            points.push(cur);
            cur = next;
        }
        windows.push(affine(&points));
        Self { windows }
    }

    /// `[k] B` for the 255 Boolean bits of `k`. With `canonical`, the resulting `x` is
    /// constrained canonical.
    pub fn mul(
        &self,
        cs: &mut ConstraintSystem,
        f: &Field,
        scalar_bits: &[Lc],
        canonical: bool,
    ) -> Pt {
        assert_eq!(scalar_bits.len(), Field::BITS);
        let mut acc: Option<Pt> = None;
        for (j, (points, bits)) in self
            .windows
            .iter()
            .zip(scalar_bits.chunks(WINDOW))
            .enumerate()
        {
            let table = PointTable::new(points, bits.len());
            let (x, y) = table.lookup(cs, bits);
            let t = Pt::from_table(x, y);
            acc = Some(match acc {
                None => t,
                Some(a) => {
                    let last = j + 1 == WINDOWS;
                    // The accumulator must be canonical where distinctness is enforced.
                    let before_last = j + 2 == WINDOWS;
                    add(
                        cs,
                        f,
                        &a,
                        &t,
                        last,
                        if last { canonical } else { before_last },
                    )
                }
            });
        }
        acc.expect("at least one window")
    }
}

/// The fixed bases of the Orchard protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Base {
    /// `G^Orchard = GroupHash^P("z.cash:Orchard", "G")`: spend authorization.
    SpendAuth,
    /// `K^Orchard = GroupHash^P("z.cash:Orchard", "K")`: nullifiers.
    Nullifier,
    /// The randomness base of `Commit^ivk`.
    CommitIvkR,
    /// The randomness base of `NoteCommit^Orchard`.
    NoteCommitR,
}

impl Base {
    pub fn point(self) -> Point {
        match self {
            Self::SpendAuth => hash_to_curve("z.cash:Orchard", b"G"),
            Self::Nullifier => hash_to_curve("z.cash:Orchard", b"K"),
            Self::CommitIvkR => hash_to_curve("z.cash:Orchard-CommitIvk-r", b""),
            Self::NoteCommitR => hash_to_curve("z.cash:Orchard-NoteCommit-r", b""),
        }
    }

    /// The window tables; kept for the life of the process with `std`.
    pub fn tables(self) -> Arc<FixedBase> {
        #[cfg(feature = "std")]
        {
            use std::sync::OnceLock;
            static TABLES: [OnceLock<Arc<FixedBase>>; 4] = [
                OnceLock::new(),
                OnceLock::new(),
                OnceLock::new(),
                OnceLock::new(),
            ];
            TABLES[self as usize]
                .get_or_init(|| Arc::new(FixedBase::new(&self.point())))
                .clone()
        }
        #[cfg(not(feature = "std"))]
        {
            Arc::new(FixedBase::new(&self.point()))
        }
    }
}

// ============================================================================
// Variable-base scalar multiplication
// ============================================================================

/// Digits of the variable-base multiplication are three bits wide.
const VAR_DIGITS: usize = 85;

/// The public constant `2 * 8^85 + (8^85 - 1) / 7 (mod q)`.
fn var_base_offset() -> Fq {
    let eight = Fq::from_u64(8);
    let mut pow = Fq::ONE;
    let mut ones = Fq::ZERO;
    for _ in 0..VAR_DIGITS {
        ones = ones.add_mod(&pow);
        pow = pow.mul_mod(&eight);
    }
    pow.double() + ones
}

/// `[k] g` for a witness point `g` on the curve (canonical `x`, reduced `y`) and the
/// Boolean bits of a scalar `k` (any 255-bit representative of its residue modulo `q`).
///
/// The prover supplies `s = k - c (mod q)` with `c` the constant of
/// `var_base_offset`, and the gadget computes `[2 * 8^85 + sum_j (s_j + 1) 8^j] g` with
/// `s_j` the base-8 digits of `s`: a Horner chain from `2 g` over a table of
/// `g, 2 g, .., 8 g`, with no zero digit. The integer in brackets is `s + c`, congruent to
/// `k`. Every addition of the chain enforces distinct `x`.
pub fn var_base_mul(
    cs: &mut ConstraintSystem,
    fp: &Field,
    fq: &Field,
    g: &Pt,
    k_bits: &[Lc],
    canonical: bool,
) -> Pt {
    assert_eq!(k_bits.len(), Field::BITS);
    assert!(g.x_canonical);
    let k_num = Num::from_bits(k_bits);
    let offset = var_base_offset();
    let k_value = Fq::from_bytes(&fq.value(cs, &k_num)).expect("canonical residue");
    let s = fq.alloc(cs, &k_value.sub_mod(&offset).to_bytes());
    fq.enforce_zero(
        cs,
        &s.num().add(&Num::constant(&offset.to_bytes())).sub(&k_num),
    );

    // Table of 1 g .. 8 g with canonical x and reduced y.
    let mut table: Vec<Pt> = Vec::with_capacity(8);
    table.push(g.clone());
    for m in 2..=8usize {
        let mut p = if m % 2 == 0 {
            double(cs, fp, &table[m / 2 - 1], true)
        } else {
            add(cs, fp, &table[m - 2], &table[0], true, true)
        };
        p.settle(cs, fp);
        table.push(p);
    }
    let table_y: Vec<Vec<Lc>> = table
        .iter()
        .map(|p| {
            // After `settle`, `y` is the limbs of an element.
            let limbs = p.y.limb_forms();
            assert_eq!(limbs.len(), LIMBS);
            limbs
        })
        .collect();
    let xs: Vec<&[Lc]> = table.iter().map(|p| p.x.as_slice()).collect();
    let ys: Vec<&[Lc]> = table_y.iter().map(|y| y.as_slice()).collect();

    let mut acc = table[1].clone();
    for j in (0..VAR_DIGITS).rev() {
        for i in 0..3 {
            acc = double(cs, fp, &acc, i == 2);
        }
        let monos = monomials(cs, &s.bits[3 * j..3 * j + 3]);
        let t = Pt::from_table(select_limbs(cs, &monos, &xs), select_limbs(cs, &monos, &ys));
        acc = add(cs, fp, &acc, &t, true, j == 0 && canonical);
    }
    acc
}

// ============================================================================
// Sinsemilla
// ============================================================================

/// The lookup table of the 1024 Sinsemilla points `S(j)`.
pub fn sinsemilla_table() -> Arc<PointTable> {
    #[cfg(feature = "std")]
    {
        static TABLE: std::sync::OnceLock<Arc<PointTable>> = std::sync::OnceLock::new();
        TABLE
            .get_or_init(|| Arc::new(PointTable::new(&super::sinsemilla::s_table(), 10)))
            .clone()
    }
    #[cfg(not(feature = "std"))]
    {
        Arc::new(PointTable::new(&super::sinsemilla::s_table(), 10))
    }
}

/// `SinsemillaHashToPoint` from the public starting point `q` over Boolean message bits.
/// The message is padded with zero bits to a multiple of ten.
///
/// Each chunk computes `Acc' = (Acc + S) + Acc` with slopes `l1`, `l2`:
///
/// ```text
/// l1 (x_S - x_A) = y_S - y_A        x_R = l1^2 - x_A - x_S
/// (l1 + l2) (x_A - x_R) = 2 y_A     x_A' = l2^2 - x_R - x_A,  y_A' = l2 (x_A - x_A') - y_A
/// ```
///
/// `x_A != x_S` is enforced on canonical limbs, which excludes `Acc = S` and `Acc = -S`.
/// If `x_R = x_A` the second slope equation reads `0 = 2 y_A`, which no point of the curve
/// satisfies. So every case in which the specification returns `⊥` is unsatisfiable, and
/// otherwise both slopes are unique. `x_R` stays unreduced.
pub fn sinsemilla_hash_to_point(
    cs: &mut ConstraintSystem,
    f: &Field,
    q: &Point,
    bits: &[Lc],
) -> Pt {
    let table = sinsemilla_table();
    let (qx, qy) = q.to_affine().expect("Q is not the identity");
    let mut acc = Pt::constant(qx, qy);
    let zero = Lc::zero();
    for chunk in bits.chunks(10) {
        let mut padded: Vec<Lc> = chunk.to_vec();
        padded.resize(10, zero.clone());
        let (sx, sy) = table.lookup(cs, &padded);
        let s = Pt::from_table(sx, sy);
        enforce_limbs_differ(cs, &acc.x, &s.x);
        acc.relax(cs, f);

        let ((ax, ay), (sxv, syv)) = (acc.values(cs, f), s.values(cs, f));
        let l1_v = (syv - ay) * (sxv - ax).invert();
        let xr_v = l1_v.square() - ax - sxv;
        let l2_v = ay.double() * (ax - xr_v).invert() - l1_v;
        let xa_v = l2_v.square() - xr_v - ax;

        let (axn, sxn) = (acc.x_num(), s.x_num());
        let l1 = f.alloc(cs, &l1_v.to_bytes()).num();
        let t1 = Num::mul(cs, &l1, &sxn.sub(&axn));
        f.enforce_zero(cs, &t1.sub(&s.y).add(&acc.y));
        let l1_sq = Num::square(cs, &l1);
        let xr = l1_sq.sub(&axn).sub(&sxn);

        let l2 = f.alloc(cs, &l2_v.to_bytes()).num();
        let t2 = Num::mul(cs, &l1.add(&l2), &axn.sub(&xr));
        f.enforce_zero(cs, &t2.sub(&acc.y.scale(2)));

        let xa = f.alloc(cs, &xa_v.to_bytes());
        let l2_sq = Num::square(cs, &l2);
        f.enforce_zero(cs, &l2_sq.sub(&l1_sq).add(&sxn).sub(&xa.num()));
        f.enforce_canonical(cs, &xa);
        let ya = Num::mul(cs, &l2, &axn.sub(&xa.num())).sub(&acc.y);
        acc = Pt {
            x: xa.limbs,
            x_bits: Some(xa.bits),
            x_canonical: true,
            y: ya,
            lazy: acc.lazy + 1,
        };
    }
    acc
}

/// `SinsemillaCommit_r(D, M) = SinsemillaHashToPoint(D || "-M", M) + [r] R` with the
/// last addition constrained to distinct `x` (see the module documentation). The result
/// has canonical `x`.
pub fn sinsemilla_commit(
    cs: &mut ConstraintSystem,
    f: &Field,
    q: &Point,
    r_base: Base,
    message: &[Lc],
    r_bits: &[Lc],
) -> Pt {
    let m = sinsemilla_hash_to_point(cs, f, q, message);
    let blind = r_base.tables().mul(cs, f, r_bits, true);
    add(cs, f, &m, &blind, true, true)
}

// ============================================================================
// Poseidon
// ============================================================================

/// `Poseidon(a, b)` over the Pallas base field (`P128Pow5T3`, constant length 2). The
/// result is a reduced element, not necessarily canonical.
pub fn poseidon_hash2(cs: &mut ConstraintSystem, f: &Field, a: &Num, b: &Num) -> Elem {
    let constant = |x: Fp| Num::constant(&x.to_bytes());
    let mut state: [Num; 3] = [a.clone(), b.clone(), constant(poseidon::capacity_two())];
    let rounds = poseidon::FULL_ROUNDS + poseidon::PARTIAL_ROUNDS;
    let mut out = None;
    for r in 0..rounds {
        let full = !(poseidon::FULL_ROUNDS / 2
            ..poseidon::FULL_ROUNDS / 2 + poseidon::PARTIAL_ROUNDS)
            .contains(&r);
        let terms: Vec<Num> = (0..3)
            .map(|j| {
                let x = state[j].add(&constant(poseidon::round_constant(r, j)));
                if j == 0 || full {
                    let sq = Num::square(cs, &x);
                    let x2 = f.reduce(cs, &sq).num();
                    let sq = Num::square(cs, &x2);
                    let x4 = f.reduce(cs, &sq).num();
                    Num::mul(cs, &x4, &x)
                } else {
                    x
                }
            })
            .collect();
        let next: Vec<Elem> = (0..3)
            .map(|i| {
                let mut sum = Num::zero();
                for (j, t) in terms.iter().enumerate() {
                    sum = sum.add(&Num::mul(cs, &constant(poseidon::mds(i, j)), t));
                }
                f.reduce(cs, &sum)
            })
            .collect();
        state = [next[0].num(), next[1].num(), next[2].num()];
        out = Some(next[0].clone());
    }
    out.expect("at least one round")
}

#[cfg(test)]
mod tests {
    use super::super::sinsemilla::{CommitDomain, HashDomain};
    use super::*;
    use crate::hem::hash::alloc_bits;
    use std::println;

    fn sample_scalar(i: u64) -> Fq {
        let mut x = Fq::from_u64(0x1234_5678_9abc_def1 ^ i);
        for _ in 0..5 {
            x = x.square() + Fq::from_u64(i + 1);
        }
        x
    }

    fn finish_ok(cs: ConstraintSystem) {
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn lookup_returns_table_points() {
        let table = sinsemilla_table();
        let points = super::super::sinsemilla::s_table();
        for index in [0usize, 1, 255, 256, 513, 1023] {
            let mut cs = ConstraintSystem::new();
            let bytes = [(index & 0xff) as u8, (index >> 8) as u8];
            let bits = alloc_bits(&mut cs, &bytes);
            let rows0 = cs.num_rows();
            let (x, y) = table.lookup(&mut cs, &bits[..10]);
            if index == 0 {
                println!("10-bit lookup: {} rows", cs.num_rows() - rows0);
            }
            let f = Field::pallas_base();
            assert_eq!(fp_value(&cs, &f, &Num::from_limbs(&x)), points[index].0);
            assert_eq!(fp_value(&cs, &f, &Num::from_limbs(&y)), points[index].1);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            // A changed output limb breaks the row that defines it.
            let var = x[3].terms()[0].0 as usize;
            let mut bad = z.clone();
            bad[var] += F::ONE;
            assert!(!shape.is_satisfied(&bad));
        }
    }

    #[test]
    fn fixed_base_matches_native() {
        let f = Field::pallas_base();
        for (base, k) in [
            (Base::SpendAuth, sample_scalar(1)),
            (Base::Nullifier, Fq::ONE),
            (Base::CommitIvkR, -Fq::ONE),
            (Base::NoteCommitR, sample_scalar(2)),
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &k.to_bytes());
            let rows0 = cs.num_rows();
            let mut p = base.tables().mul(&mut cs, &f, &bits[..255], true);
            println!("fixed-base multiplication: {} rows", cs.num_rows() - rows0);
            let (x, y) = p.canonical_coordinates(&mut cs, &f);
            let want = base.point().mul(&k).to_affine().unwrap();
            assert_eq!(x.value(&cs), want.0.to_bytes());
            assert_eq!(y.value(&cs), want.1.to_bytes());
            finish_ok(cs);
        }
    }

    #[test]
    fn fixed_base_rejects_the_zero_scalar() {
        // [0] B is the identity, which has no affine form: unsatisfiable.
        let f = Field::pallas_base();
        let mut cs = ConstraintSystem::new();
        let bits = alloc_bits(&mut cs, &[0u8; 32]);
        let _ = Base::SpendAuth
            .tables()
            .mul(&mut cs, &f, &bits[..255], true);
        let (shape, z) = cs.finish();
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn variable_base_matches_native() {
        let (fp, fq) = (Field::pallas_base(), Field::pallas_scalar());
        let g = hash_to_curve("z.cash:Orchard-gd", b"test point");
        let (gx, gy) = g.to_affine().unwrap();
        for k in [
            sample_scalar(3),
            Fq::ONE,
            Fq::from_u64(8),
            -Fq::ONE,
            sample_scalar(4),
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &k.to_bytes());
            let (ex, ey) = (
                fp.alloc(&mut cs, &gx.to_bytes()),
                fp.alloc(&mut cs, &gy.to_bytes()),
            );
            fp.enforce_canonical(&mut cs, &ex);
            enforce_on_curve(&mut cs, &fp, &ex, &ey);
            let rows0 = cs.num_rows();
            let mut p = var_base_mul(
                &mut cs,
                &fp,
                &fq,
                &Pt::from_elems(&ex, true, &ey),
                &bits[..255],
                true,
            );
            println!(
                "variable-base multiplication: {} rows",
                cs.num_rows() - rows0
            );
            let (x, y) = p.canonical_coordinates(&mut cs, &fp);
            let want = g.mul(&k).to_affine().unwrap();
            assert_eq!(x.value(&cs), want.0.to_bytes());
            assert_eq!(y.value(&cs), want.1.to_bytes());
            finish_ok(cs);
        }
    }

    #[test]
    fn off_curve_point_is_rejected() {
        let fp = Field::pallas_base();
        let g = hash_to_curve("z.cash:Orchard-gd", b"test point");
        let (gx, gy) = g.to_affine().unwrap();
        for (dy, ok) in [(Fp::ZERO, true), (Fp::ONE, false)] {
            let mut cs = ConstraintSystem::new();
            let (ex, ey) = (
                fp.alloc(&mut cs, &gx.to_bytes()),
                fp.alloc(&mut cs, &(gy + dy).to_bytes()),
            );
            enforce_on_curve(&mut cs, &fp, &ex, &ey);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn sinsemilla_matches_native() {
        let f = Field::pallas_base();
        let domain = HashDomain::new("z.cash:Orchard-MerkleCRH");
        for len in [10usize, 37, 520] {
            let bytes: Vec<u8> = (0..len.div_ceil(8)).map(|i| (i * 73 + 5) as u8).collect();
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &bytes);
            let rows0 = cs.num_rows();
            let mut p = sinsemilla_hash_to_point(&mut cs, &f, &domain.q(), &bits[..len]);
            println!(
                "Sinsemilla, {} chunks: {} rows",
                len.div_ceil(10),
                cs.num_rows() - rows0
            );
            let (x, y) = p.canonical_coordinates(&mut cs, &f);
            let native_bits: Vec<bool> = (0..len)
                .map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
                .collect();
            let want = domain
                .hash_to_point(&native_bits)
                .unwrap()
                .to_affine()
                .unwrap();
            assert_eq!(x.value(&cs), want.0.to_bytes());
            assert_eq!(y.value(&cs), want.1.to_bytes());
            finish_ok(cs);
        }
    }

    #[test]
    fn sinsemilla_bottom_is_unsatisfiable() {
        // From Q = S(0) the chunk 0 adds S(0) to itself; the specification returns ⊥.
        let f = Field::pallas_base();
        let (x, y) = super::super::sinsemilla::s_table()[0];
        let q = Point::from_affine(x, y).unwrap();
        for (byte, ok) in [(0u8, false), (1u8, true)] {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &[byte, 0]);
            let _ = sinsemilla_hash_to_point(&mut cs, &f, &q, &bits[..10]);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn sinsemilla_commit_matches_native() {
        let f = Field::pallas_base();
        let domain = CommitDomain::new("z.cash:Orchard-CommitIvk");
        let r = sample_scalar(9);
        let bytes: Vec<u8> = (0..64).map(|i| (i * 29 + 1) as u8).collect();
        let mut cs = ConstraintSystem::new();
        let bits = alloc_bits(&mut cs, &bytes);
        let r_bits = alloc_bits(&mut cs, &r.to_bytes());
        let mut p = sinsemilla_commit(
            &mut cs,
            &f,
            &domain.q(),
            Base::CommitIvkR,
            &bits[..510],
            &r_bits[..255],
        );
        let (x, _) = p.canonical_coordinates(&mut cs, &f);
        let native_bits: Vec<bool> = (0..510)
            .map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
            .collect();
        assert_eq!(
            x.value(&cs),
            domain.short_commit(&native_bits, &r).unwrap().to_bytes()
        );
        finish_ok(cs);
    }

    #[test]
    fn poseidon_matches_native() {
        let f = Field::pallas_base();
        let (a, b) = (Fp::from_u64(7).square().invert(), Fp::from_u64(11).invert());
        let mut cs = ConstraintSystem::new();
        let (ea, eb) = (
            f.alloc(&mut cs, &a.to_bytes()),
            f.alloc(&mut cs, &b.to_bytes()),
        );
        let rows0 = cs.num_rows();
        let out = poseidon_hash2(&mut cs, &f, &ea.num(), &eb.num());
        println!("Poseidon: {} rows", cs.num_rows() - rows0);
        f.enforce_canonical(&mut cs, &out);
        assert_eq!(out.value(&cs), poseidon::hash2(a, b).to_bytes());
        finish_ok(cs);
    }
}
