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

fn f_int(v: i64) -> F {
    let m = F::from_u64_reduced(v.unsigned_abs());
    if v < 0 { F::ZERO - m } else { m }
}

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
                        .map(|(s, m)| (f_int(coef[(h << low_bits) | s] as i64), m))
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
    let mut a = a.clone();
    a.relax(cs, f);
    let ((ax, ay), (bx, by)) = (a.values(cs, f), b.values(cs, f));
    let lam_v = (by - ay) * (bx - ax).invert();
    let x3_v = lam_v.square() - ax - bx;
    let lam = f.alloc(cs, &lam_v.to_bytes()).num();
    let (axn, bxn) = (a.x_num(), b.x_num());
    let t = Num::mul(cs, &lam, &bxn.sub(&axn));
    f.enforce_zero(cs, &t.sub(&b.y).add(&a.y));
    let x3 = f.alloc(cs, &x3_v.to_bytes());
    let lam2 = Num::square(cs, &lam);
    f.enforce_zero(cs, &lam2.sub(&axn).sub(&bxn).sub(&x3.num()));
    if canonical {
        f.enforce_canonical(cs, &x3);
    }
    let y3 = Num::mul(cs, &lam, &axn.sub(&x3.num())).sub(&a.y);
    Pt {
        x: x3.limbs,
        x_bits: Some(x3.bits),
        x_canonical: canonical,
        y: y3,
        lazy: a.lazy + 1,
    }
}

/// `2 a`. Pallas has no point with `y = 0`, so the tangent slope is unique.
pub fn double(cs: &mut ConstraintSystem, f: &Field, a: &Pt, canonical: bool) -> Pt {
    let mut a = a.clone();
    a.relax(cs, f);
    let (ax, ay) = a.values(cs, f);
    let lam_v = ax.square() * Fp::from_u64(3) * ay.double().invert();
    let x3_v = lam_v.square() - ax.double();
    let lam = f.alloc(cs, &lam_v.to_bytes()).num();
    let axn = a.x_num();
    let t = Num::mul(cs, &lam, &a.y.scale(2));
    let xx = Num::square(cs, &axn);
    f.enforce_zero(cs, &t.sub(&xx.scale(3)));
    let x3 = f.alloc(cs, &x3_v.to_bytes());
    let lam2 = Num::square(cs, &lam);
    f.enforce_zero(cs, &lam2.sub(&axn.scale(2)).sub(&x3.num()));
    if canonical {
        f.enforce_canonical(cs, &x3);
    }
    let y3 = Num::mul(cs, &lam, &axn.sub(&x3.num())).sub(&a.y);
    Pt {
        x: x3.limbs,
        x_bits: Some(x3.bits),
        x_canonical: canonical,
        y: y3,
        lazy: a.lazy + 1,
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
        let mut p = *base;
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
                points.push(cur);
                cur = cur.add(&p);
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
            points.push(cur);
            cur = cur.add(&p);
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
