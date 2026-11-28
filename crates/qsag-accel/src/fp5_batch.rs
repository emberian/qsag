//! Fixed-work arithmetic for multilinear evaluations and coset folds.
#[cfg(feature = "alloc")]
use crate::goldilocks::{GOLDILOCKS_ROOT_2_32, gl_inv_or_zero, gl_pow_pub};
use crate::goldilocks::{gl_add as add, gl_mul as mul, gl_reduce_u64, gl_sub as sub};
use crate::{AccelError, cpu_chunks_mut};

type Word = [u64; 5];

/// Packed base or extension evaluations in natural order.
#[derive(Clone, Copy)]
pub enum Fp5Table<'a> {
    Base(&'a [u64]),
    Extension(&'a [[u64; 5]]),
}

impl<'a> Fp5Table<'a> {
    #[cfg(feature = "std")]
    pub(crate) fn words(self) -> &'a [u64] {
        match self {
            Self::Base(v) => v,
            Self::Extension(v) => v.as_flattened(),
        }
    }
    #[cfg(feature = "std")]
    pub(crate) fn is_base(self) -> bool {
        matches!(self, Self::Base(_))
    }
    #[cfg(feature = "std")]
    pub(crate) fn width(self) -> usize {
        if self.is_base() { 1 } else { 5 }
    }

    pub(crate) fn len(self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Extension(v) => v.len(),
        }
    }
    pub(crate) fn at(self, i: usize) -> Word {
        match self {
            Self::Base(v) => [gl_reduce_u64(v[i]), 0, 0, 0, 0],
            Self::Extension(v) => v[i].map(gl_reduce_u64),
        }
    }
    fn times(self, i: usize, b: Word) -> Word {
        match self {
            Self::Base(v) => scale(b, v[i]),
            Self::Extension(v) => product(v[i], b),
        }
    }
}

#[inline]
fn plus(a: Word, b: Word) -> Word {
    core::array::from_fn(|i| add(a[i], b[i]))
}
#[inline]
fn minus(a: Word, b: Word) -> Word {
    core::array::from_fn(|i| sub(a[i], b[i]))
}
#[inline]
fn scale(a: Word, b: u64) -> Word {
    a.map(|x| mul(x, b))
}

// Split at X^3. Each quadratic product uses three diagonal products and
// three cross products. The two linear high parts need only three products.
#[inline]
fn quadratic([a, b, c]: [u64; 3], [x, y, z]: [u64; 3]) -> Word {
    let (ax, by, cz) = (mul(a, x), mul(b, y), mul(c, z));
    let cross = |a, b, x, y, diag| sub(mul(add(a, b), add(x, y)), diag);
    [
        ax,
        cross(a, b, x, y, add(ax, by)),
        add(by, cross(a, c, x, z, add(ax, cz))),
        cross(b, c, y, z, add(by, cz)),
        cz,
    ]
}
#[inline]
fn product([a, b, c, d, e]: Word, [x, y, z, u, v]: Word) -> Word {
    let low = quadratic([a, b, c], [x, y, z]);
    let du = mul(d, u);
    let ev = mul(e, v);
    let high = [du, sub(sub(mul(add(d, e), add(u, v)), du), ev), ev, 0, 0];
    let cross = minus(
        minus(
            quadratic([add(a, d), add(b, e), c], [add(x, u), add(y, v), z]),
            low,
        ),
        high,
    );
    let triple = |w| add(add(w, w), w);
    // low + X^3 cross + X^6 high, reduced by X^5 = 3.
    [
        add(low[0], triple(cross[2])),
        add(low[1], triple(add(cross[3], high[0]))),
        add(low[2], triple(high[1])),
        add(add(low[3], cross[0]), triple(high[2])),
        add(low[4], cross[1]),
    ]
}

pub(crate) fn equal_len(expected: usize, actual: usize) -> Result<(), AccelError> {
    if expected != actual {
        return Err(AccelError::LengthMismatch {
            what: "quintic table",
            expected,
            actual,
        });
    }
    Ok(())
}

pub(crate) fn pairs(n: usize) -> Result<usize, AccelError> {
    if n < 2 || !n.is_multiple_of(2) {
        return Err(AccelError::LengthOverflow);
    }
    Ok(n / 2)
}

pub(crate) fn fp5_fold_even_odd(
    t: Fp5Table<'_>,
    r: Word,
    out: &mut [Word],
) -> Result<(), AccelError> {
    equal_len(pairs(t.len())?, out.len())?;
    cpu_chunks_mut(out, 1024, |off, chunk| {
        for (j, o) in chunk.iter_mut().enumerate() {
            let i = 2 * (off + j);
            let lo = t.at(i);
            let step = match t {
                Fp5Table::Base(v) => scale(r, sub(v[i + 1], v[i])),
                Fp5Table::Extension(v) => product(r, minus(v[i + 1], lo)),
            };
            *o = plus(lo, step);
        }
    });
    Ok(())
}

fn reduce<const K: usize>(n: usize, term: impl Fn(usize) -> [Word; K] + Sync) -> [Word; K] {
    let sum = |start, end| {
        let mut acc = [[0; 5]; K];
        for i in start..end {
            let item = term(i);
            for (a, b) in acc.iter_mut().zip(item) {
                *a = plus(*a, b);
            }
        }
        acc
    };
    #[cfg(feature = "std")]
    {
        let workers = crate::cpu_workers(n, 1024);
        if workers > 1 {
            let len = n.div_ceil(workers);
            let mut partial = alloc::vec![[[0;5];K];workers];
            crate::cpu_drain(workers, partial.iter_mut().enumerate(), |(j, p)| {
                *p = sum(j * len, n.min((j + 1) * len))
            });
            let out = partial.iter().fold([[0; 5]; K], |a, b| {
                core::array::from_fn(|i| plus(a[i], b[i]))
            });
            qsag_asm::volatile_fill(&mut partial, [[0; 5]; K]);
            return out;
        }
    }
    sum(0, n)
}

pub(crate) fn fp5_dot_batch(t: Fp5Table<'_>, w: &[Word]) -> Result<Word, AccelError> {
    equal_len(t.len(), w.len())?;
    Ok(reduce(t.len(), |i| [t.times(i, w[i])])[0])
}

pub(crate) fn fp5_sumcheck_quad_evals(
    t: Fp5Table<'_>,
    w: &[Word],
) -> Result<[Word; 3], AccelError> {
    equal_len(t.len(), w.len())?;
    Ok(reduce(pairs(t.len())?, |j| {
        let i = j * 2;
        let w2 = plus(w[i + 1], minus(w[i + 1], w[i]));
        let p2 = match t {
            Fp5Table::Base(v) => scale(w2, add(v[i + 1], sub(v[i + 1], v[i]))),
            Fp5Table::Extension(v) => product(w2, plus(v[i + 1], minus(v[i + 1], v[i]))),
        };
        [t.times(i, w[i]), t.times(i + 1, w[i + 1]), p2]
    }))
}

#[cfg(feature = "alloc")]
pub(crate) fn whir_shape(
    n: usize,
    shift: u64,
    rounds: usize,
    out: usize,
) -> Result<(), AccelError> {
    if !n.is_power_of_two() || gl_reduce_u64(shift) == 0 || rounds > n.trailing_zeros() as usize {
        return Err(AccelError::LengthOverflow);
    }
    if n.trailing_zeros() > 32 {
        return Err(AccelError::DomainTooLarge {
            log2_len: n.trailing_zeros(),
        });
    }
    equal_len(n >> rounds, out)
}

#[cfg(feature = "alloc")]
pub(crate) fn whir_stage_fold_fp5(
    t: Fp5Table<'_>,
    mut shift: u64,
    challenges: &[[Word; 3]],
    out: &mut [Word],
) -> Result<(), AccelError> {
    whir_shape(t.len(), shift, challenges.len(), out.len())?;
    let mut values: alloc::vec::Vec<_> = (0..t.len()).map(|i| t.at(i)).collect();
    let mut root = gl_pow_pub(
        GOLDILOCKS_ROOT_2_32,
        1u64 << (32 - t.len().trailing_zeros()),
    );
    let half = 0x7fff_ffff_8000_0001;
    let mut n = values.len();
    for &[theta, alpha, beta] in challenges {
        n /= 2;
        let (a, b) = values[..2 * n].split_at_mut(n);
        let step = mul(root, root);
        let inv_root = gl_inv_or_zero(root);
        let inv_shift = mul(half, gl_inv_or_zero(shift));
        let shift2 = mul(shift, shift);
        cpu_chunks_mut(a, 1024, |off, part| {
            let mut y2 = mul(shift2, gl_pow_pub(step, off as u64));
            let mut inv = mul(inv_shift, gl_pow_pub(inv_root, off as u64));
            for (j, v) in part.iter_mut().enumerate() {
                let even = scale(plus(*v, b[off + j]), half);
                let odd = scale(minus(*v, b[off + j]), inv);
                *v = plus(
                    odd,
                    product(
                        plus(alpha, scale(beta, y2)),
                        plus(even, product(theta, odd)),
                    ),
                );
                inv = mul(inv, inv_root);
                y2 = mul(y2, step);
            }
        });
        shift = shift2;
        root = step;
    }
    out.copy_from_slice(&values[..n]);
    qsag_asm::volatile_fill(&mut values, [0; 5]);
    Ok(())
}
