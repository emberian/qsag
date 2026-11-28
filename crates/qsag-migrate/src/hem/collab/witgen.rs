//! Shared witness generation: from authenticated shares of a relation's secret inputs to
//! authenticated shares of its whole assignment, with no custodian seeing a value.
//!
//! The relation's builder records, for every variable, how it follows from earlier ones
//! (`qsag_agg::zk_hem::relation::Definitions`). [`generate`] walks the variables in
//! order and computes each definition on shares. It is written against [`Backend`], the
//! few operations of the authenticated engine it uses; [`Count`] runs the same code on no
//! values at all to size the preprocessing ([`demand`]).
//!
//! # Subprotocols
//!
//! Every value is an authenticated additive share over Goldilocks (`p = 2^64 - 2^32 + 1`).
//!
//! * **Random bits.** A preprocessed uniform `[a]`, one product `[a^2]`, open `a^2`, and
//!   `[b] = ([a] / sqrt(a^2) + 1) / 2` for the fixed square root. This is the random-bit
//!   protocol of SPDZ preprocessing (Damgård, Keller, Larraia, Pastro, Scholl, Smart,
//!   "Practical covertly secure MPC for dishonest majority", ESORICS 2013, Section 5,
//!   as restated in `[EGK+20]`, *edaBits*, Escudero et al., CRYPTO 2020, ePrint 2020/338,
//!   Section 2); `a^2` is uniform over the squares whatever `b` is.
//! * **Bit decomposition** of a shared `x < 2^m` ([`Witgen::decompose`]). The mask is a
//!   value whose bits are shared random bits, which is what an edaBit is
//!   (`[EGK+20]`, Section 3; here both halves live in the
//!   one field, so no cut-and-choose between domains is needed). Two cases:
//!   * `m <= 22`: `r` of `m + 40` bits, open `c = x + r` (no wrap), and the low `m` bits of
//!     `c - r` by a borrow chain with one product per bit. `c` is within `2^-40` of
//!     uniform on its range: statistical masking.
//!   * otherwise: `r` of 64 bits whose top 32 bits are not all ones (checked by opening
//!     their product, which depends on the mask alone), so `r <= p - 2`. Open
//!     `c = x + r mod p`, which is uniform up to `2^-64`. The wrap `beta = [c < r]` and
//!     `D = c - r mod 2^64` come from one 64-step borrow chain, and
//!     `x = D + beta - 2^32 beta` because `p = 2^64 - 2^32 + 1`: one more chain. This is
//!     the comparison-with-a-public-value step of
//!     `[MWP21]` (*Rabbit*, Makri, Wafo-Tapa, Patrina, FC 2021, ePrint 2021/119, Section 4.1,
//!     "LTC"), specialised to this prime; no slack, so it is exact for every `x < p`.
//! * **Integers.** An integer is a polynomial in `2^8` whose coefficients are shares with
//!   public intervals. `Witgen::normalize` turns it into bits by a carry chain, one
//!   decomposition per coefficient. Products of two such integers are computed at as many
//!   points as the product has coefficients and interpolated ([`Witgen::poly_mul`]), one
//!   secure product per coefficient.
//! * **Reduction modulo a public prime** `q` (`Witgen::canonical`): bits of the integer
//!   (plus a public multiple of `q` that makes it non-negative), then the bits above the
//!   limbs of `q` are folded down with the public constants `2^i mod q` and normalized
//!   again until that stops shortening the value, then conditional subtractions of
//!   `2^j q` by a borrow chain and a selection.
//! * **Division modulo `q`** (a slope `num / den`): a shared `rho` of `|q| + 40` random
//!   bits, the integer `den rho + q S` for a shared `S` of 40 bits more than the quotient
//!   is opened in full and gives `w = den rho mod q`, which is within `2^-40` of uniform
//!   when `den != 0 mod q`; then `num rho w^-1 mod q` by the reduction above with the
//!   public constants `2^i w^-1 mod q`. This is the masked inversion of Bar-Ilan and
//!   Beaver (PODC 1989) carried out on limbs.
//! * **Exact division** by an odd public `q` of an integer `N = Q q` with `Q < 2^k`:
//!   `Q = N q^-1 mod 2^k`, from the low `k` bits of `N`.
//! * **Field ratio** `num / den` and **inverse-or-zero** of a value in a small range:
//!   masked inversion in Goldilocks, and the interpolating polynomial through
//!   `(0, 0), (i, 1 / i)`.
//!
//! # Lookups
//!
//! A relation with lookups has one variable per table row, the number of lookups whose
//! tuple is that row (`Def::Multiplicity`). For a range table `0..2^bits` of one column
//! the quorum computes them on shares: the looked-up value is decomposed into `bits`
//! bits (a statistically masked decomposition), the products of every subset of the
//! bits are formed by halves (`2^bits - bits - 1` products in `log2 bits` rounds), the
//! indicator of the value over the table rows is a signed sum of those, and a
//! multiplicity is the sum of the indicators of all lookups. A byte lookup costs 302
//! triples and 48 uniform values, and all lookups run in the rounds their values become
//! known, about twelve rounds each. A value outside the table gives multiplicities
//! that do not satisfy the relation, and no proof. Lookups into any other table (rows
//! that are not `0..2^bits` in order, or more than one column) are refused with
//! [`WitgenError::Table`]: an indicator over arbitrary rows needs an equality test per
//! row, which is not built. The rest of a lookup proof (helper table, lookup
//! sumcheck) is the prover's (`prover`, "Lookups") and takes these shares as they are.
//!
//! # What is opened, and why it tells nothing
//!
//! Beaver openings; `a^2` of random-bit generation; the top-bits product of an exact
//! mask; `x + r` of a decomposition; `den r` of a field ratio; the integer
//! `den rho + q S + K q` of a division. Before opening a statistical mask or a
//! masked denominator, [`Backend::check`] authenticates all preceding openings.
//! This also covers input-independent random-bit and mask-generation rounds.
//! Products computed in the current round only feed subsequent rounds. The
//! authentication guarantee that this ordering relies on
//! (an opening that differs from the shared value fails the check except with probability
//! `2^-126`) is SPDZ's.
//!
//! # Divisions by zero
//!
//! A division modulo `q` opens `den rho mod q`, so a zero denominator would show. The
//! relations divide in three places (`hem/curve.rs`):
//!
//! * The chord slope of an addition inside a fixed-base multiplication, between the
//!   partial sum `S` of the signed windows and the next window's point `T`. There
//!   `|S| < |T|` and `|S| + |T|` is below the group order for every Boolean scalar, so
//!   the two points never share `x` (the argument is in the module documentation of
//!   `curve.rs`, "Scalar multiplication"). The denominator is nonzero whatever the key.
//! * The slope of a *complete* addition: the last addition of a fixed-base
//!   multiplication, and `P + [k] G` for a variable point (a BIP-32 public child, a
//!   Taproot tweak). The points share `x` when they are equal, which is one scalar per
//!   multiplication, and for a variable point when `P = [k] G`. A custodian of a key
//!   chosen by someone else cannot rule those out, so this case is computed, not
//!   aborted: [`Source::Slope`] carries the tangent, and `Witgen::slope` tests the
//!   denominator for zero on shares (its canonical residue, then the product of the
//!   complements of its bits) and selects numerator and denominator before the masked
//!   division. Nothing depends on which case holds: the same triples, the same
//!   openings, and the opened `den rho` is that of the selected denominator, which is
//!   nonzero in both cases. The remaining case, opposite points, has no satisfying
//!   assignment (the sum is the identity; the scalar is a multiple of the group order,
//!   which the range rows exclude); a quorum that holds such a secret opens a zero
//!   there and aborts with [`WitgenError::ZeroDenominator`], and has no statement to
//!   prove.
//! * The Edwards `y = (u - 1) / (u + 1)` of an Ed25519 point from its Montgomery `u`.
//!   `u = -1` belongs to points of order four, which a multiple of the base point is
//!   not.
//!
//! So for every secret that has a valid statement no division aborts.
//!
//! The statistical parameter is 40 bits per masked opening.
//!
//! # Rounds
//!
//! The subprotocols are `async` functions that await the products and openings they
//! ask for. [`Witgen::run`] is a dataflow scheduler over the relation: a product
//! variable is asked for as soon as its factors are known, a source or a division
//! starts as soon as the variables it reads are known, and one round of the engine
//! (`Engine::mul_open`: the masked openings of all products and all plain openings in
//! one exchange) serves every subprotocol that is waiting. The order of requests is a
//! function of the relation alone, so all custodians consume the same preprocessing in
//! the same order and [`demand`] is exact. The round count is the depth of the
//! relation in rounds, not its size.
//!
//! What sets that depth, and what was traded for it ([`Chains`]; the figures are
//! `tests::measure_chains` for the Bitcoin HASH160 statement, with a round priced at
//! 50 ms and a triple at the 2.02 ms the three-party ceremony was measured at):
//!
//! | chains | triples | rounds | ceremony + round trips |
//! |---|---|---|---|
//! | one product per position ([`Chains::Ripple`]) | 1,533,009 | 97,759 | 52 + 81 min |
//! | Brent-Kung prefix everywhere ([`Chains::Prefix`]) | 2,287,335 | 13,133 | 77 + 11 min |
//! | prefix, ripple for the short chains ([`Chains::Mixed`], used) | 2,151,917 | 14,049 | 72 + 12 min |
//!
//! * A carry or borrow chain `c_{i+1} = g_i + p_i c_i` against a public operand has
//!   `g_i`, `p_i` linear in the shared bit, and the result bits are linear in the
//!   carries, so a chain costs its carries only. Long chains (64 positions of an exact
//!   decomposition, some hundreds of an integer) use a Brent-Kung prefix network: about
//!   three products per position in `2 log2 n` rounds. The 22-position chains of the
//!   statistically masked decompositions stay ripple: there are about 12,000 of them
//!   and the prefix form saves 13 rounds on some 70 sequential stages.
//! * `Witgen::normalize` decomposes every coefficient on its own, in the same rounds,
//!   then brings the overlapping bits of neighbouring coefficients down to two per
//!   position with full adders (two products and two rounds a layer) and adds the two
//!   rows with one prefix chain. The form before it carried from limb to limb, one
//!   decomposition after the other: 0.3 million triples fewer and, with the sequential
//!   scheduling that went with it, 512,410 rounds for this statement.
//! * The masks (random bits, exact masks) do not depend on the relation's values. A
//!   counting pass over the relation finds how many there are and all of them are made
//!   in the first eight rounds.
//!
//! What is left is the sequence the relation itself has: 23 point additions of a
//! fixed-base multiplication, each a division, two reductions and their conditional
//! subtractions one after the other (about 450 rounds), and the rounds of the hash
//! compressions (one exact decomposition, about 30 rounds, per addition modulo `2^32`).

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::cmp::Ordering;
use core::future::{Future, poll_fn};
use core::ops::{Add, Sub};
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{Def, Definitions, IntCoef, Lc, Shape, Source};

use super::engine::{Engine, MpcError, Sb};
use super::net::Transport;

type F = Goldilocks;

/// Statistical masking parameter, in bits.
pub const SIGMA: u32 = 40;
/// Largest width decomposed with a statistical mask.
const STAT_MAX: u32 = 62 - SIGMA;
/// Opened values after which the batch MAC check runs.
const CHECK_EVERY: usize = 1 << 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitgenError {
    Mpc(MpcError),
    /// The definitions do not belong to the shape, or a variable has no definition, or one
    /// outside what this generator computes (the variable or source index is given).
    Unsupported {
        index: usize,
    },
    /// The supplied inputs do not match the relation's input sources.
    Inputs,
    /// A division by a value that is zero. Reveals that fact about the witness.
    ZeroDenominator,
    /// An opened value that the protocol defines as a bit is not one.
    NotABit,
    /// The relation has a lookup into a table that is not a range table `0..2^bits`
    /// of one column (the index of the lookup is given).
    Table {
        lookup: usize,
    },
}

impl From<MpcError> for WitgenError {
    fn from(e: MpcError) -> Self {
        Self::Mpc(e)
    }
}

use qsag_core::wipe::{SecretBuffer, SecretScratch, SecretWipe};

/// The operations of the authenticated engine that witness generation uses.
pub trait Backend {
    type S: Copy + SecretWipe + Add<Output = Self::S> + Sub<Output = Self::S>;
    fn scale(s: Self::S, k: F) -> Self::S;
    fn public(&self, c: F) -> Self::S;
    fn random(&mut self) -> Result<Self::S, MpcError>;
    /// One round: the products `xs[i] ys[i]` and the values of `opens`.
    #[allow(clippy::type_complexity)]
    fn round(
        &mut self,
        xs: &[Self::S],
        ys: &[Self::S],
        opens: &[Self::S],
    ) -> Result<(Vec<Self::S>, Vec<F>), MpcError>;
    fn check(&mut self) -> Result<(), MpcError>;
    /// Whether opened values are placeholders (see [`Count`]).
    fn counting(&self) -> bool {
        false
    }
}

impl<T: Transport> Backend for Engine<T> {
    type S = Sb;
    fn scale(s: Sb, k: F) -> Sb {
        s.scale(k)
    }
    fn public(&self, c: F) -> Sb {
        Engine::public(self, c)
    }
    fn random(&mut self) -> Result<Sb, MpcError> {
        Engine::random(self)
    }
    fn round(&mut self, xs: &[Sb], ys: &[Sb], opens: &[Sb]) -> Result<(Vec<Sb>, Vec<F>), MpcError> {
        Engine::mul_open(self, xs, ys, opens)
    }
    fn check(&mut self) -> Result<(), MpcError> {
        Engine::check(self)
    }
}

/// A share that carries no value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unit;

impl SecretWipe for Unit {
    fn secret_wipe(&mut self) {}
}

impl Add for Unit {
    type Output = Unit;
    fn add(self, _: Unit) -> Unit {
        Unit
    }
}

impl Sub for Unit {
    type Output = Unit;
    fn sub(self, _: Unit) -> Unit {
        Unit
    }
}

/// A backend with no values: it counts what [`generate`] consumes. Nothing that is
/// consumed depends on an opened value, except the retries of random-bit and mask
/// generation (probability `2^-64` and `2^-32` each), which are not counted.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Count {
    pub triples: usize,
    pub randoms: usize,
    pub opened: usize,
    pub rounds: usize,
    pub checks: usize,
}

impl Backend for Count {
    type S = Unit;
    fn scale(_: Unit, _: F) -> Unit {
        Unit
    }
    fn public(&self, _: F) -> Unit {
        Unit
    }
    fn random(&mut self) -> Result<Unit, MpcError> {
        self.randoms += 1;
        Ok(Unit)
    }
    fn round(
        &mut self,
        xs: &[Unit],
        _: &[Unit],
        opens: &[Unit],
    ) -> Result<(Vec<Unit>, Vec<F>), MpcError> {
        self.triples += xs.len();
        self.opened += 2 * xs.len() + opens.len();
        self.rounds += 1;
        Ok((vec![Unit; xs.len()], vec![F::ZERO; opens.len()]))
    }
    fn check(&mut self) -> Result<(), MpcError> {
        self.checks += 1;
        Ok(())
    }
    fn counting(&self) -> bool {
        true
    }
}

// ============================================================================
// Public integers
// ============================================================================

/// A non-negative integer, little-endian 64-bit words, no leading zero word.
type Nat = Vec<u64>;

fn nat_trim(mut a: Nat) -> Nat {
    while a.last() == Some(&0) {
        a.pop();
    }
    a
}

fn nat_from_le(bytes: &[u8]) -> Nat {
    let mut out = vec![0u64; bytes.len().div_ceil(8)];
    for (i, &b) in bytes.iter().enumerate() {
        out[i / 8] |= u64::from(b) << (8 * (i % 8));
    }
    nat_trim(out)
}

fn nat_bit(a: &[u64], i: usize) -> u64 {
    a.get(i / 64).map_or(0, |w| (w >> (i % 64)) & 1)
}

fn nat_byte(a: &[u64], k: usize) -> u64 {
    a.get(k / 8).map_or(0, |w| (w >> (8 * (k % 8))) & 0xff)
}

fn nat_bitlen(a: &[u64]) -> usize {
    match a.iter().rposition(|&w| w != 0) {
        Some(i) => 64 * i + 64 - a[i].leading_zeros() as usize,
        None => 0,
    }
}

fn nat_cmp(a: &[u64], b: &[u64]) -> Ordering {
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let (x, y) = (
            a.get(i).copied().unwrap_or(0),
            b.get(i).copied().unwrap_or(0),
        );
        if x != y {
            return x.cmp(&y);
        }
    }
    Ordering::Equal
}

fn nat_add(a: &[u64], b: &[u64]) -> Nat {
    let n = a.len().max(b.len());
    let mut out = Vec::with_capacity(n + 1);
    let mut carry = 0u128;
    for i in 0..n {
        let s = u128::from(a.get(i).copied().unwrap_or(0))
            + u128::from(b.get(i).copied().unwrap_or(0))
            + carry;
        out.push(s as u64);
        carry = s >> 64;
    }
    out.push(carry as u64);
    nat_trim(out)
}

/// `a - b` for `a >= b`.
fn nat_sub(a: &[u64], b: &[u64]) -> Nat {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0u64;
    for (i, &x) in a.iter().enumerate() {
        let y = b.get(i).copied().unwrap_or(0);
        let (d, b1) = x.overflowing_sub(y);
        let (d, b2) = d.overflowing_sub(borrow);
        out.push(d);
        borrow = u64::from(b1 | b2);
    }
    debug_assert_eq!(borrow, 0);
    nat_trim(out)
}

fn nat_mul(a: &[u64], b: &[u64]) -> Nat {
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = u128::from(x) * u128::from(y) + u128::from(out[i + j]) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    nat_trim(out)
}

fn nat_shl(a: &[u64], k: usize) -> Nat {
    let (w, s) = (k / 64, k % 64);
    let mut out = vec![0u64; a.len() + w + 1];
    for (i, &x) in a.iter().enumerate() {
        out[i + w] |= x << s;
        if s != 0 {
            out[i + w + 1] |= x >> (64 - s);
        }
    }
    nat_trim(out)
}

/// Quotient and remainder by a nonzero `d`, bit by bit.
fn nat_divrem(a: &[u64], d: &[u64]) -> (Nat, Nat) {
    let bits = nat_bitlen(a);
    let mut q = vec![0u64; a.len()];
    let mut r: Nat = Vec::new();
    for i in (0..bits).rev() {
        r = nat_shl(&r, 1);
        if nat_bit(a, i) == 1 {
            if r.is_empty() {
                r.push(1);
            } else {
                r[0] |= 1;
            }
        }
        if nat_cmp(&r, d) != Ordering::Less {
            r = nat_sub(&r, d);
            q[i / 64] |= 1 << (i % 64);
        }
    }
    (nat_trim(q), r)
}

fn nat_mulmod(a: &[u64], b: &[u64], p: &[u64]) -> Nat {
    nat_divrem(&nat_mul(a, b), p).1
}

/// `a^-1 mod p` for a prime `p` and `a != 0 mod p`.
fn nat_invmod(a: &[u64], p: &[u64]) -> Nat {
    let e = nat_sub(p, &[2]);
    let mut acc: Nat = vec![1];
    for i in (0..nat_bitlen(&e)).rev() {
        acc = nat_mulmod(&acc, &acc, p);
        if nat_bit(&e, i) == 1 {
            acc = nat_mulmod(&acc, a, p);
        }
    }
    acc
}

/// `acc += v 2^(8 byte_pos)` modulo `2^(64 acc.len())`.
fn nat_add_signed(acc: &mut [u64], v: i128, byte_pos: usize) {
    let (neg, mag) = (v < 0, v.unsigned_abs());
    let (w, s) = (byte_pos / 8, 8 * (byte_pos % 8));
    let (lo, hi) = (mag as u64, (mag >> 64) as u64);
    let words = if s == 0 {
        [lo, hi, 0]
    } else {
        [lo << s, (lo >> (64 - s)) | (hi << s), hi >> (64 - s)]
    };
    let mut carry = 0u64;
    for (k, slot) in acc.iter_mut().enumerate().skip(w) {
        let add = words.get(k - w).copied().unwrap_or(0);
        if neg {
            let (d, b1) = slot.overflowing_sub(add);
            let (d, b2) = d.overflowing_sub(carry);
            *slot = d;
            carry = u64::from(b1 | b2);
        } else {
            let (d, c1) = slot.overflowing_add(add);
            let (d, c2) = d.overflowing_add(carry);
            *slot = d;
            carry = u64::from(c1 | c2);
        }
        if k - w >= 3 && carry == 0 {
            break;
        }
    }
}

fn f_signed(v: i128) -> F {
    let m = F::from_u64_reduced((v.unsigned_abs() % 0xFFFF_FFFF_0000_0001u128) as u64);
    if v < 0 { F::ZERO - m } else { m }
}

fn pow2(i: usize) -> F {
    F::TWO.pow(i as u64)
}

/// The square root of a nonzero square, the same one for every caller (Tonelli-Shanks;
/// `p - 1 = 2^32 (2^32 - 1)` and 7 generates the multiplicative group). `None` for a
/// value that is not a square.
fn sqrt(v: F) -> Option<F> {
    const Q: u64 = (1 << 32) - 1;
    let mut x = v.pow(Q.div_ceil(2));
    let mut t = v.pow(Q);
    let mut c = F::from_u64_reduced(7).pow(Q);
    let mut m = 32;
    while t != F::ONE {
        let (mut i, mut tt) = (0, t);
        while tt != F::ONE {
            tt = tt * tt;
            i += 1;
            if i == m {
                return None;
            }
        }
        let mut b = c;
        for _ in 0..m - i - 1 {
            b = b * b;
        }
        x *= b;
        c = b * b;
        t *= c;
        m = i;
    }
    Some(x)
}

/// Row `k`, column `j`: coefficient `k` of the Lagrange polynomial of point `j` among the
/// points `0, .., n - 1`.
fn interpolation_matrix(n: usize) -> Vec<Vec<F>> {
    let pt = |j: usize| F::from_u64_reduced(j as u64);
    // master(t) = prod (t - j)
    let mut master = vec![F::ONE];
    for j in 0..n {
        let mut next = vec![F::ZERO; master.len() + 1];
        for (k, &c) in master.iter().enumerate() {
            next[k + 1] += c;
            next[k] -= c * pt(j);
        }
        master = next;
    }
    let mut out = vec![vec![F::ZERO; n]; n];
    for j in 0..n {
        // quotient = master / (t - j), by synthetic division from the top.
        let mut quotient = vec![F::ZERO; n];
        let mut carry = F::ZERO;
        for k in (0..n).rev() {
            carry = master[k + 1] + carry * pt(j);
            quotient[k] = carry;
        }
        let at = quotient
            .iter()
            .rev()
            .fold(F::ZERO, |acc, &c| acc * pt(j) + c);
        let inv = at.inv();
        for (row, &q) in out.iter_mut().zip(&quotient) {
            row[j] = q * inv;
        }
    }
    out
}

// ============================================================================
// Shared integers
// ============================================================================

/// An integer `sum_k c_k 2^(8k)` with shared coefficients in public intervals.
struct Int<S> {
    c: Vec<S>,
    lo: Vec<i128>,
    hi: Vec<i128>,
}

impl<S: Copy> Int<S> {
    fn len(&self) -> usize {
        self.c.len()
    }
}

const COEF_BOUND: i128 = 1 << 62;

/// A public prime modulus.
struct Modulus {
    p: Nat,
    bits: usize,
    limbs: usize,
    /// `p = sum digit 2^(8 position)` with digits in `[-128, 127]`.
    digits: Vec<(usize, i64)>,
}

impl Modulus {
    fn new(bytes_le: &[u8]) -> Self {
        let p = nat_from_le(bytes_le);
        let mut digits = Vec::new();
        let mut carry = 0i64;
        for (k, &b) in bytes_le.iter().enumerate() {
            let mut d = i64::from(b) + carry;
            carry = 0;
            if d > 127 {
                d -= 256;
                carry = 1;
            }
            if d != 0 {
                digits.push((k, d));
            }
        }
        if carry != 0 {
            digits.push((bytes_le.len(), carry));
        }
        Self {
            bits: nat_bitlen(&p),
            limbs: bytes_le.len(),
            p,
            digits,
        }
    }
}

/// How the carries of a chain `c_{i+1} = g_i + p_i c_i` are computed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Chains {
    /// One product and one round per position.
    Ripple,
    /// A Brent-Kung prefix network: about three products per position and
    /// `2 log2(n)` rounds.
    Prefix,
    /// [`Chains::Ripple`] for the borrow chain of a statistically masked decomposition
    /// (at most 22 positions), [`Chains::Prefix`] everywhere else.
    Mixed,
}

/// The chains [`generate`] and [`demand`] use.
pub const CHAINS: Chains = Chains::Mixed;

/// Requests of the round being collected, and the results of the round before it.
struct Queue<S: SecretWipe + Copy> {
    round: u64,
    xs: SecretScratch<S>,
    ys: SecretScratch<S>,
    opens: SecretScratch<S>,
    checked: bool,
    products: SecretScratch<S>,
    opened: Vec<F>,
}

/// Ready on its second poll.
struct NextRound(bool);

impl Future for NextRound {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

type Boxed<'f, T> = Pin<Box<dyn Future<Output = T> + 'f>>;

/// Both results, with the two futures advancing in the same rounds.
async fn join2<A, C>(a: impl Future<Output = A>, c: impl Future<Output = C>) -> (A, C) {
    let (mut a, mut c) = (Box::pin(a), Box::pin(c));
    let (mut ra, mut rc) = (None, None);
    poll_fn(move |cx| {
        if ra.is_none()
            && let Poll::Ready(v) = a.as_mut().poll(cx)
        {
            ra = Some(v);
        }
        if rc.is_none()
            && let Poll::Ready(v) = c.as_mut().poll(cx)
        {
            rc = Some(v);
        }
        if ra.is_some() && rc.is_some() {
            Poll::Ready((ra.take().expect("set"), rc.take().expect("set")))
        } else {
            Poll::Pending
        }
    })
    .await
}

/// Every result, in order, with all futures advancing in the same rounds.
async fn join_all<T>(mut futures: Vec<Boxed<'_, T>>) -> Vec<T> {
    let mut out: Vec<Option<T>> = futures.iter().map(|_| None).collect();
    poll_fn(move |cx| {
        let mut waiting = false;
        for (f, slot) in futures.iter_mut().zip(out.iter_mut()) {
            if slot.is_none() {
                match f.as_mut().poll(cx) {
                    Poll::Ready(v) => *slot = Some(v),
                    Poll::Pending => waiting = true,
                }
            }
        }
        if waiting {
            Poll::Pending
        } else {
            Poll::Ready(out.iter_mut().map(|v| v.take().expect("set")).collect())
        }
    })
    .await
}

/// One custodian's (or the counter's) run of witness generation.
///
/// The subprotocols are `async`: each awaits the products and openings it asks for, and
/// a round of the backend carries the requests of every subprotocol that is waiting.
/// [`Witgen::run`] drives a whole relation; [`Witgen::wait`] drives one subprotocol.
pub struct Witgen<'a, B: Backend> {
    b: RefCell<&'a mut B>,
    q: RefCell<Queue<B::S>>,
    matrices: RefCell<BTreeMap<usize, Rc<Vec<Vec<F>>>>>,
    unchecked: Cell<usize>,
    chains: Chains,
    counting: bool,
    /// Random bits and exact masks made before the relation's first round.
    pool: RefCell<Pool<B::S>>,
    /// Random bits and exact masks asked for so far.
    asked: Cell<(usize, usize)>,
    /// A run that only counts what [`Self::asked`] comes to.
    planning: bool,
    zero: B::S,
    one: B::S,
}

type Shares<B> = Result<Vec<<B as Backend>::S>, WitgenError>;
/// Random bits, and exact masks of 64 bits each.
type Pool<S> = (SecretBuffer<Vec<S>>, SecretBuffer<Vec<Vec<S>>>);
/// What a unit's dependencies are reported to: the terms of each form it reads.
type Visit<'v> = dyn FnMut(&[(u32, F)]) + 'v;
/// Two integers to be multiplied.
type IntPair<S> = (Int<S>, Int<S>);

impl<'a, B: Backend> Witgen<'a, B> {
    pub fn new(b: &'a mut B) -> Self {
        Self::with_chains(b, CHAINS)
    }

    pub fn with_chains(b: &'a mut B, chains: Chains) -> Self {
        let (zero, one, counting) = (b.public(F::ZERO), b.public(F::ONE), b.counting());
        Self {
            b: RefCell::new(b),
            q: RefCell::new(Queue {
                round: 0,
                xs: SecretScratch::new(),
                ys: SecretScratch::new(),
                opens: SecretScratch::new(),
                checked: false,
                products: SecretScratch::new(),
                opened: Vec::new(),
            }),
            matrices: RefCell::new(BTreeMap::new()),
            unchecked: Cell::new(0),
            chains,
            counting,
            pool: RefCell::new((SecretBuffer(Vec::new()), SecretBuffer(Vec::new()))),
            asked: Cell::new((0, 0)),
            planning: false,
            zero,
            one,
        }
    }

    fn public(&self, c: F) -> B::S {
        self.b.borrow().public(c)
    }

    fn random(&self) -> Result<B::S, WitgenError> {
        Ok(self.b.borrow_mut().random()?)
    }

    fn check(&self) -> Result<(), WitgenError> {
        self.unchecked.set(0);
        Ok(self.b.borrow_mut().check()?)
    }

    /// Queue products for the next round; their place in its results.
    fn push_mul(&self, xs: &[B::S], ys: &[B::S]) -> usize {
        assert_eq!(xs.len(), ys.len());
        let mut q = self.q.borrow_mut();
        let at = q.xs.len();
        q.xs.extend_from_slice(xs);
        q.ys.extend_from_slice(ys);
        at
    }

    async fn mul(&self, xs: &[B::S], ys: &[B::S]) -> Shares<B> {
        if xs.is_empty() {
            return Ok(Vec::new());
        }
        let at = self.push_mul(xs, ys);
        NextRound(false).await;
        Ok(self.q.borrow().products[at..at + xs.len()].to_vec())
    }

    async fn mul1(&self, x: B::S, y: B::S) -> Result<B::S, WitgenError> {
        Ok(self.mul(&[x], &[y]).await?[0])
    }

    /// Open values. With `checked`, the batch MAC check runs before the round that
    /// opens them: for values that are masked only if every earlier opening was right.
    async fn open(&self, xs: &[B::S], checked: bool) -> Result<Vec<F>, WitgenError> {
        if xs.is_empty() {
            return Ok(Vec::new());
        }
        let at = {
            let mut q = self.q.borrow_mut();
            let at = q.opens.len();
            q.opens.extend_from_slice(xs);
            q.checked |= checked;
            at
        };
        NextRound(false).await;
        Ok(self.q.borrow().opened[at..at + xs.len()].to_vec())
    }

    fn idle(&self) -> bool {
        let q = self.q.borrow();
        q.xs.is_empty() && q.opens.is_empty()
    }

    /// Run the round that was collected.
    fn step(&self) -> Result<(), WitgenError> {
        let mut q = self.q.borrow_mut();
        let opened = 2 * q.xs.len() + q.opens.len();
        if q.checked || (self.unchecked.get() > 0 && self.unchecked.get() + opened > CHECK_EVERY) {
            self.check()?;
        }
        let (products, values) = self.b.borrow_mut().round(&q.xs, &q.ys, &q.opens)?;
        q.products = SecretScratch::from(products);
        q.opened = values;
        q.xs.clear();
        q.ys.clear();
        q.opens.clear();
        q.checked = false;
        q.round += 1;
        self.unchecked.set(self.unchecked.get() + opened);
        Ok(())
    }

    /// Drive one subprotocol to its result.
    pub fn wait<T>(
        &self,
        future: impl Future<Output = Result<T, WitgenError>>,
    ) -> Result<T, WitgenError> {
        let mut future = core::pin::pin!(future);
        let mut cx = Context::from_waker(Waker::noop());
        loop {
            if let Poll::Ready(out) = future.as_mut().poll(&mut cx) {
                return out;
            }
            if self.idle() {
                return Err(WitgenError::Unsupported { index: usize::MAX });
            }
            self.step()?;
        }
    }

    fn eval(&self, z: &[B::S], lc: &Lc) -> B::S {
        lc.terms()
            .iter()
            .fold(self.zero, |acc, &(v, c)| acc + B::scale(z[v as usize], c))
    }

    /// Shared uniform bits: from the pool when it has them, else made now.
    pub async fn random_bits(&self, n: usize) -> Shares<B> {
        let asked = self.asked.get();
        self.asked.set((asked.0 + n, asked.1));
        {
            let bits = &mut self.pool.borrow_mut().0;
            if bits.len() >= n && n > 0 {
                let at = bits.len() - n;
                return Ok(bits.split_off(at));
            }
        }
        self.fresh_bits(n).await
    }

    /// Shared uniform bits, two rounds.
    async fn fresh_bits(&self, n: usize) -> Shares<B> {
        let half = F::TWO.inv();
        let mut out = SecretBuffer(Vec::with_capacity(n));
        while out.len() < n {
            let a: SecretScratch<B::S> = (0..n - out.len())
                .map(|_| self.random())
                .collect::<Result<_, _>>()?;
            let squares = SecretScratch::from(self.mul(&a, &a).await?);
            let opened = self.open(&squares, true).await?;
            for (&a, &v) in a.iter().zip(&opened) {
                if self.counting {
                    out.push(a);
                } else if v != F::ZERO {
                    let Some(root) = sqrt(v) else {
                        // The square of a shared value was opened as a non-square: some
                        // opening was wrong. The check names it; the value opened
                        // depends on preprocessed values only.
                        self.check()?;
                        return Err(WitgenError::NotABit);
                    };
                    out.push(B::scale(a, root.inv() * half) + self.public(half));
                }
            }
        }
        Ok(out.into_inner())
    }

    /// The products of every prefix of `first, ps[0], ps[1], ..` that has at least two
    /// factors: `first ps[0]`, `first ps[0] ps[1]`, and so on.
    async fn running_products(&self, first: B::S, ps: &[B::S]) -> Shares<B> {
        match self.chains {
            Chains::Ripple => {
                let mut out = Vec::with_capacity(ps.len());
                let mut acc = first;
                for &p in ps {
                    acc = self.mul1(acc, p).await?;
                    out.push(acc);
                }
                Ok(out)
            }
            Chains::Prefix | Chains::Mixed => {
                let mut v = Vec::with_capacity(ps.len() + 1);
                v.push(first);
                v.extend_from_slice(ps);
                let n = v.len();
                let mut d = 1;
                while d < n {
                    let at: Vec<usize> = (2 * d - 1..n).step_by(2 * d).collect();
                    let xs: Vec<B::S> = at.iter().map(|&i| v[i]).collect();
                    let ys: Vec<B::S> = at.iter().map(|&i| v[i - d]).collect();
                    for (&i, &r) in at.iter().zip(&self.mul(&xs, &ys).await?) {
                        v[i] = r;
                    }
                    d *= 2;
                }
                while d > 1 {
                    d /= 2;
                    let at: Vec<usize> = (3 * d - 1..n).step_by(2 * d).collect();
                    let xs: Vec<B::S> = at.iter().map(|&i| v[i]).collect();
                    let ys: Vec<B::S> = at.iter().map(|&i| v[i - d]).collect();
                    for (&i, &r) in at.iter().zip(&self.mul(&xs, &ys).await?) {
                        v[i] = r;
                    }
                }
                v.remove(0);
                Ok(v)
            }
        }
    }

    /// The carries `c_1, .., c_n` of the chain `c_{i+1} = g_i + p_i c_i`, `c_0 = 0`, for
    /// positions where `g_i` and `p_i` are bits that are not both one.
    async fn carries(&self, mut g: Vec<B::S>, mut p: Vec<B::S>, short: bool) -> Shares<B> {
        let n = g.len();
        let ripple = match self.chains {
            Chains::Ripple => true,
            Chains::Prefix => false,
            Chains::Mixed => short,
        };
        match ripple {
            true => {
                for i in 1..n {
                    g[i] = g[i] + self.mul1(p[i], g[i - 1]).await?;
                }
            }
            false => {
                // Up: position `i` comes to hold its block of `2 d` positions. A block
                // that starts at zero needs no propagate.
                let mut d = 1;
                while d < n {
                    let at: Vec<usize> = (2 * d - 1..n).step_by(2 * d).collect();
                    let mut xs: Vec<B::S> = at.iter().map(|&i| p[i]).collect();
                    let mut ys: Vec<B::S> = at.iter().map(|&i| g[i - d]).collect();
                    let wide: Vec<usize> = at.iter().copied().filter(|&i| i != 2 * d - 1).collect();
                    xs.extend(wide.iter().map(|&i| p[i]));
                    ys.extend(wide.iter().map(|&i| p[i - d]));
                    let r = self.mul(&xs, &ys).await?;
                    for (k, &i) in at.iter().enumerate() {
                        g[i] = g[i] + r[k];
                    }
                    for (k, &i) in wide.iter().enumerate() {
                        p[i] = r[at.len() + k];
                    }
                    d *= 2;
                }
                // Down: a block after a finished prefix.
                while d > 1 {
                    d /= 2;
                    let at: Vec<usize> = (3 * d - 1..n).step_by(2 * d).collect();
                    let xs: Vec<B::S> = at.iter().map(|&i| p[i]).collect();
                    let ys: Vec<B::S> = at.iter().map(|&i| g[i - d]).collect();
                    for (&i, &r) in at.iter().zip(&self.mul(&xs, &ys).await?) {
                        g[i] = g[i] + r;
                    }
                }
            }
        }
        Ok(g)
    }

    /// 64 shared random bits whose value is at most `p - 2`: from the pool when it has
    /// one, else made now.
    async fn exact_mask(&self) -> Shares<B> {
        let asked = self.asked.get();
        self.asked.set((asked.0, asked.1 + 1));
        if let Some(mask) = self.pool.borrow_mut().1.pop() {
            return Ok(mask);
        }
        self.fresh_mask().await
    }

    /// 64 shared random bits whose value is at most `p - 2`, eight rounds.
    async fn fresh_mask(&self) -> Shares<B> {
        loop {
            let bits = self.fresh_bits(64).await?;
            let mut level: Vec<B::S> = bits[32..].to_vec();
            while level.len() > 1 {
                let (xs, ys): (Vec<B::S>, Vec<B::S>) =
                    level.chunks_exact(2).map(|p| (p[0], p[1])).unzip();
                level = self.mul(&xs, &ys).await?;
            }
            let all_ones = self.open(&level, true).await?[0];
            if self.counting || all_ones == F::ZERO {
                return Ok(bits);
            }
        }
    }

    /// Fill the pool: the masks of a relation do not depend on its values, so all of
    /// them are made in its first eight rounds.
    async fn fill_pool(&self, bits: usize, masks: usize) -> Result<(), WitgenError> {
        let futures: Vec<Boxed<'_, Shares<B>>> = (0..masks)
            .map(|_| Box::pin(self.fresh_mask()) as Boxed<'_, _>)
            .collect();
        let (bits, masks) = join2(self.fresh_bits(bits), join_all(futures)).await;
        let bits = bits.map(SecretBuffer);
        let guarded: Vec<_> = masks
            .into_iter()
            .map(|result| result.map(SecretBuffer))
            .collect();
        let masks = guarded.into_iter().collect::<Result<Vec<_>, _>>()?;
        *self.pool.borrow_mut() = (
            bits?,
            SecretBuffer(masks.into_iter().map(SecretBuffer::into_inner).collect()),
        );
        Ok(())
    }

    /// `(c - r) mod 2^len` for the public `c` and shared bits `r`, with the final borrow.
    async fn sub_from_public(
        &self,
        c: u64,
        r: &[B::S],
        len: usize,
        short: bool,
    ) -> Result<(Vec<B::S>, B::S), WitgenError> {
        // Borrow out of a position: `r` and the borrow in where `c` has a one, `r` or
        // the borrow in where it has a zero.
        let bit = |i: usize| (c >> i) & 1 == 1;
        let g: Vec<B::S> = (0..len)
            .map(|i| if bit(i) { self.zero } else { r[i] })
            .collect();
        let p: Vec<B::S> = (0..len)
            .map(|i| if bit(i) { r[i] } else { self.one - r[i] })
            .collect();
        let borrows = self.carries(g, p, short).await?;
        let two = F::TWO;
        let out = (0..len)
            .map(|i| {
                let before = if i == 0 { self.zero } else { borrows[i - 1] };
                self.public(F::from_u64_reduced(u64::from(bit(i)))) - r[i] - before
                    + B::scale(borrows[i], two)
            })
            .collect();
        Ok((out, borrows[len - 1]))
    }

    /// The bits of `x`, which lies in `[0, 2^m)` and is below the field prime; `m <= 64`.
    pub async fn decompose(&self, x: B::S, m: u32) -> Shares<B> {
        assert!(m <= 64);
        let m = m as usize;
        if m == 0 {
            return Ok(Vec::new());
        }
        let pack = |bits: &[B::S]| {
            bits.iter()
                .enumerate()
                .fold(x, |acc, (i, &b)| acc + B::scale(b, pow2(i)))
        };
        if m as u32 <= STAT_MAX {
            let r = self.random_bits(m + SIGMA as usize).await?;
            let c = self.open(&[pack(&r)], true).await?[0].to_canonical_u64();
            return Ok(self.sub_from_public(c, &r, m, true).await?.0);
        }
        let r = SecretBuffer::new(self.exact_mask().await?);
        let c = self.open(&[pack(&r)], true).await?[0].to_canonical_u64();
        self.subtract_mask(c, &r, m).await
    }

    async fn subtract_mask(&self, c: u64, r: &[B::S], m: usize) -> Shares<B> {
        let (d, beta) = self.sub_from_public(c, r, 64, false).await?;
        // x = D + beta - 2^32 beta: a carry `beta` into the low 32 bits, then a borrow of
        // `beta` minus the carry out of them into the bits above.
        let low = m.min(32);
        let carries = self.running_products(beta, &d[..low]).await?;
        let mut out = Vec::with_capacity(m);
        let mut carry = beta;
        for (&di, &next) in d.iter().zip(&carries) {
            out.push(di + carry - B::scale(next, F::TWO));
            carry = next;
        }
        if m > 32 {
            let complements: Vec<B::S> = d[32..m].iter().map(|&di| self.one - di).collect();
            let first = beta - carry;
            let borrows = self.running_products(first, &complements).await?;
            let mut borrow = first;
            for (&di, &next) in d[32..m].iter().zip(&borrows) {
                // d - borrow = out - 2 (borrow out), and the borrow out is
                // `borrow (1 - d)`.
                out.push(di - borrow + B::scale(next, F::TWO));
                borrow = next;
            }
        }
        Ok(out)
    }

    // Rejection samples a mask uniformly in [0,p), including p-1. Only the
    // rejection bit leaves the computation. Revealing the high product alone
    // would identify the unique accepted mask having its top 32 bits set.
    async fn uniform_decomposition(&self, x: B::S) -> Shares<B> {
        loop {
            let bits = SecretBuffer::new(self.fresh_bits(64).await?);
            let mut level = SecretBuffer::new(
                bits.iter()
                    .enumerate()
                    .map(|(j, &b)| if j < 32 { self.one - b } else { b })
                    .collect::<Vec<_>>(),
            );
            while level.len() > 2 {
                let xs = SecretBuffer::new(level.iter().step_by(2).copied().collect::<Vec<_>>());
                let ys =
                    SecretBuffer::new(level.iter().skip(1).step_by(2).copied().collect::<Vec<_>>());
                level = SecretBuffer::new(self.mul(&xs, &ys).await?);
            }
            let reject = self.mul1(self.one - level[0], level[1]).await?;
            if self.open(&[reject], true).await?[0] != F::ZERO {
                continue;
            }
            let masked = bits
                .iter()
                .enumerate()
                .fold(x, |s, (i, &b)| s + B::scale(b, pow2(i)));
            let c = self.open(&[masked], true).await?[0].to_canonical_u64();
            return self.subtract_mask(c, &bits, 64).await;
        }
    }

    /// Jointly decompose a batch of full-width residues and settle the MAC
    /// checks before returning their least-significant-first bit shares.
    pub(super) fn canonical_bits(
        &self,
        xs: &[B::S],
    ) -> Result<SecretBuffer<Vec<Vec<B::S>>>, WitgenError> {
        let tasks: Vec<Boxed<'_, Shares<B>>> = xs
            .iter()
            .map(|&x| Box::pin(self.uniform_decomposition(x)) as Boxed<'_, _>)
            .collect();
        let results = self.wait(async { Ok(join_all(tasks).await) })?;
        let mut bits = SecretBuffer::new(Vec::with_capacity(xs.len()));
        let guarded: Vec<_> = results
            .into_iter()
            .map(|r| r.map(SecretBuffer::new))
            .collect();
        for row in guarded {
            bits.push(row?.into_inner());
        }
        self.check()?;
        Ok(bits)
    }

    fn matrix(&self, n: usize) -> Rc<Vec<Vec<F>>> {
        self.matrices
            .borrow_mut()
            .entry(n)
            .or_insert_with(|| Rc::new(interpolation_matrix(n)))
            .clone()
    }

    /// Coefficients of the product of two polynomials, one secure product each.
    pub async fn poly_mul(&self, a: &[B::S], b: &[B::S]) -> Shares<B> {
        let n = a.len() + b.len() - 1;
        let at = |poly: &[B::S], s: usize| {
            let s = F::from_u64_reduced(s as u64);
            poly.iter()
                .rev()
                .fold(self.zero, |acc, &c| B::scale(acc, s) + c)
        };
        let xs: Vec<B::S> = (0..n).map(|s| at(a, s)).collect();
        let ys: Vec<B::S> = (0..n).map(|s| at(b, s)).collect();
        let values = self.mul(&xs, &ys).await?;
        let matrix = self.matrix(n);
        Ok(matrix
            .iter()
            .map(|row| {
                row.iter()
                    .zip(&values)
                    .fold(self.zero, |acc, (&k, &v)| acc + B::scale(v, k))
            })
            .collect())
    }

    fn int_of(&self, z: &[B::S], coefs: &[IntCoef]) -> Int<B::S> {
        Int {
            c: coefs.iter().map(|c| self.eval(z, &c.lc)).collect(),
            lo: coefs.iter().map(|c| c.lo).collect(),
            hi: coefs.iter().map(|c| c.hi).collect(),
        }
    }

    fn int_of_bits(&self, bits: &[B::S]) -> Int<B::S> {
        let c: Vec<B::S> = bits
            .chunks(8)
            .map(|limb| {
                limb.iter()
                    .enumerate()
                    .fold(self.zero, |acc, (t, &b)| acc + B::scale(b, pow2(t)))
            })
            .collect();
        Int {
            lo: vec![0; c.len()],
            hi: bits.chunks(8).map(|l| (1i128 << l.len()) - 1).collect(),
            c,
        }
    }

    fn int_add(&self, a: &Int<B::S>, b: &Int<B::S>) -> Int<B::S> {
        let n = a.len().max(b.len());
        let get = |x: &Int<B::S>, k: usize| match x.c.get(k) {
            Some(&c) => (c, x.lo[k], x.hi[k]),
            None => (self.zero, 0, 0),
        };
        let mut out = Int {
            c: Vec::with_capacity(n),
            lo: Vec::with_capacity(n),
            hi: Vec::with_capacity(n),
        };
        for k in 0..n {
            let (x, y) = (get(a, k), get(b, k));
            out.c.push(x.0 + y.0);
            out.lo.push(x.1 + y.1);
            out.hi.push(x.2 + y.2);
        }
        out
    }

    async fn int_mul(&self, a: &Int<B::S>, b: &Int<B::S>) -> Result<Int<B::S>, WitgenError> {
        let wide = WitgenError::Unsupported { index: usize::MAX };
        let n = a.len() + b.len() - 1;
        let (mut lo, mut hi) = (vec![0i128; n], vec![0i128; n]);
        for i in 0..a.len() {
            for j in 0..b.len() {
                let corners = [
                    a.lo[i].checked_mul(b.lo[j]),
                    a.lo[i].checked_mul(b.hi[j]),
                    a.hi[i].checked_mul(b.lo[j]),
                    a.hi[i].checked_mul(b.hi[j]),
                ];
                let mut least = i128::MAX;
                let mut most = i128::MIN;
                for c in corners {
                    let c = c.ok_or(wide)?;
                    least = least.min(c);
                    most = most.max(c);
                }
                lo[i + j] = lo[i + j].checked_add(least).ok_or(wide)?;
                hi[i + j] = hi[i + j].checked_add(most).ok_or(wide)?;
            }
        }
        if lo.iter().any(|&v| v <= -COEF_BOUND) || hi.iter().any(|&v| v >= COEF_BOUND) {
            return Err(wide);
        }
        Ok(Int {
            c: self.poly_mul(&a.c, &b.c).await?,
            lo,
            hi,
        })
    }

    /// `sum_j a_j b_j + linear`, the products in one round.
    async fn int_sum(
        &self,
        products: &[IntPair<B::S>],
        linear: Int<B::S>,
    ) -> Result<Int<B::S>, WitgenError> {
        let futures: Vec<Boxed<'_, _>> = products
            .iter()
            .map(|(a, b)| Box::pin(self.int_mul(a, b)) as Boxed<'_, _>)
            .collect();
        let mut acc = linear;
        for product in join_all(futures).await {
            acc = self.int_add(&acc, &product?);
        }
        Ok(acc)
    }

    fn int_pairs(
        &self,
        z: &[B::S],
        products: &[(Vec<IntCoef>, Vec<IntCoef>)],
    ) -> Vec<IntPair<B::S>> {
        products
            .iter()
            .map(|(a, b)| (self.int_of(z, a), self.int_of(z, b)))
            .collect()
    }

    /// The least `K` with `x + K q >= 0` over the intervals (as `K q`), and the largest
    /// value `x + K q` can take.
    fn lift(x: &Int<B::S>, q: &Modulus) -> (Nat, Nat) {
        let words = x.len() / 8 + 4;
        let (mut neg, mut pos) = (vec![0u64; words], vec![0u64; words]);
        for k in 0..x.len() {
            nat_add_signed(&mut neg, (-x.lo[k]).max(0), k);
            nat_add_signed(&mut pos, x.hi[k].max(0), k);
        }
        let (quotient, rest) = nat_divrem(&neg, &q.p);
        let k = if rest.is_empty() {
            quotient
        } else {
            nat_add(&quotient, &[1])
        };
        let kq = nat_mul(&k, &q.p);
        let most = nat_add(&nat_trim(pos), &kq);
        (kq, most)
    }

    /// The low `out_bits` bits of the integer `x + add`, which is non-negative.
    ///
    /// Every coefficient, shifted to be non-negative and with its digit of the constant,
    /// is decomposed on its own. The bits of neighbouring coefficients overlap; full
    /// adders bring every position down to two bits and one carry chain adds those.
    async fn normalize(&self, x: &Int<B::S>, add: &[u64], out_bits: usize) -> Shares<B> {
        let limbs = out_bits.div_ceil(8);
        let width = 8 * limbs;
        let mut constant = vec![0u64; limbs / 8 + 4];
        for (slot, &w) in constant.iter_mut().zip(add) {
            *slot = w;
        }
        let shared = x.len().min(limbs);
        for k in 0..shared {
            nat_add_signed(&mut constant, x.lo[k], k);
        }
        let mut futures: Vec<Boxed<'_, Shares<B>>> = Vec::with_capacity(shared);
        for k in 0..shared {
            let digit = nat_byte(&constant, k);
            let most = (x.hi[k] - x.lo[k]) as u128 + 255;
            if most >= 1 << 63 {
                return Err(WitgenError::Unsupported { index: usize::MAX });
            }
            let t =
                x.c[k] - self.public(f_signed(x.lo[k])) + self.public(F::from_u64_reduced(digit));
            futures.push(Box::pin(self.decompose(t, 128 - most.leading_zeros())));
        }
        let mut columns: Vec<Vec<B::S>> = vec![Vec::new(); width];
        for (k, bits) in join_all(futures).await.into_iter().enumerate() {
            for (j, &bit) in bits?.iter().enumerate() {
                if let Some(column) = columns.get_mut(8 * k + j) {
                    column.push(bit);
                }
            }
        }
        for (i, column) in columns.iter_mut().enumerate().skip(8 * shared) {
            if nat_bit(&constant, i) == 1 {
                column.push(self.one);
            }
        }
        // Full adders, three bits of a position to one there and one above.
        while columns.iter().any(|c| c.len() > 2) {
            let mut triples = Vec::new();
            let mut next: Vec<Vec<B::S>> = vec![Vec::new(); width];
            for (i, column) in columns.iter().enumerate() {
                let whole = column.len() / 3 * 3;
                for t in column[..whole].chunks_exact(3) {
                    triples.push((i, t[0], t[1], t[2]));
                }
                next[i].extend_from_slice(&column[whole..]);
            }
            let xs: Vec<B::S> = triples.iter().map(|t| t.1).collect();
            let ys: Vec<B::S> = triples.iter().map(|t| t.2).collect();
            let ab = self.mul(&xs, &ys).await?;
            let xor: Vec<B::S> = triples
                .iter()
                .zip(&ab)
                .map(|(t, &ab)| t.1 + t.2 - B::scale(ab, F::TWO))
                .collect();
            let cs: Vec<B::S> = triples.iter().map(|t| t.3).collect();
            let xc = self.mul(&xor, &cs).await?;
            for (k, t) in triples.iter().enumerate() {
                next[t.0].push(xor[k] + t.3 - B::scale(xc[k], F::TWO));
                if t.0 + 1 < width {
                    next[t.0 + 1].push(ab[k] + xc[k]);
                }
            }
            columns = next;
        }
        // Two rows. Below the first position with two bits there is nothing to add.
        let start = columns.iter().position(|c| c.len() == 2).unwrap_or(width);
        let mut out: Vec<B::S> = columns[..start]
            .iter()
            .map(|c| c.first().copied().unwrap_or(self.zero))
            .collect();
        if start < width {
            let rows = &columns[start..];
            let pairs: Vec<usize> = (0..rows.len()).filter(|&i| rows[i].len() == 2).collect();
            let xs: Vec<B::S> = pairs.iter().map(|&i| rows[i][0]).collect();
            let ys: Vec<B::S> = pairs.iter().map(|&i| rows[i][1]).collect();
            let both = self.mul(&xs, &ys).await?;
            let mut g = vec![self.zero; rows.len()];
            for (&i, &v) in pairs.iter().zip(&both) {
                g[i] = v;
            }
            let p: Vec<B::S> = rows
                .iter()
                .zip(&g)
                .map(|(row, &g)| {
                    row.iter().fold(self.zero, |acc, &b| acc + b) - B::scale(g, F::TWO)
                })
                .collect();
            let carries = self.carries(g.clone(), p.clone(), false).await?;
            for i in 0..rows.len() {
                let before = if i == 0 { self.zero } else { carries[i - 1] };
                // The sum bit is `p + carry in - 2 (p and carry in)`, and the carry out
                // is `g + (p and carry in)`.
                out.push(p[i] + before - B::scale(carries[i] - g[i], F::TWO));
            }
        }
        out.truncate(out_bits);
        Ok(out)
    }

    /// `bits >= c ? bits - c : bits` for the public `c`.
    async fn conditional_sub(&self, bits: &[B::S], c: &[u64]) -> Shares<B> {
        if nat_bitlen(c) > bits.len() {
            return Ok(bits.to_vec());
        }
        // Borrow out of a position: `not v` or the borrow in where `c` has a one,
        // `not v` and the borrow in where it has a zero.
        let g: Vec<B::S> = bits
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                if nat_bit(c, i) == 1 {
                    self.one - v
                } else {
                    self.zero
                }
            })
            .collect();
        let p: Vec<B::S> = bits
            .iter()
            .enumerate()
            .map(|(i, &v)| if nat_bit(c, i) == 1 { v } else { self.one - v })
            .collect();
        let borrows = self.carries(g, p, false).await?;
        let diff: Vec<B::S> = bits
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                let before = if i == 0 { self.zero } else { borrows[i - 1] };
                v - self.public(F::from_u64_reduced(nat_bit(c, i))) - before
                    + B::scale(borrows[i], F::TWO)
            })
            .collect();
        // A final borrow means `bits < c`: keep `bits`.
        let deltas: Vec<B::S> = bits.iter().zip(&diff).map(|(&v, &d)| v - d).collect();
        let keep = self
            .mul(&vec![borrows[bits.len() - 1]; bits.len()], &deltas)
            .await?;
        Ok(diff.iter().zip(&keep).map(|(&d, &k)| d + k).collect())
    }

    /// The canonical residue modulo `q` of the integer with the given bits and bound.
    async fn reduce_bits(
        &self,
        mut bits: Vec<B::S>,
        mut most: Nat,
        q: &Modulus,
        scale: Option<&[u64]>,
    ) -> Shares<B> {
        let base = 8 * q.limbs;
        let mut scale = scale.map(<[u64]>::to_vec);
        loop {
            // weights[i]: what bit `i` contributes, modulo q.
            let first = if scale.is_some() { 0 } else { base };
            if bits.len() <= first {
                break;
            }
            let mut weight = match &scale {
                Some(s) => nat_divrem(s, &q.p).1,
                None => nat_divrem(&nat_shl(&[1], base), &q.p).1,
            };
            let mut next_most: Nat = if scale.is_some() {
                Vec::new()
            } else {
                nat_sub(&nat_shl(&[1], base), &[1])
            };
            let kept = if scale.is_some() {
                0
            } else {
                base.min(bits.len())
            };
            let mut folded = self.int_of_bits(&bits[..kept]);
            folded.c.resize(q.limbs, self.zero);
            folded.lo.resize(q.limbs, 0);
            folded.hi.resize(q.limbs, 0);
            for &bit in &bits[first..] {
                for j in 0..q.limbs {
                    let byte = nat_byte(&weight, j);
                    if byte != 0 {
                        folded.c[j] = folded.c[j] + B::scale(bit, F::from_u64_reduced(byte));
                    }
                    // With an opened scale the weights are not known in advance; the
                    // widths then come from their bound, so that what is consumed does
                    // not depend on the opened value.
                    folded.hi[j] += if scale.is_some() {
                        255
                    } else {
                        i128::from(byte)
                    };
                }
                next_most = nat_add(&next_most, if scale.is_some() { &q.p } else { &weight });
                weight = nat_shl(&weight, 1);
                if nat_cmp(&weight, &q.p) != Ordering::Less {
                    weight = nat_sub(&weight, &q.p);
                }
            }
            if scale.is_none() && nat_bitlen(&next_most) >= bits.len() {
                break;
            }
            scale = None;
            bits = self.normalize(&folded, &[], nat_bitlen(&next_most)).await?;
            most = next_most;
        }
        let count = nat_divrem(&most, &q.p).0;
        for j in (0..nat_bitlen(&count)).rev() {
            bits = self.conditional_sub(&bits, &nat_shl(&q.p, j)).await?;
        }
        bits.resize(q.bits, self.zero);
        Ok(bits)
    }

    /// The bits of the non-negative lift of `x` by a multiple of `q`, and their bound.
    async fn lifted_bits(
        &self,
        x: &Int<B::S>,
        q: &Modulus,
    ) -> Result<(Vec<B::S>, Nat), WitgenError> {
        let (kq, most) = Self::lift(x, q);
        let bits = self.normalize(x, &kq, nat_bitlen(&most)).await?;
        Ok((bits, most))
    }

    /// The canonical residue of `x` modulo `q`, as bits.
    async fn canonical(&self, x: &Int<B::S>, q: &Modulus) -> Shares<B> {
        let (bits, most) = self.lifted_bits(x, q).await?;
        self.reduce_bits(bits, most, q, None).await
    }

    /// `x mod q`, opened. The integer that is opened is `x + (K + S) q` for a shared
    /// uniform `S` with [`SIGMA`] bits more than the quotient of `x` can have.
    async fn open_residue(&self, x: &Int<B::S>, q: &Modulus) -> Result<Nat, WitgenError> {
        let (_, most) = Self::lift(x, q);
        let quotient_bits = nat_bitlen(&nat_divrem(&most, &q.p).0) + 1;
        let s_bits = self.random_bits(quotient_bits + SIGMA as usize).await?;
        let s = self.int_of_bits(&s_bits);
        let mut qs = Int {
            c: vec![self.zero; s.len() + q.limbs + 1],
            lo: vec![0; s.len() + q.limbs + 1],
            hi: vec![0; s.len() + q.limbs + 1],
        };
        for &(pos, digit) in &q.digits {
            for k in 0..s.len() {
                let d = i128::from(digit);
                qs.c[k + pos] = qs.c[k + pos] + B::scale(s.c[k], f_signed(d));
                qs.lo[k + pos] += (d * s.hi[k]).min(0);
                qs.hi[k + pos] += (d * s.hi[k]).max(0);
            }
        }
        let masked = self.int_add(x, &qs);
        let (bits, _) = self.lifted_bits(&masked, q).await?;
        let opened = self.open(&bits, true).await?;
        let mut value = vec![0u64; opened.len() / 64 + 1];
        for (i, &v) in opened.iter().enumerate() {
            match v.to_canonical_u64() {
                0 => {}
                1 => value[i / 64] |= 1 << (i % 64),
                _ => return Err(WitgenError::NotABit),
            }
        }
        Ok(nat_divrem(&value, &q.p).1)
    }

    /// The canonical residue of `num / den` modulo `q`, as bits.
    async fn quotient_mod(&self, num: &Int<B::S>, den: &Int<B::S>, q: &Modulus) -> Shares<B> {
        let rho_bits = self.random_bits(q.bits + SIGMA as usize).await?;
        let rho = self.int_of_bits(&rho_bits);
        let (masked_den, masked_num) =
            join2(self.int_mul(den, &rho), self.int_mul(num, &rho)).await;
        let (masked_den, masked_num) = (masked_den?, masked_num?);
        let (w, lifted) = join2(
            self.open_residue(&masked_den, q),
            self.lifted_bits(&masked_num, q),
        )
        .await;
        let (w, (bits, most)) = (w?, lifted?);
        let inverse = if self.counting {
            vec![1]
        } else if w.is_empty() {
            return Err(WitgenError::ZeroDenominator);
        } else {
            nat_invmod(&w, &q.p)
        };
        self.reduce_bits(bits, most, q, Some(&inverse)).await
    }

    /// `flag ? on_one : on_zero`, coefficient by coefficient.
    async fn int_select(
        &self,
        flag: B::S,
        on_one: &Int<B::S>,
        on_zero: &Int<B::S>,
    ) -> Result<Int<B::S>, WitgenError> {
        let n = on_one.len().max(on_zero.len());
        let get = |x: &Int<B::S>, k: usize| match x.c.get(k) {
            Some(&c) => (c, x.lo[k], x.hi[k]),
            None => (self.zero, 0, 0),
        };
        let (ones, zeros): (Vec<_>, Vec<_>) =
            (0..n).map(|k| (get(on_one, k), get(on_zero, k))).unzip();
        let deltas: Vec<B::S> = ones.iter().zip(&zeros).map(|(a, b)| a.0 - b.0).collect();
        let moved = self.mul(&vec![flag; n], &deltas).await?;
        Ok(Int {
            c: zeros.iter().zip(&moved).map(|(z, &m)| z.0 + m).collect(),
            lo: ones.iter().zip(&zeros).map(|(a, b)| a.1.min(b.1)).collect(),
            hi: ones.iter().zip(&zeros).map(|(a, b)| a.2.max(b.2)).collect(),
        })
    }

    /// The canonical residue of `num / den` modulo `q` where `den` is not zero modulo
    /// `q`, and of `alt_num / alt_den` where it is. Which one is not revealed.
    async fn slope(
        &self,
        num: &Int<B::S>,
        den: &Int<B::S>,
        alt_num: &Int<B::S>,
        alt_den: &Int<B::S>,
        q: &Modulus,
    ) -> Shares<B> {
        // den = 0 mod q exactly when every bit of its canonical residue is zero.
        let mut level: Vec<B::S> = self
            .canonical(den, q)
            .await?
            .iter()
            .map(|&b| self.one - b)
            .collect();
        while level.len() > 1 {
            let odd = (level.len() % 2 == 1).then(|| level[level.len() - 1]);
            let (xs, ys): (Vec<B::S>, Vec<B::S>) =
                level.chunks_exact(2).map(|p| (p[0], p[1])).unzip();
            level = self.mul(&xs, &ys).await?;
            level.extend(odd);
        }
        let is_zero = level[0];
        let (num, den) = join2(
            self.int_select(is_zero, alt_num, num),
            self.int_select(is_zero, alt_den, den),
        )
        .await;
        self.quotient_mod(&num?, &den?, q).await
    }

    /// `N / q` for an integer `N` that `q` divides, with the quotient below `2^bits`.
    async fn exact_quotient(&self, num: &Int<B::S>, q: &Modulus, bits: usize) -> Shares<B> {
        if bits > 56 {
            return Err(WitgenError::Unsupported { index: usize::MAX });
        }
        let low = self.normalize(num, &[], bits).await?;
        // q^-1 mod 2^64 by Newton's iteration.
        let q0 = q.p[0];
        let mut inverse = q0;
        for _ in 0..6 {
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(q0.wrapping_mul(inverse)));
        }
        let mask = (1u64 << bits) - 1;
        let (mut sum, mut most) = (self.zero, 0u128);
        for (i, &bit) in low.iter().enumerate() {
            let weight = (inverse << i) & mask;
            sum = sum + B::scale(bit, F::from_u64_reduced(weight));
            most += u128::from(weight);
        }
        let mut out = self.decompose(sum, 128 - most.leading_zeros()).await?;
        out.resize(bits, self.zero);
        Ok(out)
    }

    /// The inverse of `x`, or zero; `x` lies in `[0, max]`.
    async fn inverse_or_zero(&self, x: B::S, max: usize) -> Result<B::S, WitgenError> {
        let mut powers = vec![self.one, x];
        while powers.len() <= max {
            let have = powers.len();
            let upto = (2 * have - 1).min(max + 1);
            let xs: Vec<B::S> = (have..upto).map(|k| powers[k / 2]).collect();
            let ys: Vec<B::S> = (have..upto).map(|k| powers[k - k / 2]).collect();
            powers.extend(self.mul(&xs, &ys).await?);
        }
        let matrix = self.matrix(max + 1);
        Ok((1..=max).fold(self.zero, |acc, k| {
            let coefficient = (1..=max).fold(F::ZERO, |c, j| {
                c + matrix[k][j] * F::from_u64_reduced(j as u64).inv()
            });
            acc + B::scale(powers[k], coefficient)
        }))
    }

    /// `scale (num / den - minus)` in the field, for a nonzero `den`.
    async fn ratio(&self, num: B::S, den: B::S, minus: B::S, scale: F) -> Shares<B> {
        let mask = self.random()?;
        let masked = self.mul(&[den, num], &[mask, mask]).await?;
        // A denominator can only be what the definitions say once every earlier opening
        // is known to be right.
        let opened = self.open(&masked[..1], true).await?[0];
        let inverse = if self.counting {
            F::ONE
        } else if opened == F::ZERO {
            return Err(WitgenError::ZeroDenominator);
        } else {
            opened.inv()
        };
        Ok(vec![
            B::scale(masked[1], inverse * scale) - B::scale(minus, scale),
        ])
    }

    /// The indicator of the value of `x` over `0..2^bits`: entry `j` is one where
    /// `x = j`. For an `x` outside that range the entries are not an indicator, and the
    /// relation has no proof.
    async fn one_hot(&self, x: B::S, bits: u32) -> Shares<B> {
        // Products of every subset of the bits, by halves: one round per doubling.
        let mut blocks: Vec<Vec<B::S>> = self
            .decompose(x, bits)
            .await?
            .iter()
            .map(|&b| vec![self.one, b])
            .collect();
        while blocks.len() > 1 {
            let (mut xs, mut ys) = (Vec::new(), Vec::new());
            for pair in blocks.chunks_exact(2) {
                for &h in &pair[1][1..] {
                    for &l in &pair[0][1..] {
                        xs.push(l);
                        ys.push(h);
                    }
                }
            }
            let products = self.mul(&xs, &ys).await?;
            let mut at = 0;
            let mut next = Vec::with_capacity(blocks.len().div_ceil(2));
            for pair in blocks.chunks(2) {
                let mut joined = pair[0].clone();
                if let Some(high) = pair.get(1) {
                    for &h in &high[1..] {
                        joined.push(h);
                        let n = pair[0].len() - 1;
                        joined.extend_from_slice(&products[at..at + n]);
                        at += n;
                    }
                }
                next.push(joined);
            }
            blocks = next;
        }
        // From subset products to the indicator: where a bit is zero the factor is
        // `1 - bit`.
        let mut out = blocks.pop().unwrap_or_else(|| vec![self.one]);
        for bit in 0..bits as usize {
            for mask in 0..out.len() {
                if (mask >> bit) & 1 == 0 {
                    out[mask] = out[mask] - out[mask | (1 << bit)];
                }
            }
        }
        Ok(out)
    }

    /// The task of a variable that is neither a product nor read from a source.
    fn var_task<'s>(&'s self, z: &[B::S], def: &Def) -> Option<Boxed<'s, Shares<B>>> {
        Some(match def {
            Def::Ratio {
                num,
                den,
                minus,
                scale,
            } => {
                let (n, d, m) = (self.eval(z, num), self.eval(z, den), self.eval(z, minus));
                Box::pin(self.ratio(n, d, m, *scale))
            }
            Def::SumOfProducts { base, products } => {
                let xs: Vec<B::S> = products.iter().map(|(a, _)| self.eval(z, a)).collect();
                let ys: Vec<B::S> = products.iter().map(|(_, b)| self.eval(z, b)).collect();
                let base = self.eval(z, base);
                Box::pin(async move {
                    let terms = self.mul(&xs, &ys).await?;
                    Ok(vec![terms.iter().fold(base, |acc, &t| acc + t)])
                })
            }
            Def::Power7(a) => {
                let a = self.eval(z, a);
                Box::pin(async move {
                    let a2 = self.mul1(a, a).await?;
                    let next = self.mul(&[a2, a2], &[a, a2]).await?;
                    Ok(vec![self.mul1(next[0], next[1]).await?])
                })
            }
            Def::InverseOrZero { of, max } => {
                let (x, max) = (self.eval(z, of), *max as usize);
                Box::pin(async move { Ok(vec![self.inverse_or_zero(x, max).await?]) })
            }
            _ => return None,
        })
    }

    /// The task of a source that is not an input.
    fn source_task<'s>(&'s self, z: &[B::S], source: &Source) -> Option<Boxed<'s, Shares<B>>> {
        Some(match source {
            Source::Input { .. } => return None,
            Source::PolyProduct { a, b } => {
                let a: Vec<B::S> = a.iter().map(|lc| self.eval(z, lc)).collect();
                let b: Vec<B::S> = b.iter().map(|lc| self.eval(z, lc)).collect();
                Box::pin(async move { self.poly_mul(&a, &b).await })
            }
            Source::Form { lc, bits } => {
                let (x, bits) = (self.eval(z, lc), *bits);
                Box::pin(async move {
                    if bits > 64 {
                        return Err(WitgenError::Unsupported { index: usize::MAX });
                    }
                    self.decompose(x, bits).await
                })
            }
            Source::Integer {
                products,
                linear,
                bits,
            } => {
                let (products, linear) = (self.int_pairs(z, products), self.int_of(z, linear));
                let bits = *bits as usize;
                Box::pin(async move {
                    let x = self.int_sum(&products, linear).await?;
                    self.normalize(&x, &[], bits).await
                })
            }
            Source::Residue {
                products,
                linear,
                den,
                modulus,
            } => {
                let (products, linear) = (self.int_pairs(z, products), self.int_of(z, linear));
                let den = (!den.is_empty()).then(|| self.int_of(z, den));
                let q = Modulus::new(modulus);
                Box::pin(async move {
                    let num = self.int_sum(&products, linear).await?;
                    match &den {
                        None => self.canonical(&num, &q).await,
                        Some(den) => self.quotient_mod(&num, den, &q).await,
                    }
                })
            }
            Source::Slope {
                num,
                den,
                tangent_products,
                tangent_linear,
                tangent_den,
                modulus,
            } => {
                let (num, den) = (self.int_of(z, num), self.int_of(z, den));
                let products = self.int_pairs(z, tangent_products);
                let linear = self.int_of(z, tangent_linear);
                let alt_den = self.int_of(z, tangent_den);
                let q = Modulus::new(modulus);
                Box::pin(async move {
                    let alt_num = self.int_sum(&products, linear).await?;
                    self.slope(&num, &den, &alt_num, &alt_den, &q).await
                })
            }
            Source::Quotient { num, divisor, bits } => {
                let (num, q, bits) = (self.int_of(z, num), Modulus::new(divisor), *bits as usize);
                Box::pin(async move { self.exact_quotient(&num, &q, bits).await })
            }
        })
    }

    /// Shares of the assignment of `shape`, whose variables are defined by `defs`.
    /// `inputs[k]` holds the bit shares of the relation's `k`-th input source. The masking
    /// variables are left zero.
    ///
    /// A product is asked for in the round after its factors are known, and a source or
    /// a division starts then; one round of the backend serves everything that is
    /// waiting. The order of requests is a function of the relation alone.
    pub fn run(
        &self,
        shape: &Shape,
        defs: &Definitions,
        public_inputs: &[F],
        inputs: &[Vec<B::S>],
    ) -> Shares<B> {
        let unsupported = |index: usize| WitgenError::Unsupported { index };
        if defs.vars.len() != shape.num_vars || public_inputs.len() != shape.num_public {
            return Err(unsupported(0));
        }
        let first = 1 + shape.num_public;
        let stop = shape.mask_var_base;
        let vars = shape.num_vars;
        let after_sources = vars + defs.sources.len();
        let lookups = shape.lookups();
        let units = after_sources + lookups.map_or(0, |l| l.num_lookups);
        // The range tables of the relation: per table tag, its first entry and its bits.
        let constant = |m: &qsag_agg::zk_hem::relation::Csr, i: usize| {
            m.row(i)
                .try_fold(F::ZERO, |acc, (col, c)| (col == 0).then_some(acc + c))
        };
        let mut tables: BTreeMap<u64, (usize, u32)> = BTreeMap::new();
        if let Some(l) = lookups {
            let rows = l.num_lookups..l.num_lookups + l.num_table_rows;
            let mut at = rows.start;
            while at < rows.end {
                let tag = constant(&l.den[0], at);
                let len = (at..rows.end)
                    .take_while(|&e| constant(&l.den[0], e) == tag)
                    .count();
                let range = len.is_power_of_two()
                    && l.den.len() >= 2
                    && (0..len).all(|j| {
                        constant(&l.den[1], at + j) == Some(F::from_u64_reduced(j as u64))
                            && l.den[2..].iter().all(|m| m.row(at + j).next().is_none())
                    });
                if let (Some(tag), true) = (tag, range) {
                    tables.insert(tag.to_canonical_u64(), (at, len.trailing_zeros()));
                }
                at += len;
            }
        }
        // The table of lookup `i`, when it is a range table and the tuple has one column.
        let table_of = |i: usize| {
            let l = lookups?;
            let tag = constant(&l.den[0], i)?.to_canonical_u64();
            let narrow = l.den[2..].iter().all(|m| m.row(i).next().is_none());
            tables.get(&tag).copied().filter(|_| narrow)
        };
        if let Some(l) = lookups
            && let Some(lookup) = (0..l.num_lookups).find(|&i| table_of(i).is_none())
        {
            return Err(WitgenError::Table { lookup });
        }

        // The variables read from each source; the forms each unit waits for.
        let mut readers: Vec<Vec<u32>> = vec![Vec::new(); defs.sources.len()];
        for i in first..stop {
            match &defs.vars[i] {
                Def::Bits { source, .. }
                | Def::Coefficient {
                    product: source, ..
                } => readers
                    .get_mut(source.index())
                    .ok_or(unsupported(i))?
                    .push(i as u32),
                Def::Undefined | Def::One | Def::Public | Def::Mask => return Err(unsupported(i)),
                _ => {}
            }
        }
        let unit_forms = |unit: usize, visit: &mut Visit<'_>| {
            let coefs =
                |v: &[IntCoef], visit: &mut Visit<'_>| v.iter().for_each(|c| visit(c.lc.terms()));
            let pairs = |v: &[(Vec<IntCoef>, Vec<IntCoef>)], visit: &mut Visit<'_>| {
                for (a, b) in v {
                    coefs(a, visit);
                    coefs(b, visit);
                }
            };
            if unit < vars {
                match &defs.vars[unit] {
                    Def::Product(a, b) => {
                        visit(a.terms());
                        visit(b.terms());
                    }
                    Def::Power7(a) => visit(a.terms()),
                    Def::SumOfProducts { base, products } => {
                        visit(base.terms());
                        for (a, b) in products {
                            visit(a.terms());
                            visit(b.terms());
                        }
                    }
                    Def::Ratio {
                        num, den, minus, ..
                    } => {
                        visit(num.terms());
                        visit(den.terms());
                        visit(minus.terms());
                    }
                    Def::InverseOrZero { of, .. } => visit(of.terms()),
                    _ => {}
                }
            } else if unit >= after_sources {
                // A lookup waits for the variables of its value.
                if let Some(l) = lookups {
                    let terms: Vec<(u32, F)> = l.den[1]
                        .row(unit - after_sources)
                        .map(|(col, c)| (col as u32, c))
                        .collect();
                    visit(&terms);
                }
            } else {
                match &defs.sources[unit - vars] {
                    Source::Input { .. } => {}
                    Source::PolyProduct { a, b } => {
                        a.iter().chain(b).for_each(|lc| visit(lc.terms()))
                    }
                    Source::Form { lc, .. } => visit(lc.terms()),
                    Source::Integer {
                        products, linear, ..
                    } => {
                        pairs(products, visit);
                        coefs(linear, visit);
                    }
                    Source::Residue {
                        products,
                        linear,
                        den,
                        ..
                    } => {
                        pairs(products, visit);
                        coefs(linear, visit);
                        coefs(den, visit);
                    }
                    Source::Slope {
                        num,
                        den,
                        tangent_products,
                        tangent_linear,
                        tangent_den,
                        ..
                    } => {
                        coefs(num, visit);
                        coefs(den, visit);
                        pairs(tangent_products, visit);
                        coefs(tangent_linear, visit);
                        coefs(tangent_den, visit);
                    }
                    Source::Quotient { num, .. } => coefs(num, visit),
                }
            }
        };
        let is_unit = |unit: usize| {
            if unit < vars {
                (first..stop).contains(&unit)
                    && !matches!(
                        defs.vars[unit],
                        Def::Bits { .. } | Def::Coefficient { .. } | Def::Multiplicity
                    )
            } else if unit >= after_sources {
                true
            } else {
                !readers[unit - vars].is_empty()
                    && !matches!(defs.sources[unit - vars], Source::Input { .. })
            }
        };
        // waiting[u]: terms of unit `u` whose variable is not set yet. dependents: for
        // each variable, the units with a term in it (one entry per term).
        let mut waiting = vec![0u32; units];
        let mut starts = vec![0u32; vars + 1];
        let mut bad = None;
        for unit in (0..units).filter(|&u| is_unit(u)) {
            let limit = match (unit < vars, lookups) {
                (true, _) => unit,
                (false, Some(l)) => l.mult_var_base,
                (false, None) => stop,
            };
            unit_forms(unit, &mut |terms| {
                for &(v, _) in terms {
                    let v = v as usize;
                    if v >= limit {
                        bad = Some(unit);
                    } else if v >= first {
                        waiting[unit] += 1;
                        starts[v + 1] += 1;
                    }
                }
            });
        }
        if let Some(unit) = bad {
            return Err(unsupported(unit));
        }
        for v in 0..vars {
            starts[v + 1] += starts[v];
        }
        let mut dependents = vec![0u32; starts[vars] as usize];
        let mut fill = starts.clone();
        for unit in (0..units).filter(|&u| is_unit(u)) {
            unit_forms(unit, &mut |terms| {
                for &(v, _) in terms {
                    let v = v as usize;
                    if v >= first {
                        dependents[fill[v] as usize] = unit as u32;
                        fill[v] += 1;
                    }
                }
            });
        }
        drop(fill);

        let mut z = SecretBuffer(vec![self.zero; vars]);
        z[0] = self.one;
        for (slot, &v) in z[1..].iter_mut().zip(public_inputs) {
            *slot = self.public(v);
        }
        let mut ready: Vec<u32> = (0..units)
            .filter(|&u| is_unit(u) && waiting[u] == 0)
            .map(|u| u as u32)
            .collect();
        let mut unset = stop - first;
        let mut set = |z: &mut Vec<B::S>, ready: &mut Vec<u32>, i: usize, value: B::S| {
            z[i] = value;
            unset -= 1;
            for &unit in &dependents[starts[i] as usize..starts[i + 1] as usize] {
                waiting[unit as usize] -= 1;
                if waiting[unit as usize] == 0 {
                    ready.push(unit);
                }
            }
        };
        // What a finished source gives its readers.
        let read = |i: usize, values: &[B::S]| -> Result<B::S, WitgenError> {
            match &defs.vars[i] {
                Def::Coefficient { index, .. } => {
                    values.get(*index as usize).copied().ok_or(unsupported(i))
                }
                Def::Bits { lo, width, .. } => {
                    Ok((0..*width as usize).fold(self.zero, |acc, t| {
                        match values.get(*lo as usize + t) {
                            Some(&b) => acc + B::scale(b, pow2(t)),
                            None => acc,
                        }
                    }))
                }
                _ => Err(unsupported(i)),
            }
        };

        // Inputs, in the order their sources are first read.
        let mut next_input = 0;
        for (id, source) in defs.sources.iter().enumerate() {
            let Source::Input { bits } = source else {
                continue;
            };
            if readers[id].is_empty() {
                continue;
            }
            let shares = inputs
                .get(next_input)
                .filter(|s| s.len() == *bits as usize)
                .ok_or(WitgenError::Inputs)?;
            next_input += 1;
            for &i in &readers[id] {
                let value = read(i as usize, shares)?;
                set(&mut z, &mut ready, i as usize, value);
            }
        }
        if next_input != inputs.len() {
            return Err(WitgenError::Inputs);
        }

        if !self.planning {
            let (bits, masks) = plan(shape, defs, self.chains)?;
            self.wait(self.fill_pool(bits, masks))?;
        }
        // Multiplicities: the sum over the lookups of the indicator of each one's row.
        let mut counts =
            SecretScratch::from(vec![self.zero; lookups.map_or(0, |l| l.num_table_rows)]);
        let mut uncounted = lookups.map_or(0, |l| l.num_lookups);
        if let (Some(l), 0) = (lookups, uncounted) {
            for (r, &count) in counts.iter().enumerate() {
                set(&mut z, &mut ready, l.mult_var_base + r, count);
            }
        }
        let mut cx = Context::from_waker(Waker::noop());
        let mut active: Vec<(u32, Boxed<'_, Shares<B>>)> = Vec::new();
        let mut direct: Vec<(usize, u32)> = Vec::new();
        loop {
            // Start what is ready; a unit that finishes at once may make more ready.
            let mut next = 0;
            let mut finished: Vec<(u32, SecretScratch<B::S>)> = Vec::new();
            loop {
                while next < ready.len() {
                    let unit = ready[next] as usize;
                    next += 1;
                    if unit < vars
                        && let Def::Product(a, b) = &defs.vars[unit]
                    {
                        let at = self.push_mul(&[self.eval(&z, a)], &[self.eval(&z, b)]);
                        direct.push((at, unit as u32));
                        continue;
                    }
                    let task = if unit < vars {
                        self.var_task(&z, &defs.vars[unit])
                    } else if unit >= after_sources {
                        lookups
                            .zip(table_of(unit - after_sources))
                            .map(|(l, (_, bits))| {
                                let x = l.den[1]
                                    .row(unit - after_sources)
                                    .fold(self.zero, |acc, (col, c)| acc + B::scale(z[col], c));
                                Box::pin(self.one_hot(x, bits)) as Boxed<'_, Shares<B>>
                            })
                    } else {
                        self.source_task(&z, &defs.sources[unit - vars])
                    };
                    let mut task = task.ok_or(unsupported(unit))?;
                    match task.as_mut().poll(&mut cx) {
                        Poll::Ready(values) => {
                            finished.push((unit as u32, SecretScratch::from(values?)))
                        }
                        Poll::Pending => active.push((unit as u32, task)),
                    }
                }
                if finished.is_empty() {
                    break;
                }
                for (unit, values) in finished.drain(..) {
                    let unit = unit as usize;
                    if unit < vars {
                        let value = *values.first().ok_or(unsupported(unit))?;
                        set(&mut z, &mut ready, unit, value);
                    } else if unit >= after_sources {
                        let (l, (start, _)) = lookups
                            .zip(table_of(unit - after_sources))
                            .ok_or(unsupported(unit))?;
                        let row = start - l.num_lookups;
                        for (count, &hit) in counts[row..].iter_mut().zip(&values) {
                            *count = *count + hit;
                        }
                        uncounted -= 1;
                        if uncounted == 0 {
                            for (r, &count) in counts.iter().enumerate() {
                                set(&mut z, &mut ready, l.mult_var_base + r, count);
                            }
                        }
                    } else {
                        for &i in &readers[unit - vars] {
                            let value = read(i as usize, &values)?;
                            set(&mut z, &mut ready, i as usize, value);
                        }
                    }
                }
            }
            ready.clear();
            if self.idle() {
                break;
            }
            self.step()?;
            for (at, var) in direct.drain(..) {
                let value = self.q.borrow().products[at];
                set(&mut z, &mut ready, var as usize, value);
            }
            // Every waiting task asked for something in the round that just ran.
            let mut finished: Vec<(u32, SecretScratch<B::S>)> = Vec::new();
            for (unit, mut task) in core::mem::take(&mut active) {
                match task.as_mut().poll(&mut cx) {
                    Poll::Ready(values) => finished.push((unit, SecretScratch::from(values?))),
                    Poll::Pending => active.push((unit, task)),
                }
            }
            for (unit, values) in finished {
                let unit = unit as usize;
                if unit < vars {
                    let value = *values.first().ok_or(unsupported(unit))?;
                    set(&mut z, &mut ready, unit, value);
                } else if unit >= after_sources {
                    let (l, (start, _)) = lookups
                        .zip(table_of(unit - after_sources))
                        .ok_or(unsupported(unit))?;
                    let row = start - l.num_lookups;
                    for (count, &hit) in counts[row..].iter_mut().zip(&values) {
                        *count = *count + hit;
                    }
                    uncounted -= 1;
                    if uncounted == 0 {
                        for (r, &count) in counts.iter().enumerate() {
                            set(&mut z, &mut ready, l.mult_var_base + r, count);
                        }
                    }
                } else {
                    for &i in &readers[unit - vars] {
                        let value = read(i as usize, &values)?;
                        set(&mut z, &mut ready, i as usize, value);
                    }
                }
            }
        }
        drop(active);
        if unset != 0 {
            // A variable that waits for itself or for a variable nothing defines.
            return Err(unsupported(first));
        }
        self.check()?;
        Ok(z.into_inner())
    }
}

/// Bit counts of the relation's input sources, in the order [`generate`] takes them.
pub fn input_bits(defs: &Definitions) -> Vec<usize> {
    defs.sources
        .iter()
        .filter_map(|s| match s {
            Source::Input { bits } => Some(*bits as usize),
            _ => None,
        })
        .collect()
}

/// What one custodian's [`generate`] consumes: triples, uniform values, and the counts
/// of opened values, rounds and MAC checks.
pub fn demand(shape: &Shape, defs: &Definitions) -> Result<Count, WitgenError> {
    demand_with(shape, defs, CHAINS)
}

/// The random bits and exact masks the subprotocols of a relation ask for.
fn plan(shape: &Shape, defs: &Definitions, chains: Chains) -> Result<(usize, usize), WitgenError> {
    let mut count = Count::default();
    let inputs: Vec<Vec<Unit>> = input_bits(defs)
        .into_iter()
        .map(|bits| vec![Unit; bits])
        .collect();
    let public = vec![F::ZERO; shape.num_public];
    let mut w = Witgen::with_chains(&mut count, chains);
    w.planning = true;
    w.run(shape, defs, &public, &inputs)?;
    Ok(w.asked.get())
}

/// [`demand`] for a choice of carry chains.
pub fn demand_with(
    shape: &Shape,
    defs: &Definitions,
    chains: Chains,
) -> Result<Count, WitgenError> {
    let mut count = Count::default();
    let inputs: Vec<Vec<Unit>> = input_bits(defs)
        .into_iter()
        .map(|bits| vec![Unit; bits])
        .collect();
    let public = vec![F::ZERO; shape.num_public];
    Witgen::with_chains(&mut count, chains).run(shape, defs, &public, &inputs)?;
    Ok(count)
}

/// One custodian's side of witness generation: authenticated shares of the assignment of
/// `shape` from authenticated shares of the bits of its inputs.
pub fn generate<T: Transport>(
    e: &mut Engine<T>,
    shape: &Shape,
    defs: &Definitions,
    public_inputs: &[F],
    inputs: &[Vec<Sb>],
) -> Result<Vec<Sb>, WitgenError> {
    Witgen::new(e).run(shape, defs, public_inputs, inputs)
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use qsag_agg::zk_hem::SeedStream;

    /// The clear reference: the same code on plain field values.
    pub(in super::super) struct Plain {
        stream: SeedStream,
        pub count: Count,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(in super::super) struct Clear(pub F);

    impl Add for Clear {
        type Output = Clear;
        fn add(self, r: Clear) -> Clear {
            Clear(self.0 + r.0)
        }
    }

    impl Sub for Clear {
        type Output = Clear;
        fn sub(self, r: Clear) -> Clear {
            Clear(self.0 - r.0)
        }
    }

    impl Plain {
        pub(in super::super) fn new(tag: u8) -> Self {
            Self {
                stream: SeedStream::new(b"QSAG.TEST.WITGEN", &[tag; 32]),
                count: Count::default(),
            }
        }
    }

    impl SecretWipe for Clear {
        fn secret_wipe(&mut self) {
            self.0.secret_wipe();
        }
    }

    impl Backend for Plain {
        type S = Clear;
        fn scale(s: Clear, k: F) -> Clear {
            Clear(s.0 * k)
        }
        fn public(&self, c: F) -> Clear {
            Clear(c)
        }
        fn random(&mut self) -> Result<Clear, MpcError> {
            self.count.randoms += 1;
            Ok(Clear(self.stream.next_base()))
        }
        fn round(
            &mut self,
            xs: &[Clear],
            ys: &[Clear],
            opens: &[Clear],
        ) -> Result<(Vec<Clear>, Vec<F>), MpcError> {
            self.count.triples += xs.len();
            self.count.rounds += 1;
            Ok((
                xs.iter().zip(ys).map(|(x, y)| Clear(x.0 * y.0)).collect(),
                opens.iter().map(|x| x.0).collect(),
            ))
        }
        fn check(&mut self) -> Result<(), MpcError> {
            Ok(())
        }
    }

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    fn value(bits: &[Clear]) -> Nat {
        let mut out = vec![0u64; bits.len() / 64 + 1];
        for (i, b) in bits.iter().enumerate() {
            let v = b.0.to_canonical_u64();
            assert!(v <= 1, "bit {i} is {v}");
            out[i / 64] |= v << (i % 64);
        }
        nat_trim(out)
    }

    const SECP_P: [u8; 32] = {
        let mut p = [0xff; 32];
        p[0] = 0x2f;
        p[1] = 0xfc;
        p[4] = 0xfe;
        p
    };
    const ED_P: [u8; 32] = {
        let mut p = [0xff; 32];
        p[0] = 0xed;
        p[31] = 0x7f;
        p
    };

    #[test]
    fn public_integer_arithmetic_and_square_roots() {
        let mut s = SeedStream::new(b"QSAG.TEST.WITGEN", &[1; 32]);
        for _ in 0..200 {
            let a = s.next_base();
            if a != F::ZERO {
                let r = sqrt(a * a).unwrap();
                assert!(r == a || r == F::ZERO - a);
                assert_eq!(sqrt(a * a), sqrt((F::ZERO - a) * (F::ZERO - a)));
                // 7 generates the group, so 7 a^2 is not a square.
                assert_eq!(sqrt(f(7) * a * a), None);
            }
        }
        for p in [SECP_P, ED_P] {
            let q = Modulus::new(&p);
            let mut back = vec![0u64; 6];
            for &(pos, d) in &q.digits {
                nat_add_signed(&mut back, i128::from(d), pos);
            }
            assert_eq!(nat_trim(back), q.p);
            for _ in 0..5 {
                let a: Nat = (0..4).map(|_| s.next_base().to_canonical_u64()).collect();
                let a = nat_divrem(&a, &q.p).1;
                let inverse = nat_invmod(&a, &q.p);
                assert_eq!(nat_mulmod(&a, &inverse, &q.p), vec![1]);
                let (quotient, rest) = nat_divrem(&nat_mul(&a, &a), &q.p);
                assert_eq!(nat_add(&nat_mul(&quotient, &q.p), &rest), nat_mul(&a, &a));
            }
        }
        let m = interpolation_matrix(5);
        // 3 t^4 - t + 7 at 0..5, back to its coefficients.
        let values: Vec<F> = (0..5u64).map(|t| f(3 * t.pow(4) + 7) - f(t)).collect();
        let coefficients: Vec<F> = m
            .iter()
            .map(|row| {
                row.iter()
                    .zip(&values)
                    .fold(F::ZERO, |a, (&k, &v)| a + k * v)
            })
            .collect();
        assert_eq!(
            coefficients,
            [f(7), F::ZERO - F::ONE, F::ZERO, F::ZERO, f(3)]
        );
    }

    #[test]
    fn decomposition_is_exact_at_every_width_and_boundary() {
        let mut plain = Plain::new(2);
        let mut s = SeedStream::new(b"QSAG.TEST.WITGEN", &[3; 32]);
        let w = Witgen::new(&mut plain);
        for m in [1u32, 2, 8, 22, 23, 31, 32, 33, 40, 63, 64] {
            let top = if m == 64 {
                0xFFFF_FFFF_0000_0000
            } else {
                (1u64 << m) - 1
            };
            let mut cases = vec![0, 1, top, top - 1, top / 2];
            cases.extend((0..12).map(|_| s.next_base().to_canonical_u64() & top));
            for x in cases {
                let x = x.min(top);
                let bits = w.wait(w.decompose(Clear(f(x)), m)).unwrap();
                assert_eq!(bits.len(), m as usize);
                assert_eq!(value(&bits), nat_trim(vec![x]), "m={m} x={x}");
            }
        }
        // The counter is an upper bound on what a real run uses.
        drop(w);
        let used = plain.count;
        let mut count = Count::default();
        let c = Witgen::new(&mut count);
        for m in [1u32, 2, 8, 22, 23, 31, 32, 33, 40, 63, 64] {
            for _ in 0..17 {
                c.wait(c.decompose(Unit, m)).unwrap();
            }
        }
        drop(c);
        assert!(count.triples >= used.triples && count.triples <= used.triples + used.triples / 4);
        assert!(count.randoms <= used.randoms && count.randoms + 64 * 8 >= used.randoms);
    }

    fn int(values: &[i128], lo: i128, hi: i128) -> Int<Clear> {
        Int {
            c: values.iter().map(|&v| Clear(f_signed(v))).collect(),
            lo: vec![lo; values.len()],
            hi: vec![hi; values.len()],
        }
    }

    fn int_value(values: &[i128]) -> (Nat, Nat) {
        let mut pos = vec![0u64; values.len() / 8 + 4];
        let mut neg = pos.clone();
        for (k, &v) in values.iter().enumerate() {
            nat_add_signed(if v < 0 { &mut neg } else { &mut pos }, v.abs(), k);
        }
        (nat_trim(pos), nat_trim(neg))
    }

    #[test]
    fn residues_quotients_and_inverses_match_public_arithmetic() {
        let mut s = SeedStream::new(b"QSAG.TEST.WITGEN", &[4; 32]);
        let mut plain = Plain::new(5);
        let w = Witgen::new(&mut plain);
        let mut limbs = |n: usize, lo: i128, hi: i128| -> Vec<i128> {
            (0..n)
                .map(|_| lo + (s.next_base().to_canonical_u64() as i128) % (hi - lo + 1))
                .collect()
        };
        for p in [SECP_P, ED_P] {
            let q = Modulus::new(&p);
            for round in 0..3 {
                // A product of two integers minus a third, with signed wide coefficients.
                let (a, b) = (limbs(32, 0, 255), limbs(32, -255, 255));
                let c = limbs(40, -(1 << 40), 1 << 40);
                let (ia, ib, ic) = (
                    int(&a, 0, 255),
                    int(&b, -255, 255),
                    int(&c, -(1 << 40), 1 << 40),
                );
                let product = w.wait(w.int_mul(&ia, &ib)).unwrap();
                let x = w.int_add(&product, &ic);
                let (ap, an) = int_value(&a);
                let (bp, bn) = int_value(&b);
                let (cp, cn) = int_value(&c);
                let reduce = |pos: &Nat, neg: &Nat| {
                    let (pos, neg) = (nat_divrem(pos, &q.p).1, nat_divrem(neg, &q.p).1);
                    nat_divrem(&nat_sub(&nat_add(&pos, &q.p), &neg), &q.p).1
                };
                let (am, bm, cm) = (reduce(&ap, &an), reduce(&bp, &bn), reduce(&cp, &cn));
                let want = nat_divrem(&nat_add(&nat_mulmod(&am, &bm, &q.p), &cm), &q.p).1;
                let got = w.wait(w.canonical(&x, &q)).unwrap();
                assert_eq!(got.len(), q.bits);
                assert_eq!(value(&got), want, "residue, round {round}");

                // The same over a denominator.
                let d = limbs(32, -255, 255);
                let id = int(&d, -255, 255);
                let (dp, dn) = int_value(&d);
                let dm = reduce(&dp, &dn);
                let got = w.wait(w.quotient_mod(&x, &id, &q)).unwrap();
                assert_eq!(
                    value(&got),
                    nat_mulmod(&want, &nat_invmod(&dm, &q.p), &q.p),
                    "quotient, round {round}"
                );
            }
            // A zero denominator is refused.
            let zero = int(&[0; 32], -255, 255);
            let one = int(&[1], 0, 255);
            assert_eq!(
                w.wait(w.quotient_mod(&one, &zero, &q)).err(),
                Some(WitgenError::ZeroDenominator)
            );

            // Exact division: N = Q q with Q < 2^27, coefficients shifted off their digits.
            let quotient = 0x5a5_1234u64;
            let n = nat_mul(&[quotient], &q.p);
            let mut coefficients: Vec<i128> = (0..36).map(|k| nat_byte(&n, k) as i128).collect();
            coefficients[0] += 256 * 1000;
            coefficients[1] -= 1000;
            coefficients[2] -= 256 * 77;
            coefficients[3] += 77;
            let num = int(&coefficients, -(1 << 20), 1 << 20);
            let got = w.wait(w.exact_quotient(&num, &q, 27)).unwrap();
            assert_eq!(value(&got), vec![quotient]);
        }
        for max in [1usize, 2, 5, 40] {
            for x in 0..=max as u64 {
                let got = w.wait(w.inverse_or_zero(Clear(f(x)), max)).unwrap();
                assert_eq!(got.0, f(x).inv_or_zero(), "max={max} x={x}");
            }
        }
    }

    use crate::hem::relations::{
        Bip32Root, Ed25519ExtendedKey, KeySource, Lock, OwnershipStatement, OwnershipWitness,
        PathSpec, bip32_derive, ownership_auxiliary_inputs, ownership_definitions, ownership_shape,
        synthesize_ownership,
    };

    fn statement(lock: Lock, source: KeySource, witness: &OwnershipWitness) -> OwnershipStatement {
        OwnershipStatement::derive(lock, source, witness, [5; 32], [6; 32], 9)
            .expect("a witness for the statement")
    }

    /// The property a threshold prover needs of a relation: no variable without a
    /// definition, and the recorded relation is the one the verifier builds.
    #[test]
    fn every_ownership_statement_defines_every_variable() {
        const H: u32 = 1 << 31;
        let key = OwnershipWitness::secp256k1_key(&[0x11; 32]);
        let mut extended = [0u8; 96];
        extended[0] = 8;
        extended[31] = 0x40;
        extended[40] = 3;
        let mut cases = vec![
            statement(Lock::P2pkhUncompressed, KeySource::Secp256k1Key, &key),
            statement(Lock::P2shP2wpkh, KeySource::Secp256k1Key, &key),
            statement(Lock::Ethereum, KeySource::Secp256k1Key, &key),
            statement(Lock::TaprootKeyPath, KeySource::Secp256k1Key, &key),
            statement(
                Lock::TaprootScriptTree,
                KeySource::Secp256k1Key,
                &OwnershipWitness::secp256k1_key(&[0x11; 32]).with_merkle_root([3; 32]),
            ),
            statement(
                Lock::BlsWithdrawal,
                KeySource::Bls12381Key,
                &OwnershipWitness::bls12_381_key(&[0x13; 32]),
            ),
            statement(
                Lock::P2pkh,
                KeySource::Bip32 {
                    root: Bip32Root::Seed,
                    path: PathSpec::Public(vec![H, 1]),
                },
                &OwnershipWitness::seed(&[7; 16]),
            ),
            statement(
                Lock::P2pkh,
                KeySource::Bip32 {
                    root: Bip32Root::Seed,
                    path: PathSpec::Hidden { max_depth: 1 },
                },
                &OwnershipWitness::seed(&[7; 16]).with_path(&[H + 2]),
            ),
            statement(
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: PathSpec::Public(vec![H]),
                },
                &OwnershipWitness::seed(&[7; 16]),
            ),
            statement(
                Lock::Ed25519,
                KeySource::Bip32Ed25519 { path: vec![1] },
                &OwnershipWitness::ed25519_extended_key(&Ed25519ExtendedKey(extended)),
            ),
        ];
        cases.extend(reference_cases().into_iter().map(|(st, _, _)| st));
        for st in &cases {
            let (shape, defs) = ownership_definitions(st).unwrap();
            assert_eq!(shape.digest(), ownership_shape(st).unwrap().digest());
            assert_eq!(defs.vars.len(), shape.num_vars);
            assert_eq!(
                defs.undefined(),
                Vec::<usize>::new(),
                "{:?} {:?}",
                st.lock,
                st.source
            );
            assert!(matches!(defs.sources.first(), Some(Source::Input { .. })));
        }
    }

    /// The two statements the threshold prover is exercised on, with their witness and
    /// the witness secret.
    pub(in super::super) fn reference_cases() -> Vec<(OwnershipStatement, OwnershipWitness, Vec<u8>)>
    {
        let key = OwnershipWitness::secp256k1_key(&[0x11; 32]);
        let seed = OwnershipWitness::ed25519_seed(&[0x22; 32]);
        vec![
            (
                statement(Lock::P2pkh, KeySource::Secp256k1Key, &key),
                key,
                vec![0x11; 32],
            ),
            (
                statement(Lock::Ed25519, KeySource::Ed25519Seed, &seed),
                seed,
                vec![0x22; 32],
            ),
        ]
    }

    /// Statements whose relation takes inputs besides the secret, with their witness, the
    /// secret, the hidden path and the script-tree root: a master seed with a public
    /// path (`m/44'`), a longer seed with a hidden path under a Taproot script tree, a
    /// SLIP-0010 seed with a hidden path, and an extended key with a hidden public step.
    #[allow(clippy::type_complexity)]
    pub(in super::super) fn derived_cases() -> Vec<(
        OwnershipStatement,
        OwnershipWitness,
        Vec<u8>,
        Vec<u32>,
        Option<[u8; 32]>,
    )> {
        const H: u32 = 1 << 31;
        let mut out = Vec::new();
        let seed = vec![0x31; 16];
        let witness = OwnershipWitness::seed(&seed);
        let source = KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Public(vec![H + 44]),
        };
        out.push((
            statement(Lock::P2pkh, source, &witness),
            witness,
            seed,
            Vec::new(),
            None,
        ));
        let seed: Vec<u8> = (0..33).map(|i| 0x40 + i as u8).collect();
        let (path, root) = (vec![H + 86], [0x5a; 32]);
        let witness = OwnershipWitness::seed(&seed)
            .with_path(&path)
            .with_merkle_root(root);
        let source = KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Hidden { max_depth: 2 },
        };
        out.push((
            statement(Lock::TaprootScriptTree, source, &witness),
            witness,
            seed,
            path,
            Some(root),
        ));
        let seed = vec![0x77; 64];
        let path = vec![H + 5];
        let witness = OwnershipWitness::seed(&seed).with_path(&path);
        let source = KeySource::Slip10 {
            path: PathSpec::Hidden { max_depth: 1 },
        };
        out.push((
            statement(Lock::Ed25519, source, &witness),
            witness,
            seed,
            path,
            None,
        ));
        let node = bip32_derive(&[0x21; 32], &[H]).unwrap();
        let secret = [node.private_key, node.chain_code].concat();
        let path = vec![7];
        let witness = OwnershipWitness::extended_key(&node).with_path(&path);
        let source = KeySource::Bip32 {
            root: Bip32Root::ExtendedKey,
            path: PathSpec::Hidden { max_depth: 1 },
        };
        out.push((
            statement(Lock::P2pkh, source, &witness),
            witness,
            secret,
            path,
            None,
        ));
        out
    }

    /// The inputs of a relation as plain values: the secret padded to the first input's
    /// width, then the auxiliary inputs.
    fn clear_inputs(defs: &Definitions, secret: &[u8], auxiliary: &[Vec<bool>]) -> Vec<Vec<Clear>> {
        let widths = input_bits(defs);
        assert_eq!(widths.len(), 1 + auxiliary.len());
        assert!(widths[0] >= 8 * secret.len());
        let mut first: Vec<Clear> = (0..8 * secret.len())
            .map(|i| Clear(f(u64::from((secret[i / 8] >> (i % 8)) & 1))))
            .collect();
        first.resize(widths[0], Clear(F::ZERO));
        let mut out = vec![first];
        for (bits, &width) in auxiliary.iter().zip(&widths[1..]) {
            assert_eq!(bits.len(), width);
            out.push(bits.iter().map(|&b| Clear(f(u64::from(b)))).collect());
        }
        out
    }

    /// Seeds of hidden length, hidden paths and script-tree roots: the auxiliary inputs
    /// are the ones the gadgets allocate, in their order, so the definitions evaluated on
    /// the secret and those inputs give the gadget's assignment.
    #[test]
    fn auxiliary_inputs_reproduce_the_gadget_assignment() {
        const H: u32 = 1 << 31;
        for (st, witness, secret, path, root) in derived_cases() {
            let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
            let (recorded, defs) = ownership_definitions(&st).unwrap();
            assert_eq!(recorded.digest(), shape.digest());
            let auxiliary =
                ownership_auxiliary_inputs(&st, secret.len(), &path, root.as_ref()).unwrap();
            let inputs = clear_inputs(&defs, &secret, &auxiliary);
            let run = |inputs: &[Vec<Clear>]| {
                Witgen::new(&mut Plain::new(6)).run(
                    &shape,
                    &defs,
                    &st.public_inputs().unwrap(),
                    inputs,
                )
            };
            let z = run(&inputs).unwrap();
            let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
            assert_eq!(
                wrong.map(|i| (i, defs.vars[i].clone())),
                None,
                "{:?}",
                st.source
            );

            // The auxiliary inputs matter: flipping the first or the last of them moves
            // the assignment (or leaves the relation without one).
            for k in [1, inputs.len() - 1] {
                let mut other = inputs.clone();
                other[k][0] = Clear(F::ONE - other[k][0].0);
                assert!(run(&other).map_or(true, |o| o != z), "input {k}");
            }

            // What does not fit the statement is refused.
            let aux = |bytes: usize, path: &[u32], root: Option<&[u8; 32]>| {
                ownership_auxiliary_inputs(&st, bytes, path, root)
            };
            assert_eq!(aux(secret.len(), &path, root.as_ref()), Some(auxiliary));
            assert_eq!(aux(15, &path, root.as_ref()), None);
            assert_eq!(aux(65, &path, root.as_ref()), None);
            let long = [path.clone(), vec![H, H, H]].concat();
            assert_eq!(aux(secret.len(), &long, root.as_ref()), None);
            let flipped = if root.is_some() {
                None
            } else {
                Some(&[1u8; 32])
            };
            assert_eq!(aux(secret.len(), &path, flipped), None);
        }
        // A SLIP-0010 path has hardened steps only.
        let (st, _, secret, _, _) = derived_cases().swap_remove(2);
        assert_eq!(
            ownership_auxiliary_inputs(&st, secret.len(), &[5], None),
            None
        );
    }

    /// An addition that may be a doubling: the chord where the denominator is nonzero
    /// modulo the prime, the tangent where it is zero modulo the prime (as an integer it
    /// need not be zero), and the same consumption either way.
    #[test]
    fn slopes_select_chord_or_tangent_without_showing_which() {
        let q = Modulus::new(&SECP_P);
        let reduce = |values: &[i128]| {
            let (pos, neg) = int_value(values);
            let (pos, neg) = (nat_divrem(&pos, &q.p).1, nat_divrem(&neg, &q.p).1);
            nat_divrem(&nat_sub(&nat_add(&pos, &q.p), &neg), &q.p).1
        };
        let num: Vec<i128> = (0..32).map(|k| 3 * k as i128 - 40).collect();
        let alt_num: Vec<i128> = (0..40).map(|k| 1000 - 77 * k as i128).collect();
        let alt_den: Vec<i128> = (0..32).map(|k| 2 * (k as i128 % 100) + 1).collect();
        // The secp256k1 prime written with signed limbs: a denominator that is zero
        // modulo the prime and not zero as an integer.
        let mut prime: Vec<i128> = SECP_P.iter().map(|&b| i128::from(b)).collect();
        prime[0] -= 256;
        prime[1] += 1;
        let mut nonzero = vec![0i128; 32];
        nonzero[5] = -9;
        let mut counts = Vec::new();
        for (den, tangent) in [
            (nonzero, false),
            (vec![0i128; 32], true),
            (prime.clone(), true),
        ] {
            let mut plain = Plain::new(8);
            let w = Witgen::new(&mut plain);
            let got = w
                .wait(w.slope(
                    &int(&num, -300, 300),
                    &int(&den, -300, 300),
                    &int(&alt_num, -3000, 3000),
                    &int(&alt_den, -300, 300),
                    &q,
                ))
                .unwrap();
            drop(w);
            let (n, d) = if tangent {
                (reduce(&alt_num), reduce(&alt_den))
            } else {
                (reduce(&num), reduce(&den))
            };
            assert_eq!(
                value(&got),
                nat_mulmod(&n, &nat_invmod(&d, &q.p), &q.p),
                "tangent={tangent}"
            );
            counts.push((plain.count.triples, plain.count.randoms));
        }
        assert_eq!(reduce(&prime), Nat::new());
        assert!(counts.iter().all(|c| c == &counts[0]), "{counts:?}");
    }

    /// The secp256k1 key `2^250 - 1`: the last addition of its multiplication doubles the
    /// last window's point. The quorum computes its assignment like any other, with the
    /// same preprocessing.
    #[test]
    fn a_key_whose_last_addition_doubles_is_computed_like_any_other() {
        let mut key = [0xff; 32];
        key[0] = 0x03;
        let mut used = Vec::new();
        for secret in [key, [0x11; 32]] {
            let witness = OwnershipWitness::secp256k1_key(&secret);
            let st = statement(Lock::P2pkh, KeySource::Secp256k1Key, &witness);
            let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
            let (_, defs) = ownership_definitions(&st).unwrap();
            let inputs = clear_inputs(&defs, &secret, &[]);
            let mut plain = Plain::new(6);
            let z = Witgen::new(&mut plain)
                .run(&shape, &defs, &st.public_inputs().unwrap(), &inputs)
                .unwrap();
            let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
            assert_eq!(wrong.map(|i| (i, defs.vars[i].clone())), None);
            used.push((plain.count.triples, plain.count.randoms));
        }
        assert_eq!(used[0], used[1]);
    }

    /// Triples and rounds of the two reference statements under each kind of chain.
    /// `cargo test --release -p qsag-migrate --features std --lib --
    /// hem::collab::witgen::tests::measure_chains --ignored --nocapture`
    #[test]
    #[ignore = "measurement"]
    fn measure_chains() {
        let mut cases: Vec<OwnershipStatement> =
            reference_cases().into_iter().map(|c| c.0).collect();
        cases.push(derived_cases().swap_remove(0).0);
        // m/44'/0'/0'/0/0 from a master seed.
        const H: u32 = 1 << 31;
        let seed = OwnershipWitness::seed(&[0x31; 16]);
        let source = KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Public(vec![H + 44, H, H, 0, 0]),
        };
        cases.push(statement(Lock::P2pkh, source, &seed));
        for st in cases {
            let (shape, defs) = ownership_definitions(&st).unwrap();
            for chains in [Chains::Ripple, Chains::Prefix, Chains::Mixed] {
                let c = demand_with(&shape, &defs, chains).unwrap();
                std::println!(
                    "{:?} {:?} {chains:?}: triples={} randoms={} rounds={} checks={} opened={}",
                    st.lock,
                    st.source,
                    c.triples,
                    c.randoms,
                    c.rounds,
                    c.checks,
                    c.opened
                );
            }
        }
    }

    /// The definitions mean what the gadgets compute: evaluated on plain values from the
    /// secret alone they give the gadget's assignment, variable for variable.
    #[test]
    fn definitions_reproduce_the_gadget_assignment() {
        for (st, witness, secret) in reference_cases() {
            let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
            let (recorded, defs) = ownership_definitions(&st).unwrap();
            assert_eq!(recorded.digest(), shape.digest());
            assert_eq!(input_bits(&defs), [8 * secret.len()]);
            let bits: Vec<Clear> = (0..8 * secret.len())
                .map(|i| Clear(f(u64::from((secret[i / 8] >> (i % 8)) & 1))))
                .collect();
            let mut plain = Plain::new(6);
            let z = Witgen::new(&mut plain)
                .run(
                    &shape,
                    &defs,
                    &st.public_inputs().unwrap(),
                    core::slice::from_ref(&bits),
                )
                .unwrap();
            let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
            assert_eq!(wrong.map(|i| (i, defs.vars[i].clone())), None);
            let bound = demand(&shape, &defs).unwrap();
            std::println!(
                "{:?}: vars={} used triples={} randoms={}; bound triples={} randoms={} rounds={} checks={}",
                st.lock,
                shape.num_vars,
                plain.count.triples,
                plain.count.randoms,
                bound.triples,
                bound.randoms,
                bound.rounds,
                bound.checks,
            );
            // The run consumes exactly what the count says, in as many rounds, and the
            // rounds are the relation's depth (pinned), not its size.
            assert_eq!(
                (bound.triples, bound.randoms, bound.rounds),
                (plain.count.triples, plain.count.randoms, plain.count.rounds)
            );
            let pinned = match st.lock {
                Lock::P2pkh => (2_151_917, 14_049),
                _ => (2_286_466, 13_443),
            };
            assert_eq!((bound.triples, bound.rounds), pinned);

            // A wrong input bit gives a different assignment, and too few inputs are refused.
            let mut flipped = bits.clone();
            flipped[3] = Clear(F::ONE - flipped[3].0);
            let other = Witgen::new(&mut Plain::new(6)).run(
                &shape,
                &defs,
                &st.public_inputs().unwrap(),
                &[flipped],
            );
            assert!(other.map_or(true, |o| o != z));
            assert_eq!(
                Witgen::new(&mut Plain::new(6))
                    .run(
                        &shape,
                        &defs,
                        &st.public_inputs().unwrap(),
                        &[bits[1..].to_vec()]
                    )
                    .err(),
                Some(WitgenError::Inputs)
            );
        }
    }

    use super::super::engine::{Dealer, Engine, Preprocessing};
    use super::super::net::{ChannelLink, Framed, NetError, channel_mesh};
    use crate::hem::curve::{Lazy, Modulus as CurveModulus};
    use crate::hem::hash::{add_wide, alloc_bits, maj, pack_bits, xor3};
    use qsag_agg::zk_hem::relation::ConstraintSystem;

    /// A relation over a 4-byte secret that uses the hash and curve gadgets: Boolean
    /// functions, a wide addition, and a product modulo the secp256k1 base prime.
    fn small_recorded(secret: &[u8; 4]) -> (Shape, Vec<F>, Definitions) {
        let mut cs = ConstraintSystem::new_recording();
        let public: Lc = cs
            .public_input(f(u64::from(secret[0]) * u64::from(secret[1])))
            .into();
        let bits = alloc_bits(&mut cs, secret);
        let product = cs.mul(&pack_bits(&bits[..8]), &pack_bits(&bits[8..16]));
        cs.enforce_equal(&product.into(), &public);
        let sum = add_wide(&mut cs, &bits[..16], &bits[16..]);
        let mixed: Vec<Lc> = (0..16)
            .map(|i| {
                let x = xor3(&mut cs, &bits[i], &bits[i + 16], &sum[i]);
                maj(&mut cs, &x, &bits[i], &sum[i])
            })
            .collect();
        let field = CurveModulus::secp256k1_base();
        let reduced = field.mul(&mut cs, &Lazy::from_bits(&bits), &Lazy::from_bits(&mixed));
        field.enforce_canonical(&mut cs, &reduced);
        cs.finish_recorded()
    }

    /// A relation over a 4-byte secret, with or without byte lookups of six values: the
    /// four secret bytes, one of them again, and a constant.
    fn byte_lookup_recorded(secret: &[u8; 4], lookups: bool) -> (Shape, Vec<F>, Definitions) {
        let mut cs = ConstraintSystem::new_recording();
        let public: Lc = cs
            .public_input(f(u64::from(secret[0]) * u64::from(secret[1])))
            .into();
        let bits = alloc_bits(&mut cs, secret);
        let bytes: Vec<Lc> = bits.chunks(8).map(pack_bits).collect();
        let product = cs.mul(&bytes[0], &bytes[1]);
        cs.enforce_equal(&product.into(), &public);
        if lookups {
            for byte in bytes.iter().chain([&bytes[2], &Lc::constant(f(200))]) {
                cs.enforce_byte(byte);
            }
        }
        cs.finish_recorded()
    }

    /// Multiplicities on shares: the count of each table row over the lookups, at 302
    /// triples and 48 uniform values a byte lookup, in the rounds the rest takes.
    #[test]
    fn multiplicities_of_byte_lookups_are_counted_on_shares() {
        let secret = [0xa7, 0x00, 0xff, 0xa7];
        let (shape, assignment, defs) = byte_lookup_recorded(&secret, true);
        assert!(shape.is_satisfied(&assignment));
        assert_eq!(defs.undefined(), Vec::<usize>::new());
        let l = shape.lookups().unwrap();
        assert_eq!((l.num_lookups, l.num_table_rows), (6, 256));
        // 0xa7 twice, 0xff twice (bytes[2] is looked up again), 0x00 and 200 once.
        let count = |row: usize| assignment[l.mult_var_base + row].to_canonical_u64();
        assert_eq!(
            (count(0xa7), count(0xff), count(0), count(200), count(1)),
            (2, 2, 1, 1, 0)
        );

        let inputs = clear_inputs(&defs, &secret, &[]);
        let publics = assignment[1..=shape.num_public].to_vec();
        let mut plain = Plain::new(9);
        let z = Witgen::new(&mut plain)
            .run(&shape, &defs, &publics, &inputs)
            .unwrap();
        let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
        assert_eq!(wrong.map(|i| (i, defs.vars[i].clone())), None);

        let with = demand(&shape, &defs).unwrap();
        assert_eq!(
            (with.triples, with.randoms),
            (plain.count.triples, plain.count.randoms)
        );
        let (bare, _, bare_defs) = byte_lookup_recorded(&secret, false);
        let without = demand(&bare, &bare_defs).unwrap();
        assert_eq!(with.triples - without.triples, 6 * 302);
        assert_eq!(with.randoms - without.randoms, 6 * 48);
        std::println!(
            "rounds with lookups {} without {}",
            with.rounds,
            without.rounds
        );
        assert!(with.rounds <= without.rounds + 14);
    }

    /// A table that is not a range table is refused by name.
    #[test]
    fn a_lookup_into_a_table_that_is_not_a_range_is_refused() {
        let mut cs = ConstraintSystem::new_recording();
        let bits = alloc_bits(&mut cs, &[5]);
        let table = cs.table(1, vec![f(5), f(9)]);
        cs.enforce_in_table(table, &[pack_bits(&bits)]);
        let (shape, _, defs) = cs.finish_recorded();
        assert_eq!(
            demand(&shape, &defs).err(),
            Some(WitgenError::Table { lookup: 0 })
        );
    }

    /// From shares of the secret to a proof of a relation with lookups that the split
    /// verifier accepts; a wrong message during it makes the honest custodians abort.
    #[test]
    fn a_quorum_proves_a_relation_with_lookups_from_shares_of_its_inputs() {
        use super::super::prover::{prove_party, prover_demand};
        use qsag_agg::zk_hem::v2::params::Profile;
        use qsag_agg::zk_hem::v2::protocol::verify_split;
        let regime = Profile::default();
        let secret = [0x31, 0x07, 0xe0, 0x31];
        let (shape, assignment, defs) = byte_lookup_recorded(&secret, true);
        let publics = assignment[1..=shape.num_public].to_vec();
        let need = demand(&shape, &defs).unwrap();
        let prove = prover_demand(&shape, regime).unwrap();
        for (idx, fault) in [None, Some(2 * need.rounds / 3)].into_iter().enumerate() {
            let mut dealer = Dealer::new(3, &[11 + idx as u8; 32]);
            let inputs = deal_bits(&mut dealer, 3, &secret);
            let preps = dealer.preprocessing(need.triples + prove.0, need.randoms + prove.1);
            let out = run_engines(preps, fault, |e| {
                let z = generate(e, &shape, &defs, &publics, &[inputs[e.me()].clone()])
                    .map_err(|e| std::format!("{e:?}"))?;
                prove_party(e, &shape, &publics, b"lookups", regime, z)
                    .map_err(|e| std::format!("{e:?}"))
            });
            match fault {
                None => {
                    let proof = out[0].0.clone().unwrap();
                    assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(&proof)));
                    assert!(
                        proof.profile == regime
                            && verify_split(&shape, &publics, b"lookups", regime, &proof)
                    );
                    let mut other = publics.clone();
                    other[0] += F::ONE;
                    assert!(!verify_split(&shape, &other, b"lookups", regime, &proof));
                }
                Some(_) => assert!(out[0].0.is_err() && out[2].0.is_err(), "{:?}", out[0].0),
            }
        }
    }

    /// A transport that flips one bit of its `at`-th outgoing message.
    struct Faulty<T> {
        inner: T,
        sent: usize,
        at: usize,
    }

    impl<T: Transport> Transport for Faulty<T> {
        fn parties(&self) -> usize {
            self.inner.parties()
        }
        fn me(&self) -> usize {
            self.inner.me()
        }
        fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError> {
            self.sent += 1;
            if self.sent - 1 == self.at && !payload.is_empty() {
                let mut wrong = payload.to_vec();
                wrong[0] ^= 1;
                return self.inner.send(to, &wrong);
            }
            self.inner.send(to, payload)
        }
        fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError> {
            self.inner.recv(from)
        }
    }

    /// Every custodian on its own thread; custodian 1 flips a bit of its `fault`-th
    /// message. Returns each custodian's result with its round count.
    fn run_engines<R: Send>(
        preps: Vec<Preprocessing>,
        fault: Option<usize>,
        party: impl Fn(&mut Engine<Faulty<Framed<ChannelLink>>>) -> R + Sync,
    ) -> Vec<(R, u64)> {
        let session = [4u8; 32];
        let mesh = channel_mesh(session, preps.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = mesh
                .into_iter()
                .zip(preps)
                .enumerate()
                .map(|(p, (net, prep))| {
                    let party = &party;
                    scope.spawn(move || {
                        let net = Faulty {
                            inner: net,
                            sent: 0,
                            at: fault.filter(|_| p == 1).unwrap_or(usize::MAX),
                        };
                        let mut e = Engine::new(net, prep, &session, &[p as u8 + 50; 32]);
                        let out = party(&mut e);
                        (out, e.stats.rounds)
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }

    fn deal_bits(dealer: &mut Dealer, parties: usize, secret: &[u8]) -> Vec<Vec<Sb>> {
        let mut out = vec![Vec::new(); parties];
        for i in 0..8 * secret.len() {
            let bit = f(u64::from((secret[i / 8] >> (i % 8)) & 1));
            for (p, s) in dealer.share(bit).into_iter().enumerate() {
                out[p].push(s);
            }
        }
        out
    }

    #[test]
    fn custodians_compute_the_assignment_on_shares() {
        let secret = [0xa7, 0x3c, 0xf1, 0x5e];
        let (shape, assignment, defs) = small_recorded(&secret);
        assert!(shape.is_satisfied(&assignment));
        assert_eq!(defs.undefined(), Vec::<usize>::new());
        let need = demand(&shape, &defs).unwrap();
        let publics = assignment[1..=shape.num_public].to_vec();
        for parties in [2usize, 3] {
            let mut dealer = Dealer::new(parties, &[parties as u8; 32]);
            let inputs = deal_bits(&mut dealer, parties, &secret);
            let preps = dealer.preprocessing(need.triples, need.randoms);
            let out = run_engines(preps, None, |e| {
                let z = generate(e, &shape, &defs, &publics, &[inputs[e.me()].clone()]).unwrap();
                assert_eq!(e.remaining(), (0, 0), "demand is exact");
                assert!(!e.has_pending());
                z
            });
            for i in 0..shape.mask_var_base {
                let value = out.iter().fold(F::ZERO, |acc, (z, _)| acc + z[i].v);
                assert_eq!(value, assignment[i], "variable {i}");
            }
            // A single custodian's shares of the secret's bits are not the bits.
            let first = 1 + shape.num_public;
            let own = (first..first + 32)
                .filter(|&i| out[1].0[i].v == assignment[i])
                .count();
            assert_eq!(own, 0);
        }
    }

    #[test]
    fn a_wrong_message_makes_every_honest_custodian_abort_at_the_same_point() {
        let need = {
            let (shape, _, defs) = small_recorded(&[1, 2, 3, 4]);
            demand(&shape, &defs).unwrap()
        };
        // Message indices of custodian 1 (two peers, so two sends a round) spread over
        // the run: random-bit squares, masked openings, Beaver openings, check rounds.
        let total = 2 * need.rounds;
        let mut aborted = 0;
        for (at_idx, at) in [
            0,
            1,
            2,
            5,
            40,
            41,
            total / 7,
            total / 3,
            total / 2,
            total - total / 5,
        ]
        .into_iter()
        .enumerate()
        {
            let mut rounds = Vec::new();
            for secret in [[0xa7, 0x3c, 0xf1, 0x5e], [0x19, 0x80, 0x02, 0xff]] {
                let (shape, assignment, defs) = small_recorded(&secret);
                let publics = assignment[1..=shape.num_public].to_vec();
                let mut dealer = Dealer::new(3, &[70 + at_idx as u8; 32]);
                let inputs = deal_bits(&mut dealer, 3, &secret);
                let preps = dealer.preprocessing(need.triples, need.randoms);
                let session = [4u8; 32];
                let mesh = channel_mesh(session, preps.len());
                let out: Vec<_> = std::thread::scope(|scope| {
                    let handles: Vec<_> = mesh
                        .into_iter()
                        .zip(preps)
                        .enumerate()
                        .map(|(p, (net, prep))| {
                            let (shape, defs, publics, inputs) = (&shape, &defs, &publics, &inputs);
                            scope.spawn(move || {
                                let net = Faulty {
                                    inner: net,
                                    sent: 0,
                                    at: if p == 1 { at } else { usize::MAX },
                                };
                                let mut e = Engine::new_for_obliviousness_test(
                                    net,
                                    prep,
                                    &session,
                                    &[p as u8 + 50; 32],
                                );
                                let res =
                                    generate(&mut e, shape, defs, publics, &[inputs[p].clone()])
                                        .map(|_| ());
                                (res, e.stats.rounds)
                            })
                        })
                        .collect();
                    handles.into_iter().map(|h| h.join().unwrap()).collect()
                });
                for p in [0, 2] {
                    assert!(
                        matches!(out[p].0, Err(WitgenError::Mpc(_))),
                        "message {at}: custodian {p} got {:?}",
                        out[p].0
                    );
                }
                // The custodian that detects the fault first; the other may only see it
                // leave.
                let closed = |r: &Result<(), WitgenError>| {
                    matches!(r, Err(WitgenError::Mpc(MpcError::Net(_))))
                };
                let first = if closed(&out[0].0) || (!closed(&out[2].0) && out[2].1 < out[0].1) {
                    2
                } else {
                    0
                };
                assert!(!closed(&out[first].0));
                rounds.push((out[first].1, out[first].0));
            }
            // Where and how the fault is detected does not depend on the secret.
            assert_eq!(rounds[0], rounds[1], "message {at}");
            aborted += 1;
        }
        assert_eq!(aborted, 10);
    }

    #[test]
    fn a_wrong_input_share_is_caught_before_the_assignment_is_used() {
        let secret = [0xa7, 0x3c, 0xf1, 0x5e];
        let (shape, assignment, defs) = small_recorded(&secret);
        let need = demand(&shape, &defs).unwrap();
        let publics = assignment[1..=shape.num_public].to_vec();
        let mut dealer = Dealer::new(3, &[8; 32]);
        let inputs = deal_bits(&mut dealer, 3, &secret);
        let preps = dealer.preprocessing(need.triples, need.randoms);
        let out = run_engines(preps, None, |e| {
            let mut mine = inputs[e.me()].clone();
            if e.me() == 1 {
                // A different value under the old MAC share.
                mine[9].v += F::ONE;
            }
            generate(e, &shape, &defs, &publics, &[mine]).map(|_| ())
        });
        for (result, _) in &out {
            assert_eq!(*result, Err(WitgenError::Mpc(MpcError::MacCheck)));
        }
    }
}
