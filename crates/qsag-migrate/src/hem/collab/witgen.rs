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
//!   as restated in `paperbin/2020-edabits-mixed-arithmetic-binary-338`, Section 2); `a^2`
//!   is uniform over the squares whatever `b` is.
//! * **Bit decomposition** of a shared `x < 2^m` ([`Witgen::decompose`]). The mask is a
//!   value whose bits are shared random bits, which is what an edaBit is
//!   (`2020-edabits-mixed-arithmetic-binary-338`, Section 3; here both halves live in the
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
//!     `paperbin/2021-rabbit-efficient-comparison-119` (Section 4.1, "LTC"), specialised to
//!     this prime; no slack, so it is exact for every `x < p`.
//! * **Integers.** An integer is a polynomial in `2^8` whose coefficients are shares with
//!   public intervals. [`Witgen::normalize`] turns it into bits by a carry chain, one
//!   decomposition per coefficient. Products of two such integers are computed at as many
//!   points as the product has coefficients and interpolated ([`Witgen::poly_mul`]), one
//!   secure product per coefficient.
//! * **Reduction modulo a public prime** `q` ([`Witgen::canonical`]): bits of the integer
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
//! `den rho + q S + K q` of a division. The first four are functions of fresh
//! preprocessed values alone or are masked by one. The last two are masked only when the
//! shared value behind them is the one the protocol defines, so [`Backend::check`] (the
//! batch MAC check) runs before the round that carries one of them: a custodian that
//! sent a wrong share in any earlier round is caught there, before a value that its
//! error could have steered is opened. The other requests of that same round do no
//! harm: a shared value is fixed by the rounds before the one that opens it, so a
//! custodian that sends last in a round can change what is reconstructed in that round
//! and nothing that is opened in it. That ordering is this module's own argument; the engine's guarantee it rests on
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
//!   aborted: [`Source::Slope`] carries the tangent, and [`Witgen::slope`] tests the
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
//! * [`Witgen::normalize`] decomposes every coefficient on its own, in the same rounds,
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
