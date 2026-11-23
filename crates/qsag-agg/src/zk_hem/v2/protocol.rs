//! zk-Hem v2 for a [`Shape`] closed by [`ConstraintSystem::finish_v2`] or
//! [`ConstraintSystem::finish_recorded`] (SECURITY.md, section V2).
//!
//! Supports:
//! * Single-prover proofs ([`ZkHemV2Proof`], magic `QSAGZKH2`) with per-tree 256-bit
//!   `tree_nonce` and optional LogUp lookup arguments ([`LookupV2Proof`]).
//! * Split-share collaborative proofs ([`ZkHemV2SplitProof`], magic `QSAGZKS2`) across
//!   `1..=MAX_STAGE0_SHARES` additive Stage-0 roots.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use super::field5::Fp5;
use super::hash::{Channel, Digest, Transcript};
use super::params::{
    COL_DEGREE, COL_MASK_BITS, DIGEST_BYTES, EXT_BYTES, LIMBS, LOOKUP_DEGREE, LOOKUP_MASK_BITS,
    Layout, LookupLayout, PAD_VARS, Profile, ROW_DEGREE, ROW_MASK_BITS, ShapeSize,
    TREE_NONCE_BYTES,
};
use super::pcs::{
    self, MAX_STAGE0_SHARES, Opening, SplitOpening, TensorTerm, par_chunk, par_chunks_mut, par_sum,
};
use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::pcs::hypercube_to_monomial_coeffs;
use crate::sponge::cshake256_32;
use crate::zk_hem::SeedStream;
use crate::zk_hem::relation::{Closing, Lookups, Shape};
use qsag_core::wipe::SecretBuffer;

type E = Fp5;
type F = Goldilocks;

/// First bytes of every serialized single-prover v2 proof.
pub const MAGIC: [u8; 8] = *b"QSAGZKH2";
/// First bytes of every serialized split-share collaborative v2 proof.
pub const MAGIC_SPLIT: [u8; 8] = *b"QSAGZKS2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkHemV2Error {
    /// The assignment does not satisfy the relation.
    Unsatisfied,
    /// The relation was not closed for v2, or it does not fit a v2 table.
    UnsupportedRelation,
    /// The verifier's coins fell outside the event Good; retry with a new seed.
    MaskRankDeficient,
    /// The public pole challenge equals a checked compressed tuple. Retry with a fresh seed.
    LookupPoleHit,
}

/// The table layout of a v2 relation, including any [`Lookups`].
pub fn layout_of(shape: &Shape) -> Option<Layout> {
    if shape.closing() != Closing::V2 || shape.log_rows < 5 {
        return None;
    }
    let layout = Layout::with_lookup(
        ShapeSize {
            log_rows: shape.log_rows,
            num_vars: shape.num_vars,
            num_public: shape.num_public,
        },
        shape.lookups().map(|l| l.log_entries),
    )?;
    pcs::stage_dims(layout.log_cells, &layout.schedule)?;
    if let Some(ll) = &layout.lookup {
        pcs::stage_dims(ll.log_cells, &ll.schedule)?;
    }
    Some(layout)
}

/// Optional LogUp lookup subproof inside [`ZkHemV2Proof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupV2Proof {
    pub helper_tree_nonce: [u8; TREE_NONCE_BYTES],
    pub helper_root: Digest,
    pub mask_sum: E,
    pub rounds: Vec<Vec<E>>,
    pub values: [E; 3],
    pub opening: Opening,
}

/// Optional LogUp lookup subproof inside [`ZkHemV2SplitProof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitLookupV2Proof {
    pub helper_tree_nonces: Vec<[u8; TREE_NONCE_BYTES]>,
    pub helper_roots: Vec<Digest>,
    pub mask_sum: E,
    pub rounds: Vec<Vec<E>>,
    pub values: [E; 3],
    pub opening: SplitOpening,
}

/// A single-prover zk-Hem v2 proof (`QSAGZKH2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkHemV2Proof {
    pub profile: Profile,
    pub log_cells: u8,
    pub tree_nonce: [u8; TREE_NONCE_BYTES],
    pub root: Digest,
    pub lookup: Option<LookupV2Proof>,
    pub row_mask_sum: E,
    pub row_rounds: Vec<Vec<E>>,
    pub row_values: [E; 3],
    pub col_mask_sum: E,
    pub col_rounds: Vec<Vec<E>>,
    pub opening: Opening,
}

/// A split-share collaborative zk-Hem v2 proof (`QSAGZKS2`) across `1..=MAX_STAGE0_SHARES`
/// additive Stage-0 commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkHemV2SplitProof {
    pub profile: Profile,
    pub log_cells: u8,
    pub tree_nonces: Vec<[u8; TREE_NONCE_BYTES]>,
    pub roots: Vec<Digest>,
    pub lookup: Option<SplitLookupV2Proof>,
    pub row_mask_sum: E,
    pub row_rounds: Vec<Vec<E>>,
    pub row_values: [E; 3],
    pub col_mask_sum: E,
    pub col_rounds: Vec<Vec<E>>,
    pub opening: SplitOpening,
}

impl ZkHemV2Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&MAGIC);
        out.push(self.profile.wire_tag());
        out.push(self.log_cells);
        out.extend_from_slice(&self.tree_nonce);
        out.extend_from_slice(&self.root);
        let push = |out: &mut Vec<u8>, v: &E| out.extend_from_slice(&v.to_le_bytes());
        if let Some(lp) = &self.lookup {
            out.extend_from_slice(&lp.helper_tree_nonce);
            out.extend_from_slice(&lp.helper_root);
            push(&mut out, &lp.mask_sum);
            lp.rounds.iter().flatten().for_each(|v| push(&mut out, v));
            lp.values.iter().for_each(|v| push(&mut out, v));
        }
        push(&mut out, &self.row_mask_sum);
        self.row_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.row_values.iter().for_each(|v| push(&mut out, v));
        push(&mut out, &self.col_mask_sum);
        self.col_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.opening.push_bytes(&mut out);
        if let Some(lp) = &self.lookup {
            lp.opening.push_bytes(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], shape: &Shape) -> Option<Self> {
        let layout = layout_of(shape)?;
        if bytes.get(..8)? != MAGIC {
            return None;
        }
        let profile = Profile::from_wire_tag(*bytes.get(8)?)?;
        let log_cells = *bytes.get(9)?;
        if usize::from(log_cells) != layout.log_cells {
            return None;
        }
        let mut pos = 10usize;
        let take_nonce = |pos: &mut usize| -> Option<[u8; TREE_NONCE_BYTES]> {
            let chunk = bytes.get(*pos..*pos + TREE_NONCE_BYTES)?.try_into().ok()?;
            *pos += TREE_NONCE_BYTES;
            Some(chunk)
        };
        let take_root = |pos: &mut usize| -> Option<Digest> {
            let chunk = bytes.get(*pos..*pos + DIGEST_BYTES)?.try_into().ok()?;
            *pos += DIGEST_BYTES;
            Some(chunk)
        };
        let take = |pos: &mut usize| -> Option<E> {
            let chunk: [u8; EXT_BYTES] = bytes.get(*pos..*pos + EXT_BYTES)?.try_into().ok()?;
            *pos += EXT_BYTES;
            E::from_le_bytes_canonical(chunk)
        };
        let rounds = |pos: &mut usize, n: usize, d: usize| -> Option<Vec<Vec<E>>> {
            (0..n)
                .map(|_| (0..=d).map(|_| take(pos)).collect())
                .collect()
        };
        let tree_nonce = take_nonce(&mut pos)?;
        let root = take_root(&mut pos)?;
        let lookup_front = if let Some(ll) = &layout.lookup {
            let helper_tree_nonce = take_nonce(&mut pos)?;
            let helper_root = take_root(&mut pos)?;
            let mask_sum = take(&mut pos)?;
            let lk_rounds = rounds(&mut pos, ll.log_entries, LOOKUP_DEGREE)?;
            let values = [take(&mut pos)?, take(&mut pos)?, take(&mut pos)?];
            Some((helper_tree_nonce, helper_root, mask_sum, lk_rounds, values))
        } else {
            None
        };
        let row_mask_sum = take(&mut pos)?;
        let row_rounds = rounds(&mut pos, shape.log_rows, ROW_DEGREE)?;
        let row_values = [take(&mut pos)?, take(&mut pos)?, take(&mut pos)?];
        let col_mask_sum = take(&mut pos)?;
        let col_rounds = rounds(&mut pos, layout.var_bits, COL_DEGREE)?;
        let opening = Opening::read(bytes, &mut pos, layout.log_cells, &layout.schedule)?;
        let lookup = match (lookup_front, &layout.lookup) {
            (Some((helper_tree_nonce, helper_root, mask_sum, lk_rounds, values)), Some(ll)) => {
                let h_open = Opening::read(bytes, &mut pos, ll.log_cells, &ll.schedule)?;
                Some(LookupV2Proof {
                    helper_tree_nonce,
                    helper_root,
                    mask_sum,
                    rounds: lk_rounds,
                    values,
                    opening: h_open,
                })
            }
            (None, None) => None,
            _ => return None,
        };
        (pos == bytes.len()).then_some(Self {
            profile,
            log_cells,
            tree_nonce,
            root,
            lookup,
            row_mask_sum,
            row_rounds,
            row_values,
            col_mask_sum,
            col_rounds,
            opening,
        })
    }
}

impl ZkHemV2SplitProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&MAGIC_SPLIT);
        out.push(self.profile.wire_tag());
        out.push(self.log_cells);
        out.push(self.roots.len() as u8);
        for (nonce, root) in self.tree_nonces.iter().zip(&self.roots) {
            out.extend_from_slice(nonce);
            out.extend_from_slice(root);
        }
        let push = |out: &mut Vec<u8>, v: &E| out.extend_from_slice(&v.to_le_bytes());
        if let Some(lp) = &self.lookup {
            for (nonce, root) in lp.helper_tree_nonces.iter().zip(&lp.helper_roots) {
                out.extend_from_slice(nonce);
                out.extend_from_slice(root);
            }
            push(&mut out, &lp.mask_sum);
            lp.rounds.iter().flatten().for_each(|v| push(&mut out, v));
            lp.values.iter().for_each(|v| push(&mut out, v));
        }
        push(&mut out, &self.row_mask_sum);
        self.row_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.row_values.iter().for_each(|v| push(&mut out, v));
        push(&mut out, &self.col_mask_sum);
        self.col_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.opening.push_bytes(&mut out);
        if let Some(lp) = &self.lookup {
            lp.opening.push_bytes(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], shape: &Shape) -> Option<Self> {
        let layout = layout_of(shape)?;
        if bytes.get(..8)? != MAGIC_SPLIT {
            return None;
        }
        let profile = Profile::from_wire_tag(*bytes.get(8)?)?;
        let log_cells = *bytes.get(9)?;
        let committers = usize::from(*bytes.get(10)?);
        if usize::from(log_cells) != layout.log_cells
            || !(1..=MAX_STAGE0_SHARES).contains(&committers)
        {
            return None;
        }
        let mut pos = 11usize;
        let take_nonce = |pos: &mut usize| -> Option<[u8; TREE_NONCE_BYTES]> {
            let chunk = bytes.get(*pos..*pos + TREE_NONCE_BYTES)?.try_into().ok()?;
            *pos += TREE_NONCE_BYTES;
            Some(chunk)
        };
        let take_root = |pos: &mut usize| -> Option<Digest> {
            let chunk = bytes.get(*pos..*pos + DIGEST_BYTES)?.try_into().ok()?;
            *pos += DIGEST_BYTES;
            Some(chunk)
        };
        let take = |pos: &mut usize| -> Option<E> {
            let chunk: [u8; EXT_BYTES] = bytes.get(*pos..*pos + EXT_BYTES)?.try_into().ok()?;
            *pos += EXT_BYTES;
            E::from_le_bytes_canonical(chunk)
        };
        let rounds = |pos: &mut usize, n: usize, d: usize| -> Option<Vec<Vec<E>>> {
            (0..n)
                .map(|_| (0..=d).map(|_| take(pos)).collect())
                .collect()
        };
        let mut tree_nonces = Vec::with_capacity(committers);
        let mut roots = Vec::with_capacity(committers);
        for _ in 0..committers {
            tree_nonces.push(take_nonce(&mut pos)?);
            roots.push(take_root(&mut pos)?);
        }
        let lookup_front = if let Some(ll) = &layout.lookup {
            let mut helper_tree_nonces = Vec::with_capacity(committers);
            let mut helper_roots = Vec::with_capacity(committers);
            for _ in 0..committers {
                helper_tree_nonces.push(take_nonce(&mut pos)?);
                helper_roots.push(take_root(&mut pos)?);
            }
            let mask_sum = take(&mut pos)?;
            let lk_rounds = rounds(&mut pos, ll.log_entries, LOOKUP_DEGREE)?;
            let values = [take(&mut pos)?, take(&mut pos)?, take(&mut pos)?];
            Some((
                helper_tree_nonces,
                helper_roots,
                mask_sum,
                lk_rounds,
                values,
            ))
        } else {
            None
        };
        let row_mask_sum = take(&mut pos)?;
        let row_rounds = rounds(&mut pos, shape.log_rows, ROW_DEGREE)?;
        let row_values = [take(&mut pos)?, take(&mut pos)?, take(&mut pos)?];
        let col_mask_sum = take(&mut pos)?;
        let col_rounds = rounds(&mut pos, layout.var_bits, COL_DEGREE)?;
        let opening =
            SplitOpening::read(bytes, &mut pos, layout.log_cells, &layout.schedule, committers)?;
        let lookup = match (lookup_front, &layout.lookup) {
            (
                Some((helper_tree_nonces, helper_roots, mask_sum, lk_rounds, values)),
                Some(ll),
            ) => {
                let h_open =
                    SplitOpening::read(bytes, &mut pos, ll.log_cells, &ll.schedule, committers)?;
                Some(SplitLookupV2Proof {
                    helper_tree_nonces,
                    helper_roots,
                    mask_sum,
                    rounds: lk_rounds,
                    values,
                    opening: h_open,
                })
            }
            (None, None) => None,
            _ => return None,
        };
        (pos == bytes.len()).then_some(Self {
            profile,
            log_cells,
            tree_nonces,
            roots,
            lookup,
            row_mask_sum,
            row_rounds,
            row_values,
            col_mask_sum,
            col_rounds,
            opening,
        })
    }
}

// ============================================================================
// Shared algebra & Good-event predicates
// ============================================================================

pub fn limb_basis() -> [E; LIMBS] {
    core::array::from_fn(|j| {
        let mut limbs = [F::ZERO; LIMBS];
        limbs[j] = F::ONE;
        E::from_limbs(limbs)
    })
}

#[inline]
fn eval_poly(coeffs: &[E], x: E) -> E {
    coeffs.iter().rev().fold(E::ZERO, |acc, &c| acc * x + c)
}

fn eq_eval(a: &[E], b: &[E]) -> E {
    a.iter().zip(b).fold(E::ONE, |acc, (&x, &y)| {
        let xy = x * y;
        acc * (xy + xy + E::ONE - x - y)
    })
}

pub fn eq_table(point: &[E]) -> Vec<E> {
    let serial = |point: &[E]| {
        let mut table = vec![E::ZERO; 1 << point.len()];
        table[0] = E::ONE;
        for (j, &r) in point.iter().enumerate() {
            let (lo, hi) = table[..2 << j].split_at_mut(1 << j);
            for (l, h) in lo.iter_mut().zip(hi) {
                *h = *l * r;
                *l -= *h;
            }
        }
        table
    };
    let mut table = vec![E::ZERO; 1 << point.len()];
    let rows = par_chunk(table.len());
    if rows >= table.len() {
        return serial(point);
    }
    let split = point.len() / 2;
    let (low, high) = (serial(&point[..split]), serial(&point[split..]));
    let per_job = rows.div_ceil(low.len()) * low.len();
    par_chunks_of(&mut table, per_job, |off, part| {
        for (block, &h) in part.chunks_mut(low.len()).zip(&high[off / low.len()..]) {
            for (slot, &l) in block.iter_mut().zip(&low) {
                *slot = h * l;
            }
        }
    });
    table
}

fn par_chunks_of(data: &mut [E], chunk: usize, f: impl Fn(usize, &mut [E]) + Sync) {
    #[cfg(feature = "std")]
    {
        std::thread::scope(|scope| {
            for (k, part) in data.chunks_mut(chunk).enumerate() {
                let f = &f;
                crate::spawn_bounded(scope, move || f(k * chunk, part));
            }
        });
    }
    #[cfg(not(feature = "std"))]
    for (k, part) in data.chunks_mut(chunk).enumerate() {
        f(k * chunk, part);
    }
}

fn eq_index(point: &[E], index: usize) -> E {
    point.iter().enumerate().fold(E::ONE, |acc, (j, &r)| {
        acc * if (index >> j) & 1 == 1 { r } else { E::ONE - r }
    })
}

fn prefix_indicator(point: &[E], count: usize) -> E {
    if count >> point.len() != 0 {
        return E::ONE;
    }
    let mut acc = E::ZERO;
    let mut prefix = E::ONE;
    for (j, &r) in point.iter().enumerate().rev() {
        if (count >> j) & 1 == 1 {
            acc += prefix * (E::ONE - r);
            prefix *= r;
        } else {
            prefix *= E::ONE - r;
        }
    }
    acc
}

#[inline]
fn row_gate(s: E, a: E, b: E, c: E) -> E {
    let a2 = a.square();
    let a7 = a2.square() * a2 * a;
    let ab = a * b;
    s * (a7 - ab) + ab - c
}

#[inline]
fn lookup_gate(sel: E, eq: E, alpha: E, lambda: E, [n, v, h]: [E; 3]) -> E {
    sel * (h + lambda * eq * (h * (alpha - v) - n))
}

fn pow2(n: usize) -> E {
    (0..n).fold(E::ONE, |acc, _| acc + acc)
}

fn pow2_coords(x: E, bits: usize) -> Vec<E> {
    let mut out = Vec::with_capacity(bits);
    let mut cur = x;
    for _ in 0..bits {
        out.push(cur);
        cur = cur.square();
    }
    out
}

pub(crate) fn evals_to_coeffs(evals: &[E]) -> Vec<E> {
    let n = evals.len();
    let mut dd = evals.to_vec();
    for j in 1..n {
        let inv = F::from_u64_reduced(j as u64).inv();
        for i in (j..n).rev() {
            dd[i] = (dd[i] - dd[i - 1]).mul_base(inv);
        }
    }
    let mut out = vec![E::ZERO; n];
    for i in (0..n).rev() {
        let node = F::from_u64_reduced(i as u64);
        for k in (1..n).rev() {
            out[k] = out[k - 1] - out[k].mul_base(node);
        }
        out[0] = dd[i] - out[0].mul_base(node);
    }
    qsag_asm::volatile_fill(&mut dd, E::ZERO);
    out
}

pub fn pad_basis_det(rx: &[E]) -> F {
    let weights: [E; LIMBS] = core::array::from_fn(|c| eq_index(&rx[..3], c));
    let mut m: [[F; LIMBS]; LIMBS] =
        core::array::from_fn(|row| core::array::from_fn(|col| weights[col].to_limbs()[row]));
    let mut det = F::ONE;
    for col in 0..LIMBS {
        let Some(pivot) = (col..LIMBS).find(|&row| !m[row][col].is_zero()) else {
            return F::ZERO;
        };
        if pivot != col {
            m.swap(col, pivot);
            det = -det;
        }
        det *= m[col][col];
        let inv = m[col][col].inv();
        let pivot_row = m[col];
        for row in m.iter_mut().skip(col + 1) {
            let factor = row[col] * inv;
            for (cell, p) in row.iter_mut().zip(pivot_row) {
                *cell -= factor * p;
            }
        }
    }
    det
}

pub fn pad_basis_exists(rx: &[E]) -> bool {
    rx.len() >= 3 && !pad_basis_det(rx).is_zero()
}

fn corner_factor(rx: &[E], base: usize) -> E {
    rx.iter().enumerate().skip(3).fold(E::ONE, |acc, (j, &r)| {
        acc * if (base >> j) & 1 == 1 { r } else { E::ONE - r }
    })
}

/// Condition (G1): the 15 masking rows make `(Az, Bz, Cz)(rx)` uniform.
pub fn row_challenge_good(shape: &Shape, rx: &[E]) -> bool {
    pad_basis_exists(rx) && (0..3).all(|g| !corner_factor(rx, shape.mask_row_base(g)).is_zero())
}

/// Over F, each of the two independent five-pad groups spans E exactly when
/// the five corner weights form a basis. In these E coordinates the minor
/// for (n,v,h) is diagonal: k, k, eq_rl[base]. The third coordinate is
/// one free extension-field helper entry. See SECURITY.md V2.11.
pub fn lookup_masks_full_rank(lookups: &Lookups, rl: &[E]) -> bool {
    if rl.len() != lookups.log_entries || !pad_basis_exists(rl) {
        return false;
    }
    let base = lookups.mask_entry_base();
    let k = corner_factor(rl, base);
    !(k.square() * eq_index(rl, base)).is_zero()
}

// ============================================================================
// Coins and masks
// ============================================================================

struct Coins(SeedStream);

impl Coins {
    fn new(
        profile: Profile,
        shape: &Shape,
        layout: &Layout,
        statement: &[u8],
        assignment: &[F],
        seed: &[u8; 32],
    ) -> Self {
        // Both buffers hold secrets (the seed, the witness) and are sized up front: growing
        // one would free its old storage unwiped.
        let layout = layout_bytes(shape, layout);
        let mut input = Vec::with_capacity(seed.len() + 1 + 32 + layout.len() + 32 + 32);
        input.extend_from_slice(seed);
        input.push(profile.wire_tag());
        input.extend_from_slice(&shape.digest());
        input.extend_from_slice(&layout);
        input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM2.COINS.STMT/v1", statement));
        let mut witness: Vec<u8> = Vec::with_capacity(8 * assignment.len());
        for v in assignment {
            witness.extend_from_slice(&v.to_le_bytes());
        }
        let mut witness_digest = cshake256_32(b"QSAG.ZKHEM2.COINS.WIT/v1", &witness);
        qsag_asm::volatile_fill(&mut witness, 0u8);
        input.extend_from_slice(&witness_digest);
        qsag_asm::volatile_fill(&mut witness_digest, 0u8);
        let mut coin_seed = cshake256_32(b"QSAG.ZKHEM2.COINS.SEED/v1", &input);
        qsag_asm::volatile_fill(&mut input, 0u8);
        let stream = SeedStream::new(b"QSAG.ZKHEM2.COINS/v1", &coin_seed);
        qsag_asm::volatile_fill(&mut coin_seed, 0u8);
        Self(stream)
    }

    fn fill_base(&mut self, out: &mut [F]) {
        self.0.fill_base(out);
    }

    fn next_fp5(&mut self) -> E {
        self.0.next_fp5()
    }

    fn next_bytes32(&mut self) -> [u8; 32] {
        self.0.next_bytes32()
    }
}

/// A separable mask `g(x) = sum_i u_i(x_i)`, `u_i(X) = sum_k coef[i][k] X^k`.
pub struct Mask {
    coef: Vec<Vec<E>>,
}

impl Mask {
    pub fn from_coeffs(coef: Vec<Vec<E>>) -> Self {
        Self { coef }
    }

    fn sample(coins: &mut Coins, rounds: usize, degree: usize) -> Self {
        let coef = (0..rounds)
            .map(|_| (0..=degree).map(|_| coins.next_fp5()).collect())
            .collect();
        Self { coef }
    }

    fn unit_sum(&self, i: usize) -> E {
        self.coef[i].iter().fold(self.coef[i][0], |acc, &c| acc + c)
    }

    pub fn sum(&self) -> E {
        let n = self.coef.len();
        pow2(n - 1) * (0..n).fold(E::ZERO, |acc, i| acc + self.unit_sum(i))
    }

    pub fn eval(&self, point: &[E]) -> E {
        self.coef
            .iter()
            .zip(point)
            .fold(E::ZERO, |acc, (u, &c)| acc + eval_poly(u, c))
    }

    pub fn round_poly(&self, prefix: &[E]) -> Vec<E> {
        let (i, n) = (prefix.len(), self.coef.len());
        let free = n - i - 1;
        let scale = pow2(free);
        let mut out: Vec<E> = self.coef[i].iter().map(|&c| scale * c).collect();
        out[0] += scale * self.eval(prefix);
        if free > 0 {
            out[0] += pow2(free - 1) * (i + 1..n).fold(E::ZERO, |acc, j| acc + self.unit_sum(j));
        }
        out
    }

    fn write(&self, cells: &mut [F], bits: usize, block: impl Fn(usize, usize) -> usize) {
        for (i, row) in self.coef.iter().enumerate() {
            for j in 0..LIMBS {
                let mut m = vec![F::ZERO; 1 << bits];
                for (slot, c) in m.iter_mut().zip(row) {
                    *slot = c.to_limbs()[j];
                }
                for b in 0..bits {
                    for idx in 0..m.len() {
                        if (idx >> b) & 1 == 1 {
                            let lower = m[idx ^ (1 << b)];
                            m[idx] += lower;
                        }
                    }
                }
                let off = block(i, j);
                cells[off..off + m.len()].copy_from_slice(&m);
                qsag_asm::volatile_fill(&mut m, F::ZERO);
            }
        }
    }
}

impl Drop for Mask {
    fn drop(&mut self) {
        for row in &mut self.coef {
            qsag_asm::volatile_fill(row, E::ZERO);
        }
    }
}

struct Secrets {
    table: Vec<F>,
    row_mask: Mask,
    col_mask: Mask,
    mask_poly: Vec<E>,
    salt_seed: [u8; 32],
    tree_nonce: [u8; TREE_NONCE_BYTES],
}

impl Drop for Secrets {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.table, F::ZERO);
        qsag_asm::volatile_fill(&mut self.mask_poly, E::ZERO);
        qsag_asm::volatile_fill(&mut self.salt_seed, 0u8);
    }
}

fn sample_secrets(
    coins: &mut Coins,
    shape: &Shape,
    layout: &Layout,
    assignment: &mut [F],
) -> Secrets {
    coins.fill_base(&mut assignment[shape.mask_var_base..]);
    let cells = 1usize << layout.log_cells;
    let row_mask = Mask::sample(coins, shape.log_rows, ROW_DEGREE);
    let col_mask = Mask::sample(coins, layout.var_bits, COL_DEGREE);
    let mut table = vec![F::ZERO; cells];
    row_mask.write(&mut table, ROW_MASK_BITS, |i, j| {
        layout.row_mask_block(i, j)
    });
    col_mask.write(&mut table, COL_MASK_BITS, |i, j| {
        layout.col_mask_block(shape.log_rows, i, j)
    });
    table[..shape.num_vars].copy_from_slice(assignment);
    coins.fill_base(&mut table[cells - layout.blind_cells..]);
    let step_vars = layout.schedule.stages[0].step_vars;
    let mask_poly = (0..pcs::mask_len(layout.log_cells, step_vars))
        .map(|_| coins.next_fp5())
        .collect();
    let salt_seed = coins.next_bytes32();
    let tree_nonce = coins.next_bytes32();
    Secrets {
        table,
        row_mask,
        col_mask,
        mask_poly,
        salt_seed,
        tree_nonce,
    }
}

// ============================================================================
// Linear functionals (assignment table and helper table)
// ============================================================================

pub struct ClaimInputs<'a> {
    pub layout: &'a Layout,
    pub log_rows: usize,
    pub num_public: usize,
    pub rx: &'a [E],
    pub ry: &'a [E],
    pub lambda: E,
    pub rho2: E,
    pub matrix_at_point: E,
}

impl ClaimInputs<'_> {
    fn powers(&self) -> Vec<E> {
        (0..5 + self.num_public)
            .scan(E::ONE, |acc, _| {
                let cur = *acc;
                *acc *= self.lambda;
                Some(cur)
            })
            .collect()
    }

    fn var_cells(&self) -> usize {
        self.layout.var_cells.min(1 << self.layout.var_bits)
    }
}

fn block_point(block: usize, low: &[E]) -> Vec<E> {
    let mut point = low.to_vec();
    let mut b = low.len();
    while block >> b != 0 {
        point.push(if (block >> b) & 1 == 1 {
            E::ONE
        } else {
            E::ZERO
        });
        b += 1;
    }
    point
}

pub fn claim_terms(inp: &ClaimInputs<'_>) -> Vec<TensorTerm> {
    let basis = limb_basis();
    let lam = inp.powers();
    let k = inp.layout.var_bits;
    let mut terms = Vec::new();
    let mut push = |weight: E, point: Vec<E>| terms.push(TensorTerm { weight, point });
    let row_half = pow2(inp.log_rows - 1);
    let col_half = pow2(k - 1);
    for (j, &limb) in basis.iter().enumerate() {
        for i in 0..inp.log_rows {
            let block = inp.layout.row_mask_block(i, j);
            push(
                lam[0] * row_half * limb,
                block_point(block, &[E::ZERO; ROW_MASK_BITS]),
            );
            push(
                lam[0] * row_half * limb,
                block_point(block, &[E::ONE; ROW_MASK_BITS]),
            );
            push(
                lam[2] * limb,
                block_point(block, &pow2_coords(inp.rx[i], ROW_MASK_BITS)),
            );
        }
        for i in 0..k {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            push(
                lam[1] * col_half * limb,
                block_point(block, &[E::ZERO; COL_MASK_BITS]),
            );
            push(
                lam[1] * col_half * limb,
                block_point(block, &[E::ONE; COL_MASK_BITS]),
            );
            push(
                lam[3] * inp.rho2 * limb,
                block_point(block, &pow2_coords(inp.ry[i], COL_MASK_BITS)),
            );
        }
    }
    let count = inp.var_cells();
    let mut start = 0usize;
    for a in (0..=k).rev() {
        if (count >> a) & 1 == 1 {
            let weight = lam[3] * inp.matrix_at_point * eq_index(&inp.ry[a..], start >> a);
            push(weight, block_point(start, &inp.ry[..a]));
            start += 1 << a;
        }
    }
    for i in 0..=inp.num_public {
        push(lam[4 + i], block_point(i, &[]));
    }
    terms
}

pub fn claim_cell_weights(inp: &ClaimInputs<'_>) -> Vec<E> {
    let basis = limb_basis();
    let lam = inp.powers();
    let k = inp.layout.var_bits;
    let end = inp.layout.col_mask_block(inp.log_rows, k, 0);
    let mut out = vec![E::ZERO; end.next_power_of_two()];
    let row_half = pow2(inp.log_rows - 1);
    let col_half = pow2(k - 1);
    for i in 0..inp.log_rows {
        let eq = eq_table(&pow2_coords(inp.rx[i], ROW_MASK_BITS));
        for (j, &limb) in basis.iter().enumerate() {
            let block = inp.layout.row_mask_block(i, j);
            out[block] += lam[0] * row_half * limb;
            out[block + eq.len() - 1] += lam[0] * row_half * limb;
            for (slot, &e) in out[block..].iter_mut().zip(&eq) {
                *slot += lam[2] * limb * e;
            }
        }
    }
    for i in 0..k {
        let eq = eq_table(&pow2_coords(inp.ry[i], COL_MASK_BITS));
        for (j, &limb) in basis.iter().enumerate() {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            out[block] += lam[1] * col_half * limb;
            out[block + eq.len() - 1] += lam[1] * col_half * limb;
            for (slot, &e) in out[block..].iter_mut().zip(&eq) {
                *slot += lam[3] * inp.rho2 * limb * e;
            }
        }
    }
    let eq = eq_table(inp.ry);
    let scale = lam[3] * inp.matrix_at_point;
    let count = inp.var_cells();
    par_chunks_mut(&mut out[..count], |off, part| {
        for (slot, &e) in part.iter_mut().zip(&eq[off..]) {
            *slot += scale * e;
        }
    });
    for i in 0..=inp.num_public {
        out[i] += lam[4 + i];
    }
    out
}

// Project the eight subset-sum cells of a mask block onto monomials
// 0..=4. The four lower cells encode the multilinear polynomial at
// (x,x²); the quartic coefficient is cell[4] - cell[0]. This also
// bounds the verifier polynomial for *arbitrary* committed cells.
fn lookup_mask_weights(r: E, half: E, batch: E) -> [E; 5] {
    const _: () = assert!(LOOKUP_DEGREE == 4 && LOOKUP_MASK_BITS == 3);
    let r2 = r.square();
    let r4 = r2.square();
    let lo = E::ONE - r;
    let lo2 = E::ONE - r2;
    // u(0)+u(1) = cell[3]+cell[4].
    [
        batch * (lo * lo2 - r4),
        batch * r * lo2,
        batch * lo * r2,
        half + batch * r * r2,
        half + batch * r4,
    ]
}

pub fn lookup_claim_terms(ll: &LookupLayout, rl: &[E], lambda: E) -> Vec<TensorTerm> {
    let half = pow2(ll.log_entries - 1);
    let mut terms = Vec::new();
    for (j, limb) in limb_basis().into_iter().enumerate() {
        for (i, &r) in rl.iter().enumerate() {
            let block = ll.mask_block(i, j);
            for (offset, weight) in lookup_mask_weights(r, half, lambda).into_iter().enumerate() {
                terms.push(TensorTerm {
                    weight: limb * weight,
                    point: block_point(block + offset, &[]),
                });
            }
        }
        terms.push(TensorTerm {
            weight: lambda.square() * limb,
            point: block_point(ll.limb_block(j), rl),
        });
    }
    terms
}

pub fn lookup_claim_cell_weights(ll: &LookupLayout, rl: &[E], lambda: E) -> Vec<E> {
    let d = ll.log_entries;
    let half = pow2(d - 1);
    let end = ll.mask_block(d, 0);
    let mut out = vec![E::ZERO; end.next_power_of_two()];
    let basis = limb_basis();
    for (i, &r) in rl.iter().enumerate() {
        let weights = lookup_mask_weights(r, half, lambda);
        for (j, &limb) in basis.iter().enumerate() {
            let block = ll.mask_block(i, j);
            for (cell, weight) in out[block..].iter_mut().zip(weights) {
                *cell = limb * weight;
            }
        }
    }
    let eq_rl = eq_table(rl);
    for (j, &limb) in basis.iter().enumerate() {
        let block = ll.limb_block(j);
        let scale = lambda.square() * limb;
        for (slot, &e) in out[block..block + eq_rl.len()].iter_mut().zip(&eq_rl) {
            *slot += scale * e;
        }
    }
    out
}

pub fn cell_weights_to_kernel(mut weights: Vec<E>, cells: usize) -> Vec<E> {
    let bits = weights.len().trailing_zeros() as usize;
    let low = bits.min(16);
    let within = |block: &mut [E]| {
        for b in 0..low {
            for idx in 0..block.len() {
                if (idx >> b) & 1 == 0 {
                    let upper = block[idx | (1 << b)];
                    block[idx] += upper;
                }
            }
        }
    };
    let add = |lo: &mut [E], hi: &[E]| {
        for (l, h) in lo.iter_mut().zip(hi) {
            *l += *h;
        }
    };
    #[cfg(feature = "std")]
    {
        let per_job = (par_chunk(weights.len()) >> low).max(1) << low;
        std::thread::scope(|scope| {
            for part in weights.chunks_mut(per_job) {
                let within = &within;
                crate::spawn_bounded(scope, move || part.chunks_mut(1 << low).for_each(within));
            }
        });
        for b in low..bits {
            for chunk in weights.chunks_mut(2 << b) {
                let (lo, hi) = chunk.split_at_mut(1 << b);
                let step = par_chunk(lo.len());
                std::thread::scope(|scope| {
                    for (l, h) in lo.chunks_mut(step).zip(hi.chunks(step)) {
                        let add = &add;
                        crate::spawn_bounded(scope, move || add(l, h));
                    }
                });
            }
        }
    }
    #[cfg(not(feature = "std"))]
    {
        let _ = par_chunk;
        weights.chunks_mut(1 << low).for_each(within);
        for b in low..bits {
            for chunk in weights.chunks_mut(2 << b) {
                let (lo, hi) = chunk.split_at_mut(1 << b);
                add(lo, hi);
            }
        }
    }
    weights.resize(cells, E::ZERO);
    weights
}

fn batched_value(lambda: E, values: &[E]) -> E {
    values
        .iter()
        .rev()
        .fold(E::ZERO, |acc, &v| acc * lambda + v)
}

fn layout_bytes(shape: &Shape, layout: &Layout) -> Vec<u8> {
    let mut out = Vec::new();
    let mut put = |n: usize| out.extend_from_slice(&(n as u64).to_le_bytes());
    for n in [
        shape.log_rows,
        shape.num_vars,
        shape.num_public,
        layout.log_cells,
        layout.var_bits,
        layout.var_cells,
        layout.var_align,
        layout.mask_base,
        layout.blind_cells,
        layout.schedule.early_stop_vars,
        layout.schedule.stages.len(),
    ] {
        put(n);
    }
    for st in &layout.schedule.stages {
        put(st.blowup);
        put(st.step_vars);
        put(st.num_queries);
    }
    if let Some(ll) = &layout.lookup {
        for n in [
            2, // Lookup kernel revision: committed masks are projected to degree four.
            ll.log_cells,
            ll.log_entries,
            ll.blind_cells,
            ll.schedule.early_stop_vars,
            ll.schedule.stages.len(),
        ] {
            put(n);
        }
        for st in &ll.schedule.stages {
            put(st.blowup);
            put(st.step_vars);
            put(st.num_queries);
        }
    }
    out
}

fn encode_roots(nonces: &[[u8; TREE_NONCE_BYTES]], roots: &[Digest]) -> Vec<u8> {
    let mut out = Vec::with_capacity(roots.len() * (TREE_NONCE_BYTES + DIGEST_BYTES));
    for (nonce, root) in nonces.iter().zip(roots) {
        out.extend_from_slice(nonce);
        out.extend_from_slice(root);
    }
    out
}

fn start_transcript(
    profile: Profile,
    shape: &Shape,
    layout: &Layout,
    statement: &[u8],
    public_inputs: &[F],
    tree_nonce: &[u8; TREE_NONCE_BYTES],
    root: &Digest,
) -> Transcript {
    let public_bytes: Vec<u8> = public_inputs.iter().flat_map(|v| v.to_le_bytes()).collect();
    let mut tr = Transcript::new(
        profile,
        &[
            &MAGIC,
            &shape.digest(),
            &layout_bytes(shape, layout),
            statement,
            &public_bytes,
        ],
    );
    tr.absorb(
        b"STAGE0_ROOT",
        &encode_roots(core::slice::from_ref(tree_nonce), core::slice::from_ref(root)),
    );
    tr
}

/// Start the Fiat-Shamir transcript for a collaborative [`ZkHemV2SplitProof`].
pub fn split_transcript(
    profile: Profile,
    shape: &Shape,
    layout: &Layout,
    statement: &[u8],
    public_inputs: &[F],
    tree_nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
) -> Transcript {
    let public_bytes: Vec<u8> = public_inputs.iter().flat_map(|v| v.to_le_bytes()).collect();
    let count = [roots.len() as u8];
    let mut tr = Transcript::new(
        profile,
        &[
            &MAGIC_SPLIT,
            &count,
            &shape.digest(),
            &layout_bytes(shape, layout),
            statement,
            &public_bytes,
        ],
    );
    tr.absorb(b"STAGE0_ROOT", &encode_roots(tree_nonces, roots));
    tr
}

pub fn absorb_lookup_roots(
    tr: &mut Transcript,
    nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
) {
    tr.absorb(b"LK_ROOT", &encode_roots(nonces, roots));
}

fn squeeze_point(tr: &mut Transcript, label: &[u8], n: usize) -> Vec<E> {
    (0..n).map(|_| tr.squeeze_fp5(label)).collect()
}

// ============================================================================
// Prover
// ============================================================================

fn fold_pairs(table: &mut Vec<E>, secret: bool, f: impl Fn(E, E) -> E + Sync) {
    let mut out = vec![E::ZERO; table.len() / 2];
    let src = &*table;
    par_chunks_mut(&mut out, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            *slot = f(src[2 * (off + i)], src[2 * (off + i) + 1]);
        }
    });
    if secret {
        qsag_asm::volatile_fill(table, E::ZERO);
    }
    *table = out;
}

fn fold_in_place(table: &mut Vec<E>, r: E, secret: bool) {
    fold_pairs(table, secret, |lo, hi| lo + r * (hi - lo));
}

fn fold_base(table: &[F], r: E) -> Vec<E> {
    let mut out = vec![E::ZERO; table.len() / 2];
    par_chunks_mut(&mut out, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            let (lo, hi) = (table[2 * (off + i)], table[2 * (off + i) + 1]);
            *slot = E::from_base(lo) + r.mul_base(hi - lo);
        }
    });
    out
}

fn round_evals<const N: usize>(
    range: core::ops::Range<usize>,
    per_item: impl Fn(usize) -> [E; N] + Sync,
) -> [E; N] {
    let start = range.start;
    par_sum(range.len(), |sub| {
        let mut acc = [E::ZERO; N];
        for i in sub {
            for (a, p) in acc.iter_mut().zip(per_item(start + i)) {
                *a += p;
            }
        }
        acc
    })
}

struct PrefixSelector {
    count: usize,
    boundary: E,
}

impl PrefixSelector {
    fn at(&self, j: usize) -> E {
        match j.cmp(&self.count) {
            core::cmp::Ordering::Less => E::ONE,
            core::cmp::Ordering::Equal => self.boundary,
            core::cmp::Ordering::Greater => E::ZERO,
        }
    }

    fn fold(&mut self, r: E) {
        self.boundary = if self.count & 1 == 1 {
            E::ONE + r * (self.boundary - E::ONE)
        } else {
            self.boundary - r * self.boundary
        };
        self.count >>= 1;
    }
}

trait GateField:
    Copy + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + Send + Sync
{
    fn times(self, rhs: Self) -> Self;
    fn weigh(self, weight: E) -> E;
    fn lift(self) -> E;
}

impl GateField for F {
    #[inline(always)]
    fn times(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
    #[inline(always)]
    fn weigh(self, weight: E) -> E {
        weight.mul_base(self)
    }
    #[inline(always)]
    fn lift(self) -> E {
        E::from_base(self)
    }
}

impl GateField for E {
    #[inline(always)]
    fn times(self, rhs: Self) -> Self {
        self * rhs
    }
    #[inline(always)]
    fn weigh(self, weight: E) -> E {
        weight * self
    }
    #[inline(always)]
    fn lift(self) -> E {
        self
    }
}

fn row_round<T: GateField>(
    [ta, tb, tc]: [&[T]; 3],
    eq_rest: &[E],
    selector: &PrefixSelector,
) -> Vec<E> {
    let pairs = eq_rest.len();
    let mixed = (selector.count / 2).min(pairs);
    let line = |t: &[T], i: usize| (t[2 * i], t[2 * i + 1] - t[2 * i]);
    let mut sbox = round_evals::<{ ROW_DEGREE - 1 }>(0..mixed, |i| {
        let (mut a, da) = line(ta, i);
        let (mut c, dc) = line(tc, i);
        core::array::from_fn(|_| {
            let a2 = a.times(a);
            let v = (a2.times(a2).times(a2).times(a) - c).weigh(eq_rest[i]);
            a = a + da;
            c = c + dc;
            v
        })
    });
    let mut mul = round_evals::<3>((mixed + 1).min(pairs)..pairs, |i| {
        let (mut a, da) = line(ta, i);
        let (mut b, db) = line(tb, i);
        let (mut c, dc) = line(tc, i);
        core::array::from_fn(|_| {
            let v = (a.times(b) - c).weigh(eq_rest[i]);
            a = a + da;
            b = b + db;
            c = c + dc;
            v
        })
    });
    let mut coeffs = vec![E::ZERO; ROW_DEGREE];
    let mut add = |evals: &mut [E]| {
        let mut part = evals_to_coeffs(evals);
        for (c, &p) in coeffs.iter_mut().zip(&part) {
            *c += p;
        }
        qsag_asm::volatile_fill(&mut part, E::ZERO);
        qsag_asm::volatile_fill(evals, E::ZERO);
    };
    add(&mut sbox);
    add(&mut mul);
    if mixed < pairs {
        let lift = |t: &[T]| {
            let (lo, hi) = (t[2 * mixed].lift(), t[2 * mixed + 1].lift());
            (lo, hi - lo)
        };
        let (mut a, da) = lift(ta);
        let (mut b, db) = lift(tb);
        let (mut c, dc) = lift(tc);
        let mut s = selector.at(2 * mixed);
        let ds = selector.at(2 * mixed + 1) - s;
        let mut evals: [E; ROW_DEGREE] = core::array::from_fn(|_| {
            let v = eq_rest[mixed] * row_gate(s, a, b, c);
            a += da;
            b += db;
            c += dc;
            s += ds;
            v
        });
        add(&mut evals);
    }
    coeffs
}

pub(in crate::zk_hem) fn row_sumcheck(
    tr: &mut impl Channel,
    tau: &[E],
    num_sbox: usize,
    mut base: [Vec<F>; 3],
    mask: &Mask,
    rho: E,
) -> (Vec<Vec<E>>, Vec<E>, [E; 3]) {
    let _phase = crate::profile::span("zkhem2_row_sumcheck");
    let n = tau.len();
    let mut ext: [Vec<E>; 3] = core::array::from_fn(|_| Vec::new());
    let mut selector = PrefixSelector {
        count: num_sbox,
        boundary: E::ZERO,
    };
    let mut eq_rest = eq_table(&tau[1..]);
    let mut eq_bound = E::ONE;
    let mut rounds = Vec::with_capacity(n);
    let mut rx: Vec<E> = Vec::with_capacity(n);
    for (round, &t) in tau.iter().enumerate() {
        let mut h = if round == 0 {
            row_round(base.each_ref().map(Vec::as_slice), &eq_rest, &selector)
        } else {
            row_round(ext.each_ref().map(Vec::as_slice), &eq_rest, &selector)
        };
        let l1 = eq_bound * (t + t - E::ONE);
        let l0 = eq_bound * (E::ONE - t);
        let mut coeffs = vec![E::ZERO; ROW_DEGREE + 1];
        for (k, &hk) in h.iter().enumerate() {
            coeffs[k] += l0 * hk;
            coeffs[k + 1] += l1 * hk;
        }
        qsag_asm::volatile_fill(&mut h, E::ZERO);
        let mut g = mask.round_poly(&rx);
        for (c, &g) in coeffs.iter_mut().zip(&g) {
            *c += rho * g;
        }
        qsag_asm::volatile_fill(&mut g, E::ZERO);
        tr.absorb_fp5_slice(b"ROW_ROUND", &coeffs);
        let c = tr.squeeze_fp5(b"ROW_ROUND");
        rounds.push(coeffs);
        rx.push(c);

        if round == 0 {
            for (e, b) in ext.iter_mut().zip(base.iter_mut()) {
                *e = fold_base(b, c);
                qsag_asm::volatile_fill(b, F::ZERO);
                *b = Vec::new();
            }
        } else {
            for e in ext.iter_mut() {
                fold_in_place(e, c, true);
            }
        }
        selector.fold(c);
        if round + 1 < n {
            let tc = t * c;
            eq_bound *= E::ONE - t - c + tc + tc;
            fold_pairs(&mut eq_rest, false, |lo, hi| lo + hi);
        }
    }
    let values = [ext[0][0], ext[1][0], ext[2][0]];
    for e in &mut ext {
        qsag_asm::volatile_fill(e, E::ZERO);
    }
    (rounds, rx, values)
}

pub(in crate::zk_hem) fn column_sumcheck(
    tr: &mut impl Channel,
    mut tm: Vec<E>,
    z: &[F],
    mask: &Mask,
    rho: E,
) -> (Vec<Vec<E>>, Vec<E>, E) {
    let _phase = crate::profile::span("zkhem2_column_sumcheck");
    let n = tm.len().trailing_zeros() as usize;
    let mut tz: Vec<E> = Vec::new();
    let mut rounds = Vec::with_capacity(n);
    let mut ry: Vec<E> = Vec::with_capacity(n);
    for round in 0..n {
        let tm_ref = &tm;
        let mut evals: [E; COL_DEGREE + 1] = if round == 0 {
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm_ref[2 * i], tm_ref[2 * i + 1]);
                let (z0, z1) = (z[2 * i], z[2 * i + 1]);
                [
                    m0.mul_base(z0),
                    m1.mul_base(z1),
                    (m1 + m1 - m0).mul_base(z1 + z1 - z0),
                ]
            })
        } else {
            let tz_ref = &tz;
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm_ref[2 * i], tm_ref[2 * i + 1]);
                let (z0, z1) = (tz_ref[2 * i], tz_ref[2 * i + 1]);
                [m0 * z0, m1 * z1, (m1 + m1 - m0) * (z1 + z1 - z0)]
            })
        };
        let mut coeffs = evals_to_coeffs(&evals);
        qsag_asm::volatile_fill(&mut evals, E::ZERO);
        let mut g = mask.round_poly(&ry);
        for (c, &g) in coeffs.iter_mut().zip(&g) {
            *c += rho * g;
        }
        qsag_asm::volatile_fill(&mut g, E::ZERO);
        tr.absorb_fp5_slice(b"COL_ROUND", &coeffs);
        let c = tr.squeeze_fp5(b"COL_ROUND");
        rounds.push(coeffs);
        ry.push(c);
        if round == 0 {
            tz = fold_base(z, c);
        } else {
            fold_in_place(&mut tz, c, true);
        }
        fold_in_place(&mut tm, c, false);
    }
    qsag_asm::volatile_fill(&mut tz, E::ZERO);
    (rounds, ry, tm[0])
}

fn invert_lookup_denominators(values: &mut [E]) -> Result<(), ZkHemV2Error> {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = E::ONE;
    for &v in values.iter() {
        prefix.push(acc);
        acc *= v;
    }
    // In the extension field the product vanishes iff any checked denominator vanishes.
    if acc.is_zero() {
        qsag_asm::volatile_fill(&mut prefix, E::ZERO);
        return Err(ZkHemV2Error::LookupPoleHit);
    }
    let mut inv = acc.inverse();
    for (v, p) in values.iter_mut().zip(prefix.iter().copied()).rev() {
        let next = inv * *v;
        *v = inv * p;
        inv = next;
    }
    qsag_asm::volatile_fill(&mut prefix, E::ZERO);
    Ok(())
}

fn lookup_round(
    [eq, n, v, h]: [&[E]; 4],
    selector: &PrefixSelector,
    alpha: E,
    lambda: E,
) -> Vec<E> {
    let live = (selector.count / 2 + 1).min(eq.len() / 2);
    let mut evals = round_evals::<{ LOOKUP_DEGREE + 1 }>(0..live, |i| {
        let line = |t: &[E]| (t[2 * i], t[2 * i + 1] - t[2 * i]);
        let (mut e, de) = line(eq);
        let (mut nn, dn) = line(n);
        let (mut vv, dv) = line(v);
        let (mut hh, dh) = line(h);
        let mut s = selector.at(2 * i);
        let ds = selector.at(2 * i + 1) - s;
        core::array::from_fn(|_| {
            let value = lookup_gate(s, e, alpha, lambda, [nn, vv, hh]);
            e += de;
            nn += dn;
            vv += dv;
            hh += dh;
            s += ds;
            value
        })
    });
    let coeffs = evals_to_coeffs(&evals);
    qsag_asm::volatile_fill(&mut evals, E::ZERO);
    coeffs
}

struct LookupFront {
    committed: pcs::Committed,
    gamma: E,
    mask_sum: E,
    rounds: Vec<Vec<E>>,
    point: Vec<E>,
    values: [E; 3],
}

fn lookup_prove_front(
    profile: Profile,
    lookups: &Lookups,
    ll: &LookupLayout,
    z: &[F],
    tr: &mut Transcript,
    coins: &mut Coins,
    check: bool,
) -> Result<LookupFront, ZkHemV2Error> {
    let _phase = crate::profile::span("zkhem2_lookup");
    let d = lookups.log_entries;
    let (entries, checked) = (lookups.num_entries(), lookups.num_checked());
    let gamma = tr.squeeze_fp5(b"LK_GAMMA");
    let alpha = tr.squeeze_fp5(b"LK_ALPHA");

    let mut n = vec![E::ZERO; entries];
    let mut v = vec![E::ZERO; entries];
    par_chunks_mut(&mut n, |off, part| {
        for (j, slot) in part.iter_mut().enumerate() {
            *slot = E::from_base(lookups.num.row_dot(off + j, z));
        }
    });
    par_chunks_mut(&mut v, |off, part| {
        for (j, slot) in part.iter_mut().enumerate() {
            let i = off + j;
            *slot = lookups.den.iter().rev().fold(E::ZERO, |acc, m| {
                acc * gamma + E::from_base(m.row_dot(i, z))
            });
        }
    });
    let mut h: Vec<E> = v.iter().map(|&v| alpha - v).collect();
    let wipe = |tables: [&mut Vec<E>; 3]| {
        for t in tables {
            qsag_asm::volatile_fill(t, E::ZERO);
        }
    };
    if let Err(pole) = invert_lookup_denominators(&mut h[..checked]) {
        wipe([&mut n, &mut v, &mut h]);
        return Err(pole);
    }
    let mut total = E::ZERO;
    for (slot, &num) in h[..checked].iter_mut().zip(&n) {
        *slot *= num;
        total += *slot;
    }
    if check && !total.is_zero() {
        wipe([&mut n, &mut v, &mut h]);
        return Err(ZkHemV2Error::Unsatisfied);
    }
    for slot in &mut h[checked..] {
        *slot = coins.next_fp5();
    }

    let cells = 1usize << ll.log_cells;
    let mask = Mask::sample(coins, d, LOOKUP_DEGREE);
    let mut table = vec![F::ZERO; cells];
    for (i, value) in h.iter().enumerate() {
        for (j, limb) in value.to_limbs().into_iter().enumerate() {
            table[ll.limb_block(j) + i] = limb;
        }
    }
    mask.write(&mut table, LOOKUP_MASK_BITS, |i, j| ll.mask_block(i, j));
    coins.fill_base(&mut table[cells - ll.blind_cells..]);
    let step_vars = ll.schedule.stages[0].step_vars;
    let mask_poly: Vec<E> = (0..pcs::mask_len(ll.log_cells, step_vars))
        .map(|_| coins.next_fp5())
        .collect();
    let mut salt_seed = coins.next_bytes32();
    let helper_nonce = coins.next_bytes32();
    let coeffs = hypercube_to_monomial_coeffs(&table);
    qsag_asm::volatile_fill(&mut table, F::ZERO);
    let committed = pcs::commit(
        profile,
        ll.log_cells,
        &ll.schedule,
        coeffs,
        mask_poly,
        &salt_seed,
        &helper_nonce,
    );
    qsag_asm::volatile_fill(&mut salt_seed, 0u8);
    absorb_lookup_roots(
        tr,
        core::slice::from_ref(&helper_nonce),
        core::slice::from_ref(&committed.root()),
    );

    let tau = squeeze_point(tr, b"LK_TAU", d);
    let lambda = tr.squeeze_fp5(b"LK_BATCH");
    let mask_sum = mask.sum();
    tr.absorb_fp5_slice(b"LK_MASK_SUM", &[mask_sum]);
    let rho = tr.squeeze_fp5_nonzero(b"LK_RHO");
    let mut eq = eq_table(&tau);
    let mut selector = PrefixSelector {
        count: checked,
        boundary: E::ZERO,
    };
    let mut rounds = Vec::with_capacity(d);
    let mut point = Vec::with_capacity(d);
    for round in 0..d {
        let mut coeffs = lookup_round([&eq, &n, &v, &h], &selector, alpha, lambda);
        let mut g = mask.round_poly(&point);
        for (c, &gv) in coeffs.iter_mut().zip(&g) {
            *c += rho * gv;
        }
        qsag_asm::volatile_fill(&mut g, E::ZERO);
        tr.absorb_fp5_slice(b"LK_ROUND", &coeffs);
        let c = tr.squeeze_fp5(b"LK_ROUND");
        rounds.push(coeffs);
        point.push(c);
        fold_in_place(&mut eq, c, false);
        for t in [&mut n, &mut v, &mut h] {
            fold_in_place(t, c, true);
        }
        selector.fold(c);
        let _ = round;
    }
    let mut values = [n[0], v[0], h[0]];
    wipe([&mut n, &mut v, &mut h]);
    if !lookup_masks_full_rank(lookups, &point) {
        qsag_asm::volatile_fill(&mut values, E::ZERO);
        return Err(ZkHemV2Error::MaskRankDeficient);
    }
    tr.absorb_fp5_slice(b"LK_VALUES", &values);
    Ok(LookupFront {
        committed,
        gamma,
        mask_sum,
        rounds,
        point,
        values,
    })
}

/// Add `sum_i eq_rl[i] (weights[0] N + weights[1] sum_c gamma^c D_c)[i, .]` to a column table.
pub fn lookup_column_add(
    table: &mut [E],
    lookups: &Lookups,
    eq_rl: &[E],
    weights: [E; 2],
    gamma: E,
) {
    for (i, &eq) in eq_rl.iter().enumerate() {
        let weight = weights[0] * eq;
        for (col, val) in lookups.num.row(i) {
            table[col] += weight.mul_base(val);
        }
        let mut weight = weights[1] * eq;
        for m in &lookups.den {
            for (col, val) in m.row(i) {
                table[col] += weight.mul_base(val);
            }
            weight *= gamma;
        }
    }
}

pub(in crate::zk_hem) fn row_tables(shape: &Shape, assignment: &[F], check: bool) -> Option<[Vec<F>; 3]> {
    let _phase = crate::profile::span("zkhem2_row_tables");
    let rows = shape.num_rows();
    let fill = |m: &crate::zk_hem::relation::Csr| {
        let mut t = vec![F::ZERO; rows];
        par_chunks_mut(&mut t, |off, part| {
            for (j, slot) in part.iter_mut().enumerate() {
                *slot = m.row_dot(off + j, assignment);
            }
        });
        t
    };
    let (ta, tb) = (fill(&shape.a), fill(&shape.b));
    let valid = core::sync::atomic::AtomicBool::new(true);
    let mut tc = vec![F::ZERO; rows];
    par_chunks_mut(&mut tc, |off, part| {
        let mut ok = true;
        for (j, slot) in part.iter_mut().enumerate() {
            let i = off + j;
            *slot = shape.c.row_dot(i, assignment);
            let expected = if i < shape.num_sbox {
                crate::sponge::poseidon2_sbox7(ta[i])
            } else {
                ta[i].const_mul(tb[i])
            };
            ok &= expected == *slot;
        }
        if !ok {
            valid.store(false, core::sync::atomic::Ordering::Relaxed);
        }
    });
    let mut tables = [ta, tb, tc];
    if check && !valid.load(core::sync::atomic::Ordering::Relaxed) {
        for t in &mut tables {
            qsag_asm::volatile_fill(t, F::ZERO);
        }
        return None;
    }
    Some(tables)
}

pub fn column_table(shape: &Shape, eq_rx: &[E], combine: &[E], cells: usize) -> Vec<E> {
    let _phase = crate::profile::span("zkhem2_column_table");
    let mut table = vec![E::ZERO; cells];
    let matrices = [&shape.a, &shape.b, &shape.c];
    let scatter = |rows: core::ops::Range<usize>,
                   home: usize,
                   window: &mut [E],
                   far: &mut BTreeMap<usize, E>| {
        for i in rows {
            for (matrix, &r) in matrices.into_iter().zip(combine) {
                let mut entries = matrix.row(i).peekable();
                if entries.peek().is_none() {
                    continue;
                }
                let weight = r * eq_rx[i];
                for (col, val) in entries {
                    let term = weight.mul_base(val);
                    match col.checked_sub(home).and_then(|c| window.get_mut(c)) {
                        Some(slot) => *slot += term,
                        None => *far.entry(col).or_insert(E::ZERO) += term,
                    }
                }
            }
        }
    };
    #[cfg(feature = "std")]
    if eq_rx.len() > par_chunk(eq_rx.len()) {
        let newest = |rows: core::ops::Range<usize>| {
            rows.take(64)
                .flat_map(|i| matrices.into_iter().flat_map(move |m| m.row(i)))
                .map(|(col, _)| col)
                .max()
        };
        for block in [0..shape.num_sbox, shape.num_sbox..eq_rx.len()] {
            let chunk = par_chunk(block.len());
            let runs: Vec<_> = block
                .clone()
                .step_by(chunk)
                .map(|start| start..(start + chunk).min(block.end))
                .collect();
            let mut homes = vec![0; runs.len() + 1];
            for (k, run) in runs.iter().enumerate().skip(1) {
                homes[k] = newest(run.clone()).unwrap_or(0).clamp(homes[k - 1], cells);
            }
            homes[runs.len()] = cells;
            let deferred = std::thread::scope(|scope| {
                let mut rest = table.as_mut_slice();
                let workers: Vec<_> = runs
                    .iter()
                    .zip(homes.windows(2))
                    .map(|(run, home)| {
                        let (window, tail) =
                            core::mem::take(&mut rest).split_at_mut(home[1] - home[0]);
                        rest = tail;
                        let (scatter, run, home) = (&scatter, run.clone(), home[0]);
                        crate::spawn_bounded(scope, move || {
                            let mut far = BTreeMap::new();
                            scatter(run, home, window, &mut far);
                            far
                        })
                    })
                    .collect();
                workers
                    .into_iter()
                    .map(crate::join_worker)
                    .collect::<Vec<_>>()
            });
            for (col, term) in deferred.into_iter().flatten() {
                table[col] += term;
            }
        }
        return table;
    }
    let mut far = BTreeMap::new();
    scatter(0..eq_rx.len(), 0, &mut table, &mut far);
    debug_assert!(far.is_empty());
    table
}

/// Prove that `assignment` satisfies `shape`, bound to `statement`.
pub fn prove(
    shape: &Shape,
    assignment: Vec<F>,
    statement: &[u8],
    profile: Profile,
    seed: &[u8; 32],
) -> Result<ZkHemV2Proof, ZkHemV2Error> {
    prove_inner(shape, assignment, statement, profile, seed, true, None)
}

fn prove_inner(
    shape: &Shape,
    mut assignment: Vec<F>,
    statement: &[u8],
    profile: Profile,
    seed: &[u8; 32],
    check: bool,
    claimed: Option<&[F]>,
) -> Result<ZkHemV2Proof, ZkHemV2Error> {
    let Some(layout) = layout_of(shape) else {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemV2Error::UnsupportedRelation);
    };
    if assignment.len() != shape.num_vars {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemV2Error::Unsatisfied);
    }
    let phase = crate::profile::span("zkhem2_coins");
    let mut coins = Coins::new(profile, shape, &layout, statement, &assignment, seed);
    let mut secrets = sample_secrets(&mut coins, shape, &layout, &mut assignment);
    drop(phase);
    let row_base = if check && assignment[0] != F::ONE {
        None
    } else {
        row_tables(shape, &assignment, check)
    };
    let public_inputs =
        claimed.map_or_else(|| assignment[1..=shape.num_public].to_vec(), <[F]>::to_vec);
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    let Some(row_base) = row_base else {
        return Err(ZkHemV2Error::Unsatisfied);
    };
    // The row tables and `z_var` are witness data: both are erased on every exit, the
    // lookup front end's early returns included.
    let row_base = SecretBuffer::new(row_base);

    let phase = crate::profile::span("zkhem2_monomial");
    let var_cube = 1usize << layout.var_bits;
    let mut z_var = SecretBuffer::new(vec![F::ZERO; var_cube]);
    let live = layout.var_cells.min(var_cube);
    z_var[..live].copy_from_slice(&secrets.table[..live]);

    let coeffs = hypercube_to_monomial_coeffs(&secrets.table);
    qsag_asm::volatile_fill(&mut secrets.table, F::ZERO);
    secrets.table = Vec::new();
    drop(phase);
    let committed = pcs::commit(
        profile,
        layout.log_cells,
        &layout.schedule,
        coeffs,
        core::mem::take(&mut secrets.mask_poly),
        &secrets.salt_seed,
        &secrets.tree_nonce,
    );
    let tree_nonce = committed.tree_nonce();
    let root = committed.root();
    let mut tr = start_transcript(
        profile,
        shape,
        &layout,
        statement,
        &public_inputs,
        &tree_nonce,
        &root,
    );

    let lookup_front = match (shape.lookups(), &layout.lookup) {
        (Some(lookups), Some(ll)) => Some((
            lookups,
            ll,
            lookup_prove_front(
                profile,
                lookups,
                ll,
                &z_var[..shape.num_vars],
                &mut tr,
                &mut coins,
                check,
            )?,
        )),
        _ => None,
    };
    drop(coins);

    let tau = squeeze_point(&mut tr, b"TAU", shape.log_rows);
    let row_mask_sum = secrets.row_mask.sum();
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[row_mask_sum]);
    let rho1 = tr.squeeze_fp5_nonzero(b"RHO1");
    let (row_rounds, rx, mut row_values) = row_sumcheck(
        &mut tr,
        &tau,
        shape.num_sbox,
        row_base.into_inner(),
        &secrets.row_mask,
        rho1,
    );
    // (G1), before the row values exist outside the prover.
    if !row_challenge_good(shape, &rx) {
        qsag_asm::volatile_fill(&mut row_values, E::ZERO);
        return Err(ZkHemV2Error::MaskRankDeficient);
    }

    tr.absorb_fp5_slice(b"ROW_VALUES", &row_values);
    let combine = squeeze_point(&mut tr, b"COMBINE", if lookup_front.is_some() { 5 } else { 3 });
    let col_mask_sum = secrets.col_mask.sum();
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[col_mask_sum]);
    let rho2 = tr.squeeze_fp5_nonzero(b"RHO2");
    let mut tm = column_table(shape, &eq_table(&rx), &combine[..3], var_cube);
    if let Some((lookups, _, lf)) = &lookup_front {
        lookup_column_add(
            &mut tm,
            lookups,
            &eq_table(&lf.point),
            [combine[3], combine[4]],
            lf.gamma,
        );
    }
    let (col_rounds, ry, matrix_at_point) =
        column_sumcheck(&mut tr, tm, &z_var, &secrets.col_mask, rho2);
    drop(z_var);

    let lambda = tr.squeeze_fp5(b"LAMBDA");
    let phase = crate::profile::span("zkhem2_kernel");
    let weights = claim_cell_weights(&ClaimInputs {
        layout: &layout,
        log_rows: shape.log_rows,
        num_public: shape.num_public,
        rx: &rx,
        ry: &ry,
        lambda,
        rho2,
        matrix_at_point,
    });
    let kernel = cell_weights_to_kernel(weights, 1 << layout.log_cells);
    let table_coeffs = committed.coeffs();
    let [value] = par_sum(kernel.len(), |range| {
        [range.fold(E::ZERO, |acc, i| acc + kernel[i].mul_base(table_coeffs[i]))]
    });
    let helper_claim = if let Some((_, ll, lf)) = &lookup_front {
        let h_lambda = tr.squeeze_fp5(b"LK_CLAIM_BATCH");
        let h_weights = lookup_claim_cell_weights(ll, &lf.point, h_lambda);
        let h_kernel = cell_weights_to_kernel(h_weights, 1 << ll.log_cells);
        let h_coeffs = lf.committed.coeffs();
        let [h_val] = par_sum(h_kernel.len(), |range| {
            [range.fold(E::ZERO, |acc, i| acc + h_kernel[i].mul_base(h_coeffs[i]))]
        });
        Some((h_kernel, h_val))
    } else {
        None
    };
    drop(phase);

    let opening = pcs::open(&committed, kernel, value, &mut tr)
        .map_err(|pcs::MaskRankDeficient| ZkHemV2Error::MaskRankDeficient)?;
    let lookup = match (lookup_front, helper_claim) {
        (Some((_, _, lf)), Some((h_kernel, h_val))) => {
            let h_open = pcs::open(&lf.committed, h_kernel, h_val, &mut tr)
                .map_err(|pcs::MaskRankDeficient| ZkHemV2Error::MaskRankDeficient)?;
            Some(LookupV2Proof {
                helper_tree_nonce: lf.committed.tree_nonce(),
                helper_root: lf.committed.root(),
                mask_sum: lf.mask_sum,
                rounds: lf.rounds,
                values: lf.values,
                opening: h_open,
            })
        }
        _ => None,
    };
    Ok(ZkHemV2Proof {
        profile,
        log_cells: layout.log_cells as u8,
        tree_nonce,
        root,
        lookup,
        row_mask_sum,
        row_rounds,
        row_values,
        col_mask_sum,
        col_rounds,
        opening,
    })
}

// ============================================================================
// Verifier & Shared Front-End Replay (for single-prover and collaborative split)
// ============================================================================

/// Front-end messages of a v2 proof before the WHIR openings.
pub struct FrontMessages<'a> {
    pub lookup: Option<LookupMessages<'a>>,
    pub row_mask_sum: E,
    pub row_rounds: &'a [Vec<E>],
    pub row_values: [E; 3],
    pub col_mask_sum: E,
    pub col_rounds: &'a [Vec<E>],
}

pub struct LookupMessages<'a> {
    pub helper_tree_nonces: &'a [[u8; TREE_NONCE_BYTES]],
    pub helper_roots: &'a [Digest],
    pub mask_sum: E,
    pub rounds: &'a [Vec<E>],
    pub values: [E; 3],
}

pub struct HelperClaim {
    pub terms: Vec<TensorTerm>,
    pub cell_weights: Vec<E>,
    pub value: E,
}

pub struct FrontReplay {
    pub terms: Vec<TensorTerm>,
    pub cell_weights: Vec<E>,
    pub value: E,
    pub helper: Option<HelperClaim>,
}

fn verify_sumcheck(
    tr: &mut Transcript,
    label: &[u8],
    rounds: &[Vec<E>],
    degree: usize,
    mut claim: E,
) -> Option<(E, Vec<E>)> {
    let mut point = Vec::with_capacity(rounds.len());
    for round in rounds {
        if round.len() != degree + 1 {
            return None;
        }
        let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);
        if round[0] + at_one != claim {
            return None;
        }
        tr.absorb_fp5_slice(label, round);
        let c = tr.squeeze_fp5(label);
        claim = if degree == COL_DEGREE {
            E::from_verified(qsag_whir_verified::eval_quadratic_sumcheck_wire_fp5(
                round[0].to_verified(),
                round[2].to_verified(),
                claim.to_verified(),
                c.to_verified(),
            ))
        } else {
            eval_poly(round, c)
        };
        point.push(c);
    }
    Some((claim, point))
}

fn matrix_at(
    shape: &Shape,
    rx: &[E],
    ry: &[E],
    combine: &[E],
    lookup: Option<(&Lookups, &[E], E)>,
) -> E {
    let eq_rx = eq_table(rx);
    let eq_ry = eq_table(ry);
    let cols = &eq_ry[..shape.num_vars];
    let lookup_part = lookup.map_or(E::ZERO, |(lookups, rl, gamma)| {
        let eq_rl = eq_table(rl);
        let dot = |m: &crate::zk_hem::relation::Csr, i: usize| {
            m.row(i)
                .fold(E::ZERO, |acc, (col, val)| acc + cols[col].mul_base(val))
        };
        (0..eq_rl.len()).fold(E::ZERO, |acc, i| {
            let value = lookups
                .den
                .iter()
                .rev()
                .fold(E::ZERO, |v, m| v * gamma + dot(m, i));
            acc + eq_rl[i] * (combine[3] * dot(&lookups.num, i) + combine[4] * value)
        })
    });
    let [total] = par_sum(eq_rx.len(), |range| {
        let mut acc = E::ZERO;
        for i in range {
            let mut row = E::ZERO;
            for (m, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
                let inner = m
                    .row(i)
                    .fold(E::ZERO, |acc, (col, val)| acc + cols[col].mul_base(val));
                row += r * inner;
            }
            acc += eq_rx[i] * row;
        }
        [acc]
    });
    lookup_part + total
}

struct LookupReplay {
    gamma: E,
    point: Vec<E>,
    values: [E; 3],
    mask_sum: E,
    mask_at_point: E,
}

fn lookup_replay(
    lookups: &Lookups,
    tr: &mut Transcript,
    msgs: &LookupMessages<'_>,
) -> Option<LookupReplay> {
    if msgs.rounds.len() != lookups.log_entries {
        return None;
    }
    let gamma = tr.squeeze_fp5(b"LK_GAMMA");
    let alpha = tr.squeeze_fp5(b"LK_ALPHA");
    absorb_lookup_roots(tr, msgs.helper_tree_nonces, msgs.helper_roots);
    let tau = squeeze_point(tr, b"LK_TAU", lookups.log_entries);
    let lambda = tr.squeeze_fp5(b"LK_BATCH");
    tr.absorb_fp5_slice(b"LK_MASK_SUM", &[msgs.mask_sum]);
    let rho = tr.squeeze_fp5_nonzero(b"LK_RHO");
    let (last, point) = verify_sumcheck(
        tr,
        b"LK_ROUND",
        msgs.rounds,
        LOOKUP_DEGREE,
        rho * msgs.mask_sum,
    )?;
    if !lookup_masks_full_rank(lookups, &point) {
        return None;
    }
    tr.absorb_fp5_slice(b"LK_VALUES", &msgs.values);
    let gate = lookup_gate(
        prefix_indicator(&point, lookups.num_checked()),
        eq_eval(&tau, &point),
        alpha,
        lambda,
        msgs.values,
    );
    Some(LookupReplay {
        gamma,
        mask_at_point: (last - gate) * rho.inverse(),
        point,
        values: msgs.values,
        mask_sum: msgs.mask_sum,
    })
}

/// Replay Rounds L1-L3 and 1-6 on `tr`, returning the tensor terms, cell weights and claimed
/// scalar values for the assignment table (and optional helper table).
pub fn replay_front(
    shape: &Shape,
    layout: &Layout,
    public_inputs: &[F],
    tr: &mut Transcript,
    msgs: &FrontMessages<'_>,
    with_cell_weights: bool,
) -> Option<FrontReplay> {
    if msgs.row_rounds.len() != shape.log_rows
        || msgs.col_rounds.len() != layout.var_bits
        || public_inputs.len() != shape.num_public
    {
        return None;
    }
    let lk = match (shape.lookups(), &layout.lookup, &msgs.lookup) {
        (Some(lookups), Some(ll), Some(m)) => Some((lookups, ll, lookup_replay(lookups, tr, m)?)),
        (None, None, None) => None,
        _ => return None,
    };

    let tau = squeeze_point(tr, b"TAU", shape.log_rows);
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[msgs.row_mask_sum]);
    let rho1 = tr.squeeze_fp5_nonzero(b"RHO1");
    let (row_final, rx) = verify_sumcheck(
        tr,
        b"ROW_ROUND",
        msgs.row_rounds,
        ROW_DEGREE,
        rho1 * msgs.row_mask_sum,
    )?;
    let [va, vb, vc] = msgs.row_values;
    tr.absorb_fp5_slice(b"ROW_VALUES", &msgs.row_values);
    let gate = eq_eval(&tau, &rx) * row_gate(prefix_indicator(&rx, shape.num_sbox), va, vb, vc);
    let row_mask_at_point = (row_final - gate) * rho1.inverse();

    let combine = squeeze_point(tr, b"COMBINE", if lk.is_some() { 5 } else { 3 });
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[msgs.col_mask_sum]);
    let rho2 = tr.squeeze_fp5_nonzero(b"RHO2");
    let mut col_claim = combine[0] * va + combine[1] * vb + combine[2] * vc;
    if let Some((_, _, lr)) = &lk {
        col_claim += combine[3] * lr.values[0] + combine[4] * lr.values[1];
    }
    let (col_final, ry) = verify_sumcheck(
        tr,
        b"COL_ROUND",
        msgs.col_rounds,
        COL_DEGREE,
        col_claim + rho2 * msgs.col_mask_sum,
    )?;

    let lambda = tr.squeeze_fp5(b"LAMBDA");
    let phase = crate::profile::span("zkhem2_verify_matrix");
    let matrix_at_point = matrix_at(
        shape,
        &rx,
        &ry,
        &combine,
        lk.as_ref()
            .map(|(l, _, lr)| (*l, lr.point.as_slice(), lr.gamma)),
    );
    drop(phase);
    let inp = ClaimInputs {
        layout,
        log_rows: shape.log_rows,
        num_public: shape.num_public,
        rx: &rx,
        ry: &ry,
        lambda,
        rho2,
        matrix_at_point,
    };
    let terms = claim_terms(&inp);
    let cell_weights = if with_cell_weights {
        claim_cell_weights(&inp)
    } else {
        Vec::new()
    };
    let mut values = vec![
        msgs.row_mask_sum,
        msgs.col_mask_sum,
        row_mask_at_point,
        col_final,
        E::ONE,
    ];
    values.extend(public_inputs.iter().map(|&v| E::from_base(v)));
    let value = batched_value(lambda, &values);

    let helper = lk.map(|(_, ll, lr)| {
        let h_lambda = tr.squeeze_fp5(b"LK_CLAIM_BATCH");
        let h_terms = lookup_claim_terms(ll, &lr.point, h_lambda);
        let h_cell_weights = if with_cell_weights {
            lookup_claim_cell_weights(ll, &lr.point, h_lambda)
        } else {
            Vec::new()
        };
        let h_value = batched_value(h_lambda, &[lr.mask_sum, lr.mask_at_point, lr.values[2]]);
        HelperClaim {
            terms: h_terms,
            cell_weights: h_cell_weights,
            value: h_value,
        }
    });
    Some(FrontReplay {
        terms,
        cell_weights,
        value,
        helper,
    })
}

/// Verify a single-prover [`ZkHemV2Proof`].
pub fn verify(
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    profile: Profile,
    proof: &ZkHemV2Proof,
) -> bool {
    let Some(layout) = layout_of(shape) else {
        return false;
    };
    if proof.profile != profile || usize::from(proof.log_cells) != layout.log_cells {
        return false;
    }
    let mut tr = start_transcript(
        profile,
        shape,
        &layout,
        statement,
        public_inputs,
        &proof.tree_nonce,
        &proof.root,
    );
    let lk_msgs = proof.lookup.as_ref().map(|lp| LookupMessages {
        helper_tree_nonces: core::slice::from_ref(&lp.helper_tree_nonce),
        helper_roots: core::slice::from_ref(&lp.helper_root),
        mask_sum: lp.mask_sum,
        rounds: &lp.rounds,
        values: lp.values,
    });
    let Some(front) = replay_front(
        shape,
        &layout,
        public_inputs,
        &mut tr,
        &FrontMessages {
            lookup: lk_msgs,
            row_mask_sum: proof.row_mask_sum,
            row_rounds: &proof.row_rounds,
            row_values: proof.row_values,
            col_mask_sum: proof.col_mask_sum,
            col_rounds: &proof.col_rounds,
        },
        false,
    ) else {
        return false;
    };
    let _phase = crate::profile::span("zkhem2_verify_opening");
    if !pcs::verify(
        profile,
        &proof.tree_nonce,
        &proof.root,
        layout.log_cells,
        &layout.schedule,
        &front.terms,
        front.value,
        &proof.opening,
        &mut tr,
    ) {
        return false;
    }
    match (&front.helper, &proof.lookup, &layout.lookup) {
        (None, None, None) => true,
        (Some(hc), Some(lp), Some(ll)) => pcs::verify(
            profile,
            &lp.helper_tree_nonce,
            &lp.helper_root,
            ll.log_cells,
            &ll.schedule,
            &hc.terms,
            hc.value,
            &lp.opening,
            &mut tr,
        ),
        _ => false,
    }
}

/// Verify a collaborative split-share [`ZkHemV2SplitProof`].
pub fn verify_split(
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    profile: Profile,
    proof: &ZkHemV2SplitProof,
) -> bool {
    let Some(layout) = layout_of(shape) else {
        return false;
    };
    let committers = proof.roots.len();
    if proof.profile != profile
        || usize::from(proof.log_cells) != layout.log_cells
        || !(1..=MAX_STAGE0_SHARES).contains(&committers)
        || proof.tree_nonces.len() != committers
    {
        return false;
    }
    if let Some(lp) = &proof.lookup
        && (lp.helper_roots.len() != committers || lp.helper_tree_nonces.len() != committers)
    {
        return false;
    }
    let mut tr = split_transcript(
        profile,
        shape,
        &layout,
        statement,
        public_inputs,
        &proof.tree_nonces,
        &proof.roots,
    );
    let lk_msgs = proof.lookup.as_ref().map(|lp| LookupMessages {
        helper_tree_nonces: &lp.helper_tree_nonces,
        helper_roots: &lp.helper_roots,
        mask_sum: lp.mask_sum,
        rounds: &lp.rounds,
        values: lp.values,
    });
    let Some(front) = replay_front(
        shape,
        &layout,
        public_inputs,
        &mut tr,
        &FrontMessages {
            lookup: lk_msgs,
            row_mask_sum: proof.row_mask_sum,
            row_rounds: &proof.row_rounds,
            row_values: proof.row_values,
            col_mask_sum: proof.col_mask_sum,
            col_rounds: &proof.col_rounds,
        },
        false,
    ) else {
        return false;
    };
    if !pcs::verify_split(
        profile,
        &proof.tree_nonces,
        &proof.roots,
        layout.log_cells,
        &layout.schedule,
        &front.terms,
        front.value,
        &proof.opening,
        &mut tr,
    ) {
        return false;
    }
    match (&front.helper, &proof.lookup, &layout.lookup) {
        (None, None, None) => true,
        (Some(hc), Some(lp), Some(ll)) => pcs::verify_split(
            profile,
            &lp.helper_tree_nonces,
            &lp.helper_roots,
            ll.log_cells,
            &ll.schedule,
            &hc.terms,
            hc.value,
            &lp.opening,
            &mut tr,
        ),
        _ => false,
    }
}

const _: () = assert!(PAD_VARS == LIMBS);
const _: () = assert!(ROW_DEGREE < 1 << ROW_MASK_BITS && COL_DEGREE < 1 << COL_MASK_BITS);
const _: () = assert!(LOOKUP_DEGREE < 1 << LOOKUP_MASK_BITS);

#[cfg(test)]
fn solve_pad(rx: &[E], target: E) -> [F; LIMBS] {
    let weights: [E; LIMBS] = core::array::from_fn(|c| eq_index(&rx[..3], c));
    let mut aug: [[F; LIMBS + 1]; LIMBS] = core::array::from_fn(|row| {
        let mut r = [F::ZERO; LIMBS + 1];
        for col in 0..LIMBS {
            r[col] = weights[col].to_limbs()[row];
        }
        r[LIMBS] = target.to_limbs()[row];
        r
    });
    for col in 0..LIMBS {
        let pivot = (col..LIMBS).find(|&row| !aug[row][col].is_zero()).unwrap();
        aug.swap(col, pivot);
        let inv = aug[col][col].inv();
        for cell in &mut aug[col][col..] {
            *cell *= inv;
        }
        let prow = aug[col];
        for (r, row) in aug.iter_mut().enumerate() {
            if r != col && !row[col].is_zero() {
                let factor = row[col];
                for c in col..=LIMBS {
                    row[c] -= factor * prow[c];
                }
            }
        }
    }
    core::array::from_fn(|row| aug[row][LIMBS])
}

/// Test-only auxiliary-input distinguisher check: recovers the 15 row-mask cells consistent
/// with `proof.row_values` at `rx` on a `Closing::V2` relation without lookups, then compares
/// `M(rx, ry) * candidate_with_recovered_masks(ry)` with the masked column sumcheck terminal
/// claim (`col_final`).
#[cfg(test)]
pub(crate) fn candidate_matches_masked_evaluation(
    shape: &Shape,
    profile: Profile,
    public: &[F],
    statement: &[u8],
    proof: &ZkHemV2Proof,
    candidate: &[F],
) -> bool {
    let layout = layout_of(shape).unwrap();
    assert!(shape.lookups().is_none());
    let mut tr = start_transcript(
        profile,
        shape,
        &layout,
        statement,
        public,
        &proof.tree_nonce,
        &proof.root,
    );
    let _tau = squeeze_point(&mut tr, b"TAU", shape.log_rows);
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[proof.row_mask_sum]);
    let rho1 = tr.squeeze_fp5_nonzero(b"RHO1");
    let (_, rx) = verify_sumcheck(
        &mut tr,
        b"ROW_ROUND",
        &proof.row_rounds,
        ROW_DEGREE,
        rho1 * proof.row_mask_sum,
    )
    .unwrap();
    tr.absorb_fp5_slice(b"ROW_VALUES", &proof.row_values);
    let combine = squeeze_point(&mut tr, b"COMBINE", 3);
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[proof.col_mask_sum]);
    let rho2 = tr.squeeze_fp5_nonzero(b"RHO2");
    let col_claim = combine[0] * proof.row_values[0]
        + combine[1] * proof.row_values[1]
        + combine[2] * proof.row_values[2];
    let (terminal, ry) = verify_sumcheck(
        &mut tr,
        b"COL_ROUND",
        &proof.col_rounds,
        COL_DEGREE,
        col_claim + rho2 * proof.col_mask_sum,
    )
    .unwrap();

    assert_eq!(candidate.len(), shape.num_vars);
    let mut candidate = candidate.to_vec();
    candidate[shape.mask_var_base..].fill(F::ZERO);
    let row_weights = eq_table(&rx);
    let have = [&shape.a, &shape.b, &shape.c].map(|matrix| {
        row_weights
            .iter()
            .enumerate()
            .fold(E::ZERO, |acc, (row, &weight)| {
                acc + weight.mul_base(matrix.row_dot(row, &candidate))
            })
    });
    let delta: [E; 3] = core::array::from_fn(|i| proof.row_values[i] - have[i]);
    let k: [E; 3] = core::array::from_fn(|g| corner_factor(&rx, shape.mask_row_base(g)));
    let e2 = delta[1] * k[1].inverse();
    let e3 = (delta[2] - delta[1] - delta[0]) * k[2].inverse();
    let e1 = (delta[0] - k[2] * e3) * k[0].inverse();

    for (g, evaluation) in [e1, e2, e3].into_iter().enumerate() {
        let cells = solve_pad(&rx, evaluation);
        candidate[shape.mask_var_base + LIMBS * g..shape.mask_var_base + LIMBS * (g + 1)]
            .copy_from_slice(&cells);
    }
    let weights = eq_table(&ry);
    let evaluation = candidate
        .iter()
        .zip(weights)
        .fold(E::ZERO, |v, (&z, w)| v + w.mul_base(z));
    matrix_at(shape, &rx, &ry, &combine, None) * evaluation == terminal
}

#[cfg(test)]
mod tests {
    use super::super::bounds;
    use super::super::params::{MAX_LOG_CELLS, MIN_LOG_CELLS, schedule};
    use super::*;
    use crate::zk_hem::relation::{ConstraintSystem, Lc};

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
        fn fp5(&mut self) -> E {
            Fp5(core::array::from_fn(|_| f(self.next_u64())))
        }
    }

    fn relation(x: u64, w: u64, constant: u64, extra: usize) -> ConstraintSystem {
        let mut cs = ConstraintSystem::new();
        let xv = cs.public_input(f(x));
        let x7 = f(x).pow(7);
        let yv = cs.public_input(x7 * f(w) + f(constant));
        let wv = cs.alloc(f(w));
        let s = cs.sbox7(&xv.into());
        let prod = cs.mul(&s.into(), &wv.into());
        cs.enforce_equal(&Lc::from(prod).plus_const(f(constant)), &yv.into());
        let mut acc: Lc = wv.into();
        for i in 0..extra {
            let t = cs.sbox7(&acc);
            let u = cs.mul(&t.into(), &acc);
            acc = Lc::from(u).plus_const(f(i as u64 + 1));
        }
        cs
    }

    fn fixture(extra: usize) -> (Shape, Vec<F>) {
        relation(3, 5, 11, extra).finish_v2()
    }

    const SEED: [u8; 32] = [7u8; 32];
    const STATEMENT: &[u8] = b"v2 statement";

    fn publics(shape: &Shape, z: &[F]) -> Vec<F> {
        z[1..=shape.num_public].to_vec()
    }

    #[test]
    fn honest_roundtrip_both_profiles_and_serialization() {
        let (shape, z) = fixture(40);
        assert!(shape.is_satisfied(&z));
        let layout = layout_of(&shape).unwrap();
        for profile in Profile::ALL {
            let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
            assert!(verify(
                &shape,
                &publics(&shape, &z),
                STATEMENT,
                profile,
                &proof
            ));
            let bytes = proof.to_bytes();
            assert_eq!(&bytes[..8], b"QSAGZKH2");
            assert_eq!(bytes[8], profile.wire_tag());
            assert_eq!(
                ZkHemV2Proof::from_bytes(&bytes, &shape),
                Some(proof.clone())
            );
            let report = bounds::report_for_shape(profile, &shape).unwrap();
            assert_eq!(report.log_cells, layout.log_cells);
            assert!(bytes.len() <= report.proof_bytes);
            assert!(ZkHemV2Proof::from_bytes(&bytes[..bytes.len() - 1], &shape).is_none());
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(ZkHemV2Proof::from_bytes(&longer, &shape).is_none());
        }
        let mut bad = z.clone();
        bad[3] += F::ONE;
        assert_eq!(
            prove(
                &shape,
                bad.clone(),
                STATEMENT,
                Profile::CshakeJohnson400,
                &SEED
            ),
            Err(ZkHemV2Error::Unsatisfied)
        );
        let forged = prove_inner(
            &shape,
            bad,
            STATEMENT,
            Profile::CshakeJohnson400,
            &SEED,
            false,
            None,
        )
        .unwrap();
        assert!(!verify(
            &shape,
            &publics(&shape, &z),
            STATEMENT,
            Profile::CshakeJohnson400,
            &forged
        ));
    }

    #[test]
    fn lookup_pole_refusal_precedes_inversion() {
        let nonzero = Rng(123).fp5();
        let mut denominators = [nonzero, E::ZERO, E::ONE];
        let original = denominators;
        assert_eq!(
            invert_lookup_denominators(&mut denominators),
            Err(ZkHemV2Error::LookupPoleHit)
        );
        assert_eq!(denominators, original);
        invert_lookup_denominators(&mut denominators[..1]).unwrap();
        assert_eq!(denominators[0] * nonzero, E::ONE);
    }

    #[test]
    fn coupled_lookup_front_for_distinct_witnesses() {
        let build = |v| {
            let mut cs = ConstraintSystem::new();
            let t = cs.table(1, vec![f(3), f(7)]);
            let x = cs.alloc(f(v));
            cs.enforce_in_table(t, &[x.into()]);
            cs.finish_v2()
        };
        let (shape, mut left) = build(3);
        let (other, mut right) = build(7);
        assert_eq!(shape, other);
        assert!(shape.is_satisfied(&left) && shape.is_satisfied(&right));
        let lk = shape.lookups().unwrap();
        let d = lk.log_entries;
        let base = lk.mask_entry_base();
        let mut rng = Rng(345);
        let rl: Vec<_> = (0..d).map(|_| rng.fp5()).collect();
        let tau: Vec<_> = (0..d).map(|_| rng.fp5()).collect();
        let (gamma, alpha, lambda, rho) = (rng.fp5(), rng.fp5(), rng.fp5(), rng.fp5());
        assert!(lookup_masks_full_rank(lk, &rl));
        assert!(!lookup_masks_full_rank(lk, &vec![E::ZERO; d]));
        let mut bad_corner = rl.clone();
        *bad_corner.last_mut().unwrap() = E::ZERO;
        assert!(!lookup_masks_full_rank(lk, &bad_corner));
        let pads = left.len() - 2 * LIMBS;
        for (a, b) in left[pads..].iter_mut().zip(&mut right[pads..]) {
            *a = f(rng.next_u64());
            *b = *a;
        }
        let tables = |z: &[F]| {
            let n: Vec<_> = (0..lk.num_entries())
                .map(|i| E::from_base(lk.num.row_dot(i, z)))
                .collect();
            let v: Vec<_> = (0..lk.num_entries())
                .map(|i| {
                    lk.den
                        .iter()
                        .rev()
                        .fold(E::ZERO, |a, m| a * gamma + E::from_base(m.row_dot(i, z)))
                })
                .collect();
            let mut h: Vec<_> = v.iter().map(|&val| alpha - val).collect();
            invert_lookup_denominators(&mut h[..base]).unwrap();
            for i in 0..base {
                h[i] *= n[i];
            }
            [n, v, h]
        };
        let weights = eq_table(&rl);
        let eval = |t: &[E]| {
            t.iter()
                .zip(&weights)
                .fold(E::ZERO, |a, (&x, &w)| a + x * w)
        };
        let mut ta = tables(&left);
        for cell in &mut ta[2][base..] {
            *cell = rng.fp5();
        }
        let initial = tables(&right);
        for j in 0..2 {
            let delta = (eval(&ta[j]) - eval(&initial[j])) * corner_factor(&rl, base).inverse();
            let shift = solve_pad(&rl, delta);
            for (p, s) in right[pads + j * LIMBS..].iter_mut().zip(shift) {
                *p += s;
            }
        }
        let mut tb = tables(&right);
        tb[2][base..].copy_from_slice(&ta[2][base..]);
        let shift = (eval(&ta[2]) - eval(&tb[2])) * weights[base].inverse();
        tb[2][base] += shift;
        for j in 0..3 {
            assert_eq!(eval(&ta[j]), eval(&tb[j]));
        }
        let rounds = |mut t: [Vec<E>; 3]| {
            let mut eq = eq_table(&tau);
            let mut selector = PrefixSelector {
                count: base,
                boundary: E::ZERO,
            };
            let mut polys = Vec::new();
            for &r in &rl {
                polys.push(lookup_round(
                    [&eq, &t[0], &t[1], &t[2]],
                    &selector,
                    alpha,
                    lambda,
                ));
                fold_in_place(&mut eq, r, false);
                for col in &mut t {
                    fold_in_place(col, r, false);
                }
                selector.fold(r);
            }
            polys
        };
        let helpers = [ta[2].clone(), tb[2].clone()];
        let (a, b) = (rounds(ta), rounds(tb));
        let ma = Mask::from_coeffs(
            (0..d)
                .map(|_| (0..=LOOKUP_DEGREE).map(|_| rng.fp5()).collect())
                .collect(),
        );
        let mut mb = Mask::from_coeffs(ma.coef.clone());
        for i in 0..d {
            let scale_inv = (rho * pow2(d - i - 1)).inverse();
            for j in 1..=LOOKUP_DEGREE {
                mb.coef[i][j] += (a[i][j] - b[i][j]) * scale_inv;
            }
        }
        let adjust = (ma.sum() - mb.sum()) * pow2(d).inverse();
        mb.coef[0][0] += adjust;
        assert_eq!(ma.sum(), mb.sum());
        for i in 0..d {
            let (ga, gb) = (ma.round_poly(&rl[..i]), mb.round_poly(&rl[..i]));
            for j in 0..=LOOKUP_DEGREE {
                assert_eq!(a[i][j] + rho * ga[j], b[i][j] + rho * gb[j]);
            }
        }
        let ll = LookupLayout::new(d).unwrap();
        let cells = 1 << ll.log_cells;
        let kernel = cell_weights_to_kernel(lookup_claim_cell_weights(&ll, &rl, lambda), cells);
        assert!(kernel[cells - ll.blind_cells..].iter().all(|v| v.is_zero()));
        let helper_tables = core::array::from_fn(|side| {
            let mut t = vec![F::ZERO; ll.mask_block(d, 0)];
            for (i, val) in helpers[side].iter().enumerate() {
                for (j, limb) in val.to_limbs().into_iter().enumerate() {
                    t[ll.limb_block(j) + i] = limb;
                }
            }
            [&ma, &mb][side].write(&mut t, LOOKUP_MASK_BITS, |i, j| ll.mask_block(i, j));
            t
        });
        pcs::tests::couple_lookup_openings(helper_tables, lookup_claim_terms(&ll, &rl, lambda), 91);
        // The main commitment's published numerator and tuple claims are equal.
        // Exercise their batched linear functional with the assignment PCS too.
        let mut w = vec![E::ZERO; shape.num_vars];
        lookup_column_add(&mut w, lk, &weights, [E::ONE, lambda], gamma);
        let terms = w
            .into_iter()
            .enumerate()
            .filter(|(_, weight)| !weight.is_zero())
            .map(|(i, weight)| TensorTerm {
                weight,
                point: block_point(i, &[]),
            })
            .collect();
        pcs::tests::couple_lookup_openings([left, right], terms, 117);
    }

    #[test]
    fn lookup_relation_roundtrip_wire_bound_and_tamper_rejection() {
        let build = |vals: [u64; 3]| {
            let mut cs = ConstraintSystem::new();
            let pub_sum = cs.public_input(f(vals[0] + vals[1] + vals[2]));
            let pairs: Vec<F> = (0..8u64).flat_map(|t| [f(t), f(17 * t + 3)]).collect();
            let tbl = cs.table(2, pairs);
            let a: Lc = cs.alloc(f(vals[0])).into();
            let b: Lc = cs.alloc(f(vals[1])).into();
            let c: Lc = cs.alloc(f(vals[2])).into();
            cs.enforce_byte(&a);
            cs.enforce_in_table(tbl, &[b.clone(), c.clone()]);
            cs.enforce_equal(&a.plus(&b).plus(&c), &pub_sum.into());
            cs.finish_v2()
        };
        let (shape, z) = build([241, 5, 88]);
        let public = publics(&shape, &z);
        for profile in Profile::ALL {
            let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
            assert!(proof.lookup.is_some());
            assert!(verify(&shape, &public, STATEMENT, profile, &proof));
            let bytes = proof.to_bytes();
            let max_bytes = bounds::max_proof_bytes(profile, &shape).unwrap();
            assert!(bytes.len() <= max_bytes, "{} > {}", bytes.len(), max_bytes);
            assert_eq!(
                ZkHemV2Proof::from_bytes(&bytes, &shape),
                Some(proof.clone())
            );
            let mut tampered = proof.clone();
            tampered.lookup.as_mut().unwrap().values[2] += Fp5::ONE;
            assert!(!verify(&shape, &public, STATEMENT, profile, &tampered));
            let mut bad_nonce = proof.clone();
            bad_nonce.lookup.as_mut().unwrap().helper_tree_nonce[0] ^= 1;
            assert!(!verify(&shape, &public, STATEMENT, profile, &bad_nonce));
        }
        // Out-of-range byte (`256`) is rejected by `prove` and by `verify` when unchecked.
        let (_, bad_z) = build([256, 5, 88]);
        assert_eq!(
            prove(
                &shape,
                bad_z.clone(),
                STATEMENT,
                Profile::TurboShakeJohnson400,
                &SEED
            ),
            Err(ZkHemV2Error::Unsatisfied)
        );
        let forged = prove_inner(
            &shape,
            bad_z,
            STATEMENT,
            Profile::TurboShakeJohnson400,
            &SEED,
            false,
            None,
        )
        .unwrap();
        assert!(!verify(
            &shape,
            &[f(256 + 5 + 88)],
            STATEMENT,
            Profile::TurboShakeJohnson400,
            &forged
        ));
    }

    #[test]
    fn every_proof_field_including_tree_nonce_is_bound() {
        let (shape, z) = fixture(40);
        let profile = Profile::TurboShakeJohnson400;
        let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
        let public = publics(&shape, &z);
        assert!(verify(&shape, &public, STATEMENT, profile, &proof));
        let mut bad_nonce = proof.clone();
        bad_nonce.tree_nonce[17] ^= 0x40;
        assert!(!verify(&shape, &public, STATEMENT, profile, &bad_nonce));
        let mut bad_root = proof.clone();
        bad_root.root[10] ^= 1;
        assert!(!verify(&shape, &public, STATEMENT, profile, &bad_root));
        let bytes = proof.to_bytes();
        for at in (10..bytes.len()).step_by(bytes.len() / 97) {
            let mut bad = bytes.clone();
            bad[at] ^= 0x10;
            let accepted = ZkHemV2Proof::from_bytes(&bad, &shape)
                .is_some_and(|p| verify(&shape, &public, STATEMENT, profile, &p));
            assert!(!accepted, "byte {at}");
        }
    }

    #[test]
    fn public_closing_and_v2_closing_reject_each_other() {
        let (shape2, z2) = fixture(40);
        let (shape_pub, z_pub) = relation(3, 5, 11, 40).finish();
        let profile = Profile::CshakeJohnson400;
        assert_eq!(shape_pub.closing(), Closing::Public);
        assert_eq!(shape2.closing(), Closing::V2);
        assert_ne!(shape_pub.digest(), shape2.digest());
        assert!(layout_of(&shape_pub).is_none());
        assert_eq!(
            prove(&shape_pub, z_pub, STATEMENT, profile, &SEED),
            Err(ZkHemV2Error::UnsupportedRelation)
        );
        let p2 = prove(&shape2, z2.clone(), STATEMENT, profile, &SEED).unwrap();
        assert!(ZkHemV2Proof::from_bytes(&p2.to_bytes(), &shape_pub).is_none());
    }

    /// One seed must never yield the same masks under two profiles, statements, witnesses
    /// or seeds: repeated masks under different challenges reveal linear functionals of
    /// the witness (SECURITY.md V2.5).
    #[test]
    fn coins_do_not_repeat_across_profiles() {
        let (shape, z) = fixture(40);
        let (shape_w, z_w) = relation(3, 6, 11, 40).finish_v2();
        assert_eq!(shape, shape_w);
        assert_ne!(z, z_w);
        let cshake = Profile::CshakeJohnson400;
        let base = prove(&shape, z.clone(), STATEMENT, cshake, &SEED).unwrap();
        let others = [
            prove(
                &shape,
                z.clone(),
                STATEMENT,
                Profile::TurboShakeJohnson400,
                &SEED,
            ),
            prove(&shape, z.clone(), b"another statement", cshake, &SEED),
            prove(&shape, z_w, STATEMENT, cshake, &SEED),
            prove(&shape, z.clone(), STATEMENT, cshake, &[8u8; 32]),
        ];
        for other in others {
            let other = other.unwrap();
            assert_ne!(base.row_mask_sum, other.row_mask_sum);
            assert_ne!(base.col_mask_sum, other.col_mask_sum);
            assert_ne!(base.tree_nonce, other.tree_nonce);
        }
        // Control: the derivation is deterministic, so the differences above come from
        // the changed input alone.
        assert_eq!(base, prove(&shape, z, STATEMENT, cshake, &SEED).unwrap());
    }

    #[test]
    fn blinders_match_the_opened_view_and_are_fresh_per_seed() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let sched = schedule(log_cells).unwrap();
            let dims = pcs::stage_dims(log_cells, &sched).unwrap();
            let d0 = dims[0];
            let layout = Layout::new(ShapeSize {
                log_rows: log_cells - 1,
                num_vars: 1 << (log_cells - 2),
                num_public: 1,
            })
            .unwrap();
            if layout.log_cells == log_cells {
                assert_eq!(
                    layout.blind_cells,
                    d0.queries * d0.arity() + 25 * d0.arity(),
                    "2^{log_cells} cells"
                );
            }
        }
    }

    #[test]
    fn cell_weights_and_tensor_terms_are_the_same_functional() {
        let (shape, _) = fixture(300);
        let layout = layout_of(&shape).unwrap();
        let mut rng = Rng(5);
        let rx: Vec<E> = (0..shape.log_rows).map(|_| rng.fp5()).collect();
        let ry: Vec<E> = (0..layout.var_bits).map(|_| rng.fp5()).collect();
        let inp = ClaimInputs {
            layout: &layout,
            log_rows: shape.log_rows,
            num_public: shape.num_public,
            rx: &rx,
            ry: &ry,
            lambda: rng.fp5(),
            rho2: rng.fp5(),
            matrix_at_point: rng.fp5(),
        };
        let weights = claim_cell_weights(&inp);
        let terms = claim_terms(&inp);
        let cells = 1usize << layout.log_cells;
        let table: Vec<F> = (0..cells).map(|_| f(rng.next_u64())).collect();
        let by_cells = weights
            .iter()
            .zip(&table)
            .fold(E::ZERO, |acc, (&w, &z)| acc + w.mul_base(z));
        let eval = |point: &[E]| {
            let eq = eq_table(point);
            eq.iter()
                .zip(&table)
                .fold(E::ZERO, |acc, (&e, &z)| acc + e.mul_base(z))
        };
        let by_terms = terms
            .iter()
            .fold(E::ZERO, |acc, t| acc + t.weight * eval(&t.point));
        assert_eq!(by_cells, by_terms);
    }
}
