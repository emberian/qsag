// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Clean-room mathematical reference oracles for exact rational subset-cover bounds,
//! set-theoretic `PORS+FP` Octopus multiproof covers, `FrontierSumFts` combinatorics,
//! and multi-field framed NIST SP 800-185 `cSHAKE256`.

use std::cmp::Ordering;

use crate::cshake256_nist_sp800_185_ref;

/// Minimal exact arbitrary-precision unsigned integer (little-endian base-$2^{64}$ limbs)
/// for zero-float verification of Lean `Nat` binomial/falling-factorial bounds and
/// `FrontierSumFts` DP cardinalities (`N_root(h, L) * D(L, S)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactNat(Vec<u64>);

impl ExactNat {
    pub fn zero() -> Self {
        Self(Vec::new())
    }

    pub fn from_u64(v: u64) -> Self {
        if v == 0 {
            Self::zero()
        } else {
            Self(vec![v])
        }
    }

    pub fn from_u64_limbs_le(limbs: &[u64]) -> Self {
        let mut out = Self(limbs.to_vec());
        out.trim();
        out
    }

    fn trim(&mut self) {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    pub fn bit_len(&self) -> usize {
        match self.0.last() {
            None => 0,
            Some(&top) => (self.0.len() - 1) * 64 + (64 - top.leading_zeros() as usize),
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let max_len = self.0.len().max(rhs.0.len());
        let mut out = Vec::with_capacity(max_len + 1);
        let mut carry = 0u128;
        for i in 0..max_len {
            let a = *self.0.get(i).unwrap_or(&0) as u128;
            let b = *rhs.0.get(i).unwrap_or(&0) as u128;
            let sum = a + b + carry;
            out.push(sum as u64);
            carry = sum >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        let mut res = Self(out);
        res.trim();
        res
    }

    pub fn mul_u64(&self, rhs: u64) -> Self {
        if self.is_zero() || rhs == 0 {
            return Self::zero();
        }
        let mut out = Vec::with_capacity(self.0.len() + 1);
        let mut carry = 0u128;
        for &limb in &self.0 {
            let prod = (limb as u128) * (rhs as u128) + carry;
            out.push(prod as u64);
            carry = prod >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        let mut res = Self(out);
        res.trim();
        res
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }
        let mut out = vec![0u64; self.0.len() + rhs.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &b) in rhs.0.iter().enumerate() {
                let acc = (out[i + j] as u128) + (a as u128) * (b as u128) + carry;
                out[i + j] = acc as u64;
                carry = acc >> 64;
            }
            out[i + rhs.0.len()] += carry as u64;
        }
        let mut res = Self(out);
        res.trim();
        res
    }

    pub fn pow_u32(&self, mut exp: u32) -> Self {
        let mut acc = Self::from_u64(1);
        let mut base = self.clone();
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(&base);
            }
            exp >>= 1;
            if exp > 0 {
                base = base.mul(&base);
            }
        }
        acc
    }

    pub fn shl_bits(&self, bits: usize) -> Self {
        if self.is_zero() || bits == 0 {
            return self.clone();
        }
        let word_shift = bits / 64;
        let bit_shift = bits % 64;
        let mut out = vec![0u64; word_shift + self.0.len() + usize::from(bit_shift != 0)];
        if bit_shift == 0 {
            out[word_shift..word_shift + self.0.len()].copy_from_slice(&self.0);
        } else {
            let mut carry = 0u64;
            for (i, &w) in self.0.iter().enumerate() {
                out[word_shift + i] = (w << bit_shift) | carry;
                carry = w >> (64 - bit_shift);
            }
            out[word_shift + self.0.len()] = carry;
        }
        let mut res = Self(out);
        res.trim();
        res
    }

    pub fn div_rem_u32(&self, divisor: u32) -> (Self, u32) {
        assert!(divisor > 0);
        let d = divisor as u128;
        let mut quot = vec![0u64; self.0.len()];
        let mut rem = 0u128;
        for (i, &w) in self.0.iter().enumerate().rev() {
            let cur = (rem << 64) | (w as u128);
            quot[i] = (cur / d) as u64;
            rem = cur % d;
        }
        let mut q = Self(quot);
        q.trim();
        (q, rem as u32)
    }

    pub fn to_decimal_string(&self) -> String {
        if self.is_zero() {
            return "0".to_owned();
        }
        let mut cur = self.clone();
        let mut chunks = Vec::new();
        while !cur.is_zero() {
            let (q, r) = cur.div_rem_u32(1_000_000_000);
            chunks.push(r);
            cur = q;
        }
        let mut out = chunks.pop().unwrap().to_string();
        for chunk in chunks.into_iter().rev() {
            use std::fmt::Write as _;
            let _ = write!(out, "{chunk:09}");
        }
        out
    }
}

impl Ord for ExactNat {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => {
                for (&a, &b) in self.0.iter().rev().zip(other.0.iter().rev()) {
                    match a.cmp(&b) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            ord => ord,
        }
    }
}

impl PartialOrd for ExactNat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Exact falling factorial `ffTop(n, k) = n * (n - 1) * ... * (n - k + 1)` matching
/// `Qsag.PorsFpSecurity.ffTop` (`0` if `n < k`).
pub fn ff_top_exact(n: u64, k: usize) -> ExactNat {
    if (n as usize) < k {
        return ExactNat::zero();
    }
    let mut acc = ExactNat::from_u64(1);
    for i in 0..k {
        acc = acc.mul_u64(n - i as u64);
    }
    acc
}

/// Exact Lean `AtLeastBits b num den`: returns `true` iff `0 < num` and `num * 2^b <= den`
/// (i.e. `num / den <= 2^(-b)`).
pub fn rational_at_least_bits(bits: usize, num: &ExactNat, den: &ExactNat) -> bool {
    !num.is_zero() && &num.shl_bits(bits) <= den
}

/// Exact floor of `-log2(num / den)` in whole bits: unique `b` with
/// `num * 2^b <= den < num * 2^(b + 1)` (requires `0 < num <= den`).
pub fn exact_neg_log2_floor_bits(num: &ExactNat, den: &ExactNat) -> usize {
    assert!(!num.is_zero() && num <= den);
    let approx = den.bit_len().saturating_sub(num.bit_len());
    let mut b = approx.saturating_sub(1);
    while &num.shl_bits(b + 1) <= den {
        b += 1;
    }
    assert!(rational_at_least_bits(b, num, den));
    assert!(!rational_at_least_bits(b + 1, num, den));
    b
}

/// Exact floor of `-1000 * log2(num / den)` (millibits), matching `Qsag.PorsFpSecurity.MilliAtLeast`:
/// unique `m` with `num^1000 * 2^m <= den^1000 < num^1000 * 2^(m + 1)`.
pub fn exact_neg_log2_floor_millibits(num: &ExactNat, den: &ExactNat) -> usize {
    assert!(!num.is_zero() && num <= den);
    let num_1000 = num.pow_u32(1000);
    let den_1000 = den.pow_u32(1000);
    exact_neg_log2_floor_bits(&num_1000, &den_1000)
}

/// Set-theoretic specification of `PORS+FP` `octopus_positions`:
/// Node `(h, idx)` at level `h in 0..tree_height` is in the canonical sibling cover iff
/// `indices` is non-empty, strictly increasing, in `[0, 2^tree_height)`, NO leaf in `indices`
/// has ancestor `idx` at height `h`, and SOME leaf in `indices` has sibling ancestor `idx ^ 1`.
pub fn octopus_cover_ref(tree_height: usize, indices: &[u32]) -> Option<Vec<(u32, u32)>> {
    if tree_height > 31
        || indices.is_empty()
        || indices.windows(2).any(|w| w[0] >= w[1])
        || u64::from(*indices.last()?) >= (1u64 << tree_height)
    {
        return None;
    }
    let mut cover = Vec::new();
    for h in 0..tree_height as u32 {
        let mut sibling_candidates: Vec<u32> = indices.iter().map(|&x| (x >> h) ^ 1).collect();
        sibling_candidates.sort_unstable();
        sibling_candidates.dedup();
        for cand in sibling_candidates {
            let is_ancestor = indices.iter().any(|&x| (x >> h) == cand);
            if !is_ancestor {
                cover.push((h, cand));
            }
        }
    }
    Some(cover)
}

/// Independent exact combinatorics recurrence `(N_root(h, L), D(L, S), M(h, w, L, S))`
/// matching `Qsag.frontierRootSubCount` and `Qsag.frontierDecCount` in
/// `FrontierCompact1122AndCorduroySecurity.lean`.
pub fn frontier_fts_cardinalities_ref(
    h: usize,
    w: usize,
    l: usize,
    s: usize,
) -> (ExactNat, ExactNat, ExactNat) {
    let mut sub: Vec<Vec<ExactNat>> = vec![vec![ExactNat::zero(); l + 1]; h + 1];
    if l >= 1 {
        sub[0][1] = ExactNat::from_u64(1);
    }
    for t in 1..=h {
        if t < h && l >= 1 {
            sub[t][1] = ExactNat::from_u64(1);
        }
        for ell in 2..=l {
            let mut acc = ExactNat::zero();
            for left_sz in 1..ell {
                let prod = sub[t - 1][left_sz].mul(&sub[t - 1][ell - left_sz]);
                acc = acc.add(&prod);
            }
            sub[t][ell] = acc;
        }
    }

    let mut dec = vec![ExactNat::zero(); s + 1];
    dec[0] = ExactNat::from_u64(1);
    for _ in 0..l {
        let mut next = vec![ExactNat::zero(); s + 1];
        for (u, slot) in next.iter_mut().enumerate() {
            let mut acc = ExactNat::zero();
            for a in 0..w.min(u + 1) {
                acc = acc.add(&dec[u - a]);
            }
            *slot = acc;
        }
        dec = next;
    }

    let n_root = sub[h][l].clone();
    let d_card = dec[s].clone();
    let total = n_root.mul(&d_card);
    (n_root, d_card, total)
}

/// Multi-field `u64_le` length-framed NIST SP 800-185 `cSHAKE256("", custom)` reference oracle,
/// built strictly atop `sha3` and `tiny-keccak` (`0` `qsag-*` sponge code).
pub fn cshake256_framed_nist_ref(custom: &[u8], fields: &[&[u8]], out_len: usize) -> Vec<u8> {
    let total_payload: usize = 8 + fields.iter().map(|f| 8 + f.len()).sum::<usize>();
    let mut framed = Vec::with_capacity(total_payload);
    framed.extend_from_slice(&(fields.len() as u64).to_le_bytes());
    for f in fields {
        framed.extend_from_slice(&(f.len() as u64).to_le_bytes());
        framed.extend_from_slice(f);
    }
    cshake256_nist_sp800_185_ref(b"", custom, &framed, out_len)
}

/// 32-byte fixed-output helper over [`cshake256_framed_nist_ref`].
pub fn cshake256_framed_32_nist_ref(custom: &[u8], fields: &[&[u8]]) -> [u8; 32] {
    cshake256_framed_nist_ref(custom, fields, 32)
        .try_into()
        .expect("32-byte cSHAKE256 output")
}
