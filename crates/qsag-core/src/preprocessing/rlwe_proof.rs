//! Signed-monomial OR-Sigma proofs of short Ring-LWE receiver witnesses.

use super::rlwe_poly::rlwe_barrett_rem_u32;
use super::*;

/// Number of parallel/sequential repetitions in [`RlweReceiverZkPok`] (`24 * 11 = 264` classical challenge bits /
/// `132` quantum Grover bits over pairwise-invertible signed monomials $\pm X^k$).
pub const RLWE_ZKPOK_REPS: usize = 24;
/// Bit-width of one single signed-monomial challenge `c in {0..2048}` (`deg = c & 0x3ff`, `sign = (c >> 10) & 1`),
/// matching `SignedMonomialChal.ofFinIndex` / `signedMonomial_challenge_set_pairwise_invertible` in Lean.
pub const RLWE_ZKPOK_CHAL_BITS: u32 = 11;
const RLWE_ZKPOK_CHAL_MASK: u32 = (1u32 << RLWE_ZKPOK_CHAL_BITS) - 1;
/// Joint Gaussian rejection parameters over the single signed-monomial challenge set
/// $\mathcal{C} = \{\pm X^k : 0 \le k < 1024\}$ (`2048` challenges per repetition, `100%` pairwise
/// invertible over $R_{12289}$ via $(c_1 - c_2) g(X) = 2$). Key generation conditions the two
/// $\mathrm{CBD}_1$ polynomials on total squared norm $\le 1376$ (Chernoff tail $< 2^{-178}$).
/// Because negacyclic multiplication by $\pm X^k$ is an exact $\ell_2$ and $\ell_\infty$ isometry,
/// every coordinate of the shift lies in $[-1, 1]$ and the 24-repetition response shift satisfies
/// $\|v\|_2^2 \le 24 \times 1376 = 33{,}024$.
///
/// Masks follow $\exp(-y^2 / (2 \cdot 700^2))$ on $[-3072, 3071]$. Accept $z = y + v$ only in
/// $[-3070, 3069]$, with probability $\min(1, \exp((\|y\|^2 - \|z\|^2)/980000) / M)$ where
/// $M = \exp(\lceil 980000 \ln(40) \rceil / 980000)$ (`RLWE_GAUSSIAN_LOG_M = 3_615_102`).
/// Every target response has preimages inside $[-3072, 3071]$ since $\|v\|_\infty \le 1$.
/// Exact discrete-Gaussian MGF domination over $\|v\|_2^2 \le 33{,}024, \|v\|_\infty \le 1$ bounds
/// the unclipped tail below $2^{-143}$ ($< 2^{-128}$, and $< 2^{-2592}$ per single repetition at $M = 24$);
/// conditioning on acceptance and the response-box mass ($> 0.99$) leaves statistical HVZK distance
/// and secret-dependent abort indicator bias strictly below $2^{-128}$ (`0` QROM claim).
///
/// Sampling uses uniform proposals and fixed-work, 192-bit Bernoulli rejection,
/// with no mask-indexed table access. Each exponential evaluation has absolute
/// error $< 64 / 2^{192}$. Expected acceptance is $\approx 0.9926 / 40 \approx 1 / 40.3$,
/// and all rejections restart the entire joint real-branch transcript.
///
/// Bimodal rejection (Ducas–Durmus–Lepoint–Lyubashevsky, BLISS: `z = y + b v` with a secret
/// sign `b` and acceptance `1 / (M exp(-|v|^2 / 2 sigma^2) cosh(<z, v> / sigma^2))`) would give
/// `M = exp(33_024 / 980_000) < 1.04` here, but it does not apply to this statement. The sign
/// must cancel in the verification equation, which BLISS obtains from a homogeneous relation
/// `A S = q (mod 2q)`; for `Y = a s + e` that means proving `[2a | 2 | q - 2Y] (s, e, 1) = q
/// (mod 2q)` with a third response `z_3 = y_3 + b c`. Two accepting transcripts then agree only
/// modulo `q`-multiples of the challenge difference: the extractor learns
/// `a ds + de = Y dz_3 (mod q)` for a short `dz_3` with `dz_3 = c - c' (mod 2)` that the prover
/// chooses, not for `c - c'` itself. The exact extraction this proof relies on, where
/// `c - c'` is a difference of signed monomials dividing 2, is lost, and at `q = 12289` (fully
/// split, `|dz_3|_inf` up to `q / 2`) a relaxed witness with an arbitrary short denominator
/// carries no soundness for the receiver's key. `M = 40` is the cost of exact extraction at
/// this modulus across `24` joint repetitions.
pub(super) const RLWE_ZKPOK_Z_BOUND: i16 = 3070;

/// Per-branch squared Euclidean norm cap `‖z_s‖_2^2 + ‖z_e‖_2^2 <= 1_500_000_000`
/// across the `2 * 1024 = 2048` coordinates of one `(z_s[rep], z_e[rep])` pair.
///
/// Under discrete Gaussian masks of parameter `2 * sigma^2 = 980_000` (`E[Z^2] = 489_887.2`,
/// `E[‖z_s‖_2^2 + ‖z_e‖_2^2] = 1_003_288_988`), exact MGF Chernoff concentration gives per-pair
/// tail `< 2^-138.02` (`< 2^-132.44 < 2^-128` union-bounded across all 48 branch pairs in 24
/// repetitions). Forking two accepting transcripts under distinct signed monomials extracts a
/// short Ring-SIS vector `(s_sis, e_sis)` with `‖s_sis‖_2^2 + ‖e_sis‖_2^2 <= 6_060_827_392`
/// (`‖(s_sis, e_sis)‖_2 <= 77_851`, root Hermite factor `delta_0 = 1.003206`), refuting the
/// `s = 1, e = centered(-A)` public-relation bypass (`E[‖centered(-A)‖_2^2] = 12_886_999_040`,
/// tail `< 2^-310`).
pub const RLWE_ZKPOK_PAIR_L2_SQ_BOUND: u64 = 1_500_000_000;

#[inline]
fn rlwe_pair_l2_sq(zs: &[i16; RLWE_N], ze: &[i16; RLWE_N]) -> u64 {
    let mut acc = 0u64;
    for i in 0..RLWE_N {
        let vs = i64::from(zs[i]);
        let ve = i64::from(ze[i]);
        acc += (vs * vs) as u64 + (ve * ve) as u64;
    }
    acc
}

/// Constant-time HVZK OR-Sigma proof of short Ring-LWE witness knowledge for [`RlweOtReceiverMsg`]:
/// proves knowledge of short `(s, e)` on EITHER `Y_0 = pk0` OR `Y_1 = pk0 + t_crs` under `a_crs`
/// over the 11-bit pairwise-invertible signed-monomial challenge set $\pm X^k$ (`24` repetitions, `264` classical / `132` Grover bits).
#[derive(Clone, Debug)]
pub struct RlweReceiverZkPok {
    pub chal0: [u32; RLWE_ZKPOK_REPS],
    pub chal1: [u32; RLWE_ZKPOK_REPS],
    pub z_s0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_s1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
}

/// Realize 11-bit signed-monomial challenge `u` (`deg = u & 0x3ff`, `sign = (u >> 10) & 1`) in $R_q$
/// in constant time (`false -> +X^deg`, `true -> -X^deg`, matching `SignedMonomialChal.ofFinIndex`).
#[cfg(test)]
#[inline]
pub(super) fn poly_from_chal11(u: u32) -> RlwePoly {
    let deg = (u & 0x3FF) as usize;
    let sign = ((u >> 10) & 1) as u16;
    let mut coeffs = [0u16; RLWE_N];
    let value = 1 ^ (0u16.wrapping_sub(sign) & (1 ^ (RLWE_Q - 1)));
    for (i, coeff) in coeffs.iter_mut().enumerate() {
        *coeff = value & 0u16.wrapping_sub(black_box((i == deg) as u16));
    }
    RlwePoly(coeffs)
}

/// Multiply public `poly` by public signed monomial `(-1)^{sign} X^{deg}` in $R_q = \mathbb{Z}_q[X]/(X^{1024}+1)$
/// in $O(N)$ (`0` NTTs).
#[inline]
pub(super) fn mul_chal11_public(poly: &RlwePoly, u: u32) -> RlwePoly {
    let deg = (u & 0x3FF) as usize;
    let is_neg = ((u >> 10) & 1) == 1;
    let mut out = [0u16; RLWE_N];
    for (dst, slot) in out.iter_mut().enumerate() {
        let (src, wrap_neg) = if dst >= deg {
            (dst - deg, is_neg)
        } else {
            (dst + RLWE_N - deg, !is_neg)
        };
        let coeff = poly.0[src];
        *slot = if wrap_neg && coeff != 0 {
            RLWE_Q - coeff
        } else {
            coeff
        };
    }
    RlwePoly(out)
}

/// Constant-time 10-stage barrel-rotator negacyclic product `(-1)^{sign} X^{deg} * poly` over
/// signed integer coefficients (`0` NTTs, fixed compile-time offsets, `0` secret/challenge branches).
#[inline]
pub(super) fn mul_chal11_signed_ct(poly: &[i16; RLWE_N], u: u32) -> [i16; RLWE_N] {
    let u = black_box(u);
    let mut cur = *poly;
    let sign_mask = 0i16.wrapping_sub(((u >> 10) & 1) as i16);
    for x in &mut cur {
        *x = (*x ^ sign_mask).wrapping_sub(sign_mask);
    }
    let mut next = [0i16; RLWE_N];
    for stage in 0..10u32 {
        let shift = 1usize << stage;
        let sel = 0i16.wrapping_sub(((u >> stage) & 1) as i16);
        let tail_base = RLWE_N - shift;
        for dst in 0..shift {
            let p = cur[dst];
            let shifted = cur[tail_base + dst].wrapping_neg();
            next[dst] = p ^ (sel & (p ^ shifted));
        }
        for dst in shift..RLWE_N {
            let p = cur[dst];
            let shifted = cur[dst - shift];
            next[dst] = p ^ (sel & (p ^ shifted));
        }
        core::mem::swap(&mut cur, &mut next);
    }
    qsag_asm::volatile_fill(&mut next, 0);
    cur
}

#[inline]
fn rlwe_ternary_to_i16_ct(poly: &RlwePoly) -> [i16; RLWE_N] {
    let mut out = [0i16; RLWE_N];
    for (dst, &c) in out.iter_mut().zip(&poly.0) {
        let is_one = (c == 1) as i16;
        let is_neg_one = (c == RLWE_Q - 1) as i16;
        *dst = is_one - is_neg_one;
    }
    out
}

#[inline]
pub(super) fn signed_box_to_rlwe_poly(v: &[i16; RLWE_N]) -> RlwePoly {
    let mut out = [0u16; RLWE_N];
    for i in 0..RLWE_N {
        let shifted = (i32::from(v[i]) + 3 * i32::from(RLWE_Q)) as u32;
        out[i] = rlwe_barrett_rem_u32(shifted);
    }
    RlwePoly(out)
}

// Fixed-point unsigned fractions in little-endian limbs, with denominator 2^192.
// The schoolbook product retains the high half, rounding toward zero.
#[inline(always)]
pub(super) fn gaussian_fraction_mul(a: [u64; 3], b: [u64; 3]) -> [u64; 3] {
    let a0 = u128::from(a[0]);
    let a1 = u128::from(a[1]);
    let a2 = u128::from(a[2]);
    let b0 = u128::from(b[0]);
    let b1 = u128::from(b[1]);
    let b2 = u128::from(b[2]);

    let p00 = a0 * b0;
    let c0 = p00 >> 64;

    let s1_a = a0 * b1 + c0;
    let p1_a = s1_a as u64;
    let c1_a = s1_a >> 64;

    let s2_a = a0 * b2 + c1_a;
    let p2_a = s2_a as u64;
    let p3_a = (s2_a >> 64) as u64;

    let s1_b = a1 * b0 + u128::from(p1_a);
    let c1_b = s1_b >> 64;

    let s2_b = a1 * b1 + u128::from(p2_a) + c1_b;
    let p2_b = s2_b as u64;
    let c2_b = s2_b >> 64;

    let s3_b = a1 * b2 + u128::from(p3_a) + c2_b;
    let p3_b = s3_b as u64;
    let p4_b = (s3_b >> 64) as u64;

    let s2_c = a2 * b0 + u128::from(p2_b);
    let c2_c = s2_c >> 64;

    let s3_c = a2 * b1 + u128::from(p3_b) + c2_c;
    let p3 = s3_c as u64;
    let c3_c = s3_c >> 64;

    let s4_c = a2 * b2 + u128::from(p4_b) + c3_c;
    let p4 = s4_c as u64;
    let p5 = (s4_c >> 64) as u64;

    [p3, p4, p5]
}

#[inline(always)]
pub(super) fn gaussian_fraction_lt(a: [u64; 3], b: [u64; 3]) -> bool {
    let mut borrow = false;
    for (&ai, &bi) in a.iter().zip(&b) {
        let (diff, first) = ai.overflowing_sub(bi);
        let (_, second) = diff.overflowing_sub(u64::from(borrow));
        borrow = first | second;
    }
    borrow
}

// Gaussian sampling by a uniform proposal and fixed-work Bernoulli rejection.
// Unlike indexed CDT lookup, this makes neither branches nor memory addresses
// depend on the accepted mask. Trial counts are independent of the final sample.
//
// The decision is `random < probability` on 192 bits. Two Q64 bounds settle it
// from the high limb alone in all but a sliver of cases: at or above the upper
// bound the proposal is rejected, below the lower bound it is accepted. Both
// outcomes equal what the full comparison returns, and every surviving
// proposal draws its low limbs first, so the sampler's outputs and its use of
// `rng` are those of the comparison without the bounds. The 192-bit path runs
// only for a high limb between the bounds: for an accepted proposal that has
// probability below 49 / (2^64 * probability), under 2^-44 even at the edge of
// the box, so the path taken is independent of the accepted value up to that.
#[cfg(test)]
pub(super) fn sample_gaussian_box(rng: &mut PartyPrivateRng, response: bool) -> [i16; RLWE_N] {
    let half = if response {
        RLWE_ZKPOK_Z_BOUND
    } else {
        RLWE_ZKPOK_Z_BOUND + 2
    };
    let mut coins = [0u8; 26];
    let out = core::array::from_fn(|_| {
        loop {
            rng.fill_bytes(&mut coins[..10]);
            let proposal = u16::from_le_bytes([coins[0], coins[1]]) & 0x1fff;
            let valid = proposal < 2 * half as u16;
            let mask = 0u16.wrapping_sub(u16::from(valid));
            let x = (proposal & mask) as i16 - half;
            let exponent = (i64::from(x) * i64::from(x)) as u64;
            let high = u64::from_le_bytes(core::array::from_fn(|j| coins[2 + j]));
            // Reject only when the cheap upper bound proves that the full 192-bit
            // comparison would reject. Every accepted proposal still takes the same
            // fixed-work exact path; discarded proposals are independent of it.
            let upper = gaussian_exp_upper_bound(exponent);
            if black_box(u128::from(high) >= upper) {
                continue;
            }
            // The upper-bound rejection is decided by the high limb alone. Draw
            // the other two independent limbs only for surviving proposals. Rejected
            // proposals cannot affect the next sample.
            rng.fill_bytes(&mut coins[10..]);
            if black_box(high < gaussian_exp_lower_bound(exponent)) {
                if valid {
                    break x;
                }
                continue;
            }
            let random = [
                u64::from_le_bytes(core::array::from_fn(|j| coins[10 + j])),
                u64::from_le_bytes(core::array::from_fn(|j| coins[18 + j])),
                high,
            ];
            let probability = gaussian_exp_probability::<24>(exponent);
            let accept = gaussian_fraction_lt(random, probability) & valid;
            if black_box(accept) {
                break x;
            }
        }
    });
    wipe_bytes(&mut coins);
    out
}

// Ignore the low fourteen exponent bits for this bound only. This increases
// the ideal probability by at most exp(16383/980000) < 1.017, while needing
// only ten Q64 products. The actual decision below still uses all 192 bits.
// Relative to the Q192 computation with those exponent bits cleared, initial
// truncation loses <1 Q64 unit; each of ten factors and product truncations
// loses <1 more. Adding 21 therefore gives a strict upper bound. Keep the sum
// in u128 because it can exceed u64::MAX near probability one.
// No table index, loop bound or branch depends on the proposal.
#[cfg(test)]
#[inline(always)]
pub(super) fn gaussian_exp_upper_bound(exponent: u64) -> u128 {
    let mut probability = u64::MAX;
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[14..24].iter().enumerate() {
        let multiplied = ((u128::from(probability) * u128::from(factor[2])) >> 64) as u64;
        let mask = 0u64.wrapping_sub((exponent >> (bit + 14)) & 1);
        probability ^= mask & (probability ^ multiplied);
    }
    u128::from(probability) + 21
}

// Q64 chain over all 24 exponent bits, truncating at every step. It never
// exceeds the high limb of `gaussian_exp_probability::<24>`: if `v <= p >> 128`
// and `f_hi = f >> 128`, then `v * f_hi * 2^256 <= p * f`, hence
// `(v * f_hi) >> 64 <= ((p * f) >> 192) >> 128`, and the masked selection keeps
// the inequality. It falls short of that limb by fewer than 49 units (one per
// truncated product, one per truncated factor). Fixed work, no table index or
// branch on the proposal.
#[cfg(test)]
#[inline(always)]
pub(super) fn gaussian_exp_lower_bound(exponent: u64) -> u64 {
    let mut probability = u64::MAX;
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[..24].iter().enumerate() {
        let multiplied = ((u128::from(probability) * u128::from(factor[2])) >> 64) as u64;
        let mask = 0u64.wrapping_sub((exponent >> bit) & 1);
        probability ^= mask & (probability ^ multiplied);
    }
    probability
}

#[inline(always)]
fn gaussian_exp_upper_bound_x8(exponents: &[u64; 8]) -> [u128; 8] {
    let mut prob = [u64::MAX; 8];
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[14..24].iter().enumerate() {
        let f = u128::from(factor[2]);
        let shift = bit + 14;
        for lane in 0..8 {
            let multiplied = ((u128::from(prob[lane]) * f) >> 64) as u64;
            let mask = 0u64.wrapping_sub((exponents[lane] >> shift) & 1);
            prob[lane] ^= mask & (prob[lane] ^ multiplied);
        }
    }
    core::array::from_fn(|lane| u128::from(prob[lane]) + 21)
}

#[inline(always)]
fn gaussian_exp_lower_bound_x8(exponents: &[u64; 8]) -> [u64; 8] {
    let mut prob = [u64::MAX; 8];
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[..24].iter().enumerate() {
        let f = u128::from(factor[2]);
        for lane in 0..8 {
            let multiplied = ((u128::from(prob[lane]) * f) >> 64) as u64;
            let mask = 0u64.wrapping_sub((exponents[lane] >> bit) & 1);
            prob[lane] ^= mask & (prob[lane] ^ multiplied);
        }
    }
    prob
}

/// 8-lane batched constant-time Bernoulli discrete-Gaussian box sampler over `KeccakState8x`.
/// Evaluates the exact same Q64 upper/lower bounds and 192-bit Bernoulli predicate as
/// `sample_gaussian_box`, unrolling 8 independent `u64 x u64 -> u128` pipelines per step.
struct GaussianSampler8x {
    prop_init: qsag_asm::KeccakState8x,
    prop_state: qsag_asm::KeccakState8x,
    prop_ctr: u64,
    prop_slot: usize,
    tail_init: qsag_asm::KeccakState8x,
    tail_state: qsag_asm::KeccakState8x,
    tail_ctr: u64,
    tail_slot: usize,
}

impl Drop for GaussianSampler8x {
    fn drop(&mut self) {
        for r in 0..25 {
            wipe_u64s(&mut self.prop_init.0[r]);
            wipe_u64s(&mut self.prop_state.0[r]);
            wipe_u64s(&mut self.tail_init.0[r]);
            wipe_u64s(&mut self.tail_state.0[r]);
        }
        self.prop_ctr = 0;
        self.tail_ctr = 0;
    }
}

impl GaussianSampler8x {
    fn init_stream(seed: &[u8; 32], tag: &[u8; 8]) -> qsag_asm::KeccakState8x {
        let mut st = qsag_asm::KeccakState8x::default();
        let magic = u64::from_le_bytes(*b"QSAG.RNG");
        let tag_w = u64::from_le_bytes(*tag);
        st.0[0] = [magic; 8];
        st.0[1] = [tag_w; 8];
        for w in 0..4 {
            let o = 8 * w;
            let word = u64::from_le_bytes([
                seed[o],
                seed[o + 1],
                seed[o + 2],
                seed[o + 3],
                seed[o + 4],
                seed[o + 5],
                seed[o + 6],
                seed[o + 7],
            ]);
            st.0[2 + w] = [word; 8];
        }
        st.0[6] = [0, 1, 2, 3, 4, 5, 6, 7];
        st.0[8] = [0x1f; 8];
        st.0[16] = [0x8000_0000_0000_0000; 8];
        st
    }

    fn new(rng: &mut PartyPrivateRng) -> Self {
        let mut prop_seed = rng.next_bytes32();
        let mut tail_seed = rng.next_bytes32();
        let prop_init = Self::init_stream(&prop_seed, b"GSPROP8X");
        let tail_init = Self::init_stream(&tail_seed, b"GSTAIL8X");
        wipe_bytes32(&mut prop_seed);
        wipe_bytes32(&mut tail_seed);
        Self {
            prop_init,
            prop_state: qsag_asm::KeccakState8x::default(),
            prop_ctr: 0,
            prop_slot: 13,
            tail_init,
            tail_state: qsag_asm::KeccakState8x::default(),
            tail_ctr: 0,
            tail_slot: 8,
        }
    }

    #[inline(always)]
    fn next_prop_batch(&mut self) -> ([u16; 8], [u64; 8]) {
        if self.prop_slot == 13 {
            self.prop_state = self.prop_init;
            let ctr = self.prop_ctr;
            self.prop_ctr = self.prop_ctr.wrapping_add(1);
            self.prop_state.0[7] = [ctr; 8];
            qsag_asm::keccak_f1600_x8(&mut self.prop_state);
            self.prop_slot = 0;
        }
        let s = self.prop_slot;
        self.prop_slot = s + 1;
        let group = s / 4;
        let sub = s % 4;
        let prop_words = &self.prop_state.0[5 * group];
        let high_words = &self.prop_state.0[5 * group + 1 + sub];
        let shift = 13 * sub;
        let props = core::array::from_fn(|lane| ((prop_words[lane] >> shift) & 0x1fff) as u16);
        (props, *high_words)
    }

    #[inline(always)]
    fn next_tail_batch(&mut self) -> ([u64; 8], [u64; 8]) {
        if self.tail_slot == 8 {
            self.tail_state = self.tail_init;
            let ctr = self.tail_ctr;
            self.tail_ctr = self.tail_ctr.wrapping_add(1);
            self.tail_state.0[7] = [ctr; 8];
            qsag_asm::keccak_f1600_x8(&mut self.tail_state);
            self.tail_slot = 0;
        }
        let s = self.tail_slot;
        self.tail_slot = s + 1;
        (self.tail_state.0[2 * s], self.tail_state.0[2 * s + 1])
    }

    #[inline(never)]
    fn sample_box(&mut self, response: bool) -> [i16; RLWE_N] {
        // The proposal mass is about 0.214 in either public box. Retry a whole
        // budget on shortage. Its count depends only on acceptance bits, which
        // are independent of the conditional distribution of the retained values.
        const TRIALS: usize = 8 * RLWE_N;
        let half = if response {
            RLWE_ZKPOK_Z_BOUND
        } else {
            RLWE_ZKPOK_Z_BOUND + 2
        };
        let mut slots = [0u32; TRIALS];
        loop {
            let mut skipped = 0u32;
            for batch in slots.as_chunks_mut::<8>().0 {
                let (props, high) = self.next_prop_batch();
                let tail = self.next_tail_batch();
                pack_gaussian_trials(batch, &mut skipped, half, &props, &high, &tail);
            }
            if TRIALS - skipped as usize >= RLWE_N {
                break;
            }
        }
        compact(&mut slots);
        let out = core::array::from_fn(|i| slots[i] as i16);
        qsag_asm::volatile_fill(&mut slots, 0);
        out
    }
}

/// The sampler's secret-dependent arithmetic has a flat pointer ABI for the
/// instruction audit. Only the public box and fixed array lengths control work.
#[inline(never)]
fn pack_gaussian_trials(
    batch: &mut [u32; 8],
    skipped: &mut u32,
    half: i16,
    props: &[u16; 8],
    high: &[u64; 8],
    tail: &([u64; 8], [u64; 8]),
) {
    let (low, mid) = tail;
    let xs = props.map(|p| p as i16 - half);
    // Even invalid proposals must stay within the 24-bit exponent domain.
    let exps = core::array::from_fn(|i| {
        let x = i64::from(xs[i]);
        (x * x) as u64 & 0xff_ffff
    });
    let upper = gaussian_exp_upper_bound_x8(&exps);
    let lower = gaussian_exp_lower_bound_x8(&exps);
    for i in 0..8 {
        let exact = gaussian_fraction_lt(
            [low[i], mid[i], high[i]],
            gaussian_exp_probability::<24>(exps[i]),
        );
        let accept = u32::from(props[i] < 2 * half as u16)
            & black_box(u32::from(u128::from(high[i]) < upper[i]))
            & (black_box(u32::from(high[i] < lower[i])) | black_box(u32::from(exact)));
        // High half: distance this value must travel left. Rejected
        // slots have zero distance and never move.
        batch[i] = ((*skipped << 16) | u32::from(xs[i] as u16)) & black_box(accept.wrapping_neg());
        *skipped += 1 - accept;
    }
}

/// Route each accepted entry left by the number of preceding rejections, one
/// distance bit per pass. After k passes its position equals its final rank
/// plus the preceding reject count rounded down to a multiple of 2^k. These
/// positions stay strictly ordered, so a left-to-right pass cannot overwrite
/// an entry that still needs to move. Both addresses are public in every pass.
#[inline(never)]
fn compact<const N: usize>(slots: &mut [u32; N]) {
    let mut step = 1;
    while step < N {
        for src in step..N {
            let entry = slots[src];
            let mask = black_box(u32::from(entry & ((step as u32) << 16) != 0).wrapping_neg());
            slots[src - step] ^= mask & (entry ^ slots[src - step]);
            slots[src] = entry & !mask;
        }
        step *= 2;
    }
}

#[inline(always)]
pub(super) fn gaussian_exp_probability<const BITS: usize>(exponent: u64) -> [u64; 3] {
    let mut probability = [u64::MAX; 3];
    for (bit, &factor) in RLWE_GAUSSIAN_EXP_POWERS[..BITS].iter().enumerate() {
        let multiplied = gaussian_fraction_mul(probability, factor);
        let mask = 0u64.wrapping_sub((exponent >> bit) & 1);
        for (p, m) in probability.iter_mut().zip(multiplied) {
            *p ^= mask & (*p ^ m);
        }
    }
    probability
}

// Ratio D(y+v)/(M D(y)). All arithmetic depending on the witness shift uses
// fixed loops and masked selection; only the final accept/reject bit is opened.
pub(super) fn gaussian_accept(log_ratio: i64, rng: &mut PartyPrivateRng) -> bool {
    let exponent = log_ratio + RLWE_GAUSSIAN_LOG_M;
    let negative = (exponent >> 63) as u64;
    let clipped = (exponent as u64) & !negative;
    let mut probability = gaussian_exp_probability::<30>(clipped);
    let in_range = 0u64.wrapping_sub(u64::from(clipped < (1 << 30)));
    for limb in &mut probability {
        *limb &= in_range;
    }
    let random = core::array::from_fn(|_| rng.next_u64());
    gaussian_fraction_lt(random, probability) | (negative != 0)
}

// Generated at 120 decimal digits of precision. These are public bit-position
// factors, scanned in fixed order; there are no mask-indexed table accesses.
// floor(2^192 * exp(-2^i/980000)), i=0..29.
const RLWE_GAUSSIAN_EXP_POWERS: [[u64; 3]; 30] = [
    [0x1e0ee5c166ce3f45, 0x4596fdd04820cdf5, 0xffffeee161ee8ccb],
    [0xc4bd6a5137eea0f8, 0x4a2b8823ca1b4080, 0xffffddc2c5022e3e],
    [0x44427bc76a53ff98, 0x2a9c7998b671a801, 0xffffbb858e98aecd],
    [0xa0c9a58e0e64155f, 0x8111b86300311166, 0xffff770b2f82a469],
    [0x35a41e9244e165f3, 0x4c35e0bc42b0f5a8, 0xfffeee16a84a5076],
    [0x1d0613f7ebafa37a, 0xdf95f9d82b467952, 0xfffddc2e75a822ae],
    [0x1cc31b117b42ceb3, 0x692edb6ffd64b91e, 0xfffbb8617f996614],
    [0x29767ac0a297cf82, 0x4a27dce9e6d35099, 0xfff770d550301cb9],
    [0xadb8566b5ff3f42d, 0x31988b3d23e474e3, 0xffeee1f3e31bedf9],
    [0x6750e998b9b340e1, 0xf4f6785cfd460252, 0xffddc50cc75a8994],
    [0xd196fffa1ed986fd, 0xeeabfe39f8fd5b4e, 0xffbb8ead44e33bdc],
    [0x06cff414fc79dc4f, 0xdc50d69edfd2a160, 0xff772fa6efe402ed],
    [0xd0d009324a025ffe, 0x4b9e8aa4ca5654b6, 0xfeeea86be7f9fcc2],
    [0xaaf2184fd58065f9, 0x60409dd8686a08e8, 0xfdde74b3b7c53457],
    [0x965a565c6d111b08, 0xb4ec92392fe9aad0, 0xfbc173f9d621e030],
    [0x60aeffc51a982010, 0x3ca73c0a1d21b6eb, 0xf794eb9bfd25b6e8],
    [0x00bc34df6dfa8348, 0x655e44e2d45921a0, 0xef70b54847b33c5f],
    [0x647298b2cc3a9ced, 0xcf047b168746a1be, 0xdff3a41c157eb15a],
    [0x1e445c07efd41bd3, 0xefcffdd9e95adf36, 0xc3ea5fc9e3f7861f],
    [0x64853bde5727d2ff, 0x54f67e49ba147824, 0x95eee480d2374d3f],
    [0xb99bb3368bc0d7af, 0xc02dbeaedb0d80fa, 0x57cff4eba030f604],
    [0x77d66aade9197cc5, 0xe967d9885d913509, 0x1e1f0166264058a1],
    [0xd17313b79cc3aba7, 0x6b99ed77f4585a5e, 0x038b481547b64d6a],
    [0x36d997f1617c1bac, 0xf3a1a5781f3b6abe, 0x000c8f77db161fe3],
    [0x8102ba277dc54cf0, 0x1f1003bc1c646702, 0x0000009dc3a3a8f3],
    [0x29065424ef536df9, 0x8c3ff63710108879, 0x0000000000006139],
    [0x39e763f90442732a, 0x0000000024eca938, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
];
/// `ceil(980_000 * ln(40)) = 3_615_102` (`M = 40` over 24-rep signed-monomial shifts `||v||_2^2 <= 33_024`, tail `< 2^-143`).
const RLWE_GAUSSIAN_LOG_M: i64 = 3_615_102;
pub(super) const RLWE_WITNESS_ENERGY_BOUND: usize = 1376;

pub(super) fn bounded_ternary_witness(s: &RlwePoly, e: &RlwePoly) -> bool {
    let (energy, ternary) =
        s.0.iter()
            .chain(&e.0)
            .fold((0usize, true), |(energy, valid), &c| {
                (
                    energy + usize::from(c != 0),
                    valid & ((c == 0) | (c == 1) | (c == RLWE_Q - 1)),
                )
            });
    ternary & (energy <= RLWE_WITNESS_ENERGY_BOUND)
}

#[inline]
fn ct_select_i16_array(
    choice: bool,
    if_true: &[i16; RLWE_N],
    if_false: &[i16; RLWE_N],
) -> [i16; RLWE_N] {
    let mask = 0u16.wrapping_sub(black_box(choice as u16));
    let mut out = [0i16; RLWE_N];
    for i in 0..RLWE_N {
        let a = if_true[i] as u16;
        let b = if_false[i] as u16;
        out[i] = (b ^ (mask & (a ^ b))) as i16;
    }
    out
}

#[inline]
pub(super) fn encode_rlwe_poly_le(p: &RlwePoly, out: &mut [u8; RLWE_N * 2]) {
    for (i, &c) in p.0.iter().enumerate() {
        let b = c.to_le_bytes();
        out[2 * i] = b[0];
        out[2 * i + 1] = b[1];
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve explicit statement, CRS, role, and polynomial bindings in the ZKPoK challenge XOF"
)]
#[inline]
fn init_rlwe_zkpok_challenge_xof(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_crs: &RlwePoly,
    pk0: &RlwePoly,
    t_crs: &RlwePoly,
) -> Cshake256Xof {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.RLWE.ZKPOK/v3");
    let mut hdr = [0u8; 92];
    hdr[0..32].copy_from_slice(crs_coin);
    hdr[32..64].copy_from_slice(session_id);
    hdr[64..72].copy_from_slice(&(sender_id as u64).to_be_bytes());
    hdr[72..80].copy_from_slice(&(receiver_id as u64).to_be_bytes());
    hdr[80..84].copy_from_slice(&ot_idx.to_be_bytes());
    hdr[84..88].copy_from_slice(&(RLWE_ZKPOK_REPS as u32).to_be_bytes());
    hdr[88..92].copy_from_slice(&RLWE_ZKPOK_CHAL_BITS.to_be_bytes());
    xof.absorb(&hdr);

    let mut poly_buf = [0u8; RLWE_N * 2];
    encode_rlwe_poly_le(a_crs, &mut poly_buf);
    xof.absorb(&poly_buf);
    encode_rlwe_poly_le(pk0, &mut poly_buf);
    xof.absorb(&poly_buf);
    encode_rlwe_poly_le(t_crs, &mut poly_buf);
    xof.absorb(&poly_buf);
    xof
}

#[inline]
fn squeeze_rlwe_zkpok_challenges(xof: &mut Cshake256Xof) -> [u32; RLWE_ZKPOK_REPS] {
    let mut raw = [0u8; RLWE_ZKPOK_REPS * 4];
    xof.squeeze(&mut raw);
    core::array::from_fn(|rep| {
        let o = 4 * rep;
        u32::from_le_bytes([raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]) & RLWE_ZKPOK_CHAL_MASK
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
pub(super) fn hash_rlwe_zkpok_joint_challenges(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_crs: &RlwePoly,
    pk0: &RlwePoly,
    t_crs: &RlwePoly,
    commitments: &[(RlwePoly, RlwePoly)],
) -> [u32; RLWE_ZKPOK_REPS] {
    let mut xof = init_rlwe_zkpok_challenge_xof(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        a_crs,
        pk0,
        t_crs,
    );
    let mut poly_buf = [0u8; RLWE_N * 2];
    for (a, b) in commitments {
        encode_rlwe_poly_le(a, &mut poly_buf);
        xof.absorb(&poly_buf);
        encode_rlwe_poly_le(b, &mut poly_buf);
        xof.absorb(&poly_buf);
    }
    squeeze_rlwe_zkpok_challenges(&mut xof)
}

impl RlweReceiverZkPok {
    #[expect(
        clippy::too_many_arguments,
        reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
    )]
    pub(super) fn prove_ct(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        a_ntt: &RlwePolyNtt,
        t_crs: &RlwePoly,
        pk0: &RlwePoly,
        s_r: &RlwePoly,
        e1: &RlwePoly,
        choice_bit: bool,
        rng: &mut PartyPrivateRng,
    ) -> Self {
        let pk1 = pk0.add(t_crs);
        // When `choice_bit == false`, fake branch is `1` (`pk1`); when `true`, fake branch is `0` (`pk0`).
        let mut y_fake = RlwePoly::ct_select(choice_bit, pk0, &pk1);
        let mut s_signed = rlwe_ternary_to_i16_ct(s_r);
        let mut e_signed = rlwe_ternary_to_i16_ct(e1);

        let mut chal0 = [0u32; RLWE_ZKPOK_REPS];
        let mut chal1 = [0u32; RLWE_ZKPOK_REPS];
        let mut z_s0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_s1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);

        let mut g_sampler = GaussianSampler8x::new(rng);

        // Simulated branch `(u_fake, zs_fake, ze_fake, w_fake)` is witness-independent;
        // single-attempt real-branch acceptance probability is uniform across `u_real` up to `< 2^-197`.
        let mut u_fakes = [0u32; RLWE_ZKPOK_REPS];
        let mut zs_fakes = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut ze_fakes = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut w_fakes = [RlwePoly::ZERO; RLWE_ZKPOK_REPS];
        for rep in 0..RLWE_ZKPOK_REPS {
            let u_fake = (rng.next_u64() as u32) & RLWE_ZKPOK_CHAL_MASK;
            let (zs_fake, ze_fake) = loop {
                let zs = g_sampler.sample_box(true);
                let ze = g_sampler.sample_box(true);
                if rlwe_pair_l2_sq(&zs, &ze) <= RLWE_ZKPOK_PAIR_L2_SQ_BOUND {
                    break (zs, ze);
                }
            };
            let w_fake = signed_box_to_rlwe_poly(&zs_fake)
                .mul_ntt(a_ntt)
                .add(&signed_box_to_rlwe_poly(&ze_fake))
                .sub(&mul_chal11_public(&y_fake, u_fake));
            u_fakes[rep] = u_fake;
            zs_fakes[rep] = zs_fake;
            ze_fakes[rep] = ze_fake;
            w_fakes[rep] = w_fake;
        }
        wipe_u16s(&mut y_fake.0);

        let a_crs = a_ntt.from_ntt();
        let base_xof = init_rlwe_zkpok_challenge_xof(
            crs_coin,
            session_id,
            sender_id,
            receiver_id,
            ot_idx,
            &a_crs,
            pk0,
            t_crs,
        );
        let mut poly_buf = [0u8; RLWE_N * 2];
        let mut ys_masks = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut ye_masks = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut u_reals = [0u32; RLWE_ZKPOK_REPS];
        let mut ds = [0i16; RLWE_N];
        let mut de = [0i16; RLWE_N];

        // Rejection restarts the entire joint real-branch transcript.
        loop {
            let mut xof = base_xof.clone();
            for rep in 0..RLWE_ZKPOK_REPS {
                let ys = g_sampler.sample_box(false);
                let ye = g_sampler.sample_box(false);
                let w_real = signed_box_to_rlwe_poly(&ys)
                    .mul_ntt(a_ntt)
                    .add(&signed_box_to_rlwe_poly(&ye));
                let c0 = RlwePoly::ct_select(choice_bit, &w_fakes[rep], &w_real);
                let c1 = RlwePoly::ct_select(choice_bit, &w_real, &w_fakes[rep]);
                encode_rlwe_poly_le(&c0, &mut poly_buf);
                xof.absorb(&poly_buf);
                encode_rlwe_poly_le(&c1, &mut poly_buf);
                xof.absorb(&poly_buf);
                ys_masks[rep] = ys;
                ye_masks[rep] = ye;
            }
            let challenges = squeeze_rlwe_zkpok_challenges(&mut xof);
            let mut in_bounds = 1u32;
            let mut log_ratio = 0i64;
            for rep in 0..RLWE_ZKPOK_REPS {
                let u_real = challenges[rep] ^ u_fakes[rep];
                u_reals[rep] = u_real;
                ds = mul_chal11_signed_ct(&s_signed, u_real);
                de = mul_chal11_signed_ct(&e_signed, u_real);
                let ys = &mut ys_masks[rep];
                let ye = &mut ye_masks[rep];
                let mut pair_l2_sq = 0u64;
                for i in 0..RLWE_N {
                    let dsi = i64::from(ds[i]);
                    let dei = i64::from(de[i]);
                    log_ratio += 2 * i64::from(ys[i]) * dsi + dsi * dsi;
                    log_ratio += 2 * i64::from(ye[i]) * dei + dei * dei;
                    ys[i] += ds[i];
                    ye[i] += de[i];
                    let zsi = i64::from(ys[i]);
                    let zei = i64::from(ye[i]);
                    pair_l2_sq += (zsi * zsi) as u64 + (zei * zei) as u64;
                    in_bounds &= (((i32::from(ys[i]) + 3070) as u32) < 6140) as u32;
                    in_bounds &= (((i32::from(ye[i]) + 3070) as u32) < 6140) as u32;
                }
                in_bounds &= (pair_l2_sq <= RLWE_ZKPOK_PAIR_L2_SQ_BOUND) as u32;
            }
            let accept = gaussian_accept(log_ratio, rng);
            if black_box(in_bounds) == 1 && black_box(accept) {
                break;
            }
        }
        wipe_bytes(&mut poly_buf);

        let c_mask = 0u32.wrapping_sub(black_box(choice_bit as u32));
        for rep in 0..RLWE_ZKPOK_REPS {
            let u_real = u_reals[rep];
            let u_fake = u_fakes[rep];
            chal0[rep] = u_real ^ (c_mask & (u_real ^ u_fake));
            chal1[rep] = u_fake ^ (c_mask & (u_fake ^ u_real));
            z_s0[rep] = ct_select_i16_array(choice_bit, &zs_fakes[rep], &ys_masks[rep]);
            z_e0[rep] = ct_select_i16_array(choice_bit, &ze_fakes[rep], &ye_masks[rep]);
            z_s1[rep] = ct_select_i16_array(choice_bit, &ys_masks[rep], &zs_fakes[rep]);
            z_e1[rep] = ct_select_i16_array(choice_bit, &ye_masks[rep], &ze_fakes[rep]);
        }

        qsag_asm::volatile_fill(&mut s_signed, 0);
        qsag_asm::volatile_fill(&mut e_signed, 0);
        qsag_asm::volatile_fill(&mut ds, 0);
        qsag_asm::volatile_fill(&mut de, 0);
        qsag_asm::volatile_fill(&mut u_fakes, 0);
        qsag_asm::volatile_fill(&mut u_reals, 0);
        for rep in 0..RLWE_ZKPOK_REPS {
            qsag_asm::volatile_fill(&mut zs_fakes[rep], 0);
            qsag_asm::volatile_fill(&mut ze_fakes[rep], 0);
            qsag_asm::volatile_fill(&mut ys_masks[rep], 0);
            qsag_asm::volatile_fill(&mut ye_masks[rep], 0);
            wipe_u16s(&mut w_fakes[rep].0);
        }
        Self {
            chal0,
            chal1,
            z_s0,
            z_e0,
            z_s1,
            z_e1,
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
    )]
    pub fn verify(
        &self,
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        a_ntt: &RlwePolyNtt,
        t_crs: &RlwePoly,
        pk0: &RlwePoly,
    ) -> bool {
        let a_crs = a_ntt.from_ntt();
        if !a_crs.is_canonical() || !t_crs.is_canonical() || !pk0.is_canonical() {
            return false;
        }
        let y0 = *pk0;
        let y1 = pk0.add(t_crs);
        let mut commitments = Vec::with_capacity(RLWE_ZKPOK_REPS);
        for rep in 0..RLWE_ZKPOK_REPS {
            if (self.chal0[rep] >> RLWE_ZKPOK_CHAL_BITS) != 0
                || (self.chal1[rep] >> RLWE_ZKPOK_CHAL_BITS) != 0
            {
                return false;
            }
            for arr in [
                &self.z_s0[rep],
                &self.z_e0[rep],
                &self.z_s1[rep],
                &self.z_e1[rep],
            ] {
                for &v in arr {
                    if !(-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(&v) {
                        return false;
                    }
                }
            }
            if rlwe_pair_l2_sq(&self.z_s0[rep], &self.z_e0[rep]) > RLWE_ZKPOK_PAIR_L2_SQ_BOUND
                || rlwe_pair_l2_sq(&self.z_s1[rep], &self.z_e1[rep]) > RLWE_ZKPOK_PAIR_L2_SQ_BOUND
            {
                return false;
            }
            let zs0_p = signed_box_to_rlwe_poly(&self.z_s0[rep]);
            let ze0_p = signed_box_to_rlwe_poly(&self.z_e0[rep]);
            let zs1_p = signed_box_to_rlwe_poly(&self.z_s1[rep]);
            let ze1_p = signed_box_to_rlwe_poly(&self.z_e1[rep]);

            let w0 = zs0_p
                .mul_ntt(a_ntt)
                .add(&ze0_p)
                .sub(&mul_chal11_public(&y0, self.chal0[rep]));
            let w1 = zs1_p
                .mul_ntt(a_ntt)
                .add(&ze1_p)
                .sub(&mul_chal11_public(&y1, self.chal1[rep]));
            commitments.push((w0, w1));
        }
        let challenges = hash_rlwe_zkpok_joint_challenges(
            crs_coin,
            session_id,
            sender_id,
            receiver_id,
            ot_idx,
            &a_crs,
            pk0,
            t_crs,
            &commitments,
        );
        for (rep, expected) in challenges.iter().enumerate() {
            if self.chal0[rep] ^ self.chal1[rep] != *expected {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gaussian_compaction_matches_filter_for_every_eight_lane_mask() {
        for bits in 0u32..256 {
            let mut want = alloc::vec::Vec::new();
            let mut slots = core::array::from_fn::<_, 8, _>(|i| {
                if bits & (1 << i) == 0 {
                    return 0;
                }
                let skipped = i - want.len();
                want.push(i as u16 + 1);
                ((skipped as u32) << 16) | (i as u32 + 1)
            });
            compact(&mut slots);
            assert_eq!(&slots.map(|v| v as u16)[..want.len()], want);
        }
    }

    #[test]
    fn gaussian_trials_resolve_equal_high_limbs_and_invalid_proposals() {
        let half = RLWE_ZKPOK_Z_BOUND;
        let center = half as u16;
        let props = [
            center,
            center,
            center,
            center,
            center,
            center,
            2 * center,
            8191,
        ];
        // At x=0 the exact Q192 threshold is [MAX; 3]. Exercise equality,
        // both lower comparison limbs, high-limb acceptance, and the box mask.
        let max = u64::MAX;
        let high = [max, max, max, max - 1, max, 0, 0, 0];
        let mid = [max, max, max - 1, max, max, 0, 0, 0];
        let low = [max, max - 1, max, max, max, 0, 0, 0];
        let mut skipped = 1;
        let mut slots = [0; 8];
        pack_gaussian_trials(&mut slots, &mut skipped, half, &props, &high, &(low, mid));
        assert_eq!(slots, [0, 2 << 16, 2 << 16, 2 << 16, 0, 3 << 16, 0, 0]);
        assert_eq!(skipped, 5);
    }

    #[test]
    fn gaussian_sampler_matches_exact_rejection_and_box_moments() {
        let init =
            || GaussianSampler8x::new(&mut PartyPrivateRng::from_seed([0x39; 32], b"gaussian-8x"));
        let mut sampler = init();
        let mut reference = init();
        for response in [true, false] {
            let half = if response {
                RLWE_ZKPOK_Z_BOUND
            } else {
                RLWE_ZKPOK_Z_BOUND + 2
            };
            let got = sampler.sample_box(response);
            let mut expected = alloc::vec::Vec::new();
            for _ in 0..RLWE_N {
                let (props, high) = reference.next_prop_batch();
                let (lo, mid) = reference.next_tail_batch();
                for i in 0..8 {
                    let x = props[i] as i16 - half;
                    if (-half..half).contains(&x)
                        && gaussian_fraction_lt(
                            [lo[i], mid[i], high[i]],
                            gaussian_exp_probability::<24>(i64::from(x).pow(2) as u64),
                        )
                    {
                        expected.push(x);
                    }
                }
            }
            assert_eq!(got, expected[..RLWE_N]);
            let mean = got.iter().map(|&x| i64::from(x)).sum::<i64>() / RLWE_N as i64;
            let energy = got.iter().map(|&x| i64::from(x).pow(2)).sum::<i64>() / RLWE_N as i64;
            assert!(mean.abs() < 100 && (400_000..580_000).contains(&energy));
        }
    }
}
