#![no_std]
#![forbid(unsafe_code)]

//! Dependency-free `#![no_std]` Quintic Goldilocks (`Fp5 = F_p[X]/(X^5 - 3)`) WHIR & Canopy
//! verification kernels extracted via Charon + Aeneas to Lean 4 (`aeneas/lean-whir`).
//!
//! Every live verifier acceptance gate in `qsag-agg` (`hem_quintic`, `zk_hem::v2`, and
//! `recursive`) routes directly through these functions. Structs intentionally omit `#[derive]`
//! so Charon/Aeneas emits pure Lean structures and functions with zero external trait models.

/// Canonical Goldilocks prime `p = 2^64 - 2^32 + 1`.
pub const GOLDILOCKS_P: u64 = 0xffff_ffff_0000_0001;

/// Maximum 64-bit unsigned word (`u64::MAX`), used for explicit overflow-free guards.
pub const MAX_U64_WORD: u64 = 0xffff_ffff_ffff_ffff;

/// Defining binomial non-residue `w = 3` in `F_p[X]/(X^5 - 3)`.
pub const FP5_NONRESIDUE_W: u64 = 3;

/// Primitive fifth root of unity `zeta_5 = 3^((p - 1) / 5) mod p` (`X^p = zeta_5 * X`).
pub const FROBENIUS_ZETA5_1: u64 = 1_041_288_259_238_279_555;
/// `zeta_5^2 mod p`.
pub const FROBENIUS_ZETA5_2: u64 = 15_820_824_984_080_659_046;
/// `zeta_5^3 mod p`.
pub const FROBENIUS_ZETA5_3: u64 = 211_587_555_138_949_697;
/// `zeta_5^4 mod p`.
pub const FROBENIUS_ZETA5_4: u64 = 1_373_043_270_956_696_022;

/// Canonical `QSAGHQM2` wire profile tag for 400-bit `TurboSHAKE256` Canopy commitments.
pub const QSAGHQM2_PROFILE_TURBO400: u8 = 1;
/// Canonical `QSAGHQM2` wire profile tag for 448-bit (`7` Goldilocks limbs) `Poseidon2-GL-w24` Canopy commitments.
pub const QSAGHQM2_PROFILE_GL24: u8 = 2;

/// Smallest certified `[DKT26]` `< 2^{-128}` QROM Quintic WHIR table log2 size (`2^16`).
pub const MIN_QUINTIC_LOG_CELLS: u32 = 16;
/// Largest certified `[DKT26]` `< 2^{-128}` QROM Quintic WHIR table log2 size (`2^28`).
pub const MAX_QUINTIC_LOG_CELLS: u32 = 28;
/// Largest Canopy Merkle tree depth (`<= 28`).
pub const MAX_CANOPY_LOG_LEAVES: u32 = 28;

/// Quintic Goldilocks extension element `c0 + c1 X + c2 X^2 + c3 X^3 + c4 X^4`
/// in polynomial power basis `[1, X, X^2, X^3, X^4]` modulo `X^5 - 3`.
pub struct Fp5 {
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
    pub c3: u64,
    pub c4: u64,
}

/// Ordered 400-bit (`[u8; 50]`) Canopy Merkle child pair (`TurboSHAKE256` / `cSHAKE256`).
pub struct MerklePair400 {
    pub left: [u8; 50],
    pub right: [u8; 50],
}

/// Canonical 448-bit (`7` Goldilocks limbs `< GOLDILOCKS_P`) `Poseidon2-GL-w24` Canopy digest.
pub struct Gl24Digest {
    pub l0: u64,
    pub l1: u64,
    pub l2: u64,
    pub l3: u64,
    pub l4: u64,
    pub l5: u64,
    pub l6: u64,
}

/// Ordered 448-bit (`Gl24Digest`) canonical Goldilocks Canopy Merkle child pair (`Poseidon2-GL-w24`).
pub struct MerklePairGl24 {
    pub left: Gl24Digest,
    pub right: Gl24Digest,
}

/// Validated `QSAGHQM2` wire header fields.
pub struct Qsaghqm2Header {
    pub profile_tag: u8,
    pub active_signers: u64,
    pub payload_len: u64,
}

#[inline]
const fn copy_fp5(x: &Fp5) -> Fp5 {
    Fp5 {
        c0: x.c0,
        c1: x.c1,
        c2: x.c2,
        c3: x.c3,
        c4: x.c4,
    }
}

#[inline]
const fn load_le_u64_40(bytes: &[u8; 40], off: usize) -> u64 {
    if off > 32 {
        return 0;
    }
    (bytes[off] as u64)
        | ((bytes[off + 1] as u64) << 8)
        | ((bytes[off + 2] as u64) << 16)
        | ((bytes[off + 3] as u64) << 24)
        | ((bytes[off + 4] as u64) << 32)
        | ((bytes[off + 5] as u64) << 40)
        | ((bytes[off + 6] as u64) << 48)
        | ((bytes[off + 7] as u64) << 56)
}

#[inline]
const fn load_le_u64_56(bytes: &[u8; 56], off: usize) -> u64 {
    if off > 48 {
        return 0;
    }
    (bytes[off] as u64)
        | ((bytes[off + 1] as u64) << 8)
        | ((bytes[off + 2] as u64) << 16)
        | ((bytes[off + 3] as u64) << 24)
        | ((bytes[off + 4] as u64) << 32)
        | ((bytes[off + 5] as u64) << 40)
        | ((bytes[off + 6] as u64) << 48)
        | ((bytes[off + 7] as u64) << 56)
}

/// Strict canonical limb decoder: accepts `x` iff `x < GOLDILOCKS_P`.
pub const fn decode_canonical_u64(x: u64) -> Option<u64> {
    if x < GOLDILOCKS_P { Some(x) } else { None }
}

/// Strict canonical 5-limb `Fp5` constructor: accepts iff all five limbs are `< GOLDILOCKS_P`.
pub const fn decode_canonical_fp5_limbs(
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
) -> Option<Fp5> {
    if c0 < GOLDILOCKS_P
        && c1 < GOLDILOCKS_P
        && c2 < GOLDILOCKS_P
        && c3 < GOLDILOCKS_P
        && c4 < GOLDILOCKS_P
    {
        Some(Fp5 { c0, c1, c2, c3, c4 })
    } else {
        None
    }
}

/// Strict canonical 320-bit (`40`-byte little-endian) `Fp5` wire decoder.
pub const fn decode_canonical_fp5(bytes: &[u8; 40]) -> Option<Fp5> {
    decode_canonical_fp5_limbs(
        load_le_u64_40(bytes, 0),
        load_le_u64_40(bytes, 8),
        load_le_u64_40(bytes, 16),
        load_le_u64_40(bytes, 24),
        load_le_u64_40(bytes, 32),
    )
}

/// Strict canonical check for 7 Goldilocks limbs (`Poseidon2-GL-w24` 448-bit Canopy digest).
pub const fn decode_canonical_gl24_limbs(
    l0: u64,
    l1: u64,
    l2: u64,
    l3: u64,
    l4: u64,
    l5: u64,
    l6: u64,
) -> Option<Gl24Digest> {
    if l0 < GOLDILOCKS_P
        && l1 < GOLDILOCKS_P
        && l2 < GOLDILOCKS_P
        && l3 < GOLDILOCKS_P
        && l4 < GOLDILOCKS_P
        && l5 < GOLDILOCKS_P
        && l6 < GOLDILOCKS_P
    {
        Some(Gl24Digest {
            l0,
            l1,
            l2,
            l3,
            l4,
            l5,
            l6,
        })
    } else {
        None
    }
}

/// Strict canonical 448-bit (`56`-byte little-endian) `Poseidon2-GL-w24` Canopy digest decoder.
pub const fn decode_canonical_gl24_digest(bytes: &[u8; 56]) -> Option<Gl24Digest> {
    decode_canonical_gl24_limbs(
        load_le_u64_56(bytes, 0),
        load_le_u64_56(bytes, 8),
        load_le_u64_56(bytes, 16),
        load_le_u64_56(bytes, 24),
        load_le_u64_56(bytes, 32),
        load_le_u64_56(bytes, 40),
        load_le_u64_56(bytes, 48),
    )
}

/// Goldilocks modular addition `(a + b) mod p`.
pub fn add(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % GOLDILOCKS_P as u128) as u64
}

/// Goldilocks modular subtraction `(a - b) mod p`.
pub fn sub(a: u64, b: u64) -> u64 {
    let reduced_b = b % GOLDILOCKS_P;
    add(a, GOLDILOCKS_P - reduced_b)
}

/// Goldilocks modular multiplication `(a * b) mod p`.
pub fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % GOLDILOCKS_P as u128) as u64
}

/// Additive identity `0` in `Fp5`.
pub const fn fp5_zero() -> Fp5 {
    Fp5 {
        c0: 0,
        c1: 0,
        c2: 0,
        c3: 0,
        c4: 0,
    }
}

/// Multiplicative identity `1` in `Fp5`.
pub const fn fp5_one() -> Fp5 {
    Fp5 {
        c0: 1,
        c1: 0,
        c2: 0,
        c3: 0,
        c4: 0,
    }
}

/// Canonical base-field embedding `x mod p -> c0 + 0 X + ... + 0 X^4`.
pub fn fp5_from_base(x: u64) -> Fp5 {
    Fp5 {
        c0: x % GOLDILOCKS_P,
        c1: 0,
        c2: 0,
        c3: 0,
        c4: 0,
    }
}

/// Coordinate-wise equality on `Fp5`.
pub const fn fp5_eq(x: Fp5, y: Fp5) -> bool {
    x.c0 == y.c0 && x.c1 == y.c1 && x.c2 == y.c2 && x.c3 == y.c3 && x.c4 == y.c4
}

/// Addition in `Fp5 = F_p[X]/(X^5 - 3)`.
pub fn fp5_add(x: Fp5, y: Fp5) -> Fp5 {
    Fp5 {
        c0: add(x.c0, y.c0),
        c1: add(x.c1, y.c1),
        c2: add(x.c2, y.c2),
        c3: add(x.c3, y.c3),
        c4: add(x.c4, y.c4),
    }
}

/// Subtraction in `Fp5 = F_p[X]/(X^5 - 3)`.
pub fn fp5_sub(x: Fp5, y: Fp5) -> Fp5 {
    Fp5 {
        c0: sub(x.c0, y.c0),
        c1: sub(x.c1, y.c1),
        c2: sub(x.c2, y.c2),
        c3: sub(x.c3, y.c3),
        c4: sub(x.c4, y.c4),
    }
}

/// Negation `-x` in `Fp5 = F_p[X]/(X^5 - 3)`.
pub fn fp5_neg(x: Fp5) -> Fp5 {
    fp5_sub(fp5_zero(), x)
}

/// Base-field scalar multiplication `s * x` in `Fp5`.
pub fn fp5_scale(x: Fp5, s: u64) -> Fp5 {
    Fp5 {
        c0: mul(x.c0, s),
        c1: mul(x.c1, s),
        c2: mul(x.c2, s),
        c3: mul(x.c3, s),
        c4: mul(x.c4, s),
    }
}

/// Multiplication in `Fp5 = F_p[X]/(X^5 - 3)` (`X^5 = 3`).
pub fn fp5_mul(x: Fp5, y: Fp5) -> Fp5 {
    let w = FP5_NONRESIDUE_W;
    Fp5 {
        c0: add(
            mul(x.c0, y.c0),
            mul(
                w,
                add(
                    add(mul(x.c1, y.c4), mul(x.c2, y.c3)),
                    add(mul(x.c3, y.c2), mul(x.c4, y.c1)),
                ),
            ),
        ),
        c1: add(
            add(mul(x.c0, y.c1), mul(x.c1, y.c0)),
            mul(
                w,
                add(add(mul(x.c2, y.c4), mul(x.c3, y.c3)), mul(x.c4, y.c2)),
            ),
        ),
        c2: add(
            add(add(mul(x.c0, y.c2), mul(x.c1, y.c1)), mul(x.c2, y.c0)),
            mul(w, add(mul(x.c3, y.c4), mul(x.c4, y.c3))),
        ),
        c3: add(
            add(
                add(mul(x.c0, y.c3), mul(x.c1, y.c2)),
                add(mul(x.c2, y.c1), mul(x.c3, y.c0)),
            ),
            mul(w, mul(x.c4, y.c4)),
        ),
        c4: add(
            add(
                add(mul(x.c0, y.c4), mul(x.c1, y.c3)),
                add(mul(x.c2, y.c2), mul(x.c3, y.c1)),
            ),
            mul(x.c4, y.c0),
        ),
    }
}

/// Frobenius endomorphism `x -> x^p` in `Fp5 = F_p[X]/(X^5 - 3)` (`X^p = zeta_5 * X`).
pub fn fp5_frobenius(x: Fp5) -> Fp5 {
    Fp5 {
        c0: x.c0 % GOLDILOCKS_P,
        c1: mul(x.c1, FROBENIUS_ZETA5_1),
        c2: mul(x.c2, FROBENIUS_ZETA5_2),
        c3: mul(x.c3, FROBENIUS_ZETA5_3),
        c4: mul(x.c4, FROBENIUS_ZETA5_4),
    }
}

/// Affine combination `odd + alpha * even` in `Fp5`.
pub fn affine_combine_fp5(even: Fp5, odd: Fp5, alpha: Fp5) -> Fp5 {
    fp5_add(odd, fp5_mul(alpha, even))
}

/// Antipodal coset duet fold `odd + alpha * even` in `Fp5`, where
/// `even = (v0 + v1) * inv_two` and `odd = (v0 - v1) * inv_two_y0`.
pub fn duet_fold_fp5(v0: Fp5, v1: Fp5, inv_two_y0: u64, inv_two: u64, alpha: Fp5) -> Fp5 {
    let even = fp5_scale(fp5_add(copy_fp5(&v0), copy_fp5(&v1)), inv_two);
    let odd = fp5_scale(fp5_sub(v0, v1), inv_two_y0);
    affine_combine_fp5(even, odd, alpha)
}

/// Exact acceptance gate for one symmetric antipodal coset duet fold step in `Fp5`.
pub fn verify_affine_duet_fold_step_fp5(
    v0: Fp5,
    v1: Fp5,
    inv_two_y0: u64,
    inv_two: u64,
    alpha: Fp5,
    claimed_folded: Fp5,
) -> bool {
    fp5_eq(
        duet_fold_fp5(v0, v1, inv_two_y0, inv_two, alpha),
        claimed_folded,
    )
}

/// Asymmetric `[CWYZ26]` / `[DKT26]` monomial coset duet fold in `Fp5`:
/// `odd + (alpha + beta * y0_sq) * (even + theta * odd)`.
#[allow(clippy::too_many_arguments)]
pub fn cwyz_duet_fold_fp5(
    v0: Fp5,
    v1: Fp5,
    inv_two_y0: u64,
    inv_two: u64,
    y0_sq: u64,
    theta: Fp5,
    alpha: Fp5,
    beta: Fp5,
) -> Fp5 {
    let even = fp5_scale(fp5_add(copy_fp5(&v0), copy_fp5(&v1)), inv_two);
    let odd = fp5_scale(fp5_sub(v0, v1), inv_two_y0);
    let mixed = fp5_add(even, fp5_mul(theta, copy_fp5(&odd)));
    affine_combine_fp5(mixed, odd, fp5_add(alpha, fp5_scale(beta, y0_sq)))
}

/// Exact acceptance gate for one `[CWYZ26]` / `[DKT26]` asymmetric coset duet fold step in `Fp5`.
#[allow(clippy::too_many_arguments)]
pub fn verify_cwyz_duet_fold_step_fp5(
    v0: Fp5,
    v1: Fp5,
    inv_two_y0: u64,
    inv_two: u64,
    y0_sq: u64,
    theta: Fp5,
    alpha: Fp5,
    beta: Fp5,
    claimed_folded: Fp5,
) -> bool {
    fp5_eq(
        cwyz_duet_fold_fp5(v0, v1, inv_two_y0, inv_two, y0_sq, theta, alpha, beta),
        claimed_folded,
    )
}

/// Dual linear-functional `[CWYZ26]` sumcheck bridge step in `Fp5`:
/// `f = w0 + phi * w1`, `g = w2 + phi * (claim - w0)`,
/// `next = (g + alpha * (f + theta * g)) + beta * (w3 + theta * w4)`.
#[allow(clippy::too_many_arguments)]
pub fn cwyz_bridge_claim_step_fp5(
    w0: Fp5,
    w1: Fp5,
    w2: Fp5,
    w3: Fp5,
    w4: Fp5,
    claim: Fp5,
    phi: Fp5,
    theta: Fp5,
    alpha: Fp5,
    beta: Fp5,
) -> Fp5 {
    let w0_copy = copy_fp5(&w0);
    let phi_copy = copy_fp5(&phi);
    let f = fp5_add(w0, fp5_mul(phi, w1));
    let g = fp5_add(w2, fp5_mul(phi_copy, fp5_sub(claim, w0_copy)));
    let g_copy = copy_fp5(&g);
    let theta_copy = copy_fp5(&theta);
    let core_term = fp5_add(g, fp5_mul(alpha, fp5_add(f, fp5_mul(theta, g_copy))));
    let shift_term = fp5_mul(beta, fp5_add(w3, fp5_mul(theta_copy, w4)));
    fp5_add(core_term, shift_term)
}

/// Exact acceptance gate for one dual linear-functional `[CWYZ26]` sumcheck bridge round in `Fp5`.
#[allow(clippy::too_many_arguments)]
pub fn verify_cwyz_bridge_claim_step_fp5(
    w0: Fp5,
    w1: Fp5,
    w2: Fp5,
    w3: Fp5,
    w4: Fp5,
    claim: Fp5,
    phi: Fp5,
    theta: Fp5,
    alpha: Fp5,
    beta: Fp5,
    claimed_next: Fp5,
) -> bool {
    fp5_eq(
        cwyz_bridge_claim_step_fp5(w0, w1, w2, w3, w4, claim, phi, theta, alpha, beta),
        claimed_next,
    )
}

/// Evaluate quadratic sumcheck wire `(c0, c2)` at challenge `r` in `Fp5`, reconstructing
/// `c1 = sum_claim - 2 * c0 - c2` so `g(0) + g(1) == sum_claim` holds identically.
pub fn eval_quadratic_sumcheck_wire_fp5(c0: Fp5, c2: Fp5, sum_claim: Fp5, r: Fp5) -> Fp5 {
    let c0_a = copy_fp5(&c0);
    let c0_b = copy_fp5(&c0);
    let c2_a = copy_fp5(&c2);
    let r_a = copy_fp5(&r);
    let two_c0 = fp5_add(c0, c0_a);
    let c1 = fp5_sub(fp5_sub(sum_claim, two_c0), c2);
    fp5_add(fp5_mul(fp5_add(fp5_mul(c2_a, r), c1), r_a), c0_b)
}

/// Evaluate ascending-degree univariate `Fp5` polynomial `coeffs` at base-field point `z` via Horner's rule.
pub fn eval_fp5_univariate_at_base(coeffs: &[Fp5], z: u64) -> Fp5 {
    let mut acc = fp5_zero();
    let mut rem = coeffs.len();
    while rem > 0 {
        rem -= 1;
        let c = &coeffs[rem];
        acc = fp5_add(fp5_scale(acc, z), copy_fp5(c));
    }
    acc
}

/// Exact acceptance gate pinning a terminal univariate `Fp5` polynomial at base-field query `z`.
pub fn verify_fp5_univariate_at_base_pin(coeffs: &[Fp5], z: u64, expected: Fp5) -> bool {
    fp5_eq(eval_fp5_univariate_at_base(coeffs, z), expected)
}

/// Exact `Fp5` claim/OOD equality gate (`expected == supplied` across all 5 limbs).
pub const fn verify_ood_pin_eq_fp5(expected: Fp5, supplied: Fp5) -> bool {
    fp5_eq(expected, supplied)
}

/// Canonical query-fiber index reduction (`None` iff `groups == 0`).
pub const fn canonical_query_group_idx(raw_idx: u64, groups: u64) -> Option<u64> {
    if groups == 0 {
        None
    } else {
        Some(raw_idx % groups)
    }
}

/// Bounded 400-bit (`[u8; 50]`) Canopy Merkle child-pair ordering at `level < 64`.
pub const fn step_merkle_pair_order_400(
    idx: u64,
    level: u32,
    node: [u8; 50],
    sibling: [u8; 50],
) -> Option<MerklePair400> {
    if level >= 64 {
        return None;
    }
    if ((idx >> level) & 1) == 0 {
        Some(MerklePair400 {
            left: node,
            right: sibling,
        })
    } else {
        Some(MerklePair400 {
            left: sibling,
            right: node,
        })
    }
}

/// Bounded 448-bit (`Gl24Digest` `< GOLDILOCKS_P`) `Poseidon2-GL-w24` Canopy Merkle child-pair ordering.
pub const fn step_merkle_pair_order_gl24(
    idx: u64,
    level: u32,
    node: Gl24Digest,
    sibling: Gl24Digest,
) -> Option<MerklePairGl24> {
    if level >= 64 {
        return None;
    }
    let Some(canon_node) = decode_canonical_gl24_limbs(
        node.l0, node.l1, node.l2, node.l3, node.l4, node.l5, node.l6,
    ) else {
        return None;
    };
    let Some(canon_sibling) = decode_canonical_gl24_limbs(
        sibling.l0, sibling.l1, sibling.l2, sibling.l3, sibling.l4, sibling.l5, sibling.l6,
    ) else {
        return None;
    };
    if ((idx >> level) & 1) == 0 {
        Some(MerklePairGl24 {
            left: canon_node,
            right: canon_sibling,
        })
    } else {
        Some(MerklePairGl24 {
            left: canon_sibling,
            right: canon_node,
        })
    }
}

/// Overflow-free per-shard and global quorum weight check:
/// verifies `counts.len() == minimums.len() > 0`, `minimum_global > 0`,
/// `0 < minimums[i] <= counts[i]` for every shard, neither `sum(counts)` nor `sum(minimums)`
/// overflows `u64`, and `sum(counts) >= minimum_global`.
pub fn checked_quorum_sum(counts: &[u64], minimums: &[u64], minimum_global: u64) -> Option<u64> {
    if counts.is_empty() || counts.len() != minimums.len() || minimum_global == 0 {
        return None;
    }
    let mut total: u64 = 0;
    let mut min_total: u64 = 0;
    let mut i = 0;
    while i < counts.len() {
        let c = counts[i];
        let m = minimums[i];
        if m == 0 || c < m {
            return None;
        }
        if total > MAX_U64_WORD - c {
            return None;
        }
        total += c;
        if min_total > MAX_U64_WORD - m {
            return None;
        }
        min_total += m;
        i += 1;
    }
    if total < minimum_global {
        None
    } else {
        Some(total)
    }
}

/// Validate the `QSAGHQM2` wire header envelope:
/// - 8-byte magic equals ASCII `QSAGHQM2` (`[0x51, 0x53, 0x41, 0x47, 0x48, 0x51, 0x4d, 0x32]`),
/// - `profile_tag` is `1` (`TurboShake400`) or `2` (`Poseidon2Gl24`),
/// - `1 <= active_signers <= num_validators`,
/// - `declared_payload_len > 0` and `declared_payload_len == actual_payload_len`.
pub const fn verify_qsaghqm2_header(
    magic: [u8; 8],
    profile_tag: u8,
    active_signers: u64,
    num_validators: u64,
    declared_payload_len: u64,
    actual_payload_len: u64,
) -> Option<Qsaghqm2Header> {
    if magic[0] != 0x51
        || magic[1] != 0x53
        || magic[2] != 0x41
        || magic[3] != 0x47
        || magic[4] != 0x48
        || magic[5] != 0x51
        || magic[6] != 0x4d
        || magic[7] != 0x32
    {
        return None;
    }
    if profile_tag != QSAGHQM2_PROFILE_TURBO400 && profile_tag != QSAGHQM2_PROFILE_GL24 {
        return None;
    }
    if active_signers == 0
        || active_signers > num_validators
        || declared_payload_len == 0
        || declared_payload_len != actual_payload_len
    {
        return None;
    }
    Some(Qsaghqm2Header {
        profile_tag,
        active_signers,
        payload_len: declared_payload_len,
    })
}

/// Validate that a Quintic WHIR folding schedule lies in the `[DKT26]` `< 2^{-128}` QROM
/// certified table range (`16 <= log_cells <= 28`), has the canonical stage count (`3` for
/// `16..=22`, `4` for `23..=28`), `1 <= early_stop_vars <= 8`, and partitions `log_cells`
/// variables (`early_stop_vars + folded_vars_sum == log_cells`).
pub const fn verify_quintic_schedule_envelope(
    log_cells: u32,
    early_stop_vars: u32,
    folded_vars_sum: u32,
    num_stages: u32,
) -> bool {
    if log_cells < MIN_QUINTIC_LOG_CELLS || log_cells > MAX_QUINTIC_LOG_CELLS {
        return false;
    }
    let expected_stages = if log_cells <= 22 { 3 } else { 4 };
    if num_stages != expected_stages || early_stop_vars == 0 || early_stop_vars > 8 {
        return false;
    }
    if folded_vars_sum > log_cells {
        return false;
    }
    early_stop_vars + folded_vars_sum == log_cells
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(c0: u64, c1: u64, c2: u64, c3: u64, c4: u64) -> Fp5 {
        Fp5 { c0, c1, c2, c3, c4 }
    }

    fn limbs(x: Fp5) -> [u64; 5] {
        [x.c0, x.c1, x.c2, x.c3, x.c4]
    }

    #[test]
    fn canonical_decoders_and_fp5_ring_identities() {
        assert_eq!(decode_canonical_u64(0), Some(0));
        assert_eq!(
            decode_canonical_u64(GOLDILOCKS_P - 1),
            Some(GOLDILOCKS_P - 1)
        );
        assert_eq!(decode_canonical_u64(GOLDILOCKS_P), None);
        assert_eq!(decode_canonical_u64(u64::MAX), None);

        let mut raw40 = [0u8; 40];
        for i in 0..5 {
            raw40[8 * i..8 * (i + 1)].copy_from_slice(&(i as u64 + 1).to_le_bytes());
        }
        let decoded = decode_canonical_fp5(&raw40).expect("canonical fp5");
        assert_eq!(limbs(decoded), [1, 2, 3, 4, 5]);

        for limb in 0..5 {
            let mut bad = raw40;
            bad[8 * limb..8 * (limb + 1)].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
            assert!(decode_canonical_fp5(&bad).is_none());
        }

        // X^5 == 3 in F_p[X]/(X^5 - 3).
        let x_basis = e(0, 1, 0, 0, 0);
        let x2 = fp5_mul(e(0, 1, 0, 0, 0), e(0, 1, 0, 0, 0));
        let x4 = fp5_mul(copy_fp5(&x2), x2);
        let x5 = fp5_mul(x4, x_basis);
        assert!(fp5_eq(x5, e(3, 0, 0, 0, 0)));

        // Frobenius matches Lean kernel-evaluated `frob_kat12345` in `QuinticExt5.lean`.
        let frob1 = fp5_frobenius(e(1, 2, 3, 4, 5));
        assert_eq!(
            limbs(frob1),
            [
                1,
                2_082_576_518_476_559_110,
                10_568_986_813_412_808_496,
                846_350_220_555_798_788,
                6_865_216_354_783_480_110,
            ]
        );
        // Order 5 on non-base elements: phi^5(x) == x.
        let mut iter = e(1, 2, 3, 4, 5);
        for _ in 0..5 {
            iter = fp5_frobenius(iter);
        }
        assert_eq!(limbs(iter), [1, 2, 3, 4, 5]);
    }

    #[test]
    fn canopy_merkle_quorum_and_header_gates() {
        let p0 = step_merkle_pair_order_400(2, 0, [1u8; 50], [2u8; 50]).unwrap();
        assert_eq!((p0.left, p0.right), ([1u8; 50], [2u8; 50]));
        let p1 = step_merkle_pair_order_400(2, 1, [1u8; 50], [2u8; 50]).unwrap();
        assert_eq!((p1.left, p1.right), ([2u8; 50], [1u8; 50]));
        assert!(step_merkle_pair_order_400(0, 64, [1u8; 50], [2u8; 50]).is_none());

        let g0 = step_merkle_pair_order_gl24(
            3,
            0,
            Gl24Digest {
                l0: 1,
                l1: 1,
                l2: 1,
                l3: 1,
                l4: 1,
                l5: 1,
                l6: 1,
            },
            Gl24Digest {
                l0: 2,
                l1: 2,
                l2: 2,
                l3: 2,
                l4: 2,
                l5: 2,
                l6: 2,
            },
        )
        .unwrap();
        assert_eq!((g0.left.l0, g0.right.l0), (2, 1));
        assert!(
            step_merkle_pair_order_gl24(
                0,
                0,
                Gl24Digest {
                    l0: GOLDILOCKS_P,
                    l1: 0,
                    l2: 0,
                    l3: 0,
                    l4: 0,
                    l5: 0,
                    l6: 0,
                },
                Gl24Digest {
                    l0: 1,
                    l1: 1,
                    l2: 1,
                    l3: 1,
                    l4: 1,
                    l5: 1,
                    l6: 1,
                },
            )
            .is_none()
        );

        assert_eq!(canonical_query_group_idx(7, 0), None);
        assert_eq!(canonical_query_group_idx(u64::MAX, 8), Some(u64::MAX % 8));

        assert_eq!(checked_quorum_sum(&[4, 4, 4], &[3, 4, 2], 12), Some(12));
        assert_eq!(checked_quorum_sum(&[4, 4, 4], &[3, 4, 2], 13), None);
        assert_eq!(checked_quorum_sum(&[u64::MAX, 1], &[1, 1], 2), None);

        let magic = [0x51, 0x53, 0x41, 0x47, 0x48, 0x51, 0x4d, 0x32];
        assert!(verify_qsaghqm2_header(magic, 1, 3, 4, 128, 128).is_some());
        assert!(verify_qsaghqm2_header(magic, 2, 4, 4, 128, 128).is_some());
        assert!(verify_qsaghqm2_header(magic, 3, 3, 4, 128, 128).is_none());
        assert!(verify_qsaghqm2_header(magic, 1, 0, 4, 128, 128).is_none());
        assert!(verify_qsaghqm2_header(magic, 1, 5, 4, 128, 128).is_none());
        assert!(verify_qsaghqm2_header(magic, 1, 3, 4, 0, 0).is_none());
        assert!(verify_qsaghqm2_header(magic, 1, 3, 4, 128, 129).is_none());

        assert!(verify_quintic_schedule_envelope(16, 6, 10, 3));
        assert!(verify_quintic_schedule_envelope(22, 8, 14, 3));
        assert!(verify_quintic_schedule_envelope(23, 7, 16, 4));
        assert!(verify_quintic_schedule_envelope(28, 8, 20, 4));
        assert!(!verify_quintic_schedule_envelope(15, 5, 10, 3));
        assert!(!verify_quintic_schedule_envelope(29, 8, 21, 4));
        assert!(!verify_quintic_schedule_envelope(24, 8, 16, 3));
    }
}
