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

/// Whether a complete field of the given width fits at this byte offset.
fn has_bytes_at(bytes: &[u8], off: usize, width: usize) -> bool {
    width <= bytes.len() && off <= bytes.len() - width
}

/// Read a possibly unaligned little-endian word without advancing the caller.
pub fn load_le_u64_slice(bytes: &[u8], off: usize) -> Option<u64> {
    if !has_bytes_at(bytes, off, 8) {
        return None;
    }
    Some(
        (bytes[off] as u64)
            | ((bytes[off + 1] as u64) << 8)
            | ((bytes[off + 2] as u64) << 16)
            | ((bytes[off + 3] as u64) << 24)
            | ((bytes[off + 4] as u64) << 32)
            | ((bytes[off + 5] as u64) << 40)
            | ((bytes[off + 6] as u64) << 48)
            | ((bytes[off + 7] as u64) << 56),
    )
}

pub fn decode_canonical_u64_at(bytes: &[u8], off: usize) -> Option<u64> {
    let Some(word) = load_le_u64_slice(bytes, off) else {
        return None;
    };
    decode_canonical_u64(word)
}

/// Read one canonical Fp5 at an arbitrary byte offset.
pub fn decode_canonical_fp5_at(bytes: &[u8], off: usize) -> Option<Fp5> {
    if !has_bytes_at(bytes, off, 40) {
        return None;
    }
    let Some(l0) = load_le_u64_slice(bytes, off) else {
        return None;
    };
    let Some(l1) = load_le_u64_slice(bytes, off + 8) else {
        return None;
    };
    let Some(l2) = load_le_u64_slice(bytes, off + 16) else {
        return None;
    };
    let Some(l3) = load_le_u64_slice(bytes, off + 24) else {
        return None;
    };
    let Some(l4) = load_le_u64_slice(bytes, off + 32) else {
        return None;
    };
    decode_canonical_fp5_limbs(l0, l1, l2, l3, l4)
}

/// Read one canonical Gl24Digest at an arbitrary byte offset.
pub fn decode_canonical_gl24_at(bytes: &[u8], off: usize) -> Option<Gl24Digest> {
    if !has_bytes_at(bytes, off, 56) {
        return None;
    }
    let Some(l0) = load_le_u64_slice(bytes, off) else {
        return None;
    };
    let Some(l1) = load_le_u64_slice(bytes, off + 8) else {
        return None;
    };
    let Some(l2) = load_le_u64_slice(bytes, off + 16) else {
        return None;
    };
    let Some(l3) = load_le_u64_slice(bytes, off + 24) else {
        return None;
    };
    let Some(l4) = load_le_u64_slice(bytes, off + 32) else {
        return None;
    };
    let Some(l5) = load_le_u64_slice(bytes, off + 40) else {
        return None;
    };
    let Some(l6) = load_le_u64_slice(bytes, off + 48) else {
        return None;
    };
    decode_canonical_gl24_limbs(l0, l1, l2, l3, l4, l5, l6)
}

/// Number of edges below the first common parent of two distinct sorted leaves,
/// on either path, excluding the edge incident to that parent.
fn sibling_path_below_join(mut difference: u64) -> u64 {
    let mut height = 0;
    while difference > 1 {
        difference >>= 1;
        height += 1;
    }
    height
}

/// The first leaf opens one sibling per level. Each following leaf replaces
/// one of those unopened subtrees by the sibling path inside it. Sorted order
/// makes its predecessor the leaf with the deepest common ancestor.
pub fn compute_steiner_multiproof_siblings(log_leaves: u32, indices: &[usize]) -> Option<usize> {
    if log_leaves > MAX_CANOPY_LOG_LEAVES || indices.is_empty() {
        return None;
    }
    let limit = 1usize << log_leaves;
    let mut previous = indices[0];
    if previous >= limit {
        return None;
    }
    let mut siblings = log_leaves as usize;
    let mut i = 1;
    let mut valid = true;
    while valid && i < indices.len() {
        let leaf = indices[i];
        valid = previous < leaf && leaf < limit && siblings != 0;
        if valid {
            siblings = siblings - 1 + sibling_path_below_join((previous ^ leaf) as u64) as usize;
            previous = leaf;
        }
        i += 1;
    }
    if valid { Some(siblings) } else { None }
}

/// Reciprocal of the Lagrange denominator at node i of the grid 0 through 8.
fn row_interpolation_weight(i: usize) -> u64 {
    match i {
        0 | 8 => 877958875724369725,
        1 | 7 => 11423073063619626521,
        2 | 6 => 6136104450867767979,
        3 | 5 => 6174535167679048363,
        _ => 6116889092462127787,
    }
}

/// Interpolate the nine evaluations at nodes 0 through 8, enforcing the
/// Boolean sum at the incoming claim. The challenge comes from the transcript
/// after absorption of these exact 360 bytes.
pub fn verify_deg8_row_sumcheck_round_at(
    payload: &[u8],
    off: usize,
    claim: Fp5,
    challenge: Fp5,
) -> Option<Fp5> {
    if !has_bytes_at(payload, off, 360) {
        return None;
    }
    let mut first = fp5_zero();
    let mut sum = fp5_zero();
    let mut product = fp5_one();
    let mut i = 0;
    while i < 9 {
        let Some(value) = decode_canonical_fp5_at(payload, off + 40 * i) else {
            return None;
        };
        if i == 0 {
            first = copy_fp5(&value);
        } else if i == 1
            && !fp5_eq(
                fp5_add(copy_fp5(&first), copy_fp5(&value)),
                copy_fp5(&claim),
            )
        {
            return None;
        }
        let weight = row_interpolation_weight(i);
        let factor = fp5_sub(copy_fp5(&challenge), fp5_from_base(i as u64));
        sum = fp5_add(
            fp5_mul(sum, copy_fp5(&factor)),
            fp5_mul(copy_fp5(&product), fp5_scale(value, weight)),
        );
        product = fp5_mul(product, factor);
        i += 1;
    }
    Some(sum)
}

/// Fold the row claim from zero using the post-absorption challenge for each
/// round. A table with at most 28 variables has at most 20 row coordinates.
pub fn verify_qsaghqm2_row_rounds_at(
    payload: &[u8],
    off: usize,
    challenges: &[Fp5],
) -> Option<Fp5> {
    if challenges.len() > 20 || !has_bytes_at(payload, off, 360 * challenges.len()) {
        return None;
    }
    let mut claim = fp5_zero();
    let mut i = 0;
    while i < challenges.len() {
        let Some(next) = verify_deg8_row_sumcheck_round_at(
            payload,
            off + 360 * i,
            claim,
            copy_fp5(&challenges[i]),
        ) else {
            return None;
        };
        claim = next;
        i += 1;
    }
    Some(claim)
}

/// End of a fixed-width block whose element count comes from the verifier geometry.
/// Division before multiplication also checks offsets near the address-space limit.
fn block_end(len: usize, off: usize, count: usize, width: usize) -> Option<usize> {
    if width == 0 || off > len || count > (len - off) / width {
        None
    } else {
        Some(off + count * width)
    }
}

/// Check all little-endian field words in a half-open byte interval.
fn canonical_words_between(bytes: &[u8], mut off: usize, end: usize) -> bool {
    if end > bytes.len() || off > end || (end - off) % 8 != 0 {
        return false;
    }
    while off < end {
        let Some(_) = decode_canonical_u64_at(bytes, off) else {
            return false;
        };
        off += 8;
    }
    true
}

/// Validate contiguous root or sibling commitments of the given wire profile.
pub fn qsaghqm2_digest_block_end(bytes: &[u8], off: usize, count: usize, tag: u8) -> Option<usize> {
    if tag == QSAGHQM2_PROFILE_TURBO400 {
        block_end(bytes.len(), off, count, 50)
    } else if tag == QSAGHQM2_PROFILE_GL24 {
        let Some(end) = block_end(bytes.len(), off, count, 56) else {
            return None;
        };
        if canonical_words_between(bytes, off, end) {
            Some(end)
        } else {
            None
        }
    } else {
        None
    }
}

/// Check fiber symbols and the pruned authentication path. Return the split
/// between symbols and siblings, and the first byte after the opening. The
/// caller hashes these exact intervals against its transcript-bound root.
pub fn qsaghqm2_opening_bounds(
    bytes: &[u8],
    off: usize,
    indices: &[usize],
    log_leaves: u32,
    step_vars: u32,
    base: bool,
    tag: u8,
) -> Option<(usize, usize)> {
    if step_vars > MAX_QUINTIC_LOG_CELLS {
        return None;
    }
    let Some(siblings) = compute_steiner_multiproof_siblings(log_leaves, indices) else {
        return None;
    };
    let width = if base { 8 } else { 40 };
    let Some(fiber_width) = block_end(bytes.len(), 0, 1usize << step_vars, width) else {
        return None;
    };
    let Some(split) = block_end(bytes.len(), off, indices.len(), fiber_width) else {
        return None;
    };
    if !canonical_words_between(bytes, off, split) {
        return None;
    }
    let Some(end) = qsaghqm2_digest_block_end(bytes, split, siblings, tag) else {
        return None;
    };
    Some((split, end))
}

/// Fiat–Shamir challenges for a single five-element CWYZ message.
pub struct CwyzFoldChals {
    pub phi: Fp5,
    pub theta: Fp5,
    pub alpha: Fp5,
    pub beta: Fp5,
}

macro_rules! wire_value {
    ($value:expr) => {
        match $value {
            Some(value) => value,
            None => return None,
        }
    };
}

/// Decode the five wire elements and advance the dual linear-functional claim.
pub fn verify_qsaghqm2_cwyz_fold_at(
    payload: &[u8],
    off: usize,
    claim: Fp5,
    chals: CwyzFoldChals,
) -> Option<Fp5> {
    if !has_bytes_at(payload, off, 200) {
        return None;
    }
    let sigma_even = wire_value!(decode_canonical_fp5_at(payload, off));
    let tau_01 = wire_value!(decode_canonical_fp5_at(payload, off + 40));
    let tau_10 = wire_value!(decode_canonical_fp5_at(payload, off + 80));
    let c_f = wire_value!(decode_canonical_fp5_at(payload, off + 120));
    let c_g = wire_value!(decode_canonical_fp5_at(payload, off + 160));
    Some(cwyz_bridge_claim_step_fp5(
        sigma_even,
        tau_01,
        tau_10,
        c_f,
        c_g,
        claim,
        chals.phi,
        chals.theta,
        chals.alpha,
        chals.beta,
    ))
}

/// Replay all fold messages in a single oracle stage.
pub fn verify_qsaghqm2_cwyz_folds_at(
    payload: &[u8],
    off: usize,
    mut claim: Fp5,
    fold_chals: &[CwyzFoldChals],
) -> Option<Fp5> {
    if fold_chals.len() > MAX_QUINTIC_LOG_CELLS as usize {
        return None;
    }
    wire_value!(block_end(payload.len(), off, fold_chals.len(), 200));
    let mut i = 0;
    while i < fold_chals.len() {
        let c = &fold_chals[i];
        let chals = CwyzFoldChals {
            phi: copy_fp5(&c.phi),
            theta: copy_fp5(&c.theta),
            alpha: copy_fp5(&c.alpha),
            beta: copy_fp5(&c.beta),
        };
        claim = wire_value!(verify_qsaghqm2_cwyz_fold_at(
            payload,
            off + 200 * i,
            claim,
            chals
        ));
        i += 1;
    }
    Some(claim)
}

/// Verifier-derived geometry and sorted transcript queries for one commitment.
pub struct StageEnvelope<'a> {
    pub step_vars: u32,
    pub log_leaves: u32,
    pub indices: &'a [usize],
}

fn fp5_block_end(bytes: &[u8], off: usize, count: usize) -> Option<usize> {
    let end = wire_value!(block_end(bytes.len(), off, count, 40));
    if canonical_words_between(bytes, off, end) {
        Some(end)
    } else {
        None
    }
}

/// Consume a fold block, the next commitment and OOD values (or the terminal
/// polynomial), then the current commitment's opening at its transcript queries.
fn qsaghqm2_stage_end(
    bytes: &[u8],
    off: usize,
    stage: &StageEnvelope<'_>,
    base: bool,
    terminal_count: usize,
    tag: u8,
) -> Option<usize> {
    if stage.step_vars == 0 || stage.step_vars > 6 {
        return None;
    }
    let folds = wire_value!(fp5_block_end(bytes, off, 5 * stage.step_vars as usize));
    let opening = if terminal_count == 0 {
        let root = wire_value!(qsaghqm2_digest_block_end(bytes, folds, 1, tag));
        wire_value!(fp5_block_end(bytes, root, 2))
    } else {
        wire_value!(fp5_block_end(bytes, folds, terminal_count))
    };
    let (_, end) = wire_value!(qsaghqm2_opening_bounds(
        bytes,
        opening,
        stage.indices,
        stage.log_leaves,
        stage.step_vars,
        base,
        tag,
    ));
    Some(end)
}

/// The two deployed schedule shapes, with each opening bound to its own indices.
pub struct PayloadStages<'a> {
    pub first: StageEnvelope<'a>,
    pub second: StageEnvelope<'a>,
    pub third: StageEnvelope<'a>,
    pub fourth: Option<StageEnvelope<'a>>,
}

fn payload_schedule_ok(
    rows: usize,
    early: u32,
    a: u32,
    b: u32,
    c: u32,
    extra: u32,
    count: u32,
) -> bool {
    if rows > 20 || a > 6 || b > 6 || c > 6 || extra > 6 {
        return false;
    }
    verify_quintic_schedule_envelope(rows as u32 + 8, early, a + b + c + extra, count)
}

/// Check the complete payload after stripping the framed header. The returned
/// zero-initialized row sumcheck's terminal value is pinned to the row relation
/// by the caller. The caller also replays the fold claims and hashes the openings.
pub fn verify_qsaghqm2_multiproof_and_rounds(
    payload: &[u8],
    tag: u8,
    row_challenges: &[Fp5],
    early_stop_vars: u32,
    stages: PayloadStages<'_>,
) -> Option<Fp5> {
    let (extra, count) = match &stages.fourth {
        Some(stage) => (stage.step_vars, 4),
        None => (0, 3),
    };
    if early_stop_vars > 8
        || !payload_schedule_ok(
            row_challenges.len(),
            early_stop_vars,
            stages.first.step_vars,
            stages.second.step_vars,
            stages.third.step_vars,
            extra,
            count,
        )
    {
        return None;
    }
    let row = wire_value!(qsaghqm2_digest_block_end(payload, 0, 1, tag));
    let claim = wire_value!(verify_qsaghqm2_row_rounds_at(payload, row, row_challenges));
    let cols = wire_value!(block_end(payload.len(), row, row_challenges.len(), 360));
    let ood = wire_value!(fp5_block_end(payload, cols, 256));
    let off = wire_value!(fp5_block_end(payload, ood, 5));
    let off = wire_value!(qsaghqm2_stage_end(
        payload,
        off,
        &stages.first,
        true,
        0,
        tag
    ));
    let off = wire_value!(qsaghqm2_stage_end(
        payload,
        off,
        &stages.second,
        false,
        0,
        tag
    ));
    let terminal = (1usize << early_stop_vars) + 2;
    let end = match &stages.fourth {
        None => wire_value!(qsaghqm2_stage_end(
            payload,
            off,
            &stages.third,
            false,
            terminal,
            tag
        )),
        Some(last) => {
            let off = wire_value!(qsaghqm2_stage_end(
                payload,
                off,
                &stages.third,
                false,
                0,
                tag
            ));
            wire_value!(qsaghqm2_stage_end(payload, off, last, false, terminal, tag))
        }
    };
    if end == payload.len() {
        Some(claim)
    } else {
        None
    }
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
