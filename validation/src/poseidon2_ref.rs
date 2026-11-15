// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Dense-matrix reference for the canonical width-12 Goldilocks `Poseidon2` profile.
//!
//! Written from the profile definition alone, in plain `u64`/`u128` arithmetic, and sharing no
//! code with any `qsag-*` crate:
//!
//! * `M_E = M_4 ⊗ P_3` with `M_4 = circ(2, 3, 1, 1)` and `P_3 = circ(2, 1, 1)`, in flattened
//!   lane order `i = 3 * (M_4 index) + (P_3 index)`;
//! * `M_I = J + diag(-64, 1, 2, 4, ..., 1024)`;
//! * round constants from three Stafford-13 steps over `"POS2_GL1" ^ tag`, `round`, `lane`;
//! * `R_F = 4 + 4` full rounds around `R_P = 22` partial rounds, S-box `x^7`;
//! * rate-8 sponge `hash32` with capacity `(8, 4, 32, "POS2_GL1")`;
//! * weighted compression `perm(in0 ‖ in1 ‖ tweak)[0..4] + in0 + 2·in1 + 4·tweak`.
//!
//! The inverse permutation uses Gauss-Jordan inverses of the two dense matrices.

use std::sync::OnceLock;

/// Goldilocks prime `p = 2^64 - 2^32 + 1`.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;

/// Round-constant and sponge domain IV, ASCII `"POS2_GL1"`.
pub const CONST_IV: u64 = 0x504F_5332_5F47_4C31;

/// Full rounds on each side of the partial rounds.
pub const HALF_FULL_ROUNDS: u64 = 4;

/// Partial rounds.
pub const PARTIAL_ROUNDS: u64 = 22;

/// `7^{-1} mod (p - 1)`, the exponent inverting the S-box.
pub const SBOX_INV_EXP: u64 = 10_540_996_611_094_048_183;

/// A `12 x 12` matrix over Goldilocks, row-major, entries canonical.
pub type Matrix12 = [[u64; 12]; 12];

/// A width-12 state of canonical Goldilocks lanes.
pub type State12 = [u64; 12];

const M4: [[u64; 4]; 4] = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];

/// External matrix `M_E = M_4 ⊗ P_3`.
pub const M_E: Matrix12 = {
    let mut m = [[0u64; 12]; 12];
    let mut i = 0;
    while i < 12 {
        let mut j = 0;
        while j < 12 {
            let p3 = if i % 3 == j % 3 { 2 } else { 1 };
            m[i][j] = M4[i / 3][j / 3] * p3;
            j += 1;
        }
        i += 1;
    }
    m
};

/// Internal matrix `M_I = J + diag(-64, 1, 2, 4, ..., 1024)`.
pub const M_I: Matrix12 = {
    let mut m = [[1u64; 12]; 12];
    m[0][0] = P - 63;
    let mut i = 1;
    while i < 12 {
        m[i][i] = 1 + (1 << (i - 1));
        i += 1;
    }
    m
};

#[inline]
const fn add(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % P as u128) as u64
}

#[inline]
const fn sub(a: u64, b: u64) -> u64 {
    ((a as u128 + P as u128 - b as u128) % P as u128) as u64
}

#[inline]
const fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % P as u128) as u64
}

const fn pow(mut base: u64, mut exp: u64) -> u64 {
    let mut acc = 1u64;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mul(acc, base);
        }
        base = mul(base, base);
        exp >>= 1;
    }
    acc
}

/// `m · x` over Goldilocks.
pub fn mat_vec(m: &Matrix12, x: &State12) -> State12 {
    core::array::from_fn(|i| {
        let acc: u128 = (0..12).map(|j| mul(m[i][j], x[j]) as u128).sum();
        (acc % P as u128) as u64
    })
}

/// Gauss-Jordan inverse of a `12 x 12` matrix over Goldilocks; `None` when singular.
pub fn mat_inv(m: &Matrix12) -> Option<Matrix12> {
    let mut a = *m;
    let mut inv = [[0u64; 12]; 12];
    for (i, row) in inv.iter_mut().enumerate() {
        row[i] = 1;
    }
    for col in 0..12 {
        let pivot = (col..12).find(|&r| a[r][col] != 0)?;
        a.swap(col, pivot);
        inv.swap(col, pivot);
        let scale = pow(a[col][col], P - 2);
        for j in 0..12 {
            a[col][j] = mul(a[col][j], scale);
            inv[col][j] = mul(inv[col][j], scale);
        }
        for r in 0..12 {
            let factor = a[r][col];
            if r == col || factor == 0 {
                continue;
            }
            for j in 0..12 {
                a[r][j] = sub(a[r][j], mul(factor, a[col][j]));
                inv[r][j] = sub(inv[r][j], mul(factor, inv[col][j]));
            }
        }
    }
    Some(inv)
}

fn inverse_matrices() -> &'static (Matrix12, Matrix12) {
    static INV: OnceLock<(Matrix12, Matrix12)> = OnceLock::new();
    INV.get_or_init(|| {
        (
            mat_inv(&M_E).expect("canonical M_E is invertible"),
            mat_inv(&M_I).expect("canonical M_I is invertible"),
        )
    })
}

const fn stafford13(x: u64) -> u64 {
    let z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Round constant for `(tag, round, lane)`; `tag` is 0 (first full rounds), 1 (partial), 2 (last).
pub const fn round_constant(tag: u64, round: u64, lane: u64) -> u64 {
    stafford13(stafford13(stafford13(CONST_IV ^ tag) ^ round) ^ lane) % P
}

/// Canonical permutation. Lanes are reduced modulo `p` on entry.
pub fn perm12(x: &State12) -> State12 {
    let mut st = mat_vec(&M_E, &x.map(|v| v % P));
    for (tag, rounds) in [(0, HALF_FULL_ROUNDS), (1, PARTIAL_ROUNDS), (2, HALF_FULL_ROUNDS)] {
        for r in 0..rounds {
            if tag == 1 {
                st[0] = pow(add(st[0], round_constant(1, r, 0)), 7);
                st = mat_vec(&M_I, &st);
            } else {
                let sboxed =
                    core::array::from_fn(|i| pow(add(st[i], round_constant(tag, r, i as u64)), 7));
                st = mat_vec(&M_E, &sboxed);
            }
        }
    }
    st
}

/// Inverse of [`perm12`].
pub fn perm12_inv(y: &State12) -> State12 {
    let (me_inv, mi_inv) = inverse_matrices();
    let mut st = y.map(|v| v % P);
    for (tag, rounds) in [(2, HALF_FULL_ROUNDS), (1, PARTIAL_ROUNDS), (0, HALF_FULL_ROUNDS)] {
        for r in (0..rounds).rev() {
            if tag == 1 {
                st = mat_vec(mi_inv, &st);
                st[0] = sub(pow(st[0], SBOX_INV_EXP), round_constant(1, r, 0));
            } else {
                let mixed = mat_vec(me_inv, &st);
                st = core::array::from_fn(|i| {
                    sub(pow(mixed[i], SBOX_INV_EXP), round_constant(tag, r, i as u64))
                });
            }
        }
    }
    mat_vec(me_inv, &st)
}

/// 256-bit sponge hash: 7-byte big-endian limbs behind a `0x01` byte marker, `10*1` limb padding
/// to the rate of 8, capacity `(8, 4, 32, CONST_IV)`, four big-endian output lanes.
pub fn hash32(msg: &[u8]) -> [u8; 32] {
    let mut bytes = msg.to_vec();
    bytes.push(0x01);
    bytes.resize(bytes.len().next_multiple_of(7), 0);
    let mut limbs: Vec<u64> = bytes
        .as_chunks::<7>()
        .0
        .iter()
        .map(|c| c.iter().fold(0u64, |acc, &b| (acc << 8) | b as u64))
        .collect();
    let zeros = (8 - (limbs.len() + 1) % 8) % 8;
    if zeros == 0 {
        limbs.push((1 << 56) + 1);
    } else {
        limbs.push(1);
        limbs.resize(limbs.len() + zeros - 1, 0);
        limbs.push(1 << 56);
    }
    let mut st: State12 = [0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 32, CONST_IV];
    for block in limbs.as_chunks::<8>().0 {
        for (lane, &limb) in block.iter().enumerate() {
            st[lane] = add(st[lane], limb);
        }
        st = perm12(&st);
    }
    let mut out = [0u8; 32];
    for (chunk, lane) in out.as_chunks_mut::<8>().0.iter_mut().zip(st) {
        *chunk = lane.to_be_bytes();
    }
    out
}

/// Weighted compression `perm(in0 ‖ in1 ‖ tweak)[0..4] + in0 + 2·in1 + 4·tweak`.
pub fn compress(in0: [u64; 4], in1: [u64; 4], tweak: [u64; 4]) -> [u64; 4] {
    let x: State12 = core::array::from_fn(|i| [in0, in1, tweak][i / 4][i % 4] % P);
    let y = perm12(&x);
    core::array::from_fn(|i| {
        add(
            add(y[i], x[i]),
            add(mul(2, x[4 + i]), mul(4, x[8 + i])),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEQ: State12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    #[test]
    fn matrices_have_the_stated_shape() {
        // First row of `M_4 ⊗ P_3`: `2·P_3[0], 3·P_3[0], 1·P_3[0], 1·P_3[0]`.
        assert_eq!(M_E[0], [4, 2, 2, 6, 3, 3, 2, 1, 1, 2, 1, 1]);
        for i in 0..12 {
            for j in 0..12 {
                // Circulant in both tensor factors.
                assert_eq!(M_E[i][j], M_E[(i + 3) % 12][(j + 3) % 12]);
                assert_eq!(M_E[i][j], M_E[i / 3 * 3 + (i + 1) % 3][j / 3 * 3 + (j + 1) % 3]);
                if i != j {
                    assert_eq!(M_I[i][j], 1);
                }
            }
        }
        let diag: [u64; 12] = core::array::from_fn(|i| sub(M_I[i][i], 1));
        assert_eq!(diag, [P - 64, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]);
        assert_eq!((7u128 * SBOX_INV_EXP as u128) % (P as u128 - 1), 1);
    }

    #[test]
    fn inverse_matrices_are_two_sided() {
        let (me_inv, mi_inv) = inverse_matrices();
        for (m, inv) in [(&M_E, me_inv), (&M_I, mi_inv)] {
            for j in 0..12 {
                let mut e = [0u64; 12];
                e[j] = 1;
                assert_eq!(mat_vec(inv, &mat_vec(m, &e)), e);
                assert_eq!(mat_vec(m, &mat_vec(inv, &e)), e);
            }
        }
    }

    /// The vectors that the canonical `Poseidon2.lean` checks by kernel reduction.
    #[test]
    fn canonical_known_answers() {
        assert_eq!(
            perm12(&[0; 12]),
            [
                17528629447354354351,
                5014055130248055117,
                10679077121839038553,
                431078547345611051,
                7807009921345120310,
                2413869689279715014,
                11875300792986830377,
                1872634884137602556,
                15069512080271275672,
                14253608580209913153,
                14550618143248480092,
                107036164978639472
            ]
        );
        assert_eq!(
            perm12(&SEQ),
            [
                13782584570844608145,
                13136387643152332171,
                7171133015474200819,
                7643370872200861694,
                14144755201299840503,
                16470027036684692562,
                1748465969625202405,
                1718729118078964347,
                6141020819996733037,
                16322330185628708898,
                11650380702735067362,
                2734959974607798415
            ]
        );
        assert_eq!(
            hex::encode(hash32(b"")),
            "b6a8416a0036177c167477c74bfdca917b0d73c8ba8fcf42a2a1c609dc25b0a2"
        );
        assert_eq!(
            hex::encode(hash32(b"qsag-poseidon2-kat")),
            "e49c8c937c0a64c5676aa807fec4fab7d482111a028beb0fdb2ec1ee9432ece5"
        );
        assert_eq!(
            compress([0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]),
            [
                13782584570844608185,
                13136387643152332218,
                7171133015474200873,
                7643370872200861755
            ]
        );
    }

    #[test]
    fn inverse_permutation_is_two_sided() {
        for x in [[0; 12], SEQ, [P - 1; 12], core::array::from_fn(|i| stafford13(i as u64) % P)] {
            assert_eq!(perm12_inv(&perm12(&x)), x);
            assert_eq!(perm12(&perm12_inv(&x)), x);
        }
    }
}
