//! Boolean word circuits. Words are arrays of little-endian bit wires.
use crate::circuit::{Builder, Domain, Wire};
#[cfg(test)]
use alloc::vec;
use alloc::vec::Vec;
type Word = [Wire; 32];
const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
const RMD_RL: [usize; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
    2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
    13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];
const RMD_RR: [usize; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];
const RMD_SL: [u32; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
    9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
    15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];
const RMD_SR: [u32; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
    7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
    6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];
const KECCAK_RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];
const KECCAK_PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];
fn word(c: &Builder, x: u32) -> Word {
    core::array::from_fn(|i| c.small(Domain::Bit, u64::from((x >> i) & 1)))
}
fn xor(c: &Builder, a: Word, b: Word) -> Word {
    core::array::from_fn(|i| c.add(a[i], b[i]))
}
fn and(c: &Builder, a: Word, b: Word) -> Word {
    core::array::from_fn(|i| c.mul(a[i], b[i]))
}
fn not(c: &Builder, a: Word) -> Word {
    a.map(|b| c.not(b))
}
fn or(c: &Builder, a: Word, b: Word) -> Word {
    xor(c, xor(c, a, b), and(c, a, b))
}
fn rotr(a: Word, n: usize) -> Word {
    core::array::from_fn(|i| a[(i + n) % 32])
}
fn shr(c: &Builder, a: Word, n: usize) -> Word {
    core::array::from_fn(|i| {
        if i + n < 32 {
            a[i + n]
        } else {
            c.small(Domain::Bit, 0)
        }
    })
}
fn add(c: &Builder, a: Word, b: Word) -> Word {
    let mut carry = c.small(Domain::Bit, 0);
    core::array::from_fn(|i| {
        let xc = c.add(a[i], carry);
        let s = c.add(xc, b[i]);
        if i < 31 {
            let yc = c.add(b[i], carry);
            carry = c.add(carry, c.mul(xc, yc));
        }
        s
    })
}
fn csa(c: &Builder, x: Word, y: Word, z: Word) -> (Word, Word) {
    let xy = xor(c, x, y);
    let s = xor(c, xy, z);
    let xz = xor(c, x, z);
    let zero = c.small(Domain::Bit, 0);
    let carry = core::array::from_fn(|i| {
        if i == 0 {
            zero
        } else {
            c.add(x[i - 1], c.mul(xy[i - 1], xz[i - 1]))
        }
    });
    (s, carry)
}
fn sum(c: &Builder, words: &[Word]) -> Word {
    let mut rows = words.to_vec();
    while rows.len() > 2 {
        let mut next = Vec::with_capacity((rows.len() / 3) * 2 + (rows.len() % 3));
        for triple in rows.chunks_exact(3) {
            let (s, carry) = csa(c, triple[0], triple[1], triple[2]);
            next.push(s);
            next.push(carry);
        }
        next.extend_from_slice(&rows[(rows.len() / 3) * 3..]);
        rows = next;
    }
    if rows.len() == 1 {
        rows[0]
    } else {
        add(c, rows[0], rows[1])
    }
}
pub(crate) fn bytes(c: &Builder, bs: &[u8]) -> Vec<Wire> {
    bs.iter()
        .flat_map(|&b| (0..8).map(move |i| c.small(Domain::Bit, u64::from((b >> i) & 1))))
        .collect()
}
fn padding(c: &Builder, input: &[Wire], big: bool) -> Vec<Wire> {
    assert_eq!(input.len() % 8, 0);
    let mut out = input.to_vec();
    out.extend(bytes(c, &[0x80]));
    while out.len() % 512 != 448 {
        out.extend(bytes(c, &[0]));
    }
    let len = input.len() as u64;
    out.extend(bytes(
        c,
        &if big {
            len.to_be_bytes()
        } else {
            len.to_le_bytes()
        },
    ));
    out
}
fn load(block: &[Wire], big: bool) -> Vec<Word> {
    block
        .chunks_exact(32)
        .map(|w| core::array::from_fn(|i| w[if big { (3 - i / 8) * 8 + i % 8 } else { i }]))
        .collect()
}
fn store(words: &[Word], big: bool) -> Vec<Wire> {
    words
        .iter()
        .flat_map(|w| (0..32).map(move |i| w[if big { (3 - i / 8) * 8 + i % 8 } else { i }]))
        .collect()
}
pub(crate) fn sha256(c: &Builder, input: &[Wire]) -> Vec<Wire> {
    let mut state = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ]
    .map(|x| word(c, x));
    for block in padding(c, input, true).chunks_exact(512) {
        let mut w = load(block, true);
        while w.len() < 64 {
            let i = w.len();
            let s0 = xor(
                c,
                xor(c, rotr(w[i - 15], 7), rotr(w[i - 15], 18)),
                shr(c, w[i - 15], 3),
            );
            let s1 = xor(
                c,
                xor(c, rotr(w[i - 2], 17), rotr(w[i - 2], 19)),
                shr(c, w[i - 2], 10),
            );
            w.push(sum(c, &[w[i - 16], s0, w[i - 7], s1]));
        }
        let [mut a, mut b, mut cc, mut d, mut e, mut f, mut g, mut h] = state;
        for (&k, &ww) in SHA256_K.iter().zip(&w) {
            let s1 = xor(c, xor(c, rotr(e, 6), rotr(e, 11)), rotr(e, 25));
            // Ch(e, f, g) = (e & f) ^ (~e & g) = g ^ (e & (f ^ g))  (1 word AND instead of 2)
            let ch = xor(c, g, and(c, e, xor(c, f, g)));
            let t1 = sum(c, &[h, s1, ch, word(c, k), ww]);
            let s0 = xor(c, xor(c, rotr(a, 2), rotr(a, 13)), rotr(a, 22));
            // Maj(a, b, cc) = a ^ ((a ^ b) & (a ^ cc))  (1 word AND instead of 3)
            let maj = xor(c, a, and(c, xor(c, a, b), xor(c, a, cc)));
            let t2 = add(c, s0, maj);
            h = g;
            g = f;
            f = e;
            e = add(c, d, t1);
            d = cc;
            cc = b;
            b = a;
            a = add(c, t1, t2);
        }
        for (s, v) in state.iter_mut().zip([a, b, cc, d, e, f, g, h]) {
            *s = add(c, *s, v);
        }
    }
    store(&state, true)
}
fn rmd_f(c: &Builder, round: usize, x: Word, y: Word, z: Word) -> Word {
    match round / 16 {
        0 => xor(c, xor(c, x, y), z),
        1 => xor(c, z, and(c, x, xor(c, y, z))),
        2 => xor(c, or(c, x, not(c, y)), z),
        3 => xor(c, y, and(c, z, xor(c, x, y))),
        _ => xor(c, x, or(c, y, not(c, z))),
    }
}
pub(crate) fn ripemd160(c: &Builder, input: &[Wire]) -> Vec<Wire> {
    let mut state =
        [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map(|x| word(c, x));
    let kl = [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e];
    let kr = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0];
    for block in padding(c, input, false).chunks_exact(512) {
        let x = load(block, false);
        let mut l = state;
        let mut r = state;
        for (j, &rl) in RMD_RL.iter().enumerate() {
            let tl = add(
                c,
                rotr(
                    sum(
                        c,
                        &[
                            l[0],
                            rmd_f(c, j, l[1], l[2], l[3]),
                            x[rl],
                            word(c, kl[j / 16]),
                        ],
                    ),
                    32 - RMD_SL[j] as usize,
                ),
                l[4],
            );
            let tr = add(
                c,
                rotr(
                    sum(
                        c,
                        &[
                            r[0],
                            rmd_f(c, 79 - j, r[1], r[2], r[3]),
                            x[RMD_RR[j]],
                            word(c, kr[j / 16]),
                        ],
                    ),
                    32 - RMD_SR[j] as usize,
                ),
                r[4],
            );
            l = [l[4], tl, l[1], rotr(l[2], 22), l[3]];
            r = [r[4], tr, r[1], rotr(r[2], 22), r[3]];
        }
        state = [
            sum(c, &[state[1], l[2], r[3]]),
            sum(c, &[state[2], l[3], r[4]]),
            sum(c, &[state[3], l[4], r[0]]),
            sum(c, &[state[4], l[0], r[1]]),
            sum(c, &[state[0], l[1], r[2]]),
        ];
    }
    store(&state, false)
}
type Lane = [Wire; 64];
fn lx(c: &Builder, a: Lane, b: Lane) -> Lane {
    core::array::from_fn(|i| c.add(a[i], b[i]))
}
fn rol(a: Lane, n: usize) -> Lane {
    core::array::from_fn(|i| a[(i + 64 - n) % 64])
}
pub(crate) fn keccak256(c: &Builder, input: &[Wire]) -> Vec<Wire> {
    let zero = c.small(Domain::Bit, 0);
    let mut state = [[zero; 64]; 25];
    let mut padded = input.to_vec();
    padded.extend(bytes(c, &[1]));
    while padded.len() % (136 * 8) != 0 {
        padded.extend(bytes(c, &[0]));
    }
    let last = padded.len() - 1;
    padded[last] = c.not(padded[last]);
    for block in padded.chunks_exact(136 * 8) {
        for (s, lane) in state.iter_mut().zip(block.chunks_exact(64)) {
            *s = lx(c, *s, lane.try_into().unwrap());
        }
        for rc in qsag_accel::keccak::KECCAK_RC {
            let columns: [Lane; 5] = core::array::from_fn(|i| {
                lx(
                    c,
                    lx(
                        c,
                        lx(c, lx(c, state[i], state[i + 5]), state[i + 10]),
                        state[i + 15],
                    ),
                    state[i + 20],
                )
            });
            for (i, s) in state.iter_mut().enumerate() {
                *s = lx(
                    c,
                    *s,
                    lx(c, columns[(i + 4) % 5], rol(columns[(i + 1) % 5], 1)),
                );
            }
            let mut t = state[1];
            for (&j, &n) in KECCAK_PI.iter().zip(&KECCAK_RHO) {
                let next = state[j];
                state[j] = rol(t, n as usize);
                t = next;
            }
            for row in state.chunks_exact_mut(5) {
                let old: [Lane; 5] = core::array::from_fn(|i| row[i]);
                for (i, s) in row.iter_mut().enumerate() {
                    *s = core::array::from_fn(|b| {
                        c.add(
                            old[i][b],
                            c.mul(c.not(old[(i + 1) % 5][b]), old[(i + 2) % 5][b]),
                        )
                    });
                }
            }
            state[0] = lx(
                c,
                state[0],
                core::array::from_fn(|i| c.small(Domain::Bit, (rc >> i) & 1)),
            );
        }
    }
    state[..4].iter().flatten().copied().collect()
}
#[cfg(test)]
mod tests {
    use super::*;
    fn evaluate(c: &Builder, out: Vec<Wire>) -> Vec<u8> {
        out.chunks_exact(8)
            .map(|bits| {
                bits.iter()
                    .enumerate()
                    .fold(0, |a, (i, &w)| a | ((c.value(w)[0] as u8) << i))
            })
            .collect()
    }
    #[test]
    fn hash_circuits_match_native_at_block_boundaries() {
        for n in [0, 3, 55, 56, 64, 135, 136] {
            let c = Builder::default();
            let input = vec![0xa5; n];
            let b: Vec<_> = input
                .iter()
                .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1))
                .map(|bit| c.input(bit))
                .collect();
            assert_eq!(
                evaluate(&c, sha256(&c, &b)),
                qsag_accel::sha2::sha256(&input)
            );
            assert_eq!(
                evaluate(&c, ripemd160(&c, &b)),
                qsag_accel::sha2::ripemd160(&input)
            );
            assert_eq!(
                evaluate(&c, keccak256(&c, &b)),
                qsag_accel::keccak::keccak256(&input)
            );
        }
    }
}
