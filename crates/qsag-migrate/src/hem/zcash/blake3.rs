//! BLAKE3 `derive_key` for inputs of at most one block, natively and as a gadget.
//!
//! ZIP 2005 defines `H^qk(qsk) = BLAKE3.derive_key("Zcash ZIP 2005 qk-derivation v1", qsk, 32)`.
//! Both the context string and the key material fit one 64-byte block, so each of the two
//! BLAKE3 invocations is a single compression of a single-block root chunk. The context
//! key is a public constant; the relation runs one compression (about 15,000 rows).
//! Checked against the official BLAKE3 test vectors.

use alloc::vec::Vec;

use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

use super::blake2::{g32, xor_words};
use crate::hem::hash::Word;

const IV: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
const QUARTERS: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const ROOT: u32 = 1 << 3;
const DERIVE_KEY_CONTEXT: u32 = 1 << 5;
const DERIVE_KEY_MATERIAL: u32 = 1 << 6;

/// The context string of `H^qk` (ZIP 2005).
pub const QK_CONTEXT: &str = "Zcash ZIP 2005 qk-derivation v1";

/// The first eight output words of the compression of a one-block root chunk.
fn compress_root(cv: &[u32; 8], input: &[u8], flags: u32) -> [u32; 8] {
    assert!(input.len() <= 64, "one block only");
    let mut block = [0u8; 64];
    block[..input.len()].copy_from_slice(input);
    let mut m: [u32; 16] =
        core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(cv);
    v[8..12].copy_from_slice(&IV[..4]);
    v[14] = input.len() as u32;
    v[15] = flags | CHUNK_START | CHUNK_END | ROOT;
    for round in 0..7 {
        for (i, q) in QUARTERS.iter().enumerate() {
            let (a, b, c, d) = (q[0], q[1], q[2], q[3]);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[2 * i]);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[2 * i + 1]);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
        if round < 6 {
            m = core::array::from_fn(|i| m[MSG_PERMUTATION[i]]);
        }
    }
    let out = core::array::from_fn(|i| v[i] ^ v[i + 8]);
    qsag_asm::volatile_fill(&mut block, 0);
    qsag_asm::volatile_fill(&mut m, 0);
    qsag_asm::volatile_fill(&mut v, 0);
    out
}

/// The context key of `derive_key` for a context string of at most 64 bytes.
pub fn context_key(context: &str) -> [u32; 8] {
    compress_root(&IV, context.as_bytes(), DERIVE_KEY_CONTEXT)
}

/// `BLAKE3.derive_key(context, key_material, 32)` for a context and key material of at
/// most 64 bytes each.
pub fn derive_key_32(context: &str, key_material: &[u8]) -> [u8; 32] {
    let mut words = compress_root(&context_key(context), key_material, DERIVE_KEY_MATERIAL);
    let mut out = [0u8; 32];
    for (o, w) in out.chunks_exact_mut(4).zip(&words) {
        o.copy_from_slice(&w.to_le_bytes());
    }
    qsag_asm::volatile_fill(&mut words, 0);
    out
}

/// [`derive_key_32`] over the bits of a 32-byte key material (least significant bit first
/// within each byte). Returns the 256 output bits in the same layout.
pub fn derive_key_32_gadget(
    cs: &mut ConstraintSystem,
    context: &str,
    key_material: &[Lc],
) -> Vec<Lc> {
    assert_eq!(key_material.len(), 256, "32-byte key material");
    let cv = context_key(context);
    let mut m: Vec<Word> = (0..16)
        .map(|i| {
            if i < 8 {
                Word::from_bits(key_material[32 * i..32 * i + 32].to_vec())
            } else {
                Word::constant(0, 32)
            }
        })
        .collect();
    let mut v: Vec<Word> = cv.iter().map(|&w| Word::constant(w as u64, 32)).collect();
    v.extend(IV[..4].iter().map(|&w| Word::constant(w as u64, 32)));
    v.push(Word::constant(0, 32));
    v.push(Word::constant(0, 32));
    v.push(Word::constant(32, 32));
    v.push(Word::constant(
        (DERIVE_KEY_MATERIAL | CHUNK_START | CHUNK_END | ROOT) as u64,
        32,
    ));
    for round in 0..7 {
        for (i, q) in QUARTERS.iter().enumerate() {
            g32(cs, &mut v, q, &m[2 * i], &m[2 * i + 1]);
        }
        if round < 6 {
            m = (0..16).map(|i| m[MSG_PERMUTATION[i]].clone()).collect();
        }
    }
    (0..8)
        .flat_map(|i| xor_words(cs, &v[i], &v[i + 8]).into_bits())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::hash::{alloc_bits, bits_to_bytes};
    use std::vec::Vec;

    const TEST_CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
            .collect()
    }

    // BLAKE3 test_vectors.json: `derive_key` (first 32 bytes) for inputs `i % 251`.
    const VECTORS: [(usize, &str); 4] = [
        (
            0,
            "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d",
        ),
        (
            1,
            "b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c",
        ),
        (
            63,
            "b6451e30b953c206e34644c6803724e9d2725e0893039cfc49584f991f451af3",
        ),
        (
            64,
            "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e",
        ),
    ];

    #[test]
    fn derive_key_official_vectors() {
        for (len, want) in VECTORS {
            let input: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
            assert_eq!(
                derive_key_32(TEST_CONTEXT, &input).to_vec(),
                hex(want),
                "len {len}"
            );
        }
        assert_ne!(
            derive_key_32(QK_CONTEXT, &[7; 32]),
            derive_key_32(TEST_CONTEXT, &[7; 32])
        );
    }

    #[test]
    fn gadget_matches_native() {
        for context in [TEST_CONTEXT, QK_CONTEXT] {
            let input: [u8; 32] = core::array::from_fn(|i| (i * 13 + 1) as u8);
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &input);
            let rows0 = cs.num_rows();
            let out = derive_key_32_gadget(&mut cs, context, &bits);
            std::println!("BLAKE3 derive_key: {} rows", cs.num_rows() - rows0);
            assert_eq!(
                bits_to_bytes(&cs, &out),
                derive_key_32(context, &input).to_vec()
            );
            let var = out[0].terms().last().expect("a variable").0 as usize;
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            let mut bad = z.clone();
            bad[var] += qsag_agg::field::Goldilocks::ONE;
            assert!(!shape.is_satisfied(&bad));
        }
    }
}
