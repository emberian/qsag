// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Differential test of the 56-bit limb packing behind the migration nullifier.
//!
//! Lean specifies `Qsag.pack256ToLimbs56` on a `BitVec 256` as the base-`2^56` digits,
//! most significant first, of `x * 2^24 + 2^16`. Rust packs 32 bytes followed by
//! `01 00 00` in big-endian seven-byte chunks. The two agree only if the 32 bytes are read
//! as a big-endian integer, which is what this file checks:
//!
//! - `fixtures/lean_pack256_limbs56.jsonl` holds outputs of the Lean definitions
//!   (`fixtures/lean_pack256_limbs56.gen.lean`). Every row is compared with
//!   `qsag-accel`, `qsag-core` and the `qsag-migrate` call sites.
//! - [`spec_limbs`] is the Lean formula in word arithmetic. It is first checked against
//!   the fixture and then used as the oracle for random inputs.
//!
//! `QSAG_LEAN_PACK256_JSONL` overrides the embedded fixture with a freshly generated one.

use proptest::prelude::*;
use qsag_accel::goldilocks::pack_bytes32_to_limbs56;
use qsag_accel::poseidon2::poseidon2_hash_limbs;
use qsag_core::sponge::poseidon2::pack_bytes32_to_limbs56_canonical;
use qsag_migrate::scalar::NULLIFIER_DOMAIN;
use qsag_migrate::{LegacyCommitmentKind, ScalarGroup, SpendingScalar};
use serde::Deserialize;

const EMBEDDED_JSONL: &str = include_str!("fixtures/lean_pack256_limbs56.jsonl");
const LIMB_MASK: u64 = (1 << 56) - 1;

#[derive(Deserialize)]
struct Row {
    kind: String,
    #[serde(default)]
    x: String,
    #[serde(default)]
    limbs: Vec<String>,
    #[serde(default)]
    group: String,
    #[serde(default)]
    s: String,
    #[serde(default)]
    domain: String,
    #[serde(default)]
    input: Vec<String>,
}

fn rows() -> Vec<Row> {
    let raw = match std::env::var("QSAG_LEAN_PACK256_JSONL") {
        Ok(path) if !path.is_empty() => {
            std::fs::read_to_string(&path).expect("read QSAG_LEAN_PACK256_JSONL")
        }
        _ => EMBEDDED_JSONL.to_string(),
    };
    raw.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| serde_json::from_str(line).expect("parse pack256 fixture row"))
        .collect()
}

fn be_bytes(hex_be: &str) -> [u8; 32] {
    hex::decode(hex_be)
        .expect("hex")
        .try_into()
        .expect("32 bytes")
}

fn decimals<const N: usize>(values: &[String]) -> [u64; N] {
    let parsed: Vec<u64> = values.iter().map(|v| v.parse().expect("decimal limb")).collect();
    parsed.try_into().expect("limb count")
}

/// `((x * 2^24 + 2^16) / 2^(56 * (4 - k))) % 2^56` for `k = 0..5`, with `x` the
/// big-endian integer in `bytes`, computed on little-endian 64-bit words.
fn spec_limbs(bytes: &[u8; 32]) -> [u64; 5] {
    let mut x = [0u64; 4];
    for (word, chunk) in x.iter_mut().rev().zip(bytes.as_chunks::<8>().0) {
        *word = u64::from_be_bytes(*chunk);
    }
    // n = x << 24, at most 280 bits; then the 2^16 delimiter into the vacated low bits.
    let mut n = [0u64; 5];
    for i in 0..4 {
        n[i] |= x[i] << 24;
        n[i + 1] |= x[i] >> 40;
    }
    n[0] += 1 << 16;
    core::array::from_fn(|k| {
        let shift = 56 * (4 - k);
        let (word, bit) = (shift / 64, shift % 64);
        let low = n[word] >> bit;
        let high = if bit == 0 || word + 1 == n.len() {
            0
        } else {
            n[word + 1] << (64 - bit)
        };
        (low | high) & LIMB_MASK
    })
}

/// Inverse of the packing, so a wrong chunk order cannot hide behind a symmetric input.
fn unpack(limbs: &[u64; 5]) -> ([u8; 32], [u8; 3]) {
    let mut marked = [0u8; 35];
    for (chunk, limb) in marked.as_chunks_mut::<7>().0.iter_mut().zip(limbs) {
        chunk.copy_from_slice(&limb.to_be_bytes()[1..]);
    }
    (
        marked[..32].try_into().unwrap(),
        marked[32..].try_into().unwrap(),
    )
}

fn assert_all_packers(bytes: &[u8; 32], expected: [u64; 5], context: &str) {
    assert_eq!(pack_bytes32_to_limbs56(bytes), expected, "qsag-accel: {context}");
    assert_eq!(
        pack_bytes32_to_limbs56_canonical(bytes).map(|limb| limb.to_canonical_u64()),
        expected,
        "qsag-core: {context}"
    );
    let commitment = LegacyCommitmentKind::BitcoinTaprootXOnly(*bytes).to_canonical_limbs56();
    assert_eq!(commitment[0], 2, "taproot tag: {context}");
    assert_eq!(commitment[1..], expected, "qsag-migrate legacy commitment: {context}");
}

#[test]
fn rust_packing_equals_lean_pack256_to_limbs56() {
    let mut checked = 0usize;
    for row in rows().iter().filter(|row| row.kind != "nullifier_input") {
        let bytes = be_bytes(&row.x);
        let lean: [u64; 5] = decimals(&row.limbs);
        let context = format!("{} x={}", row.kind, row.x);
        assert_eq!(spec_limbs(&bytes), lean, "word-arithmetic spec: {context}");
        assert_all_packers(&bytes, lean, &context);
        assert!(lean.iter().all(|&limb| limb <= LIMB_MASK), "{context}");
        assert_eq!(unpack(&lean), (bytes, [1, 0, 0]), "{context}");
        checked += 1;
    }
    assert_eq!(checked, 1125, "fixture lost pack rows");
}

/// The values Lean proves by `decide` in `pack256ToLimbs56_zero_delimiter` and
/// `pack256ToLimbs56_end_bytes`, independent of the fixture file.
#[test]
fn rust_packing_equals_the_kernel_checked_lean_vectors() {
    assert_eq!(pack_bytes32_to_limbs56(&[0; 32])[4], 65536);
    let mut end_bytes = [0u8; 32];
    end_bytes[0] = 1;
    end_bytes[31] = 1;
    let limbs = pack_bytes32_to_limbs56(&end_bytes);
    assert_eq!(limbs[0], 1 << 48);
    assert_eq!(limbs[4], (1 << 24) + (1 << 16));
    assert_all_packers(&end_bytes, [1 << 48, 0, 0, 0, (1 << 24) + (1 << 16)], "end bytes");
}

/// A little-endian reading of the bytes, a reversed limb order, and a missing delimiter
/// are each rejected by the Lean rows.
#[test]
fn lean_rows_reject_the_wrong_endianness_and_layout() {
    let all = rows();
    let ramp = all.iter().find(|row| row.kind == "byte_ramp").expect("byte_ramp row");
    let bytes = be_bytes(&ramp.x);
    let lean: [u64; 5] = decimals(&ramp.limbs);

    let mut little_endian = bytes;
    little_endian.reverse();
    assert_ne!(pack_bytes32_to_limbs56(&little_endian), lean);

    let mut reversed_limbs = pack_bytes32_to_limbs56(&bytes);
    reversed_limbs.reverse();
    assert_ne!(reversed_limbs, lean);

    let reversed = all
        .iter()
        .find(|row| row.kind == "byte_ramp_reversed")
        .expect("byte_ramp_reversed row");
    assert_eq!(be_bytes(&reversed.x), little_endian);
    assert_ne!(decimals::<5>(&reversed.limbs), lean);

    // Every single-bit input lands in exactly one limb bit, at the position the
    // big-endian reading predicts: bit `i` of `x` is bit `i + 24` of the marked integer.
    for (i, row) in all.iter().filter(|row| row.kind == "bit").enumerate() {
        let lean: [u64; 5] = decimals(&row.limbs);
        let position = i + 24;
        let mut expected = [0u64; 5];
        expected[4] = 1 << 16;
        expected[4 - position / 56] |= 1 << (position % 56);
        assert_eq!(lean, expected, "bit {i}");
    }
}

#[test]
fn rust_nullifier_preimage_equals_lean_migration_nullifier_input() {
    let mut checked = 0usize;
    for row in rows().iter().filter(|row| row.kind == "nullifier_input") {
        let group = match row.group.as_str() {
            "secp256k1" => ScalarGroup::Secp256k1,
            "ed25519" => ScalarGroup::Ed25519,
            other => panic!("unknown group {other}"),
        };
        let s_be = be_bytes(&row.s);
        let domain = be_bytes(&row.domain);
        let lean_input: [u64; 11] = decimals(&row.input);

        let mut rust_input = [0u64; 11];
        rust_input[0] = match group {
            ScalarGroup::Secp256k1 => 1,
            ScalarGroup::Ed25519 => 2,
        };
        rust_input[1..6].copy_from_slice(&spec_limbs(&s_be));
        rust_input[6..].copy_from_slice(&spec_limbs(&domain));
        assert_eq!(rust_input, lean_input, "preimage layout: s={} domain={}", row.s, row.domain);

        let mut s_le = s_be;
        s_le.reverse();
        let scalar = SpendingScalar::from_le_bytes(s_le, group).expect("canonical scalar");
        assert_eq!(scalar.to_be_bytes(), s_be);
        let nullifier = scalar.compute_nullifier(&domain);
        assert_eq!(
            nullifier,
            poseidon2_hash_limbs(NULLIFIER_DOMAIN, &lean_input),
            "compute_nullifier hashes the Lean preimage: s={} domain={}",
            row.s,
            row.domain
        );

        // The scalar read little-endian, or the scalar and domain exchanged, is a
        // different preimage and a different nullifier.
        let mut swapped = lean_input;
        swapped[1..6].copy_from_slice(&lean_input[6..]);
        swapped[6..].copy_from_slice(&lean_input[1..6]);
        if swapped != lean_input {
            assert_ne!(nullifier, poseidon2_hash_limbs(NULLIFIER_DOMAIN, &swapped));
        }
        let mut little_endian = lean_input;
        little_endian[1..6].copy_from_slice(&spec_limbs(&s_le));
        if little_endian != lean_input {
            assert_ne!(nullifier, poseidon2_hash_limbs(NULLIFIER_DOMAIN, &little_endian));
        }
        checked += 1;
    }
    assert_eq!(checked, 64, "fixture lost nullifier rows");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20_000))]

    #[test]
    fn rust_packing_equals_the_spec_formula_on_random_inputs(bytes in any::<[u8; 32]>()) {
        let expected = spec_limbs(&bytes);
        prop_assert_eq!(pack_bytes32_to_limbs56(&bytes), expected);
        prop_assert_eq!(
            pack_bytes32_to_limbs56_canonical(&bytes).map(|limb| limb.to_canonical_u64()),
            expected
        );
        prop_assert!(expected.iter().all(|&limb| limb <= LIMB_MASK));
        prop_assert_eq!(expected[4] & 0xff_ffff, 0x01_0000);
        prop_assert_eq!(unpack(&expected), (bytes, [1, 0, 0]));
    }

    /// One flipped input bit changes exactly one limb, by exactly that bit.
    #[test]
    fn a_flipped_bit_moves_one_limb_bit(bytes in any::<[u8; 32]>(), bit in 0usize..256) {
        let mut flipped = bytes;
        flipped[31 - bit / 8] ^= 1 << (bit % 8);
        let (a, b) = (pack_bytes32_to_limbs56(&bytes), pack_bytes32_to_limbs56(&flipped));
        let position = bit + 24;
        for k in 0..5 {
            let expected = if k == 4 - position / 56 { 1u64 << (position % 56) } else { 0 };
            prop_assert_eq!(a[k] ^ b[k], expected);
        }
    }
}
