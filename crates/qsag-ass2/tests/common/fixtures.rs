//! Real protocol inputs for the four firmware images, computed by the live `qsag-agg` and
//! `qsag-accel` implementations. `tests/firmware_kat.rs` and
//! `examples/export_cosim_vectors.rs` both include this file and each uses a subset of it.
#![allow(dead_code)]

use core::array::from_fn;
use qsag_accel::{gf2_128::gf2_128_mul_const, poseidon2::poseidon2_gl24_compress_merkle};
use qsag_agg::field::Goldilocks;
use qsag_agg::sig::wots_step_hash_injective;
use qsag_agg::sponge::{turboshake256_from_midstate_into, turboshake256_static_midstate};
use qsag_agg::zk_hem::v2::{
    field5::Fp5,
    hash::{Digest, Hasher, MerkleTree, Transcript},
    params::Profile,
};
use qsag_ass2::firmware::{CanopyInput, CthWotsInput, JiveInput, SumcheckInput};

pub const P: u64 = 0xffff_ffff_0000_0001;
pub const PROFILE: Profile = Profile::TurboShakeJohnson400;
pub const FS_CUSTOMIZATION: &[u8] = b"QSAG.ZKHEM2.FS/v1";
pub const TREE_CUSTOMIZATION: &[u8] = b"QSAG.ZKHEM2.TREE/v1";

/// Reproducible full-width words (xorshift64).
pub fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn limbs(v: Fp5) -> [u64; 5] {
    v.to_limbs().map(Goldilocks::to_canonical_u64)
}

/// Length-prefixed transcript frame.
fn frame(fields: &[&[u8]]) -> Vec<u8> {
    let mut out = Vec::new();
    for field in fields {
        out.extend_from_slice(&(field.len() as u64).to_le_bytes());
        out.extend_from_slice(field);
    }
    out
}

/// One padded TurboSHAKE256 rate block: domain byte 0x07 after the frame, 0x80 in byte 135.
fn rate_block(frame: &[u8]) -> [u8; 136] {
    let mut block = [0u8; 136];
    block[..frame.len()].copy_from_slice(frame);
    block[frame.len()] ^= 0x07;
    block[135] ^= 0x80;
    block
}

/// A valid sumcheck mailbox and the value the image must output.
pub struct Sumcheck {
    pub input: SumcheckInput,
    /// The polynomial at the squeezed point, by direct power sum.
    pub value: [u64; 5],
}

/// A random degree-nine round polynomial bound into a live `zk-Hem v2` transcript, with the
/// transcript's own `SQUEEZE_E` frame and challenge.
pub fn sumcheck(sample: u8, rng: &mut u64) -> Sumcheck {
    let midstate = turboshake256_static_midstate(FS_CUSTOMIZATION);
    let coeffs: [Fp5; 10] = from_fn(|_| Fp5(from_fn(|_| Goldilocks::from_u64_reduced(next(rng)))));
    let sum = coeffs.iter().fold(coeffs[0], |s, &c| s + c);
    let mut transcript = Transcript::new(PROFILE, &[b"firmware KAT", &[sample]]);
    transcript.absorb_fp5_slice(b"round", &coeffs);
    let chain = transcript.digest();
    let squeeze = frame(&[b"SQUEEZE_E", &chain, b"r", &[0u8; 8], &[0u8; 8]]);
    let mut digest = [0u8; 50];
    turboshake256_from_midstate_into(&midstate, &squeeze, &mut digest);
    let x = transcript.squeeze_fp5(b"r");
    assert_eq!(
        x.to_le_bytes(),
        digest[..40],
        "first SQUEEZE_E attempt is the challenge"
    );
    // Direct power sum, independent of the firmware's Horner schedule.
    let mut power = Fp5::ONE;
    let mut value = Fp5::ZERO;
    for c in coeffs {
        value += c * power;
        power *= x;
    }
    Sumcheck {
        input: SumcheckInput {
            coeffs: coeffs.map(limbs),
            claim: limbs(sum),
            midstate,
            block: rate_block(&squeeze),
            expected: digest,
        },
        value: limbs(value),
    }
}

/// The zero polynomial with an `ABSORB` frame of exactly 135 bytes, so the domain byte and
/// the final padding bit share byte 135.
pub fn sumcheck_rate_boundary() -> Sumcheck {
    let mut transcript = Transcript::new(PROFILE, &[]);
    let chain = transcript.digest();
    let payload = [0x4e; 46];
    let absorb = frame(&[b"ABSORB", &chain, b"a", &payload]);
    assert_eq!(absorb.len(), 135);
    transcript.absorb(b"a", &payload);
    Sumcheck {
        input: SumcheckInput {
            coeffs: [[0; 5]; 10],
            claim: [0; 5],
            midstate: turboshake256_static_midstate(FS_CUSTOMIZATION),
            block: rate_block(&absorb),
            expected: transcript.digest(),
        },
        value: [0; 5],
    }
}

/// A real TurboSHAKE256 output under the transcript midstate whose third word is `>= p`:
/// a draw the live transcript discards. `expected` is that output, so only the canonicity
/// rule can reject it. The message is the eight bytes of a nonce found by search.
pub fn sumcheck_noncanonical_draw() -> SumcheckInput {
    let midstate = turboshake256_static_midstate(FS_CUSTOMIZATION);
    let message = 0x1400_0000_0173_6fffu64.to_le_bytes();
    let mut expected = [0u8; 50];
    turboshake256_from_midstate_into(&midstate, &message, &mut expected);
    let word = |i: usize| u64::from_le_bytes(expected[8 * i..8 * i + 8].try_into().unwrap());
    assert_eq!(word(2), 0xffff_ffff_83c3_a9dd);
    assert!(word(2) >= P && [0, 1, 3, 4].iter().all(|&i| word(i) < P));
    assert!(Fp5::from_le_bytes_canonical(expected[..40].try_into().unwrap()).is_none());
    SumcheckInput {
        coeffs: [[0; 5]; 10],
        claim: [0; 5],
        midstate,
        block: rate_block(&message),
        expected,
    }
}

/// A live 16-leaf tree and its leaves.
pub fn canopy_tree(stage: u8) -> (MerkleTree, Vec<Digest>) {
    let hasher = Hasher::new(PROFILE);
    let leaves: Vec<_> = (0..16)
        .map(|i| hasher.leaf_ext(stage, i, &[Fp5::from_u64(i.into())]))
        .collect();
    (MerkleTree::build(hasher, stage, leaves.clone()), leaves)
}

/// The depth-4 opening of leaf `index` in [`canopy_tree`].
pub fn canopy(tree: &MerkleTree, leaves: &[Digest], stage: u8, index: usize) -> CanopyInput {
    CanopyInput {
        depth: 4,
        stage,
        index: index as u64,
        leaf: leaves[index],
        expected_root: tree.root(),
        siblings: tree.open(&[index]),
    }
}

/// One synthetic path of the given depth with live node and root hashes.
pub fn canopy_synthetic_path(depth: u8) -> CanopyInput {
    let hasher = Hasher::new(PROFILE);
    let stage = 0xfd;
    let mut u = (1u32 << depth) + (((1u32 << depth) - 1) & 0x5555);
    let index = u64::from(u - (1 << depth));
    let leaf = [0x31; 50];
    let mut cur = leaf;
    let mut siblings = Vec::new();
    for j in 0..depth {
        let sib: Digest = from_fn(|i| i as u8 ^ j);
        siblings.push(sib);
        cur = if u & 1 == 0 {
            hasher.node(u / 2, &cur, &sib)
        } else {
            hasher.node(u / 2, &sib, &cur)
        };
        u /= 2;
    }
    CanopyInput {
        depth,
        stage,
        index,
        leaf,
        expected_root: hasher.root(stage, depth, &cur),
        siblings,
    }
}

/// The reference compression of a Jive mailbox.
pub fn jive_digest(input: &JiveInput) -> [u64; 7] {
    poseidon2_gl24_compress_merkle(&input.left, &input.right, &input.tweak)
}

/// The known-answer Jive input and its digest.
pub fn jive_kat() -> (JiveInput, [u64; 7]) {
    let input = JiveInput {
        left: [1, 2, 3, 4, 5, 6, 7],
        right: [8, 9, 10, 11, 12, 13, 14],
        tweak: [100, 200],
    };
    let digest = [
        1170443848852734659,
        833485916214919520,
        373819593114229865,
        2500389336842599945,
        2668122737528357675,
        15131165148025152836,
        573418327208874869,
    ];
    assert_eq!(jive_digest(&input), digest);
    (input, digest)
}

/// Four opened values, their two weight columns and the two matching tags.
pub fn cth_mac(rng: &mut u64) -> ([u128; 4], [[u128; 2]; 4], [u128; 2]) {
    let mut wide = || u128::from(next(rng)) | (u128::from(next(rng)) << 64);
    let values = [1 << 127, wide(), wide(), wide()];
    let weights: [[u128; 2]; 4] = from_fn(|_| [wide(), wide()]);
    let mut tags = [0; 2];
    for (v, w) in values.iter().zip(&weights) {
        tags[0] ^= gf2_128_mul_const(*v, w[0]);
        tags[1] ^= gf2_128_mul_const(*v, w[1]);
    }
    (values, weights, tags)
}

/// The chain value after zero, one, two and three live WOTS+C steps.
pub fn wots_chain(
    seed: [u64; 4],
    start: [u64; 4],
    layer: u32,
    tree: u64,
    keypair: u32,
    chain: u32,
) -> [[u64; 4]; 4] {
    let seed = seed.map(Goldilocks::from_u64_reduced);
    let mut x = start.map(Goldilocks::from_u64_reduced);
    let mut out = [[0; 4]; 4];
    for (step, slot) in out.iter_mut().enumerate() {
        *slot = x.map(Goldilocks::to_canonical_u64);
        if step < 3 {
            x = wots_step_hash_injective(seed, x, layer, tree, keypair, chain, step as u32);
        }
    }
    out
}

/// A valid dual-MAC and WOTS+C mailbox for each digit `0..=3`, with the chain value each
/// must release.
pub fn cth_wots(rng: &mut u64) -> [(CthWotsInput, [u64; 4]); 4] {
    let (values, weights, tags) = cth_mac(rng);
    let (layer, tree, keypair, chain) = (13, 0xfeab_8291_0157_aa03, 0xabcde, 127);
    let seed: [u64; 4] = from_fn(|_| next(rng) % P);
    let start = [P - 1, 0, next(rng) % P, next(rng) % P];
    let ends = wots_chain(seed, start, layer, tree, keypair, chain);
    from_fn(|digit| {
        let input = CthWotsInput {
            values,
            weights,
            tags,
            start,
            seed,
            layer: layer.into(),
            tree,
            keypair: keypair.into(),
            chain: chain.into(),
            digit: digit as u64,
        };
        (input, ends[digit])
    })
}
